//! Python's `random.Random(seed).shuffle`, bit for bit.
//!
//! The pinned recovery cases shuffle cell indices with `random.Random(42)`.
//! Reproducing their bytes needs the same generator and the same shuffle.
//!
//! - The generator is MT19937, from Matsumoto and Nishimura, "Mersenne Twister", ACM TOMACS 8(1), 1998.
//! - Seeding, bit drawing and shuffling follow CPython's `Modules/_randommodule.c` and `Lib/random.py`.

/// Words in the generator's state.
const N: usize = 624;

/// The middle word offset of the twist.
const M: usize = 397;

/// The twist's conditional XOR, the last row of the generator matrix.
const MATRIX_A: u32 = 0x9908_b0df;

/// The most significant bit of a word.
const UPPER_MASK: u32 = 0x8000_0000;

/// The 31 low bits of a word.
const LOWER_MASK: u32 = 0x7fff_ffff;

/// A Mersenne Twister seeded the way CPython seeds `random.Random(seed)`.
pub(crate) struct PythonRandom {
    /// The 624 words of state.
    state: [u32; N],
    /// The next word to temper; `N` means the state must twist first.
    index: usize,
}

impl PythonRandom {
    /// The generator `random.Random(seed)` builds for a small non-negative integer.
    ///
    /// CPython splits the seed into 32-bit words, least significant first.
    /// A seed below 2^32 is one word, so the key is `[seed]`.
    pub(crate) fn new(seed: u32) -> Self {
        Self::from_key(&[seed])
    }

    /// The reference `init_by_array`: mix every key word into a linear seeding.
    fn from_key(key: &[u32]) -> Self {
        // Phase 1: seed the state linearly from a fixed constant.
        let mut state = [0u32; N];
        state[0] = 19_650_218;
        for i in 1..N {
            state[i] = 1_812_433_253u32.wrapping_mul(state[i - 1] ^ (state[i - 1] >> 30)).wrapping_add(word(i));
        }

        // Phase 2: fold the key in, cycling through it until every word has been touched.
        let (mut i, mut j) = (1, 0);
        for _ in 0..N.max(key.len()) {
            let mixed = (state[i - 1] ^ (state[i - 1] >> 30)).wrapping_mul(1_664_525);
            state[i] = (state[i] ^ mixed).wrapping_add(key[j]).wrapping_add(word(j));
            i += 1;
            j += 1;
            if i >= N {
                state[0] = state[N - 1];
                i = 1;
            }
            if j >= key.len() {
                j = 0;
            }
        }

        // Phase 3: one more pass without the key, to spread it through the state.
        for _ in 0..N - 1 {
            let mixed = (state[i - 1] ^ (state[i - 1] >> 30)).wrapping_mul(1_566_083_941);
            state[i] = (state[i] ^ mixed).wrapping_sub(word(i));
            i += 1;
            if i >= N {
                state[0] = state[N - 1];
                i = 1;
            }
        }

        // The top bit of the first word is set, so the state is never all zero.
        state[0] = UPPER_MASK;
        Self { state, index: N }
    }

    /// The next 32-bit output: the reference `genrand_int32`.
    fn next_u32(&mut self) -> u32 {
        // Regenerate all 624 words once every word has been used.
        if self.index >= N {
            for k in 0..N {
                let y = (self.state[k] & UPPER_MASK) | (self.state[(k + 1) % N] & LOWER_MASK);
                let twisted = (y >> 1) ^ if y & 1 == 0 { 0 } else { MATRIX_A };
                self.state[k] = self.state[(k + M) % N] ^ twisted;
            }
            self.index = 0;
        }

        // Temper the word, so that its bits are equidistributed.
        let mut y = self.state[self.index];
        self.index += 1;
        y ^= y >> 11;
        y ^= (y << 7) & 0x9d2c_5680;
        y ^= (y << 15) & 0xefc6_0000;
        y ^ (y >> 18)
    }

    /// Python's `getrandbits(k)` for `1 <= k <= 32`: the top `k` bits of one output.
    fn bits(&mut self, k: u32) -> u32 {
        self.next_u32() >> (32 - k)
    }

    /// Python's `_randbelow(n)`: a uniform integer in `[0, n)`, by rejection.
    ///
    /// It draws as many bits as `n` has, and retries until the draw falls below `n`.
    fn below(&mut self, n: u32) -> u32 {
        let k = u32::BITS - n.leading_zeros();
        loop {
            let r = self.bits(k);
            if r < n {
                return r;
            }
        }
    }

    /// Python's `shuffle`: Fisher-Yates, from the last position down to the second.
    pub(crate) fn shuffle<T>(&mut self, items: &mut [T]) {
        for i in (1..items.len()).rev() {
            let bound = u32::try_from(i + 1).expect("a shuffled list fits in 32 bits");
            let j = self.below(bound) as usize;
            items.swap(i, j);
        }
    }
}

/// An index as the reference code adds it: a 32-bit word.
fn word(index: usize) -> u32 {
    u32::try_from(index).expect("indices stay below the state size")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn matches_the_reference_outputs() {
        // The reference program `mt19937ar.c` seeds with this key and prints these first outputs.
        let mut rng = PythonRandom::from_key(&[0x123, 0x234, 0x345, 0x456]);
        let outputs: Vec<u32> = (0..5).map(|_| rng.next_u32()).collect();
        assert_eq!(outputs, [1_067_595_299, 955_945_823, 477_289_528, 4_107_218_783, 4_228_976_476]);
    }

    #[test]
    fn shuffle_matches_the_pinned_recovery_case() {
        // One pinned recovery case lists 0..64 as `random.Random(42).shuffle` leaves it.
        //
        //     case : recover_cells_and_kzg_proofs_case_invalid_shuffled_half_missing
        //     head : 23, 25, 7, 22, 45, 33, 19, 59, 46, 9
        let mut indices: Vec<u32> = (0..64).collect();
        PythonRandom::new(42).shuffle(&mut indices);
        assert_eq!(indices[..10], [23, 25, 7, 22, 45, 33, 19, 59, 46, 9]);
    }
}
