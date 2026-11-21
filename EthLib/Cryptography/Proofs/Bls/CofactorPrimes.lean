module

public import EthLib.Cryptography.Proofs.Pratt
public import Mathlib.NumberTheory.LucasPrimality
public import Mathlib.Tactic.NormNum.Prime

/-!
# Proofs: Kernel-checked Lucas certificates for the prime factors of the twist group order
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.CofactorPrimes
open EthLib.Cryptography

theorem prime_4920833 : Nat.Prime 4920833 :=
  Pratt.prime_of_lucas 4920833 3 [(2, 9), (7, 1), (1373, 1)] (by decide +kernel)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl <;> norm_num)
    (by decide +kernel) (by decide +kernel)

theorem prime_52872661 : Nat.Prime 52872661 :=
  Pratt.prime_of_lucas 52872661 2 [(2, 2), (3, 2), (5, 1), (83, 1), (3539, 1)] (by decide +kernel)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl <;> norm_num)
    (by decide +kernel) (by decide +kernel)

theorem prime_12211063 : Nat.Prime 12211063 :=
  Pratt.prime_of_lucas 12211063 5 [(2, 1), (3, 1), (103, 1), (19759, 1)] (by decide +kernel)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl <;> norm_num)
    (by decide +kernel) (by decide +kernel)

theorem prime_1402724681 : Nat.Prime 1402724681 :=
  Pratt.prime_of_lucas 1402724681 3
    [(2, 3), (5, 1), (7, 1), (1307, 1), (3833, 1)]
    (by decide +kernel)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl <;> norm_num)
    (by decide +kernel) (by decide +kernel)

theorem prime_16297965815447 : Nat.Prime 16297965815447 :=
  Pratt.prime_of_lucas 16297965815447 5
    [(2, 1), (7, 3), (68059, 1), (349079, 1)]
    (by decide +kernel)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl <;> norm_num)
    (by decide +kernel) (by decide +kernel)

theorem prime_810774871 : Nat.Prime 810774871 :=
  Pratt.prime_of_lucas 810774871 11
    [(2, 1), (3, 1), (5, 1), (89, 1), (151, 1), (2011, 1)]
    (by decide +kernel)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
    (by decide +kernel) (by decide +kernel)

theorem prime_63240439939 : Nat.Prime 63240439939 :=
  Pratt.prime_of_lucas 63240439939 3 [(2, 1), (3, 1), (13, 1), (810774871, 1)] (by decide +kernel)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl <;>
        first
        | exact prime_810774871
        | norm_num)
    (by decide +kernel) (by decide +kernel)

theorem prime_1770732318293 : Nat.Prime 1770732318293 :=
  Pratt.prime_of_lucas 1770732318293 2 [(2, 2), (7, 1), (63240439939, 1)] (by decide +kernel)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl <;>
        first
        | exact prime_63240439939
        | norm_num)
    (by decide +kernel) (by decide +kernel)

theorem prime_21561538103037546247 : Nat.Prime 21561538103037546247 :=
  Pratt.prime_of_lucas 21561538103037546247 5
    [(2, 1), (3, 3), (225493, 1), (1770732318293, 1)]
    (by decide +kernel)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl <;>
        first
        | exact prime_1770732318293
        | norm_num)
    (by decide +kernel) (by decide +kernel)

theorem prime_86246152412150184989 : Nat.Prime 86246152412150184989 :=
  Pratt.prime_of_lucas 86246152412150184989 2
    [(2, 2), (21561538103037546247, 1)]
    (by decide +kernel)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl <;>
        first
        | exact prime_21561538103037546247
        | norm_num)
    (by decide +kernel) (by decide +kernel)

theorem prime_6716327 : Nat.Prime 6716327 :=
  Pratt.prime_of_lucas 6716327 5 [(2, 1), (17, 1), (197539, 1)] (by decide +kernel)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl <;> norm_num)
    (by decide +kernel) (by decide +kernel)

theorem prime_40297963 : Nat.Prime 40297963 :=
  Pratt.prime_of_lucas 40297963 2 [(2, 1), (3, 1), (6716327, 1)] (by decide +kernel)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl <;>
        first
        | exact prime_6716327
        | norm_num)
    (by decide +kernel) (by decide +kernel)

theorem prime_241787779 : Nat.Prime 241787779 :=
  Pratt.prime_of_lucas 241787779 2 [(2, 1), (3, 1), (40297963, 1)] (by decide +kernel)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl <;>
        first
        | exact prime_40297963
        | norm_num)
    (by decide +kernel) (by decide +kernel)

theorem prime_1435735831703 : Nat.Prime 1435735831703 :=
  Pratt.prime_of_lucas 1435735831703 5 [(2, 1), (2969, 1), (241787779, 1)] (by decide +kernel)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl <;>
        first
        | exact prime_241787779
        | norm_num)
    (by decide +kernel) (by decide +kernel)

theorem prime_1367711 : Nat.Prime 1367711 :=
  Pratt.prime_of_lucas 1367711 7 [(2, 1), (5, 1), (233, 1), (587, 1)] (by decide +kernel)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl <;> norm_num)
    (by decide +kernel) (by decide +kernel)

theorem prime_12192593745179 : Nat.Prime 12192593745179 :=
  Pratt.prime_of_lucas 12192593745179 2
    [(2, 1), (7, 1), (11, 1), (107, 1), (541, 1), (1367711, 1)]
    (by decide +kernel)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact prime_1367711
        | norm_num)
    (by decide +kernel) (by decide +kernel)

theorem prime_512088937297519 : Nat.Prime 512088937297519 :=
  Pratt.prime_of_lucas 512088937297519 6
    [(2, 1), (3, 1), (7, 1), (12192593745179, 1)]
    (by decide +kernel)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl <;>
        first
        | exact prime_12192593745179
        | norm_num)
    (by decide +kernel) (by decide +kernel)

theorem prime_1857858664515398933 : Nat.Prime 1857858664515398933 :=
  Pratt.prime_of_lucas 1857858664515398933 2
    [(2, 2), (907, 1), (512088937297519, 1)]
    (by decide +kernel)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl <;>
        first
        | exact prime_512088937297519
        | norm_num)
    (by decide +kernel) (by decide +kernel)

theorem prime_22294303974184787197 : Nat.Prime 22294303974184787197 :=
  Pratt.prime_of_lucas 22294303974184787197 14
    [(2, 2), (3, 1), (1857858664515398933, 1)]
    (by decide +kernel)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl <;>
        first
        | exact prime_1857858664515398933
        | norm_num)
    (by decide +kernel) (by decide +kernel)

theorem prime_19931107752921199754119 : Nat.Prime 19931107752921199754119 :=
  Pratt.prime_of_lucas 19931107752921199754119 3
    [(2, 1), (3, 1), (149, 1), (22294303974184787197, 1)]
    (by decide +kernel)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl <;>
        first
        | exact prime_22294303974184787197
        | norm_num)
    (by decide +kernel) (by decide +kernel)

theorem prime_81162125843606155545104998607900118769099783 : Nat.Prime 81162125843606155545104998607900118769099783 :=
  Pratt.prime_of_lucas 81162125843606155545104998607900118769099783 5
    [(2, 1), (3, 2), (2731, 1), (57697, 1), (1435735831703, 1), (19931107752921199754119, 1)]
    (by decide +kernel)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact prime_1435735831703
        | exact prime_19931107752921199754119
        | norm_num)
    (by decide +kernel) (by decide +kernel)

theorem prime_26935696298915610574513298451669528361624243820491956655650666425177 : Nat.Prime 26935696298915610574513298451669528361624243820491956655650666425177 :=
  Pratt.prime_of_lucas 26935696298915610574513298451669528361624243820491956655650666425177 3
    [(2, 3), (13, 1), (37, 1), (86246152412150184989, 1),
     (81162125843606155545104998607900118769099783, 1)]
    (by decide +kernel)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact prime_86246152412150184989
        | exact prime_81162125843606155545104998607900118769099783
        | norm_num)
    (by decide +kernel) (by decide +kernel)

theorem prime_4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 : Nat.Prime 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 :=
  Pratt.prime_of_lucas _ 3
    [(2, 3), (373, 1), (8329, 1), (37501, 1), (661873, 1), (12211063, 1), (1402724681, 1),
     (16297965815447, 1),
     (26935696298915610574513298451669528361624243820491956655650666425177, 1)]
    (by decide +kernel)
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact prime_12211063
        | exact prime_1402724681
        | exact prime_16297965815447
        | exact prime_26935696298915610574513298451669528361624243820491956655650666425177
        | norm_num)
    (by decide +kernel) (by decide +kernel)

-- This certificate checks the conditions of Lucas by hand.
--
-- One of its prime factors has 115 digits.
--
-- A call to the shared lemma would name that factor and its proof, and neither fits in 100 columns.
private theorem pow_one_402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 : ((13 : Nat) : ZMod 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249) ^ (402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff
    402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249
    13
    (402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 - 1)]
  decide +kernel

private theorem pow_ne_402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 : ∀ q : Nat, q.Prime → q ∣ 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 - 1 →
    ((13 : Nat) : ZMod 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249) ^ ((402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 - 1 = 2 ^ 4 * (3 * (11 * (631 * (4920833 * (52872661 * (4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297)))))) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one
      402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249
      13 2 (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one
      402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249
      13 3 (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 11 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one
      402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249
      13 11 (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 631 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one
      402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249
      13 631 (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 4920833 prime_4920833 h
    exact PowMod.natCast_pow_div_ne_one
      402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249
      13 4920833 (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 52872661 prime_52872661 h
    exact PowMod.natCast_pow_div_ne_one
      402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249
      13 52872661 (by decide +kernel)
  · obtain rfl := heq 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 prime_4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 hdvd
    exact PowMod.natCast_pow_div_ne_one
      402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249
      13
      4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297
      (by decide +kernel)

theorem prime_402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 : Nat.Prime 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 :=
  lucas_primality 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 ((13 : Nat) : ZMod 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249) pow_one_402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 pow_ne_402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249

theorem prime_13 : Nat.Prime 13 := by norm_num

theorem prime_23 : Nat.Prime 23 := by norm_num

theorem prime_2713 : Nat.Prime 2713 := by norm_num

theorem prime_11953 : Nat.Prime 11953 := by norm_num

theorem prime_262069 : Nat.Prime 262069 := by norm_num

def largePrime : Nat := 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249

theorem largePrime_prime : Nat.Prime largePrime :=
  prime_402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249

end EthLib.Cryptography.Bls.CofactorPrimes
