//! The generic framework: an operation, its cases, and the check of each outcome.

use std::fmt::{self, Debug, Display};
use std::marker::PhantomData;
use std::path::PathBuf;

use ethlib::Error;
use serde::Serialize;

/// One call of a specification operation, exposed by EthLib and pinned by test vectors.
///
/// The implementing type holds the call's arguments, and serializes as the case's `input:`.
/// Its cases only describe inputs, and the outcome the specification requires for each.
pub trait Operation: Serialize + Send + Sized + 'static {
    /// The suite directory, such as `kzg`.
    const KIND: &'static str;

    /// The handler directory, named after the specification function.
    const HANDLER: &'static str;

    /// What the operation returns, as written under `output:`.
    type Output: Serialize + PartialEq + Debug + Send + 'static;

    /// Run the Lean definition through the bindings.
    ///
    /// # Errors
    ///
    /// Fails when Lean rejects the input.
    fn run(&self) -> Result<Self::Output, Error>;

    /// Declare every case of the operation.
    fn cases(cases: &mut Cases<'_, Self>);
}

/// The outcome the specification requires for one input.
enum Expect<T> {
    /// The input is well formed, and its output is recorded.
    Valid,
    /// The input is well formed, and the output must be this one.
    Returns(T),
    /// The input is malformed, and the operation must reject it.
    Invalid,
}

/// The cases of one operation, as it declares them.
///
/// Each method takes the case name without the handler prefix, and a closure that builds the input.
/// Building is deferred, so listing or filtering the cases runs no Lean code.
pub struct Cases<'a, O> {
    /// Where each declared case goes, with its type erased.
    out: &'a mut Vec<Case>,
    /// The operation the cases belong to.
    operation: PhantomData<O>,
}

impl<O: Operation> Cases<'_, O> {
    /// A well-formed input, whose output is recorded.
    pub fn valid(&mut self, name: impl Display, input: impl FnOnce() -> O + Send + 'static) {
        self.push(name, Expect::Valid, input);
    }

    /// A well-formed input, whose output must be `output`.
    ///
    /// A verifier's cases use it, so a wrong verdict fails the case instead of being recorded.
    pub fn returns(&mut self, name: impl Display, output: O::Output, input: impl FnOnce() -> O + Send + 'static) {
        self.push(name, Expect::Returns(output), input);
    }

    /// A malformed input, which the operation must reject.
    pub fn invalid(&mut self, name: impl Display, input: impl FnOnce() -> O + Send + 'static) {
        self.push(name, Expect::Invalid, input);
    }

    /// Record a case, with the work that generates its file.
    fn push(&mut self, name: impl Display, expect: Expect<O::Output>, input: impl FnOnce() -> O + Send + 'static) {
        let generate = move || {
            let input = input();
            // The outcome must be the one the specification requires.
            let output = match (input.run(), expect) {
                (Ok(output), Expect::Valid) => Some(output),
                (Ok(output), Expect::Returns(expected)) if output == expected => Some(output),
                (Ok(output), Expect::Returns(expected)) => {
                    return Err(format!("EthLib returned {output:?}, the specification {expected:?}"));
                }
                (Err(_), Expect::Invalid) => None,
                (Ok(_), Expect::Invalid) => {
                    return Err("the specification rejects this input, EthLib accepted it".into());
                }
                (Err(err), _) => {
                    return Err(format!("the specification accepts this input, EthLib rejected it: {err}"));
                }
            };
            Ok(ethlib_vectors::encode(&input, output.as_ref()))
        };
        self.out.push(Case {
            kind: O::KIND,
            handler: O::HANDLER,
            name: format!("{}_{name}", O::HANDLER),
            generate: Box::new(generate),
        });
    }
}

/// One case of any operation, ready to generate its file.
pub struct Case {
    /// The suite directory.
    kind: &'static str,
    /// The handler directory.
    handler: &'static str,
    /// The case directory, unique within its handler.
    name: String,
    /// Runs Lean, checks the outcome, and returns the file's text.
    generate: Box<dyn FnOnce() -> Result<String, String> + Send>,
}

impl Case {
    /// Every case of `O`, appended to `out`.
    pub(crate) fn collect<O: Operation>(out: &mut Vec<Self>) {
        O::cases(&mut Cases { out, operation: PhantomData });
    }

    /// The suite directory, such as `kzg`.
    #[must_use]
    pub fn kind(&self) -> &'static str {
        self.kind
    }

    /// A name unique across every suite: `<kind>::<handler>::<case>`.
    #[must_use]
    pub fn id(&self) -> String {
        format!("{}::{}::{}", self.kind, self.handler, self.name)
    }

    /// The case file, relative to the vector root.
    #[must_use]
    pub fn path(&self) -> PathBuf {
        [self.kind, self.handler, &self.name, ethlib_vectors::CASE_FILE].iter().collect()
    }

    /// Run the operation, and return the text of the case file.
    ///
    /// # Errors
    ///
    /// Fails when EthLib's outcome is not the one the specification requires.
    pub fn generate(self) -> Result<String, String> {
        (self.generate)()
    }
}

impl Debug for Case {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.id())
    }
}
