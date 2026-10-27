//! Let the test binaries find the Lean runtime the `ethlib` crate links.

fn main() {
    // The `ethlib` build script publishes the runtime's directory through its `links` key.
    let dir = std::env::var("DEP_ETHLIB_LEAN_LIB_DIR").expect("the ethlib crate publishes the Lean library directory");
    println!("cargo::rustc-link-arg=-Wl,-rpath,{dir}");
}
