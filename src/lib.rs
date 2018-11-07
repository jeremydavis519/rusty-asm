// Copyright (c) 2017-2018 Jeremy Davis (jeremydavis519@gmail.com)
//
// Licensed under the Apache License, Version 2.0 (located at /LICENSE-APACHE
// or http://www.apache.org/licenses/LICENSE-2.0), or the MIT license
// (located at /LICENSE-MIT or http://opensource.org/licenses/MIT), at your
// option. The file may not be copied, modified, or distributed except
// according to those terms.
//
// Unless required by applicable law or agreed to in writing, this software
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF
// ANY KIND, either express or implied. See the applicable license for the
// specific language governing permissions and limitations under that license.

//! A layer of syntactic sugar between Rust and inline assembly
//!
//! Rust currently has the [`asm!`] macro for writing inline ASM within a function defined in Rust. It uses the same basic
//! format as GCC uses for its own inline ASM--and that format isn't the most ergonomic. Here's a small example, taken from
//! [the OSDev wiki] and translated into Rust:
//!
//! [`asm!`]: https://doc.rust-lang.org/1.12.0/book/inline-assembly.html
//! [the OSDev wiki]: https://wiki.osdev.org/Inline_Assembly/Examples
//!
//! ```no_run
//! # #![feature(asm)]
//! // Retrieves a value from memory in a different segment than the one currently being used (x86[-64])
//! unsafe fn farpeekl(segment_selector: u16, offset: *const u32) -> u32 {
//!     let ret: u32;
//!     asm!("
//!         push %fs
//!         mov $1, %fs
//!         mov %fs:($2), $0
//!         pop %fs
//!     "   : "=r"(ret) : "r"(segment_selector), "r"(offset)
//!     );
//!     ret
//! }
//! # fn main() {}
//! ```
//!
//! (This example actually looks a little cleaner in my opinion than it does when written for GCC, but it could still use some work.)
//!
//! The `asm!` macro is currently an unstable, nightly-only feature. From what I've seen, there are several reasons, but one of
//! them is the syntax. It's too easy to forget the precise order of things (which come first: inputs or outputs?), and parts of
//! it are needlessly redundant. Using `"=r"`, `"r"`, or `"~r"` means the register is, respectively, an output, an input, or
//! clobbered, but the different types also have to be separated by colons. So using `asm!`, the programmer has to remember both
//! ways to tell the compiler what it should expect to happen to each register.
//!
//! This crate attempts to improve the syntax surrounding inline ASM so that it's both easier to read and easier to write without
//! looking up the required format every time. It works by using a procedural macro (1) to overload Rust's `let` statements, making
//! variables capable of storing information about how they'll be used in upcoming inline ASM blocks, and (2) to parse `asm`
//! blocks that allow variables defined with the new syntax to be used directly in the ASM code.
//!
//! ## Setup
//!
//! To use this crate, add the following to `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! rusty-asm = "0.2.0"
//! ```
//!
//! Then reference the crate in your main source file and activate the features you'll need:
//!
//! ```
//! #![feature(proc_macro_hygiene, asm)]
//! # /*
//! extern crate rusty_asm;
//! use rusty_asm::rusty_asm; // Because who wants to write `rusty_asm::rusty_asm!`?
//! # */
//! # fn main() {}
//! ```
//!
//! Note that you'll still need a nightly compiler for this. `rusty_asm` doesn't make inline ASM stable.
//!
//! ### Supported Features
//!
//! The following features are available:
//!
//! * `proc-macro`: Causes [`proc-macro2`](https://crates.io/crates/proc-macro2) to act as a thin wrapper over
//!   [`proc_macro`](https://doc.rust-lang.org/proc_macro/index.html), including the parts that are still unstable.
//!   The benefit of this feature is that it allows `rusty-asm` to provide its own warnings, which should make
//!   debugging your own code easier.
//!
//! ## Basic Syntax
//!
//! In the place where you want to add some inline ASM, call `rusty_asm!` like so:
//!
//! ```ignore
//! # extern crate rusty_asm;
//! # use rusty_asm::rusty_asm;
//! # fn main() {
//! # unsafe {
//! rusty_asm! {
//!     // (arbitrary Rust statements go here)
//!
//!     asm (/* maybe some options in here */) {
//!         // (insert your ASM code here, in quotes)
//!     }
//!
//!     // (possibly some cleanup code here)
//! }
//! # }
//! # }
//! ```
//!
//! The contents of the `asm` block need to be a string literal to make sure that Rust's parser doesn't mess up the
//! formatting. (Macros currently don't have access to whitespace information.) See the examples below for more specifics
//! about how it should look.
//!
//! Also, it's possible to have multiple `asm` blocks in the same `rusty_asm!` block, in case you want to reuse your bridge
//! variables (see below).
//!
//! ## Bridge Variables
//!
//! A _bridge variable_ is a variable that bridges the gap between Rust and ASM by incorporating the input/ouput/clobber
//! information in its definition. They can only be defined inside `rusty_asm!` blocks, and because the macro makes a new scope,
//! they are dropped when execution leaves those blocks (along with any other variables that are defined in the same scope). In
//! order to define a bridge variable, you'll need to use one of three keywords that are only valid inside `rusty_asm!` blocks:
//!
//! * `in`
//! * `out`
//! * `inout`
//!
//! Each of these keywords is used in a "let" statement to define a bridge variable. The exact syntax is as follows:
//!
//! ```text
//! let [mut] <identifier>: [<type>:] in(<constraint>) [= <expression>];
//! let [mut] <identifier>: [<type>:] out(<constraint>) [= <expression>];
//! let [mut] <identifier>: [<type>:] inout(<constraint>) [= <expression>];
//! ```
//!
//! The optional `<type>` is any Rust type, as far as the macro knows, but it should be something that makes sense to put in the
//! appropriate register (e.g. `usize`, `i8`, etc. for a general-purpose integer register).
//!
//! In addition, you can specify that you'll clobber a particular register (or that you'll clobber memory) with this syntax:
//!
//! ```text
//! clobber(<constraint>);
//! ```
//!
//! where `<constraint>` is either the name of a register (like `"eax"`) or `"memory"`.
//!
//! These statements correspond to LLVM constraints in the following way:
//!
//! ```text
//! // in, out, or inout:
//! <new-constraint>(<identifier>)
//! // clobber
//! <new-constraint>
//! ```
//!
//! In each case, `<new_constraint>` is equivalent to `<constraint>` except that for the `out` and `clobber` keywords, the `'='`
//! or `'~'` is prepended to satisfy `asm!` and LLVM. So, for instance, if you write the constraint as `"r"`, it will be
//! automatically translated to `"=r"` or `"~r"` as needed before being given to the compiler. The `inout` keyword results in two
//! new constraints: (1) the equivalent constraint for the `out` keyword (e.g. `"=r"`) and (2) an input constraint that's tied to
//! it (e.g. `"0"`).
//!
//! In order to let Rust know how to work with the bridge variables, `rusty_asm!` removes the new keywords and constraints during
//! macro expansion, so as far as Rust knows, they're just ordinary variables.
//!
//! ## The `asm` Block
//!
//! When an `asm` block is encountered, it is converted directly into an asm! invocation, using all of the constraints that have
//! been created thus far. The `asm` block's syntax is as follows:
//!
//! ```text
//! asm [(<options>)] {
//!     "<asm-code>"
//! }
//! ```
//!
//! `<options>` is an optional comma-separated list of the options that would be after the 4th colon if `asm!` were being used, such
//! as `"volatile"`. `<asm-code>` is pure ASM code, enclosed in quotes, except that it can (and should) use the bridge variables
//! that have been defined above the `asm` block.
//!
//! In order to reference a bridge variable from inside an `asm` block, insert `$<ident>` into the code, where `<ident>` is the
//! variable's identifier. As with the `asm!` macro, `$$` encodes a literal dollar sign.
//!
//! ## The `rusty_asm!` Block and Scope
//!
//! The new macro puts its entire contents inside a new scope, so that any variables defined therein are dropped at the end. Their
//! values can be moved to variables outside the macro's scope before it ends, using regular Rust code, if they need to be preserved.
//! In addition, just like any of Rust's code blocks, this one has a return value that can be used by ending the block with an
//! expression.
//!
//! Also, as of version 0.2, the macro also correctly handles inner blocks, shadowing and dropping bridge variables just like Rust
//! shadows and drops regular variables. That means you can now write code like this:
//!
//! ```ignore
//! # #![feature(asm)]
//! # extern crate rusty_asm;
//! # use rusty_asm::rusty_asm;
//! #
//! # #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
//! // Sends 1, 2, or 4 bytes at once to an ISA address (x86/x64).
//! unsafe fn poke_isa(port: u16, value: usize, bytes: u8) {
//!     rusty_asm! {
//!         let port: in("{dx}") = port;
//!         if bytes == 1 {
//!             let value: in("{al}") = value as u8;
//!             asm("volatile", "intel") {
//!                 "out $port, $value"
//!             }
//!         } else if bytes == 2 {
//!             let value: in("{ax}") = value as u16;
//!             asm("volatile", "intel") {
//!                 "out $port, $value"
//!             }
//!         } else {
//!             assert_eq!(bytes, 4);
//!             let value: in("{eax}") = value as u32;
//!             asm("volatile", "intel") {
//!                 "out $port, $value"
//!             }
//!         }
//!     };
//! }
//! # fn main() {}
//! ```
//!
//! Defining bridge variables in `if let` and `while let` constructions is still not supported, since Rust doesn't support explicit
//! type annotations in them either, and I imagine the syntax would become overly complex.
//!
//! ## Further Reading
//!
//! There are too many platform-specific constraints and options that you can specify to list them all here. Follow these links for
//! more information.
//!
//! * [The Rust book: Inline Assembly chapter]. Discusses what can be done with the `asm!` macro.
//! * [LLVM's inline assembly documentation]. Documents exactly what is allowed in LLVM inline assembly (and therefore in Rust's `asm!`
//!   invocations), along with platform-specific details.
//!
//! [The Rust book: Inline Assembly chapter]: https://doc.rust-lang.org/1.12.0/book/inline-assembly.html
//! [LLVM's inline assembly documentation]: http://llvm.org/docs/LangRef.html#inline-assembler-expressions
//!
//! ## Usage Examples
//!
//! Note that while all of these examples use x86 assembly, `rusty_asm!` should work with any assembly dialect that Rust supports (which
//! probably means any dialect that LLVM supports).
//!
//! ```ignore
//! # #![feature(asm)]
//! # extern crate rusty_asm;
//! # use rusty_asm::rusty_asm;
//! #
//! # #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
//! // Disables interrupts on an x86 CPU.
//! unsafe fn disable_interrupts() {
//!     rusty_asm! {
//!         asm("volatile") { // This block has to be marked "volatile" to make sure the compiler, seeing
//!            "cli"          // no outputs and no clobbers, doesn't assume it does nothing and
//!         }                 // decide to "optimize" it away.
//!     };
//! }
//! # fn main() {}
//! ```
//!
//! ```ignore
//! # #![cfg(any(target_arch = "x86", target_arch = "x86_64"))]
//! # #![feature(asm)]
//! # extern crate rusty_asm;
//! # use rusty_asm::rusty_asm;
//! #
//! // Shifts the hexadecimal digits of `existing` up and puts `digit` in the resulting gap.
//! fn append_hex_digit(existing: usize, digit: u8) -> usize {
//!     assert!(digit < 0x10);
//!     unsafe {
//!         rusty_asm! {
//!             let mut big: inout("r") = existing;
//!             let little: in("r") = digit as usize;
//!
//!             asm {"
//!                 shll %4, $big
//!                 orl $little, $big
//!             "}
//!
//!             big
//!         }
//!     }
//! }
//!
//! # fn main() {
//! assert_eq!(append_hex_digit(0, 0), 0);
//! assert_eq!(append_hex_digit(0, 0xf), 0xf);
//! assert_eq!(append_hex_digit(4, 2), 0x42);
//! # }
//! ```
//!
//! ## Limitations
//!
//! The bridge variable declaration syntax is slightly more restrictive than that of general `let` statements in that it only allows
//! an identifier after the `let` keyword, not an arbitrary pattern. So, for instance, this statement would not work:
//!
//! ```compile_fail
//! # #![feature(asm)]
//! # extern crate rusty_asm
//! # use rusty_asm::rusty_asm;
//! #
//! rusty_asm! {
//!     let (a, b): (in("r"), out("r")) = (12, 14);
//!     /* ... */
//! }
//! ```

#![cfg_attr(all(feature = "proc-macro"), feature(proc_macro_diagnostic))]
#![recursion_limit = "128"]

extern crate proc_macro;
#[macro_use]
extern crate quote;
#[macro_use]
extern crate syn;

use proc_macro2::TokenStream;

mod parse;
use self::parse::RustyAsmBlock;

/// Allows bridge variables, clobbers, and `asm` blocks to be defined.
///
/// See the [module documentation] for details.
///
/// [module documentation]: index.html
#[proc_macro]
pub fn rusty_asm(ts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    rusty_asm_internal(ts.into()).into()
}

fn rusty_asm_internal(ts: TokenStream) -> TokenStream {
    match syn::parse2::<RustyAsmBlock>(ts) {
        Ok(rusty_block) => quote!(#rusty_block),
        Err(e) => {
            // The test harness relies on panics, but producing a `compile_error!` gives better
            // error messages.
            if cfg!(test) {
                panic!("invalid rusty_asm! block: {}", e);
            } else {
                e.to_compile_error()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate runtime_macros;
    use self::runtime_macros::emulate_macro_expansion_fallible;
    use crate::rusty_asm_internal;
    use std::{env, fs};
    use std::path::PathBuf;

    #[test]
    fn code_coverage() {
        // Loop through all the files in `tests/`.
        let mut path = env::current_dir().unwrap();
        path.push("tests");
        for res in path.read_dir().unwrap() {
            let dir_entry = res.unwrap();
            let path = dir_entry.path();
            if path.is_file() {
                cover_tests(path, true);
            }
        }
    }

    #[test]
    fn compile_fail() {
        // Loop through all the files in `tests/compile-fail`, making sure none of them compile.
        let mut path = env::current_dir().unwrap();
        path.push("tests");
        path.push("compile-fail");
        for res in path.read_dir().unwrap() {
            let dir_entry = res.unwrap();
            let path = dir_entry.path();
            if path.is_file() {
                println!("{:#?} shouldn't compile", path);
                cover_tests(path, false);
            }
        }
    }

    fn cover_tests(path: PathBuf, should_compile: bool) {
        if let Ok(file) = fs::File::open(path) {
            let res = emulate_macro_expansion_fallible(file, "rusty_asm", rusty_asm_internal);
            if let Err(ref e) = res {
                println!("Error: {}", e);
            } else {
                println!("Compiled successfully");
            }
            // Make sure the macro invocation was or wasn't valid, as appropriate.
            assert!((should_compile && res.is_ok()) || (!should_compile && res.is_err()));
        }
    }
}
