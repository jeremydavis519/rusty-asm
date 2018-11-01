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
//! rusty-asm = "0.1.0"
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
//! While `rusty_asm!` tries to parse arbitrary Rust code, it can't yet do anything with the code
//! inside nested blocks. So, for instance, the following code doesn't compile because it tries to
//! define a bridge variable and use an `asm` block inside `if` and `else` blocks:
//!
//! ```compile_fail
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
//! I have an idea of how this limitation could be lifted, but it's a breaking change to Syn. In
//! the meantime, the workaround if you need extra blocks within a `rusty_asm!` invocation is to
//! invoke `rusty_asm!` again inside each of those blocks, redefining any bridge variables you'll
//! need there. So, while it's not the cleanest solution, the above example would have to be
//! changed to something like this:
//!
//! ```ignore
//! # #![feature(asm)]
//! # extern crate rusty_asm;
//! # use rusty_asm::rusty_asm;
//! #
//! # #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
//! // Sends 1, 2, or 4 bytes at once to an ISA address (x86/x64).
//! unsafe fn poke_isa(port: u16, value: usize, bytes: u8) {
//!     rusty_asm! {                     // These two lines could actually be removed. I've left
//!         let port: in("{dx}") = port; // them in to show a possible worst-case workaround.
//!         if bytes == 1 { rusty_asm! {
//!             let port: in("{dx}") = port; // Need to redefine `port` for the inner macro.
//!             let value: in("{al}") = value as u8;
//!             asm("volatile", "intel") {
//!                 "out $port, $value"
//!             }
//!         }} else if bytes == 2 { rusty_asm! {
//!             let port: in("{dx}") = port;
//!             let value: in("{ax}") = value as u16;
//!             asm("volatile", "intel") {
//!                 "out $port, $value"
//!             }
//!         }} else { rusty_asm! {
//!             assert_eq!(bytes, 4);
//!             let port: in("{dx}") = port;
//!             let value: in("{eax}") = value as u32;
//!             asm("volatile", "intel") {
//!                 "out $port, $value"
//!             }
//!         }}
//!     };
//! }
//! # fn main() {}
//! ```

#![cfg_attr(all(feature = "proc-macro"), feature(proc_macro_diagnostic))]
#![recursion_limit = "128"]

extern crate proc_macro;
extern crate proc_macro2;
#[macro_use]
extern crate quote;
#[macro_use]
extern crate syn;
extern crate unicode_xid;

use std::collections::HashSet;
use std::hash::{Hash, Hasher};
use std::str::Chars;

use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, TokenStreamExt};
use syn::{Expr, Ident, LitStr, Stmt, Type};
use syn::parse::{self, Parse, ParseBuffer, ParseStream};
use syn::punctuated::Punctuated;
use unicode_xid::UnicodeXID;

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
        Err(x) => {
            // The test harness relies on panics, but producing a `compile_error!` gives better
            // error messages.
            if cfg!(test) {
                panic!("invalid rusty_asm! block: {}", x);
            } else {
                let message = format!("{}", x);
                quote!(compile_error!(#message))
            }
        }
    }
}

struct RustyAsmBlock {
    stmts: Vec<RustyAsmStmt>
}

mod keyword {
    custom_keyword!(out);
    custom_keyword!(inout);
    custom_keyword!(clobber);
    custom_keyword!(asm);
}

impl Parse for RustyAsmBlock {
    fn parse(input: ParseStream) -> parse::Result<Self> {
        while input.peek(Token![;]) {
            let _ = input.parse::<Token![;]>();
        }

        let mut stmts = Vec::new();
        while let Ok(stmt) = input.fork().parse::<RustyAsmStmt>() {
            // TODO: We're re-parsing an unbounded number of tokens here. Avoid this if possible.
            let _ = input.parse::<RustyAsmStmt>();
            stmts.push(stmt);
            while input.peek(Token![;]) {
                let _ = input.parse::<Token![;]>();
            }
        }

        let ends_with_expr;
        if let Ok(expr) = input.parse::<Expr>() {
            stmts.push(RustyAsmStmt::Stmt(Stmt::Expr(expr)));
            ends_with_expr = true;
        } else {
            ends_with_expr = false;
        }

        if input.is_empty() {
            Ok(RustyAsmBlock::new(stmts))
        } else if ends_with_expr {
            Err(parse::Error::new(input.cursor().span(), "expected `;`"))
        } else {
            Err(parse::Error::new(input.cursor().span(), "expected a statement"))
        }
    }
}

impl ToTokens for RustyAsmBlock {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let stmts = &self.stmts;
        let temp_tokens = quote!({
            #(#stmts)*
        });
        tokens.append_all(temp_tokens);
    }
}

impl RustyAsmBlock {
    fn new(mut stmts: Vec<RustyAsmStmt>) -> RustyAsmBlock {
        // We're done parsing the tokens at this point. Now we just need to make sure each `asm` block
        // has all of its constraints and options set up.
        let mut bridge_variables_out = Vec::<BridgeVariable>::new();
        let mut bridge_variables_in = Vec::<BridgeVariable>::new();
        let mut clobbers = HashSet::<Clobber>::new();
        for stmt in stmts.iter_mut() {
            match stmt {
                RustyAsmStmt::LetBridgeStmt(ref stmt) => {
                    stmt.push_bridge_variable(&mut bridge_variables_out, &mut bridge_variables_in);
                },
                RustyAsmStmt::ClobberStmt(ref stmt) => {
                    stmt.push_clobber(&mut clobbers);
                },
                RustyAsmStmt::InnerAsmBlock(ref mut stmt) => {
                    stmt.bridge_variables_out = bridge_variables_out.clone();
                    stmt.bridge_variables_in = bridge_variables_in.clone();
                    stmt.clobbers = clobbers.clone();
                    stmt.fix_overlapping_clobbers();
                },
                RustyAsmStmt::Stmt(_) => {}
            };
        }
        RustyAsmBlock { stmts }
    }
}

#[derive(Debug, Clone)]
enum RustyAsmStmt {
    LetBridgeStmt(LetBridgeStmt),
    ClobberStmt(ClobberStmt),
    InnerAsmBlock(InnerAsmBlock),
    Stmt(Stmt)
}

impl Parse for RustyAsmStmt {
    fn parse(input: ParseStream) -> parse::Result<Self> {
        if let Ok(stmt) = input.parse::<LetBridgeStmt>() {
            Ok(RustyAsmStmt::LetBridgeStmt(stmt))
        } else if let Ok(stmt) = input.parse::<ClobberStmt>() {
            Ok(RustyAsmStmt::ClobberStmt(stmt))
        } else if let Ok(stmt) = input.parse::<InnerAsmBlock>() {
            Ok(RustyAsmStmt::InnerAsmBlock(stmt))
        } else if let Ok(stmt) = input.parse::<Stmt>() {
            Ok(RustyAsmStmt::Stmt(stmt))
        } else {
            Err(parse::Error::new(input.cursor().span(), "expected a statement"))
        }
    }
}

impl ToTokens for RustyAsmStmt {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            RustyAsmStmt::LetBridgeStmt(stmt) => stmt.to_tokens(tokens),
            RustyAsmStmt::ClobberStmt(stmt) => stmt.to_tokens(tokens),
            RustyAsmStmt::InnerAsmBlock(stmt) => stmt.to_tokens(tokens),
            RustyAsmStmt::Stmt(stmt) => stmt.to_tokens(tokens)
        }
    }
}

#[derive(Debug, Clone)]
struct LetBridgeStmt {
    let_keyword: Token![let],
    mut_keyword: Option<Token![mut]>,
    bridge_ident: Ident,
    explicit_type: Option<(Token![:], Type)>,
    constraint_keyword: ConstraintKeyword,
    constraint_string: LitStr,
    assignment: Option<(Token![=], Expr)>,
    semicolon: Token![;]
}

#[derive(Debug, Clone)]
enum ConstraintKeyword {
    In,
    Out,
    InOut
}

impl Parse for LetBridgeStmt {
    fn parse(input: ParseStream) -> parse::Result<Self> {
        // `let [mut] <identifier>:`
        let let_keyword = input.parse::<Token![let]>()?;
        let mut_keyword;
        if input.peek(Token![mut]) {
            mut_keyword = input.parse::<Token![mut]>().ok();
        } else {
            mut_keyword = None;
        }
        let bridge_ident = input.parse::<Ident>()?;
        let colon = input.parse::<Token![:]>()?;

        // `[<type>:]`
        let explicit_type;
        if let Ok(parsed_type) = input.fork().parse::<Type>() {
            // TODO: We're re-parsing an unbounded number of tokens here. Avoid this if possible.
            let _ = input.parse::<Type>();
            explicit_type = Some((colon, parsed_type));
            input.parse::<Token![:]>()?;
        } else {
            explicit_type = None;
        }

        // `<constraint>`
        let constraint_keyword;
        let lookahead = input.lookahead1();
        if lookahead.peek(Token![in]) {
            let _ = input.parse::<Token![in]>();
            constraint_keyword = ConstraintKeyword::In;
        } else if lookahead.peek(keyword::out) {
            let _ = input.parse::<keyword::out>();
            constraint_keyword = ConstraintKeyword::Out;
        } else if lookahead.peek(keyword::inout) {
            let _ = input.parse::<keyword::inout>();
            constraint_keyword = ConstraintKeyword::InOut;
        } else {
            return Err(lookahead.error());
        }

        // `(<constraint_string>)` - e.g. `("r")`
        let content;
        parenthesized!(content in input);
        let constraint_string = content.parse::<LitStr>()?;

        let assignment;
        if let Ok(assign_op) = input.parse::<Token![=]>() {
            let init_expr = input.parse::<Expr>()?;
            assignment = Some((assign_op, init_expr));
        } else {
            assignment = None;
        }

        let semicolon = input.parse::<Token![;]>()?;

        Ok(LetBridgeStmt {
            let_keyword,
            mut_keyword,
            bridge_ident,
            explicit_type,
            constraint_keyword,
            constraint_string,
            assignment,
            semicolon
        })
    }
}

impl ToTokens for LetBridgeStmt {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        // Emit the equivalent Rust `let` statement, keeping the original span for each token.
        self.let_keyword.to_tokens(tokens);
        if let Some(mut_keyword) = self.mut_keyword {
            mut_keyword.to_tokens(tokens);
        }
        self.bridge_ident.to_tokens(tokens);
        if let Some((colon, ref explicit_type)) = self.explicit_type {
            colon.to_tokens(tokens);
            explicit_type.to_tokens(tokens);
        }
        if let Some((assign_op, ref init_expr)) = self.assignment {
            assign_op.to_tokens(tokens);
            init_expr.to_tokens(tokens);
        }
        self.semicolon.to_tokens(tokens);
    }
}

impl LetBridgeStmt {
    fn push_bridge_variable(&self, bridge_variables_out: &mut Vec<BridgeVariable>,
            bridge_variables_in: &mut Vec<BridgeVariable>) {
        match self.constraint_keyword {
            ConstraintKeyword::In => {
                Self::push_variable(bridge_variables_in, BridgeVariable {
                    ident: self.bridge_ident.clone(),
                    llvm_constraint: (self.constraint_string.value(), self.constraint_string.span())
                });
            },

            ConstraintKeyword::Out => {
                let duplicate_index = Self::push_variable(bridge_variables_out, BridgeVariable {
                    ident: self.bridge_ident.clone(),
                    llvm_constraint: (String::from("=") + self.constraint_string.value().as_str(), self.constraint_string.span())
                });

                // If a duplicate was found, and it was an `inout` variable, remove the `in` constraint. It technically wouldn't
                // be incorrect to keep it, but it would make it a little harder for LLVM to optimize the register usage.
                if let Some(index) = duplicate_index {
                    Self::swap_remove_variable(bridge_variables_in, BridgeVariable {
                        ident: self.bridge_ident.clone(),
                        llvm_constraint: (format!("{}", index), Span::call_site()) // The span doesn't matter here.
                    });
                }
            },

            ConstraintKeyword::InOut => {
                let mut index = bridge_variables_out.len();
                let span = self.constraint_string.span();
                if let Some(unexpected_index) = Self::push_variable(bridge_variables_out, BridgeVariable {
                            ident: self.bridge_ident.clone(),
                            llvm_constraint: (String::from("=") + self.constraint_string.value().as_str(), span)
                        }) {
                    // If a duplicate `out` variable was found, use that index instead of a new one.
                    index = unexpected_index;
                }
                Self::push_variable(bridge_variables_in, BridgeVariable {
                    ident: self.bridge_ident.clone(),
                    llvm_constraint: (format!("{}", index), span) // Linked to the output constraint for the same variable
                });
            }
        }
    }

    fn push_variable(vec: &mut Vec<BridgeVariable>, var: BridgeVariable) -> Option<usize> {
        // First, check for a duplicate and overwrite it if it's found.
        // TODO: It might be worthwhile to use a HashSet to make finding duplicates faster.
        for (i, mut other) in vec.iter_mut().enumerate() {
            if var.bad_duplicate_of(other) {
                // Duplicate found.
                *other = var;
                return Some(i);
            }
        }

        // No duplicates found. Put the new variable at the end of the vector.
        vec.push(var);
        None
    }

    // Using swap_remove is O(1). It doesn't preserve the order of the elements, but we don't always care about that.
    // Specifically, we don't care about it with the input and clobber vectors. And removing from the output vector
    // would require special handling anyway to make sure we don't break any `inout` constraints.
    fn swap_remove_variable(vec: &mut Vec<BridgeVariable>, var: BridgeVariable) {
        // TODO: This search, on the other hand, is O(n). HashSet?
        let mut index = vec.len();
        for (i, ref other) in vec.iter().enumerate() {
            if var.bad_duplicate_of(other) {
                index = i;
                break;
            }
        }
        if index < vec.len() {
            vec.swap_remove(index);
        }
    }
}

#[derive(Debug, Clone)]
struct ClobberStmt {
    constraint_string: LitStr
}

impl Parse for ClobberStmt {
    fn parse(input: ParseStream) -> parse::Result<Self> {
        input.parse::<keyword::clobber>()?;
        let content;
        parenthesized!(content in input);
        let constraint_string = content.parse::<LitStr>()?;
        input.parse::<Token![;]>()?;
        
        Ok(ClobberStmt { constraint_string })
    }
}

impl ToTokens for ClobberStmt {
    fn to_tokens(&self, _: &mut TokenStream) {
        // We have nothing to do here. A clobber doesn't correspond to any Rust statements.
    }
}

impl ClobberStmt {
    fn push_clobber(&self, clobbers: &mut HashSet<Clobber>) {
        clobbers.insert(Clobber {
            llvm_constraint: (self.constraint_string.value(), self.constraint_string.span())
        });
    }
}

#[derive(Debug, Clone)]
struct InnerAsmBlock {
    options: Punctuated<LitStr, Token![,]>,
    asm_unchanged: Option<LitStr>,

    bridge_variables_out: Vec<BridgeVariable>,
    bridge_variables_in: Vec<BridgeVariable>,
    clobbers: HashSet<Clobber>
}

impl Parse for InnerAsmBlock {
    fn parse(input: ParseStream) -> parse::Result<Self> {
        input.parse::<keyword::asm>()?;

        let options: Punctuated<LitStr, Token![,]>;
        if let Ok(content) = parenthesized(input) {
            if content.is_empty() {
                options = Punctuated::new();
            } else {
                options = content.call(Punctuated::parse_separated_nonempty)?;
            }
        } else {
            options = Punctuated::new();
        }

        let content;
        braced!(content in input);
        let asm_unchanged = content.parse::<LitStr>().ok();

        Ok(InnerAsmBlock {
            options,
            asm_unchanged,

            bridge_variables_out: Vec::new(),
            bridge_variables_in: Vec::new(),
            clobbers: HashSet::new()
        })
    }
}

impl ToTokens for InnerAsmBlock {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        // Emit a standard (albeit unstable) `asm!` macro.

        if let Some(ref asm_unchanged) = self.asm_unchanged {
            let asm_span = asm_unchanged.span();

            // Replace every occurrence of `$<ident>` in the ASM code with the appropriate `$0`, `$1`, etc.
            let (llvm_asm, used_idents) = self.replace_identifiers(asm_unchanged.value().as_str(), asm_span);

            // Warn the programmer if one of the available bridge variables wasn't referenced in the ASM code.
            for var in self.bridge_variables_out.iter().chain(self.bridge_variables_in.iter()) {
                if !used_idents.contains(&var.ident.to_string()) {
                    warn(var.ident.span(), "bridge variable not used");
                    help(asm_span, "in this `asm` block");
                }
            }

            let asm_str = LitStr::new(llvm_asm.as_str(), asm_span);
            let constraints_out = self.bridge_variables_out.iter().map(|v| v.constraint_as_tokens());
            let constraints_in = self.bridge_variables_in.iter().map(|v| v.constraint_as_tokens());
            let constraints_clobber = self.clobbers.iter().map(|v| v.constraint_as_lit_str());
            let options = &self.options;

            let temp_tokens = quote!(asm!(#asm_str : #(#constraints_out),* : #(#constraints_in),* : #(#constraints_clobber),* : #(#options),*););
            tokens.append_all(temp_tokens);
        }
    }
}

impl InnerAsmBlock {
    // Replaces every occurrence of `$<ident>` in `orig` with the appropriate numeral reference to an
    // input or output register, if the identifier matches a bridge variable.
    fn replace_identifiers(&self, orig: &str, span: Span) -> (String, HashSet<String>) {
        let mut result = String::new();
        let mut used_idents = HashSet::new();
        let mut chars = orig.chars();
        while let Some(c) = chars.next() {
            result.push(c);
            if c == '$' {
                let rest = chars.as_str();
                if let Some(c2) = chars.next() {
                    if c2 == '$' {
                        // Keep the "$$" around so LLVM will see it.
                        result.push(c2);
                    } else if let Some((ident, replacement)) = self.consume_translate_ident(rest, &mut chars, span) {
                        // A defined identifier was found. Replace it with its position in the register lists.
                        result.push_str(replacement.as_str());
                        used_idents.insert(ident);
                    } else {
                        // No identifier found. Issue a warning.
                        result.push(c2);
                        warn(span, "expected an identifier after `$`");
                        help(span, "you can include a literal dollar sign by using `$$`");
                    }
                } else {
                    // No more characters. Issue a warning.
                    warn(span, "unexpected end of asm block after `$`");
                    help(span, "you can include a literal dollar sign by using `$$`");
                }
            }
        }
        (result, used_idents)
    }

    // Consumes and translates the next identifier if there is an identifier here.
    // When this is called, `chars` should be one character ahead of `orig`.
    fn consume_translate_ident(&self, orig: &str, chars: &mut Chars, span: Span) -> Option<(String, String)> {
        let output_regs_count = self.bridge_variables_out.len();
        if let Some((ident, length)) = Self::parse_ident_at_start(orig) {
            // There's a valid identifier here. Let's see if it corresponds to a bridge variable.
            if let Some(index) = Self::find_var_by_ident(&self.bridge_variables_out, &ident) {
                // Found the identifier in the `out` bridge variables.
                if length > 1 {
                    chars.nth(length - 2); // Skip past the identifier.
                }
                Some((ident, format!("{}", index)))
            } else if let Some(index) = Self::find_var_by_ident(&self.bridge_variables_in, &ident) {
                // Found the identifier in the `in` bridge variables.
                if length > 1 {
                    chars.nth(length - 2); // Skip past the identifier.
                }
                Some((ident, format!("{}", index + output_regs_count)))
            } else {
                // Couldn't find the identifier anywhere. Issue a warning.
                warn(span, format!("unrecognized bridge variable `{}`", ident));
                help(span, "it must be declared in this `rusty_asm` block with `in`, `out`, or `inout`");
                None
            }
        } else {
            // Not a valid identifier. Issue a warning.
            warn(span, "expected an identifier after `$`");
            help(span, "you can include a literal dollar sign by using `$$`");
            None
        }
    }

    fn parse_ident_at_start(text: &str) -> Option<(String, usize)> {
        let mut chars = text.chars();
        let mut result = String::new();
        let mut length = 0; // Total length of the string, in characters
        if let Some(first_char) = chars.next() {
            result.push(first_char);
            length += 1;
            if first_char != '_' && !UnicodeXID::is_xid_start(first_char) {
                return None; // Invalid first character.
            }
            for c in chars {
                if !UnicodeXID::is_xid_continue(c) {
                    break; // We've reached the end of the identifier before the end of the string.
                }
                result.push(c);
                length += 1;
            }
            if result.as_str() == "_" {
                None // An underscore by itself isn't a valid identifier.
            } else {
                Some((result, length))
            }
        } else {
            None // We were given an empty string.
        }
    }

    fn find_var_by_ident(variables: &Vec<BridgeVariable>, ident_string: &String) -> Option<usize> {
        for (i, var) in variables.iter().enumerate() {
            if format!("{}", var.ident) == *ident_string {
                return Some(i);
            }
        }
        None
    }

    // Makes sure that the list of clobbers has nothing in common with the lists of inputs and outputs. The `asm!` macro
    // may or may not require that, and it doesn't hurt in any case.
    fn fix_overlapping_clobbers(&mut self) {
        // If a clobber is the same as an output, remove the clobber and produce a warning, since
        // that may or may not be what the programmer expects. In any case, having both an `out`
        // variable and a clobber is confusing to the reader, so one should be removed.
        for var in self.bridge_variables_out.iter() {
            if let Some(reg) = var.explicit_register() {
                for clobber in self.clobbers.clone().iter() {
                    if clobber.constraint_as_str() == reg {
                        warn(clobber.span(), "clobber points to same register as an output; ignoring clobber");
                        help(var.constraint_span(), "output declared here");
                        self.clobbers.remove(&clobber);
                        break; // There are already no duplicate clobbers.
                    }
                }
            }
        }

        // If a clobber is the same as an input, change the clobber into an output, bound to the
        // same variable (since the `asm!` macro won't let us bind something to `_`).
        for (i, var) in self.bridge_variables_in.clone().iter().enumerate() {
            if let Some(reg) = var.explicit_register() {
                for clobber in self.clobbers.clone().iter() {
                    if clobber.constraint_as_str() == reg {
                        // Add the output and link the input to it.
                        let out_constraint = format!("={}", var.constraint_as_str());
                        let in_constraint = format!("{}", self.bridge_variables_out.len());
                        self.bridge_variables_out.push(BridgeVariable {
                            ident: var.ident.clone(),
                            llvm_constraint: (out_constraint, var.constraint_span())
                        });
                        self.bridge_variables_in.remove(i);
                        self.bridge_variables_in.push(BridgeVariable {
                            ident: var.ident.clone(),
                            llvm_constraint: (in_constraint, var.constraint_span())
                        });
                        // Remove the clobber.
                        self.clobbers.remove(&clobber);
                        break;
                    }
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
struct BridgeVariable {
    ident: Ident,
    llvm_constraint: (String, Span)
}

impl BridgeVariable {
    fn constraint_as_tokens(&self) -> TokenStream {
        let constraint = LitStr::new(self.llvm_constraint.0.as_str(), self.llvm_constraint.1);
        let ident = &self.ident;
        quote!(#constraint(#ident))
    }

    fn bad_duplicate_of(&self, other: &Self) -> bool {
        // Removing duplicate identifiers is a matter of memory safety--it's dangerous (and maybe disallowed by the
        // compiler) to have two output registers linked to the same Rust variable.
        format!("{}", self.ident) == format!("{}", other.ident)
    }

    // Returns the name of the explicit register referenced by this variable's constraint, if any.
    // For instance, with a constraint of `"{eax}"`, it returns `"eax"`.
    pub fn explicit_register(&self) -> Option<&str> {
        let constraint = self.llvm_constraint.0.as_str();
        if constraint.starts_with('{') && constraint.ends_with('}') {
            Some(&constraint[1 .. constraint.len() - 1])
        } else {
            None
        }
    }

    pub fn constraint_as_str(&self) -> &str {
        self.llvm_constraint.0.as_str()
    }

    pub fn constraint_span(&self) -> Span {
        self.llvm_constraint.1
    }
}

#[derive(Debug, Clone)]
struct Clobber {
    llvm_constraint: (String, Span)
}

impl Clobber {
    pub fn constraint_as_str(&self) -> &str {
        self.llvm_constraint.0.as_str()
    }

    fn constraint_as_lit_str(&self) -> LitStr {
        let lit = LitStr::new(self.constraint_as_str(), self.llvm_constraint.1);
        lit
    }

    pub fn span(&self) -> Span {
        self.llvm_constraint.1
    }
}

impl PartialEq for Clobber {
    fn eq(&self, other: &Self) -> bool {
        self.llvm_constraint.0 == other.llvm_constraint.0
    }
}

impl Eq for Clobber {}

impl Hash for Clobber {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.llvm_constraint.0.hash(state)
    }
}

fn parenthesized(input: ParseStream) -> parse::Result<ParseBuffer> {
    let content;
    parenthesized!(content in input);
    Ok(content)
}
use std::fmt::Display;
#[cfg(all(feature = "proc-macro", not(test)))]
fn warn<T: Into<String>+Display>(span: Span, message: T) {
    span.unstable().warning(message).emit();
}

#[cfg(not(all(feature = "proc-macro", not(test))))]
fn warn<T: Into<String>+Display>(_: Span, _: T) {}

#[cfg(all(feature = "proc-macro", not(test)))]
fn help<T: Into<String>+Display>(span: Span, message: T) {
    span.unstable().help(message).emit();
}

#[cfg(not(all(feature = "proc-macro", not(test))))]
fn help<T: Into<String>+Display>(_: Span, _: T) {}

#[cfg(test)]
mod tests {
    extern crate runtime_macros;
    use self::runtime_macros::emulate_macro_expansion_fallible;
    use super::rusty_asm_internal;
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
