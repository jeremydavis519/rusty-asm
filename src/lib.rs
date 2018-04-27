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
//! format as GCC uses for its own inline ASM--and that format is _awful_. I have yet to hear of anyone who actually likes it.
//! Here's a small example, taken from [the OSDev wiki] and translated into Rust:
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
//! it are needlessly redundant. Using `"=r"`, `"r"`, or `"~r"` means the register is, respectively, an output, and input, or
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
//! ```ignore
//! #![feature(proc_macro)]
//! extern crate rusty_asm;
//! use rusty_asm::rusty_asm; // Because who wants to write `rusty_asm::rusty_asm!`?
//! # fn main() {}
//! ```
//! 
//! ## Basic Syntax
//! 
//! In the place where you want to add some inline ASM, call `rusty_asm!` like so:
//! 
//! ```ignore
//! # #![feature(proc_macro)]
//! # #![feature(asm)]
//! # extern crate rusty_asm;
//! # use rusty_asm::rusty_asm;
//! # fn main() {
//! # unsafe {
//! rusty_asm! {
//!     // (arbitrary Rust statements go here)
//!     
//!     asm (/* maybe some options in here */) {
//!         // (insert your ASM code here)
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
//! let <identifier>: in(<constraint>) [= <expression>];
//! let mut <identifier>: out(<constraint>) [= <expression>];
//! let mut <identifier>: inout(<constraint>) [= <expression>];
//! ```
//! 
//! Currently, those `mut` assignments are hard rules. The parser won't accept a mutable `in` variable or an immutable `out` or
//! `inout` variable. That restriction may be lifted in the future if it turns out to be an issue. The idea is that their
//! mutability in Rust should match their mutability in ASM.
//! 
//! In addition, you can specify that you'll clobber a particular register (or that you'll clobber memory) with this syntax:
//! 
//! ```text
//! clobber(<constraint>);
//! ```
//! 
//! where `<constraint>` is the name of a register or `"memory"`.
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
//! or `'~'` is prepended to satisfy `asm!` and LLVM. The `inout` keyword results in two new constraints: (1) the equivalent
//! constraint for the `out` keyword and (2) an input constraint that's tied to it.
//! 
//! In order to let Rust know how to work with the bridge variables, `rusty_asm!` removes the new keywords and constraints during
//! macro expansion, so as far as Rust knows, they're just ordinary variables with inferred types.
//! 
//! ## The `asm` Block
//! 
//! When an `asm` block is encountered, it is converted directly into an asm! invocation, using all of the constraints that have
//! been created thus far. The `asm` block's syntax is as follows:
//! 
//! ```text
//! asm [(<options>)] {
//!     <asm-code>
//! }
//! ```
//! 
//! `<options>` is an optional comma-separated list of the options that would be after the 4th colon if `asm!` were being used, such
//! as `"volatile"`. `<asm-code>` is pure ASM code, enclosed in quotes, except that it can (and should) use the bridge variables
//! that have been defined above the `asm` block.
//! 
//! In order to reference a bridge variable from inside an `asm` block, insert `$<ident>` into the code, where `<ident>` is the
//! variable's identifier. As with the `asm!` macro, `$$` is the way to write an escaped dollar sign.
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
//! ```ignore
//! # #![feature(proc_macro)]
//! # #![feature(asm)]
//! # extern crate rusty_asm;
//! # use rusty_asm::rusty_asm;
//! #
//! # #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
//! // Disables interrupts on an x86 CPU.
//! unsafe fn disable_interrupts() {
//!     rusty_asm! {
//!         asm("volatile") { // This block has to be marked "volatile" to make sure the compiler, seeing
//!             cli           // no outputs and no clobbers, doesn't assume it does nothing and
//!         }                 // decide to "optimize" it away.
//!     };
//! }
//! # fn main() {}
//! ```
//! 
//! ```ignore
//! # #![cfg(any(target_arch = "x86", target_arch = "x86_64"))]
//! # #![feature(proc_macro)]
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
//!             let digit: usize = digit;
//!             let little: in("r") = digit;
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

#![cfg_attr(feature = "nightly", feature(proc_macro))]

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

use proc_macro2::{Span, TokenTree};
use quote::{Tokens, ToTokens};
use syn::{Expr, Ident, LitStr, Stmt};
use syn::buffer::Cursor;
use syn::punctuated::Punctuated;
use syn::synom::{PResult, Synom};
use unicode_xid::UnicodeXID;

/// Allows bridge variables, clobbers, and `asm` blocks to be defined.
/// 
/// See the [module documentation] for details.
/// 
/// [module documentation]: index.html
#[proc_macro]
pub fn rusty_asm(ts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    match syn::parse2::<RustyAsmBlock>(ts.into()) {
        Ok(rusty_block) => quote!(#rusty_block),
        Err(x) => {
            let message = format!("{}", x);
            quote!(compile_error!(#message))
        }
    }.into()
}

fn next_token_tree(cursor: Cursor) -> PResult<TokenTree> {
    match cursor.token_tree() {
        Some((tt, cursor)) => Ok((tt, cursor)),
        None => reject!(cursor,)
    }
}

macro_rules! expect {
    ($i:expr, $const:ident) => {
        match next_token_tree($i) {
            Ok((tt, cursor)) => {
                if format!("{}", tt) == stringify!($const) {
                    let result: PResult<Ident> = Ok((Ident::new(stringify!($const), tt.span()), cursor));
                    result
                } else {
                    reject!(cursor,)
                    //Err(ParseError(Some(format!("Expected `{}`, found `{}`", stringify!($const), tt))))
                }
            },
            
            Err(x) => Err(x)
            //Err(_) => Err(ParseError(Some(format!("Identifier `{}` expected", stringify!($const)))))
        }
    }
}

struct RustyAsmBlock {
    stmts: Vec<RustyAsmStmt>
}

impl Synom for RustyAsmBlock {
    named!(parse -> Self, do_parse!(
        many0!(punct!(;)) >>
        mut stmts: many0!(do_parse!(
            stmt: syn!(RustyAsmStmt) >>
            many0!(punct!(;)) >>
            (stmt)
        )) >>
        last: option!(syn!(Expr)) >>
        (match last {
            None => RustyAsmBlock::new(stmts),
            Some(last) => {
                stmts.push(RustyAsmStmt::Stmt(Stmt::Expr(last)));
                RustyAsmBlock::new(stmts)
            }
        })
    ));
    
    fn description() -> Option<&'static str> {
        Some("rusty_asm block")
    }
}

impl ToTokens for RustyAsmBlock {
    fn to_tokens(&self, tokens: &mut Tokens) {
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
                },
                RustyAsmStmt::Stmt(_) => {}
            };
        }
        RustyAsmBlock { stmts }
    }
}

enum RustyAsmStmt {
    LetBridgeStmt(LetBridgeStmt),
    ClobberStmt(ClobberStmt),
    InnerAsmBlock(InnerAsmBlock),
    Stmt(Stmt)
}

impl Synom for RustyAsmStmt {
    named!(parse -> Self, do_parse!(
        stmt: alt!(
              syn!(LetBridgeStmt) => { |x| RustyAsmStmt::LetBridgeStmt(x) }
            | syn!(ClobberStmt) => { |x| RustyAsmStmt::ClobberStmt(x) }
            | syn!(InnerAsmBlock) => { |x| RustyAsmStmt::InnerAsmBlock(x) }
            | syn!(Stmt) => { |x| RustyAsmStmt::Stmt(x) }
        ) >>
        (stmt)
    ));
}

impl ToTokens for RustyAsmStmt {
    fn to_tokens(&self, tokens: &mut Tokens) {
        match self {
            RustyAsmStmt::LetBridgeStmt(stmt) => stmt.to_tokens(tokens),
            RustyAsmStmt::ClobberStmt(stmt) => stmt.to_tokens(tokens),
            RustyAsmStmt::InnerAsmBlock(stmt) => stmt.to_tokens(tokens),
            RustyAsmStmt::Stmt(stmt) => stmt.to_tokens(tokens)
        }
    }
}

struct LetBridgeStmt {
    let_keyword: Token![let],
    mut_keyword: Option<Token![mut]>,
    bridge_ident: Ident,
    constraint_keyword: LetBridgeKeyword,
    constraint_string: LitStr,
    assignment: Option<(Token![=], Expr)>,
    semicolon: Token![;]
}

impl Synom for LetBridgeStmt {
    named!(parse -> Self, do_parse!(
        let_keyword: keyword!(let) >>
        mut_keyword: option!(keyword!(mut)) >>
        bridge_ident: syn!(Ident) >>
        punct!(:) >>
        constraint_keyword: switch!(value!(mut_keyword.is_some()),
              true => call!(LetBridgeKeyword::parse_mutable)
            | false => call!(LetBridgeKeyword::parse_immutable)
        ) >>
        constraint_string: map!(parens!(syn!(LitStr)), |parens| parens.1) >>
        assignment: option!(do_parse!(
            assign_op: punct!(=) >>
            init_expr: syn!(Expr) >>
            (assign_op, init_expr)
        )) >>
        semicolon: punct!(;) >>
        (LetBridgeStmt {
            let_keyword,
            mut_keyword,
            bridge_ident,
            constraint_keyword,
            constraint_string,
            assignment,
            semicolon
        })
    ));
    
    fn description() -> Option<&'static str> {
        Some("bridge variable declaration")
    }
}

impl ToTokens for LetBridgeStmt {
    fn to_tokens(&self, tokens: &mut Tokens) {
        // Emit the equivalent Rust `let` statement, keeping the original span for each token.
        self.let_keyword.to_tokens(tokens);
        if let Some(mut_keyword) = self.mut_keyword {
            mut_keyword.to_tokens(tokens);
        }
        self.bridge_ident.to_tokens(tokens);
        if let Some((assign_op, ref init_expr)) = self.assignment {
            assign_op.to_tokens(tokens);
            init_expr.to_tokens(tokens);
        }
        self.semicolon.to_tokens(tokens);
    }
}

impl LetBridgeStmt {
    fn push_bridge_variable(&self, bridge_variables_out: &mut Vec<BridgeVariable>, bridge_variables_in: &mut Vec<BridgeVariable>) {
        match self.constraint_keyword {
            LetBridgeKeyword::In => {
                Self::push_variable(bridge_variables_in, BridgeVariable {
                    ident: self.bridge_ident,
                    llvm_constraint: (self.constraint_string.value(), self.constraint_string.span())
                });
            },
            
            LetBridgeKeyword::Out => {
                let duplicate_index = Self::push_variable(bridge_variables_out, BridgeVariable {
                    ident: self.bridge_ident,
                    llvm_constraint: (String::from("=") + self.constraint_string.value().as_str(), self.constraint_string.span())
                });
                
                // If a duplicate was found, and it was an `inout` variable, remove the `in` constraint. It technically wouldn't
                // be incorrect to keep it, but it would make it a little harder for LLVM to optimize the register usage.
                if let Some(index) = duplicate_index {
                    Self::swap_remove_variable(bridge_variables_in, BridgeVariable {
                        ident: self.bridge_ident,
                        llvm_constraint: (format!("{}", index), Span::call_site()) // The span doesn't matter here.
                    });
                }
            },
            
            LetBridgeKeyword::InOut => {
                let mut index = bridge_variables_out.len();
                let span = self.constraint_string.span();
                if let Some(unexpected_index) = Self::push_variable(bridge_variables_out, BridgeVariable {
                            ident: self.bridge_ident,
                            llvm_constraint: (String::from("=") + self.constraint_string.value().as_str(), span)
                        }) {
                    index = unexpected_index;
                }
                Self::push_variable(bridge_variables_in, BridgeVariable {
                    ident: self.bridge_ident,
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

struct ClobberStmt {
    constraint_string: LitStr
}

impl Synom for ClobberStmt {
    named!(parse -> Self, do_parse!(
        expect!(clobber) >>
        constraint_string: map!(parens!(
            syn!(LitStr)
        ), |parens| parens.1) >>
        punct!(;) >>
        (ClobberStmt {
            constraint_string
        })
    ));
    
    fn description() -> Option<&'static str> {
        Some("clobber declaration")
    }
}

impl ToTokens for ClobberStmt {
    fn to_tokens(&self, _: &mut Tokens) {
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

#[derive(Clone, Copy)]
enum LetBridgeKeyword {
    In,
    Out,
    InOut
}

impl LetBridgeKeyword {
    named!(parse_mutable -> Self, alt!(
          expect!(out) => { |_| LetBridgeKeyword::Out }
        | expect!(inout) => { |_| LetBridgeKeyword::InOut }
    ));
    
    named!(parse_immutable -> Self, alt!(
        expect!(in) => { |_| LetBridgeKeyword::In }
    ));
}

struct InnerAsmBlock {
    options: Punctuated<LitStr, Token![,]>,
    asm_unchanged: Option<LitStr>,
    
    bridge_variables_out: Vec<BridgeVariable>,
    bridge_variables_in: Vec<BridgeVariable>,
    clobbers: HashSet<Clobber>
}

impl Synom for InnerAsmBlock {
    named!(parse -> Self, do_parse!(
        expect!(asm) >>
        options: map!(option!(map!(
            parens!(
                call!(Punctuated::<LitStr, Token![,]>::parse_separated)
            ),
            |parens| parens.1 // Extract the stuff inside the parentheses.
        )), |punctuated| punctuated.unwrap_or(Punctuated::new())) >>
        asm_unchanged: map!(braces!(option!(syn!(LitStr))), |braces| braces.1) >>
        (InnerAsmBlock {
            options,
            asm_unchanged,
            
            bridge_variables_out: Vec::new(),
            bridge_variables_in: Vec::new(),
            clobbers: HashSet::new()
        })
    ));
    
    fn description() -> Option<&'static str> {
        Some("asm block")
    }
}

impl ToTokens for InnerAsmBlock {
    fn to_tokens(&self, tokens: &mut Tokens) {
        // Emit a standard (albeit unstable) `asm!` macro.
        
        if let Some(ref asm_unchanged) = self.asm_unchanged {
            let asm_span = asm_unchanged.span();
            
            // Replace every occurrence of `$<ident>` in the ASM code with the appropriate `$0`, `$1`, etc.
            let llvm_asm = self.replace_identifiers(asm_unchanged.value().as_str(), asm_span);
            
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
    fn replace_identifiers(&self, orig: &str, span: Span) -> String {
        let mut result = String::new();
        let mut chars = orig.chars();
        while let Some(c) = chars.next() {
            result.push(c);
            if c == '$' {
                let rest = chars.as_str();
                if let Some(c2) = chars.next() {
                    if c2 == '$' {
                        // Keep the "$$" around so LLVM will see it.
                        result.push(c2);
                    } else if let Some(replacement) = self.consume_translate_ident(rest, &mut chars, span) {
                        // A defined identifier was found. Replace it with its position in the register lists.
                        result.push_str(replacement.as_str());
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
        result
    }
    
    // Consumes and translates the next identifier if there is an identifier here.
    // When this is called, `chars` should be one character ahead of `orig`.
    fn consume_translate_ident(&self, orig: &str, chars: &mut Chars, span: Span) -> Option<String> {
        let output_regs_count = self.bridge_variables_out.len();
        if let Some((ident, length)) = Self::parse_ident_at_start(orig) {
            // There's a valid identifier here. Let's see if it corresponds to a bridge variable.
            if let Some(index) = Self::find_var_by_ident(&self.bridge_variables_out, &ident) {
                // Found the identifier in the `out` bridge variables.
                if length > 1 {
                    chars.nth(length - 2); // Skip past the identifier.
                }
                Some(format!("{}", index))
            } else if let Some(index) = Self::find_var_by_ident(&self.bridge_variables_in, &ident) {
                // Found the identifier in the `in` bridge variables.
                if length > 1 {
                    chars.nth(length - 2); // Skip past the identifier.
                }
                Some(format!("{}", index + output_regs_count))
            } else {
                // Couldn't find the identifier anywhere. Issue a warning.
                if cfg!(all(feature = "nightly", feature = "proc-macro")) {
                    warn(span, format!("unrecognized bridge variable `{}`", ident));
                    help(span, "it must be declared in this `rusty_asm` block with `in`, `out`, or `inout`");
                }
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
}

#[derive(Clone)]
struct BridgeVariable {
    ident: Ident,
    llvm_constraint: (String, Span)
}

impl BridgeVariable {
    fn constraint_as_tokens(&self) -> Tokens {
        let constraint = LitStr::new(self.llvm_constraint.0.as_str(), self.llvm_constraint.1);
        let ident = self.ident;
        quote!(#constraint(#ident))
    }
    
    fn bad_duplicate_of(&self, other: &Self) -> bool {
        // Removing duplicate identifiers is a matter of memory safety--it's dangerous (and maybe disallowed by the
        // compiler) to have two output registers linked to the same Rust variable.
        format!("{}", self.ident) == format!("{}", other.ident)
    }
}

#[derive(Clone)]
struct Clobber {
    llvm_constraint: (String, Span)
}

impl Clobber {
    fn constraint_as_lit_str(&self) -> LitStr {
        let lit = LitStr::new(self.llvm_constraint.0.as_str(), self.llvm_constraint.1);
        lit
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

#[cfg(all(feature = "nightly", feature = "proc-macro"))]
fn warn<T: Into<String>>(span: Span, message: T) {
    span.unstable().warning(message);
}

#[cfg(not(all(feature = "nightly", feature = "proc-macro")))]
fn warn<T: Into<String>>(_: Span, _: T) {}

#[cfg(all(feature = "nightly", feature = "proc-macro"))]
fn help<T: Into<String>>(span: Span, message: T) {
    span.unstable().help(message);
}

#[cfg(not(all(feature = "nightly", feature = "proc-macro")))]
fn help<T: Into<String>>(_: Span, _: T) {}
