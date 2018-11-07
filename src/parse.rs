// Copyright (c) 2018 Jeremy Davis (jeremydavis519@gmail.com)
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

use std::collections::HashSet;
use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::str::Chars;

use proc_macro2::{Span, TokenStream, TokenTree, Delimiter};
use quote::{ToTokens, TokenStreamExt};
use syn::{Expr, Ident, LitStr, Type};
use syn::parse::{self, Parse, ParseBuffer, ParseStream};
use syn::punctuated::Punctuated;
use syn::token::Brace;
use unicode_xid::UnicodeXID;

#[derive(Debug)]
pub struct RustyAsmBlock {
    contents: Vec<RustyAsmPiece>
}

mod keyword {
    custom_keyword!(out);
    custom_keyword!(inout);
    custom_keyword!(clobber);
    custom_keyword!(asm);
}

impl Parse for RustyAsmBlock {
    // Parses the inside of the top-level block (i.e. all the contents of a `rusty_asm!` invocation.
    fn parse(input: ParseStream) -> parse::Result<Self> {
        let bridge_vars_out = Vec::<BridgeVar>::new();
        let bridge_vars_in = Vec::<BridgeVar>::new();
        let clobbers = HashSet::<Clobber>::new();
        Self::parse_subblock(input, bridge_vars_out, bridge_vars_in, clobbers)
    }
}

impl ToTokens for RustyAsmBlock {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let contents = &self.contents;
        let temp_tokens = quote!({
            #(#contents)*
        });
        tokens.append_all(temp_tokens);
    }
}

impl RustyAsmBlock {
    // Parses the inside of a block that is contained within another rusty_asm block. The
    // parameters allow bridge variables and clobbers from outer scopes to be used in inner scopes.
    fn parse_subblock(input: ParseStream, mut bridge_vars_out: Vec<BridgeVar>, mut bridge_vars_in: Vec<BridgeVar>,
            mut clobbers: HashSet<Clobber>) -> parse::Result<Self> {
        let mut contents = Vec::new();
        while !input.is_empty() {
            let piece = RustyAsmPiece::parse(input, &mut bridge_vars_out, &mut bridge_vars_in, &mut clobbers)?;
            contents.push(piece);
        }

        Ok(RustyAsmBlock { contents })
    }
}

#[derive(Debug)]
enum RustyAsmPiece {
    RustyAsmBlock(Brace, RustyAsmBlock),
    BridgeVarDecl(BridgeVarDecl),
    ClobberDecl(ClobberDecl),
    AsmBlock(AsmBlock),
    TokenTrees(Vec<TokenTree>)
}

impl RustyAsmPiece {
    fn parse(input: ParseStream, bridge_vars_out: &mut Vec<BridgeVar>, bridge_vars_in: &mut Vec<BridgeVar>,
            clobbers: &mut HashSet<Clobber>) -> parse::Result<Self> {
        if input.peek(Brace) {
            // A block
            let contents;
            let brace = braced!(contents in input);
            let block = RustyAsmBlock::parse_subblock(
                &contents,
                bridge_vars_out.clone(),
                bridge_vars_in.clone(),
                clobbers.clone()
            )?;
            Ok(RustyAsmPiece::RustyAsmBlock(brace, block))
        } else if input.peek(Token![let]) {
            // Possibly a bridge variable declaration
            if let Ok(decl) = input.fork().parse::<BridgeVarDecl>() {
                // TODO: We're re-parsing an unbounded number of tokens here. Avoid this if possible.
                let _ = input.parse::<BridgeVarDecl>();
                decl.push_bridge_var(bridge_vars_out, bridge_vars_in);
                Ok(RustyAsmPiece::BridgeVarDecl(decl))
            } else {
                // Not a bridge variable
                let (tt, _) = input.cursor().token_tree().unwrap();
                let _ = input.parse::<Token![let]>();
                Ok(RustyAsmPiece::TokenTrees(vec![tt]))
            }
        } else if input.peek(keyword::clobber) {
            // Possibly a clobber declaration
            if let Ok(decl) = input.fork().parse::<ClobberDecl>() {
                // TODO: We're re-parsing an unbounded number of tokens here. Avoid this if possible.
                let _ = input.parse::<ClobberDecl>();
                decl.push_clobber(clobbers);
                Ok(RustyAsmPiece::ClobberDecl(decl))
            } else {
                // Not a clobber
                let (tt, _) = input.cursor().token_tree().unwrap();
                let _ = input.parse::<keyword::clobber>();
                Ok(RustyAsmPiece::TokenTrees(vec![tt]))
            }
        } else if input.peek(keyword::asm) {
            // Possibly an ASM block
            if let Ok(mut block) = AsmBlock::parse(
                        &input.fork(),
                        bridge_vars_out.clone(),
                        bridge_vars_in.clone(),
                        clobbers.clone()
                    ) {
                // TODO: We're re-parsing an unbounded number of tokens here. Avoid this if possible.
                let _ = AsmBlock::parse(input, bridge_vars_out.clone(), bridge_vars_in.clone(), clobbers.clone());
                block.fix_overlapping_clobbers();
                Ok(RustyAsmPiece::AsmBlock(block))
            } else {
                // Not an ASM block
                let (tt, _) = input.cursor().token_tree().unwrap();
                let _ = input.parse::<keyword::asm>();
                Ok(RustyAsmPiece::TokenTrees(vec![tt]))
            }
        } else if input.peek(Token![if]) || input.peek(Token![while]) {
            // We don't support `if let` or `while let`, so avoid parsing any tokens until the upcoming block.
            let tts = input.step(|cursor| {
                let mut tts = Vec::new();
                let mut rest = *cursor;
                while let Some((tt, next)) = rest.token_tree() {
                    match tt {
                        TokenTree::Group(ref group) if group.delimiter() == Delimiter::Brace => return Ok((tts, rest)),
                        _ => {
                            tts.push(tt);
                            rest = next;
                        }
                    };
                }
                // The block never came.
                Err(cursor.error("unexpected end of input"))
            })?;
            Ok(RustyAsmPiece::TokenTrees(tts))
        } else {
            // Any other token tree
            let tt = input.step(|cursor| cursor.token_tree().ok_or(cursor.error("unexpected end of input")))?;
            Ok(RustyAsmPiece::TokenTrees(vec![tt]))
        }
    }
}

impl ToTokens for RustyAsmPiece {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            RustyAsmPiece::RustyAsmBlock(brace, block) => brace.surround(tokens, |tokens| block.to_tokens(tokens)),
            RustyAsmPiece::BridgeVarDecl(decl)         => decl.to_tokens(tokens),
            RustyAsmPiece::ClobberDecl(decl)           => decl.to_tokens(tokens),
            RustyAsmPiece::AsmBlock(block)             => block.to_tokens(tokens),
            RustyAsmPiece::TokenTrees(tts)             => {
                for tt in tts {
                    tt.to_tokens(tokens);
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
struct BridgeVarDecl {
    let_keyword: Token![let],
    mut_keyword: Option<Token![mut]>,
    ident: Ident,
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

impl Parse for BridgeVarDecl {
    fn parse(input: ParseStream) -> parse::Result<Self> {
        // `let [mut] <identifier>:`
        let let_keyword = input.parse::<Token![let]>()?;
        let mut_keyword;
        if input.peek(Token![mut]) {
            mut_keyword = input.parse::<Token![mut]>().ok();
        } else {
            mut_keyword = None;
        }
        let ident = input.parse::<Ident>()?;
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

        Ok(BridgeVarDecl {
            let_keyword,
            mut_keyword,
            ident,
            explicit_type,
            constraint_keyword,
            constraint_string,
            assignment,
            semicolon
        })
    }
}

impl ToTokens for BridgeVarDecl {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        // Emit the equivalent Rust `let` statement, keeping the original span for each token.
        self.let_keyword.to_tokens(tokens);
        if let Some(mut_keyword) = self.mut_keyword {
            mut_keyword.to_tokens(tokens);
        }
        self.ident.to_tokens(tokens);
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

impl BridgeVarDecl {
    fn push_bridge_var(&self, bridge_vars_out: &mut Vec<BridgeVar>, bridge_vars_in: &mut Vec<BridgeVar>) {
        match self.constraint_keyword {
            ConstraintKeyword::In => {
                Self::push_var(bridge_vars_in, BridgeVar {
                    ident: self.ident.clone(),
                    llvm_constraint: (self.constraint_string.value(), self.constraint_string.span())
                });
            },

            ConstraintKeyword::Out => {
                let duplicate_index = Self::push_var(bridge_vars_out, BridgeVar {
                    ident: self.ident.clone(),
                    llvm_constraint: (String::from("=") + self.constraint_string.value().as_str(), self.constraint_string.span())
                });

                // If a duplicate was found, and it was an `inout` variable, remove the `in` constraint. It technically wouldn't
                // be incorrect to keep it, but it would make it a little harder for LLVM to optimize the register usage.
                if let Some(index) = duplicate_index {
                    Self::swap_remove_var(bridge_vars_in, BridgeVar {
                        ident: self.ident.clone(),
                        llvm_constraint: (format!("{}", index), Span::call_site()) // The span doesn't matter here.
                    });
                }
            },

            ConstraintKeyword::InOut => {
                let mut index = bridge_vars_out.len();
                let span = self.constraint_string.span();
                if let Some(unexpected_index) = Self::push_var(bridge_vars_out, BridgeVar {
                            ident: self.ident.clone(),
                            llvm_constraint: (String::from("=") + self.constraint_string.value().as_str(), span)
                        }) {
                    // If a duplicate `out` variable was found, use that index instead of a new one.
                    index = unexpected_index;
                }
                Self::push_var(bridge_vars_in, BridgeVar {
                    ident: self.ident.clone(),
                    llvm_constraint: (format!("{}", index), span) // Linked to the output constraint for the same variable
                });
            }
        }
    }

    fn push_var(vec: &mut Vec<BridgeVar>, var: BridgeVar) -> Option<usize> {
        // First, check for a duplicate and overwrite it if it's found.
        // TODO: It might be worthwhile to use a HashSet to make finding duplicates faster.
        for (i, other) in vec.iter_mut().enumerate() {
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
    fn swap_remove_var(vec: &mut Vec<BridgeVar>, var: BridgeVar) {
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
struct ClobberDecl {
    constraint_string: LitStr
}

impl Parse for ClobberDecl {
    fn parse(input: ParseStream) -> parse::Result<Self> {
        input.parse::<keyword::clobber>()?;
        let content;
        parenthesized!(content in input);
        let constraint_string = content.parse::<LitStr>()?;
        input.parse::<Token![;]>()?;
        
        Ok(ClobberDecl { constraint_string })
    }
}

impl ToTokens for ClobberDecl {
    fn to_tokens(&self, _: &mut TokenStream) {
        // We have nothing to do here. A clobber doesn't correspond to any Rust statements.
    }
}

impl ClobberDecl {
    fn push_clobber(&self, clobbers: &mut HashSet<Clobber>) {
        clobbers.insert(Clobber {
            llvm_constraint: (self.constraint_string.value(), self.constraint_string.span())
        });
    }
}

#[derive(Debug, Clone)]
struct AsmBlock {
    options: Punctuated<LitStr, Token![,]>,
    asm_unchanged: Option<LitStr>,

    bridge_vars_out: Vec<BridgeVar>,
    bridge_vars_in: Vec<BridgeVar>,
    clobbers: HashSet<Clobber>
}

impl AsmBlock {
    fn parse(input: ParseStream, bridge_vars_out: Vec<BridgeVar>, bridge_vars_in: Vec<BridgeVar>,
            clobbers: HashSet<Clobber>) -> parse::Result<Self> {
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

        Ok(AsmBlock {
            options,
            asm_unchanged,

            bridge_vars_out,
            bridge_vars_in,
            clobbers
        })
    }
}

impl ToTokens for AsmBlock {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        // Emit a standard (albeit unstable) `asm!` macro.

        if let Some(ref asm_unchanged) = self.asm_unchanged {
            let asm_span = asm_unchanged.span();

            // Replace every occurrence of `$<ident>` in the ASM code with the appropriate `$0`, `$1`, etc.
            let (llvm_asm, used_idents) = self.replace_identifiers(asm_unchanged.value().as_str(), asm_span);

            // Warn the programmer if one of the available bridge variables wasn't referenced in the ASM code.
            for var in self.bridge_vars_out.iter().chain(self.bridge_vars_in.iter()) {
                if !used_idents.contains(&var.ident.to_string()) {
                    warn(var.ident.span(), "bridge variable not used");
                    help(asm_span, "in this `asm` block");
                }
            }

            let asm_str = LitStr::new(llvm_asm.as_str(), asm_span);
            let constraints_out = self.bridge_vars_out.iter().map(|v| v.constraint_as_tokens());
            let constraints_in = self.bridge_vars_in.iter().map(|v| v.constraint_as_tokens());
            let constraints_clobber = self.clobbers.iter().map(|v| v.constraint_as_lit_str());
            let options = &self.options;

            let temp_tokens = quote!(asm!(#asm_str : #(#constraints_out),* : #(#constraints_in),* : #(#constraints_clobber),* : #(#options),*););
            tokens.append_all(temp_tokens);
        }
    }
}

impl AsmBlock {
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
        let output_regs_count = self.bridge_vars_out.len();
        if let Some((ident, length)) = Self::parse_ident_at_start(orig) {
            // There's a valid identifier here. Let's see if it corresponds to a bridge variable.
            if let Some(index) = Self::find_var_by_ident(&self.bridge_vars_out, &ident) {
                // Found the identifier in the `out` bridge vars.
                if length > 1 {
                    chars.nth(length - 2); // Skip past the identifier.
                }
                Some((ident, format!("{}", index)))
            } else if let Some(index) = Self::find_var_by_ident(&self.bridge_vars_in, &ident) {
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

    fn find_var_by_ident(vars: &Vec<BridgeVar>, ident_string: &String) -> Option<usize> {
        for (i, var) in vars.iter().enumerate() {
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
        for var in self.bridge_vars_out.iter() {
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
        for (i, var) in self.bridge_vars_in.clone().iter().enumerate() {
            if let Some(reg) = var.explicit_register() {
                for clobber in self.clobbers.clone().iter() {
                    if clobber.constraint_as_str() == reg {
                        // Add the output and link the input to it.
                        let out_constraint = format!("={}", var.constraint_as_str());
                        let in_constraint = format!("{}", self.bridge_vars_out.len());
                        self.bridge_vars_out.push(BridgeVar {
                            ident: var.ident.clone(),
                            llvm_constraint: (out_constraint, var.constraint_span())
                        });
                        self.bridge_vars_in.remove(i);
                        self.bridge_vars_in.push(BridgeVar {
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
struct BridgeVar {
    ident: Ident,
    llvm_constraint: (String, Span)
}

impl BridgeVar {
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
