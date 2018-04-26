# rusty-asm

A layer of syntactic sugar between Rust and inline assembly

Rust currently has the [`asm!`] macro for writing inline ASM within a function defined in Rust. It uses the same basic
format as GCC uses for its own inline ASM--and that format is _awful_. I have yet to hear of anyone who actually likes it.
Here's a small example, taken from [the OSDev wiki] and translated into Rust:

[`asm!`]: https://doc.rust-lang.org/1.12.0/book/inline-assembly.html
[the OSDev wiki]: https://wiki.osdev.org/Inline_Assembly/Examples

```no_run
# #![feature(asm)]
// Retrieves a value from memory in a different segment than the one currently being used (x86[-64])
unsafe fn farpeekl(segment_selector: u16, offset: *const u32) -> u32 {
    let ret: u32;
    asm!("
        push %fs
        mov $1, %fs
        mov %fs:($2), $0
        pop %fs
    "   : "=r"(ret) : "r"(segment_selector), "r"(offset)
    );
    ret
}
# fn main() {}
```

(This example actually looks a little cleaner in my opinion than it does when written for GCC, but it could still use some work.)

The `asm!` macro is currently an unstable, nightly-only feature. From what I've seen, there are several reasons, but one of
them is the syntax. It's too easy to forget the precise order of things (which come first: inputs or outputs?), and parts of
it are needlessly redundant. Using `"=r"`, `"r"`, or `"~r"` means the register is, respectively, an output, and input, or
clobbered, but the different types also have to be separated by colons. So using `asm!`, the programmer has to remember both
ways to tell the compiler what it should expect to happen to each register.

This crate attempts to improve the syntax surrounding inline ASM so that it's both easier to read and easier to write without
looking up the required format every time. It works by using a procedural macro (1) to overload Rust's `let` statements, making
variables capable of storing information about how they'll be used in upcoming inline ASM blocks, and (2) to parse `asm`
blocks that allow variables defined with the new syntax to be used directly in the ASM code.

# Setup

To use this crate, add the following to `Cargo.toml`:

```toml
[dependencies]
rusty-asm = "0.0.1"
```

Then reference the crate in your main source file and activate the features you'll need:

```ignore
#![feature(proc_macro)]
extern crate rusty_asm;
use rusty_asm::rusty_asm; // Because who wants to write `rusty_asm::rusty_asm!`?
# fn main() {}
```

# Basic Syntax

In the place where you want to add some inline ASM, call `rusty_asm!` like so:

```ignore
# #![feature(proc_macro)]
# #![feature(asm)]
# extern crate rusty_asm;
# use rusty_asm::rusty_asm;
# fn main() {
# unsafe {
rusty_asm! {
    // (arbitrary Rust statements go here)
    
    asm (/* maybe some options in here */) {
        // (insert your ASM code here)
    }
    
    // (possibly some cleanup code here)
}
# }
# }
```

The contents of the `asm` block need to be a string literal to make sure that Rust's parser doesn't mess up the
formatting. (Macros currently don't have access to whitespace information.) See the examples below for more specifics
about how it should look.

Also, it's possible to have multiple `asm` blocks in the same `rusty_asm!` block, in case you want to reuse your bridge
variables (see below).

# Bridge Variables

A _bridge variable_ is a variable that bridges the gap between Rust and ASM by incorporating the input/ouput/clobber
information in its definition. They can only be defined inside `rusty_asm!` blocks, and because the macro makes a new scope,
they are dropped when execution leaves those blocks (along with any other variables that are defined in the same scope). In
order to define a bridge variable, you'll need to use one of three keywords that are only valid inside `rusty_asm!` blocks:

* `in`
* `out`
* `inout`

Each of these keywords is used in a "let" statement to define a bridge variable. The exact syntax is as follows:

```text
let <identifier>: in(<constraint>) [= <expression>];
let mut <identifier>: out(<constraint>) [= <expression>];
let mut <identifier>: inout(<constraint>) [= <expression>];
```

Currently, those `mut` assignments are hard rules. The parser won't accept a mutable `in` variable or an immutable `out` or
`inout` variable. That restriction may be lifted in the future if it turns out to be an issue. The idea is that their
mutability in Rust should match their mutability in ASM.

In addition, you can specify that you'll clobber a particular register (or that you'll clobber memory) with this syntax:

```text
clobber(<constraint>);
```

where `<constraint>` is the name of a register or `"memory"`.

These statements correspond to LLVM constraints in the following way:

```text
// in, out, or inout:
<new-constraint>(<identifier>)
// clobber
<new-constraint>
```

In each case, `<new_constraint>` is equivalent to `<constraint>` except that for the `out` and `clobber` keywords, the `'='`
or `'~'` is prepended to satisfy `asm!` and LLVM. The `inout` keyword results in two new constraints: (1) the equivalent
constraint for the `out` keyword and (2) an input constraint that's tied to it.

In order to let Rust know how to work with the bridge variables, `rusty_asm!` removes the new keywords and constraints during
macro expansion, so as far as Rust knows, they're just ordinary variables with inferred types.

# The `asm` Block

When an `asm` block is encountered, it is converted directly into an asm! invocation, using all of the constraints that have
been created thus far. The `asm` block's syntax is as follows:

```text
asm [(<options>)] {
    <asm-code>
}
```

`<options>` is an optional comma-separated list of the options that would be after the 4th colon if `asm!` were being used, such
as `"volatile"`. `<asm-code>` is pure ASM code, enclosed in quotes, except that it can (and should) use the bridge variables
that have been defined above the `asm` block.

In order to reference a bridge variable from inside an `asm` block, insert `$<ident>` into the code, where `<ident>` is the
variable's identifier. As with the `asm!` macro, `$$` is the way to write an escaped dollar sign.

# The `rusty_asm!` Block and Scope

The new macro puts its entire contents inside a new scope, so that any variables defined therein are dropped at the end. Their
values can be moved to variables outside the macro's scope before it ends, using regular Rust code, if they need to be preserved.
In addition, just like any of Rust's code blocks, this one has a return value that can be used by ending the block with an
expression.

# Further Reading

There are too many platform-specific constraints and options that you can specify to list them all here. Follow these links for
more information.

* [The Rust book: Inline Assembly chapter]. Discusses what can be done with the `asm!` macro.
* [LLVM's inline assembly documentation]. Documents exactly what is allowed in LLVM inline assembly (and therefore in Rust's `asm!`
  invocations), along with platform-specific details.

[The Rust book: Inline Assembly chapter]: https://doc.rust-lang.org/1.12.0/book/inline-assembly.html
[LLVM's inline assembly documentation]: http://llvm.org/docs/LangRef.html#inline-assembler-expressions

# Usage Examples

```ignore
# #![feature(proc_macro)]
# #![feature(asm)]
# extern crate rusty_asm;
# use rusty_asm::rusty_asm;
#
# #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
// Disables interrupts on an x86 CPU.
unsafe fn disable_interrupts() {
    rusty_asm! {
        asm("volatile") { // This block has to be marked "volatile" to make sure the compiler, seeing
            cli           // no outputs and no clobbers, doesn't assume it does nothing and
        }                 // decide to "optimize" it away.
    };
}
# fn main() {}
```

```ignore
# #![cfg(any(target_arch = "x86", target_arch = "x86_64"))]
# #![feature(proc_macro)]
# #![feature(asm)]
# extern crate rusty_asm;
# use rusty_asm::rusty_asm;
#
// Shifts the hexadecimal digits of `existing` up and puts `digit` in the resulting gap.
fn append_hex_digit(existing: usize, digit: u8) -> usize {
    assert!(digit < 0x10);
    unsafe {
        rusty_asm! {
            let mut big: inout("r") = existing;
            let digit: usize = digit;
            let little: in("r") = digit;
            
            asm {"
                shll %4, $big
                orl $little, $big
            "}
            
            big
        }
    }
}

# fn main() {
assert_eq!(append_hex_digit(0, 0), 0);
assert_eq!(append_hex_digit(0, 0xf), 0xf);
assert_eq!(append_hex_digit(4, 2), 0x42);
# }
```