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

#![feature(proc_macro_hygiene, asm)]
extern crate rusty_asm;
use rusty_asm::rusty_asm;

//extern crate compiletest_rs as compiletest;

//use std::path::Path;

#[test]
fn empty() {
    rusty_asm! {}
}

#[test]
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn nop() {
    unsafe {
        rusty_asm! {
            asm("volatile") {
                "nop"
            }
        }
    }
}

#[test]
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn add() {
    assert_eq!(util::add(0, 0), 0);
    assert_eq!(util::add(3, 0), 3);
    assert_eq!(util::add(0, 4), 4);
    assert_eq!(util::add(1, 5), 6);
    assert_eq!(util::add(17, 17), 34);
    assert_eq!(util::add(3, usize::max_value()), 2);
    assert_eq!(util::add(50, -10isize as usize), 40);
}

#[test]
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn inner_block() {
    unsafe {
        rusty_asm! {
            let mut sum: inout("r") = 0usize;
            for i in 0 .. 20 {
                let i: in("r") = (i + 1) as usize;
                asm("intel") {
                    "add $sum, $i"
                }
            }
            assert_eq!(sum, 210);
        }
    }
}

#[test]
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn explicit_types() {
    assert_eq!(util::sub_u8(0, 0), 0);
    assert_eq!(util::sub_u8(10, 2), 8);
    assert_eq!(util::sub_u8(2, 10), -8);
    assert_eq!(util::sub_u8(0, u8::max_value()), -(u8::max_value() as i16));
}

#[test]
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn clobbers() {
    for x in 0 .. 20 {
        for y in 1 .. 21 {
            assert_eq!(util::div(x, y) as u64, x / (y as u64));
        }
    }
}

#[test]
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn shadow_bridge_var() {
    unsafe {
        rusty_asm! {
            let mut a: u32: inout("r") = 0;
            let b: in("r") = 31u32;
            asm() { // Empty parentheses here are acceptable.
                "addl $b, $a"
            }
            assert_eq!(b, 31);
            let b: in("r") = 15u32;
            asm {
                "subl $b, $a"
            }
            assert_eq!(a, 0 + 31 - 15);
            assert_eq!(b, 15);
        }
    }
}

#[test]
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn literal_dollar() {
    unsafe {
        rusty_asm! {
            let c: u8: out("r");
            asm {
                "movb $$0x40, $c"
            }
            assert_eq!(c, 0x40);
        }
    }
}

#[test]
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn bad_identifiers() {
    unsafe {
        rusty_asm! {
            let mut x: u32: inout("r") = 2;
            // The dollar sign here should produce a warning but still work.
            asm("intel") {
                "shl $0, 3"
            }
            assert_eq!(x, 2 << 3);
        }
    }
}

#[test]
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn inout_out_inout() {
    unsafe {
        rusty_asm! {
            let mut foo: u32: inout("r") = 8;
            asm {
                "addl $foo, $foo"
            }
            assert_eq!(foo, 16);
            let foo: u32: out("r");
            asm {
                "movl $$0x20, $foo"
            }
            assert_eq!(foo, 32);
            let mut foo: inout("r") = foo;
            asm {
                "addl $foo, $foo"
            }
            assert_eq!(foo, 64);
        }
    }
}

#[test]
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn clobber_overlap() {
    unsafe {
        rusty_asm! {
            // Make sure the conflicting clobber is automatically removed, not the output.
            let mut eax: u32: out("{eax}");
            clobber("eax");
            asm {
                "movl $$0x14, %eax"
            }
            assert_eq!(eax, 0x14);
            asm {
                "movl $$0x28, %eax"
            }
            assert_eq!(eax, 0x28);
        }
        rusty_asm! {
            // Try it again with the output and clobber switched.
            clobber("eax");
            let mut eax: u32: out("{eax}");
            asm {
                "movl $$0x14, %eax"
            }
            assert_eq!(eax, 0x14);
            asm {
                "movl $$0x28, %eax"
            }
            assert_eq!(eax, 0x28);
        }
    }
}

// TODO: This test can be uncommented whenever compiletest_rs starts expanding macros.
/*#[test]
fn compile_fail() {
    let mut config = compiletest::Config::default();

    config.mode = "compile-fail".parse().unwrap();
    config.src_base = Path::new("tests").join("compile-fail");
    config.link_deps(); // Give dependency paths to rustc
    config.clean_rmeta();

    compiletest::run_tests(&config);
}*/

mod util {
    use rusty_asm::rusty_asm;

    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    pub fn add(a: usize, b: usize) -> usize {
        unsafe {
            rusty_asm! {
                ; ;; // Extra semicolons should be ignored.
                let mut a: inout("r") = a;;
                let b: in("r") = b;

                ;asm("intel") {
                    "add $a, $b"
                } ;

                a
            }
        }
    }

    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    pub fn sub_u8(a: u8, b: u8) -> i16 {
        unsafe {
            rusty_asm! {
                let mut a: i16: inout("r") = a.into();
                let b: i16: in("r") = b.into();

                asm {
                    "subw $b, $a"
                }

                a
            }
        }
    }

    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    pub fn div(a: u64, b: u32) -> u32 {
        unsafe {
            rusty_asm! {
                // We can't divide by zero.
                assert_ne!(b, 0);

                let _dividend_lo: in("{eax}") = (a & 0xffff_ffff) as u32;
                let mut _dividend_hi: in("{edx}") = ((a >> 32) & 0xffff_ffff) as u32;
                let divisor: in("r") = b;
                let quotient: out("{eax}");
                clobber("edx"); // Ignoring the remainder

                // If we didn't do this check here, the `asm` block might cause a crash that would
                // bypass Rust's `panic` mechanism. The x86 DIV instruction causes a hardware-level
                // divide-by-zero exception if the quotient doesn't fit in the target register (32
                // bits in this case).
                assert!(a < (b as u64) << 32);

                asm("intel") {
                    "div $divisor"
                }

                quotient
            }
        }
    }
}
