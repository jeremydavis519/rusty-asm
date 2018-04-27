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

//! This file contains all of the integration tests for the `rusty-asm` crate.

#![feature(proc_macro, proc_macro_non_items, asm)]
extern crate rusty_asm;
use rusty_asm::rusty_asm;

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
    let x: isize = -10;
    assert_eq!(util::add(50, x as usize), 40);
}

mod util {
    use rusty_asm::rusty_asm;
    
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    pub fn add(a: usize, b: usize) -> usize {
        unsafe {
            rusty_asm! {
                let mut a: inout("r") = a;
                let b: in("r") = b;
                
                asm("intel") {
                    "add $a, $b"
                }
                
                a
            }
        }
    }
}
