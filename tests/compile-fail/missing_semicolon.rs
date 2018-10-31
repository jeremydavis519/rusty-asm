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

fn missing_semicolon() {
    unsafe {
        let _ = rusty_asm! {
            2
            3
        };
    }
}
