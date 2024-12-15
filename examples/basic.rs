//
// Copyright (c) 2023 Piotr Stolarz
// GNU-like Command line options parser.
//
// Distributed under the 2-clause BSD License (the License)
// see accompanying file LICENSE for details.
//
// This software is distributed WITHOUT ANY WARRANTY; without even the
// implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
// See the License for more information.
//

use cmdopts::{parse_opts, CmdOpt, InfoCode, ParseError, ProcessCode};

#[allow(unused_imports)]
pub fn main() {
    use std::cell::Cell;
    use CmdOpt::*;
    use InfoCode::*;
    use OptId::*;
    use ParseError::*;
    use ProcessCode::*;

    #[derive(Clone, Copy)]
    enum OptId {
        OptA,
        OptB,
    }
    impl Default for OptId {
        fn default() -> Self {
            OptA
        }
    }
    let opt_id: Cell<OptId> = Default::default();

    let rc = parse_opts(
        // Options info provider
        //
        |opt, _| {
            match opt {
                Short(c) => {
                    match c {
                        // -a, option w/o value
                        'a' => {
                            opt_id.set(OptA);
                            NoValueOpt
                        }
                        // -b, option w/value
                        'b' => {
                            opt_id.set(OptB);
                            ValueOpt
                        }
                        _ => InfoCode::InvalidOpt,
                    }
                }
                Long(s) => {
                    match s.as_str() {
                        // long counterpart of the short options
                        "long_a" => {
                            opt_id.set(OptA);
                            NoValueOpt
                        }
                        "long_b" => {
                            opt_id.set(OptB);
                            ValueOpt
                        }
                        _ => InfoCode::InvalidOpt,
                    }
                }
            }
        },
        // Options handler
        //
        |opt, val| {
            // all parsed tokens must form options
            opt.as_ref()
                .ok_or(GenericErr("Non-option detected".to_string()))?;

            match opt_id.get() {
                OptA => {
                    println!("A option");
                }
                OptB => {
                    println!("B option with {}", val.as_ref().unwrap().val);
                }
            };

            Ok(ProcessCode::Continue)
        },
    );

    if rc.is_err() {
        eprintln!("[ERROR] {}", rc.unwrap_err());
    }
}
