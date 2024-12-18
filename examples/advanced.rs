//
// Copyright (c) 2023,2024 Piotr Stolarz
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

fn print_usage() {
    eprintln!(
        "Usage: {} [OPTION]... [--] FILE1 [FILE2]",
        std::env::args().next().unwrap()
    );
    println!(
        r"
Available options:
-a, --long_a        No value option
-b, --long_b=INT    Option with integer value, range [-10..10]
-c, --long_c=STR    Option with string value
-d                  Short option with string value
    --long_e=STR    Long option with string value
-h, --help          Print this help

All options are optional. FILE1 is required, FILE2 is not.
Use -- separator to avoid ambiguity if file name starts with '-'.
"
    )
}

#[derive(Debug)]
struct Options {
    a_opt: Option<()>,
    b_opt: Option<i32>,
    c_opt: Option<String>,
    d_opt: Option<String>,
    e_opt: Option<String>,
    file1: Option<String>,
    file2: Option<String>,
    help: Option<()>,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            a_opt: None,
            b_opt: None,
            c_opt: None,
            d_opt: None,
            e_opt: None,
            file1: None,
            file2: None,
            help: None,
        }
    }
}

#[allow(unused_imports)]
fn process_cmdopts(opts: &mut Options) -> Result<(), ParseError> {
    use std::cell::Cell;
    use CmdOpt::*;
    use InfoCode::*;
    use ParseError::*;
    use ProcessCode::*;

    // processed option id
    let opt_id = Cell::new('h');

    // file parsing index (1-based), 0 for option parsing mode
    let mut file_i = 0;

    parse_opts(
        |opt, constr| match opt {
            &Short(c) => match c {
                'a' | 'h' => {
                    opt_id.set(c);
                    NoValueOpt
                }
                'b' | 'c' | 'd' => {
                    opt_id.set(c);
                    ValueOpt
                }
                '-' => {
                    constr.not_in_group();
                    opt_id.set('-');
                    NoValueOpt
                }
                _ => InfoCode::InvalidOpt,
            },
            Long(s) => match s.as_str() {
                "long_a" => {
                    opt_id.set('a');
                    NoValueOpt
                }
                "long_b" => {
                    opt_id.set('b');
                    ValueOpt
                }
                "long_c" => {
                    opt_id.set('c');
                    ValueOpt
                }
                "long_e" => {
                    opt_id.set('e');
                    ValueOpt
                }
                "help" => {
                    opt_id.set('h');
                    NoValueOpt
                }
                _ => InfoCode::InvalidOpt,
            },
        },
        |opt, val| {
            // if true, mode needs to be switched at the return of the handler
            let mut switch_mode = false;

            // 1st standalone value switches the parser into files parsing mode
            if file_i <= 0 && opt.is_none() {
                file_i = 1;
                switch_mode = true;
            }

            if file_i <= 0 {
                //
                // Options parser
                //

                // Options w/o associated value
                //
                let mut handled = true;

                match opt_id.get() {
                    // print help and exit
                    'h' => {
                        opts.help = Some(());
                        return Ok(ProcessCode::Break);
                    }
                    '-' => {
                        file_i = 1;
                        return Ok(ProcessCode::ToggleParsingMode);
                    }
                    'a' => {
                        opts.a_opt = Some(());
                    }
                    _ => {
                        handled = false;
                    }
                }
                if handled {
                    return Ok(ProcessCode::Continue);
                }

                // Options w/associated string value
                //
                let val_str = &val.as_ref().unwrap().val;
                handled = true;

                match opt_id.get() {
                    'c' => {
                        opts.c_opt = Some(val_str.clone());
                    }
                    'd' => {
                        opts.d_opt = Some(val_str.clone());
                    }
                    'e' => {
                        opts.e_opt = Some(val_str.clone());
                    }
                    _ => {
                        handled = false;
                    }
                }
                if handled {
                    return Ok(ProcessCode::Continue);
                }

                // Options w/associated int value
                //
                let opt_ref = opt.as_ref().unwrap();

                let val_i: i32 = val_str.parse().map_err(|_| {
                    ParseError::InvalidOpt(opt_ref.clone(), "Integer expected".to_string())
                })?;

                match opt_id.get() {
                    'b' => {
                        if val_i >= -10 && val_i <= 10 {
                            opts.b_opt = Some(val_i);
                        } else {
                            return Err(ParseError::InvalidOpt(
                                opt_ref.clone(),
                                "Integer in range [-10..10] required".to_string(),
                            ));
                        }
                    }
                    _ => {}
                }

                Ok(ProcessCode::Continue)
            } else {
                //
                // Files parser
                //
                let val_str = &val.as_ref().unwrap().val;

                match file_i {
                    1 => {
                        opts.file1 = Some(val_str.clone());
                    }
                    2 => {
                        opts.file2 = Some(val_str.clone());
                    }
                    _ => {
                        return Err(ParseError::GenericErr(
                            "Invalid number of files".to_string(),
                        ));
                    }
                }
                file_i += 1;

                if switch_mode {
                    Ok(ToggleParsingMode)
                } else {
                    Ok(Continue)
                }
            }
        },
    )
}

pub fn main() -> Result<(), i32> {
    // CLI provided options
    let mut opts: Options = Default::default();

    let rc = process_cmdopts(&mut opts);
    if rc.is_ok() {
        if std::env::args().len() <= 1 || opts.help.is_some() {
            print_usage();
        } else if opts.file1.is_none() {
            eprintln!("[ERROR] FILE1 required");
            return Err(2);
        } else {
            println!("{:?}", opts);
        }
    } else {
        eprintln!("[ERROR] {}", rc.unwrap_err());
        return Err(1);
    }
    Ok(())
}
