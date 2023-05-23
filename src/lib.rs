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

//! GNU-like command line options parser for long and short formats. Optional
//! argument (aka option's value) may be associated with an option. The parsing
//! routine `parse_opts()` accepts two user callbacks:
//! * `opt_i()` provides parser with a context the parsed option may be used,
//! * `opt_h()` is the actual handler of the option.
//!
//! The library doesn't interpret parsed options, rather passes them to the
//! user's handler to further processing. The idea is similar to `getopt(3)`
//! and `getopt_long(3)` routines.
//!
//! # Options Format
//!
//! ## Short format
//!
//! All options starting with a single hyphen character `-` are short options.
//! For example: `-a -b -c` constitute 3 short options. These options may grouped
//! into a single block of options as `-abc`.
//!
//! If a short option requires an argument, the argument may be provided directly
//! after the option or separated by white-space(s): `-dARG` or `-d ARG`.
//!
//! If short options are grouped into a block, the last one may be provided
//! with an argument. For example: `-abcdARG` or `-abcd ARG` is equivalent to
//! `-a -b -c -d ARG`, where `-a` `-b` `-c` don't have an argument, while `-d`
//! does.
//!
//! ## Long format
//!
//! If an option starts with `--` it's long format option. For example `--help`.
//! Long options may not be formed into a group. An argument may be provided to
//! the long-format option directly after `=` character or followed by
//! white-space(s): `--config=FILE` or `--config FILE`.

use std::env;
use std::error;
use std::fmt;
use std::ops;

use CmdOpt::*;
use ParseError::*;
use ProcessCode::*;
use InfoCode::*;
use OptValSpec::*;

///
/// Command option types.
///
#[derive(Clone)]
#[derive(Debug)]
#[derive(PartialEq)]
pub enum CmdOpt {
    /// Short (single char) option.
    Short(char),

    /// Long (string) option.
    Long(String),
}

impl fmt::Display for CmdOpt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::Short(o) => write!(f, "-{}", o),
            Self::Long(o) => write!(f, "--{}", o),
        }
    }
}

///
/// Parser error codes returned by the option handler `opt_h()`.
///
#[derive(Clone)]
#[derive(Debug)]
#[derive(PartialEq)]
pub enum ParseError {
    /// Empty option found.
    EmptyOptFound,

    /// Invalid option with error description.
    InvalidOpt(CmdOpt, String),

    /// Handler may use this code to return arbitrary errors not particularly
    /// associated with some option (for which case `InvalidOpt` should be
    /// used).
    GenericErr(String)
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::EmptyOptFound => {
                write!(f, "Empty option")
            },
            Self::InvalidOpt(opt, desc) => {
                write!(f, "{}: {}", opt.to_string(), desc)?;
                Ok(())
            },
            Self::GenericErr(desc) => {
                write!(f, "{}", desc)?;
                Ok(())
            },
        }
    }
}

impl error::Error for ParseError {}

///
/// Option process codes returned by the option handler `opt_h()`.
///
#[derive(Clone)]
#[derive(Copy)]
#[derive(Debug)]
#[derive(PartialEq)]
pub enum ProcessCode {
    /// Continue the parsing process in the current parsing mode.
    Continue,

    /// Break further parsing with success.
    Break,

    /// Switch the parser between *values-parsing-mode* and *options-parsing-mode*
    /// then continue the parsing process. The activated mode is valid until
    /// `ToggleParsingMode` is returned by the handler or end of options
    /// is reached.
    ///
    /// - *options-parsing-mode* - the parser recognizes options along with
    ///   their values and passes them to the handler. This is the default
    ///   parsing mode.
    ///
    /// - *values-parsing-mode* - the parser treats all parsed tokens as values
    ///   (independent tokens) and passes them to the handler with option
    ///   argument set as `None`.
    ToggleParsingMode,
}

///
/// Option info codes returned by the `opt_i()` callback.
///
#[derive(Clone)]
#[derive(Copy)]
#[derive(Debug)]
#[derive(PartialEq)]
pub enum InfoCode {
    /// Value expected for this option
    ValueOpt,

    /// No value expected for this option
    NoValueOpt,

    /// Invalid option
    InvalidOpt,
}

///
/// The enumeration specifies how a value has been provided for an option.
///
#[derive(Clone)]
#[derive(Copy)]
#[derive(Debug)]
#[derive(PartialEq)]
pub enum OptValSpec {
    /// Value provided as separate token for an option (long and short)
    /// or standalone value without associated option.
    Standalone,

    /// Value provided after '=' for long option.
    StandaloneEqu,

    /// Short option value provided as a tail of option(s) in a group
    /// (the group may consist of a single option only).
    Group,
}

///
/// Option's value description.
///
#[derive(Clone)]
#[derive(Debug)]
#[derive(PartialEq)]
pub struct OptVal {
    /// Value content
    pub val: String,

    /// Value specifier
    pub val_spec: OptValSpec,
}

///
/// Option constraints.
///
/// Mutable reference to an `OptConstr` object is passed to the `opt_i()`
/// hander to provide ability to define additional constraints on a parsed
/// option. The handler should call `OptConstr` public methods for the object
/// to specify required constraints or remain the object untouched if no
/// constraints are required.
///
pub struct OptConstr(u32);

impl Default for OptConstr {
    fn default() -> Self { OptConstr(0) }
}

impl OptConstr {
    const NOT_IN_GROUP: u32 = 1;

    ///
    /// Option may not occur inside a group. Applies only for short options.
    ///
    #[inline]
    pub fn not_in_group(&mut self) {
        self.0 |= Self::NOT_IN_GROUP;
    }

    #[inline]
    fn is_not_in_group(&mut self) -> bool {
        (self.0 & Self::NOT_IN_GROUP) != 0
    }
}

macro_rules! process_h_rc {
    ($rc:expr, $mod:expr) => {
        match $rc {
            Break => { return Ok(()); },
            ToggleParsingMode => { $mod = !$mod; },
            _ => {},
        }
    }
}

fn parse_opts_iter<I, Fi, Fh>(opts: I, opt_i: Fi, opt_h: Fh) -> Result<(), ParseError>
where
    I: Iterator<Item = String>,
    Fi: FnMut(&CmdOpt, &mut OptConstr) -> InfoCode,
    Fh: FnMut(&Option<CmdOpt>, &Option<OptVal>) -> Result<ProcessCode, ParseError>
{
    // convert to mutable
    let mut opt_h = opt_h;
    let mut opt_i = opt_i;

    let mut val_mode = false; // false: option-parsing-mode, true: value-parsing-mode
    let mut val_req = false;  // true is value is required for the parsed option

    let mut opt: Option<CmdOpt> = None;

    for tkn in opts.into_iter() {
        if val_mode || val_req || !tkn.starts_with("-") {
            //
            // Option's value or standalone value.
            //
            let val = Some(OptVal{
                val: tkn,
                val_spec: Standalone
            });
            let h_rc = opt_h(&opt, &val)?;
            process_h_rc!(h_rc, val_mode);

            val_req = false;
            opt = None;
            continue;
        }

        //
        // options-parsing-mode below
        //

        if tkn.starts_with("--") && tkn.len() > 2 {
            //
            // Long option. Note "--" is treated as short "-" option.
            //
            let _opt;
            let mut constr: OptConstr = Default::default();

            if let Some(equ) = tkn.find('=') {
                // value provided after '='
                _opt = Long(tkn[ops::Range{start: 2, end: equ}].to_string());
                let val = if tkn.len() <= equ + 1 {
                    None
                } else {
                    Some(OptVal{
                        val: tkn[ops::RangeFrom{start: equ + 1}].to_string(),
                        val_spec: StandaloneEqu,
                    })
                };

                match opt_i(&_opt, &mut constr) {
                    InfoCode::InvalidOpt => {
                        return Err(ParseError::InvalidOpt(_opt.clone(),
                            "Invalid option".to_string()));
                    },
                    ValueOpt => {
                        let h_rc = opt_h(&Some(_opt), &val)?;
                        process_h_rc!(h_rc, val_mode);
                    },
                    NoValueOpt => {
                        return Err(ParseError::InvalidOpt(_opt.clone(),
                            "Argument not expected".to_string()));
                    },
                }
            } else {
                _opt = Long(tkn[2..].to_string());
                match opt_i(&_opt, &mut constr) {
                    InfoCode::InvalidOpt => {
                        return Err(ParseError::InvalidOpt(_opt.clone(),
                            "Invalid option".to_string()));
                    },
                    ValueOpt => {
                        // value provided in the next token
                        opt = Some(_opt);
                        val_req = true;
                    },
                    NoValueOpt => {
                        let h_rc = opt_h(&Some(_opt), &None)?;
                        process_h_rc!(h_rc, val_mode);
                    },
                }
            }
        } else {
            //
            // Short option.
            //
            let opts_grp = tkn[1..].to_string();
            let opts_grp_len = opts_grp.len();

            if opts_grp_len <= 0 {
                return Err(EmptyOptFound);
            }

            // parse group of shorts options
            for (i, c) in opts_grp.char_indices() {
                let mut constr: OptConstr = Default::default();
                let _opt = Short(c);

                // In case some option in the group requires an value,
                // the remaining part of the group constitutes the value.
                // In case last option in the group requires an value, the
                // next token will be used as the value.
                // If some of the option in the group suppresses options-parsing-mode,
                // the mode is still valid until the entire group is handled.
                match opt_i(&_opt, &mut constr) {
                    InfoCode::InvalidOpt => {
                        return Err(ParseError::InvalidOpt(_opt.clone(),
                            "Invalid option".to_string()));
                    },
                    ValueOpt => {
                        if constr.is_not_in_group() && i > 0 {
                            return Err(ParseError::InvalidOpt(_opt.clone(),
                                "The option may not exist in group".to_string()));
                        }

                        if i + 1 >= opts_grp_len {
                            // value provided in the next token
                            opt = Some(_opt);
                            val_req = true;
                        } else {
                            // value provided as part of the group
                            let val = Some(OptVal {
                                val: opts_grp[ops::RangeFrom{start: i + 1}].to_string(),
                                val_spec: Group,
                            });

                            let h_rc = opt_h(&Some(_opt), &val)?;
                            process_h_rc!(h_rc, val_mode);
                        }
                        break;
                    },
                    NoValueOpt => {
                        if constr.is_not_in_group() && opts_grp.chars().count() > 1 {
                            return Err(ParseError::InvalidOpt(_opt.clone(),
                                "The option may not exist in group".to_string()));
                        }

                        let h_rc = opt_h(&Some(_opt), &None)?;
                        process_h_rc!(h_rc, val_mode);
                    },
                }
            }
        }
    }

    if opt.is_some() {
        if val_req {
            return Err(ParseError::InvalidOpt(opt.unwrap().clone(),
                "Argument required".to_string()));
        } else {
            opt_h(&opt, &None)?;
        }
    }
    Ok(())
}

///
/// Parse process command line options.
///
/// For every parsed option user's provided option `opt_i()` is called-back to
/// retrieve information about parsed option followed by call to `opt_h()` to
/// handle that option.
///
#[inline]
pub fn parse_opts<Fi, Fh>(opt_i: Fi, opt_h: Fh) -> Result<(), ParseError>
where
    Fi: FnMut(&CmdOpt, &mut OptConstr) -> InfoCode,
    Fh: FnMut(&Option<CmdOpt>, &Option<OptVal>) -> Result<ProcessCode, ParseError>
{
    parse_opts_iter(env::args().skip(1), opt_i, opt_h)
}

#[allow(unused_imports)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_opt()
    {
        let opts = vec!("-")
            .into_iter()
            .map(|v| v.to_string());

        let rc = parse_opts_iter(opts,
            |_, _| {
                return NoValueOpt;
            },
            |opt, val| {
                match (opt, val) {
                    _ => {
                        println!("UNEXPECTED opt:{:?}, val:{:?}", opt, val);
                        assert!(false);
                    },
                };
                Ok(Continue)
            }
        );
        assert_eq!(rc, Err(EmptyOptFound));
    }

    #[test]
    fn test_short_noval()
    {
        let opts = vec!(
                "-abc", // group of 3 short options
                "-d",   // single short option
                "-e")   // invalid option
            .into_iter()
            .map(|v| v.to_string());

        let mut i = 0;
        let rc = parse_opts_iter(opts,
            |opt, _| {
                if let Short(o) = opt {
                    if "abcd".contains(*o) {
                        NoValueOpt
                    } else {
                        InfoCode::InvalidOpt
                    }
                } else {
                    InfoCode::InvalidOpt
                }
            },
            |opt, val| {
                match (i, opt, val) {
                    (0, Some(Short('a')), None) => {},
                    (1, Some(Short('b')), None) => {},
                    (2, Some(Short('c')), None) => {},
                    (3, Some(Short('d')), None) => {},
                    (4, Some(Short('e')), None) => {},
                    _ => {
                        println!("UNEXPECTED i:{}, opt:{:?}, val:{:?}", i, opt, val);
                        assert!(false);
                    },
            };
            i += 1;
            Ok(Continue)
        });

        assert_eq!(i, 4);
        if let Err(ParseError::InvalidOpt(Short(o), _)) = rc {
            assert_eq!(o, 'e');
        } else {
            assert!(false);
        }
    }

    #[test]
    fn test_short_val()
    {
        let opts = vec!(
                "-abc",     // single short options value read from the group
                "-d", "-e") // short option with value
            .into_iter()
            .map(|v| v.to_string());

        let mut i = 0;
        let rc = parse_opts_iter(opts,
            |opt, _| {
                if let Short(o) = opt {
                    if "ad".contains(*o) {
                        ValueOpt
                    } else {
                        InfoCode::InvalidOpt
                    }
                } else {
                    InfoCode::InvalidOpt
                }
            },
            |opt, val| {
                match (i, opt, val) {
                    (0, Some(Short('a')), Some(v))
                        if v.val == "bc" && v.val_spec == Group => {},
                    (1, Some(Short('d')), Some(v))
                        if v.val == "-e" && v.val_spec == Standalone => {},
                    _ => {
                        println!("UNEXPECTED i:{}, opt:{:?}, val:{:?}", i, opt, val);
                        assert!(false);
                    },
            };
            i += 1;
            Ok(Continue)
        });

        assert_eq!(i, 2);
        assert_eq!(rc, Ok(()));
    }

    #[test]
    fn test_long()
    {
        let opts = vec!(
                "--a",
                "--b=v",    // option with value (case 1)
                "--b", "v", // option with value (case 2)
                "--c=v")    // value not expected
            .into_iter()
            .map(|v| v.to_string());

        let mut i = 0;
        let rc = parse_opts_iter(opts,
            |opt, _| {
                if let Long(o) = opt {
                    match o.as_str() {
                        "a" | "c" => {
                            InfoCode::NoValueOpt
                        },
                        "b" => {
                            InfoCode::ValueOpt
                        },
                        _ => {
                            InfoCode::InvalidOpt
                        },
                    }
                } else {
                    InfoCode::InvalidOpt
                }
            },
            |opt, val| {
                match (i, opt, val) {
                    (0, Some(Long(o)), None) if o == "a" => {},
                    (1, Some(Long(o)), Some(v))
                        if o == "b" && v.val  == "v" && v.val_spec == StandaloneEqu => {},
                    (2, Some(Long(o)), Some(v))
                        if o == "b" && v.val  == "v" && v.val_spec == Standalone => {},
                    _ => {
                        println!("UNEXPECTED i:{}, opt:{:?}, val:{:?}", i, opt, val);
                        assert!(false);
                    },
            };
            i += 1;
            Ok(Continue)
        });

        assert_eq!(i, 3);
        if let Err(ParseError::InvalidOpt(Long(o), _)) = rc {
            assert_eq!(o, "c");
        } else {
            assert!(false);
        }
    }

    #[test]
    fn test_inv_long_opt()
    {
        let opts = vec!(
            "--a",
            "--a=v");

        for a in opts.into_iter() {
            let opt = vec!(a)
                .into_iter()
                .map(|v| v.to_string());

            let rc = parse_opts_iter(opt,
                 |_, _| {
                     InfoCode::InvalidOpt
                 },
                 |opt, val| {
                     match (opt, val) {
                         _ => {
                             println!("UNEXPECTED opt:{:?}, val:{:?}", opt, val);
                             assert!(false);
                         },
                     }
                     Ok(Continue)
                 });

            if let Err(ParseError::InvalidOpt(Long(o), _)) = rc {
                assert_eq!(o, "a");
            } else {
                assert!(false);
            }
        }
    }

    #[test]
    fn test_last_opt()
    {
        // ok, value provided
        let opt = vec!("--a", "v")
            .into_iter()
            .map(|v| v.to_string());

        let mut i = 0;
        let rc = parse_opts_iter(opt,
             |_, _| {
                 InfoCode::ValueOpt
             },
             |opt, val| {
                 match (i, opt, val) {
                    (0, Some(Long(o)), Some(v))
                        if o == "a" && v.val == "v" && v.val_spec == Standalone => {},
                     _ => {
                         println!("UNEXPECTED i:{}, opt:{:?}, val:{:?}", i, opt, val);
                         assert!(false);
                     },
                 }
                i += 1;
                 Ok(Continue)
             });

        assert_eq!(i, 1);
        assert_eq!(rc, Ok(()));

        // error, required value not provided
        let opt = vec!("-a")
            .into_iter()
            .map(|v| v.to_string());

        let rc = parse_opts_iter(opt,
             |_, _| {
                 InfoCode::ValueOpt
             },
             |opt, val| {
                 match (i, opt, val) {
                     _ => {
                         println!("UNEXPECTED i:{}, opt:{:?}, val:{:?}", i, opt, val);
                         assert!(false);
                     },
                 }
                 Ok(Continue)
             });

        if let Err(ParseError::InvalidOpt(Short(o), _)) = rc {
            assert_eq!(o, 'a');
        } else {
            assert!(false);
        }
    }

    #[test]
    fn test_modes_switch()
    {
        let opts = vec!(
                "-a",   // short option
                "--",   // switch to values-parsing-mode
                "--b",  // standalone value
                "-c",   // standalone value
                "--",   // back to options-parsing-mode
                "-d-e", // group of shorts, mode switched after it
                "-f",   // standalone value
                "FILE", // standalone value
                "--")   // back to options-parsing-mode
            .into_iter()
            .map(|v| v.to_string());

        let mut i = 0;
        let rc = parse_opts_iter(opts,
            |_, _| {
                InfoCode::NoValueOpt
            },
            |opt, val| {
                let mut ret = Ok(Continue);
                match (i, opt, val) {
                    (0, Some(Short('a')), None) => {},
                    (1, Some(Short('-')), None) => {
                        ret = Ok(ToggleParsingMode);
                    },
                    (2, None, Some(v))
                        if v.val == "--b" && v.val_spec == Standalone => {},
                    (3, None, Some(v))
                        if v.val == "-c" && v.val_spec == Standalone => {},
                    (4, None, Some(v))
                        if v.val == "--"  => {
                            ret = Ok(ToggleParsingMode);
                        },
                    (5, Some(Short('d')), None) => {},
                    (6, Some(Short('-')), None) => {
                        ret = Ok(ToggleParsingMode);
                    },
                    (7, Some(Short('e')), None) => {},
                    (8, None, Some(v))
                        if v.val == "-f" && v.val_spec == Standalone => {},
                    (9, None, Some(v))
                        if v.val == "FILE" && v.val_spec == Standalone => {},
                    (10,None, Some(v))
                        if v.val == "--"  && v.val_spec == Standalone => {
                            ret = Ok(ToggleParsingMode);
                        },
                    _ => {
                        println!("UNEXPECTED i:{}, opt:{:?}, val:{:?}", i, opt, val);
                        assert!(false);
                    },
                };
                i += 1;
                ret
            });
        assert_eq!(i, 11);
        assert_eq!(rc, Ok(()));
    }

    #[test]
    fn test_break()
    {
        let opts = vec!(
                "-a",       // 1st short option
                "--help",   // will cause break
                "-b")       // ignored
            .into_iter()
            .map(|v| v.to_string());

        let mut i = 0;
        let rc = parse_opts_iter(opts,
            |_, _| {
                InfoCode::NoValueOpt
            },
            |opt, val| {
                let mut ret = Ok(Continue);
                match (i, opt, val) {
                    (0, Some(Short('a')), None) => {},
                    (1, Some(Long(opt)), None)
                        if opt == "help" => {
                            ret = Ok(Break);
                        },
                    _ => {
                        println!("UNEXPECTED i:{}, opt:{:?}, val:{:?}", i, opt, val);
                        assert!(false);
                    },
                };
                i += 1;
                ret
        });
        assert_eq!(i, 2);
        assert_eq!(rc, Ok(()));
    }

    #[test]
    fn test_not_in_group_constr()
    {
        // option w/o value test
        let opts = vec!(
                "-a",   // ok
                "-ab")  // error
            .into_iter()
            .map(|v| v.to_string());

        let mut i = 0;
        let rc = parse_opts_iter(opts,
            |opt, constr| {
                if let Short('a') = opt {
                    constr.not_in_group();
                }
                InfoCode::NoValueOpt
            },
            |opt, val| {
                match (i, opt, val) {
                    (0, Some(Short('a')), None) => {},
                    _ => {
                        println!("UNEXPECTED i:{}, opt:{:?}, val:{:?}", i, opt, val);
                        assert!(false);
                    },
                };
                i += 1;
                Ok(Continue)
        });
        assert_eq!(i, 1);
        if let Err(ParseError::InvalidOpt(Short(o), _)) = rc {
            assert_eq!(o, 'a');
        } else {
            assert!(false);
        }

        // option w/value test
        let opts = vec!(
                "-av",  // ok
                "-bav") // error
            .into_iter()
            .map(|v| v.to_string());

        let mut i = 0;
        let rc = parse_opts_iter(opts,
            |opt, constr| {
                if let Short('a') = opt {
                    constr.not_in_group();
                    InfoCode::ValueOpt
                } else {
                    InfoCode::NoValueOpt
                }
            },
            |opt, val| {
                match (i, opt, val) {
                    (0, Some(Short('a')), Some(v))
                        if v.val == "v" && v.val_spec == Group => {},
                    (1, Some(Short('b')), None) => {},
                    _ => {
                        println!("UNEXPECTED i:{}, opt:{:?}, val:{:?}", i, opt, val);
                        assert!(false);
                    },
                };
                i += 1;
                Ok(Continue)
        });
        assert_eq!(i, 2);
        if let Err(ParseError::InvalidOpt(Short(o), _)) = rc {
            assert_eq!(o, 'a');
        } else {
            assert!(false);
        }
    }
} // mod tests
