# Command Line Options Parser

Simple command line parser in Rust.

`cmdopts` supports GNU-like command line options parsing with long and short
formats. Optional argument (aka option's value) may be associated with an option.
The parsing routine `parse_opts()` accepts two user callbacks:
* `opt_i()` provides parser with a context the parsed option may be used,
* `opt_h()` is the actual handler of the option.

The library doesn't interpret parsed options, rather passes them to the user's
handler to further processing. The idea is similar to `getopt(3)` and `getopt_long(3)`
routines.

## Options Format

### Short format

All options starting with single hyphen character `-` are short options. For
example: `-a -b -c` constitute 3 short options. These options may grouped into
single block of options as `-abc`.

If a short option requires an argument, the argument may be provided directly
after the option or separated by white space(s): `-dARG` or `-d ARG`.

If short options are grouped into a block, one the last one may be provided
with an argument. For example: `-abcdARG` or `-abcd ARG` is equivalent to
`-a -b -c -d ARG`, where `-a` `-b` `-c` don't have an argument, while `-d`
does.

### Long format

If an option starts with `--` it's long format option. For example `--help`.
Long options may not be formed into a group. An argument may be provided to
the long-format option directly after `=` character or followed by whitespace(s):
`--config=FILE` or `--config FILE`.

## Usage

See enclosed [`examples`](examples) for details.

## License

2 clause BSD license. See [`LICENSE`](LICENSE) file for details.
