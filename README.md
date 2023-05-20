# Command Line Options Parser

Simple command line parser in Rust.

`cmdopts` supports GNU-like options format (long and short) with optional
arguments. The parsing routine accepts two user callbacks:
* 1st one provides info of the currently parsed option,
* 2nd is the actual handler of the option.

The library doesn't interpret parsed options, rather passes them to the user's
handler to further processing. The idea is similar to `getopt(3)` and `getopt_long(3)`.
