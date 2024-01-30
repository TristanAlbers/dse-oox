Note: this is a clone of Daniel's thesis project work on OOX, https://github.com/DanielvanVliet/OO

# OOX
A symbolic verification tool for verifying object oriented languages. Programs that are verified are written in the OOX intermediate verification language, examples can be found in `/examples` and `/benchmark_programs`. This repository is a rewrite of the <https://github.com/stefankoppier/oox> repository, without support for concurrency, with the following additions:
- Support for inheritance, interfaces and dynamic dispatch
- Heuristic search algorithms
- Other optimisations

## Running for the first time
[Windows]  
Make sure to have cmake installed  
Make sure to have `libclang.dll` installed. Can be done via `choco install llvm` on powershell

Make sure you have Rust installed <https://www.rust-lang.org/tools/install>.
We can run and build the project in debug mode with `cargo run`, `cargo build` and in release mode by passing the `--release` flag.
Building the project for the first time can take 5-10 minutes because it has to build a version of Z3.

Alternatively you can use the provided Dockerfile.

### Passing arguments
Arguments to OOX can be passed after a `--`.
You can find the arguments required by passing `--help` like this:
`cargo run -- --help` or  `cargo run -- verify --help`


## How to run (in release):
Running in release is 5-30 times faster depending on the program, but will not log any debug logs to the log file.
`cargo run --release -- "./examples/intLinkedList.oox" --heuristic depth-first-search --function Node.test2 --k 50`

You can also run a multi-file setup, the files will be merged in the order you pass them. Note that sometimes this can leads to some typing problems. For example:
`cargo run --release -- verify ./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/ArchiveOutputStream.oox ./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/ArchiveEntry.oox ./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/Zip/* ./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/**/*.oox ./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/*.oox --k 1000 -f Main.test_symbolic`

## Coverage
The coverage is displayed when running the programs. The coverage is computed over the reachable program statements. Sometimes it may not be possible to reach 100% due to infeasible paths. 
You can confirm this by using the `--visualize-coverage` command which will print the program to `coverage_visualized.txt` and show for each statement the coverage.

## Tests
`cargo test --release`
I recommend running the tests with the `--release` flag unless you are debugging, to speed it up.

## Mutations
The mutations for experiment 2 were generated using
`cargo run -- mutate ./benchmark_programs/experiment2/list-sorting/sorting.oox --out ./benchmark_programs/experiment2/list-sorting/mutations --exclude Main.test Node.toArray List.toArray`.


## Editor tips
I recommend to use the visual studio code editor, with the 'rust analyzer' extension.

In vscode, you can add settings for file associations. Since OOX is somewhat similar to Java syntax, we can use this to add syntax highlighting to `.oox` files.
Lookup 'File associations' in settings and add *.oox : java

Often in the logs you'll find a reference to a path:line, like:  "src/exec.rs:268". You can quickly navigate to that file and line by using Ctrl + P and pasting it there.

## Logging
The project uses a library 'slog' for logging purposes.
There are some macros provided by the library that look similar to existing macros, like debug!() and dbg!(). 
The first is from slog the latter is from the Rust itself. I have used both, but recommend using dbg!() for small errors and slog's debug!() to put larger, more permanent debugging in place.

To pretty print a log with slog: 
debug!(logger, "message"; "key1" => #?value, key2 => "string value");

The #? prefix ensures the pretty-print: 
https://docs.rs/slog/latest/slog/trait.Value.html

other log macro's exist such as info!(..), warning!(..), etc.


Running the project with the `--release` flag will disable any debug or below logs.
This can be changed with feature flags from slog: <https://docs.rs/crate/slog/latest/features>

## Known minor issues
- Error path does not point to the right file
    - This can occur when multiple tests are ran after one another due to the way I implemented global files....
    - When running the test in isolation this will not happen.
- The resolver does not look at arguments.
    - This can cause weird behaviour like passing wrong values to functions to be OK, only to go wrong at assertions (where the values are checked).
- It seems like method invocation slows the execution by alot, so refactoring a bit of code to a separate method has a lot of impact.
- Bug in Control flow graph generation, when returning from inside a catch statement. (See ./examples/issues/CFG_bug.oox)

## Implementation differences with previous OOX
- We currently only support 1D arrays
- In Rust there is no guaranteed tail call optimization, so some of the recursion in the original OOX has been implemented as loops. 
    - Unfortunately not all recursion has been removed so a stackoverflow can occur if a program method is too large in some cases.
