# AlgST

AlgST is an implementation of [Parameterized Algebraic Protocols][paper-doi] by
Mordido et al. It includes a typechecker, interpreter and a simple module
system.

[paper-doi]: https://doi.org/10.1145/3591277


## Getting Started

AlgST can be built from source but we recommend using either a pre-built docker
image or a self-built docker image. Please refer to the corresponding section
below.


### Pre-built image

To retrieve the pre-built image use

```sh
docker pull registry.gitlab.com/algst/algst:artifact
```

Enter a shell inside a temporary container:

```sh
docker run --rm -it registry.gitlab.com/algst/algst:artifact
```

The shell session inside the new container will start in a directory containing
the examples discussed below. `algst` is available on the `PATH`. You can check
this with `algst --version` which should print `2.0.0`. The image contains an
install of `nano` if you want to make edits to the examples.

**Troubleshooting**
* If docker complains that the image's platform does not match the host
  platform you can try self-building the image as described in the next session
  but you will probably have to build from source.


### Self-built image

For building an image yourself, run the following command from the root of the
repository/zip file contents. Building should take about 10 to 15 minutes
depending on the amount of RAM and number of CPUs available to docker.

```sh
docker build . -t algst/algst:artifact
```

Enter a shell inside a temporary container:

```sh
docker run --rm -it algst/algst:artifact
```

The shell session inside the new container will start in a directory containing
the examples discussed below. `algst` is available on the `PATH`. You can check
this with `algst --version` which should print `2.0.0`. The image contains an
install of `nano` if you want to make edits to the examples.

**Troubleshooting**
* If docker complains that it can't build the image for the host platform you
  will have to build from source as described in the following section.
* It is possible to reduce the amount of resources necessary during the build
  in exchange for a slightly longer build: append `--build-arg BUILD_OPTS=-j1`
  to the `docker build` command.


### Building from source

* **Prerequisites:** the [stack](https://docs.haskellstack.org/en/stable) build
  tool. Please follow the link for installation instructions.

* **Building:** installs the correct version of GHC, builds the dependencies
  and finally the `algst` executable.

  ```sh
  stack build
  ```

* **Testing** (optional): runs the test suite covering most parts of the
  parser, type checker and interpreter after building its dependencies. The
  test suite is run automatically when building the docker image.

  ```sh
  stack test
  ```

* **Installing:** will copy the built executable to a user-owned, global
  location (typically `$HOME/.local/bin`). The exact location will be printed
  to the terminal. Make sure that this directory is added to your `$PATH`. Once
  everything is set-up correctly executing `algst --version` should print
  `2.0.0`.

  ```sh
  stack install
  ```

* **Examples:** the examples discussed below are located inside the `examples/`
  folder. Due to way `algst` handles imported files you will have to run the
  examples from *inside* the `examples/` directory.

* **Benchmarking:** to run the FreeST counterpart to the AlgST benchmarks you
  will have to build and install the `freest-bench` tool.

  ```sh
  cd benchmarks
  stack install FreeST:exe:freest-bench
  ```

  If you get an error *Error parsing targets: Unknown local package: FreeST*
  make sure that you run the `stack` command from inside the `benchmarks/`
  directory.


## Instructions

There are three parts to the artifact. The first are the code examples in the
section [Code Examples](#code-examples) which can be type checked. Most of them
also include a `main` function which can be run using the builtin tree-walking
interpreter.

`algst` can also show the type theory in action. Instructions for this second
part of the artifact are below the code examples in the section [Type
Theory](#type-theory).

The paper shows benchmark results demonstrating the linear-time behavior of
AlgST's type equivalence algorithm. The section [Benchmarking](#benchmarking)
contains instructions on how to reproduce these results.

An overview over the implemented language in AlgST can be found at the end of
the README in the section [AlgST Language](#algst-language). It gives type
signatures and a short documentation for each of the builtin operations.

A description of the command line interface and supported options is available
with `algst --help`. Studying it should not be necessary though, as the used
options will be presented throughout these instructions.


### Code Examples

Sections 2 and 5 are the relevant parts for the artifact regarding code
examples. The former gives many examples how the AlgST language can be used.
Section 5 talks about the implementation. The list below proceeds in the order
of appearance in the paper.

* `Ast.algst` contains the protocol definitions and functions from the
  examples in section 2.1.

  Additionally, it contains a `main` function which sends the data defined by
  `ast` over a channel. Typecheck and run the example through the interpreter
  with the below command.

  ```sh
  algst --run Ast.algst
  ```

  If you see **Success.** printed to your screen this indicates that typechecking
  was successful. If an error occurred you will see **Failed.** instead and a
  list of errors.

  The `--run` flag instructs `algst` to run the `main` function once everything
  type checked correctly. When evaluation completes successfully the value
  returned from `main` is printed to the terminal prefixed by **Result:**.
  Verify that the printed result matches the value of `ast`. The syntax of the
  output is not valid AlgST but reflects the interpreter's runtime
  representation of values.

* `Arith.algst` contains the definition of the `Arith` protocol and the
  functions from the examples in section 2.2.

  The `serveArith` function handles a single `Arith` interaction. If `Neg` is
  selected by the other side it receives one number and sends the negation
  back. If the other end selects `Add` instead the function will receive two
  numbers and reply with their sum. The `clientNeg` and `clientAdd` functions
  handle the other end of the communication: they select the operation to
  perform, send the arguments and receive the result.

  Note the difference between the paper and the implementation regarding
  `sendInt`/`send [Int]` and `receiveInt`/`receive [Int]`. The implementation
  provides one polymorphic operation for sending and one for receiving. The
  first type argument to those functions is the type being sent/received.
  Otherwise they behave the same. Other sendable/receivable types, for example,
  are strings and channels.

  Check and run, as with the previous example. You should see the result of
  `10 + 20` and its negation printed to the screen. The prefix `[0]` of these
  messages indicates from which thread (in this case the main thread) the
  messages originated.

  Now remove one of the `let ... = receive ... in` lines from `serveArith` and
  adjust the argument to `send` in a way that it does not depend on the
  variables `x` and `y` (which are not bound anymore), e.g. `send [Int, s] 10 c`.
  Typechecking will now fail because `serveArith` does not handle the `Arith`
  protocol correctly.

  Later examples depend on `Arith.algst`. Make sure to revert any changes
  before moving on. If you are running from a docker container you can also
  leave the current container and continue in a new one.

* `Stream.algst` contains the `Stream` protocol from the beginning of
  section 2.3.

  The symbol `ones` sends an infinite amount of `1` values over the provided
  channel by selecting `Next`, sending a `1` value and calling itself
  recursively. In a small difference from the paper, the unit type and the unit
  value are written as `()` in AlgST.

  The function `showAll` takes a function like `ones`, which sends an infinite
  stream of something over a provided channel. `showAll` will fork the
  execution of that function and read a new element from the stream every 0.5
  seconds. This function will be re-used in a later example.

  The included `main` function combines `showAll` with `ones`. When you run
  this file, you will have to interrupt it using Ctrl-C as the program tries to
  print the complete contents of an infinite stream.

* `GenericPassive.algst` contains the definitions from section 2.3.1. It
  imports the datatypes and protocols from `Arith.algst` and `Stream.algst`.

  This file includes no `main` function. Typecheck it by leaving the `--run`
  flag out.

* `GenericActive.algst` contains the definitions from section 2.3.2. It imports
  the datatypes and protocols from `Arith.algst` and `Stream.algst`. The
  behavior of `main` is the same as for `Stream.algst` but the code looks
  different: `streamActOnes` is now built from generic components. Evaluation
  will have to be interrupted using Ctrl-C as the program tries to print
  the complete contents of an infinite stream.

* `Toolbox.algst` corresponds to section 2.3.3. It provides a toolbox for
  generic servers. This file includes no main function either. Typecheck it
  using `algst Toolbox.algst`.

* `ArithTB.algst` shows a pratical application of the building blocks from
  section 2.3.3. The program uses `Toolbox.algst` to assemble a repeating
  server with the same behavior as `serveArith` from `Arith.algst` using
  handlers for the `Neg` and `Add` cases. Look at the type aliases at the top
  of the file to see how a protocol with similar behavior to `Arith` can be
  assembled.

  The functions `clientNeg` and `clientAdd` don't select `Neg` and `Add`
  constructors but have to select the constructors corresponding to the
  protocols from `Toolbox.algst`.

  The `main` function is concerned with selecting `More` to unroll one
  repetition before the calls to `clientNeg` and `clientAdd`. At the end the
  repetition has to be terminated explicitly by selecting `Quit`. Running this
  file should produce the same output as `Arith.algst`.

* `List.algst` contains functions for transmitting parametric lists,
  corresponding to section 2.3.4. The included `main` function sends and
  receives first a single list and then a list of lists.

* `Isomorphism.algst` demonstrates the extended type equivalence discussed in
  Section 5.

  It shows that the two types `forall a. Int -> a -> a` and `Int -> forall a. a
  -> a` are considered isomorphic. AlgST does not have subtyping. The short
  example of `iso` being the identity function and the fact that it typechecks
  demonstrate that the two types are considered equivalent.

* `Lambdas.algst` demonstrates the additional typing judgements added to allow
  writing some lambda abstractions without giving type annotations.

  *This file is expected to fail typechecking!* `f` and `g` are fine, however
  typechecking of `h` fails. `h'` demonstrates that with a type annotation `h`
  would be fine as well.

  `h` fails mostly because of technical reasons. The expected type not
  propagated in every case. `h` demonstrates that pattern matching on a pair is
  one such case.

* `Buffering.algst` demonstrates the different behaviors that can be achieved
  with blocking vs non-blocking `send` operations. (This example demonstrates
  an implementation choice which is not mentioned in the submitted paper but
  will be clarified in the revised version.)

  The `main` function forks two threads: a sender and 1.5 seconds later a
  receiver. The sender (identified by `[0-1]` in the output) immediately starts
  sending values on a channel. The receiver (identified by `[0-2]`) reads those
  values and prints them to the screen, waiting 1.5 seconds between each
  `receive` operation.

  When running the file with default options the sender sends the first number
  immediately but is then blocked until the receiver reads the first value.
  Sending/receiving happens fully synchronous:

  ```sh
  algst --run Buffering.algst
  ```

  By increasing the buffer inside the channels from zero to one the sender can
  send the first number without blocking but blocks on the second number:

  ```sh
  algst --run --eval-chan-size 1 Buffering.algst
  ```

  By increasing the buffer even further, the sender can terminate before the
  receiver even starts:

  ```sh
  algst --run --eval-chan-size 5 Buffering.algst
  ```

The following examples don't correspond directly to parts of the paper but are
interesting for the comparison with Context Free Session Types and Nested
Session Types (Thiemann and Vasconcelos, 2016; Das et al, 2021; Almeida
et al, 2022).

* `Tree.algst` translates the tree example from the introduction of
  "Context-Free Session Types" (Thiemann and Vasconcelos, 2016) to AlgST.

  The provided `main` function sends the tree defined by `tree` over a channel,
  it is echoed back and read from the channel again.

* `Stack.algst` translates the stack example (the example exercised in the
  introduction) from "Polymorphic Lambda Calculus with Context-Free Session
  Types" (Almeida et al, 2022) to AlgST.

  The provided `main` function pushes two numbers onto the stack, pops them
  again and terminates.

* `Queue.algst` translates the *Queues* example from section 2 of "Nested
  Session Types" (Das et al, 2021) to AlgST.

* `NestedCFL.algst` translates the *Context Free Languages, Multiple Kinds of
  Parentheses* and *Multiple States as Multiple Parameters* examples from
  section 2 of "Nested Session Types" (Das et al, 2021) to AlgST.

The final set of examples demonstrates interesting but well-defined behavior of
the type system of AlgST. These are part of the supplementary material.

* `Flip.algst` illustrates that AlgST handles negated recursion correctly. When
  sending a `Flipper` the negated `Int` is received. In the negated recursion
  the negated `Int` (now doubly-negated) is sent.

  The `Flipper` protocol can be handled by pair of mutual recursive functions
  (`flip` and `flop`) or just one recursive function (`flipper`).

* `FlipFlop.algst` demonstrates that AlgST handles mutually recursive protocols
  correctly. In fact, the protocol `Flip` is equivalent to (but maybe more
  intuitive than) `Flipper` from `Flip.algst`. This correspondence is
  illustrated by the pair of functions `flipperFlop` and `flopFlipper`: the
  former forwards an interaction received as `Flipper` on a channel as `Flip`,
  the latter encodes the reverse forwarding.

* `Dual.algst` encodes the problem discovered by Bernardi and Hennessy
  (2014, 2016) in the interaction between duality and recursive session types.
  The problem is most concisely exposed by the recursive type `μX.!X.X`.
  Translating this session type to AlgST results in the protocol `X`.

  The outcome matches the expected correct outcome according to Bernardi and
  Hennessy (2016) which is illustrated in the types of `selectMu`, `dualT`, and
  `matchMu`.


### Type Theory

This part of the artifact is concerned with type formation and type
normalization (section 3) and type synthesis (section 4). It refers to examples
from section 2 in the paper and data definitions from the previous part.

The typechecker inside `algst` can be queried using the following flags which
we will now make use of. By providing a file together with these flags on the
command line you will have access to the definitions and symbols inside that
file.

| Flag             | Description                          |
|------------------|--------------------------------------|
| `--nf TYPE`      | calculate the normal form for `TYPE` |
| `--kind,-K TYPE` | perform kind synthesis for `TYPE`    |
| `--type,-T EXPR` | perform type synthesis for `EXPR`    |

The following invocation synthesizes the kinds for some basic types. Compare
this with the type formation rules from section 3. The implementation
differentiates between linear and unrestricted values which is the reason why
you will see `TU` (unrestricted `T`) or `TL` (linear `T`) instead of a simple
`T`, the same for kind `S` (but not `P`).

```sh
algst --kind 'Int -> Int' --kind '?Int.End!'
```

For sending any linear value (here a linear session value) `sendLin` is
required. Refer to its documentation in the section [AlgST Language/Session
operations](#session-operations) for more information.

```sh
algst --kind 'Int'        --type 'send [Int]'
algst --kind '?Int.End!'  --type 'sendLin [?Int.End!]'
```

Negating any type results in a protocol type:

```sh
algst --kind '-Int' --kind '-Ast' --kind '-AstP' Ast.algst
```

The following invocation synthesizes the types of the given expressions and
prints them to the screen. It demonstrates how the `select`-expressions
generate functions to unroll a protocol type. Compare with the `select ConP`
and `select AddP` examples in section 2.2 and the typing of `select` in figure 4.

```sh
algst --type 'select ConP' --type 'select AddP' Ast.algst
```

Repeat this, but now selecting the constructors of the `Arith` protocol
(section 2.2) and compare with the `select Neg` and `select Add` examples.
Here, the synthesized type and the normalized type are syntactically different.
In such cases `algst` will output both, the synthesized type (prefixed by
`[SYN]`) and the normalized type (prefixed by `[NF]`). See how the negation
reduces to a change in communication direction.

```sh
algst --type 'select Neg' --type 'select Add' Arith.algst
```

Communication direction is only inverted for the one negated component as is
demonstrated by the following example. We instruct `algst` to read the source
code from standard input and provide it with a single protocol definition which
negates is middle component. Only this middle component is received, the other
two components have to be sent.

```sh
echo 'protocol P = C Int -Int Int' | algst --type 'select C' -
```

The following example demonstrates the normalization example from section 3.
Because `algst` requires the given types to be closed we have to wrap the type
from the example in an explicit `forall`. As a small syntactic difference
`Dual` in the paper is written as `dual` in AlgST.

```sh
algst --nf 'forall (s:S). dual (?(-Int).s)'
```

Section 2.3.2 in the paper uses the fact that double negation of a type results
in the original type. This is visible in the normal form. (Be sure to separate
double negation using parentheses or whitespace, otherwise it is interpreted as
a line comment!)

```sh
algst --nf 'Stream Int' --nf 'Stream -Int' --nf 'Stream -(-Int)' Stream.algst
```

The isomorphism demonstrated in `Isomorphism.algst` is also reflected in the
normal form:

```sh
algst --nf 'forall a. Int -> a -> a' --nf 'Int -> forall a. a -> a'
```

Introduce another type parameter and observe how the individual quantifiers are
pushed down the function arrow as far as possible but always keep their
relative ordering:

```sh
algst --nf 'forall a b. Int -> a -> b -> b' --nf 'forall a b. b -> a -> ()'
```


### Benchmarking

AlgST includes a type equivalence benchmarker. The example `Benchmark.algst`
contains two benchmarks

1. a test case benchmarking the equivalence algorithm on the two types `forall
   a b. a -> b -> a` and `forall a. a -> forall b. b -> a`

2. a test case benchmarking the equivalence algorithm on the two session types
   `!Stack Int.End!` and `dual (?Stack Int.End?)` (using the `Stack` protocol
   from `Stack.algst`)

To run the benchmarks give the `--bench CSV-OUTPUT` option to `algst`. The
measurements will be written to `CSV-OUTPUT`. Timings will also be printed to
the terminal. The command below runs the benchmarks and writes the results to
`benchmark-example.csv`.

```sh
algst --bench benchmark-example.csv Benchmark.algst
```

Benchmarks are numbered using the order in which they appear in the source
file. The resulting CSV contains a `Mean` column showing the average of
multiple executions of the equivalence algorithm. All timings in the CSV file
are in seconds.

Section 5 in the paper shows benchmark results comparing AlgST's type
equivalence algorithm with that of FreeST, a freely available programming
language implementing Context Free Session Types. The following steps explain
how to reproduce our results. Of course, the exact numbers may vary given the
benchmarks are run on different machines, inside docker containers, etc.

The used test cases are included in the artifact inside the directory
`benchmarks/test-cases`. Inside the docker container they can be found under
the same path. There are nine files with positive test cases (prefixed with
`pos`) and nine files containing negative test cases (prefixed with `neg`).
Each file consists of 36 test cases of increasing size. On the AlgST side the
benchmarks are annotated with the size: a benchmark with name "10/26" indicates
the tenth benchmark of that file and that it has a size of 26. Every \*.algst
file is accompanied by a \*.fst file containing a translation of the same
equivalence problem from AlgST to FreeST.

The script `benchmarks/run-benchmarks.sh` (available on the `PATH` inside the
docker container) can be used to run the benchmarks. It expects the directory
containing the test cases as an argument. The CSV files containing the timings
will be placed next to the benchmarks with the `.csv` extension added.

```sh
# From inside the docker container
run-benchmarks.sh benchmarks/test-cases
# When using a build from source
./benchmarks/run-benchmarks.sh benchmarks/test-cases
```

Running only a subset of the tests is possible by listing specific files on the
command line. This is advised if you are not interested in the full results as
running just the two benchmark sets `neg-1.algst`, `neg-1.fst` may already take
about thirty minutes.

```sh
run-benchmarks.sh benchmarks/test-cases/neg-1.*
```


## AlgST Language

This section gives an overview over the most important parts of the AlgST
language. A description of the language's grammar can be found in
`grammar.txt`.


### Declarations

* **Algebraic Data Types**

  ADTs are introduced by the `data` keyword followed by the type's name. ADTs may
  be parameterized. Type parameters always default to kind `TU` but a different
  kind may be specified explicitly.

  Type names and constructors must start with an uppercase letter. Any kind of
  variable must start with a lowercase letter.

  ```algst
  data Tree a
    = Branch (Tree a) (Tree a)
    | Leaf a

  data Handler (s:SL) = Handler (s -> ()) (dual s -> ())
  ```

  If any constructor argument is linear, the whole type has to explicitly be
  marked as linear:

  ```algst
  data LinTree:TL (a:TL)
    = LinBranch (LinTree a) (LinTree a)
    | LinLeaf a
  ```

* **Algebraic Protocols**

  Protocol declarations are introduced by the `protocol` keyword. Otherwise
  protocol declarations look like ADT declarations: they may be parameterized,
  have multiple constructors, etc. The arguments of a protocol constructor are
  of kind `P`. This allows arguments to be negated.

  ```algst
  protocol List a
    = Cons a (List a)
    | Nil

  protocol Arith
    = Add Int Int -Int
    | Neg Int -Int
  ```

* **Type Aliases**

  Type abbreviations are written using the `type` keyword and may be
  parameterized.

  ```algst
  type Send a = a -> forall (s:SL). !a.s -> s
  ```

* **Functions/Top-Level Values**

  Every top-level value must have a type signature. Its type must be a subkind
  of `TU`; linear top-level values are not allowed. There may be no other
  definitions between a value's type signature and its definition. Top-level
  values may be (mutually) recursive. The order of definitions does not matter.
  Functions can be declared and used without providing a definition but running
  such a program will fail.

  ```algst
  implementLater : Int -> Int

  f1 : Int -> Int
  f1 x = f2 (x + 1)

  f2 : Int -> Int
  f2 x =
    if x > 100
       then implementLater x
       else f1 (x + 1)
  ```

  To bind a type parameter write it in square brackets. Binding type parameters
  is optional. But if a type parameter is bound, different from type
  applications (see below) type parameters and ordinary parameters have to be
  bound in exactly the same order as they are appear in the type signature.

  ```algst
  const1 : forall a b. a -> b -> a
  const1 a _ = a

  const2 : forall a b. a -> b -> a
  const2 [a] a b = a

  const3 : forall a b. a -> b -> a
  const3 [a] [b] a b = a

  -- Error!
  const4 : forall a b. a -> b -> a
  const4 [a] a [b] b = a
  ```

  At the moment, AlgST does not allow patterns on the left-hand side of
  function definitions.


### Basic expressions

* `f x` and `f [T]`

  AlgST has ordinary function application (the first form). AlgST also requires
  explicit type application which is written using square brackets.

  The two types `forall a. Int -> a -> Int` and `Int -> forall a. a -> Int` are
  considered equivalent. This isomorphism allows relative liberal placement of
  type applications. However, their relative ordering must be preserved and a
  quantifier may only be shifted further right/inwards if the quantified
  variables does not appear free in the next argument.

  Function application can also be written as `f <| x` or `x |> f`. These
  operators have low precedence which enable simple sequencing of operations.

* `\(x : T) -> ...` and `\(x : T) -o ...` and `\[x:TU] -> ...`

  In AlgST there are three different kinds of lambda expressions. The first
  form creates an ordinary function of some type `T -> U`. The second form
  creates a linear function of some type `T -o U`. The third form is a type
  abstraction. In some cases AlgST can infer the type of bound variables making
  a definition such as the following one valid:

  ```algst
  increment : Int -> Int
  increment = \i -> i + 1
  ```

* `if cond then true_expr else false_expr`

  Evaluates `cond`, which must be of type `Bool`. If the result is `True` the
  if-expression evaluates to the value of `true_expr`, otherwise it evaluates to the
  value of `false_expr`.

  The boolean operators `&&` and `||` are currently not short-circuiting.

* `case value of { Con1 x y z -> ..., Con2 -> ... }`

  The type of `value` must be an ADT. Depending on the constructor used by
  `value` a different expression is evaluated. AlgST's pattern language is
  currently very limited: patterns cannot be nested and literal expressions are
  not recognised as patterns either.

  If the matched type has only a single constructor the unwrapping can be done
  in a let-expression as well.

  ```algst
  data Vec3 a = Vec3 a a a

  vecAdd : Vec3 Int -> Vec3 Int -> Vec3 Int
  vecAdd v u =
    let Vec3 v1 v2 v3 = v in
    let Vec3 u1 u2 u3 = u in
    Vec3 [Int] (v1 + u1) (v2 + u2) (v3 + u3)
  ```

* `rec x : T = e`

  Evaluates to the expression `e` with `x` naming the recursive expression in
  its body. Giving a type `T` is obligatory and must be a function type. `e`
  itself must be a lambda abstraction.

* `let rec x : T = e1 in e2`

  Is similar to the version above. Additionally, the recursive function `e1` is
  also visible to `e2` under the same name `x`.


### Session operations

* `new [T] : (T, dual T)`

  The `new` expression creates a pair of connected channels. It *must* be used
  with a type application.

* `send : forall (a:TU) (s:SL). a -> !a.s -> s`

  Sends an *unrestricted* message type over the provided channel.

  `send` exists as a convenience version of `sendLin`. See `sendLin` for an
  explanation.

* `sendLin : forall (a:TL) (s:SL). a -> !a.s -o s`

  Sends any message type over the provided channel.

  If used with unrestricted data (e.g. `Int`) the partially applied function
  (e.g. `sendLin [Int] 1`) is linear, i.e. must be called exactly once. By
  using `send` instead the same partial application `send [Int] 1` results in
  an unrestricted function which may be called any number of times.

* `receive : forall (a:TL) (s:SL). ?a.s -> (a, s)`

  Receives any message type from the provided channel.

* `wait : End? -> ()`

  Waits for a session to be closed by the other end.

* `fstWait : forall (a:TL). (a, End?) -> a`

  Combines `wait` with extracting a value `a` from a pair. This is useful if a
  `receive` operation results in an exhausted channel of type `End?` for which
  termination has to be awaited:

  ```
  receiveFinalWait : forall (a:TL). ?a.End? -> a
  receiveFinalWait [a] c = receive [a, End?] c |> fstWait [a]
  ```

* `terminate : End! -> ()`

  Terminates a session.

* `fstTerminate : forall (a:TL). (a, End!) -> a`

  Combines `terminate` with extracting a value `a` from a pair. Like `fstWait`
  but with `terminate`:

  ```
  receiveFinalTerm : forall (a:TL). ?a.End! -> a
  receiveFinalTerm [a] c = receive [a, End!] c |> fstTerminate [a]
  ```


### Concurrency Primitives

* `fork : forall (a:TL). a -> ?a.End?`

  `fork e` evaluates expression `e` in a new thread. In the parent context it
  evaluates to a single element channel from which the result can be read once
  it becomes available.

  A type application is not necessary.

* `fork_ : forall (a:TU). a -> ()`

  `fork_ e` evaluates expression `e` in a new thread and discards the result
  value. In the parent context `fork_ e` evaluates to the unit value `()`.

  A type application is not necessary.

* `usleep : Int -> ()`

  Delays execution for the given number of microseconds.


### Printing

* `trace : forall (a:TL). a -> a`

  Prints a description of the given value to the screen. The message is
  prefixed by an ID of the printing thread.

* `traceMsg : String -> ()`

  Prints the given message to the screen. The message is prefixed by an ID of
  the printing thread.


### Modules

For demonstration purposes consider a module `Data.List` with the following
contents:

```algst
data List a = Cons a (List a) | Nil

single : forall a. a -> List a
single [a] a = Cons [a] a (Nil [a])
```

By importing a module all its top level symbols and associated constructors
become available to the importing module. An import list can be used to modify
the set of imported symbols.

1. Import all symbols:

     ```algst
     import Data.List
     ```

2. Import only specific symbols:

    ```algst
    import Data.List (type List, Nil, single)
    ```

    The above statement imports all symbols from `Data.List` except the `Cons`
    constructor.

    Type names have to be prefied with the `type` keyword.

3. Import symbols under a new name:

    ```algst
    import Data.List (type List as ConsList, single as singleton)
    import Data.List (*, type List as ConsList, single as singleton)
    ```

    The first statement imports the `List` type under the name `ConsList` and
    the `single` function is made available under the name `singleton`.

    The second statement (note the leading `*`) applies the same renamings but
    additionally imports the remaining symbols under their given name.

    Type names have to be prefied with the `type` keyword.

4. Import all symbols *except* the given identifiers:

    ```algst
    import Data.List (*, type List as _, Cons as _, single as _)
    ```

    The above statement imports only the `Nil` constructor as all other symbols
    are hidden. Note the leading `*` in the import list.

    Hiding and renaming symbols can be combined freely.

Re-exporting symbols is currently not supported. Neither is it possible to
control which top-level symbols can be imported by other modules.

A module name `A.B.C` maps to a file `A/B/C.algst` in the module search path.

Without any additional arguments `algst` will search for modules in the current
working directory. With `-I,--search-dir DIR` other directories can be
specified.


## Editor Support

The directory ``utils/vim`` contains syntax files for highlighting in vim.


# References

* Bernardo Almeida, Andreia Mordido, Peter Thiemann, and Vasco T. Vasconcelos. 2022. Polymorphic Lambda Calculus with Context-Free Session Types. Information and Computation (2022). https://arxiv.org/abs/2106.06658
* Giovanni Bernardi and Matthew Hennessy. 2014. Using Higher-Order Contracts to Model Session Types (Extended Abstract). In CONCUR (Lecture Notes in Computer Science, Vol. 8704). Springer, Rome, Italy, 387–401. https://doi.org/10.1007/978-3-662-44584-6_27
* Giovanni Bernardi and Matthew Hennessy. 2016. Using Higher-Order Contracts to Model Session Types. Logical Methods in Computer Science 12, 2 (2016). https://doi.org/10.2168/LMCS-12(2:10)2016
* Ankush Das, Henry De Young, Andreia Mordido, and Frank Pfenning. 2021. Nested Session Types. In Programming Languages and Systems - 30th European Symposium on Programming, ESOP 2021 (Lecture Notes in Computer Science, Vol. 12648), Nobuko Yoshida (Ed.). Springer, Luxembourg City, Luxembourg, 178–206. https://doi.org/10.1007/978-3-030-72019-3_7
* Peter Thiemann and Vasco T. Vasconcelos. 2016. Context-Free Session Types. In Proceedings of the 21st ACMSIGPLAN International Conference on Functional Programming, ICFP 2016, Jacques Garrigue, Gabriele Keller, and Eijiro Sumii (Eds.). ACM, Nara, Japan, 462–475. https://doi.org/10.1145/2951913.2951926
