# AlgST

AlgST is an implementation of Algebraic Session Types by Andreia Mordido et al. (unpublished).

It includes a typechecker, interpreter and a simple module system.


## Building

Building is supported either in a Docker container or using the [stack] build
tool.


### Docker Container

* **Prerequisits:** Docker, e.g. via [Docker Desktop][docker-desktop]

* **Building:**

    ```sh
    ; docker build -t proglang/algst -f utils/Dockerfile .
    ```

    Building takes about 10 minutes on my machine.

* **Testing:**

    ```sh
    ; docker run --rm -it proglang/algst stack test
    ```

    This will run the test suite covering the parser, type checker and
    interpreter.

* **Running:** To run `algst` prefix the invocations given below with

    ```sh
    ; docker run --rm -it proglang/algst  # command follows here...
    ```

    To verify that running `algst` works execute

    ```sh
    ; docker run --rm -it proglang/algst algst --help
    ```


### Stack

* **Prerequisits:** [stack], installation instructions are provided on the
  linked page.

* **Building:**

    ```sh
    ; stack build
    ```

    This command will download and install the required version of GHC, build
    the dependencies and finally the `algst` executable.

* **Testing:**

    ```sh
    ; stack test
    ```

    The command will compile and execute the test suite covering the parser,
    type checker and interpreter.

* **Running:** To run `algst` prefix the invocations given below with

    ```sh
    ; stack exec --  # command follows here...
    ```

    To verify that running `algst` works execute

    ```sh
    ; stack exec -- algst --help
    ```

[stack]: https://docs.haskellstack.org/en/stable/README/
[docker-desktop]: https://www.docker.com/products/docker-desktop/

## Usage

A file can be checked by giving its path as an argument; to read input from the
terminal give `-` as the path.

When the flag `--run` is given the `main` symbol will be executed and the
result printed.

Querying the typechecker is possible with the flags

| Flag             | Description                          |
|------------------|--------------------------------------|
| `--nf TYPE`      | calculate the normal form for `TYPE` |
| `--kind,-K TYPE` | perform kind synthesis for `TYPE`    |
| `--type,-T EXPR` | perform type synthesis for `EXPR`    |

Full usage info is available with `--help`.


### Example

```bash
; algst - --run --type 'fork main' --nf 'dual ?-Int.End!' <<EOF
main : Int
main = 10 + 20
EOF
```

outputs

```
Success.

--type fork number
  ?Int.End?

--nf dual ?-Int.End!
  ?Int.End?

Result: Number 30
```


## AlgST Language

### Recursive expressions

* `rec x : T = e`

  Evaluates to the expression `e` with `x` naming the recursive expression in
  its body. Giving a type `T` is obligatory and must be a function type. `e`
  itself must be a lambda abstraction.

* `let rec x : T = e1 in e2`

  Is similar to the version above. Additionally the recursive function `e1` is
  also visible to `e2` under the same name `x`.

### Session operations

* `new [T] : (T, dual T)`

  The `new` expression creates a pair of connected channels. It *must* be used
  with a type application.

* `send : forall (a:MU) (s:SL). a -> !a.s -> s`

  Sends an *unrestricted* message type over the provided channel.

  `send` exists as a convenience version of `sendLin`. See `sendLin` for an
  explanation.

* `sendLin : forall (a:ML) (s:SL). a -> !a.s -o s`

  Sends any message type over the provided channel.

  If used with unrestricted data (e.g. `Int`) the partially applied function
  (e.g. `sendLin [Int] 1`) is linear, i.e. must be called exactly once. By
  using `send` instead the same partial application `send [Int] 1` results in
  an unrestricted function which may be called any number of times.

* `receive : forall (a:ML) (s:SL). ?a.s -> (a, s)`

  Receives any message type from the provided channel.

### Concurrency Primitives

* `fork : forall (a:ML). a -> ?a.End?`

  `fork e` evaluates expression `e` in a new thread. In the parent context it
  evaluates to a single element channel from which the result can be read once
  it becomes available.

  A type application is not necessary.

* `fork_ : forall (a:TU). a -> ()`

  `fork_ e` evaluates expression `e` in a new thread and discards the result
  value. In the parent context `fork_ e` evaluates to the unit value `()`.

  A type application is not necessary.

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
