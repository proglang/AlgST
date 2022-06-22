# AlgST

AlgST is an implementation of Algebraic Session Types by Andreia Mordido et al. (unpublished).


## Building

Building is supported either in a Docker container or using the [stack]() build
tool.


### Docker Container

* **Prerequisits:** Docker, e.g. via [Docker Desktop]()

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
    ; docker run --rm -it jaspa/algst  # command follows here...
    ```

    To verify that running `algst` works execute

    ```sh
    ; docker run --rm -it jaspa/algst algst --help
    ```


### Stack

* **Prerequisits:** [stack](), installation instrunctions are provided on the
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


## Usage

A file can be checked by giving its path as an argument; to read input from the
terminal give `-` as the path.

Querying the typechecker is possible with the flags

| Flag             | Description                          |
|------------------|--------------------------------------|
| `--nf TYPE`      | calculate the normal form for `TYPE` |
| `--kind,-K TYPE` | perform kind synthesis for `TYPE`    |
| `--type,-T EXPR` | perform type synthesis for `EXPR`    |

Full usage info is available with `--help`.


### Example

```bash
; algst - -T 'fork number' --nf 'dual ?-Int.end' <<EOF
number : Int
number = 42
EOF
```

outputs

```
Success.

--type fork number
  ?Int.end

--nf dual ?-Int.end
  ?Int.end
```

[stack]: https://docs.haskellstack.org/en/stable/README/
