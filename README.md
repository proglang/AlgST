# AlgST

AlgST is an implementation of Algebraic Session Types by Bernardo Almeida et al. (unpublished).


## Building & Running

Building is only officially supported through [stack]. AlgST can be run using

```
stack run -- <args...>
```

### Usage

A file can be checked by giving its path as an argument; if omitted input will be read from the terminal.

Querying the typechecker is possible with the flags

| Flag             | Description                          |
|------------------|--------------------------------------|
| `--nf TYPE`      | calculate the normal form for `TYPE` |
| `--kind,-K TYPE` | perform kind synthesis for `TYPE`    |
| `--type,-T EXPR` | perform type synthesis for `EXPR`    |

Full usage info is available with `--help`.


### Example

```bash
$ stack run -- -T 'fork number' --nf 'dual ?-Int.end' <<EOF
number : Int
number = 42
EOF
```

outputs

```
Parsing ... ok
Checking ... ok

[1] type synthesis ... ok
fork number
  => ?Int.end

[2] normal form ... ok
dual (?-Int.end)
  => ?Int.end
```

[stack]: https://docs.haskellstack.org/en/stable/README/


## Tests

The test suite can be run with

```
stack test
```
