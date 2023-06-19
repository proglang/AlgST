#!/usr/bin/env bash
#
# This file expects `algst` and `freest-bench` to be on the path.

set -euo pipefail

usage() {
  echo "usage: $0 <DIRECTORY | FILES>..."
  exit
}

bench-file() {
  case "$1" in
    *.fst )
      if ! command -v freest-bench >/dev/null 2>&1; then
        echo >&2 "warning: skipping benchmark of ‘$1’ (‘freest-bench’ not available on the PATH)"
      else
        echo -e "\033[1mFreeST: benchmarking $1\033[0m"
        freest-bench -o "$1.csv" "$1"
      fi
      ;;

    *.algst )
      echo -e "\033[1mAlgST: benchmarking $1\033[0m"
      algst --bench "$1.csv" "$1"
      ;;

    * )
      echo >&2 "warning: skipping benchmark of ‘$1’ (unexpected file extension)"
      ;;
  esac
}

bench-dir() {
  find "$1" -type f '(' -name '*.fst' -o -name '*.algst' ')' \
    -exec bash -c 'bench-file "$@"' _ '{}' ';'
}

export -f bench-file

if [[ $# == 0 ]]; then
  usage
fi

for arg in "$@"; do
  case "$arg" in
    --help | -h )
      # Check if `--help` or `-h` is given anywhere.
      usage ;;
    -- )
      # Don't look beyond `--`.
      break ;;
  esac
done

if ! command -v algst >/dev/null 2>&1; then
  echo >&2 "command ‘algst’ not found, must be available on the PATH"
  exit 1
fi

for arg in "$@"; do
  if [ -d "$arg" ]; then
    bench-dir "$arg"
  else
    bench-file "$arg"
  fi
done
