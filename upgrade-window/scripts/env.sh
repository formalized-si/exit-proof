# Build environment; sourced by check.sh and the scripts. Every variable can be set by the caller.
#   CARGO_TARGET_DIR    where cargo builds the harness (default: harness/target in this directory)
#   UW_CONTRACT_TARGET  where cargo builds the example vault and its mutants
#                       (default: $CARGO_TARGET_DIR/upgrade-window-contract)
#   LIBCLANG_PATH       directory that holds libclang.so, when it is not installed system-wide.
#                       nearcore's RocksDB bindings need libclang at build time; without root,
#                       `python3 -m pip install libclang` provides one in site-packages/clang/native.
_ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
command -v cargo > /dev/null 2>&1 || PATH="$HOME/.cargo/bin:$PATH"
command -v lake > /dev/null 2>&1 || PATH="$HOME/.elan/bin:$PATH"
export PATH
mkdir -p "${CARGO_TARGET_DIR:-$_ROOT_DIR/harness/target}"
CARGO_TARGET_DIR="$(cd "${CARGO_TARGET_DIR:-$_ROOT_DIR/harness/target}" && pwd)"
export CARGO_TARGET_DIR
export UW_CONTRACT_TARGET="${UW_CONTRACT_TARGET:-$CARGO_TARGET_DIR/upgrade-window-contract}"
if [ -n "${LIBCLANG_PATH:-}" ]; then
  export LIBCLANG_PATH LD_LIBRARY_PATH="$LIBCLANG_PATH${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
  # a bare libclang (the pip package) ships no C headers: point it at the compiler's own
  if [ -z "${BINDGEN_EXTRA_CLANG_ARGS:-}" ] && command -v gcc > /dev/null 2>&1; then
    export BINDGEN_EXTRA_CLANG_ARGS="-I$(gcc -print-file-name=include)"
  fi
fi
