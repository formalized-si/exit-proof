# Build environment of the harness; sourced by check.sh. Every variable can be set by the caller.
#   CARGO_TARGET_DIR  where cargo builds the harness (default: harness/target next to this file)
#   LIBCLANG_PATH     directory that holds libclang.so, when it is not installed system-wide.
#                     nearcore's RocksDB bindings need libclang at build time; without root,
#                     `python3 -m pip install libclang` provides one in site-packages/clang/native.
_HARNESS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
command -v cargo > /dev/null 2>&1 || PATH="$HOME/.cargo/bin:$PATH"
command -v lake > /dev/null 2>&1 || PATH="$HOME/.elan/bin:$PATH"
export PATH
mkdir -p "${CARGO_TARGET_DIR:-$_HARNESS_DIR/target}"
CARGO_TARGET_DIR="$(cd "${CARGO_TARGET_DIR:-$_HARNESS_DIR/target}" && pwd)"
export CARGO_TARGET_DIR
if [ -n "${LIBCLANG_PATH:-}" ]; then
  export LIBCLANG_PATH LD_LIBRARY_PATH="$LIBCLANG_PATH${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
  # a bare libclang (the pip package) ships no C headers: point it at the compiler's own
  if [ -z "${BINDGEN_EXTRA_CLANG_ARGS:-}" ] && command -v gcc > /dev/null 2>&1; then
    export BINDGEN_EXTRA_CLANG_ARGS="-I$(gcc -print-file-name=include)"
  fi
fi
