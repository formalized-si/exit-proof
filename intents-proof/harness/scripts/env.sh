# Build environment; sourced by the scripts. Every variable can be set by the caller.
#   CARGO_TARGET_DIR  where cargo builds the harness (default: target/ in the harness directory)
#   LIBCLANG_PATH     directory that holds libclang.so, when it is not installed system-wide
#                     (nearcore's RocksDB bindings need libclang at build time).
_ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
command -v cargo > /dev/null 2>&1 || PATH="$HOME/.cargo/bin:$PATH"
export PATH
mkdir -p "${CARGO_TARGET_DIR:-$_ROOT_DIR/target}"
CARGO_TARGET_DIR="$(cd "${CARGO_TARGET_DIR:-$_ROOT_DIR/target}" && pwd)"
export CARGO_TARGET_DIR
if [ -n "${LIBCLANG_PATH:-}" ]; then
  export LIBCLANG_PATH LD_LIBRARY_PATH="$LIBCLANG_PATH${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
  if [ -z "${BINDGEN_EXTRA_CLANG_ARGS:-}" ] && command -v gcc > /dev/null 2>&1; then
    export BINDGEN_EXTRA_CLANG_ARGS="-I$(gcc -print-file-name=include)"
  fi
fi
