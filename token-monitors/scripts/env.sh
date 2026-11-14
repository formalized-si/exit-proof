# Build environment; sourced by the kit's scripts. Every variable can be set by the caller.
#   TOKEN_MONITORS_BUILD  where the kit keeps everything it builds or downloads
#                         (default: build/ inside the kit directory)
#   CARGO_TARGET_DIR      cargo target directory of the trace generator
#                         (default: $TOKEN_MONITORS_BUILD/target)
#   JOBS                  parallel jobs (default: the number of cores, at most 8)
#   LIBCLANG_PATH         directory that holds libclang.so, when it is not installed system-wide.
#                         nearcore's RocksDB bindings need libclang at build time; without root,
#                         `python3 -m pip install libclang` provides one in site-packages/clang/native.
_KIT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
command -v cargo > /dev/null 2>&1 || PATH="$HOME/.cargo/bin:$PATH"
export PATH
TOKEN_MONITORS_BUILD="${TOKEN_MONITORS_BUILD:-$_KIT_ROOT/build}"
mkdir -p "$TOKEN_MONITORS_BUILD"
TOKEN_MONITORS_BUILD="$(cd "$TOKEN_MONITORS_BUILD" && pwd)"
export TOKEN_MONITORS_BUILD
mkdir -p "${CARGO_TARGET_DIR:-$TOKEN_MONITORS_BUILD/target}"
CARGO_TARGET_DIR="$(cd "${CARGO_TARGET_DIR:-$TOKEN_MONITORS_BUILD/target}" && pwd)"
export CARGO_TARGET_DIR
if [ -z "${JOBS:-}" ]; then
  JOBS=$(nproc 2> /dev/null || echo 4)
  [ "$JOBS" -gt 8 ] && JOBS=8
fi
export JOBS
if [ -n "${LIBCLANG_PATH:-}" ]; then
  export LIBCLANG_PATH LD_LIBRARY_PATH="$LIBCLANG_PATH${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
  # a bare libclang (the pip package) ships no C headers: point it at the compiler's own
  if [ -z "${BINDGEN_EXTRA_CLANG_ARGS:-}" ] && command -v gcc > /dev/null 2>&1; then
    export BINDGEN_EXTRA_CLANG_ARGS="-I$(gcc -print-file-name=include)"
  fi
fi
FTMON="$CARGO_TARGET_DIR/release/ftmon"
