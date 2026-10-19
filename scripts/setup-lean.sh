#!/usr/bin/env bash
# Gets Lean working for this repo on Linux, then checks every model once.
#
# Lean's usual installer downloads from release.lean-lang.org, which some
# sandboxes (Claude's cloud sessions among them) block, while GitHub is
# reachable. So this script fetches everything from GitHub instead:
#   1. elan, Lean's version manager;
#   2. the exact Lean version named in the file `lean-toolchain`.
# It is safe to run more than once; finished steps are skipped.
#
# Usage, from anywhere inside the repo:
#   scripts/setup-lean.sh
# Afterwards, `lake build` (with ~/.elan/bin on PATH) checks every model.
set -euo pipefail

cd "$(dirname "$0")/.."
toolchain=$(tr -d '[:space:]' < lean-toolchain)     # e.g. leanprover/lean4:v4.35.0
version=${toolchain##*:v}                          # e.g. 4.35.0
ELAN_HOME=${ELAN_HOME:-$HOME/.elan}
export ELAN_HOME PATH="$ELAN_HOME/bin:$PATH"

case "$(uname -m)" in
  x86_64)        elan_arch=x86_64;  lean_suffix=linux ;;
  aarch64|arm64) elan_arch=aarch64; lean_suffix=linux_aarch64 ;;
  *) echo "Unsupported machine: $(uname -m)" >&2; exit 1 ;;
esac

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# 1. elan
if ! command -v elan >/dev/null 2>&1; then
  echo "Installing elan from GitHub..."
  curl -fsSL --retry 5 -o "$tmp/elan.tar.gz" \
    "https://github.com/leanprover/elan/releases/latest/download/elan-${elan_arch}-unknown-linux-gnu.tar.gz"
  tar -xzf "$tmp/elan.tar.gz" -C "$tmp"
  "$tmp/elan-init" -y --default-toolchain none --no-modify-path
fi

# 2. The Lean version in lean-toolchain
if elan toolchain list 2>/dev/null | sed 's/ .*//' | grep -qxF "$toolchain"; then
  echo "Lean $version is already installed."
else
  echo "Downloading Lean $version from GitHub (about 600 MB, 3 GB unpacked)..."
  archive="lean-${version}-${lean_suffix}"
  curl -fsSL --retry 5 -o "$tmp/$archive.tar.zst" \
    "https://github.com/leanprover/lean4/releases/download/v${version}/${archive}.tar.zst"
  dest="$ELAN_HOME/github-toolchains"
  mkdir -p "$dest"
  rm -rf "${dest:?}/$archive"
  if command -v zstd >/dev/null 2>&1; then
    zstd -dc "$tmp/$archive.tar.zst" | tar -x -C "$dest"
  else
    # No zstd program: unpack with Python's zstandard module instead.
    python3 -c "import zstandard" 2>/dev/null ||
      python3 -m pip install --quiet zstandard 2>/dev/null ||
      python3 -m pip install --quiet --break-system-packages zstandard
    python3 - "$tmp/$archive.tar.zst" "$dest" <<'PY'
import sys, tarfile, zstandard
with open(sys.argv[1], "rb") as f:
    with tarfile.open(fileobj=zstandard.ZstdDecompressor().stream_reader(f), mode="r|") as t:
        try:
            t.extractall(sys.argv[2], filter="tar")
        except TypeError:  # Python older than 3.12 has no filter argument
            t.extractall(sys.argv[2])
PY
  fi
  elan toolchain link "$toolchain" "$dest/$archive"
fi

lean --version
echo "Checking every model (lake build)..."
lake build
echo
echo "Done. In a new shell, put Lean on your PATH first:"
echo "  export PATH=\"$ELAN_HOME/bin:\$PATH\""
