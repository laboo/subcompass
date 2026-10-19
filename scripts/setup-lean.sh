#!/usr/bin/env bash
# Gets Lean and Mathlib working for this repo on Linux, then builds it once.
#
# Lean's usual installer downloads from release.lean-lang.org, and Mathlib's
# built files come from cache.mathlib.org; some sandboxes (Claude's cloud
# sessions among them) block both, while GitHub is reachable. So this script
# fetches everything from GitHub instead:
#   1. elan, Lean's version manager;
#   2. the exact Lean version named in the file `lean-toolchain`;
#   3. Mathlib with all its built files, from this repo's release named in
#      MATHLIB_TAG below (made by .github/workflows/mathlib.yml), unpacked
#      once into ~/.cache/subcompass and linked into this repo as
#      .lake/packages, so nothing in Mathlib is ever rebuilt.
# It is safe to run more than once; finished steps are skipped.
#
# Usage, from anywhere inside the repo:
#   scripts/setup-lean.sh
# Afterwards, `lake build` (with ~/.elan/bin on PATH) builds everything.
set -euo pipefail

# The Mathlib release to use. Keep it in step with the mathlib entries in
# lakefile.toml and lake-manifest.json, and with mathlib.yml.
MATHLIB_TAG=mathlib-v4.35.0
REPO_URL=https://github.com/laboo/subcompass

cd "$(dirname "$0")/.."
toolchain=$(tr -d '[:space:]' < lean-toolchain)     # e.g. leanprover/lean4:v4.35.0
version=${toolchain##*:v}                          # e.g. 4.35.0
ELAN_HOME=${ELAN_HOME:-$HOME/.elan}
CACHE=${SUBCOMPASS_CACHE:-$HOME/.cache/subcompass}
export ELAN_HOME PATH="$ELAN_HOME/bin:$PATH"

case "$(uname -m)" in
  x86_64)        elan_arch=x86_64;  lean_suffix=linux ;;
  aarch64|arm64) elan_arch=aarch64; lean_suffix=linux_aarch64 ;;
  *) echo "Unsupported machine: $(uname -m)" >&2; exit 1 ;;
esac

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# Unpacks a .tar.zst read from standard input into the folder $1, giving
# every file to the current user. (The Mathlib pack records the user id of
# GitHub's builder, and git refuses folders owned by someone else as
# "dubious ownership".)
cat > "$tmp/unpack.py" <<'PY'
import sys, tarfile, zstandard

class Tar(tarfile.TarFile):
    def chown(self, *args, **kwargs):  # keep files owned by the current user
        pass

stream = zstandard.ZstdDecompressor().stream_reader(sys.stdin.buffer)
with Tar.open(fileobj=stream, mode="r|") as t:
    try:
        t.extractall(sys.argv[1], filter="tar")
    except TypeError:  # Python older than 3.12 has no filter argument
        t.extractall(sys.argv[1])
PY
unpack_zst() {
  if command -v zstd >/dev/null 2>&1; then
    zstd -dc | tar -x --no-same-owner -C "$1"
  else
    # No zstd program: unpack with Python's zstandard module instead.
    python3 -c "import zstandard" 2>/dev/null ||
      python3 -m pip install --quiet zstandard 2>/dev/null ||
      python3 -m pip install --quiet --break-system-packages zstandard
    python3 "$tmp/unpack.py" "$1"
  fi
}

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
  unpack_zst "$dest" < "$tmp/$archive.tar.zst"
  elan toolchain link "$toolchain" "$dest/$archive"
fi
lean --version

# 3. Mathlib, already built, from this repo's release
mathlib="$CACHE/$MATHLIB_TAG"
packages="$mathlib/mathlib-project/.lake/packages"
if [ -f "$mathlib/.complete" ]; then
  echo "Mathlib ($MATHLIB_TAG) is already unpacked in $mathlib."
else
  echo "Downloading Mathlib from GitHub (about 1.9 GB, 7.3 GB unpacked)..."
  rm -rf "${mathlib:?}"
  mkdir -p "$mathlib"
  base="$REPO_URL/releases/download/$MATHLIB_TAG"
  curl -fsSL --retry 5 -o "$mathlib/$MATHLIB_TAG.sha256" "$base/$MATHLIB_TAG.sha256"
  parts=$(awk '{print $2}' "$mathlib/$MATHLIB_TAG.sha256")
  for part in $parts; do
    curl -fsSL --retry 5 -o "$mathlib/$part" "$base/$part"
  done
  (cd "$mathlib" && sha256sum -c --quiet "$MATHLIB_TAG.sha256")
  echo "Unpacking Mathlib..."
  (cd "$mathlib" && cat $parts) | unpack_zst "$mathlib"
  (cd "$mathlib" && rm -f $parts "$MATHLIB_TAG.sha256")
  touch "$mathlib/.complete"
fi
mkdir -p .lake
if [ "$(readlink .lake/packages || true)" != "$packages" ]; then
  rm -rf .lake/packages
  ln -s "$packages" .lake/packages
fi

echo "Building (lake build)..."
lake build
echo
echo "Done. In a new shell, put Lean on your PATH first:"
echo "  export PATH=\"$ELAN_HOME/bin:\$PATH\""
