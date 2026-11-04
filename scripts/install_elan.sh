#!/usr/bin/env bash
# Install elan from a pinned release, and check the digest of the archive first.
# elan then installs the Lean toolchain that `lean-toolchain` names.
#
# The installer script of elan downloads its latest release, so this script
# downloads the release archive itself instead.
set -euo pipefail

version="v4.2.4"
case "$(uname -s)-$(uname -m)" in
  Linux-x86_64)
    target="x86_64-unknown-linux-gnu"
    digest="42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63"
    ;;
  Linux-aarch64)
    target="aarch64-unknown-linux-gnu"
    digest="05febd124d84ebf994b2e7479922a5650b1e950c17ae3bd1ddd776b65bb72bf9"
    ;;
  Darwin-arm64)
    target="aarch64-apple-darwin"
    digest="7ad829861392c718dfebde3a83b5c8508df47be02af68894b094b0b3952616e5"
    ;;
  *)
    echo "no pinned elan release for $(uname -s) $(uname -m)" >&2
    exit 1
    ;;
esac

work_dir="$(mktemp -d)"
trap 'rm -rf "$work_dir"' EXIT
archive="$work_dir/elan-$target.tar.gz"
curl -sSfL -o "$archive" \
  "https://github.com/leanprover/elan/releases/download/$version/elan-$target.tar.gz"

# macOS has shasum, and the manylinux image has sha256sum.
if command -v sha256sum > /dev/null; then
  echo "$digest  $archive" | sha256sum -c -
else
  echo "$digest  $archive" | shasum -a 256 -c -
fi

tar -xzf "$archive" -C "$work_dir"
"$work_dir/elan-init" -y --default-toolchain none
