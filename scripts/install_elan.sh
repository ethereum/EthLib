#!/usr/bin/env bash
# Install elan v4.2.4 and the Lean toolchain of `lean-toolchain` from pinned releases, and check the SHA-256 digest of each archive first.
#
# The installer script of elan downloads its latest release, so this script downloads the release archives through GitHub's REST asset endpoint instead.
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
toolchain_file="$script_dir/../lean-toolchain"
toolchain="$(tr -d '[:space:]' < "$toolchain_file")"
if [[ "$toolchain" != "leanprover/lean4:v4.35.0" ]]; then
  echo "no pinned Lean release for $toolchain" >&2
  exit 1
fi

lean_version="4.35.0"
case "$(uname -s)-$(uname -m)" in
  Linux-x86_64)
    elan_target="x86_64-unknown-linux-gnu"
    elan_asset_id="529114798"
    elan_digest="42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63"
    lean_target="linux"
    lean_asset_id="634574462"
    lean_digest="7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d"
    ;;
  Linux-aarch64)
    elan_target="aarch64-unknown-linux-gnu"
    elan_asset_id="529114794"
    elan_digest="05febd124d84ebf994b2e7479922a5650b1e950c17ae3bd1ddd776b65bb72bf9"
    lean_target="linux_aarch64"
    lean_asset_id="634574469"
    lean_digest="c8f0f8a3920e839718b1343e6781fd80a3e9b1024fbcd7078eb30f54e806b028"
    ;;
  Darwin-arm64)
    elan_target="aarch64-apple-darwin"
    elan_asset_id="529120756"
    elan_digest="7ad829861392c718dfebde3a83b5c8508df47be02af68894b094b0b3952616e5"
    lean_target="darwin_aarch64"
    lean_asset_id="634574458"
    lean_digest="c0c6f34f35ba1dcc5c4a5fd106fefab9eb5e8469712624dd2c868d51b63177c2"
    ;;
  *)
    echo "no pinned release for $(uname -s) $(uname -m)" >&2
    exit 1
    ;;
esac

# macOS has shasum, and the manylinux image has sha256sum.
check_sha256() {
  if command -v sha256sum > /dev/null; then
    echo "$1  $2" | sha256sum -c -
  else
    echo "$1  $2" | shasum -a 256 -c -
  fi
}

# Download via GitHub's REST asset endpoint, which redirects straight to blob storage without hitting the web release redirector.
download_asset() {
  local out="$1"
  local repo="$2"
  local asset_id="$3"
  local -a auth_args=()
  if [[ -n "${GITHUB_TOKEN:-}" ]]; then
    auth_args=(-H "Authorization: Bearer $GITHUB_TOKEN")
  fi
  curl -sSfL --retry 5 --retry-delay 2 --retry-all-errors \
    -H "Accept: application/octet-stream" "${auth_args[@]}" \
    -o "$out" "https://api.github.com/repos/$repo/releases/assets/$asset_id"
}

work_dir="$(mktemp -d)"
trap 'rm -rf "$work_dir"' EXIT

elan_archive="$work_dir/elan-$elan_target.tar.gz"
download_asset "$elan_archive" "leanprover/elan" "$elan_asset_id"
check_sha256 "$elan_digest" "$elan_archive"

tar -xzf "$elan_archive" -C "$work_dir"
"$work_dir/elan-init" -y --default-toolchain none --no-modify-path

elan_home="${ELAN_HOME:-$HOME/.elan}"
toolchain_dir="$elan_home/toolchains/leanprover--lean4---v$lean_version"
if [[ ! -d "$toolchain_dir" ]]; then
  lean_archive="$work_dir/lean-$lean_version-$lean_target.tar.zst"
  download_asset "$lean_archive" "leanprover/lean4" "$lean_asset_id"
  check_sha256 "$lean_digest" "$lean_archive"
  mkdir -p "$elan_home/toolchains"
  zstd -dc "$lean_archive" | tar -xf - -C "$work_dir"
  mv "$work_dir/lean-$lean_version-$lean_target" "$toolchain_dir"
fi
