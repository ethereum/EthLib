#!/usr/bin/env bash
# Install elan v4.2.4 and the Lean toolchain of `lean-toolchain` from pinned releases, and check the SHA-256 digest of each archive first.
#
# The installer script of elan downloads its latest release, so this script downloads the release archives through GitHub's REST asset endpoint instead.
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
toolchain_file="$script_dir/../lean-toolchain"
toolchain="$(tr -d '[:space:]' < "$toolchain_file")"
if [[ "$toolchain" != "leanprover/lean4:v4.36.0" ]]; then
  echo "no pinned Lean release for $toolchain" >&2
  exit 1
fi

lean_version="4.36.0"
case "$(uname -s)-$(uname -m)" in
  Linux-x86_64)
    elan_target="x86_64-unknown-linux-gnu"
    elan_asset_id="529114798"
    elan_digest="42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63"
    lean_target="linux"
    lean_asset_id="755416458"
    lean_digest="2b7ab1ed8b92d2e6abfaf41344823b510064dbc9c0260cac73eb496ab2dea6eb"
    ;;
  Linux-aarch64)
    elan_target="aarch64-unknown-linux-gnu"
    elan_asset_id="529114794"
    elan_digest="05febd124d84ebf994b2e7479922a5650b1e950c17ae3bd1ddd776b65bb72bf9"
    lean_target="linux_aarch64"
    lean_asset_id="755416453"
    lean_digest="35471998152191ef809418ce5bf61f8fc5f209e5e3be05b48bdc4949fdb3e726"
    ;;
  Darwin-arm64)
    elan_target="aarch64-apple-darwin"
    elan_asset_id="529120756"
    elan_digest="7ad829861392c718dfebde3a83b5c8508df47be02af68894b094b0b3952616e5"
    lean_target="darwin_aarch64"
    lean_asset_id="755416456"
    lean_digest="49acada8749ad1343eff1224a3d2510ac61ed53363d37b5e738e8c587e7deabd"
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
# The token, when set, reaches curl on standard input, so it never appears on a command line.
download_asset() {
  local out="$1"
  local url="https://api.github.com/repos/$2/releases/assets/$3"
  local -a curl_args=(-sSfL --retry 5 --retry-delay 2 --retry-all-errors -H "Accept: application/octet-stream")
  if [[ -n "${GITHUB_TOKEN:-}" ]]; then
    printf 'Authorization: Bearer %s\n' "$GITHUB_TOKEN" | curl "${curl_args[@]}" -H @- -o "$out" "$url"
  else
    curl "${curl_args[@]}" -o "$out" "$url"
  fi
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
# A toolchain counts as installed only when its `lean` binary is there.
if [[ ! -x "$toolchain_dir/bin/lean" ]]; then
  if ! command -v zstd > /dev/null; then
    echo "zstd is required to unpack the Lean toolchain" >&2
    exit 1
  fi
  lean_archive="$work_dir/lean-$lean_version-$lean_target.tar.zst"
  download_asset "$lean_archive" "leanprover/lean4" "$lean_asset_id"
  check_sha256 "$lean_digest" "$lean_archive"

  # Unpack next to the final directory, so that the last step is a rename on one filesystem.
  # A partial directory from an interrupted run moves into the unpack directory, which the trap removes.
  mkdir -p "$elan_home/toolchains"
  unpack_dir="$(mktemp -d "$elan_home/toolchains/.unpack.XXXXXX")"
  trap 'rm -rf "$work_dir" "$unpack_dir"' EXIT
  zstd -dc "$lean_archive" | tar -xf - -C "$unpack_dir"
  if [[ -e "$toolchain_dir" ]]; then
    mv "$toolchain_dir" "$unpack_dir/partial"
  fi
  mv "$unpack_dir/lean-$lean_version-$lean_target" "$toolchain_dir"
fi
