#!/usr/bin/env bash
# Run the vector suites against an installed wheel, then check the pinned vectors.
# cibuildwheel runs it with the path of the project, in an environment where the wheel is installed.
#
# The suites rewrite every vector case, so they run on a copy of the tests.
# The copy holds no `ethlib` package, so the tests import the installed wheel.
# The slow cases of leanXMSS and leanSPHINCS stay skipped, as in CI.
set -euo pipefail

project="$1"
work_dir="$(mktemp -d)"
trap 'rm -rf "$work_dir"' EXIT

mkdir -p "$work_dir/bindings/python"
cp -R "$project/tests" "$work_dir/tests"
cp -R "$project/bindings/python/tests" "$work_dir/bindings/python/tests"
# The other files that the suites and the vector check read: the binding contract and the C
# sources that it describes, the KZG trusted setup, and the archive fetcher.
cp -R "$project/bindings/contract" "$work_dir/bindings/contract"
cp "$project"/bindings/python/*.c "$work_dir/bindings/python/"
mkdir -p "$work_dir/EthLib/Cryptography/Kzg" "$work_dir/scripts"
cp "$project/EthLib/Cryptography/Kzg/TrustedSetupData.lean" "$work_dir/EthLib/Cryptography/Kzg/"
cp "$project/scripts/fetch_archives.py" "$work_dir/scripts/"
# The pytest settings of the project are in pyproject.toml.
cp "$project/pyproject.toml" "$work_dir/pyproject.toml"

cd "$work_dir"
python -c "import ethlib, sys; print('testing', ethlib.__file__, 'with Python', sys.version)"
python -m pytest -p no:cacheprovider
python tests/cryptography/check_vectors.py
