#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
TARGET_BASE="$ROOT_DIR/_split_repos"

if [[ $# -gt 0 && "${1#--}" == "$1" ]]; then
  TARGET_BASE="$1"
  shift
fi

mkdir -p "$TARGET_BASE"

"$ROOT_DIR/scripts/factorization/extract_nonstandard_repo.sh" \
  "$TARGET_BASE/stochasticpde-nonstandard" "$@"

echo
echo "all split repos exported under: $TARGET_BASE"
