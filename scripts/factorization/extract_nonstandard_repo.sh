#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: extract_nonstandard_repo.sh [output_dir] [--init-git] [--no-checks]

Examples:
  extract_nonstandard_repo.sh
  extract_nonstandard_repo.sh _split_repos/stochasticpde-nonstandard
  extract_nonstandard_repo.sh /tmp/stochasticpde-nonstandard --init-git
USAGE
}

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
OUT_DIR="$ROOT_DIR/_split_repos/stochasticpde-nonstandard"
INIT_GIT="false"
RUN_CHECKS="true"

for arg in "$@"; do
  case "$arg" in
    --init-git)
      INIT_GIT="true"
      ;;
    --no-checks)
      RUN_CHECKS="false"
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    --*)
      echo "unknown flag: $arg" >&2
      usage
      exit 2
      ;;
    *)
      if [[ "$OUT_DIR" != "$ROOT_DIR/_split_repos/stochasticpde-nonstandard" ]]; then
        echo "multiple output directories provided" >&2
        usage
        exit 2
      fi
      OUT_DIR="$arg"
      ;;
  esac
done

if [[ ! -d "$ROOT_DIR/StochasticPDE/Nonstandard" || ! -f "$ROOT_DIR/StochasticPDE/Nonstandard.lean" ]]; then
  echo "missing Nonstandard source tree in this checkout; nothing to extract" >&2
  exit 1
fi

if [[ -e "$OUT_DIR" && -n "$(ls -A "$OUT_DIR" 2>/dev/null || true)" ]]; then
  echo "target directory exists and is not empty: $OUT_DIR" >&2
  exit 1
fi

MATHLIB_REV="$(
  awk '
    BEGIN { in_req = 0; req_name = "" }
    /^\[\[require\]\]/ { in_req = 1; req_name = ""; next }
    in_req && /^name = / {
      req_name = $3
      gsub(/"/, "", req_name)
      next
    }
    in_req && /^rev = / && req_name == "mathlib" {
      rev = $3
      gsub(/"/, "", rev)
      print rev
      exit
    }
  ' "$ROOT_DIR/lakefile.toml"
)"

if [[ -z "$MATHLIB_REV" ]]; then
  echo "failed to read mathlib rev from $ROOT_DIR/lakefile.toml" >&2
  exit 1
fi

mkdir -p "$OUT_DIR/StochasticPDE"
cp -R "$ROOT_DIR/StochasticPDE/Nonstandard" "$OUT_DIR/StochasticPDE/Nonstandard"
cp "$ROOT_DIR/StochasticPDE/Nonstandard.lean" "$OUT_DIR/StochasticPDE/Nonstandard.lean"
cp "$ROOT_DIR/lean-toolchain" "$OUT_DIR/lean-toolchain"
cp "$ROOT_DIR/lake-manifest.json" "$OUT_DIR/lake-manifest.json"

cat > "$OUT_DIR/lakefile.toml" <<EOF
name = "StochasticPDENonstandard"
version = "0.1.0"
defaultTargets = ["StochasticPDE.Nonstandard"]

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "$MATHLIB_REV"

[[lean_lib]]
name = "StochasticPDE"
EOF

cat > "$OUT_DIR/.gitignore" <<'EOF'
/.lake/
/build/
/.DS_Store
EOF

SORRY_COUNT="$(
  (rg -n '^\s*sorry\b' "$OUT_DIR/StochasticPDE/Nonstandard" --glob '*.lean' || true) | wc -l | tr -d ' '
)"
TODAY="$(date +%F)"

cat > "$OUT_DIR/README.md" <<EOF
# stochasticpde-nonstandard

Standalone split of \`StochasticPDE.Nonstandard\` from the StochasticPDE monorepo.

## Status ($TODAY)

1. Theorem-level \`sorry\` count in \`StochasticPDE/Nonstandard\`: $SORRY_COUNT
2. Lean namespace preserved as \`StochasticPDE.Nonstandard.*\`.
3. Build target: \`lake build StochasticPDE.Nonstandard\`.

## Quick Checks

\`\`\`bash
lake build StochasticPDE.Nonstandard
rg -n '^\s*sorry\b' StochasticPDE/Nonstandard --glob '*.lean'
\`\`\`
EOF

# Reuse local package cache for offline validation when available.
if [[ -d "$ROOT_DIR/.lake/packages" ]]; then
  mkdir -p "$OUT_DIR/.lake"
  if [[ ! -e "$OUT_DIR/.lake/packages" ]]; then
    ln -s "$ROOT_DIR/.lake/packages" "$OUT_DIR/.lake/packages"
  fi
fi

if command -v lake >/dev/null 2>&1; then
  if ! (cd "$OUT_DIR" && lake update >/dev/null); then
    echo "warning: lake update failed in $OUT_DIR; using existing package cache if present" >&2
  fi
fi

if [[ "$RUN_CHECKS" == "true" ]]; then
  echo
  echo "== import-boundary scan =="
  IMPORTS="$(
    rg -n '^import StochasticPDE\.' \
      "$OUT_DIR/StochasticPDE/Nonstandard" "$OUT_DIR/StochasticPDE/Nonstandard.lean" --glob '*.lean' || true
  )"
  printf '%s\n' "$IMPORTS"

  CROSS_IMPORTS="$(printf '%s\n' "$IMPORTS" | rg -v 'import StochasticPDE\.Nonstandard(\.|$)' || true)"
  if [[ -n "$CROSS_IMPORTS" ]]; then
    echo
    echo "cross-package imports detected:"
    printf '%s\n' "$CROSS_IMPORTS"
    exit 1
  fi

  echo
  echo "== build check =="
  (
    cd "$OUT_DIR"
    lake build StochasticPDE.Nonstandard
  )
fi

if [[ "$INIT_GIT" == "true" ]]; then
  git -C "$OUT_DIR" init
  git -C "$OUT_DIR" add .
  git -C "$OUT_DIR" commit -m "Initial split from StochasticPDE (Nonstandard)"
fi

echo
echo "extracted split repo at: $OUT_DIR"
