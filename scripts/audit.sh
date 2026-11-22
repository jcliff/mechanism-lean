#!/usr/bin/env bash
# Build, check axioms, and re-verify every declaration with the kernel replayer.
set -euo pipefail
cd "$(dirname "$0")/.."

lake build

echo "== Axiom audit"
out="$(lake env lean Check.lean)"
echo "$out"

axiom_lines="$(grep "depends on axioms" <<<"$out" || true)"
expected=5
count="$(grep -c "depends on axioms" <<<"$out" || true)"
if [[ "$count" -ne "$expected" ]]; then
  echo "FAIL: expected $expected axiom reports, got $count" >&2
  exit 1
fi
bad="$(grep -oE '\[[^]]*\]' <<<"$axiom_lines" | tr -d '[] ' | tr ',' '\n' \
  | grep -vxE 'propext|Classical\.choice|Quot\.sound' || true)"
if [[ -n "$bad" ]]; then
  echo "FAIL: non-standard axioms used: $bad" >&2
  exit 1
fi
if grep -q "sorry" Mechanism.lean; then
  echo "FAIL: sorry found" >&2
  exit 1
fi

echo "== Independent replay (leanchecker --fresh)"
lake env leanchecker --fresh Mechanism
echo "OK: all checks passed"
