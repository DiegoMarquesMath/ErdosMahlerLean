#!/usr/bin/env bash
set -euo pipefail

echo '[AUDIT] Scanning all local Lean sources, including newly created files.'
if find . -type f -name '*.lean' -not -path './.lake/*' -print0 | \
   xargs -0 grep -nE '(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)'; then
  echo '[FAIL] Found sorry/admit marker. Resolve before claiming verification.' >&2
  exit 1
fi

found="$(find . -type f -name '*.lean' -not -path './.lake/*' -print0 | \
  xargs -0 grep -nE '^[[:space:]]*(axiom|constant)[[:space:]]' | \
  grep -v '^\./ErdosMahlerLean/External/' || true)"
if [[ -n "$found" ]]; then
  printf '%s\n' "$found" >&2
  echo '[FAIL] An axiom/constant declaration exists outside the reviewed external input boundary.' >&2
  exit 1
fi

echo '[PASS] Static proof-hygiene scan passed.'
echo '[NOTE] This scan is not a theorem verification or a substitute for #print axioms.'
