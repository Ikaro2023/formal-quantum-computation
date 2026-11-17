#!/usr/bin/env bash
# Check that each `lean_lib` root file (e.g. `QuantumComputation.lean`) imports
# every `.lean` file of its library, in the exact format `lake exe mk_all`
# writes. This replaces `lake exe mk_all --check`, which has to build `mk_all`
# and its Mathlib dependencies before it can run.
#
# Usage: scripts/check_all_imported.sh   (from the repository root)
# Fix a failure with `lake exe mk_all`.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

libs=$(sed -n '/^\[\[lean_lib\]\]/,/^name/ s/^name *= *"\(.*\)"/\1/p' lakefile.toml)
[ -n "$libs" ] || { echo "no [[lean_lib]] found in lakefile.toml" >&2; exit 1; }

status=0
for lib in $libs; do
  # Solutions to challenges of the same spec re-declare that spec: no root module.
  [ "$lib" = QuantumComputationDiscoveries ] && continue
  # Same header as `mk_all` for a module-style aggregator, then the modules
  # sorted by byte order (`mk_all` sorts with `String.<`).
  expected=$(
    printf 'module  -- shake: keep-all --deprecated_module: ignore\n\n'
    git ls-files "$lib/*.lean" | sed 's|\.lean$||; s|/|.|g' | LC_ALL=C sort |
      sed 's/^/public import /'
  )
  # Ignore any optional header comment before `module`.
  if ! diff -u --label "$lib.lean" --label "expected" <(sed -n '/^module/,$p' "$lib.lean") <(printf '%s\n' "$expected"); then
    echo "::error file=$lib.lean::$lib.lean is out of date: run \`lake exe mk_all\`"
    status=1
  fi
done
[ "$status" -eq 0 ] && echo "All library files are imported."
exit "$status"
