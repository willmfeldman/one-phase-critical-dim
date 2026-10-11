#!/bin/bash
# Local acceptance check for a challenge workspace (a substitute for a Comparator run,
# which needs Linux). Run from anywhere, in a trusted checkout, after the root library is built.
#
# 1. Builds Vocabulary, Challenge and Solution with `lake`, or with the command in the environment
#    variable LAKE if it is set (for example a wrapper that limits parallelism).
# 2. Runs `#print axioms` on every theorem of config.json in the Solution environment. Each must
#    use only the permitted axioms; `sorryAx` or any other axiom is a failure.
# 3. Checks that Vocabulary.lean is a verbatim copy (after the copyright header) of
#    OnePhaseDimension/Sanity/Textbook/Defs.lean.
# 4. Emulates Comparator's statement check: a structural fingerprint (hashes of types, definition
#    values and inductive shapes) of the challenge theorems and of every project constant they
#    depend on, once in the Challenge environment and once in the Solution environment, must be
#    identical.
#
# Usage: challenges/<name>/check.sh [--strict]   (--strict is accepted for compatibility; the
# check is always strict)
set -u
ws=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$ws/../.." && pwd)
cd "$ws" || exit 2
lake_() { ${LAKE:-lake} "$@"; }
status=0

echo "==> Vocabulary.lean is a verbatim copy of the library file"
if diff <(tail -n +6 Vocabulary.lean) <(tail -n +6 "$root/OnePhaseDimension/Sanity/Textbook/Defs.lean") > /dev/null; then
  echo "  VERBATIM"
else
  echo "  DIFFERENT from OnePhaseDimension/Sanity/Textbook/Defs.lean"; status=1
fi

echo "==> build Vocabulary Challenge Solution"
build_log=$(lake_ build Vocabulary Challenge Solution 2>&1); build_status=$?
printf '%s\n' "$build_log" | grep -E "^error|✖|Build completed"
if [ $build_status -ne 0 ]; then echo "BUILD FAILED"; exit 1; fi

thms=$(python3 -I -c "import json,sys;print(' '.join(json.load(open(sys.argv[1]))['theorem_names']))" config.json)
allowed=$(python3 -I -c "import json,sys;print(' '.join(json.load(open(sys.argv[1]))['permitted_axioms']))" config.json)

echo "==> axioms"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/challenge-XXXXXX")
{ echo "import Solution"; for t in $thms; do echo "#print axioms $t"; done; } > "$tmp/axioms.lean"
out=$(lake_ env lean "$tmp/axioms.lean" 2>&1 | tr '\n' ' ' | tr -s ' ')
for t in $thms; do
  axs=$(printf '%s' "$out" | sed -n "s/.*'$t' depends on axioms: \[\([^]]*\)\].*/\1/p" | tr -d ' ' | tr ',' ' ')
  if printf '%s' "$out" | grep -q "'$t' does not depend on any axioms"; then axs=""; fi
  if ! printf '%s' "$out" | grep -q "'$t'"; then echo "  MISSING  $t"; status=1; continue; fi
  bad=""
  for a in $axs; do
    if ! printf ' %s ' "$allowed" | grep -q " $a "; then bad="$bad $a"; fi
  done
  if [ -n "$bad" ]; then echo "  FAIL     $t: forbidden axioms:$bad"; status=1
  else echo "  OK       $t [$axs]"; fi
done

echo "==> statement fingerprints (Challenge vs Solution)"
lake_ env lean --run tools/fingerprint.lean Challenge $thms > "$tmp/challenge" 2>&1
lake_ env lean --run tools/fingerprint.lean Solution $thms > "$tmp/solution" 2>&1
if grep -q MISSING "$tmp/challenge" "$tmp/solution"; then
  echo "  MISSING constants:"; grep MISSING "$tmp/challenge" "$tmp/solution"; status=1
elif diff "$tmp/challenge" "$tmp/solution" > "$tmp/diff"; then
  echo "  IDENTICAL ($(wc -l < "$tmp/challenge" | tr -d ' ') constants)"
else
  echo "  DIFFERENT"; cat "$tmp/diff"; status=1
fi
rm -rf "$tmp"
[ $status = 0 ] && echo "PASS" || echo "FAIL"
exit $status
