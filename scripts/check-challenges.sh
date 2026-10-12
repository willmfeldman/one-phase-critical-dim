#!/usr/bin/env bash
# Elaborate every comparator challenge workspace in a trusted checkout, and check the axioms of
# every solution theorem.
#
# For each challenges/*/config.json this builds Vocabulary, Challenge and Solution, then runs
# `#print axioms` on each theorem in the config and requires exactly the config's
# permitted_axioms. It shows that the files elaborate and that the solutions are sorry-free. It
# does NOT check that Challenge and Solution state the same theorems: only Comparator does that
# (.github/workflows/release-comparator.yml). Run it only on a trusted checkout, after the root
# library is built.
#
# A workspace without its own lakefile (`challenges/headline`) is a set of libraries of the root
# package, built from the repository root. Vocabulary and Solution must build without warnings;
# Challenge states the theorems with `sorry`, so it is built without `--wfail`.
#
# Set LAKE to a command to use instead of `lake` (for example a wrapper that limits parallelism;
# use absolute paths, since the command runs in the workspace or the repository root).
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
lake_() { ${LAKE:-lake} "$@"; }
status=0
for config in "$ROOT"/challenges/*/config.json; do
  dir=$(dirname "$config")
  name=$(basename "$dir")
  # A workspace without its own lakefile is built by the root lakefile.
  proj=$dir; [ -e "$dir/lakefile.toml" ] || [ -e "$dir/lakefile.lean" ] || proj=$ROOT
  echo "==> $name: lake build Vocabulary Solution (--wfail), Challenge"
  (cd "$proj" && lake_ build --wfail Vocabulary Solution && lake_ build Challenge)
  check=$(mktemp "${TMPDIR:-/tmp}/challenge-axioms-XXXXXX")
  ruby -rjson -e '
    cfg = JSON.parse(File.read(ARGV[0]))
    puts "import Solution"
    cfg["theorem_names"].each { |n| puts "#print axioms #{n}" }' "$config" > "$check.lean"
  out=$(cd "$proj" && lake_ env lean "$check.lean" 2>&1) || { echo "$out"; status=1; continue; }
  if ! ruby -rjson -e '
    cfg = JSON.parse(File.read(ARGV[0]))
    out = STDIN.read.gsub(/\s+/, " ")
    allowed = cfg["permitted_axioms"].sort
    bad = cfg["theorem_names"].reject do |n|
      m = out.match(/\x27#{Regexp.escape(n)}\x27 depends on axioms: \[([^\]]*)\]/)
      m && m[1].split(",").map(&:strip).sort == allowed
    end
    bad.each { |n| warn "#{ARGV[1]}: #{n}: axioms differ from #{allowed.inspect}" }
    exit(bad.empty? ? 0 : 1)' "$config" "$name" <<< "$out"; then
    echo "$out"
    status=1
  else
    echo "    solution axioms OK"
  fi
  rm -f "$check" "$check.lean"
done
exit $status
