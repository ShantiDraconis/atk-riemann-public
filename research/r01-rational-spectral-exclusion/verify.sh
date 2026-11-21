#!/usr/bin/env bash
# Run with bash verify.sh, with elan and git on PATH.
set -euo pipefail
sources=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
revision=751835c6e1aa915d261828e5a120345bc5d2462c
if [[ -n "${ATK_CHECKOUT:-}" ]]; then
  git -C "$ATK_CHECKOUT" archive "$revision" imports/M-Core/atk-kernel | tar -x -C "$tmp"
else
git -C "$tmp" init -q
git -C "$tmp" fetch -q --depth=1 https://github.com/ShantiDraconis/atk-math-core-public "$revision"
git -C "$tmp" checkout -q --detach FETCH_HEAD
test "$(git -C "$tmp" rev-parse HEAD)" = "$revision"
fi
cd "$tmp/imports/M-Core/atk-kernel"
lake --version
lean --version
lake exe cache get Mathlib
lake build ATK.BarreiraZero
mkdir -p "$tmp/modules"
export LEAN_PATH="$tmp/modules${LEAN_PATH:+:$LEAN_PATH}"
for mod in Closure Exclusion ConcreteClosure; do
  cp "$sources/$mod.lean" "$mod.lean"
  lake env lean -DwarningAsError=true -o "$tmp/modules/$mod.olean" "$mod.lean"
done
cat > AuditR01.lean <<'LEAN'
import ConcreteClosure
import Exclusion
#print axioms R01.concrete_exclusion
#print axioms R01.concrete_strip_of_certificates
#print axioms R01.concrete_inf_zero
#print axioms R01.mathlib_rh_of_concrete_certificates
#print axioms R01.certificates_of_log_rate
#print axioms R01.concrete_closure_of_log_rate
LEAN
lake env lean AuditR01.lean | tee "$tmp/report"
python3 - "$tmp/report" <<'PY'
import pathlib, re, sys
report = pathlib.Path(sys.argv[1]).read_text()
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name in ("concrete_exclusion", "concrete_strip_of_certificates",
             "concrete_inf_zero", "mathlib_rh_of_concrete_certificates",
             "certificates_of_log_rate", "concrete_closure_of_log_rate"):
    label = re.escape("'R01." + name + "'")
    matches = re.findall(label + r"\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", report)
    if len(matches) != 1:
        sys.exit("Missing or ambiguous axiom report for " + name)
    unexpected = {s.strip() for s in matches[0].split(",") if s.strip()} - allowed
    if unexpected:
        sys.exit(f"{name}: unexpected axioms {unexpected}")
print("Conditional implications audited. Quantitative R01: OPEN_MATH.")
PY
