#!/bin/bash
# Measure the disk writes of each heavy step alone, one after another (nothing else may run).
S=/private/tmp/claude-501/-Users-centrevillage-projects-onsalang/a2556302-b53b-4d28-907e-23e1286e4458/scratchpad/diskw
R=/Users/centrevillage/projects/onsalang
M="python3 -I $S/measure.py"
N="--changed-since c4282d1 --sample 0.1 --salt W4-03"
cd "$R" || exit 2
$M idle:30
$M fmt-props-after -- python3 -B tools/fmt_props.py $N --binary target/debug/onsa --cases-binary target/debug/onsa_cases
$M fmt-props-before -- python3 -B "$S/old_tools/fmt_props.py" --root "$R" $N --binary target/debug/onsa
$M fmt-cst -- python3 -B tools/fmt_props.py --property cst $N --binary target/debug/onsa --cases-binary target/debug/onsa_cases
$M fuzz -- python3 -B tools/fuzz.py $N
$M cargo-test-warm -- cargo test --workspace --no-fail-fast
rm -rf "$S/tdir1" "$S/tdir2"
CARGO_TARGET_DIR="$S/tdir1" $M fresh-build-default -- cargo test --workspace --no-run
du -sh "$S/tdir1"
CARGO_TARGET_DIR="$S/tdir2" CARGO_PROFILE_DEV_DEBUG=line-tables-only $M fresh-build-line-tables -- cargo test --workspace --no-run
du -sh "$S/tdir2"
rm -rf "$S/tdir1" "$S/tdir2"
$M idle:30
