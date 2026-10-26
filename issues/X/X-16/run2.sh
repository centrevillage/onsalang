#!/bin/bash
S=/private/tmp/claude-501/-Users-centrevillage-projects-onsalang/a2556302-b53b-4d28-907e-23e1286e4458/scratchpad/diskw
R=/Users/centrevillage/projects/onsalang
M="python3 -I $S/measure.py"
N="--changed-since c4282d1 --sample 0.1 --salt W4-03"
cd "$R" || exit 2
$M idle:20
$M fmt-props-before -- python3 -B "$S/oldrepo/tools/fmt_props.py" --root "$R" $N --binary target/debug/onsa
$M fmt-props-after -- python3 -B tools/fmt_props.py $N --binary target/debug/onsa --cases-binary target/debug/onsa_cases
$M cargo-test-norun -- cargo test --workspace --no-run
$M cargo-test-run -- cargo test --workspace --no-fail-fast
