#!/bin/bash
# X-16: the writes after W4-18 U8 and U10c (102nd session), one at a time, nothing else running.
R=/Users/centrevillage/projects/onsalang
M="$R/issues/X/X-16/measure.py"
cd "$R" || exit 2
cargo test -q -p onsa_cli --test cli --no-run >/dev/null 2>&1 || exit 3
python3 -I "$M" idle:30
python3 -I "$M" onsa_cli-cli -- cargo test -q -p onsa_cli --test cli
python3 -I "$M" idle:20
python3 -I "$M" fuzz-shard0 -- python3 -B tools/fuzz.py --shard 0/2
python3 -I "$M" fmt-props-shard0 -- python3 -B tools/fmt_props.py --shard 0/2
python3 -I "$M" fmt-cst-shard0 -- python3 -B tools/fmt_props.py --property cst --shard 0/2
python3 -I "$M" idle:20
