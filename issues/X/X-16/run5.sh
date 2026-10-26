#!/bin/bash
S=/private/tmp/claude-501/-Users-centrevillage-projects-onsalang/a2556302-b53b-4d28-907e-23e1286e4458/scratchpad/diskw
R=/Users/centrevillage/projects/onsalang
cd "$R" || exit 2
for f in crates/onsa_cli/tests/*.rs; do
  t=$(basename "$f" .rs)
  python3 -I "$S/measure.py" "$t" -- cargo test -q -p onsa_cli --test "$t"
done
