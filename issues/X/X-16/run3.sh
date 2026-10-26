#!/bin/bash
S=/private/tmp/claude-501/-Users-centrevillage-projects-onsalang/a2556302-b53b-4d28-907e-23e1286e4458/scratchpad/diskw
R=/Users/centrevillage/projects/onsalang
cd "$R" || exit 2
for p in onsa_cli onsa_tests onsa_sema onsa_syntax onsa_driver onsa_interp onsa_core onsa_backend_c onsa_lsp onsa_diag; do
  python3 -I "$S/measure.py" "test-$p" -- cargo test -p "$p" --no-fail-fast
done
