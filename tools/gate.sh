#!/bin/sh
# The one check command (Q-08). The items and their order are in tools/gate_steps.py.
#   tools/gate.sh [--stage-end STAGE]
cd "$(dirname "$0")/.." || exit 2
if ! python3 -c 'import sys; sys.exit(0 if sys.version_info >= (3, 11) else 1)' 2>/dev/null; then
    echo "tools/gate.sh needs python3 3.11 or later (tomllib); found: $(python3 --version 2>&1)" >&2
    exit 2
fi
PYTHONDONTWRITEBYTECODE=1 exec python3 -B tools/gate.py "$@"
