#!/bin/sh
# Build the voice flow as a static library and link the C host (spec §17.5).
# Usage: ./build.sh   (needs `onsa` on the PATH or in ../../target/debug)
set -e
cd "$(dirname "$0")"
ONSA=${ONSA:-$(command -v onsa || echo ../../target/debug/onsa)}
"$ONSA" build --target host
cc -std=c11 -O2 -ffp-contract=off -fno-fast-math host.c -Itarget/host -Ltarget/host -lonsa_voice -o voice_host -lm
./voice_host && echo "wrote out.wav"
