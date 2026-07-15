#!/usr/bin/env bash
# Synthesize the router with yosys and report the gate/FF cost.
#
#   ./IP/NoC/wave/synth.sh            # the router as emitted
#   ./IP/NoC/wave/synth.sh --blocks   # arbiter5 / xbarPort standalone,
#                                     #   i.e. what the router SHOULD cost
#
# Why both: the standalone blocks give the per-block denominator for
# judging the full router's cost.  (The emitted netlist used to carry
# ~105 duplicate arbiter5 instances — Sparkle issue #107, fixed by the
# compiler commit this branch sits on; see Router.lean's header.  The
# no-arg run measured 14418 cells / 780 FFs then, 3044 / 280 now.)
set -euo pipefail
cd "$(dirname "$0")/../../.."

WAVE=IP/NoC/wave
SV=$WAVE/router5.sv

lake build IP.NoC.Router           # refresh router5.sv from the Lean source

stat_of () {                       # $1 = top module
  yosys -p "read_verilog -sv $SV; synth -top $1 -flatten; opt -full; stat" 2>/dev/null \
    | awk '/Printing statistics/{last=NR} {line[NR]=$0} END{for(i=last;i<=NR;i++) print line[i]}' \
    | grep -E "cells$|DFF|Printing|===" || true
}

if [[ "${1:-}" == "--blocks" ]]; then
  for m in Sparkle_IP_NoC_arbiter5 Sparkle_IP_NoC_xbarPort; do
    echo "=== $m (standalone)"
    stat_of "$m"
    echo
  done
else
  echo "=== Sparkle_IP_NoC_router5 (as emitted)"
  stat_of Sparkle_IP_NoC_router5
fi
