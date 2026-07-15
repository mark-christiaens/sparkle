/-
  NoC — the 5-port wormhole router, Signal DSL implementation.

  This is where `Route` + `Arbiter5` + `Crossbar` come together.

  ## Ports

  Five in, five out, indexed exactly as `allPorts`:

      0 = North   1 = South   2 = East   3 = West   4 = Local

  `Local` is the tile (CPU / accelerator) hanging off this router: input
  4 is injection, output 4 is ejection.  Each side is a valid/ready
  stream of 42-bit flits, so routers tile edge-to-edge with no glue.

  `myX` / `myY` are inputs, not parameters, so *one* Verilog module tiles
  into the whole mesh — each instance just gets its coordinate wired in.

  ## Per-input state (× 5)

      v   : flit buffer occupied
      f   : the buffered flit
      act : mid-packet — the head has gone, the tail has not
      rte : the output port the head reserved

  ## Wormhole, and where the output lock lives

  A head flit reserves an output port; body flits follow it blindly; the
  tail releases it.  The obvious implementation keeps a `locked`/`owner`
  register per output — but that is *redundant*: output `o` is reserved
  by input `i` exactly when `act_i ∧ rte_i = o`.  So we derive it:

      locked o = ⋁ᵢ (act_i ∧ rte_i = o)

  which removes 10 registers and makes "at most one input owns an output"
  true by construction rather than by invariant.  It holds because an
  output is only ever reserved by a head that won arbitration, and each
  output's arbiter grants exactly one winner per cycle.

  ## Backpressure

  `outReady_o` comes from downstream.  A grant only completes when the
  downstream port is ready, so a blocked worm stalls in place, still
  holding its reserved channels.  That is hold-and-wait — precisely the
  behaviour whose cycle-freedom is proved in `Deadlock.lean`.

  ## Known limitation (be honest about this)

  Outputs are **combinational** — `outValid`/`outFlit` fall straight out
  of the arbiter and crossbar in the same cycle.  So a mesh of these has
  a combinational path running through every router, and Fmax will fall
  off as the mesh grows.  Sparkle's DRC says so out loud:

      [DRC] output 'out' is not driven by a register

  Fixing it means a registered output stage, which turns the handshake
  into a skid buffer.  That is the honest next step, not a detail — see
  the note at the bottom of this file.

  A second, compiler-side caveat used to live here, and it cost real
  silicon: the emitted `router5` carried ~105 instances each of
  `arbiter5` and `xbarPort` instead of 5 + 5 — a stateful
  `@[hardware_module]` `let`-bound inside `circuit do` was re-emitted
  once per register next-state leaf, E = I·(D+1) (Sparkle issue #107;
  here I = 5 arbiters × (D = 20 registers + 1) = 105).  yosys could
  fold the combinational clones but not the stateful arbiters (merging
  those needs sequential equivalence checking, which `opt_merge` does
  not do — `-share_all` and `freduce` were tried), so the netlist
  measured 14 418 cells / 780 flip-flops where ~2 500 / ~250 belong.

  That is FIXED by the compiler commit this branch sits on (the #107
  fix): an idempotency guard for sub-module instances in the synth
  elaborator, plus a CSE + duplicate-instance-merge pass in the IR
  optimizer (`Sparkle/IR/Optimize.lean`, Phase 0.6) that folds the
  clones the elaborator-side caches cannot see through (state-derived
  wires get fresh fvars per elaboration pass; only the IR is
  canonical).  Merging the stateful clones there is sound by
  construction: same module + same inputs + same clock/reset ⇒ same
  state trajectory, which is what Sparkle's pure semantics says
  structurally identical calls denote.

  A freshly generated netlist now has exactly 5 + 5 instances and
  measures 3 044 cells / 280 flip-flops (yosys 0.66, `synth -flatten;
  opt -full`); the remaining gap to the standalone-blocks estimate is
  real buffer/control logic, not clones.  `./IP/NoC/wave/synth.sh`
  reproduces the measurement, and the regression test pinning the
  instance counts is `Tests/Compiler/Issue107LetBoundInstanceDup.lean`.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.NoC.Flit
import IP.NoC.Arbiter5
import IP.NoC.Crossbar

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.IP.NoC

/-! ## Port codes — *defined as* the spec encodings in `Flit.lean`, so
    the RTL and the proofs cannot drift apart. -/

def pNorth : BitVec 3 := Port.North.toBits
def pSouth : BitVec 3 := Port.South.toBits
def pEast  : BitVec 3 := Port.East.toBits
def pWest  : BitVec 3 := Port.West.toBits
def pLocal : BitVec 3 := Port.Local.toBits

def kHead : BitVec 2 := FlitKind.Head.toBits
def kTail : BitVec 2 := FlitKind.Tail.toBits

/-! ## Flit field extraction

    The layout is owned by `Flit.toBits` (Flit.lean), which also proves
    that `kindBits`/`destXBits`/`destYBits` invert it.  The synth
    elaborator cannot unfold value-level defs inside `map`, so the raw
    `extractLsb'` lambdas must be written out here — but the `rfl`
    proofs after each definition pin them to the spec extractors: if
    either side changes, the build fails. -/

def flitKind  {dom : DomainConfig} (f : Signal dom FlitBits) : Signal dom (BitVec 2) :=
  f.map (BitVec.extractLsb' 40 2 ·)

example (b : FlitBits) : BitVec.extractLsb' 40 2 b = kindBits b := rfl

def flitDestX {dom : DomainConfig} (f : Signal dom FlitBits) : Signal dom (BitVec 4) :=
  f.map (BitVec.extractLsb' 36 4 ·)

example (b : FlitBits) : BitVec.extractLsb' 36 4 b = destXBits b := rfl

def flitDestY {dom : DomainConfig} (f : Signal dom FlitBits) : Signal dom (BitVec 4) :=
  f.map (BitVec.extractLsb' 32 4 ·)

example (b : FlitBits) : BitVec.extractLsb' 32 4 b = destYBits b := rfl

def isHeadFlit {dom : DomainConfig} (f : Signal dom FlitBits) : Signal dom Bool :=
  flitKind f === (Signal.pure kHead)

def isTailFlit {dom : DomainConfig} (f : Signal dom FlitBits) : Signal dom Bool :=
  flitKind f === (Signal.pure kTail)

/--
  **XY route computation in hardware.**  The synthesizable mirror of
  `Route.routeXY` — same decision, same priority order.  `SimTest`
  checks the two agree on all 65 536 (myX, myY, destX, destY) inputs.
-/
def routeXYHw {dom : DomainConfig}
    (myX myY dX dY : Signal dom (BitVec 4)) : Signal dom (BitVec 3) :=
  hw_cond (Signal.pure pLocal)
    | Signal.ult myX dX => Signal.pure pEast    -- dest.x > my.x
    | Signal.ult dX myX => Signal.pure pWest    -- dest.x < my.x
    | Signal.ult myY dY => Signal.pure pNorth   -- dest.y > my.y
    | Signal.ult dY myY => Signal.pure pSouth   -- dest.y < my.y

-- Router I/O: five output streams + five upstream ready lines.
declare_signal_state RouterOut
  | oV0 : Bool      := false
  | oV1 : Bool      := false
  | oV2 : Bool      := false
  | oV3 : Bool      := false
  | oV4 : Bool      := false
  | oF0 : BitVec 42 := 0#42
  | oF1 : BitVec 42 := 0#42
  | oF2 : BitVec 42 := 0#42
  | oF3 : BitVec 42 := 0#42
  | oF4 : BitVec 42 := 0#42
  | iR0 : Bool      := false
  | iR1 : Bool      := false
  | iR2 : Bool      := false
  | iR3 : Bool      := false
  | iR4 : Bool      := false

/--
  **The 5-port wormhole router.**

  Inputs  : `myX`/`myY` (this router's mesh coordinate),
            `inV*`/`inF*` (flit streams from the five neighbours),
            `outR*` (downstream ready — backpressure).
  Outputs : `oV*`/`oF*` (flit streams out), `iR*` (ready to upstream).
-/
@[hardware_module]
def router5 {dom : DomainConfig}
    (myX myY : Signal dom (BitVec 4))
    (inV0 inV1 inV2 inV3 inV4 : Signal dom Bool)
    (inF0 inF1 inF2 inF3 inF4 : Signal dom FlitBits)
    (outR0 outR1 outR2 outR3 outR4 : Signal dom Bool)
    : Signal dom RouterOut := circuit do
  -- ── per-input state ───────────────────────────────────────────────
  -- `Signal.reg` yields a register *handle* (assigned with `<~`); the
  -- `s*` aliases are the same registers coerced to readable Signals.
  let rv0 ← Signal.reg false
  let rv1 ← Signal.reg false
  let rv2 ← Signal.reg false
  let rv3 ← Signal.reg false
  let rv4 ← Signal.reg false
  let rf0 ← Signal.reg (0#42)
  let rf1 ← Signal.reg (0#42)
  let rf2 ← Signal.reg (0#42)
  let rf3 ← Signal.reg (0#42)
  let rf4 ← Signal.reg (0#42)
  let ra0 ← Signal.reg false
  let ra1 ← Signal.reg false
  let ra2 ← Signal.reg false
  let ra3 ← Signal.reg false
  let ra4 ← Signal.reg false
  let rt0 ← Signal.reg (0#3)
  let rt1 ← Signal.reg (0#3)
  let rt2 ← Signal.reg (0#3)
  let rt3 ← Signal.reg (0#3)
  let rt4 ← Signal.reg (0#3)

  let v0 := (rv0 : Signal dom Bool)
  let v1 := (rv1 : Signal dom Bool)
  let v2 := (rv2 : Signal dom Bool)
  let v3 := (rv3 : Signal dom Bool)
  let v4 := (rv4 : Signal dom Bool)
  let f0 := (rf0 : Signal dom FlitBits)
  let f1 := (rf1 : Signal dom FlitBits)
  let f2 := (rf2 : Signal dom FlitBits)
  let f3 := (rf3 : Signal dom FlitBits)
  let f4 := (rf4 : Signal dom FlitBits)
  let a0 := (ra0 : Signal dom Bool)
  let a1 := (ra1 : Signal dom Bool)
  let a2 := (ra2 : Signal dom Bool)
  let a3 := (ra3 : Signal dom Bool)
  let a4 := (ra4 : Signal dom Bool)
  let t0 := (rt0 : Signal dom (BitVec 3))
  let t1 := (rt1 : Signal dom (BitVec 3))
  let t2 := (rt2 : Signal dom (BitVec 3))
  let t3 := (rt3 : Signal dom (BitVec 3))
  let t4 := (rt4 : Signal dom (BitVec 3))

  -- ── where does each input's current flit want to go? ──────────────
  -- A head computes its route; a body/tail blindly follows the route
  -- the head reserved.
  let d0 := Signal.mux a0 t0 (routeXYHw myX myY (flitDestX f0) (flitDestY f0))
  let d1 := Signal.mux a1 t1 (routeXYHw myX myY (flitDestX f1) (flitDestY f1))
  let d2 := Signal.mux a2 t2 (routeXYHw myX myY (flitDestX f2) (flitDestY f2))
  let d3 := Signal.mux a3 t3 (routeXYHw myX myY (flitDestX f3) (flitDestY f3))
  let d4 := Signal.mux a4 t4 (routeXYHw myX myY (flitDestX f4) (flitDestY f4))

  -- ── is output `o` reserved, and by whom? (derived, not stored) ────
  -- These are bound as explicit `let`s, one per (input, output) pair, so
  -- each is emitted as a single wire.  Written as a closure applied at
  -- 25 call sites instead, the elaborator re-expands the whole
  -- expression every time and the module explodes.
  let o0N := a0 &&& (t0 === Signal.pure pNorth)
  let o1N := a1 &&& (t1 === Signal.pure pNorth)
  let o2N := a2 &&& (t2 === Signal.pure pNorth)
  let o3N := a3 &&& (t3 === Signal.pure pNorth)
  let o4N := a4 &&& (t4 === Signal.pure pNorth)
  let o0S := a0 &&& (t0 === Signal.pure pSouth)
  let o1S := a1 &&& (t1 === Signal.pure pSouth)
  let o2S := a2 &&& (t2 === Signal.pure pSouth)
  let o3S := a3 &&& (t3 === Signal.pure pSouth)
  let o4S := a4 &&& (t4 === Signal.pure pSouth)
  let o0E := a0 &&& (t0 === Signal.pure pEast)
  let o1E := a1 &&& (t1 === Signal.pure pEast)
  let o2E := a2 &&& (t2 === Signal.pure pEast)
  let o3E := a3 &&& (t3 === Signal.pure pEast)
  let o4E := a4 &&& (t4 === Signal.pure pEast)
  let o0W := a0 &&& (t0 === Signal.pure pWest)
  let o1W := a1 &&& (t1 === Signal.pure pWest)
  let o2W := a2 &&& (t2 === Signal.pure pWest)
  let o3W := a3 &&& (t3 === Signal.pure pWest)
  let o4W := a4 &&& (t4 === Signal.pure pWest)
  let o0L := a0 &&& (t0 === Signal.pure pLocal)
  let o1L := a1 &&& (t1 === Signal.pure pLocal)
  let o2L := a2 &&& (t2 === Signal.pure pLocal)
  let o3L := a3 &&& (t3 === Signal.pure pLocal)
  let o4L := a4 &&& (t4 === Signal.pure pLocal)

  let lockN := o0N ||| o1N ||| o2N ||| o3N ||| o4N
  let lockS := o0S ||| o1S ||| o2S ||| o3S ||| o4S
  let lockE := o0E ||| o1E ||| o2E ||| o3E ||| o4E
  let lockW := o0W ||| o1W ||| o2W ||| o3W ||| o4W
  let lockL := o0L ||| o1L ||| o2L ||| o3L ||| o4L

  let freeN := ~~~ lockN
  let freeS := ~~~ lockS
  let freeE := ~~~ lockE
  let freeW := ~~~ lockW
  let freeL := ~~~ lockL

  -- ── does input i want output o? ───────────────────────────────────
  let w0N := v0 &&& (d0 === Signal.pure pNorth)
  let w1N := v1 &&& (d1 === Signal.pure pNorth)
  let w2N := v2 &&& (d2 === Signal.pure pNorth)
  let w3N := v3 &&& (d3 === Signal.pure pNorth)
  let w4N := v4 &&& (d4 === Signal.pure pNorth)
  let w0S := v0 &&& (d0 === Signal.pure pSouth)
  let w1S := v1 &&& (d1 === Signal.pure pSouth)
  let w2S := v2 &&& (d2 === Signal.pure pSouth)
  let w3S := v3 &&& (d3 === Signal.pure pSouth)
  let w4S := v4 &&& (d4 === Signal.pure pSouth)
  let w0E := v0 &&& (d0 === Signal.pure pEast)
  let w1E := v1 &&& (d1 === Signal.pure pEast)
  let w2E := v2 &&& (d2 === Signal.pure pEast)
  let w3E := v3 &&& (d3 === Signal.pure pEast)
  let w4E := v4 &&& (d4 === Signal.pure pEast)
  let w0W := v0 &&& (d0 === Signal.pure pWest)
  let w1W := v1 &&& (d1 === Signal.pure pWest)
  let w2W := v2 &&& (d2 === Signal.pure pWest)
  let w3W := v3 &&& (d3 === Signal.pure pWest)
  let w4W := v4 &&& (d4 === Signal.pure pWest)
  let w0L := v0 &&& (d0 === Signal.pure pLocal)
  let w1L := v1 &&& (d1 === Signal.pure pLocal)
  let w2L := v2 &&& (d2 === Signal.pure pLocal)
  let w3L := v3 &&& (d3 === Signal.pure pLocal)
  let w4L := v4 &&& (d4 === Signal.pure pLocal)

  -- ── request = wants it, and it is free or already his ─────────────
  -- ── one round-robin arbiter per output port ───────────────────────
  let arbN := arbiter5 (w0N &&& (freeN ||| o0N)) (w1N &&& (freeN ||| o1N))
                       (w2N &&& (freeN ||| o2N)) (w3N &&& (freeN ||| o3N))
                       (w4N &&& (freeN ||| o4N))
  let arbS := arbiter5 (w0S &&& (freeS ||| o0S)) (w1S &&& (freeS ||| o1S))
                       (w2S &&& (freeS ||| o2S)) (w3S &&& (freeS ||| o3S))
                       (w4S &&& (freeS ||| o4S))
  let arbE := arbiter5 (w0E &&& (freeE ||| o0E)) (w1E &&& (freeE ||| o1E))
                       (w2E &&& (freeE ||| o2E)) (w3E &&& (freeE ||| o3E))
                       (w4E &&& (freeE ||| o4E))
  let arbW := arbiter5 (w0W &&& (freeW ||| o0W)) (w1W &&& (freeW ||| o1W))
                       (w2W &&& (freeW ||| o2W)) (w3W &&& (freeW ||| o3W))
                       (w4W &&& (freeW ||| o4W))
  let arbL := arbiter5 (w0L &&& (freeL ||| o0L)) (w1L &&& (freeL ||| o1L))
                       (w2L &&& (freeL ||| o2L)) (w3L &&& (freeL ||| o3L))
                       (w4L &&& (freeL ||| o4L))

  let vN := Arb5Out.valid arbN
  let vS := Arb5Out.valid arbS
  let vE := Arb5Out.valid arbE
  let vW := Arb5Out.valid arbW
  let vL := Arb5Out.valid arbL

  let wN := Arb5Out.idx arbN
  let wS := Arb5Out.idx arbS
  let wE := Arb5Out.idx arbE
  let wW := Arb5Out.idx arbW
  let wL := Arb5Out.idx arbL

  -- ── crossbar: each output takes the flit of its granted input ─────
  let xb := crossbar5 wN wS wE wW wL f0 f1 f2 f3 f4
  let xN := Xbar5Out.oN xb
  let xS := Xbar5Out.oS xb
  let xE := Xbar5Out.oE xb
  let xW := Xbar5Out.oW xb
  let xL := Xbar5Out.oL xb

  -- ── a grant only completes if downstream can take it ──────────────
  let gN := vN &&& outR0
  let gS := vS &&& outR1
  let gE := vE &&& outR2
  let gW := vW &&& outR3
  let gL := vL &&& outR4

  -- ── did input i get its flit moved this cycle? ────────────────────
  -- Again: explicit lets, not a closure applied five times.
  let g0 := (gN &&& (wN === Signal.pure 0#3)) ||| (gS &&& (wS === Signal.pure 0#3)) |||
            (gE &&& (wE === Signal.pure 0#3)) ||| (gW &&& (wW === Signal.pure 0#3)) |||
            (gL &&& (wL === Signal.pure 0#3))
  let g1 := (gN &&& (wN === Signal.pure 1#3)) ||| (gS &&& (wS === Signal.pure 1#3)) |||
            (gE &&& (wE === Signal.pure 1#3)) ||| (gW &&& (wW === Signal.pure 1#3)) |||
            (gL &&& (wL === Signal.pure 1#3))
  let g2 := (gN &&& (wN === Signal.pure 2#3)) ||| (gS &&& (wS === Signal.pure 2#3)) |||
            (gE &&& (wE === Signal.pure 2#3)) ||| (gW &&& (wW === Signal.pure 2#3)) |||
            (gL &&& (wL === Signal.pure 2#3))
  let g3 := (gN &&& (wN === Signal.pure 3#3)) ||| (gS &&& (wS === Signal.pure 3#3)) |||
            (gE &&& (wE === Signal.pure 3#3)) ||| (gW &&& (wW === Signal.pure 3#3)) |||
            (gL &&& (wL === Signal.pure 3#3))
  let g4 := (gN &&& (wN === Signal.pure 4#3)) ||| (gS &&& (wS === Signal.pure 4#3)) |||
            (gE &&& (wE === Signal.pure 4#3)) ||| (gW &&& (wW === Signal.pure 4#3)) |||
            (gL &&& (wL === Signal.pure 4#3))

  -- ── input buffer: consume on grant, accept when there is room ─────
  let r0 := (~~~ v0) ||| g0
  let r1 := (~~~ v1) ||| g1
  let r2 := (~~~ v2) ||| g2
  let r3 := (~~~ v3) ||| g3
  let r4 := (~~~ v4) ||| g4

  let acc0 := inV0 &&& r0
  let acc1 := inV1 &&& r1
  let acc2 := inV2 &&& r2
  let acc3 := inV3 &&& r3
  let acc4 := inV4 &&& r4

  rv0 <~ ((v0 &&& (~~~ g0)) ||| acc0)
  rv1 <~ ((v1 &&& (~~~ g1)) ||| acc1)
  rv2 <~ ((v2 &&& (~~~ g2)) ||| acc2)
  rv3 <~ ((v3 &&& (~~~ g3)) ||| acc3)
  rv4 <~ ((v4 &&& (~~~ g4)) ||| acc4)

  rf0 <~ Signal.mux acc0 inF0 f0
  rf1 <~ Signal.mux acc1 inF1 f1
  rf2 <~ Signal.mux acc2 inF2 f2
  rf3 <~ Signal.mux acc3 inF3 f3
  rf4 <~ Signal.mux acc4 inF4 f4

  -- ── wormhole: head opens the worm, tail closes it ─────────────────
  ra0 <~ hw_cond a0 | (g0 &&& isTailFlit f0) => Signal.pure false
                   | (g0 &&& isHeadFlit f0) => Signal.pure true
  ra1 <~ hw_cond a1 | (g1 &&& isTailFlit f1) => Signal.pure false
                   | (g1 &&& isHeadFlit f1) => Signal.pure true
  ra2 <~ hw_cond a2 | (g2 &&& isTailFlit f2) => Signal.pure false
                   | (g2 &&& isHeadFlit f2) => Signal.pure true
  ra3 <~ hw_cond a3 | (g3 &&& isTailFlit f3) => Signal.pure false
                   | (g3 &&& isHeadFlit f3) => Signal.pure true
  ra4 <~ hw_cond a4 | (g4 &&& isTailFlit f4) => Signal.pure false
                   | (g4 &&& isHeadFlit f4) => Signal.pure true

  rt0 <~ Signal.mux (g0 &&& isHeadFlit f0) d0 t0
  rt1 <~ Signal.mux (g1 &&& isHeadFlit f1) d1 t1
  rt2 <~ Signal.mux (g2 &&& isHeadFlit f2) d2 t2
  rt3 <~ Signal.mux (g3 &&& isHeadFlit f3) d3 t3
  rt4 <~ Signal.mux (g4 &&& isHeadFlit f4) d4 t4

  return RouterOut.mk
    (oV0 := vN) (oV1 := vS) (oV2 := vE) (oV3 := vW) (oV4 := vL)
    (oF0 := xN) (oF1 := xS) (oF2 := xE) (oF3 := xW) (oF4 := xL)
    (iR0 := r0) (iR1 := r1) (iR2 := r2) (iR3 := r3) (iR4 := r4)

#synthesizeVerilog router5

-- A stable copy of the netlist for the Verilator waveform flow
-- (`IP/NoC/wave/run.sh`).  `#sim` also emits one, but under
-- `.lake/build/`, which a clean build wipes.
#writeVerilogDesign router5 "IP/NoC/wave/router5.sv"

/-
  Next step, and why it is not a detail:

  The output stage is combinational (see the DRC note at the top).  To
  pipeline it you register `oV*`/`oF*`, which means the router can no
  longer retract a flit once presented — so the input buffer must become
  a 2-deep skid buffer to absorb the cycle of latency in the ready path.
  That is a real design change, not a wrapper, and it is the right thing
  to do before pushing a large mesh onto an FPGA.
-/

end Sparkle.IP.NoC
