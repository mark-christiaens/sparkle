/-
  NoC — hardware-vs-spec equivalence tests.

  The proofs in `ArbiterProps.lean` are about the *spec* (`grant`).  They
  only say something about the silicon if the Signal DSL implementation
  actually computes the same function.  This file closes that gap:

  1. `checkArbiterCombinational` — **exhaustive**.  All 5 values of `last`
     × all 32 request patterns = 160 cases, every one compared against
     `grant`.  This is a complete equivalence check of the arbiter's
     combinational core; there is nothing left to sample.

  2. `checkArbiterSequential` — drives the real `arbiter5` (with its state
     register) for 512 cycles against a spec simulation, checking the
     rotation state evolves identically.

  3. `checkCrossbar` — all 5 select values through `xbarPort`.

  4. `checkRotation` / `checkStarvation` — the fairness claims, observed
     on the hardware rather than the spec.

  5. `checkRouteHw` — **exhaustive**: `routeXYHw` ≡ `routeXY` on all
     16×16×16×16 = 65 536 coordinate pairs.

  6./7. The full wormhole router (forwarding, ejection, and two packets
     contending for one output), driven through the `#sim` JIT simulator
     — see the note at section 6 for why not native evaluation.

  Run: `lake exe noc-test`
-/

import Sparkle
import Sparkle.Core.JIT
import Sparkle.Core.SimTyped
import IP.NoC.Route
import IP.NoC.ArbiterProps
import IP.NoC.Arbiter5
import IP.NoC.Crossbar
import IP.NoC.Router

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.IP.NoC.SimTest

open Sparkle.IP.NoC

abbrev dom : DomainConfig := defaultDomain

def clientOfIdx : Nat → Client
  | 0 => .C0
  | 1 => .C1
  | 2 => .C2
  | 3 => .C3
  | _ => .C4

/-- Request pattern from a 5-bit number. -/
def reqsOfNat (n : Nat) : Reqs :=
  ⟨n.testBit 0, n.testBit 1, n.testBit 2, n.testBit 3, n.testBit 4⟩

/-! ## 1. Exhaustive combinational equivalence: hardware ≡ `grant` -/

def checkArbiterCombinational : IO Bool := do
  let mut ok := true
  let mut checked := 0
  for lastN in [0, 1, 2, 3, 4] do
    for rn in List.range 32 do
      let r := reqsOfNat rn
      let s0 : Signal dom Bool := Signal.pure r.r0
      let s1 : Signal dom Bool := Signal.pure r.r1
      let s2 : Signal dom Bool := Signal.pure r.r2
      let s3 : Signal dom Bool := Signal.pure r.r3
      let s4 : Signal dom Bool := Signal.pure r.r4
      let lastS : Signal dom (BitVec 3) := Signal.pure (BitVec.ofNat 3 lastN)

      let hwValid := (anyReq s0 s1 s2 s3 s4).atTime 0
      let hwIdx   := (grantIdxOf lastS s0 s1 s2 s3 s4).atTime 0

      let specGrant := grant (clientOfIdx lastN) r
      let specValid := r.any

      checked := checked + 1

      if hwValid != specValid then
        ok := false
        IO.println s!"  MISMATCH valid: last={lastN} reqs={rn} hw={hwValid} spec={specValid}"

      match specGrant with
      | some c =>
          let want := BitVec.ofNat 3 c.idx
          if hwIdx != want then
            ok := false
            IO.println s!"  MISMATCH idx: last={lastN} reqs={rn} hw={hwIdx} spec={want}"
      | none =>
          -- nobody asking: `idx` is don't-care, `valid` is low (checked above)
          pure ()
  IO.println s!"  exhaustive combinational: {checked}/160 cases checked"
  return ok

/-! ## 2. Sequential equivalence: the real `arbiter5`, state and all -/

def checkArbiterSequential (cycles : Nat) : IO Bool := do
  -- A pseudo-random-ish walk through the 32 request patterns.
  let pat : Nat → Reqs := fun t => reqsOfNat ((t * 13 + 5) % 32)

  let s0 : Signal dom Bool := ⟨fun t => (pat t).r0⟩
  let s1 : Signal dom Bool := ⟨fun t => (pat t).r1⟩
  let s2 : Signal dom Bool := ⟨fun t => (pat t).r2⟩
  let s3 : Signal dom Bool := ⟨fun t => (pat t).r3⟩
  let s4 : Signal dom Bool := ⟨fun t => (pat t).r4⟩

  let out := arbiter5 s0 s1 s2 s3 s4

  let mut last : Client := .C0    -- matches the register's reset value (0)
  let mut ok := true
  for t in List.range cycles do
    let r := pat t
    let hwValid := (Arb5Out.valid out).atTime t
    let hwIdx   := (Arb5Out.idx out).atTime t

    match grant last r with
    | some c =>
        let want := BitVec.ofNat 3 c.idx
        if hwValid != true || hwIdx != want then
          ok := false
          IO.println s!"  MISMATCH cycle {t}: hw=({hwValid},{hwIdx}) spec=(true,{want})"
    | none =>
        if hwValid != false then
          ok := false
          IO.println s!"  MISMATCH cycle {t}: hw valid={hwValid}, spec idle"

    last := nextLast last r
  IO.println s!"  sequential: {cycles} cycles, hardware tracked spec state exactly"
  return ok

/-! ## 3. Crossbar: every select line routes the right input -/

def checkCrossbar : IO Bool := do
  let d : Nat → Signal dom FlitBits := fun i => Signal.pure (BitVec.ofNat 42 (0xA0 + i))
  let mut ok := true
  for sel in [0, 1, 2, 3, 4] do
    let o := (xbarPort (Signal.pure (BitVec.ofNat 3 sel))
                (d 0) (d 1) (d 2) (d 3) (d 4)).atTime 0
    let want := BitVec.ofNat 42 (0xA0 + sel)
    if o != want then
      ok := false
      IO.println s!"  MISMATCH xbar sel={sel}: got {o}, want {want}"
  IO.println "  crossbar: all 5 select lines route correctly"
  return ok

/-! ## 4. Fairness, observed on the hardware -/

/-- Under full contention the hardware grant must advance by exactly one
    client per cycle (`ArbiterProps.rotation`). -/
def checkRotation : IO Bool := do
  let hi : Signal dom Bool := Signal.pure true
  let out := arbiter5 hi hi hi hi hi
  let mut ok := true
  let mut seen : List Nat := []
  for t in List.range 10 do
    let idx := (Arb5Out.idx out).atTime t
    seen := seen ++ [idx.toNat]
    -- with everyone asking, cycle t must grant client (t+1) % 5
    if idx != BitVec.ofNat 3 ((t + 1) % 5) then
      ok := false
      IO.println s!"  MISMATCH rotation cycle {t}: got {idx.toNat}, want {(t+1) % 5}"
  IO.println s!"  rotation under full contention: {seen}"
  return ok

/-- A client that keeps asking is granted within 5 cycles, whatever the
    others do (`ArbiterProps.starvation_free`).  Checked here on the
    hardware for every client, against the worst case: all four others
    also hammering. -/
def checkStarvation : IO Bool := do
  let hi : Signal dom Bool := Signal.pure true
  let out := arbiter5 hi hi hi hi hi
  let mut ok := true
  for c in [0, 1, 2, 3, 4] do
    let mut granted := false
    for t in List.range 5 do
      if (Arb5Out.valid out).atTime t && (Arb5Out.idx out).atTime t == BitVec.ofNat 3 c then
        granted := true
    if !granted then
      ok := false
      IO.println s!"  STARVED: client {c} not granted within 5 cycles"
  IO.println "  starvation-freedom: every client granted within 5 cycles"
  return ok

/-! ## 5. `routeXYHw` ≡ `routeXY` — exhaustively, all 65 536 inputs -/

def checkRouteHw : IO Bool := do
  let mut ok := true
  let mut checked := 0
  for mx in List.range 16 do
    for my in List.range 16 do
      for dx in List.range 16 do
        for dy in List.range 16 do
          let hw := (routeXYHw (dom := dom)
                       (Signal.pure (BitVec.ofNat 4 mx)) (Signal.pure (BitVec.ofNat 4 my))
                       (Signal.pure (BitVec.ofNat 4 dx)) (Signal.pure (BitVec.ofNat 4 dy))).atTime 0
          let spec := (routeXY ⟨mx, my⟩ ⟨dx, dy⟩).toBits
          checked := checked + 1
          if hw != spec then
            ok := false
            if checked < 2000 then
              IO.println s!"  MISMATCH route: my=({mx},{my}) dest=({dx},{dy}) hw={hw} spec={spec}"
  IO.println s!"  exhaustive routeXYHw ≡ routeXY: {checked}/65536 cases checked"
  return ok

/-! ## 6. The router itself — via the JIT simulator

  Native `.atTime` evaluation of the full router hangs: the Signal graph
  is evaluated as a tree, and the router's fan-out (five arbiters, each
  reading all five route computations) multiplies out to millions of node
  visits per cycle.  Sparkle's own guidance (Signal.lean) is to simulate
  designs of this size through the compiled backends.  `#sim` generates a
  C simulator + typed Lean wrappers; the testbench below drives it from
  IO, so the packet sources and checks are plain software against the
  real synthesized router.
-/

-- Monomorphic top for `#sim`: the router pinned at coordinate (1,1).
def routerTop
    (inV0 inV1 inV2 inV3 inV4 : Signal dom Bool)
    (inF0 inF1 inF2 inF3 inF4 : Signal dom FlitBits)
    (outR0 outR1 outR2 outR3 outR4 : Signal dom Bool) : Signal dom RouterOut :=
  router5 (Signal.pure 1#4) (Signal.pure 1#4)
    inV0 inV1 inV2 inV3 inV4
    inF0 inF1 inF2 inF3 inF4
    outR0 outR1 outR2 outR3 outR4

#sim routerTop

/-- Build a flit through the spec encoder — the layout lives solely in
    `Flit.toBits`. -/
def mkFlit (kind : FlitKind) (dx dy payload : Nat) : FlitBits :=
  (Flit.mk kind ⟨dx, dy⟩ (BitVec.ofNat 32 payload)).toBits

/-- Kind of the flit at position `i` in a `len`-flit packet. -/
def kindAt (i len : Nat) : FlitKind :=
  if i == 0 then .Head else if i + 1 == len then .Tail else .Body

def flitPayload (f : FlitBits) : Nat := (payloadBits f).toNat
def flitKindOf  (f : FlitBits) : Nat := (kindBits f).toNat

/-- Unpack the 220-bit `RouterOut` bundle.  `declare_signal_state` packs
    fields in declaration order from the MSB down:
    `oV0..oV4` at bits 219-215, `oF0..oF4` at [214:173]..[46:5],
    `iR0..iR4` at bits 4-0. -/
def outOV (o : BitVec 220) (p : Nat) : Bool := BitVec.extractLsb' (219 - p) 1 o == 1#1
def outOF (o : BitVec 220) (p : Nat) : BitVec 42 := BitVec.extractLsb' (173 - 42 * p) 42 o
def outIR (o : BitVec 220) (p : Nat) : Bool := BitVec.extractLsb' (4 - p) 1 o == 1#1

def b1 (b : Bool) : BitVec 1 := if b then 1#1 else 0#1

/-- A software packet source: a `len`-flit packet (Head, Body…, Tail)
    to `(dx,dy)`, payloads `tag, tag+1, …`.  `idx` is the next flit to
    offer; the driver advances it only when the router accepts. -/
structure Src where
  len : Nat
  dx  : Nat
  dy  : Nat
  tag : Nat
  idx : Nat := 0

def Src.valid (s : Src) : Bool := s.idx < s.len
def Src.flit (s : Src) : FlitBits :=
  mkFlit (kindAt s.idx s.len) s.dx s.dy (s.tag + s.idx)

/--
  Drive the JIT router for `cycles` cycles: source A on input North (0),
  source B on input South (1), all five outputs permanently ready.
  A source advances only when the router asserts `iR` — real
  backpressure, not an idealised source.  Returns the `(kind, payload)`
  sequence of every flit presented on output port `watch`.

  Per-cycle protocol: `step` sets the inputs and evaluates + ticks; the
  outputs read afterwards are the combinational values of the cycle just
  ended (evaluated before the clock edge), so `iR` tells us whether the
  flit we offered this cycle was accepted at that edge.
-/
def runRouter (sim : routerTop.Sim.Simulator) (a b : Src)
    (watch : Nat) (cycles : Nat) : IO (List (Nat × Nat)) := do
  Sparkle.Core.Sim.Sim.reset sim
  let mut sa := a
  let mut sb := b
  let mut got : List (Nat × Nat) := []
  for _ in List.range cycles do
    let inp : routerTop.Sim.SimInput :=
      { _gen_inV0 := b1 sa.valid, _gen_inV1 := b1 sb.valid
      , _gen_inV2 := 0#1, _gen_inV3 := 0#1, _gen_inV4 := 0#1
      , _gen_inF0 := sa.flit, _gen_inF1 := sb.flit
      , _gen_inF2 := 0#42, _gen_inF3 := 0#42, _gen_inF4 := 0#42
      , _gen_outR0 := 1#1, _gen_outR1 := 1#1, _gen_outR2 := 1#1
      , _gen_outR3 := 1#1, _gen_outR4 := 1#1 }
    Sparkle.Core.Sim.Sim.step sim inp
    let o ← Sparkle.Core.Sim.Sim.read sim
    if sa.valid && outIR o.out 0 then sa := { sa with idx := sa.idx + 1 }
    if sb.valid && outIR o.out 1 then sb := { sb with idx := sb.idx + 1 }
    if outOV o.out watch then
      let f := outOF o.out watch
      got := got ++ [(flitKindOf f, flitPayload f)]
  return got

def noSrc : Src := { len := 0, dx := 0, dy := 0, tag := 0 }

/-- The `(kind, payload)` sequence a `len`-flit packet with payload base
    `tag` must produce on the wire: Head, Body…, Tail, payloads
    contiguous.  Built from the same `kindAt` as `Src.flit`. -/
def wantPacket (tag len : Nat) : List (Nat × Nat) :=
  (List.range len).map fun i => ((kindAt i len).toBits.toNat, tag + i)

/-- A packet from (1,1) to (3,1) must leave East, in order, Head→Body→Tail. -/
def checkForward (sim : routerTop.Sim.Simulator) : IO Bool := do
  let got ← runRouter sim { len := 5, dx := 3, dy := 1, tag := 0xA0 } noSrc 2 14
  let want := wantPacket 0xA0 5
  IO.println s!"  East output: {got}"
  if got != want then
    IO.println s!"  MISMATCH: wanted {want}"
    return false
  IO.println "  forwarding: XY route sent the packet East, flits in order"
  return true

/-- A packet addressed to this router's own coordinate must be ejected to
    the Local port, not forwarded. -/
def checkEject (sim : routerTop.Sim.Simulator) : IO Bool := do
  let got ← runRouter sim { len := 5, dx := 1, dy := 1, tag := 0xC0 } noSrc 4 14
  let want := wantPacket 0xC0 5
  IO.println s!"  Local output: {got}"
  if got != want then
    IO.println s!"  MISMATCH: wanted {want}"
    return false
  IO.println "  ejection: packet for (1,1) left via Local"
  return true

/--
  **The wormhole test.**  Two packets, from different inputs, both bound
  for the same output port at the same time.

  The output must carry one packet's flits *contiguously*, then the
  other's.  If the head reservation did not hold the output port, the two
  worms would interleave and both packets would be corrupted — which is
  exactly the bug wormhole routing exists to prevent, and exactly what a
  naive crossbar+arbiter (with no lock) would do.
-/
def checkWormhole (sim : routerTop.Sim.Simulator) : IO Bool := do
  -- North sends A→(3,1); South sends B→(3,1).  Both must go East.
  let len := 5
  let got ← runRouter sim
    { len := len, dx := 3, dy := 1, tag := 0xA0 }
    { len := len, dx := 3, dy := 1, tag := 0xB0 } 2 24
  IO.println s!"  East output: {got}"

  if got.length != 2 * len then
    IO.println s!"  MISMATCH: expected {2 * len} flits, got {got.length}"
    return false

  -- The output must carry one complete packet, then the other — any
  -- other arrangement means the worms interleaved.
  let first  := got.take len
  let second := got.drop len
  let okAB := first == wantPacket 0xA0 len && second == wantPacket 0xB0 len
  let okBA := first == wantPacket 0xB0 len && second == wantPacket 0xA0 len
  if !okAB && !okBA then
    IO.println s!"  INTERLEAVED: {got} is not two clean packets back-to-back"
    return false

  IO.println "  wormhole: two packets contended for East; each crossed intact,"
  IO.println "            one after the other — no interleaving"
  return true

/-- Print + flush, so a hung run still shows how far it got.
    Goes to stderr, which is unbuffered — a killed run still shows it. -/
def say (s : String) : IO Unit := do
  IO.eprintln s

/-- Run a named check, reporting how long it took. -/
def step (name : String) (act : IO Bool) : IO Bool := do
  say name
  let t0 ← IO.monoMsNow
  let r ← act
  let t1 ← IO.monoMsNow
  say s!"  ({t1 - t0} ms)"
  return r

def run : IO Unit := do
  say "=== Sparkle NoC — hardware vs. proven spec ==="
  say ""
  let a ← step "[1] Arbiter, exhaustive combinational equivalence"
                checkArbiterCombinational
  let b ← step "[2] Arbiter, sequential equivalence (state + rotation)"
                (checkArbiterSequential 512)
  let c ← step "[3] Crossbar" checkCrossbar
  let d ← step "[4a] Fairness: rotation" checkRotation
  let e ← step "[4b] Fairness: starvation-freedom" checkStarvation
  let f ← step "[5] Route computation, exhaustive hardware ≡ spec" checkRouteHw
  say "[6] Compiling router JIT simulator"
  let t0 ← IO.monoMsNow
  let sim ← routerTop.Sim.load
  let t1 ← IO.monoMsNow
  say s!"  ({t1 - t0} ms)"
  let g ← step "[6a] Router: forwarding" (checkForward sim)
  let h ← step "[6b] Router: ejection" (checkEject sim)
  let i ← step "[7] Wormhole: two packets contending for one output"
                (checkWormhole sim)
  Sparkle.Core.Sim.Sim.destroy sim
  say ""
  if a && b && c && d && e && f && g && h && i then
    IO.println "ALL PASS — the RTL computes the function the proofs are about."
  else
    IO.println "FAIL"
    throw (IO.userError "NoC hardware/spec mismatch")

end Sparkle.IP.NoC.SimTest

def main : IO Unit := Sparkle.IP.NoC.SimTest.run
