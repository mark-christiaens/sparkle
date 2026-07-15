/-
  NoC — 5-client round-robin arbiter, Signal DSL implementation.

  Synthesizable mirror of the spec in `ArbiterProps.lean`.  One of these
  sits on each of the router's five output ports.

  State: `last` — the client granted most recently (BitVec 3, values 0-4).
  Each cycle the arbiter walks the five clients in rotated order starting
  at `last + 1`, and grants the first one that is requesting.  The winner
  becomes the new `last`, dropping it to lowest priority — that rotation
  is the fairness argument (`ArbiterProps.rotation`,
  `ArbiterProps.starvation_free`).

  The rotation is done with a 5-way `succIdx` lookup rather than
  `(last + i) % 5`, which keeps everything inside 3 bits and costs a
  handful of LUTs instead of a modulo.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.NoC.ArbiterProps

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.IP.NoC

-- Grant bundle: `valid` = someone was granted, `idx` = which client (0-4).
-- The five one-hot grant lines are `valid && (idx === i)`.
declare_signal_state Arb5Out
  | valid : Bool       := false
  | idx   : BitVec 3   := 0#3

/-- Next client in the rotation, cyclically: 0→1→2→3→4→0.
    Mirrors `Client.succ`. -/
private def succIdx {dom : DomainConfig}
    (i : Signal dom (BitVec 3)) : Signal dom (BitVec 3) :=
  hw_cond (Signal.pure 0#3)
    | i === (Signal.pure 0#3) => Signal.pure 1#3
    | i === (Signal.pure 1#3) => Signal.pure 2#3
    | i === (Signal.pure 2#3) => Signal.pure 3#3
    | i === (Signal.pure 3#3) => Signal.pure 4#3

/-- 5:1 mux selecting request line `i`.  Mirrors `Reqs.get`. -/
private def selReq {dom : DomainConfig}
    (r0 r1 r2 r3 r4 : Signal dom Bool)
    (i : Signal dom (BitVec 3)) : Signal dom Bool :=
  hw_cond r4
    | i === (Signal.pure 0#3) => r0
    | i === (Signal.pure 1#3) => r1
    | i === (Signal.pure 2#3) => r2
    | i === (Signal.pure 3#3) => r3

/-- Is anybody requesting? -/
def anyReq {dom : DomainConfig}
    (r0 r1 r2 r3 r4 : Signal dom Bool) : Signal dom Bool :=
  r0 ||| r1 ||| r2 ||| r3 ||| r4

/--
  The combinational heart: given `last`, pick the winner.

  Walk the rotation `last+1, last+2, …, last+5` and take the first
  requester.  The fifth candidate is `last` itself, so it is the default
  arm — correct, because if none of the other four are asking then either
  `last` is asking (and wins) or nobody is (and `valid` is low anyway).
-/
def grantIdxOf {dom : DomainConfig}
    (last : Signal dom (BitVec 3))
    (r0 r1 r2 r3 r4 : Signal dom Bool) : Signal dom (BitVec 3) :=
  let c1 := succIdx last
  let c2 := succIdx c1
  let c3 := succIdx c2
  let c4 := succIdx c3
  let c5 := succIdx c4    -- = last, one full turn around
  hw_cond c5
    | selReq r0 r1 r2 r3 r4 c1 => c1
    | selReq r0 r1 r2 r3 r4 c2 => c2
    | selReq r0 r1 r2 r3 r4 c3 => c3
    | selReq r0 r1 r2 r3 r4 c4 => c4

/-- The `last`-granted register.  Updated only when a grant is issued, so
    an idle cycle does not disturb the rotation. -/
def arb5Last {dom : DomainConfig}
    (r0 r1 r2 r3 r4 : Signal dom Bool) : Signal dom (BitVec 3) :=
  Signal.loop fun last =>
    let gi   := grantIdxOf last r0 r1 r2 r3 r4
    let next := Signal.mux (anyReq r0 r1 r2 r3 r4) gi last
    Signal.register 0#3 next

/-- **5-client round-robin arbiter.** -/
@[hardware_module]
def arbiter5 {dom : DomainConfig}
    (r0 r1 r2 r3 r4 : Signal dom Bool) : Signal dom Arb5Out :=
  let last := arb5Last r0 r1 r2 r3 r4
  Arb5Out.mk
    (valid := anyReq r0 r1 r2 r3 r4)
    (idx   := grantIdxOf last r0 r1 r2 r3 r4)

#synthesizeVerilog arbiter5

end Sparkle.IP.NoC
