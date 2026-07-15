/-
  NoC — 5×5 crossbar switch, Signal DSL implementation.

  The crossbar is the router's datapath: it moves a flit from whichever
  input port won arbitration to the output port.  Structurally it is five
  independent 5:1 muxes — one per output — each steered by the `idx` of
  that output's own arbiter (`Arbiter5.lean`).

      inputs                        outputs
      N ─┐                        ┌─ N   (sel from arbiter_N)
      S ─┤                        ├─ S   (sel from arbiter_S)
      E ─┼──  5×5 crossbar  ──────┼─ E   (sel from arbiter_E)
      W ─┤                        ├─ W   (sel from arbiter_W)
      L ─┘                        └─ L   (sel from arbiter_L)

  There is no state and no arbitration here — all the fairness lives in
  the arbiters, and all the deadlock reasoning lives in the routing.  The
  crossbar is pure wire.

  Note the cost: five 5:1 muxes of 42 bits each = 5 × 5 × 42 ≈ 1050 mux
  bits.  This is why NoC links are narrow and why flits exist at all.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.NoC.Flit
import IP.NoC.Arbiter5

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.IP.NoC

/-- One output port of the crossbar: a 5:1 mux over the five input flits,
    steered by `sel` (0-4, the arbiter's granted input index). -/
@[hardware_module]
def xbarPort {dom : DomainConfig}
    (sel : Signal dom (BitVec 3))
    (d0 d1 d2 d3 d4 : Signal dom FlitBits) : Signal dom FlitBits :=
  hw_cond d4
    | sel === (Signal.pure 0#3) => d0
    | sel === (Signal.pure 1#3) => d1
    | sel === (Signal.pure 2#3) => d2
    | sel === (Signal.pure 3#3) => d3

#synthesizeVerilog xbarPort

-- The five crossbar outputs, in `allPorts` order (N, S, E, W, Local).
declare_signal_state Xbar5Out
  | oN : BitVec 42 := 0#42
  | oS : BitVec 42 := 0#42
  | oE : BitVec 42 := 0#42
  | oW : BitVec 42 := 0#42
  | oL : BitVec 42 := 0#42

/--
  **The full 5×5 crossbar.**

  `dN … dL` are the flits offered by each input port.  `selN … selL` are
  the granted input indices, one per output port, each from that output's
  round-robin arbiter.

  A flit is *broadcast* to all five muxes; each output independently
  selects the input its arbiter granted.  Two outputs may legitimately
  select the same input in the same cycle (a head flit going to only one
  of them — the router's control logic is what ensures only one is
  actually driven; see `Router.lean`).
-/
def crossbar5 {dom : DomainConfig}
    (selN selS selE selW selL : Signal dom (BitVec 3))
    (dN dS dE dW dL : Signal dom FlitBits) : Signal dom Xbar5Out :=
  Xbar5Out.mk
    (oN := xbarPort selN dN dS dE dW dL)
    (oS := xbarPort selS dN dS dE dW dL)
    (oE := xbarPort selE dN dS dE dW dL)
    (oW := xbarPort selW dN dS dE dW dL)
    (oL := xbarPort selL dN dS dE dW dL)

#synthesizeVerilog crossbar5

end Sparkle.IP.NoC
