/-
  NoC — Network-on-Chip router IP.

  A 5-port wormhole router for a 2-D mesh (North/South/East/West/Local),
  with XY dimension-order routing.

  Following the Sparkle Way:
    1. pure Lean spec      — Flit.lean, Route.lean
    2. proofs              — RouteProps.lean  (safety, progress, delivery)
                             Deadlock.lean    (channel-dependency graph is
                                               acyclic ⇒ cannot deadlock)
    3. Signal DSL impl     — (Arbiter5 / Crossbar / Router, to come)
    4. Verilog             — #synthesizeVerilog on the router top
-/

import IP.NoC.Flit
import IP.NoC.Route
import IP.NoC.RouteProps
import IP.NoC.Deadlock
import IP.NoC.ArbiterProps
import IP.NoC.Arbiter5
import IP.NoC.Crossbar
import IP.NoC.Router
