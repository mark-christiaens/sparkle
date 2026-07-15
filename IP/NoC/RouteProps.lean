/-
  NoC — Formal properties of XY routing.

  Safety   — a packet is ejected exactly at its destination, never early,
             never late (`route_local_iff_arrived`).
  Progress — every hop strictly reduces the Manhattan distance
             (`dist_decreases`).
  Liveness — therefore every packet is delivered, in at most `dist` hops
             (`travel_arrives`).  This is LTL's ◇ (eventually), as a
             *bounded* statement: not "eventually" but "within N".
  Deadlock — XY routing never makes a Y→X turn (`no_y_to_x_turn`).

  ## Why `no_y_to_x_turn` is the deadlock argument

  A wormhole packet occupies every link it is stretched across, and holds
  them while its head waits.  The network deadlocks iff the "channel
  waits-for channel" graph has a cycle.  In a 2-D mesh, any such cycle
  must go around a loop, and going around a loop requires *both* an X→Y
  turn and a Y→X turn.  XY routing permits the first and forbids the
  second — so no cycle can be closed, so the network cannot deadlock.
  (This is Glass & Ni's turn model; `no_y_to_x_turn` is the hypothesis it
  turns on.)
-/

import IP.NoC.Route

namespace Sparkle.IP.NoC

/-! ## Basic facts about distance -/

/-- Distance is zero exactly at the destination. -/
theorem dist_eq_zero_iff (c d : Coord) : dist c d = 0 ↔ c = d := by
  cases c; cases d
  simp only [dist, absDiff, Coord.mk.injEq]
  omega

/-! ## Safety: eject exactly on arrival -/

/-- The packet is sent to the `Local` port (ejected to the tile) if and
    only if it has arrived.  No early ejection, no overshoot. -/
theorem route_local_iff_arrived (cur dest : Coord) :
    routeXY cur dest = .Local ↔ cur = dest := by
  cases cur; cases dest
  simp only [routeXY, Coord.mk.injEq]
  repeat' split
  all_goals (try simp)
  all_goals omega

/-! ## Characterization: what each routing decision means

    These turn a `routeXY … = SomePort` fact into pure `Nat` arithmetic,
    which is what lets `omega` discharge the channel-dependency-graph
    proofs in `Deadlock.lean`. -/

theorem route_east_iff (cur dest : Coord) :
    routeXY cur dest = .East ↔ dest.x > cur.x := by
  unfold routeXY
  repeat' split
  all_goals (try simp)
  all_goals omega

theorem route_west_iff (cur dest : Coord) :
    routeXY cur dest = .West ↔ dest.x < cur.x := by
  unfold routeXY
  repeat' split
  all_goals (try simp)
  all_goals omega

/-- A North hop happens only once the packet is in the destination
    column — the X dimension is already resolved. -/
theorem route_north_iff (cur dest : Coord) :
    routeXY cur dest = .North ↔ (dest.x = cur.x ∧ dest.y > cur.y) := by
  unfold routeXY
  repeat' split
  all_goals (try simp)
  all_goals omega

theorem route_south_iff (cur dest : Coord) :
    routeXY cur dest = .South ↔ (dest.x = cur.x ∧ dest.y < cur.y) := by
  unfold routeXY
  repeat' split
  all_goals (try simp)
  all_goals omega

/-! ## Progress: every hop gets strictly closer -/

/-- Each hop strictly decreases the Manhattan distance to the
    destination.  This is the well-founded measure that makes delivery
    terminate. -/
theorem dist_decreases (cur dest : Coord) (h : cur ≠ dest) :
    dist (step cur (routeXY cur dest)) dest < dist cur dest := by
  have hne : ¬(cur.x = dest.x ∧ cur.y = dest.y) := by
    intro hc
    exact h (by cases cur; cases dest; simp only [Coord.mk.injEq]; exact hc)
  unfold routeXY
  repeat' split
  all_goals simp only [step, dist, absDiff]
  all_goals omega

/-! ## Liveness: every packet is delivered

    `travel n` walks the route for `n` hops.  We show `dist` hops always
    suffice — so a packet launched at `cur` for `dest` arrives, and we
    know the bound. -/

/-- **Delivery.**  Following the XY route for `n ≥ dist cur dest` hops
    lands exactly on `dest`.  Every packet is delivered, within a bound
    linear in the mesh diameter. -/
theorem travel_arrives (n : Nat) (cur dest : Coord) (h : dist cur dest ≤ n) :
    travel n cur dest = dest := by
  induction n generalizing cur with
  | zero =>
      have : dist cur dest = 0 := Nat.le_zero.mp h
      simp [travel, (dist_eq_zero_iff cur dest).mp this]
  | succ n ih =>
      unfold travel
      split
      · assumption
      · rename_i hne
        refine ih _ ?_
        have := dist_decreases cur dest hne
        omega

/-- Corollary: `dist` hops are always enough. -/
theorem delivered (cur dest : Coord) : travel (dist cur dest) cur dest = dest :=
  travel_arrives _ cur dest (Nat.le_refl _)

/-! ## Deadlock-freedom: XY routing never turns from Y back into X -/

/-- Routing in the Y dimension only happens once the packet is already in
    the destination column. -/
theorem route_y_implies_x_aligned (cur dest : Coord) :
    isYPort (routeXY cur dest) = true → cur.x = dest.x := by
  unfold routeXY
  repeat' split
  all_goals (try simp [isYPort])
  all_goals omega

/-- A Y hop does not change the packet's column. -/
theorem step_y_preserves_x (c : Coord) (p : Port) (h : isYPort p = true) :
    (step c p).x = c.x := by
  cases p <;> simp_all [isYPort, step]

/-- Once in the destination column, XY routing never asks for an X hop. -/
theorem route_x_aligned_not_x_port (cur dest : Coord) (h : cur.x = dest.x) :
    isXPort (routeXY cur dest) = false := by
  unfold routeXY
  repeat' split
  all_goals (try simp [isXPort])
  all_goals omega

/-- **No Y→X turn.**  If a packet leaves this router through a Y port,
    then at the *next* router it will not be routed through an X port.

    This is the turn XY routing forbids, and forbidding it is what makes
    the channel-dependency graph acyclic — i.e. what makes the network
    deadlock-free. -/
theorem no_y_to_x_turn (cur dest : Coord)
    (h : isYPort (routeXY cur dest) = true) :
    isXPort (routeXY (step cur (routeXY cur dest)) dest) = false := by
  have hx    : cur.x = dest.x := route_y_implies_x_aligned cur dest h
  have hstep : (step cur (routeXY cur dest)).x = cur.x :=
    step_y_preserves_x cur (routeXY cur dest) h
  exact route_x_aligned_not_x_port _ dest (by rw [hstep, hx])

end Sparkle.IP.NoC
