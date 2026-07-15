/-
  NoC — XY (dimension-order) route computation, pure Lean spec.

  The routing rule for a 2-D mesh:

      travel in X until aligned with the destination column,
      then travel in Y until you arrive.

  Trivial to implement (a few comparators) and — crucially — the reason
  the network cannot deadlock.  A wormhole packet holds the links it is
  lying across while waiting for the next one (hold-and-wait), so a cycle
  in the "who waits for whom" graph wedges the network permanently.
  XY routing forbids the Y→X turn, which is exactly the turn needed to
  close such a cycle.  That is proved in `RouteProps.lean`.

  Everything here is pure `Nat` arithmetic so the proofs stay in reach of
  `omega`; `Router.lean` implements the same function over `BitVec`.
-/

import IP.NoC.Flit

namespace Sparkle.IP.NoC

/-- Dimension-order (XY) route computation.

    Given the router's own coordinate `cur` and the head flit's `dest`,
    return the output port the packet must take.  `Local` means "you have
    arrived — eject to the attached tile". -/
def routeXY (cur dest : Coord) : Port :=
  if dest.x > cur.x then .East
  else if dest.x < cur.x then .West
  else if dest.y > cur.y then .North
  else if dest.y < cur.y then .South
  else .Local

/-- Where a flit lands after leaving through port `p`. -/
def step (c : Coord) (p : Port) : Coord :=
  match p with
  | .East  => { c with x := c.x + 1 }
  | .West  => { c with x := c.x - 1 }
  | .North => { c with y := c.y + 1 }
  | .South => { c with y := c.y - 1 }
  | .Local => c

/-- `|a - b|`, written with truncated subtraction so that `omega` can see
    through it without a case split. -/
def absDiff (a b : Nat) : Nat := (a - b) + (b - a)

/-- Manhattan distance — the number of hops still to go. -/
def dist (c d : Coord) : Nat := absDiff c.x d.x + absDiff c.y d.y

/-- Is this port an X-dimension hop? -/
def isXPort : Port → Bool
  | .East | .West => true
  | _             => false

/-- Is this port a Y-dimension hop? -/
def isYPort : Port → Bool
  | .North | .South => true
  | _               => false

/-- Follow the route for up to `n` hops.  Models a packet walking the
    mesh; `n` is fuel, and `travel_arrives` shows `dist` hops suffice. -/
def travel : Nat → Coord → Coord → Coord
  | 0,     cur, _    => cur
  | n + 1, cur, dest =>
      if cur = dest then cur
      else travel n (step cur (routeXY cur dest)) dest

end Sparkle.IP.NoC
