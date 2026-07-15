/-
  NoC — Deadlock-freedom of XY routing, in full.

  ## The problem

  A wormhole packet is stretched across every link on its path, and it
  *holds* those links while its head waits for the next one.  That is
  hold-and-wait.  If channel c₁ waits for c₂, which waits for c₃, …, which
  waits back for c₁, then nothing in that cycle can ever move again: the
  network is permanently wedged.  No amount of simulation proves this
  cannot happen; it depends on a traffic pattern you may never hit.

  Dally & Seitz (1987): a wormhole network is deadlock-free **iff its
  channel-dependency graph (CDG) is acyclic**.

  ## What is proved here

  `Channel`  — a directed link: leave router `src` through port `dir`.
  `Dep N`    — the CDG edge relation.  `Dep N c₁ c₂` holds when some
               packet, routed by `routeXY`, uses channel `c₁` and then
               immediately channel `c₂`.  (`N` = mesh size.)
  `Reaches`  — the transitive closure of `Dep`.
  `acyclic`  — **¬ Reaches N c c** : no channel ever depends on itself.
               The CDG is acyclic, so by Dally & Seitz the network is
               deadlock-free.

  ## How

  Not by graph search — by a *ranking function*.  We exhibit
  `rank : Channel → Nat` that **strictly increases along every CDG edge**
  (`rank_mono`).  A cycle would give `rank c < rank c`, which is absurd.
  This is a complete argument, and it is a dozen lines of `omega`.

  The rank encodes exactly the intuition behind dimension-order routing:

      X-channels ....... rank ≤ N        (phase 0: resolve the X dimension)
      Y-channels ....... rank ≥ N+1      (phase 1: resolve the Y dimension)

  A packet can go X→Y (rank jumps up), but never Y→X — that would need
  the rank to fall.  Within a phase, East hops walk `x` up and West hops
  walk `x` down, and both directions are made to *increase* rank by
  ranking West channels as `N - x`.  East and West never depend on each
  other (a packet never reverses), so the two orderings never collide.

  The mesh is `N × N` and finite — as every real mesh is.  Finiteness is
  what makes a `Nat`-valued rank possible for the West/South directions.
-/

import IP.NoC.RouteProps

namespace Sparkle.IP.NoC

/-- A directed channel (link) of the mesh: leave router `src` through
    port `dir`.  `dir = Local` is the ejection port, not a mesh link. -/
structure Channel where
  src : Coord
  dir : Port
  deriving DecidableEq, Repr, Inhabited

/--
  **The channel-dependency graph.**  There is an edge `c₁ → c₂` when some
  packet uses channel `c₁` and then immediately channel `c₂`:

  * `c₂` starts where `c₁` lands (`c₂.src = step c₁.src c₁.dir`), and
  * some destination `dest` makes `routeXY` choose `c₁.dir` at `c₁.src`
    and then `c₂.dir` at `c₂.src`.

  Both channels are real mesh links inside the `N × N` mesh.
-/
def Dep (N : Nat) (c₁ c₂ : Channel) : Prop :=
  c₁.src.x < N ∧ c₁.src.y < N ∧
  c₂.src.x < N ∧ c₂.src.y < N ∧
  c₁.dir ≠ .Local ∧ c₂.dir ≠ .Local ∧
  c₂.src = step c₁.src c₁.dir ∧
  ∃ dest : Coord, routeXY c₁.src dest = c₁.dir ∧ routeXY c₂.src dest = c₂.dir

/--
  The ranking function.  X-channels land in `[0, N]`, Y-channels in
  `[N+1, 2N+1]`, so any X→Y dependency strictly increases rank and no
  Y→X dependency can exist.  Within a dimension, `East`/`North` increase
  with the coordinate and `West`/`South` increase as it decreases.
-/
def rank (N : Nat) : Channel → Nat
  | ⟨s, .East⟩  => s.x
  | ⟨s, .West⟩  => N - s.x
  | ⟨s, .North⟩ => (N + 1) + s.y
  | ⟨s, .South⟩ => (N + 1) + (N - s.y)
  | ⟨_, .Local⟩ => 0

/--
  **The key lemma: rank strictly increases along every CDG edge.**

  The proof is one `omega` per (from-port, to-port) pair.  Of the 25
  pairs, 9 are impossible and `omega` derives the contradiction itself:

  * `East → West`, `West → East` — a packet never reverses in X
    (`dest.x` cannot be both `> cur.x` and `≤ cur.x`).
  * `North → South`, `South → North` — likewise in Y.
  * `North/South → East/West` — the **Y→X turn**.  A Y hop only happens
    when `dest.x = cur.x`, and a Y hop preserves `x`; an X hop would need
    `dest.x ≠ cur.x`.  Contradiction.  *This is the turn that would close
    a cycle, and XY routing cannot make it.*
-/
theorem rank_mono (N : Nat) (c₁ c₂ : Channel) (h : Dep N c₁ c₂) :
    rank N c₁ < rank N c₂ := by
  obtain ⟨hx1, hy1, hx2, hy2, hl1, hl2, hstep, dest, hr1, hr2⟩ := h
  cases c₁ with
  | mk a p =>
    cases c₂ with
    | mk b q =>
      dsimp only at hx1 hy1 hx2 hy2 hl1 hl2 hstep hr1 hr2 ⊢
      subst hstep
      cases a with
      | mk ax ay =>
        cases dest with
        | mk dx dy =>
          cases p <;> cases q <;>
            simp_all [rank, step, route_east_iff, route_west_iff,
                      route_north_iff, route_south_iff] <;>
            omega

/-- Transitive closure of the dependency relation: `Reaches N a b` means
    a chain of CDG edges leads from channel `a` to channel `b`. -/
inductive Reaches (N : Nat) : Channel → Channel → Prop
  | single {a b} : Dep N a b → Reaches N a b
  | tail   {a b c} : Reaches N a b → Dep N b c → Reaches N a c

/-- Rank strictly increases along any chain of dependencies. -/
theorem reaches_rank_lt (N : Nat) {a b : Channel} (h : Reaches N a b) :
    rank N a < rank N b := by
  induction h with
  | single hd      => exact rank_mono N _ _ hd
  | tail _ hd ih   => exact Nat.lt_trans ih (rank_mono N _ _ hd)

/--
  **The channel-dependency graph is acyclic.**

  No channel depends on itself, however long the chain.  A cycle would
  force `rank N c < rank N c`.
-/
theorem acyclic (N : Nat) (c : Channel) : ¬ Reaches N c c :=
  fun h => Nat.lt_irrefl _ (reaches_rank_lt N h)

/--
  **Deadlock-freedom** (Dally & Seitz 1987).

  A wormhole network deadlocks iff its channel-dependency graph contains
  a cycle.  `acyclic` says ours never does — for *any* mesh size, *any*
  set of packets in flight, and *any* traffic pattern.

  So the router cannot deadlock.  Not "did not deadlock in simulation":
  cannot.
-/
theorem deadlock_free (N : Nat) : ∀ c : Channel, ¬ Reaches N c c := acyclic N

/-! ## Sanity: the CDG really does contain the edges we think it does.

    An acyclicity theorem is worthless if `Dep` is accidentally empty —
    it would hold vacuously.  So: exhibit a real dependency, and show the
    Y→X turn is genuinely absent. -/

/-- A real CDG edge: in a 4×4 mesh, a packet bound for `(2,1)` leaves
    `(0,0)` East and then leaves `(1,0)` East.  `Dep` is not vacuous. -/
example : Dep 4 ⟨⟨0, 0⟩, .East⟩ ⟨⟨1, 0⟩, .East⟩ :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, rfl, ⟨2, 1⟩, rfl, rfl⟩

/-- The X→Y turn *is* allowed (rank jumps from phase 0 to phase 1). -/
example : Dep 4 ⟨⟨0, 0⟩, .East⟩ ⟨⟨1, 0⟩, .North⟩ :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, rfl, ⟨1, 1⟩, rfl, rfl⟩

/-- But the Y→X turn is **not** in the graph — for any mesh, any
    coordinate, any X-direction port.  This is the structural fact that
    makes the CDG acyclic. -/
theorem no_y_to_x_dependency (N : Nat) (c₁ c₂ : Channel)
    (hy : isYPort c₁.dir = true) (hx : isXPort c₂.dir = true) :
    ¬ Dep N c₁ c₂ := by
  rintro ⟨_, _, _, _, _, _, hstep, dest, hr1, hr2⟩
  cases c₁ with
  | mk a p =>
    cases c₂ with
    | mk b q =>
      dsimp only at hy hx hstep hr1 hr2
      subst hstep
      cases a with
      | mk ax ay =>
        cases dest with
        | mk dx dy =>
          cases p <;> cases q <;>
            simp_all [isYPort, isXPort, step, route_east_iff,
                      route_west_iff, route_north_iff, route_south_iff]

end Sparkle.IP.NoC
