/-
  NoC — 5-client round-robin arbiter: pure spec + proofs.

  Each output port of the router has one of these.  Up to five input
  ports may want the same output in the same cycle; the arbiter picks
  one, and picks *fairly* — the loser this cycle gets priority next.

  The spec is a `find?` over the clients in rotated priority order,
  starting just after the last client granted.  That single line is the
  whole round-robin rule:

      grant last r = (order last).find? (r.get ·)

  Properties proved below:
    Safety   — no spurious grants        (`grant_sound`)
             — at most one grant         (`mutual_exclusion`)
    Progress — work-conserving           (`work_conserving`, `grant_none_iff`)
    Fairness — strict rotation on full contention (`rotation`)
             — starvation-freedom within 5 cycles (`starvation_free`)
             — the same bound against *time-varying* requests: the other
               four may toggle adversarially every cycle
               (`starvation_free_dynamic`)

  `Arbiter5.lean` implements this in the Signal DSL, and `SimTest.lean`
  checks the hardware against this spec exhaustively.
-/

namespace Sparkle.IP.NoC

/-- The five arbiter clients — one per router input port, in the same
    order as `allPorts` (North, South, East, West, Local). -/
inductive Client where
  | C0 | C1 | C2 | C3 | C4
  deriving DecidableEq, Repr, BEq, Inhabited

/-- The five request lines, one per client. -/
structure Reqs where
  r0 : Bool
  r1 : Bool
  r2 : Bool
  r3 : Bool
  r4 : Bool
  deriving DecidableEq, Repr, BEq, Inhabited

def Reqs.get : Reqs → Client → Bool
  | ⟨a, _, _, _, _⟩, .C0 => a
  | ⟨_, b, _, _, _⟩, .C1 => b
  | ⟨_, _, c, _, _⟩, .C2 => c
  | ⟨_, _, _, d, _⟩, .C3 => d
  | ⟨_, _, _, _, e⟩, .C4 => e

/-- Is anybody asking? -/
def Reqs.any (r : Reqs) : Bool := r.r0 || r.r1 || r.r2 || r.r3 || r.r4

/-- Everybody asking — full contention. -/
def allReqs : Reqs := ⟨true, true, true, true, true⟩

/-- Next client in the rotation (cyclic). -/
def Client.succ : Client → Client
  | .C0 => .C1
  | .C1 => .C2
  | .C2 => .C3
  | .C3 => .C4
  | .C4 => .C0

/-- Priority order for this cycle: everybody, starting just *after* the
    client granted last time.  That rotation is what makes it fair — the
    client granted last cycle drops to lowest priority. -/
def order (last : Client) : List Client :=
  let a := last.succ
  let b := a.succ
  let c := b.succ
  let d := c.succ
  let e := d.succ
  [a, b, c, d, e]

/-- **The arbiter.**  Grant the first requesting client in rotated
    priority order; `none` if nobody is asking. -/
def grant (last : Client) (r : Reqs) : Option Client :=
  (order last).find? (fun c => r.get c)

/-- The client the arbiter will rotate away from next cycle. -/
def nextLast (last : Client) (r : Reqs) : Client :=
  match grant last r with
  | some c => c
  | none   => last

/-- State after `k` cycles of the same request pattern. -/
def lastAfter : Nat → Client → Reqs → Client
  | 0,     last, _ => last
  | n + 1, last, r => lastAfter n (nextLast last r) r

/-- Grant issued on cycle `k`, holding the request pattern fixed. -/
def grantAfter (k : Nat) (last : Client) (r : Reqs) : Option Client :=
  grant (lastAfter k last r) r

/-! ## Safety -/

/-- **No spurious grants.**  A granted client was actually requesting. -/
theorem grant_sound (last c : Client) (r : Reqs) :
    grant last r = some c → r.get c = true := by
  obtain ⟨r0, r1, r2, r3, r4⟩ := r
  cases last <;> cases c <;>
    cases r0 <;> cases r1 <;> cases r2 <;> cases r3 <;> cases r4 <;> decide

/-- **Mutual exclusion.**  The arbiter never grants two clients at once.

    This is free from the type: `grant` returns an `Option Client`, so a
    two-client grant is not expressible.  In the hardware the five grant
    bits are `valid && (idx === i)`, which is one-hot for the same
    reason. -/
theorem mutual_exclusion (last : Client) (r : Reqs) (c₁ c₂ : Client)
    (h₁ : grant last r = some c₁) (h₂ : grant last r = some c₂) : c₁ = c₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-! ## Progress -/

/-- The arbiter idles exactly when nobody is asking. -/
theorem grant_none_iff (last : Client) (r : Reqs) :
    grant last r = none ↔ r.any = false := by
  obtain ⟨r0, r1, r2, r3, r4⟩ := r
  cases last <;>
    cases r0 <;> cases r1 <;> cases r2 <;> cases r3 <;> cases r4 <;> decide

/-- **Work-conserving.**  If anyone is asking, someone is granted — the
    arbiter never wastes a cycle while work is pending. -/
theorem work_conserving (last : Client) (r : Reqs) :
    r.any = true → (grant last r).isSome = true := by
  obtain ⟨r0, r1, r2, r3, r4⟩ := r
  cases last <;>
    cases r0 <;> cases r1 <;> cases r2 <;> cases r3 <;> cases r4 <;> decide

/-! ## Fairness -/

/-- **Strict rotation.**  Under full contention the grant advances by
    exactly one client per cycle: C0 → C1 → C2 → C3 → C4 → C0 → … -/
theorem rotation (last : Client) : grant last allReqs = some last.succ := by
  cases last <;> decide

/--
  **Starvation-freedom.**  A client that keeps requesting is granted
  within 5 cycles — no matter what the other four do.

  Five clients, so five cycles is the tight bound: worst case the other
  four are all ahead of you in the rotation and all requesting.
-/
theorem starvation_free (last c : Client) (r : Reqs) (h : r.get c = true) :
    grantAfter 0 last r = some c ∨
    grantAfter 1 last r = some c ∨
    grantAfter 2 last r = some c ∨
    grantAfter 3 last r = some c ∨
    grantAfter 4 last r = some c := by
  obtain ⟨r0, r1, r2, r3, r4⟩ := r
  revert h
  cases last <;> cases c <;>
    cases r0 <;> cases r1 <;> cases r2 <;> cases r3 <;> cases r4 <;> decide

/-! ## Fairness against time-varying requests

  `starvation_free` above holds the request pattern *fixed*.  That leaves
  a gap: could the other four clients starve `c` by toggling their
  requests adversarially, cycle by cycle?  No — and the proof is a
  ranking argument, like the deadlock proof in `Deadlock.lean`: every
  cycle `c` requests and loses, the winner sits strictly before `c` in
  the rotation order and becomes the new `last`, so `c`'s position in
  the order strictly decreases.  It starts ≤ 4, hence at most 4 losses.

  `decide` cannot chew through the statement directly (a request
  *sequence* `Nat → Reqs` is an infinite object), so the finite per-step
  fact is discharged by `decide` and a small induction lifts it to
  sequences.

  `lastSeq` below is exactly the state evolution `checkArbiterSequential`
  drives against the RTL with a time-varying pattern, so this theorem's
  semantics is the one already validated against the hardware.
-/

/-- Numeric client index. -/
def Client.idx : Client → Nat
  | .C0 => 0 | .C1 => 1 | .C2 => 2 | .C3 => 3 | .C4 => 4

/-- Position of `c` in this cycle's priority order (0 = next in line,
    4 = just granted, last in line). -/
def pos (last c : Client) : Nat := (c.idx + 4 - last.idx) % 5

theorem pos_lt_five (last c : Client) : pos last c < 5 := by
  cases last <;> cases c <;> decide

/-- **The per-step ranking fact** (finite, by `decide`): when `c`
    requests, either `c` wins, or the winner ends up strictly closer to
    the front of `c`'s queue than `last` was. -/
theorem rr_progress (last c w : Client) (r : Reqs)
    (hg : grant last r = some w) (hc : r.get c = true) :
    w = c ∨ pos w c < pos last c := by
  obtain ⟨r0, r1, r2, r3, r4⟩ := r
  revert hg hc
  cases last <;> cases c <;> cases w <;>
    cases r0 <;> cases r1 <;> cases r2 <;> cases r3 <;> cases r4 <;> decide

/-- A requesting client is enough to make the arbiter grant someone. -/
theorem get_any (r : Reqs) (c : Client) (h : r.get c = true) :
    r.any = true := by
  obtain ⟨r0, r1, r2, r3, r4⟩ := r
  revert h
  cases c <;> cases r0 <;> cases r1 <;> cases r2 <;> cases r3 <;> cases r4 <;> decide

/-- Arbiter state at the start of cycle `t`, driven by the time-varying
    request sequence `r`. -/
def lastSeq (last : Client) (r : Nat → Reqs) : Nat → Client
  | 0     => last
  | t + 1 => nextLast (lastSeq last r t) (r t)

/-- Grant issued on cycle `t` under the time-varying sequence `r`. -/
def grantSeq (t : Nat) (last : Client) (r : Nat → Reqs) : Option Client :=
  grant (lastSeq last r t) (r t)

/-- Running the sequence one step is the same as stepping the state once
    and running the shifted sequence. -/
theorem lastSeq_shift (last : Client) (r : Nat → Reqs) (t : Nat) :
    lastSeq last r (t + 1) =
    lastSeq (nextLast last (r 0)) (fun s => r (s + 1)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show nextLast (lastSeq last r (t + 1)) (r (t + 1)) =
         nextLast (lastSeq (nextLast last (r 0)) (fun s => r (s + 1)) t) (r (t + 1))
    rw [ih]

theorem grantSeq_shift (t : Nat) (last : Client) (r : Nat → Reqs) :
    grantSeq (t + 1) last r =
    grantSeq t (nextLast last (r 0)) (fun s => r (s + 1)) := by
  unfold grantSeq
  rw [lastSeq_shift]

/-- The induction: if `c` is within `k` places of the front and requests
    for `k` cycles, `c` is granted within `k` cycles. -/
theorem starvation_free_bounded (c : Client) :
    ∀ (k : Nat) (last : Client) (r : Nat → Reqs),
      pos last c < k → (∀ t, t < k → (r t).get c = true) →
      ∃ t, t < k ∧ grantSeq t last r = some c := by
  intro k
  induction k with
  | zero => intro last r hpos _; exact absurd hpos (Nat.not_lt_zero _)
  | succ k ih =>
    intro last r hpos hreq
    have hc0 : (r 0).get c = true := hreq 0 (Nat.succ_pos k)
    -- cycle 0 grants someone (work conservation)
    obtain ⟨w, hw⟩ : ∃ w, grant last (r 0) = some w := by
      cases hgg : grant last (r 0) with
      | some w => exact ⟨w, rfl⟩
      | none   =>
        have := (grant_none_iff last (r 0)).mp hgg
        rw [get_any (r 0) c hc0] at this
        exact absurd this (by simp)
    by_cases hwc : w = c
    · subst hwc
      exact ⟨0, Nat.succ_pos k, by simpa [grantSeq, lastSeq] using hw⟩
    · -- c lost: the winner is strictly closer, recurse on the tail
      have hlt : pos w c < pos last c :=
        (rr_progress last c w (r 0) hw hc0).resolve_left hwc
      have hnext : nextLast last (r 0) = w := by simp [nextLast, hw]
      obtain ⟨t, ht, hgt⟩ :=
        ih w (fun s => r (s + 1)) (by omega)
          (fun t ht => hreq (t + 1) (by omega))
      refine ⟨t + 1, by omega, ?_⟩
      rw [grantSeq_shift, hnext]
      exact hgt

/--
  **Starvation-freedom, dynamic version.**  A client that requests for 5
  consecutive cycles is granted in one of them — even while the other
  four clients toggle their requests arbitrarily (adversarially) every
  cycle.  Subsumes `starvation_free`, which is the special case of a
  constant sequence.
-/
theorem starvation_free_dynamic (last c : Client) (r : Nat → Reqs)
    (h : ∀ t, t < 5 → (r t).get c = true) :
    ∃ t, t < 5 ∧ grantSeq t last r = some c :=
  starvation_free_bounded c 5 last r (pos_lt_five last c) h

/-- The bound is tight: under full contention, a freshly-granted client
    waits the full 4 cycles before winning again — and does win at
    exactly cycle 4. -/
example :
    grantSeq 0 .C0 (fun _ => allReqs) ≠ some Client.C0 ∧
    grantSeq 1 .C0 (fun _ => allReqs) ≠ some Client.C0 ∧
    grantSeq 2 .C0 (fun _ => allReqs) ≠ some Client.C0 ∧
    grantSeq 3 .C0 (fun _ => allReqs) ≠ some Client.C0 ∧
    grantSeq 4 .C0 (fun _ => allReqs) = some Client.C0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Sparkle.IP.NoC
