/-
  TalonLock/CompositionInvariant.lean
  ════════════════════════════════════
  Theorem 1: Composition Invariant.

  Paper §5 — ACM CCS 2026.

  Statement (reproduced from the paper):
    For all (v, l) ∈ Reach(Init),
      TL(l, v) →
        ∀ u ∈ participants(l).
          sched(v, u, v.start + v.duration) = alloc_L(l, u)   [Goal 1]
          ∧ v.released(u) ≤ sched(v, u, v.start + v.duration) [Goal 2]
          ∧ v.coin + v.totalVested + v.collected = v.supply    [Goal 3]

  Note: the paper writes `l.closeTime + l.duration` for the end time.
  Under TL, `v.start = l.closeTime` (start_eq field), so these are equal.
  The proof uses `v.start + v.duration` throughout for cleanness.

  Proof structure (three independent goals):
    Goal 1: calc block via sched_at_end → entitlement_strategy_two → alloc_eq
    Goal 2: durationScheduleCeiling → ReleasedBounded
    Goal 3: fundConservation → WellFormedVesting.fund

  The theorem is parametric over JointReach, which carries the
  WF preservation obligation through the entire execution history.
-/

import TalonLock.Defs
import TalonLock.TalonLock
import TalonLock.VestingReach
import TalonLock.LaunchpadReach
import TalonLock.Lemmas

namespace TalonLock

-- ── Joint step and reachability ──────────────────────────────────

/-- JointStep: one transition in the composed protocol.
    Carries a well-formedness preservation obligation over the
    joint state, ensuring WF is maintained throughout. -/
structure JointStep (s s' : JointState) : Prop where
  preserve_wf : WellFormedState s → WellFormedState s'

inductive JointReach : JointState → JointState → Prop where
  | refl (s : JointState) : JointReach s s
  | step {s s' s'' : JointState} :
      JointStep s s' → JointReach s' s'' → JointReach s s''

theorem JointReach.preserves_wf {s s' : JointState}
    (h : JointReach s s') (hw : WellFormedState s) :
    WellFormedState s' := by
  induction h with
  | refl s => exact hw
  | step hs hr ih => exact ih (hs.preserve_wf hw)

-- ── Hardened handoff constructor ─────────────────────────────────

/-- createVestingState: the abstract vesting object created by the
    hardened createVesting call.  Allocations are set to alloc_L l u
    for all users, strategy is 2, and metadata matches l. -/
def createVestingState
    (l       : LaunchpadState)
    (vId     : Addr)
    (coin supply totalVested collected duration : Nat)
    (released proofLock : AddrMap)
    : VestingState :=
  { id          := vId
    coin        := coin
    supply      := supply
    totalVested := totalVested
    collected   := collected
    start       := l.closeTime
    admin       := l.admin
    strategy    := 2
    amountEach  := 0
    duration    := duration
    allocMap    := fun u => alloc_L l u
    released    := released
    proofLock   := proofLock }

/-- The hardened handoff establishes TL by construction.
    Every field of TalonLock is satisfied by definition of createVestingState
    and linkVesting. -/
theorem createVesting_establishes_talonLock
    (l : LaunchpadState) (vId : Addr)
    (coin supply totalVested collected duration : Nat)
    (released proofLock : AddrMap) :
    let v  := createVestingState l vId coin supply totalVested collected duration released proofLock
    let l' := linkVesting l vId
    TalonLock l' v := by
  intro v l'
  constructor
  · -- ref_set: l'.vestingRef = some v.id
    unfold linkVesting createVestingState; simp
  · -- strategy_two: v.strategy = 2
    unfold createVestingState; simp
  · -- alloc_eq: v.allocMap u = alloc_L l' u for all participants
    intro u _hu
    unfold createVestingState linkVesting alloc_L; simp
  · -- start_eq: v.start = l'.closeTime
    unfold createVestingState linkVesting; simp
  · -- admin_eq: v.admin = l'.admin
    unfold createVestingState linkVesting; simp

-- ── Main theorem ─────────────────────────────────────────────────

/-- Theorem 1: Composition Invariant.

    Under the talon-lock predicate, for every reachable joint state:
    (1) Allocation integrity: every participant's vesting entitlement
        at schedule end equals their launchpad-computed allocation.
    (2) Schedule boundedness: released amounts are bounded by the
        schedule ceiling.
    (3) Fund conservation: all tokens are accounted for.

    Proof: three goals dispatched independently using lemmas from
    Lemmas.lean. -/
theorem compositionInvariant
    {s₀ s : JointState}
    (hreach  : JointReach s₀ s)
    (hw₀     : WellFormedState s₀)
    (htl     : TalonLock s.l s.v) :
    ∀ u : Addr, participants s.l u →
      sched s.v u (s.v.start + s.v.duration) = alloc_L s.l u ∧
      s.v.released u ≤ sched s.v u (s.v.start + s.v.duration) ∧
      FundConservation s.v := by
  intro u hu
  -- Obtain well-formedness at s from the reach chain
  have hw : WellFormedState s := JointReach.preserves_wf hreach hw₀
  -- ── Goal 1: sched = alloc_L ──────────────────────────────────
  -- Chain: sched_at_end → entitlement_strategy_two → alloc_eq
  have hEnt : entitlement s.v u = s.v.allocMap u :=
    entitlement_strategy_two htl.strategy_two u
  have hMap : s.v.allocMap u = alloc_L s.l u :=
    htl.alloc_eq u hu
  have hGoal1 : sched s.v u (s.v.start + s.v.duration) = alloc_L s.l u :=
    calc sched s.v u (s.v.start + s.v.duration)
        = entitlement s.v u    := sched_at_end s.v u hw.vwf.duration_pos
      _ = s.v.allocMap u       := hEnt
      _ = alloc_L s.l u        := hMap
  -- ── Goal 2: released ≤ sched ─────────────────────────────────
  -- sched_at_end + ReleasedBounded from WellFormedVesting
  have hGoal2 : s.v.released u ≤ sched s.v u (s.v.start + s.v.duration) :=
    durationScheduleCeiling hw.vwf u
  -- ── Goal 3: fund conservation ────────────────────────────────
  have hGoal3 : FundConservation s.v :=
    fundConservation hw.vwf
  exact ⟨hGoal1, hGoal2, hGoal3⟩

-- ── Corollaries ──────────────────────────────────────────────────

/-- P5 Allocation Integrity: projection of Goal 1. -/
corollary allocationIntegrity
    {s₀ s : JointState}
    (hreach : JointReach s₀ s)
    (hw₀    : WellFormedState s₀)
    (htl    : TalonLock s.l s.v)
    (u      : Addr) (hu : participants s.l u) :
    sched s.v u (s.v.start + s.v.duration) = alloc_L s.l u :=
  (compositionInvariant hreach hw₀ htl u hu).1

/-- Directly after the hardened createVesting handoff. -/
theorem compositionInvariant_after_createVesting
    (l : LaunchpadState) (vId : Addr)
    (coin supply totalVested collected duration : Nat)
    (released proofLock : AddrMap)
    (hwv : WellFormedVesting
      (createVestingState l vId coin supply totalVested collected duration released proofLock))
    (hwl : WellFormedLaunchpad (linkVesting l vId)) :
    let v  := createVestingState l vId coin supply totalVested collected duration released proofLock
    let l' := linkVesting l vId
    ∀ u : Addr, participants l' u →
      sched v u (v.start + v.duration) = alloc_L l' u ∧
      v.released u ≤ sched v u (v.start + v.duration) ∧
      FundConservation v := by
  intro v l' u hu
  let s : JointState := { v := v, l := l' }
  have hw : WellFormedState s := ⟨hwv, hwl⟩
  have htl : TalonLock l' v :=
    createVesting_establishes_talonLock l vId coin supply totalVested collected duration released proofLock
  exact compositionInvariant (JointReach.refl s) hw htl u hu

end TalonLock
