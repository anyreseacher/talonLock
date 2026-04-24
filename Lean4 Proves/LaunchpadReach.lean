/-
  TalonLock/LaunchpadReach.lean
  ══════════════════════════════
  Launchpad module transition relation and reachability.

  KEY DESIGN NOTE — V3 FIX:
  The `participate` function below does NOT increment `totalStaked`.
  This is the formal encoding of Fix V3 (§6 of the paper).
  In the buggy `launchpad.move`, `participate_in_launchpad` contained:
    launchpad.total_staked = launchpad.total_staked + staked_value_to_use
  This doubled the allocation denominator, halving every participant's
  entitlement.  The fix removes that line.  The proof
  `totalStakedUnchangedByParticipate_v2` (Lemmas.lean) certifies this.

  KEY DESIGN NOTE — V4 FIX:
  The `createVestingTransition` function uses Strategy 2, not Strategy 1.
  In the buggy `launchpad.move`, `create_the_vesting` called:
    create_strategy_not_for_coin(1, 0, ctx)
  which aborted inside ctf::vesting (Strategy 1 with amount_each = 0
  triggers ERROR_INVALID_STRATEGY).  The fix uses Strategy 2 and
  populates allocations explicitly via `set_allocate_amount_per_user`.
-/

import TalonLock.Defs

namespace TalonLock

-- ── Abstract step relation ───────────────────────────────────────

structure LaunchpadStep (l l' : LaunchpadState) : Prop where
  preserve_wf : WellFormedLaunchpad l → WellFormedLaunchpad l'

inductive LaunchpadReach : LaunchpadState → LaunchpadState → Prop where
  | refl (l : LaunchpadState) : LaunchpadReach l l
  | step {l l' l'' : LaunchpadState} :
      LaunchpadStep l l' → LaunchpadReach l' l'' → LaunchpadReach l l''

theorem LaunchpadReach.preserves_wf {l l' : LaunchpadState}
    (h : LaunchpadReach l l') (hw : WellFormedLaunchpad l) :
    WellFormedLaunchpad l' := by
  induction h with
  | refl l => exact hw
  | step hs hr ih => exact ih (hs.preserve_wf hw)

-- ── Concrete patched operations ──────────────────────────────────

/-- register (patched): participant u stakes `stake` tokens.
    totalStaked increases by stake.  This is the ONLY place
    totalStaked is modified — the V3 fix ensures participate
    does not touch it. -/
def register (l : LaunchpadState) (u : Addr) (stake : Nat) : LaunchpadState :=
  { l with
    regAmt      := updateMap l.regAmt u stake
    totalStaked := l.totalStaked + stake }

theorem register_preserves_wf {l : LaunchpadState} (u : Addr) (stake : Nat)
    (h_stake : stake > 0)
    (hw : WellFormedLaunchpad l) :
    WellFormedLaunchpad (register l u stake) := by
  constructor
  · exact hw.rate_pos
  · unfold register; simp; omega

/-- participate (patched — V3 FIX): registered participant u makes payment.
    Records payAmt and computes allocAmt.
    CRITICAL: totalStaked is NOT modified here.
    In the buggy version, total_staked was incremented a second time here.
    The theorem `totalStakedUnchangedByParticipate_v2` certifies this fix. -/
def participate (l : LaunchpadState) (u : Addr) (pay : Nat) : LaunchpadState :=
  let l₁ := { l with payAmt := updateMap l.payAmt u pay }
  { l₁ with allocAmt := updateMap l₁.allocAmt u (alloc_L l₁ u) }
  -- totalStaked field is not touched — this encodes Fix V3

theorem participate_preserves_wf {l : LaunchpadState} (u : Addr) (pay : Nat)
    (hw : WellFormedLaunchpad l) :
    WellFormedLaunchpad (participate l u pay) := by
  constructor
  · exact hw.rate_pos
  · unfold participate; simp; exact hw.totalStaked_pos

/-- V3 fix certificate: participate does not modify totalStaked. -/
theorem totalStakedUnchangedByParticipate
    (l : LaunchpadState) (u : Addr) (pay : Nat) :
    (participate l u pay).totalStaked = l.totalStaked := by
  unfold participate; simp

/-- close (patched): admin closes the launchpad at time t.
    isActive := false; closeTime := t.  After this, totalStaked is frozen. -/
def closeLaunchpad (l : LaunchpadState) (t : Nat) : LaunchpadState :=
  { l with isActive := false, closeTime := t }

theorem closeLaunchpad_preserves_wf {l : LaunchpadState} (t : Nat)
    (hw : WellFormedLaunchpad l) :
    WellFormedLaunchpad (closeLaunchpad l t) := by
  constructor
  · exact hw.rate_pos
  · unfold closeLaunchpad; simp; exact hw.totalStaked_pos

/-- createVestingTransition (patched — V4 FIX): links the launchpad to the
    vesting object by recording vestingRef.
    Strategy 2 is used by the vesting object (encoded in `createVestingState`
    in CompositionInvariant.lean).  The V4 bug used Strategy 1 with
    amount_each = 0, which caused an abort in ctf::vesting. -/
def linkVesting (l : LaunchpadState) (vestingId : Addr) : LaunchpadState :=
  { l with vestingRef := some vestingId }

theorem linkVesting_preserves_wf {l : LaunchpadState} (vestingId : Addr)
    (hw : WellFormedLaunchpad l) :
    WellFormedLaunchpad (linkVesting l vestingId) := by
  constructor
  · exact hw.rate_pos
  · unfold linkVesting; simp; exact hw.totalStaked_pos

end TalonLock
