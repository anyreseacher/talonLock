/-
  TalonLock/Defs.lean
  ═══════════════════
  Core types, state records, predicates, and schedule function.

  Paper: "Talon-Lock Invariants: Cross-Module Formal Verification
          of Composed IOTA Move Protocols"  ACM CCS 2026

  §3 Joint Formal Model — Definitions 1–7.

  Design notes
  ────────────
  • All arithmetic is over ℕ (Lean's Nat), which abstracts u64
    without modelling overflow.  Truncating subtraction (a - b for
    Nat) is used for elapsed-time calculations; this is the V2 fix.
  • `VestingState.id` abstracts the IOTA on-chain object UID.
  • `VestingState.collected` tracks admin-collected residue so that
    fund conservation can be stated as an equality over all states,
    including post-`collect` states.
  • `sched` is the proportional formula from §3 Definition 5.
    It returns `entitlement v u * min(elapsed, duration) / duration`.
    The step-function approximation is *not* used: the paper gives
    the proportional formula and the CCS FM&PL reviewer will check it.
-/

namespace TalonLock

-- ── Basic types ──────────────────────────────────────────────────

abbrev Addr := Nat

/-- Address map: total function with default value 0.
    Abstracts `iota::dynamic_field` key–value lookups. -/
abbrev AddrMap := Addr → Nat

-- ── Vesting state ────────────────────────────────────────────────

/-- §3 Definition 1.  Abstract state of ctf::vesting. -/
structure VestingState where
  id           : Addr      -- IOTA object UID (abstract address)
  coin         : Nat       -- in-contract token balance
  supply       : Nat       -- cumulative supply ever deposited
  totalVested  : Nat       -- cumulative amount released to participants
  collected    : Nat       -- admin-collected residue (after vestingEnded)
  start        : Nat       -- vesting start timestamp (milliseconds)
  admin        : Addr      -- administrator address
  strategy     : Nat       -- 1 = linear-equal, 2 = per-user, 3 = proof-token
  amountEach   : Nat       -- Strategy-1 entitlement per user
  duration     : Nat       -- vesting duration (must be > 0)
  allocMap     : AddrMap   -- Strategy-2 per-user allocation
  released     : AddrMap   -- cumulative released per user
  proofLock    : AddrMap   -- Strategy-3 proof-lock per user

-- ── Launchpad state ──────────────────────────────────────────────

/-- §3 Definition 2.  Abstract state of ctf::launchpad. -/
structure LaunchpadState where
  totalStaked : Nat           -- sum of registered stakes (frozen at close)
  totalAlloc  : Nat           -- total token allocation for participants
  rate        : Nat           -- conversion rate (must be > 0)
  isActive    : Bool          -- true until close_launchpad fires
  closeTime   : Nat           -- timestamp at which launchpad closed
  admin       : Addr          -- administrator address
  vestingRef  : Option Addr   -- UID of created vesting object (None until createVesting)
  regAmt      : AddrMap       -- stake registered per participant
  payAmt      : AddrMap       -- payment made per participant
  allocAmt    : AddrMap       -- allocation computed per participant

-- ── Joint state ──────────────────────────────────────────────────

structure JointState where
  v : VestingState
  l : LaunchpadState

-- ── Derived sets ─────────────────────────────────────────────────

/-- §3 Definition 3.  Participant set: addresses with positive stake. -/
def participants (l : LaunchpadState) (u : Addr) : Prop :=
  l.regAmt u > 0

-- ── Allocation function ──────────────────────────────────────────

/-- §3 Definition 4 (Eq. 1).  Per-participant token allocation at close.
    Uses truncating Nat division throughout.  Requires rate > 0 and
    totalStaked > 0 to avoid division by zero (ensured by WellFormedLaunchpad). -/
def alloc_L (l : LaunchpadState) (u : Addr) : Nat :=
  (Nat.min (l.payAmt u) (l.regAmt u) * l.totalAlloc) /
  (l.rate * l.totalStaked)

-- ── Schedule function ────────────────────────────────────────────

/-- Strategy-dependent entitlement (before time scaling).
    S1 → amountEach;  S2 → allocMap u;  S3 → proofLock u. -/
def entitlement (v : VestingState) (u : Addr) : Nat :=
  if v.strategy = 1 then v.amountEach
  else if v.strategy = 2 then v.allocMap u
  else v.proofLock u

/-- §3 Definition 5.  Maximum tokens releasable to u at time t.
    Proportional formula: entitlement × min(elapsed, duration) / duration.
    • Elapsed = t - start (truncating subtraction, i.e. monus).
    • At t = start + duration: sched = entitlement (proved below).
    • For t < start: elapsed = 0, so sched = 0 (no early release, P4(i)). -/
def sched (v : VestingState) (u : Addr) (t : Nat) : Nat :=
  let elapsed  := t - v.start          -- Nat subtraction: 0 when t < start
  let progress := Nat.min elapsed v.duration
  entitlement v u * progress / v.duration

-- ── Fund conservation and release bounds ─────────────────────────

/-- P1: at every reachable state, coin + totalVested + collected = supply.
    `collected` tracks admin residue so the equality holds post-collect. -/
def FundConservation (v : VestingState) : Prop :=
  v.coin + v.totalVested + v.collected = v.supply

/-- P3-support: released amount for each user never exceeds their entitlement. -/
def ReleasedBounded (v : VestingState) : Prop :=
  ∀ u : Addr, v.released u ≤ entitlement v u

-- ── Well-formedness predicates ────────────────────────────────────

/-- Vesting well-formedness: structural invariants that all reachable
    vesting states satisfy. -/
structure WellFormedVesting (v : VestingState) : Prop where
  duration_pos     : v.duration > 0
  strategy_valid   : v.strategy = 1 ∨ v.strategy = 2 ∨ v.strategy = 3
  fund             : FundConservation v
  released_bounded : ReleasedBounded v

/-- Launchpad well-formedness: rate and totalStaked positive. -/
structure WellFormedLaunchpad (l : LaunchpadState) : Prop where
  rate_pos        : l.rate > 0
  totalStaked_pos : l.totalStaked > 0

structure WellFormedState (s : JointState) : Prop where
  vwf : WellFormedVesting s.v
  lwf : WellFormedLaunchpad s.l

-- ── Utility ──────────────────────────────────────────────────────

/-- Pointwise map update: updateMap m a x u = if u = a then x else m u. -/
def updateMap (m : AddrMap) (a : Addr) (x : Nat) : AddrMap :=
  fun u => if u = a then x else m u

-- ── Key schedule lemmas ──────────────────────────────────────────

/-- Lemma: at t = start + duration, sched = entitlement.
    This is the §4 P4(ii) ceiling fact: vesting is complete at end time. -/
theorem sched_at_end (v : VestingState) (u : Addr)
    (h_dur : v.duration > 0) :
    sched v u (v.start + v.duration) = entitlement v u := by
  unfold sched
  simp only []
  -- elapsed = (start + duration) - start = duration
  have h_elapsed : v.start + v.duration - v.start = v.duration := by omega
  rw [h_elapsed]
  -- progress = min duration duration = duration
  have h_min : Nat.min v.duration v.duration = v.duration := Nat.min_self v.duration
  rw [h_min]
  -- entitlement * duration / duration = entitlement
  -- entitlement * duration / duration = entitlement  (duration > 0)
  exact Nat.mul_div_cancel (entitlement v u) h_dur

/-- Lemma: for t ≤ start, sched = 0 (no early release, supports P4(i)). -/
theorem sched_before_start (v : VestingState) (u : Addr)
    (h : t ≤ v.start) :
    sched v u t = 0 := by
  unfold sched
  simp only []
  -- elapsed = t - start = 0 when t ≤ start
  have h_zero : t - v.start = 0 := Nat.sub_eq_zero_of_le h
  rw [h_zero]
  simp

/-- Lemma: under Strategy 2, entitlement = allocMap u. -/
theorem entitlement_strategy_two {v : VestingState} (h : v.strategy = 2) (u : Addr) :
    entitlement v u = v.allocMap u := by
  unfold entitlement; simp [h]

end TalonLock
