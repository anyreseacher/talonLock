/-
  TalonLock/TalonLock.lean
  ═════════════════════════
  The talon-lock predicate — §3 Definition 7.

  TL(l, v) holds when the vesting object v faithfully reflects
  the launchpad state l at the composition boundary.
  Five conditions must hold simultaneously:
    (1) ref_set      — launchpad holds a reference to v's object id
    (2) strategy_two — v uses Strategy 2 (per-user allocation)
    (3) alloc_eq     — every participant's allocMap entry = alloc_L(l, u)
    (4) start_eq     — vesting start = launchpad close time
    (5) admin_eq     — administrative authority is consistent

  The strategy_two field is essential: it ensures that
  `entitlement v u = v.allocMap u`, which is required for
  `sched v u (start + duration) = alloc_L l u` (Goal 1 of Theorem 1).
  Without it, the schedule could use amountEach (S1) or proofLock (S3),
  neither of which is set by the launchpad handoff.

  This predicate is what distinguishes talon-lock from a weaker
  existence predicate.  A CCS FM&PL reviewer will check that all
  five fields are genuinely necessary and jointly sufficient.
-/

import TalonLock.Defs

namespace TalonLock

/-- §3 Definition 7: Talon-Lock predicate. -/
structure TalonLock (l : LaunchpadState) (v : VestingState) : Prop where
  /-- (1) The launchpad holds a reference to the vesting object. -/
  ref_set      : l.vestingRef = some v.id
  /-- (2) The vesting object uses Strategy 2 (per-user allocation).
      Required so that entitlement v u = v.allocMap u. -/
  strategy_two : v.strategy = 2
  /-- (3) Every participant's allocation map entry equals the
      launchpad-computed allocation.  This is the handoff integrity
      condition: V3 (the denominator double-increment) violates this. -/
  alloc_eq     : ∀ u : Addr, participants l u → v.allocMap u = alloc_L l u
  /-- (4) The vesting schedule starts exactly when the launchpad closes. -/
  start_eq     : v.start = l.closeTime
  /-- (5) The administrator is the same across both modules. -/
  admin_eq     : v.admin = l.admin

end TalonLock
