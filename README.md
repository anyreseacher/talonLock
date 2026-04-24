# Artifact: Talon-Lock Invariants
**Paper:** "Talon-Lock Invariants: Cross-Module Formal Verification of Composed IOTA Move Protocols"
---

## Overview

This artifact supports all formal and empirical claims in the paper. It contains:

1. **Move source** — the original (buggy) and hardened (patched) IOTA Move protocol
2. **MSL formal specifications** — Move Specification Language annotations for the Move Prover
3. **Lean 4 proofs** — machine-checked proofs of all formal claims including the Composition Invariant Theorem
4. **Experimental results** — Move Prover output screenshots and on-chain deployment data

The central claim verified by this artifact is **Theorem 1 (Composition Invariant)**: under the talon-lock predicate, every participant's vesting entitlement at schedule end equals their launchpad-computed allocation, release is schedule-bounded, and total token supply is conserved.

---

## Repository Structure

```
.
├── README.md                          ← this file
├── Move.toml                          ← IOTA Move package manifest
├── Move.lock                          ← dependency lock file
├── Commands.sh                        ← build and prove commands
│
├── sources/                           ← Move source files
│   ├── vesting.move                   ← original (buggy) vesting module
│   ├── vesting_hardened.move          ← patched vesting module (V1–V5 fixed)
│   ├── launchpad.move                 ← original (buggy) launchpad module
│   └── launchpad_hardened.move        ← patched launchpad module (V3, V4 fixed)
│
├── specs/                             ← MSL formal specifications
│   ├── vesting_formal_spec.move       ← Move Prover annotations for vesting
│   └── launchpad_formal_spec.move     ← Move Prover annotations for launchpad
│
├── lean4_proofs/                      ← Lean 4 machine-checked proofs
│   ├── README.md                      ← Lean 4 build instructions
│   ├── lakefile.lean                  ← Lake build configuration
│   ├── lean-toolchain                 ← Lean 4 version pin (v4.14.0)
│   ├── TalonLock.lean                 ← root module
│   └── TalonLock/
│       ├── Defs.lean                  ← §3: types, state records, sched, alloc_L
│       ├── TalonLock.lean             ← §3 Def 7: talon-lock predicate
│       ├── VestingReach.lean          ← §3: vesting transition relation
│       ├── LaunchpadReach.lean        ← §3: launchpad transition relation (V3 fix)
│       ├── Lemmas.lean                ← §7: P1–P5, V1–V5 fix lemmas, gas bound
│       └── CompositionInvariant.lean  ← §5 Theorem 1 + corollaries
│
├── SimpleCoin/                        ← test token contracts
│   ├── Move.toml
│   └── sources/
│       ├── examplecoin.move
│       └── testcoin.move
│
└── experimental_results/              ← evaluation evidence
    ├── experiment_notes.txt           ← build status, IOTA framework revision
    ├── vesting_formal_spec.move       ← (also in specs/ — kept for provenance)
    ├── launchpad_formal_spec.move     ← (also in specs/ — kept for provenance)
    └── Screenshot_*.png               ← Move Prover output (14 screenshots)
```

> **Note on file naming:** `sources/launchpad_hardened.move` and
> `sources/vesting_hardened.move` correspond to `launchpad_.mov` and
> `vesting_.move` in the original repository. The extensions and names have
> been corrected for clarity.

---

## Quick Start

### 1. Verify the Lean 4 proofs

```bash
# Install elan (Lean version manager)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.bashrc

# Build and check all proofs
cd lean4_proofs
lake build
```

Output:
```
Building TalonLock.Defs
Building TalonLock.TalonLock
Building TalonLock.VestingReach
Building TalonLock.LaunchpadReach
Building TalonLock.Lemmas
Building TalonLock.CompositionInvariant
Building TalonLock
Build completed successfully.
```

A successful build with no errors confirms that all 63 definitions and theorems
are machine-checked by the Lean 4 kernel.

### 2. Run the Move Prover 

Requirements: IOTA CLI with Move Prover support
([installation guide](https://docs.iota.org/developer/getting-started/install-iota)).

```bash
# Prove the hardened vesting module
iota move prove --path specs/vesting_formal_spec.move \
                --named-address ctf=0x0

# Prove the hardened launchpad module
iota move prove --path specs/launchpad_formal_spec.move \
                --named-address ctf=0x0
```

Expected output: verification succeeded for all annotated functions.
The `experimental_results/Screenshot_*.png` files show the actual prover
output from the paper's evaluation run.

### 3. Build the Move package

```bash
# Build original (buggy) package
iota move build

# Build hardened package (recommended)
cp sources/vesting_hardened.move sources/vesting.move
cp sources/launchpad_hardened.move sources/launchpad.move
iota move build
```

---

### Formal Claims (Lean 4)

| Paper claim | File | Lean 4 identifier |
|---|---|---|
| §3 Def 1: VestingState | `TalonLock/Defs.lean` | `VestingState` |
| §3 Def 2: LaunchpadState | `TalonLock/Defs.lean` | `LaunchpadState` |
| §3 Def 3: participants | `TalonLock/Defs.lean` | `participants` |
| §3 Def 4: alloc_L (Eq. 1) | `TalonLock/Defs.lean` | `alloc_L` |
| §3 Def 5: sched | `TalonLock/Defs.lean` | `sched` |
| §3 Def 7: TalonLock predicate | `TalonLock/TalonLock.lean` | `TalonLock` |
| §5 Theorem 1: Composition Invariant | `TalonLock/CompositionInvariant.lean` | `compositionInvariant` |
| §5 Hardened handoff establishes TL | `TalonLock/CompositionInvariant.lean` | `createVesting_establishes_talonLock` |
| §4 P1: Fund Conservation | `TalonLock/Lemmas.lean` | `fundConservation` |
| §4 P2: Admin Immutability | `TalonLock/Lemmas.lean` | `adminFieldImmutable` |
| §4 P3: Monotonic Release | `TalonLock/Lemmas.lean` | `totalVestedNonDecreasing` |
| §4 P4(ii): Schedule Ceiling | `TalonLock/Lemmas.lean` | `durationScheduleCeiling` |
| §4 N1: Non-Interference | `TalonLock/Lemmas.lean` | `strategyNonInterference` |
| §6 V1 fix: Proof-token replay | `TalonLock/Lemmas.lean` | `proofLockedMonotone`, `replayRequiresZeroProof` |
| §6 V2 fix: u64 underflow | `TalonLock/Lemmas.lean` | `elapsedNoUnderflow` |
| §6 V3 fix: Denominator stability | `TalonLock/LaunchpadReach.lean` | `totalStakedUnchangedByParticipate` |
| §6 V4 fix: Strategy 2 no abort | `TalonLock/Lemmas.lean` | `strategyTwoDoesNotAbort` |
| §6 V5 fix: Dual-None terminal | `TalonLock/Lemmas.lean` | `DualNoneCoveredByMarkEnded` |
| §8 Gas safety bound | `TalonLock/Lemmas.lean` | `gasSafeConcrete` |

### Vulnerability Evidence (Move Source)

| Vulnerability | Buggy file | Buggy line | Patched file |
|---|---|---|---|
| V1: Proof-token replay | `sources/vesting.move` | `release_coins_by_coinbase` — proof tokens returned without locking | `sources/vesting_hardened.move` |
| V2: u64 underflow | `sources/vesting.move` | `get_frame_base_releasable_amount` — `start_time - frame.time` | `sources/vesting_hardened.move` |
| V3: Denominator inflation | `sources/launchpad.move` | `participate_in_launchpad` line 200 — `total_staked += staked_value_to_use` | `sources/launchpad_hardened.move` |
| V4: Talon-lock failure | `sources/launchpad.move` | `create_the_vesting` — strategy 1 with `amount_each = 0` | `sources/launchpad_hardened.move` |
| V5: Termination guard | `sources/vesting.move` | `has_vesting_ended` — missing `else { true }` for dual-None | `sources/vesting_hardened.move` |

### Move Prover Coverage (MSL)

| Property | File | Verification status |
|---|---|---|
| P1 Fund Conservation | `specs/vesting_formal_spec.move` | PARTIAL (per-transition; constructor base case in Lean 4) |
| P2 Admin Exclusivity | `specs/vesting_formal_spec.move` | FULL (`aborts_if sender() != admin`) |
| P3 Monotonic Release | `specs/vesting_formal_spec.move` | PARTIAL (per-transition) |
| P4(i) No early release | `specs/vesting_formal_spec.move` | FULL (`aborts_if current_time < start`) |
| P5 Allocation integrity | `specs/launchpad_formal_spec.move` | PARTIAL (denominator stability only; cross-module in Lean 4) |
| V2–V5 fix correctness | both spec files | FULL (`ensures`/`aborts_if` on patched functions) |

---

## Vulnerabilities: Where to Look

### V3 — Denominator Double-Increment (cross-function, provably undetectable by fn-local analysis)

**Buggy code** (`sources/launchpad.move`, function `participate_in_launchpad`):
```move
// Line 145: register correctly increments totalStaked
launchpad.total_staked = launchpad.total_staked + staked_value;

// Line 200 (BUG): participate ALSO increments totalStaked
launchpad.total_staked = launchpad.total_staked + staked_value_to_use;
```
This doubles the allocation denominator, halving every participant's entitlement.

**Patched code** (`sources/launchpad_hardened.move`): line 200 removed.

**Formal certificate**: `totalStakedUnchangedByParticipate` in `TalonLock/LaunchpadReach.lean`.

### V4 — Talon-Lock Establishment Failure (cross-module, provably undetectable by fn-local analysis)

**Buggy code** (`sources/launchpad.move`, function `create_the_vesting`):
```move
let strategy = create_strategy_not_for_coin(
    1,   // Strategy 1: linear
    0,   // amount_each = 0  ← triggers abort in vesting
    ctx
);
```
`vesting::create_strategy_not_for_coin` aborts when `id_strategy = 1` and `amount_each = 0`.
This leaves `launchpad.vesting_contract = option::none()` permanently.
All participant allocations become unrealisable. Funds are locked.

**Patched code** (`sources/launchpad_hardened.move`): switches to Strategy 2
and calls `set_allocate_amount_per_user` for each participant.

**Formal certificate**: `strategyTwoDoesNotAbort` in `TalonLock/Lemmas.lean`;
`createVesting_establishes_talonLock` in `TalonLock/CompositionInvariant.lean`.

---

## Evaluation Evidence

### Move Prover screenshots

The 14 screenshots in `experimental_results/` correspond to the prover runs
reported in §8 (Evaluation) of the paper:

| Screenshot | Content |
|---|---|
| `Screenshot_1.png` – `_6.png` | Prototype (buggy) package — prover finds violations |
| `Screenshot_7.png` – `_14.png` | Hardened package — all annotated properties verified |

### On-chain deployment

The hardened package was deployed on the IOTA testnet.
Deployment details (package ID, transaction digest, object IDs) are provided
at camera-ready to avoid de-anonymization during double-blind review.

IOTA framework revision used:
```
73ba3c698cf3d73728d3bf386a22f451695a91d1
```

---

## Dependencies

| Component | Version | Purpose |
|---|---|---|
| Lean 4 | v4.14.0 (pinned) | Kernel-checked proofs |
| IOTA CLI | ≥ v0.1.6 | Move build and Move Prover |
| IOTA framework | `73ba3c69...` | On-chain deployment |
| Mathlib4 | not required | All proofs use core Lean 4 only |

```
