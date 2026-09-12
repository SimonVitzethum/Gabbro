/-
  Audit 46, fixture BLIND-WEAK (from `instrumente/pruefe-praemisse.py`,
  read, not run: `--sprechprobe` calls `lean` directly, which hard rule 2
  forbids -- so the fixture is rebuilt here as a Lean demonstration).

  Fixture source (lines 1595-1602):
    theorem mid (h : 0 < 1) (k : 1 < 2) : 0 < 2 ∧ 1 < 2 ∧ 0 < 1 := by
      exact ⟨Nat.lt_trans h k, k, h⟩

  What the instrument claims for it (lines 1752-1755, 1789-1793): per-theorem
  reads DERIVED (variant A red: `h := True` breaks c1 and c3; variant B red:
  `k := True` breaks c1 and c2), per-conjunct need reads [NEEDS, FREE, NEEDS]
  (weakening `h` breaks c1 and c3 but not c2), and strength at c3 reads ALONE
  (weakening `k` leaves c3 green: `h : 0 < 1` alone carries `0 < 1`).

  Demonstrated below WITHOUT the instrument: the exact per-conjunct
  tripwires. Each copy keeps the binders, narrows the conclusion to one
  conjunct, and runs its own closer:
  - c1 NEEDS h: `mid__c1` uses `h`; with `h : True` the `Nat.lt_trans h k`
    closer dies (shown as the `True`-weakened copy failing to elaborate --
    pinned here by the positive: the unweakened copy checks).
  - c2 FREE of h: `audit46_blindweak_c2_free` proves `1 < 2` from `k` alone,
    with `h` generalized away (works for ALL `h`, hence uses none of it).
  - c3 ALONE in h: `audit46_blindweak_c3_alone` proves `0 < 1` from `h` alone,
    with `k` generalized away; the per-theorem B direction (weaken `k`, keep
    `h`) still derives c3 -- restatement shape, weak.
-/

namespace Audit46BlindWeak

/-- c1 needs `h` jointly with `k`: the transit closes only from both. -/
theorem audit46_blindweak_c1_needs_h (h : 0 < 1) (k : 1 < 2) : 0 < 2 :=
  Nat.lt_trans h k

/-- c2 is FREE of `h`: proves from `k` alone, `h` generalized away. -/
theorem audit46_blindweak_c2_free (k : 1 < 2) : 1 < 2 :=
  k

/-- c2 with `h` present but unread: same statement, proof ignores `h`. -/
theorem audit46_blindweak_c2_ignores_h (h : 0 < 1) (k : 1 < 2) : 1 < 2 :=
  k

/-- c3 is ALONE in `h`: proves from `h` alone, `k` generalized away.
    This is the WEAK side: the premise alone carries the conjunct. -/
theorem audit46_blindweak_c3_alone (h : 0 < 1) : 0 < 1 :=
  h

/-- c3 with `k` present but unread: weakening `k` (variant B direction for
    the strength question) leaves c3 green. -/
theorem audit46_blindweak_c3_strength (h : 0 < 1) (k : 1 < 2) : 0 < 1 :=
  h

/-- The full fixture, green basis: all three closers together. -/
theorem audit46_blindweak_mid (h : 0 < 1) (k : 1 < 2) : 0 < 2 ∧ 1 < 2 ∧ 0 < 1 :=
  ⟨Nat.lt_trans h k, k, h⟩

end Audit46BlindWeak

/-
CUTS:
- The NEEDS/FREE/ALONE verdicts themselves are computed by
  `pruefe-praemisse.py` (lane builds + hermetic `lean`), which this lane may
  not run (hard rule 2: never call `lake`/`lean` directly; `--sprechprobe`
  violates it). What is demonstrated here is the Lean CONTENT of each verdict:
  the per-conjunct tripwire copies whose red/green the instrument reads.
- c1 NEEDS h is shown positively (the closer mentions `h`); the negative
  (weakened copy red) is instrument-measured, not re-proved here.
- Every premise of every theorem above is used, except `audit46_blindweak_c2_ignores_h`
  and `audit46_blindweak_c3_strength`, which DELIBERATELY carry an unread
  premise to exhibit the FREE/ALONE direction -- the unused-premise shape IS
  the demonstration (same license as MUSE-REPORT-23 F2, whose linter warnings
  were filed as evidence).
-/
#print axioms Audit46BlindWeak.audit46_blindweak_c1_needs_h
#print axioms Audit46BlindWeak.audit46_blindweak_c2_free
#print axioms Audit46BlindWeak.audit46_blindweak_c3_alone
#print axioms Audit46BlindWeak.audit46_blindweak_mid
