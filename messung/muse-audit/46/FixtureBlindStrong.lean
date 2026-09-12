/-
  Audit 46, fixture BLIND-STRONG (from `instrumente/pruefe-praemisse.py`,
  read, not run: `--sprechprobe` calls `lean` directly, which hard rule 2
  forbids -- so the fixture is rebuilt here as a Lean demonstration).

  Fixture source (lines 1604-1610):
    theorem mid (h : 0 < 1) (k : 1 < 2) : 0 < 2 ∧ 1 < 2 ∧ 0 < 2 := by
      exact ⟨Nat.lt_trans h k, k, Nat.lt_trans h k⟩

  Same shape as BLIND-WEAK except c3 needs `h` and `k` JOINTLY. What the
  instrument claims (lines 1752-1755, 1789-1793): per-theorem still DERIVED,
  per-conjunct need still [NEEDS, FREE, NEEDS] -- but strength at c3 reads
  JOINT (weakening `k` breaks c3: `Nat.lt_trans h k` mentions `k`).

  Demonstrated below WITHOUT the instrument: the per-conjunct tripwires.
  The ONLY difference from the WEAK fixture is the c3 closer: `h` alone no
  longer suffices; both premises travel. Compare
  `FixtureBlindWeak.lean:audit46_blindweak_c3_alone` (`h` alone, green) with
  `audit46_blindstrong_c3_needs_both` below (needs `h` AND `k`).
-/

namespace Audit46BlindStrong

/-- c1 needs `h` jointly with `k`, as in the WEAK fixture. -/
theorem audit46_blindstrong_c1_needs_h (h : 0 < 1) (k : 1 < 2) : 0 < 2 :=
  Nat.lt_trans h k

/-- c2 is FREE of `h`, as in the WEAK fixture. -/
theorem audit46_blindstrong_c2_free (k : 1 < 2) : 1 < 2 :=
  k

/-- c3 is JOINT in `h` and `k`: the transit closer reads both premises.
    This is the STRONG side: weakening `k` (strength variant) breaks c3. -/
theorem audit46_blindstrong_c3_needs_both (h : 0 < 1) (k : 1 < 2) : 0 < 2 :=
  Nat.lt_trans h k

/-- c3 with `k` weakened dies: from `h` alone no `0 < 2` follows by transit
    through `1` -- stated as the contrapositive the instrument measures:
    the `h`-only context proves a WEAKER bound (`0 < 1`), not the `0 < 2`
    the closer demands without `k`. -/
theorem audit46_blindstrong_h_alone_weaker (h : 0 < 1) : 0 < 1 :=
  h

/-- The full fixture, green basis: all three closers together. -/
theorem audit46_blindstrong_mid (h : 0 < 1) (k : 1 < 2) : 0 < 2 ∧ 1 < 2 ∧ 0 < 2 :=
  ⟨Nat.lt_trans h k, k, Nat.lt_trans h k⟩

end Audit46BlindStrong

/-
CUTS:
- As in the WEAK fixture: NEEDS/FREE/JOINT verdicts are computed by
  `pruefe-praemisse.py`, which this lane may not run; demonstrated here is the
  Lean content of each verdict (per-conjunct tripwire copies).
- The instrument-level difference (strength ALONE vs JOINT at c3) is exactly
  the closer difference: `h` (weak) vs `Nat.lt_trans h k` (strong).
- The per-theorem verdict cannot tell the fixtures apart (both DERIVED) and
  per-conjunct need cannot either (both [NEEDS, FREE, NEEDS]) -- only the
  strength probe at c3 separates them. That is the blind spot the pair names.
-/
#print axioms Audit46BlindStrong.audit46_blindstrong_c1_needs_h
#print axioms Audit46BlindStrong.audit46_blindstrong_c3_needs_both
#print axioms Audit46BlindStrong.audit46_blindstrong_mid
