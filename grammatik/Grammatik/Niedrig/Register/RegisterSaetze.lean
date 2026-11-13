/-
  File:      Grammatik/Niedrig/Register/RegisterSaetze.lean
  Subject:   THEOREMS OVER DEVICE REGISTERS (L2c): the frame (refused
    operations keep the state), read-after-write shape, the width bound,
    the fallible-read promise, the transition trace, and independence.

  Left out (booked, not hidden): general bit-vector lemmas over
  `Nat.land` / `Nat.lor` / `Nat.xor` (for example that `neuerWert` stays
  below `2 ^ breite` for all masks, or that clearing then setting is the
  identity outside the mask). Only what `rfl` / `decide` on the fixture
  and simple unfolding give is proved; the rest is a later bit package.
-/
module

public import Grammatik.Niedrig.Register.Register

@[expose] public section


namespace Gabbro.Grammatik.Niedrig.Register

/-! ## A read changes no state -/

/-- `regRead` keeps the device state. Reading is a query of `lies`; read
    side effects of real devices are OUTSIDE this layer. -/
theorem lesBleibt {S : Type} (d : Device S) (s : S) (r : Reg) :
    (regRead d s r).1 = s := by
  unfold regRead
  cases hdecl : d.decl r with
  | none =>
    rfl
  | some decl =>
    dsimp only
    by_cases hles : darfLesen decl.klasse = true
    · rw [if_pos hles]
    · rw [if_neg hles]

/-- A refused read (no read right) keeps the state. -/
theorem lesVerweigertBleibt {S : Type} (d : Device S) (s : S) (r : Reg)
    (decl : RegDecl)
    (hdecl : d.decl r = some decl)
    (hles : darfLesen decl.klasse = false) :
    (regRead d s r).1 = s := by
  unfold regRead
  rw [hdecl]
  dsimp only
  have hneg : ¬ (darfLesen decl.klasse = true) := by
    rw [hles]
    exact fun h => Bool.noConfusion h
  rw [if_neg hneg]

/-- A read of an undeclared register keeps the state. -/
theorem lesUnbekanntBleibt {S : Type} (d : Device S) (s : S) (r : Reg)
    (hdecl : d.decl r = none) :
    (regRead d s r).1 = s := by
  unfold regRead
  rw [hdecl]

/-- A refused write (no write right) keeps the state. -/
theorem schreibVerweigertBleibt {S : Type} (d : Device S) (s : S) (r v : Nat)
    (decl : RegDecl)
    (hdecl : d.decl r = some decl)
    (hschreib : darfSchreiben decl.klasse = false) :
    (regWrite d s r v).1 = s := by
  unfold regWrite
  rw [hdecl]
  dsimp only
  have hneg : ¬ (darfSchreiben decl.klasse = true) := by
    rw [hschreib]
    exact fun h => Bool.noConfusion h
  rw [if_neg hneg]

/-- A write with too large a value keeps the state. -/
theorem schreibZuGrossBleibt {S : Type} (d : Device S) (s : S) (r v : Nat)
    (decl : RegDecl)
    (hdecl : d.decl r = some decl)
    (hschreib : darfSchreiben decl.klasse = true)
    (hgross : ¬ v < 2 ^ decl.breite) :
    (regWrite d s r v).1 = s := by
  unfold regWrite
  rw [hdecl]
  dsimp only
  rw [if_pos hschreib, if_neg hgross]

/-- A refused fallible read keeps the state. -/
theorem elseVerweigertBleibt {S : Type} (d : Device S) (s : S) (r : Reg)
    (decl : RegDecl)
    (hdecl : d.decl r = some decl)
    (hles : darfLesen decl.klasse = false) :
    (regReadElse d s r).1 = s := by
  unfold regReadElse
  rw [hdecl]
  dsimp only
  have hneg : ¬ (darfLesen decl.klasse = true) := by
    rw [hles]
    exact fun h => Bool.noConfusion h
  rw [if_neg hneg]

/-! ## The value returned by `regRead` fits the width -/

/-- The value returned by `regRead` is below `2 ^ breite`. -/
theorem lesWertKlein {S : Type} (d : Device S) (s : S) (r : Reg)
    (decl : RegDecl) (v : Nat)
    (hdecl : d.decl r = some decl)
    (h : (regRead d s r).2.1 = Except.ok v) :
    v < 2 ^ decl.breite := by
  unfold regRead at h
  rw [hdecl] at h
  dsimp only at h
  by_cases hles : darfLesen decl.klasse = true
  · rw [if_pos hles] at h
    cases h
    show kuerze decl.breite (d.lies s r) < 2 ^ decl.breite
    unfold kuerze
    exact Nat.mod_lt _ (Nat.pow_pos (by decide))
  · rw [if_neg hles] at h
    cases h

/-! ## `regReadElse` returns `ok` exactly when the promise holds -/

/-- A fallible read returning `ok` means the promise holds on the value. -/
theorem elseOkDannZusage {S : Type} (d : Device S) (s : S) (r : Reg)
    (decl : RegDecl) (v : Nat)
    (hdecl : d.decl r = some decl)
    (h : (regReadElse d s r).2.1 = Except.ok (FallErgebnis.ok v)) :
    decl.zusage v = true := by
  unfold regReadElse at h
  rw [hdecl] at h
  dsimp only at h
  by_cases hles : darfLesen decl.klasse = true
  · rw [if_pos hles] at h
    by_cases hzus : decl.zusage (kuerze decl.breite (d.lies s r)) = true
    · rw [if_pos hzus] at h
      cases h
      exact hzus
    · rw [if_neg hzus] at h
      cases h
  · rw [if_neg hles] at h
    cases h

/-- When the promise holds on the truncated value, the fallible read
    returns `ok`. -/
theorem elseZusageDannOk {S : Type} (d : Device S) (s : S) (r : Reg)
    (decl : RegDecl)
    (hdecl : d.decl r = some decl)
    (hles : darfLesen decl.klasse = true)
    (hzus : decl.zusage (kuerze decl.breite (d.lies s r)) = true) :
    (regReadElse d s r).2.1 =
      Except.ok (FallErgebnis.ok (kuerze decl.breite (d.lies s r))) := by
  unfold regReadElse
  rw [hdecl]
  dsimp only
  rw [if_pos hles, if_pos hzus]

/-- When the promise fails on the truncated value, the fallible read takes
    the ELSE branch. -/
theorem elseKeineZusageDannSonst {S : Type} (d : Device S) (s : S) (r : Reg)
    (decl : RegDecl)
    (hdecl : d.decl r = some decl)
    (hles : darfLesen decl.klasse = true)
    (hzus : ¬ decl.zusage (kuerze decl.breite (d.lies s r)) = true) :
    (regReadElse d s r).2.1 =
      Except.ok (FallErgebnis.sonst (kuerze decl.breite (d.lies s r))) := by
  unfold regReadElse
  rw [hdecl]
  dsimp only
  rw [if_pos hles, if_neg hzus]

/-! ## The transition writes the masked value with one read and one write -/

/-- A successful write installs the value through `schreib`. -/
theorem schreibNachSchreib {S : Type} (d : Device S) (s : S) (r v : Nat)
    (decl : RegDecl)
    (hdecl : d.decl r = some decl)
    (hschreib : darfSchreiben decl.klasse = true)
    (hfit : v < 2 ^ decl.breite) :
    (regWrite d s r v).1 = d.schreib s r v := by
  unfold regWrite
  rw [hdecl]
  dsimp only
  rw [if_pos hschreib, if_pos hfit]

/-- A transition through the mirror writes the masked value and shows the
    two-event trace. -/
theorem wechselSpiegelSpur {S : Type} (d : Device S) (s : S)
    (r m maske bits : Nat) (decl mdecl : RegDecl)
    (hdecl : d.decl r = some decl)
    (hschreib : darfSchreiben decl.klasse = true)
    (hspiegel : decl.spiegel = some m)
    (hmdecl : d.decl m = some mdecl)
    (hles : darfLesen mdecl.klasse = true) :
    (regTransition d s r maske bits).2.2 =
      [Event.lese m,
        Event.schreibe r
          (neuerWert decl.breite (kuerze decl.breite (d.lies s m)) maske bits)] ∧
    (regTransition d s r maske bits).1 =
      d.schreib s r
        (neuerWert decl.breite (kuerze decl.breite (d.lies s m)) maske bits) := by
  unfold regTransition
  rw [hdecl]
  dsimp only
  rw [hspiegel]
  dsimp only
  rw [hmdecl]
  dsimp only
  rw [if_pos hschreib, if_pos hles]
  exact ⟨rfl, rfl⟩

/-- A transition without mirror reads the register itself and shows the
    two-event trace. -/
theorem wechselSelbstSpur {S : Type} (d : Device S) (s : S)
    (r maske bits : Nat) (decl : RegDecl)
    (hdecl : d.decl r = some decl)
    (hschreib : darfSchreiben decl.klasse = true)
    (hspiegel : decl.spiegel = none)
    (hles : darfLesen decl.klasse = true) :
    (regTransition d s r maske bits).2.2 =
      [Event.lese r,
        Event.schreibe r
          (neuerWert decl.breite (kuerze decl.breite (d.lies s r)) maske bits)] ∧
    (regTransition d s r maske bits).1 =
      d.schreib s r
        (neuerWert decl.breite (kuerze decl.breite (d.lies s r)) maske bits) := by
  unfold regTransition
  rw [hdecl]
  dsimp only
  rw [hspiegel]
  dsimp only
  rw [if_pos hschreib, if_pos hles]
  exact ⟨rfl, rfl⟩

/-- A successful transition through the mirror performs two events. -/
theorem wechselSpiegelLaenge {S : Type} (d : Device S) (s : S)
    (r m maske bits : Nat) (decl mdecl : RegDecl)
    (hdecl : d.decl r = some decl)
    (hschreib : darfSchreiben decl.klasse = true)
    (hspiegel : decl.spiegel = some m)
    (hmdecl : d.decl m = some mdecl)
    (hles : darfLesen mdecl.klasse = true) :
    List.length (regTransition d s r maske bits).2.2 = 2 := by
  have hspur := wechselSpiegelSpur d s r m maske bits decl mdecl
    hdecl hschreib hspiegel hmdecl hles
  rw [hspur.1]
  rfl

/-- A transition on a write-only register without mirror is refused and
    keeps the state. -/
theorem wechselOhneSpiegelVerweigert {S : Type} (d : Device S) (s : S)
    (r maske bits : Nat) (decl : RegDecl)
    (hdecl : d.decl r = some decl)
    (hschreib : darfSchreiben decl.klasse = true)
    (hspiegel : decl.spiegel = none)
    (hles : darfLesen decl.klasse = false) :
    (regTransition d s r maske bits).2.1 = Except.error ohneSpiegel ∧
    (regTransition d s r maske bits).1 = s := by
  unfold regTransition
  rw [hdecl]
  dsimp only
  rw [hspiegel]
  dsimp only
  have hneg : ¬ (darfLesen decl.klasse = true) := by
    rw [hles]
    exact fun h => Bool.noConfusion h
  rw [if_pos hschreib, if_neg hneg]
  exact ⟨rfl, rfl⟩

/-! ## Operations on different registers commute under `Unabhaengig` -/

/-- A read of one register survives a write to another. -/
theorem lesNachFremdSchreib {S : Type} (d : Device S) (s : S) (r1 r2 v : Nat)
    (hindep : Unabhaengig d)
    (hne : r1 ≠ r2) :
    d.lies (d.schreib s r1 v) r2 = d.lies s r2 := by
  exact hindep.1 s r1 r2 v hne

/-- Two writes to different registers commute pointwise. -/
theorem schreibVertauscht {S : Type} (d : Device S) (s : S)
    (r1 r2 v1 v2 r : Nat)
    (hindep : Unabhaengig d) :
    d.lies (d.schreib (d.schreib s r1 v1) r2 v2) r =
    d.lies (d.schreib (d.schreib s r2 v2) r1 v1) r := by
  exact hindep.2.2 s r1 r2 v1 v2 r

/-- Two successful `regWrite` operations to different registers commute
    pointwise under `Unabhaengig`. -/
theorem schreibOpVertauscht {S : Type} (d : Device S) (s : S)
    (r1 r2 v1 v2 r : Nat) (decl1 decl2 : RegDecl)
    (hdecl1 : d.decl r1 = some decl1)
    (hdecl2 : d.decl r2 = some decl2)
    (hschreib1 : darfSchreiben decl1.klasse = true)
    (hschreib2 : darfSchreiben decl2.klasse = true)
    (hfit1 : v1 < 2 ^ decl1.breite)
    (hfit2 : v2 < 2 ^ decl2.breite)
    (hindep : Unabhaengig d) :
    d.lies (regWrite d (regWrite d s r1 v1).1 r2 v2).1 r =
    d.lies (regWrite d (regWrite d s r2 v2).1 r1 v1).1 r := by
  have e1 : (regWrite d s r1 v1).1 = d.schreib s r1 v1 :=
    schreibNachSchreib d s r1 v1 decl1 hdecl1 hschreib1 hfit1
  have e2 : (regWrite d s r2 v2).1 = d.schreib s r2 v2 :=
    schreibNachSchreib d s r2 v2 decl2 hdecl2 hschreib2 hfit2
  have e12 : (regWrite d (regWrite d s r1 v1).1 r2 v2).1 =
      d.schreib (d.schreib s r1 v1) r2 v2 := by
    rw [e1]
    exact schreibNachSchreib d (d.schreib s r1 v1) r2 v2 decl2
      hdecl2 hschreib2 hfit2
  have e21 : (regWrite d (regWrite d s r2 v2).1 r1 v1).1 =
      d.schreib (d.schreib s r2 v2) r1 v1 := by
    rw [e2]
    exact schreibNachSchreib d (d.schreib s r2 v2) r1 v1 decl1
      hdecl1 hschreib1 hfit1
  rw [e12, e21]
  exact hindep.2.2 s r1 r2 v1 v2 r

#print axioms Gabbro.Grammatik.Niedrig.Register.lesBleibt
#print axioms Gabbro.Grammatik.Niedrig.Register.lesWertKlein
#print axioms Gabbro.Grammatik.Niedrig.Register.elseZusageDannOk
#print axioms Gabbro.Grammatik.Niedrig.Register.wechselSpiegelSpur
#print axioms Gabbro.Grammatik.Niedrig.Register.schreibOpVertauscht

end Gabbro.Grammatik.Niedrig.Register
