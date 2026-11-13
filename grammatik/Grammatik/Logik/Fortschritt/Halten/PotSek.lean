/-
  File:      Grammatik/Logik/Fortschritt/Halten/PotSek.lean
  Subject:   THE POTENTIAL OF A `locks L` SECTION AS A RESIDUE SEGMENT (bridge 2 of Lebendigkeit.lean).
             A section of `L` runs as the residue `.dann body (.frei L k)`; its frame is not a frame of its
             own, so the frame potential `potRest` (KostenG) counts the continuation `k` too. `potSek L`
             reads `potRest` up to the first release marker of `L` and stops there: the marker itself costs
             `1` (the release), and the continuation behind it only `k.freis.length` -- the outer releases a
             scoped `return` inside the section performs before it can release `L` (the cleanup order
             `R.scopes` is any permutation of the markers). `rufeV L` is `rufeR` cut at the same marker:
             only the callees of the section need an admission. Both take the return-predicate price `ep`
             of the frame's function first, exactly as `potRest ep` (C05): a value `return` inside the
             section is priced with its epilogue.

  Every own step of the section's frame lowers `potSek L` by at least one while `L` stays held
  (`schrittSek`, Halten/SchrittSek*.lean), exactly as `schrittArt` lowers `potRest`.
-/
module
public import Grammatik.Logik.Fortschritt.KostenG.T1.Antwort
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **The section potential**: `potRest` up to the first `frei L`, the release `1` and the number of
    release markers behind it. -/
def potSek (L : D.Lock) (ep : Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : GRest D V l Γ Λ → Nat
  | .ende e => kostenEnd ep c pa e
  | .dann b k => kostenBlock ep c pa b + potSek L ep c pa k
  | .schrumpf k => 1 + potSek L ep c pa k
  | .frei L' k => if L' = L then 1 + k.freis.length else 1 + potSek L ep c pa k
  | .trav _ inv body ks k =>
      1 + ks.length * (kostenBlock ep c pa body + kostenExpr inv + 2) + potSek L ep c pa k
  | .travRest _ inv body ks k =>
      2 + ks.length * (kostenBlock ep c pa body + kostenExpr inv + 2) + potSek L ep c pa k
  | .verbrauch _ member edge inv _ mass body rest k =>
      1 + rest * (kostenBlock ep c pa body + kostenExpr member + kostenExpr edge +
        kostenExpr inv + kostenExpr mass + 2) + potSek L ep c pa k
  | .verbrauchRest _ member edge inv _ mass body rest _ k =>
      2 + rest * (kostenBlock ep c pa body + kostenExpr member + kostenExpr edge +
        kostenExpr inv + kostenExpr mass + 2) + potSek L ep c pa k
  | .wieder n bis body ueber k =>
      1 + n * (kostenBlock ep c pa body + kostenExpr bis + 2) + (2 + kostenExpr bis + kostenBlock ep c pa ueber) +
        potSek L ep c pa k
  | .wiederRest n bis body ueber k =>
      2 + n * (kostenBlock ep c pa body + kostenExpr bis + 2) + (2 + kostenExpr bis + kostenBlock ep c pa ueber) +
        potSek L ep c pa k
  | .ewig _ n inv body k =>
      1 + n * (kostenBlock ep c pa body + kostenExpr inv + 2) + potSek L ep c pa k
  | .ewigRest _ n inv body k =>
      2 + n * (kostenBlock ep c pa body + kostenExpr inv + 2) + potSek L ep c pa k
  | .wartet rest k => kostenBlock ep c pa rest + 1 + potSek L ep c pa k
  | .wartetSonst _ err rest k =>
      max (kostenSonst ep c pa err + 2 + potSek L ep c pa k) (kostenBlock ep c pa rest + 1 + potSek L ep c pa k)
  | .abbruch k => 1 + potSek L ep c pa k
  | .zurueckgekehrt _ => 0
  | .aufraeumen _ remaining => remaining.length
  | .leer => 1
  | .rueckBereit _ k => 1 + potSek L ep c pa k

/-- **The callees of a section**: `rufeR` up to the first `frei L`. -/
def rufeV (L : D.Lock) (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)} : GRest D V l Γ Λ → Bool
  | .ende e => rufeE Z ZS EW e
  | .dann b k => rufeB Z ZS EW b && rufeV L Z ZS EW k
  | .schrumpf k => rufeV L Z ZS EW k
  | .frei L' k => if L' = L then true else rufeV L Z ZS EW k
  | .trav _ _ body _ k => rufeB Z ZS EW body && rufeV L Z ZS EW k
  | .travRest _ _ body _ k => rufeB Z ZS EW body && rufeV L Z ZS EW k
  | .verbrauch _ _ _ _ _ _ body _ k => rufeB Z ZS EW body && rufeV L Z ZS EW k
  | .verbrauchRest _ _ _ _ _ _ body _ _ k => rufeB Z ZS EW body && rufeV L Z ZS EW k
  | .wieder _ _ body ueber k => rufeB Z ZS EW body && rufeB Z ZS EW ueber && rufeV L Z ZS EW k
  | .wiederRest _ _ body ueber k => rufeB Z ZS EW body && rufeB Z ZS EW ueber && rufeV L Z ZS EW k
  | .ewig _ _ _ body k => EW && rufeB Z ZS EW body && rufeV L Z ZS EW k
  | .ewigRest _ _ _ body k => EW && rufeB Z ZS EW body && rufeV L Z ZS EW k
  | .wartet rest k => rufeB Z ZS EW rest && rufeV L Z ZS EW k
  | .wartetSonst _ err rest k => rufeE Z ZS EW err && rufeB Z ZS EW rest && rufeV L Z ZS EW k
  | .abbruch k => rufeV L Z ZS EW k
  | .zurueckgekehrt _ => true
  | .aufraeumen _ _ => true
  | .leer => true
  | .rueckBereit _ k => rufeV L Z ZS EW k

section Lemmas

variable (L : D.Lock) (ep : Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}

/-- The section's own marker: the release and the markers behind it. -/
theorem potSek_frei_gleich {Λ : List (Res D)} (k : GRest D V l Γ Λ) :
    potSek L ep c pa (GRest.frei L k) = 1 + k.freis.length := by
  first
  | (show (if L = L then 1 + k.freis.length else 1 + potSek L ep c pa k) = _; exact if_pos rfl)
  | simp [potSek]

theorem rufeV_frei_gleich (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) {Λ : List (Res D)}
    (k : GRest D V l Γ Λ) : rufeV L Z ZS EW (GRest.frei L k) = true := by
  first
  | (show (if L = L then true else rufeV L Z ZS EW k) = true; exact if_pos rfl)
  | simp [rufeV]

/-- An own step lowers a positive potential: a residue that can step has `potSek` at least one. -/
theorem potSek_pos {Λ : List (Res D)} (r : GRest D V l Γ Λ)
    (h : r.arbeitsfaehig = true) : 1 ≤ potSek L ep c pa r := by
  cases r with
  | ende e => exact kostenEnd_pos ep c pa e
  | dann b k => have := kostenBlock_pos ep c pa b; simp only [potSek]; omega
  | frei L' k => simp only [potSek]; split <;> omega
  | wartet rest k => simp only [potSek]; omega
  | wartetSonst n err rest k => simp only [potSek]; omega
  | zurueckgekehrt a => cases h
  | aufraeumen a remaining =>
      cases remaining with
      | nil => cases h
      | cons K remaining => simp only [potSek, List.length_cons]; omega
  | _ => simp only [potSek]; omega

/-- Every pending marker has a unit of section potential. -/
theorem GRest.freis_budgetSek {Λ : List (Res D)} (r : GRest D V l Γ Λ) :
    r.freis.length ≤ potSek L ep c pa r := by
  induction r <;> simp only [GRest.freis, potSek, List.length_cons, List.length_nil] at *
  all_goals first | omega | (split <;> omega)

theorem GRest.scopedWert_budgetSek {Λ : List (Res D)} (r : GRest D V l Γ Λ)
    (e : ErgExpr D Γ Λ V.erg) (R : RueckRessourcen D V Λ)
    (hb : r.scopeBalance) (hr : r.scopedWert = some (e, R)) :
    scopedReturnSteps R.scopes ≤ potSek L ep c pa r := by
  have hlen := r.scopes_length R hb
  rcases GRest.scopedWert_faelle hr with rfl | ⟨rest, rfl⟩ | ⟨Λ', rest, k, rfl⟩
  · simp only [GRest.freis, List.length_nil] at hlen
    simp only [scopedReturnSteps, potSek, kostenEnd]
    omega
  · simp only [GRest.freis, List.length_nil] at hlen
    simp only [scopedReturnSteps, potSek, kostenEnd, kostenStmt]
    omega
  · have hk := k.freis_budgetSek L ep c pa
    simp only [GRest.freis] at hlen
    simp only [scopedReturnSteps, potSek, kostenBlock, kostenStmt]
    omega

theorem GRest.scopedGrund_budgetSek {Λ : List (Res D)} (r : GRest D V l Γ Λ)
    (grund : Fin V.gruende) (R : RueckRessourcen D V Λ)
    (hb : r.scopeBalance) (hr : r.scopedGrund = some (grund, R)) :
    scopedReturnSteps R.scopes ≤ potSek L ep c pa r := by
  have hlen := r.scopes_length R hb
  rcases GRest.scopedGrund_faelle hr with rfl | ⟨rest, rfl⟩ | ⟨Λ', rest, k, rfl⟩
  · simp only [GRest.freis, List.length_nil] at hlen
    simp only [scopedReturnSteps, potSek, kostenEnd]
    omega
  · simp only [GRest.freis, List.length_nil] at hlen
    simp only [scopedReturnSteps, potSek, kostenEnd, kostenStmt]
    omega
  · have hk := k.freis_budgetSek L ep c pa
    simp only [GRest.freis] at hlen
    simp only [scopedReturnSteps, potSek, kostenBlock, kostenStmt]
    omega

end Lemmas

/-- Both answer channels resume a suspended caller without increasing its section potential. -/
theorem antwortRestG_sek (L : D.Lock) {V : Vertrag D} (g : D.Fn)
    (a : ErgVal D (vertragVon D g).erg ⊕ Fin (vertragVon D g).gruende)
    (x y : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ)
    (ha : antwortRestG g a x = some y) (pa : Nat) (ep : Nat)
    (c : D.Fn → Nat) (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) :
    (rufeV L Z ZS EW x.2.2.2.2 = true → rufeV L Z ZS EW y.2.2.2.2 = true) ∧
      potSek L ep c pa y.2.2.2.2 ≤ potSek L ep c pa x.2.2.2.2 := by
  obtain ⟨l, Γ, Λ, ρ, r⟩ := x
  cases a with
  | inl v =>
      cases r with
      | wartet b k | wartetSonst _ _ b k =>
          simp only [antwortRestG] at ha
          split at ha
          · simp only [Option.some.injEq] at ha
            subst y
            simp only [rufeV, potSek, Bool.and_eq_true]
            exact ⟨by simp_all, by omega⟩
          · cases ha
      | _ =>
          simp only [antwortRestG, Option.some.injEq] at ha
          subst y
          exact ⟨id, Nat.le_refl _⟩
  | inr grund =>
      cases r with
      | wartetSonst n err b k =>
          simp only [antwortRestG] at ha
          split at ha
          · simp only [Option.some.injEq] at ha
            subst y
            simp only [rufeV, potSek, rufeB_alsBlock, kostenBlock_alsBlock, Bool.and_eq_true]
            exact ⟨fun h => ⟨h.1.1, h.2⟩, by omega⟩
          · cases ha
      | _ => simp only [antwortRestG, reduceCtorEq] at ha

/-- Delivery either completes a zero-potential root, or pops and resumes a caller. -/
theorem rufAntwortG_kostenSek (L : D.Lock) {z z' : RufFadenG D} {vor σ : World D}
    {a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende}
    (ha : rufAntwortG z vor σ a = some z') (pa : Nat) :
    (z'.stapel = z.stapel ∧ ∀ (ep : Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool)
      (ZS : Nat → Bool) (EW : Bool),
      rufeV L Z ZS EW z'.kopf.rest.2.2.2.2 = true ∧ potSek L ep c pa z'.kopf.rest.2.2.2.2 = 0) ∨
    (∃ (caller : RufRahmenG D) (rst : List (RufRahmenG D)),
      z.stapel = caller :: rst ∧ z'.stapel = rst ∧
      ∀ (ep : Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool),
        (rufeV L Z ZS EW caller.rest.2.2.2.2 = true →
          rufeV L Z ZS EW z'.kopf.rest.2.2.2.2 = true) ∧
        potSek L ep c pa z'.kopf.rest.2.2.2.2 ≤ potSek L ep c pa caller.rest.2.2.2.2) := by
  cases hst : z.stapel with
  | nil =>
      simp only [rufAntwortG, hst, Option.some.injEq] at ha
      subst z'
      exact Or.inl ⟨rfl, fun _ _ _ _ _ => ⟨rfl, rfl⟩⟩
  | cons caller rst =>
      obtain ⟨r, hr⟩ : ∃ r, antwortRestG z.kopf.f a caller.rest = some r := by
        cases hr : antwortRestG z.kopf.f a caller.rest with
        | none => simp [rufAntwortG, hst, hr] at ha
        | some r => exact ⟨r, rfl⟩
      simp [rufAntwortG, hst, hr] at ha
      subst z'
      exact Or.inr ⟨caller, rst, rfl, rfl,
        fun ep c Z ZS EW => antwortRestG_sek L _ _ _ _ hr pa ep c Z ZS EW⟩

end Gabbro.Grammatik
