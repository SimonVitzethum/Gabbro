module

public import Grammatik.Logik.Fortschritt.KostenG.T1.Teil2
public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.ScopeBalanceReplay

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Every pending lexical marker contributes at least one unit. Completed
    residues contribute zero, and cleanup contains exactly its pending units. -/
theorem GRest.freis_budget (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ) :
    r.freis.length ≤ potRest c pa r := by
  induction r <;> simp only [GRest.freis, potRest, List.length_cons, List.length_nil] at *
  all_goals omega

/-- Evaluation plus one step per scope. The last release delivers the answer. -/
def scopedReturnSteps (scopes : List D.Lock) : Nat := 1 + scopes.length

/-- The source return pays for evaluation, and its skipped continuation
    already pays for the releases. No source cost changes. -/
theorem GRest.scopedWert_budget (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ)
    (e : ErgExpr D Γ Λ V.erg) (R : RueckRessourcen D V Λ)
    (hb : r.scopeBalance) (hr : r.scopedWert = some (e, R)) :
    scopedReturnSteps R.scopes ≤ potRest c pa r := by
  have hlen := r.scopes_length R hb
  rcases GRest.scopedWert_faelle hr with rfl | ⟨rest, rfl⟩ | ⟨Λ', rest, k, rfl⟩
  · simp only [GRest.freis, List.length_nil] at hlen
    simp only [scopedReturnSteps, potRest, kostenEnd]
    omega
  · simp only [GRest.freis, List.length_nil] at hlen
    simp only [scopedReturnSteps, potRest, kostenEnd, kostenStmt]
    omega
  · have hk := k.freis_budget c pa
    simp only [GRest.freis] at hlen
    simp only [scopedReturnSteps, potRest, kostenBlock, kostenStmt]
    omega

theorem GRest.scopedGrund_budget (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ)
    (grund : Fin V.gruende) (R : RueckRessourcen D V Λ)
    (hb : r.scopeBalance) (hr : r.scopedGrund = some (grund, R)) :
    scopedReturnSteps R.scopes ≤ potRest c pa r := by
  have hlen := r.scopes_length R hb
  rcases GRest.scopedGrund_faelle hr with rfl | ⟨rest, rfl⟩ | ⟨Λ', rest, k, rfl⟩
  · simp only [GRest.freis, List.length_nil] at hlen
    simp only [scopedReturnSteps, potRest, kostenEnd]
    omega
  · simp only [GRest.freis, List.length_nil] at hlen
    simp only [scopedReturnSteps, potRest, kostenEnd, kostenStmt]
    omega
  · have hk := k.freis_budget c pa
    simp only [GRest.freis] at hlen
    simp only [scopedReturnSteps, potRest, kostenBlock, kostenStmt]
    omega

/-- The own-step test on a whole sigma residue (a non-dependent argument, so that the head
    equation of a rule can rewrite it). -/
private def RestArb {V : Vertrag D}
    (x : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ) : Bool :=
  x.2.2.2.2.arbeitsfaehig

/-- A rule can fire only at a residue with positive own-step potential. -/
theorem rufSchrittG_arbeitsfaehig {P : Programm D} {O : Orakel D} {pa : Nat}
    {M M' : RufMaschineG D} {t : Faden} (hs : RufSchrittG P O pa M t M') :
    (M.faeden t).kopf.rest.2.2.2.2.arbeitsfaehig = true := by
  cases hs with
  | g7 hs =>
      cases hs with
      | rueckScopedWert ρ r e R hhead hret
      | rueckScopedWertDirekt ρ r e R hhead hret =>
          rw [hhead]
          rcases GRest.scopedWert_faelle hret with rfl | ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
      | rueckScopedGrund ρ r grund R hhead hret
      | rueckScopedGrundDirekt ρ r grund R hhead hret =>
          rw [hhead]
          rcases GRest.scopedGrund_faelle hret with rfl | ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
      | _ =>
          show RestArb (M.faeden t).kopf.rest = true
          rw [‹(M.faeden t).kopf.rest = _›]
          rfl
  | g1 hs | g2 hs | g3 hs | g4 hs | g5 hs | g6 hs =>
      cases hs <;>
        (show RestArb (M.faeden t).kopf.rest = true
         rw [‹(M.faeden t).kopf.rest = _›]
         rfl)

end Gabbro.Grammatik
