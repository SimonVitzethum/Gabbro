/- Part 4 of `RahmenTreu` (C11 scoped-return release: release-aware frame
   transport; pure move out of `Teil1.lean` to keep every file under 500 lines). -/
module

public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}

/-- Release then release is the same combined release (scopes concatenate). -/
theorem TreuRet.transRet {W G} {a b c : World D} (h1 : TreuRet W G a b)
    (h2 : TreuRet W G b c) : TreuRet W G a c := by
  obtain ⟨Ls1, hLs1⟩ := h1.2
  obtain ⟨Ls2, hLs2⟩ := h2.2
  exact ⟨h1.1.trans h2.1, ⟨Ls1 ++ Ls2, by rw [hLs2, hLs1, List.foldl_append]⟩⟩

/-- A releasing frame pulls through a sub-block: non-returns keep the release,
    returns concatenate it. -/
theorem TreuAusgang.vorRet {W G} {σ σ1 : World D} {o : Ausgang V l Γ}
    (h1 : TreuRet W G σ σ1) (h : TreuAusgang W G σ1 o) : TreuAusgang W G σ o := by
  intro σ' hs
  cases o with
  | ok _ _ => exact h1.transGut (h _ hs)
  | zurueck _ _ => exact h1.transRet (h _ hs)
  | why _ _ => exact h1.transRet (h _ hs)
  | leave _ _ _ => exact h1.transGut (h _ hs)
  | next _ _ _ => exact h1.transGut (h _ hs)
  | logik _ => cases hs
  | hardware _ => cases hs

theorem TreuEnd.vorRet {W G} {σ σ1 : World D} {o : EndAusgang V l Γ}
    (h1 : TreuRet W G σ σ1) (h : TreuEnd W G σ1 o) : TreuEnd W G σ o := by
  intro σ' hs
  cases o with
  | zurueck _ _ => exact h1.transRet (h _ hs)
  | why _ _ => exact h1.transRet (h _ hs)
  | leave _ _ _ => exact h1.transGut (h _ hs)
  | next _ _ _ => exact h1.transGut (h _ hs)
  | logik _ => cases hs
  | hardware _ => cases hs

/-- Every handler outcome keeps the frame (both `Treu` and `TreuRet` carry `Rahmen`). -/
theorem TreuR.rahmen (hR : TreuR R) {f : D.Fn} {σ : World D} {ρ : Env D (D.params f)}
    {σ' : World D} (h : (R f σ ρ).welt = some σ') :
    Rahmen (D.schreibt f) (D.gschreibt f) σ σ' := by
  have h2 := hR f σ ρ σ' h
  cases he : R f σ ρ with
  | ok _ _ => rw [he] at h2; exact h2.1
  | why _ _ => rw [he] at h2; exact h2.1
  | logik _ => simp only [RufAusgang.welt, reduceCtorEq] at h
  | hardware _ => simp only [RufAusgang.welt, reduceCtorEq] at h

/-- Joint frame for the two exits of an indirect else-call («C07»): the pointer is
    evaluated once in the recorded world `s0`, the actual conforming function runs
    under its transported caller duty, and both continuations see the transported
    value (`runOk`) or reason (`runWhy`). A propagated reason may release the
    callee's scopes (`TreuRet`); the release pulls through the continuation
    (`TreuAusgang.vorRet`). The three `*_treu` cases instantiate it
    with their runners; the branch inventories stay shared, never rolled back. -/
theorem indSonst_treu (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (hR : TreuR R)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat} {τ : Ty}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ) (hr : 0 < (D.sigNr n).gruende)
    (σ s0 : World D) (ρ : Env D Γ)
    (hl : Treu V.schreibt V.gschreibt σ s0)
    (ok : World D → Wert D τ → Ausgang V l Γ)
    (why : World D → Fin (D.sigNr n).gruende → Ausgang V l Γ)
    (runOk : ∀ σ1 v, TreuAusgang V.schreibt V.gschreibt σ1 (ok σ1 v))
    (runWhy : ∀ σ1 r, TreuAusgang V.schreibt V.gschreibt σ1 (why σ1 r))
    (σ' : World D) (h : (indSonst R p args he hr s0 ρ ok why).welt = some σ') :
    match (indSonst R p args he hr s0 ρ ok why) with
    | .zurueck _ _ => TreuRet V.schreibt V.gschreibt σ σ'
    | .why _ _ => TreuRet V.schreibt V.gschreibt σ σ'
    | _ => Treu V.schreibt V.gschreibt σ σ' := by
  simp only [indSonst] at h ⊢
  generalize hpv : eval s0 p s0 ρ = pv at h ⊢
  obtain ⟨f, hf⟩ := pv
  simp only at h ⊢
  split at h ⊢
  · rename_i σ1 v hR1
    replace hp := RufPasst.vonPasst (D.passt_sig hf) hp
    have h2 := hR f s0 (umsig hf (evalArgs s0 args s0 ρ)) σ1 (by rw [hR1]; rfl)
    rw [hR1] at h2
    have g1 := hl.trans (Treu.weiter hp.hw hp.hg h2)
    exact (TreuAusgang.vor g1 (runOk σ1 (ergWert (ergSig hf he) v))) σ' h
  · rename_i σ1 r hR1
    replace hp := RufPasst.vonPasst (D.passt_sig hf) hp
    have h2 := hR f s0 (umsig hf (evalArgs s0 args s0 ρ)) σ1 (by rw [hR1]; rfl)
    rw [hR1] at h2
    have g1 := hl.transRet (h2.weiter hp.hw hp.hg)
    exact (TreuAusgang.vorRet g1 (runWhy σ1 (grundSig hf r))) σ' h
  · simp only [Ausgang.welt, reduceCtorEq] at h
  · simp only [Ausgang.welt, reduceCtorEq] at h

/-- Joint frame for the two exits of an indirect else-call at the end of a body («C07»):
    the `TreuEnd` variant of `indSonst_treu`, for the `end_treu` case. -/
theorem indSonstE_treu (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (hR : TreuR R)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat} {τ : Ty}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ) (hr : 0 < (D.sigNr n).gruende)
    (σ s0 : World D) (ρ : Env D Γ)
    (hl : Treu V.schreibt V.gschreibt σ s0)
    (ok : World D → Wert D τ → EndAusgang V l Γ)
    (why : World D → Fin (D.sigNr n).gruende → EndAusgang V l Γ)
    (runOk : ∀ σ1 v, TreuEnd V.schreibt V.gschreibt σ1 (ok σ1 v))
    (runWhy : ∀ σ1 r, TreuEnd V.schreibt V.gschreibt σ1 (why σ1 r))
    (σ' : World D) (h : (indSonstE R p args he hr s0 ρ ok why).welt = some σ') :
    match (indSonstE R p args he hr s0 ρ ok why) with
    | .zurueck _ _ => TreuRet V.schreibt V.gschreibt σ σ'
    | .why _ _ => TreuRet V.schreibt V.gschreibt σ σ'
    | _ => Treu V.schreibt V.gschreibt σ σ' := by
  simp only [indSonstE] at h ⊢
  generalize hpv : eval s0 p s0 ρ = pv at h ⊢
  obtain ⟨f, hf⟩ := pv
  simp only at h ⊢
  split at h ⊢
  · rename_i σ1 v hR1
    replace hp := RufPasst.vonPasst (D.passt_sig hf) hp
    have h2 := hR f s0 (umsig hf (evalArgs s0 args s0 ρ)) σ1 (by rw [hR1]; rfl)
    rw [hR1] at h2
    have g1 := hl.trans (Treu.weiter hp.hw hp.hg h2)
    exact (TreuEnd.vor g1 (runOk σ1 (ergWert (ergSig hf he) v))) σ' h
  · rename_i σ1 r hR1
    replace hp := RufPasst.vonPasst (D.passt_sig hf) hp
    have h2 := hR f s0 (umsig hf (evalArgs s0 args s0 ρ)) σ1 (by rw [hR1]; rfl)
    rw [hR1] at h2
    have g1 := hl.transRet (h2.weiter hp.hw hp.hg)
    exact (TreuEnd.vorRet g1 (runWhy σ1 (grundSig hf r))) σ' h
  · simp only [EndAusgang.welt, reduceCtorEq] at h
  · simp only [EndAusgang.welt, reduceCtorEq] at h

end Gabbro.Grammatik
