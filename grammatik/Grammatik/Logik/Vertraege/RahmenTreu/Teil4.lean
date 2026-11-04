/- Part 4 of `RahmenTreu` (C11 scoped-return release: release-aware frame
    transport; pure move out of `Teil1.lean` to keep every file under 500 lines). -/
module

public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}
variable {returnGuard : Prop}

/-- Release then release is the same combined release (scopes concatenate;
    spare and rank persist over the union). -/
theorem TreuRet.transRet {W G} {haelt : List D.Lock} {boden : Option Int}
    {a b c : World D} (h1 : TreuRet W G haelt boden a b)
    (h2 : TreuRet W G haelt boden b c) : TreuRet W G haelt boden a c := by
  obtain ⟨hr1, Ls1, heq1, hsp1, hrk1⟩ := h1
  obtain ⟨hr2, Ls2, heq2, hsp2, hrk2⟩ := h2
  refine ⟨hr1.trans hr2, Ls1 ++ Ls2, ?_, ?_, ?_⟩
  · rw [heq2, heq1, List.foldl_append]
  · intro L hL
    simp only [List.mem_append] at hL
    rcases hL with hL | hL
    · exact hsp1 L hL
    · exact hsp2 L hL
  · intro L hL c hc
    simp only [List.mem_append] at hL
    rcases hL with hL | hL
    · exact hrk1 L hL c hc
    · exact hrk2 L hL c hc

/-- Every handler outcome keeps the frame (both `Treu` and `TreuRet` carry `Rahmen`). -/
theorem TreuR.rahmen (hR : TreuR R) {f : D.Fn} {σ : World D} {ρ : Env D (D.params f)}
    (hh : HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) σ.haelt)
    {σ' : World D} (h : (R f σ ρ).welt = some σ') :
    Rahmen (D.schreibt f) (D.gschreibt f) σ σ' := by
  have h2 := hR f σ ρ hh σ' h
  cases he : R f σ ρ with
  | ok _ _ => rw [he] at h2; exact h2.1
  | why _ _ => rw [he] at h2; exact h2.1
  | logik _ => simp only [he, RufAusgang.welt, reduceCtorEq] at h
  | hardware _ => simp only [he, RufAusgang.welt, reduceCtorEq] at h

/-- Joint frame for the two exits of an indirect else-call («C07»): the pointer is
    evaluated once in the recorded world `s0`, the actual conforming function runs
    under its transported caller duty, and both continuations see the transported
    value (`runOk`) or reason (`runWhy`) under the transported caller discipline
    (`HeldB` over the caller's `nachSig` residual, derived from the restored
    frame). The ok exit of the callee is `Treu` (held equality, from `TreuR`
    under the transported entry discipline); a propagated reason is collapsed
    back to `Treu` (`TreuRet.toTreu_entry`) before the continuation runs
    (`TreuAusgang.vorCall`). The conclusion is outcome-aware (`TreuRet` at
    `.zurueck`/`.why`, `Treu` elsewhere). -/
theorem indSonst_treu (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (hR : TreuR R)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat} {τ : Ty}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ) (hr : 0 < (D.sigNr n).gruende)
    (σ s0 : World D) (ρ : Env D Γ)
    (hl : Treu V.schreibt V.gschreibt σ s0)
    (bo : Option Int) (hbV : BodenUnter bo V.boden) (hh : HeldB bo Λ σ.haelt)
    (ok : World D → Wert D τ → Ausgang V l Γ)
    (why : World D → Fin (D.sigNr n).gruende → Ausgang V l Γ)
    (runOk : ∀ σ1 v, HeldB bo (nachSig D (D.sigNr n) Λ) σ1.haelt →
      TreuAusgang V.schreibt V.gschreibt σ1 (ok σ1 v) returnGuard)
    (runWhy : ∀ σ1 r, HeldB bo (nachSig D (D.sigNr n) Λ) σ1.haelt →
      TreuAusgang V.schreibt V.gschreibt σ1 (why σ1 r) returnGuard)
    (σ' : World D) (h : (indSonst R p args he hr s0 ρ ok why).welt = some σ') :
    match (indSonst R p args he hr s0 ρ ok why) with
    | .zurueck _ _ => returnGuard → TreuRet V.schreibt V.gschreibt V.haelt V.boden σ σ'
    | .why _ _ => returnGuard → TreuRet V.schreibt V.gschreibt V.haelt V.boden σ σ'
    | _ => Treu V.schreibt V.gschreibt σ σ' := by
  simp only [indSonst] at h ⊢
  generalize hpv : eval s0 p s0 ρ = pv at h ⊢
  obtain ⟨f, hf⟩ := pv
  simp only at h ⊢
  replace hp := RufPasst.vonPasst (D.passt_sig hf) hp
  have hentry : HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) s0.haelt :=
    heldB_ruf hp hbV (hl.heldB hh)
  generalize hR1 : R f s0 (umsig hf (evalArgs s0 args s0 ρ)) = rv at h ⊢
  cases rv with
  | ok σ1 v =>
      have h2 := hR f s0 _ hentry σ1 (by rw [hR1]; rfl)
      rw [hR1] at h2
      have g1 := hl.trans (Treu.weiter hp.hw hp.hg h2)
      exact (TreuAusgang.vorCall g1 (runOk σ1 (ergWert (ergSig hf he) v)
        (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh)))) σ' h
  | why σ1 r =>
      have h2 := hR f s0 _ hentry σ1 (by rw [hR1]; rfl)
      rw [hR1] at h2
      have gcall : Treu V.schreibt V.gschreibt s0 σ1 :=
        (TreuRet.weiter hp.hw hp.hg h2).toTreu_entry hentry
      have g1 := hl.trans gcall
      exact (TreuAusgang.vorCall g1 (runWhy σ1 (grundSig hf r)
        (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh)))) σ' h
  | logik _ => simp only [Ausgang.welt, reduceCtorEq] at h
  | hardware _ => simp only [Ausgang.welt, reduceCtorEq] at h

/-- Joint frame for the two exits of an indirect else-call at the end of a body («C07»):
    the `TreuEnd` variant of `indSonst_treu`, for the `end_treu` case. -/
theorem indSonstE_treu (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (hR : TreuR R)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat} {τ : Ty}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ) (hr : 0 < (D.sigNr n).gruende)
    (σ s0 : World D) (ρ : Env D Γ)
    (hl : Treu V.schreibt V.gschreibt σ s0)
    (bo : Option Int) (hbV : BodenUnter bo V.boden) (hh : HeldB bo Λ σ.haelt)
    (ok : World D → Wert D τ → EndAusgang V l Γ)
    (why : World D → Fin (D.sigNr n).gruende → EndAusgang V l Γ)
    (runOk : ∀ σ1 v, HeldB bo (nachSig D (D.sigNr n) Λ) σ1.haelt →
      TreuEnd V.schreibt V.gschreibt σ1 (ok σ1 v) returnGuard)
    (runWhy : ∀ σ1 r, HeldB bo (nachSig D (D.sigNr n) Λ) σ1.haelt →
      TreuEnd V.schreibt V.gschreibt σ1 (why σ1 r) returnGuard)
    (σ' : World D) (h : (indSonstE R p args he hr s0 ρ ok why).welt = some σ') :
    match (indSonstE R p args he hr s0 ρ ok why) with
    | .zurueck _ _ => returnGuard → TreuRet V.schreibt V.gschreibt V.haelt V.boden σ σ'
    | .why _ _ => returnGuard → TreuRet V.schreibt V.gschreibt V.haelt V.boden σ σ'
    | _ => Treu V.schreibt V.gschreibt σ σ' := by
  simp only [indSonstE] at h ⊢
  generalize hpv : eval s0 p s0 ρ = pv at h ⊢
  obtain ⟨f, hf⟩ := pv
  simp only at h ⊢
  replace hp := RufPasst.vonPasst (D.passt_sig hf) hp
  have hentry : HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) s0.haelt :=
    heldB_ruf hp hbV (hl.heldB hh)
  generalize hR1 : R f s0 (umsig hf (evalArgs s0 args s0 ρ)) = rv at h ⊢
  cases rv with
  | ok σ1 v =>
      have h2 := hR f s0 _ hentry σ1 (by rw [hR1]; rfl)
      rw [hR1] at h2
      have g1 := hl.trans (Treu.weiter hp.hw hp.hg h2)
      exact (TreuEnd.vorCall g1 (runOk σ1 (ergWert (ergSig hf he) v)
        (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh)))) σ' h
  | why σ1 r =>
      have h2 := hR f s0 _ hentry σ1 (by rw [hR1]; rfl)
      rw [hR1] at h2
      have gcall : Treu V.schreibt V.gschreibt s0 σ1 :=
        (TreuRet.weiter hp.hw hp.hg h2).toTreu_entry hentry
      have g1 := hl.trans gcall
      exact (TreuEnd.vorCall g1 (runWhy σ1 (grundSig hf r)
        (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh)))) σ' h
  | logik _ => simp only [EndAusgang.welt, reduceCtorEq] at h
  | hardware _ => simp only [EndAusgang.welt, reduceCtorEq] at h

end Gabbro.Grammatik
