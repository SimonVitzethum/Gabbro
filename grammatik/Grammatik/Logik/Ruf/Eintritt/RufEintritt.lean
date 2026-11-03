/-
  File:      Grammatik/RufEintritt.lean
  Subject:   **THE ENTRY-GATED HANDLER** -- the bridge between the user's
              obligation (quantified over `RespektiertRahmen` handlers) and
              the model's own call `rufAt`.

  WHY IT EXISTS. Part 4 (`RufLogika.lean`) applies the user obligation to a
  patched `rufAt` (`rufFrei`: every `logik` answer replaced by the hardware
  default). The obligation needs `RespektiertRahmen`, but the patched handler
  is not in it: at an entry world that fails the callee-entry discipline
  `HeldB`, an `ok` answer of `rufAt` need not keep the frame (a scoped return
  may unwind scopes; collapsing the release needs the discipline --
  `TreuRet.toTreu_entry`). The unconditional frame was the gap; the strongest
  honest close keeps the discipline as a premise everywhere and gates the
  handler by it:

  * `rufEintritt` answers like `rufFrei` at disciplined entries and
    `.hardware .ieee` elsewhere (the `rufAusL` idiom from
    `ZielOrtGanz.lean`: a hardware default is neither `ok` -- so no frame or
    contract duty attaches -- nor `logik`);
  * it IS in `RespektiertRahmen` (and in `OhneVorbedingung`, `OhneLogik`),
    so the obligation applies to it;
  * it AGREES with `rufFrei` wherever the discipline holds, so body runs
    from disciplined entries coincide (`RufGleich*.lean`).

  `treuR_rufFrei` (the patched handler is `TreuR`) and `treuR_torRuf`
  (gating preserves `TreuR`) are the frame facts the joint induction runs on.
-/
module
public import Grammatik.Logik.Ruf.RufLogik
public import Grammatik.Logik.Vertraege.RahmenTreu
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **The frame half of `RespektiertRahmen`, for a handler**: an `ok` answer
    keeps the callee's declared frame and gives back every lock it took, at
    every world meeting the callee-entry discipline. `rufAt_gut` (`Satz.lean`)
    gives it only at worlds meeting `HeldB`; `rufAt_treu` (`RahmenTreu.lean`)
    gives it wherever the entry discipline holds -- collapsing the callee's
    release needs it, and an arbitrary world does not meet it. -/
def RufRahmenTreu (P : Programm D)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) (σ' : World D) (v : ErgVal D (D.erg f)),
    HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) σ.haelt →
    R f σ ρ = RufAusgang.ok σ' v →
      Rahmen (D.schreibt f) (D.gschreibt f) σ σ' ∧ offen σ'.spur = offen σ.spur

/-- **The patched handler is frame-faithful.** `rufFrei` answers `rufAt`'s
    answers except that `logik` becomes the hardware default; at a
    disciplined entry the `ok`/`why` answers satisfy `Treu`/`TreuRet`
    (`rufAt_treu`) and the default answers satisfy `True`. -/
theorem treuR_rufFrei (P : Programm D) (O : Orakel D) (passes : Nat) (hO : TreuO O)
    (hS : ScopesOkProg P) (n : Nat) : TreuR (rufFrei P O passes n) := by
  intro f σ ρ hh σ' h
  have hT := rufAt_treu P O passes hO hS n f σ ρ hh
  unfold rufFrei at h ⊢
  cases hx : rufAt P O passes n f σ ρ with
  | ok σ₂ v =>
      simp only [hx, RufAusgang.welt, Option.some.injEq] at h ⊢
      subst h
      have ht := hT σ₂ (by rw [hx]; rfl)
      rw [hx] at ht
      exact ht
  | why σ₁ r =>
      simp only [hx, RufAusgang.welt, Option.some.injEq] at h ⊢
      subst h
      have ht := hT σ₁ (by rw [hx]; rfl)
      rw [hx] at ht
      exact ht
  | logik e =>
      simp only [hx, RufAusgang.welt, reduceCtorEq] at h
  | hardware e =>
      exact True.intro

/-- **Gating by the entry contract preserves `TreuR`.** `torRuf` answers the
    handler's answer where the entry contract holds and a `logik` mark
    elsewhere; both satisfy the `TreuR` match (`logik` gives `True`). -/
theorem treuR_torRuf (P : Programm D)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (hR : TreuR R) :
    TreuR (torRuf P R) := by
  intro f σ ρ hh σ' h
  unfold torRuf at h ⊢
  by_cases hq : wahr? (eval σ (P.requires f) σ ρ) = true
  · rw [if_pos hq] at h ⊢
    exact hR f σ ρ hh σ' h
  · rw [if_neg hq] at h ⊢
    simp only [RufAusgang.welt, reduceCtorEq] at h

/-- **The entry-gated handler.** Like `rufFrei` at entries meeting the
    callee-entry discipline, the hardware default elsewhere. -/
noncomputable def rufEintritt (P : Programm D) (O : Orakel D) (passes n : Nat) :
    ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f :=
  fun g σ ρ =>
    haveI := Classical.propDecidable
      (HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g)) σ.haelt)
    if _ : HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g)) σ.haelt
    then rufFrei P O passes n g σ ρ
    else .hardware .ieee

/-- At a disciplined entry the gated handler IS the patched handler. -/
theorem eintritt_agree (P : Programm D) (O : Orakel D) (passes n : Nat)
    (g : D.Fn) (σ : World D) (ρ : Env D (D.params g))
    (hh : HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g)) σ.haelt) :
    rufEintritt P O passes n g σ ρ = rufFrei P O passes n g σ ρ := by
  simp only [rufEintritt, dif_pos hh]

/-- Gating by the entry contract keeps the agreement. -/
theorem eintritt_agree_tor (P : Programm D) (O : Orakel D) (passes n : Nat)
    (g : D.Fn) (σ : World D) (ρ : Env D (D.params g))
    (hh : HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g)) σ.haelt) :
    torRuf P (rufEintritt P O passes n) g σ ρ =
      torRuf P (rufFrei P O passes n) g σ ρ := by
  unfold torRuf
  by_cases hq : wahr? (eval σ (P.requires g) σ ρ) = true
  · rw [if_pos hq, if_pos hq, eintritt_agree P O passes n g σ ρ hh]
  · rw [if_neg hq, if_neg hq]

/-- The gated handler answers no `logik` outcome. -/
theorem eintritt_ohneLogik (P : Programm D) (O : Orakel D) (passes n : Nat) :
    OhneLogik (rufEintritt P O passes n) := by
  intro g σ ρ e h
  by_cases hh : HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g)) σ.haelt
  · simp only [rufEintritt, dif_pos hh] at h
    exact absurd h (rufFrei_ohneLogik P O passes n g σ ρ e)
  · simp only [rufEintritt, dif_neg hh] at h
    cases h

/-- The gated handler answers no `vorbedingung` outcome. -/
theorem eintritt_ohneVorbedingung (P : Programm D) (O : Orakel D) (passes n : Nat) :
    OhneVorbedingung (rufEintritt P O passes n) := by
  intro g σ ρ e h
  exact absurd h (eintritt_ohneLogik P O passes n g σ ρ e)

/-- The gated handler respects the contracts at their place: its `ok`
    answers are `rufAt`'s `ok` answers at disciplined entries. -/
theorem eintritt_vertrag (P : Programm D) (O : Orakel D) (passes n : Nat) :
    RespektiertVertraege P (rufEintritt P O passes n) := by
  intro f σ ρ hreq σ' v h
  by_cases hh : HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) σ.haelt
  · simp only [rufEintritt, dif_pos hh] at h
    exact rufAt_vertraege P O passes n f σ ρ hreq σ' v
      (rufFrei_ok P O passes n f σ ρ σ' v h)
  · simp only [rufEintritt, dif_neg hh] at h
    cases h

/-- The gated handler keeps the frame: at disciplined entries by
    `rufAt_treu`, elsewhere it has no `ok` answer. -/
theorem eintritt_rahmen (P : Programm D) (O : Orakel D) (passes : Nat) (hO : TreuO O)
    (hS : ScopesOkProg P) (n : Nat) : RufRahmenTreu P (rufEintritt P O passes n) := by
  intro f σ ρ σ' v hh h
  simp only [rufEintritt, dif_pos hh] at h
  have hout := rufFrei_ok P O passes n f σ ρ σ' v h
  have ht := rufAt_treu P O passes hO hS n f σ ρ hh σ' (by rw [hout]; rfl)
  rw [hout] at ht
  exact ⟨ht.1, ht.2⟩

/-- **The gated handler is in the obligation's class.** Contracts
    (`eintritt_vertrag`) and frames at every world -- at undisciplined
    entries there is no `ok` answer to constrain. -/
theorem eintritt_respektiert (P : Programm D) (O : Orakel D) (passes : Nat)
    (hO : TreuO O) (hS : ScopesOkProg P) (n : Nat) :
    RespektiertRahmen P (rufEintritt P O passes n) := by
  refine ⟨eintritt_vertrag P O passes n, fun f σ ρ σ' v h => ?_⟩
  by_cases hh : HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) σ.haelt
  · exact eintritt_rahmen P O passes hO hS n f σ ρ σ' v hh
      (by simpa only [rufEintritt, dif_pos hh] using h)
  · simp only [rufEintritt, dif_neg hh] at h
    cases h

/-- **The gated handler is frame-faithful.** At disciplined entries it is
    the patched handler (`treuR_rufFrei`); elsewhere it answers the hardware
    default, which satisfies the `TreuR` match. -/
theorem treuR_eintritt (P : Programm D) (O : Orakel D) (passes : Nat) (hO : TreuO O)
    (hS : ScopesOkProg P) (n : Nat) : TreuR (rufEintritt P O passes n) := by
  intro f σ ρ hh σ' h
  by_cases hd : HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) σ.haelt
  · simp only [rufEintritt, dif_pos hd] at h ⊢
    exact treuR_rufFrei P O passes hO hS n f σ ρ hd σ' h
  · simp only [rufEintritt, dif_neg hd] at h ⊢

#print axioms Gabbro.Grammatik.treuR_rufFrei
#print axioms Gabbro.Grammatik.treuR_torRuf
#print axioms Gabbro.Grammatik.eintritt_respektiert
#print axioms Gabbro.Grammatik.treuR_eintritt

end Gabbro.Grammatik
