module
public import Grammatik.Logik.Ruf.RufLogik
public import Grammatik.Logik.Ruf.Eintritt.RufEintritt
public import Grammatik.Logik.Ruf.Eintritt.RufGleichStmt
public import Grammatik.Logik.Vertraege.HandlerKongruenz.Teil6
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 4. The three congruence instances, over disciplined entries -/

/-- The error set of step 1: a `logik` mark. -/
def LogikMarke (m : Fehlermarke D) : Prop := ∃ e : Logik D, m = .logik e

/-- The error set of step 2: a `vorbedingung` mark. -/
def VorbedMarke (m : Fehlermarke D) : Prop := ∃ g : D.Fn, m = .logik (.vorbedingung g)

/-- **Step 1**: `rufAt` differs from the patched handler only where it
    answers a `logik`. -/
theorem kong_rufAt_rufFrei (P : Programm D) (O : Orakel D) (passes n : Nat) :
    HandlerUnter LogikMarke (rufAt P O passes n) (rufFrei P O passes n) := by
  intro g σ ρ
  unfold rufFrei
  cases hx : rufAt P O passes n g σ ρ with
  | ok σ' v => exact Or.inl rfl
  | why σ' r => exact Or.inl rfl
  | logik e => exact Or.inr ⟨.logik e, rfl, ⟨e, rfl⟩⟩
  | hardware e => exact Or.inl rfl

/-- **Step 2, for any handler**: the gated handler differs from the bare one
    only where the callee's `requires` fails, and there it answers a
    `vorbedingung`. The inner handler is irrelevant -- only the gate. -/
theorem kong_torRuf (P : Programm D)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) :
    HandlerUnter VorbedMarke (torRuf P R) R := by
  intro g σ ρ
  unfold torRuf
  by_cases hq : wahr? (eval σ (P.requires g) σ ρ) = true
  · rw [if_pos hq]; exact Or.inl rfl
  · rw [if_neg hq]; exact Or.inr ⟨.logik (.vorbedingung g), rfl, ⟨g, rfl⟩⟩

/-- **The statement the depth induction carries**: at an entry that meets
    the callee's `requires` AND the callee-entry discipline, the only
    `logik` outcome of `rufAt` is an `abstieg`. The discipline premise is
    load-bearing, not a technicality: an `ok` answer at an undisciplined
    entry need not keep the frame (a scoped return may unwind scopes), so
    the frame half of the handler class -- and with it the whole discharge
    -- is only available at disciplined entries. -/
def NurAbstieg (P : Programm D) (O : Orakel D) (passes n : Nat) : Prop :=
  ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)) (e : Logik D),
    HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g)) σ.haelt →
    ReqAmEintritt P g σ ρ → rufAt P O passes n g σ ρ = .logik e → ∃ h : D.Fn, e = .abstieg h

/-- **Step 3, gated by the entry discipline**: under the induction
    hypothesis, `rufAt` differs from the gated patched handler only where
    it answers an `abstieg` -- at entries meeting the discipline. At
    undisciplined entries `rufAt` may answer a non-`abstieg` `logik` with
    no frame to constrain it, so the congruence is only stated where the
    discipline holds. -/
theorem kong_rufAt_torRuf_diszipliniert (P : Programm D) (O : Orakel D) (passes n : Nat)
    (ih : NurAbstieg P O passes n) :
    HandlerUnterDisz AbstiegMarke (rufAt P O passes n) (torRuf P (rufFrei P O passes n)) := by
  intro g σ ρ hh
  unfold torRuf rufFrei
  by_cases hq : wahr? (eval σ (P.requires g) σ ρ) = true
  · rw [if_pos hq]
    cases hx : rufAt P O passes n g σ ρ with
    | ok σ' v => exact Or.inl rfl
    | why σ' r => exact Or.inl rfl
    | hardware e => exact Or.inl rfl
    | logik e =>
        obtain ⟨h, rfl⟩ := ih g σ ρ e hh (by simpa [ReqAmEintritt] using hq) hx
        exact Or.inr ⟨.logik (.abstieg h), rfl, ⟨h, rfl⟩⟩
  · rw [if_neg hq]
    cases n with
    | zero => exact Or.inr ⟨.logik (.abstieg g), rfl, ⟨g, rfl⟩⟩
    | succ m =>
        exact Or.inl (rufAt_vorbed P O passes m g σ ρ (by simpa [ReqAmEintritt] using hq))

/-- **The congruence at the call level, gated by the entry discipline.**
    Mirror of `rufSchritt_kongruent`: one unfolding of `rufAt` under two
    gatedly-related handlers gives calls that agree or fail early with a
    first-side mark. -/
theorem rufSchritt_unter (P : Programm D) (O : Orakel D) (passes : Nat)
    (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (hR : HandlerUnterDisz AbstiegMarke R₁ R₂)
    (hT₁ : TreuR R₁) (hO : TreuO O) (hS : ScopesOkProg P)
    (g : D.Fn) (σ : World D) (ρ : Env D (D.params g))
    (hh : HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g)) σ.haelt) :
    RufUnter AbstiegMarke (rufSchritt P O passes R₁ g σ ρ) (rufSchritt P O passes R₂ g σ ρ) := by
  have g0 : Treu (D.schreibt g) (D.gschreibt g) σ
      (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) :=
    treu_lese _ _ _
  have hcong := end_unter (V := vertragVon D g) O passes R₁ R₂ hR hT₁ hO
    (D.signatur g).boden (bodenUnter_refl _) (P.rumpf g)
    (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ
    (hS g) (g0.heldB hh)
  simp only [rufSchritt]
  by_cases hq : wahr? (eval (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte)
      (P.requires g) (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ) = false
  · rw [if_pos hq, if_pos hq]; exact Or.inl rfl
  · rw [if_neg hq, if_neg hq]
    rcases hcong with h | ⟨mk, h1, hE⟩
    · rw [h]
      cases hx : execEnd (V := vertragVon D g) O passes R₂ (P.rumpf g)
          (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ with
      | zurueck σ' v => exact Or.inl rfl
      | why σ' r => exact Or.inl rfl
      | leave hl σ' ρ' => exact Or.inl rfl
      | next hl σ' ρ' => exact Or.inl rfl
      | logik e => exact Or.inl rfl
      | hardware e => exact Or.inl rfl
    · exact Or.inr ⟨mk, by rw [h1]; cases mk <;> rfl, hE⟩

/-! ## 5. THE DISCHARGE -/

/-- **THE FRAME HALF OF `RespektiertRahmen` FOR `rufAt`, AT EVERY DISCIPLINED
    WORLD -- PROVED** (`rufAt_treu`, RahmenTreu.lean). The premises are the
    hardware's (an axiom keeps the frame of its declared `effects` and leaves
    the held locks alone: `TreuO`, the first two conjuncts of `GutO` -- that
    is H1 and it is named, not hidden), the static scope discipline
    (`ScopesOkProg`: every scoped return spares the residual and respects
    the floor) and the entry discipline (`HeldB`). Together with
    `rufAt_vertraege` this puts `rufAt` into `RespektiertRahmen` wherever
    the caller's duty and the entry discipline hold. -/
theorem rufAt_rahmenTreu (P : Programm D) (O : Orakel D) (passes : Nat) (hO : TreuO O)
    (hS : ScopesOkProg P) :
    ∀ n : Nat, RufRahmenTreu P (rufAt P O passes n) := by
  intro n f σ ρ σ' v hh h
  have hT := rufAt_treu P O passes hO hS n f σ ρ hh σ' (by rw [h]; rfl)
  rw [h] at hT
  exact ⟨hT.1, hT.2⟩

section Entladung

variable (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D) (S : SperrInv D)
  (U : Umwelt D)

/-- **THE DISCHARGE, BY INDUCTION ON THE DEPTH.** Under the user's own
    obligation (`KoerperGutS`, `InvGutS`), an oracle in the named class and
    bodies without `locks`: at an entry meeting the callee's `requires`
    AND the callee-entry discipline, the ONLY `logik` outcome `rufAt` has
    is an `abstieg` -- the depth residue, which `rufAt_stabil_ab` turns
    into a computation at one depth. The frame comes from the entry-gated
    handler (`rufEintritt`, in `RespektiertRahmen`): the patched handler
    agrees with it wherever the discipline holds (`RufGleich*.lean`), and
    the step-3 congruence is gated the same way (`rufSchritt_unter`). -/
theorem rufAt_nurAbstieg (hTO : TreuO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hU : HavocOk S U) (hlocks : ∀ f : D.Fn, (P.rumpf f).ohneLocks = true)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hI : ∀ f : D.Fn, InvGutS P passes Q S f)
    (hS : ScopesOkProg P) :
    ∀ n : Nat, NurAbstieg P O passes n := by
  have hRO : RahmenO O := fun a σ ρ => (hTO a σ ρ).1
  have hRE : ∀ n : Nat, RespektiertRahmen P (rufEintritt P O passes n) :=
    fun n => eintritt_respektiert P O passes hTO hS n
  have hTE : ∀ n : Nat, TreuR (rufEintritt P O passes n) :=
    fun n => treuR_eintritt P O passes hTO hS n
  have hTtor : ∀ n : Nat, TreuR (torRuf P (rufEintritt P O passes n)) :=
    fun n => treuR_torRuf P (rufEintritt P O passes n) (hTE n)
  -- the gated handler's runs coincide with the patched handler's, from disciplined entries
  have hEqTor : ∀ (m : Nat) (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)),
      HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g)) σ.haelt →
      execEnd (V := vertragVon D g) O passes (torRuf P (rufEintritt P O passes m)) (P.rumpf g)
        (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ =
      execEnd (V := vertragVon D g) O passes (torRuf P (rufFrei P O passes m)) (P.rumpf g)
        (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ := by
    intro m g σ ρ hh
    have g0 : Treu (D.schreibt g) (D.gschreibt g) σ
        (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) :=
      treu_lese _ _ _
    exact end_gleich O passes (torRuf P (rufEintritt P O passes m))
      (torRuf P (rufFrei P O passes m))
      (fun g σ ρ hh => eintritt_agree_tor P O passes m g σ ρ hh)
      (hTtor m) hTO (D.signatur g).boden (bodenUnter_refl _) (P.rumpf g)
      (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ
      (hS g) (g0.heldB hh)
  intro n
  induction n with
  | zero =>
      intro g σ ρ e hh _ h
      simp only [rufAt] at h
      cases h
      exact ⟨g, rfl⟩
  | succ m ih =>
      intro g σ ρ e hh hreq heq
      rw [rufAt_succ_eq] at heq
      have hkong : HandlerUnterDisz AbstiegMarke (rufAt P O passes m)
          (torRuf P (rufFrei P O passes m)) :=
        kong_rufAt_torRuf_diszipliniert P O passes m ih
      have hTreuRufAt : TreuR (rufAt P O passes m) :=
        rufAt_treu P O passes hTO hS m
      rcases rufSchritt_unter P O passes (rufAt P O passes m)
          (torRuf P (rufFrei P O passes m)) hkong hTreuRufAt hTO hS g σ ρ hh with
        hEq | ⟨mk, h1, ⟨hh', rfl⟩⟩
      · exfalso
        have hreq1 : ReqAmEintritt P g
            (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ := by
          unfold ReqAmEintritt; rw [req_lese]; exact hreq
        -- the caller duty, on the gated run over the gated handler
        have hduty : ∀ g' : D.Fn,
            execEnd (V := vertragVon D g) O passes (torRuf P (rufEintritt P O passes m)) (P.rumpf g)
              (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ ≠
                EndAusgang.logik (Logik.vorbedingung g') := by
          intro g' hcon
          refine ((hK g).1 O hRO hRL hQ U hU (rufEintritt P O passes m) (hRE m)
            (eintritt_ohneVorbedingung P O passes m)
            (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ hreq1).2 g' ?_
          rw [Endblock.execH_ohne S O U passes (torRuf P (rufEintritt P O passes m))
            (P.rumpf g) (hlocks g)]
          exact hcon
        -- so the gated run on the gated handler IS the bare run on it
        have hYYstar : execEnd (V := vertragVon D g) O passes
              (torRuf P (rufEintritt P O passes m))
              (P.rumpf g) (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ =
            execEnd (V := vertragVon D g) O passes (rufEintritt P O passes m) (P.rumpf g)
              (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ := by
          rcases Endblock.kongruent (V := vertragVon D g) O passes
              (torRuf P (rufEintritt P O passes m)) (rufEintritt P O passes m)
              (kong_torRuf P (rufEintritt P O passes m)) (P.rumpf g)
              (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ with
            h | ⟨mk', h1', ⟨g', rfl⟩⟩
          · exact h
          · exact absurd h1' (hduty g')
        -- the three duties of the call, on the gated run
        have hbody : ∀ e' : Logik D,
            execEnd (V := vertragVon D g) O passes (torRuf P (rufFrei P O passes m)) (P.rumpf g)
              (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ ≠
                EndAusgang.logik e' := by
          intro e' hcon
          rw [← hEqTor m g σ ρ hh, hYYstar] at hcon
          refine (hK g).2 O hRO hRL hQ U hU (rufEintritt P O passes m) (hRE m)
            (eintritt_ohneLogik P O passes m)
            (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ hreq1 e' ?_
          rw [Endblock.execH_ohne S O U passes (rufEintritt P O passes m) (P.rumpf g) (hlocks g)]
          exact hcon
        have hensAll : ∀ (σ₂ : World D) (v : ErgVal D (D.erg g)),
            execEnd (V := vertragVon D g) O passes (torRuf P (rufFrei P O passes m)) (P.rumpf g)
              (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ =
                .zurueck σ₂ v →
              EnsAmRueck P g (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte)
                σ₂ ρ v := by
          intro σ₂ v hz
          rw [← hEqTor m g σ ρ hh, hYYstar] at hz
          refine ((hK g).1 O hRO hRL hQ U hU (rufEintritt P O passes m) (hRE m)
            (eintritt_ohneVorbedingung P O passes m)
            (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ hreq1).1 σ₂ v ?_
          rw [Endblock.execH_ohne S O U passes (rufEintritt P O passes m) (P.rumpf g) (hlocks g)]
          exact hz
        have hinvAll : ∀ (σ₂ : World D) (v : ErgVal D (D.erg g)),
            execEnd (V := vertragVon D g) O passes (torRuf P (rufFrei P O passes m)) (P.rumpf g)
              (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ =
                .zurueck σ₂ v → InvAmRueck P g σ₂ := by
          intro σ₂ v hz
          rw [← hEqTor m g σ ρ hh, hYYstar] at hz
          refine hI g O hRO hRL hQ U hU (rufEintritt P O passes m) (hRE m)
            (eintritt_ohneVorbedingung P O passes m)
            (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ hreq1 σ₂ v ?_
          rw [Endblock.execH_ohne S O U passes (rufEintritt P O passes m) (P.rumpf g) (hlocks g)]
          exact hz
        exact rufSchritt_nicht_logik P O passes (torRuf P (rufFrei P O passes m)) g σ ρ
          hreq hbody hensAll hinvAll e (by rw [← hEq]; exact heq)
      · rw [h1] at heq
        cases heq
        exact ⟨hh', rfl⟩

/-- **THE TWO HALVES, TOGETHER, AT DISCIPLINED WORLDS**: wherever the
    caller's duty and the entry discipline hold, `rufAt` IS in the frame
    half of the handler class (`RufRahmenTreu`) the user's obligation is
    quantified over -- and it respects the contracts (`rufAt_vertraege`).
    That is the answer to "is `rufAt` in `RespektiertRahmen`?", which used
    to be answered with "no, and here is the missing half": the missing
    half was the entry discipline, and part 4 now carries it as a premise. -/
theorem rufAt_respektiertRahmen (hTO : TreuO O) (hS : ScopesOkProg P) :
    ∀ n : Nat, RespektiertVertraege P (rufAt P O passes n) ∧
      RufRahmenTreu P (rufAt P O passes n) :=
  fun n => ⟨rufAt_vertraege P O passes n, rufAt_rahmenTreu P O passes hTO hS n⟩

end Entladung

#print axioms Gabbro.Grammatik.rufAt_rahmenTreu
#print axioms Gabbro.Grammatik.rufAt_respektiertRahmen
#print axioms Gabbro.Grammatik.rufAt_vertraege
#print axioms Gabbro.Grammatik.rufSchritt_nicht_logik
#print axioms Gabbro.Grammatik.rufAt_nurAbstieg

end Gabbro.Grammatik
