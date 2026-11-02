module
public import Grammatik.Logik.Ruf.RufLogik
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 4. The three congruence instances -/

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

/-- **Step 2**: the gated handler differs from the patched one only where the
    callee's `requires` fails, and there it answers a `vorbedingung`. -/
theorem kong_torRuf_rufFrei (P : Programm D) (O : Orakel D) (passes n : Nat) :
    HandlerUnter VorbedMarke (torRuf P (rufFrei P O passes n)) (rufFrei P O passes n) := by
  intro g σ ρ
  unfold torRuf
  by_cases hq : wahr? (eval σ (P.requires g) σ ρ) = true
  · rw [if_pos hq]; exact Or.inl rfl
  · rw [if_neg hq]; exact Or.inr ⟨.logik (.vorbedingung g), rfl, ⟨g, rfl⟩⟩

/-- **The statement the depth induction carries**: at an entry that meets the
    callee's `requires`, the only `logik` outcome of `rufAt` is an `abstieg`. -/
def NurAbstieg (P : Programm D) (O : Orakel D) (passes n : Nat) : Prop :=
  ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)) (e : Logik D),
    ReqAmEintritt P g σ ρ → rufAt P O passes n g σ ρ = .logik e → ∃ h : D.Fn, e = .abstieg h

/-- **Step 3**: under the induction hypothesis, `rufAt` differs from the
    gated patched handler only where it answers an `abstieg`. -/
theorem kong_rufAt_torRuf (P : Programm D) (O : Orakel D) (passes n : Nat)
    (ih : NurAbstieg P O passes n) :
    HandlerUnter AbstiegMarke (rufAt P O passes n) (torRuf P (rufFrei P O passes n)) := by
  intro g σ ρ
  by_cases hq : wahr? (eval σ (P.requires g) σ ρ) = true
  · unfold torRuf rufFrei
    rw [if_pos hq]
    cases hx : rufAt P O passes n g σ ρ with
    | ok σ' v => exact Or.inl rfl
    | why σ' r => exact Or.inl rfl
    | hardware e => exact Or.inl rfl
    | logik e =>
        obtain ⟨hh, rfl⟩ := ih g σ ρ e hq hx
        exact Or.inr ⟨.logik (.abstieg hh), rfl, ⟨hh, rfl⟩⟩
  · have hgate : torRuf P (rufFrei P O passes n) g σ ρ = .logik (.vorbedingung g) := by
      unfold torRuf; rw [if_neg hq]
    cases n with
    | zero => exact Or.inr ⟨.logik (.abstieg g), rfl, ⟨g, rfl⟩⟩
    | succ m =>
        rw [hgate]
        exact Or.inl (rufAt_vorbed P O passes m g σ ρ (by simpa [ReqAmEintritt] using hq))

/-! ## 5. THE DISCHARGE -/

/-- **The frame half of `RespektiertRahmen`, for a handler**: an `ok` answer
    keeps the callee's declared frame and gives back every lock it took, at
    EVERY world. `rufAt_gut` (`Satz.lean`) gives it only at worlds meeting
    `HeldB`, and part 4 quantifies over all of them; `rufAt_treu`
    (`RahmenTreu.lean`) gives it at all of them. -/
def RufRahmenTreu (P : Programm D)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) (σ' : World D) (v : ErgVal D (D.erg f)),
    R f σ ρ = RufAusgang.ok σ' v →
      Rahmen (D.schreibt f) (D.gschreibt f) σ σ' ∧ offen σ'.spur = offen σ.spur

/-- **THE FRAME HALF OF `RespektiertRahmen` FOR `rufAt`, AT EVERY WORLD --
    PROVED** (`rufAt_treu`, RahmenTreu.lean). The only premise is the
    hardware's: an axiom keeps the frame of its declared `effects` and leaves
    the held locks alone. Together with `rufAt_vertraege` this puts `rufAt`
    into `RespektiertRahmen` wherever the caller's duty holds. -/
theorem rufAt_rahmenTreu (P : Programm D) (O : Orakel D) (passes : Nat) (hO : TreuO O) :
    ∀ n : Nat, RufRahmenTreu P (rufAt P O passes n) := by
  intro n f σ ρ σ' v h
  exact rufAt_treu P O passes hO n f σ ρ σ' (by rw [h]; rfl)

section Entladung

variable (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D) (S : SperrInv D)
  (U : Umwelt D)

/-- **THE DISCHARGE, BY INDUCTION ON THE DEPTH.** Under the user's own
    obligation (`KoerperGutS`, `InvGutS`), an oracle in the named class and
    bodies without `locks`: at an entry meeting the callee's `requires`, the
    ONLY `logik` outcome `rufAt` has is an `abstieg` -- the depth residue,
    which `rufAt_stabil_ab` turns into a computation at one depth. NO
    hypothesis about the frame: `rufAt_rahmenTreu` proves it. -/
theorem rufAt_nurAbstieg (hTO : TreuO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hU : HavocOk S U) (hlocks : ∀ f : D.Fn, (P.rumpf f).ohneLocks = true)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hI : ∀ f : D.Fn, InvGutS P passes Q S f) :
    ∀ n : Nat, NurAbstieg P O passes n := by
  have hRO : RahmenO O := fun a σ ρ => (hTO a σ ρ).1
  have hRT : ∀ n : Nat, RufRahmenTreu P (rufAt P O passes n) :=
    rufAt_rahmenTreu P O passes hTO
  have hFrame : ∀ n : Nat, RespektiertRahmen P (rufFrei P O passes n) := fun n =>
    ⟨fun f σ ρ hreq σ' v h =>
        rufAt_vertraege P O passes n f σ ρ hreq σ' v (rufFrei_ok P O passes n f σ ρ σ' v h),
     fun f σ ρ σ' v h => hRT n f σ ρ σ' v (rufFrei_ok P O passes n f σ ρ σ' v h)⟩
  intro n
  induction n with
  | zero =>
      intro g σ ρ e _ h
      simp only [rufAt] at h
      cases h
      exact ⟨g, rfl⟩
  | succ m ih =>
      intro g σ ρ e hreq heq
      rw [rufAt_succ_eq] at heq
      rcases rufSchritt_kongruent (kong_rufAt_torRuf P O passes m ih) P O passes g σ ρ with
        hEq | ⟨mk, h1, ⟨hh, rfl⟩⟩
      · exfalso
        have hreq1 : ReqAmEintritt P g
            (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ := by
          unfold ReqAmEintritt; rw [req_lese]; exact hreq
        -- the caller duty, on the GATED run
        have hduty : ∀ g' : D.Fn,
            execEnd (V := vertragVon D g) O passes (torRuf P (rufFrei P O passes m)) (P.rumpf g)
              (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ ≠
                EndAusgang.logik (Logik.vorbedingung g') := by
          intro g' hcon
          refine ((hK g).1 O hRO hRL hQ U hU (rufFrei P O passes m) (hFrame m)
            (rufFrei_ohneVorbedingung P O passes m)
            (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ hreq1).2 g' ?_
          rw [Endblock.execH_ohne S O U passes (torRuf P (rufFrei P O passes m))
            (P.rumpf g) (hlocks g)]
          exact hcon
        -- so the gated run IS the patched run
        have hYY : execEnd (V := vertragVon D g) O passes (torRuf P (rufFrei P O passes m))
              (P.rumpf g) (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ =
            execEnd (V := vertragVon D g) O passes (rufFrei P O passes m) (P.rumpf g)
              (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ := by
          rcases Endblock.kongruent (V := vertragVon D g) O passes
              (torRuf P (rufFrei P O passes m)) (rufFrei P O passes m)
              (kong_torRuf_rufFrei P O passes m) (P.rumpf g)
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
          rw [hYY] at hcon
          refine (hK g).2 O hRO hRL hQ U hU (rufFrei P O passes m) (hFrame m)
            (rufFrei_ohneLogik P O passes m)
            (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ hreq1 e' ?_
          rw [Endblock.execH_ohne S O U passes (rufFrei P O passes m) (P.rumpf g) (hlocks g)]
          exact hcon
        have hensAll : ∀ (σ₂ : World D) (v : ErgVal D (D.erg g)),
            execEnd (V := vertragVon D g) O passes (torRuf P (rufFrei P O passes m)) (P.rumpf g)
              (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ =
                .zurueck σ₂ v →
              EnsAmRueck P g (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte)
                σ₂ ρ v := by
          intro σ₂ v hz
          rw [hYY] at hz
          refine ((hK g).1 O hRO hRL hQ U hU (rufFrei P O passes m) (hFrame m)
            (rufFrei_ohneVorbedingung P O passes m)
            (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ hreq1).1 σ₂ v ?_
          rw [Endblock.execH_ohne S O U passes (rufFrei P O passes m) (P.rumpf g) (hlocks g)]
          exact hz
        have hinvAll : ∀ (σ₂ : World D) (v : ErgVal D (D.erg g)),
            execEnd (V := vertragVon D g) O passes (torRuf P (rufFrei P O passes m)) (P.rumpf g)
              (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ =
                .zurueck σ₂ v → InvAmRueck P g σ₂ := by
          intro σ₂ v hz
          rw [hYY] at hz
          refine hI g O hRO hRL hQ U hU (rufFrei P O passes m) (hFrame m)
            (rufFrei_ohneVorbedingung P O passes m)
            (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ hreq1 σ₂ v ?_
          rw [Endblock.execH_ohne S O U passes (rufFrei P O passes m) (P.rumpf g) (hlocks g)]
          exact hz
        exact rufSchritt_nicht_logik P O passes (torRuf P (rufFrei P O passes m)) g σ ρ
          hreq hbody hensAll hinvAll e (by rw [← hEq]; exact heq)
      · rw [h1] at heq
        cases heq
        exact ⟨hh, rfl⟩

/-- **THE TWO HALVES, TOGETHER**: wherever the caller's duty holds, `rufAt`
    IS in the handler class the user's obligation is quantified over. That
    is the fact the discharge above turns into a statement about `logik`
    outcomes; it is stated on its own because it is the answer to "is
    `rufAt` in `RespektiertRahmen`?", which used to be answered with "no,
    and here is the missing half". -/
theorem rufAt_respektiertRahmen (hTO : TreuO O) :
    ∀ n : Nat, RespektiertVertraege P (rufAt P O passes n) ∧
      (∀ (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) (σ' : World D)
        (v : ErgVal D (D.erg f)), rufAt P O passes n f σ ρ = .ok σ' v →
          Rahmen (D.schreibt f) (D.gschreibt f) σ σ' ∧ offen σ'.spur = offen σ.spur) :=
  fun n => ⟨rufAt_vertraege P O passes n, rufAt_rahmenTreu P O passes hTO n⟩

end Entladung

#print axioms Gabbro.Grammatik.rufAt_rahmenTreu
#print axioms Gabbro.Grammatik.rufAt_respektiertRahmen
#print axioms Gabbro.Grammatik.rufAt_vertraege
#print axioms Gabbro.Grammatik.rufSchritt_nicht_logik
#print axioms Gabbro.Grammatik.rufAt_nurAbstieg

end Gabbro.Grammatik
