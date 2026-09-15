/-
  File:      Grammatik/RufLogik.lean
  Subject:   **THE `logik` HALF OF PART 4's CONDITION** -- what the user's own
             obligation discharges of it, once the handler congruence
             (`HandlerKongruenz.lean`) is there to carry the obligation from
             the handler class it is quantified over to `rufAt`.

  WHERE THIS SITS. `Schlusssatz.lean` part 4 is conditional on
  `(rufAt K.E.P O passes n f σ ρG).istFehler = false`. The model has two error
  classes; the HARDWARE one is discharged for every certified program
  (`korrOk_rufAt_ohneHardware`, clause 4b). What is left is the writer's
  logic, and the reason it was left is NOT that the user proves too little:
  `KoerperGutS` (Zielsatz/Spec.lean (b)) covers every body-own `logik` outcome
  and the caller duty. The reason is that it is quantified over handlers in
  `RespektiertRahmen ∧ OhneVorbedingung` and `RespektiertRahmen ∧ OhneLogik`,
  and `rufAt` is in NEITHER.

  THE ROUTE, in three steps, each one an instance of the congruence:

  1. `rufFrei P O passes n` is `rufAt` with every `logik` answer replaced by
     the hardware default. It IS in `OhneLogik` and in `OhneVorbedingung`, and
     `rufAt` differs from it only where `rufAt` answers a `logik`.
  2. `torRuf P (rufFrei …)` gates the calls by their `requires`; `rufAt`
     differs from THAT only where `rufAt` answers an `abstieg` -- which is
     where the induction hypothesis of the depth induction bites, and where
     the depth `0` case sits.
  3. The obligations then apply to the two runs, and the three error kinds
     `rufAt` adds on its own -- `vorbedingung`, `nachbedingung`,
     `invariante` -- fall to the caller duty, the body triple and `InvGutS`.

  WHAT IS LEFT -- AND SINCE 2026-09-15 IT IS NOTHING BUT THE DEPTH.
  `RespektiertRahmen P (rufAt P O passes n)` has two halves. The CONTRACT
  half is `rufAt_vertraege` below. The FRAME half was carried as a named
  hypothesis (`RufRahmenTreu`) for one day, because `rufAt_gut` (`Satz.lean`)
  proves the frame only at worlds meeting
  `HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) σ.haelt` and
  part 4 quantifies over ANY world. `RahmenTreu.lean` now proves it at every
  world (`rufAt_treu`), by the same induction over the grammar with the lock
  discipline deleted from the conclusion: the frame and the held set never
  needed it, only the trace QUALITY did. So `rufAt_nurAbstieg` is
  unconditional in that hypothesis. See `messung/muse/OPUS-BERICHT-RAHMEN.md`
  and `-KONGRUENZ.md`.
-/
import Grammatik.RahmenTreu
import Grammatik.RufTiefe
import Grammatik.SperreFuss
import Grammatik.ZielOrtInv

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Reads do not change memory, and an expression does not see the trace -/

theorem foldl_lese_slots (P : Programm D) :
    ∀ (is : List D.Inv) (σ : World D),
      (is.foldl (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte) σ).slots = σ.slots
  | [], _ => rfl
  | i :: is, σ => foldl_lese_slots P is (σ.lese (invSicht D i) (P.invariante i).orte)

theorem foldl_lese_globs (P : Programm D) :
    ∀ (is : List D.Inv) (σ : World D),
      (is.foldl (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte) σ).globs = σ.globs
  | [], _ => rfl
  | i :: is, σ => foldl_lese_globs P is (σ.lese (invSicht D i) (P.invariante i).orte)

/-- **An expression does not see the trace.** Two worlds with the same slots
    and globals give the same value, on the `old(..)` side and on the current
    side -- so a READ, which only appends events, changes no test. -/
theorem eval_spurfrei {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (σ₀ σ₀' σ σ' : World D) (h0s : σ₀.slots = σ₀'.slots) (h0g : σ₀.globs = σ₀'.globs)
    (hs : σ.slots = σ'.slots) (hg : σ.globs = σ'.globs) (ρ : Env D Γ) :
    eval σ₀ e σ ρ = eval σ₀' e σ' ρ :=
  Extraktion.eval_liest_nur_orte e e.orte (fun _ h => h) σ₀ σ₀' σ σ' ρ
    (fun _ _ _ _ => by rw [hs]) (fun _ _ => by rw [hg])
    (fun _ _ _ _ => by rw [h0s]) (fun _ _ => by rw [h0g])

/-- **`rufAt`'s gate IS the entry contract**: the requires test at the world
    after the entry read is the requires test at the entry world. -/
theorem req_lese (P : Programm D) (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) :
    wahr? (eval (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) (P.requires f)
        (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ) =
      wahr? (eval σ (P.requires f) σ ρ) :=
  congrArg wahr? (eval_spurfrei (P.requires f)
    (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) σ
    (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) σ rfl rfl rfl rfl ρ)

/-- **A call above depth `0` whose entry contract fails IS a `vorbedingung`
    outcome.** -/
theorem rufAt_vorbed (P : Programm D) (O : Orakel D) (passes n : Nat) (f : D.Fn)
    (σ : World D) (ρ : Env D (D.params f)) (h : ¬ ReqAmEintritt P f σ ρ) :
    rufAt P O passes (n + 1) f σ ρ = .logik (.vorbedingung f) := by
  rw [rufAt_succ_eq]
  simp only [rufSchritt]
  rw [if_pos]
  rw [req_lese]
  simpa [ReqAmEintritt] using h

/-! ## 2. One unfolding of `rufAt` cannot end in a `logik` outcome of its own -/

/-- **The three error kinds a CALL adds to its body's.** If the entry contract
    holds, the body ends in no `logik` outcome, every return satisfies the
    `ensures` and every return satisfies the owed invariants, then the call
    does not end in a `logik` outcome either. Nothing about depth here: this
    is one unfolding (`rufSchritt`). -/
theorem rufSchritt_nicht_logik (P : Programm D) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (f : D.Fn)
    (σ : World D) (ρ : Env D (D.params f)) (hq : ReqAmEintritt P f σ ρ)
    (hbody : ∀ e : Logik D,
      execEnd (V := vertragVon D f) O passes R (P.rumpf f)
        (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ ≠ .logik e)
    (hens : ∀ (σ₂ : World D) (v : ErgVal D (D.erg f)),
      execEnd (V := vertragVon D f) O passes R (P.rumpf f)
        (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ = .zurueck σ₂ v →
        EnsAmRueck P f (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) σ₂ ρ v)
    (hinv : ∀ (σ₂ : World D) (v : ErgVal D (D.erg f)),
      execEnd (V := vertragVon D f) O passes R (P.rumpf f)
        (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ = .zurueck σ₂ v →
        InvAmRueck P f σ₂) :
    ∀ e : Logik D, rufSchritt P O passes R f σ ρ ≠ .logik e := by
  intro e hcon
  simp only [rufSchritt] at hcon
  rw [if_neg (by rw [req_lese, show wahr? (eval σ (P.requires f) σ ρ) = true from hq]; simp)]
    at hcon
  cases hy : execEnd (V := vertragVon D f) O passes R (P.rumpf f)
      (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ with
  | grund σ₂ r => simp [hy] at hcon
  | leave hl σ₂ ρ₂ => exact absurd hl (by decide)
  | next hl σ₂ ρ₂ => exact absurd hl (by decide)
  | logik e' => exact hbody e' hy
  | hardware e' => simp [hy] at hcon
  | zurueck σ₂ w =>
      simp only [hy] at hcon
      have h1 : wahr? (eval (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
          (P.ensures f) (σ₂.lese (vertragVon D f).ende (P.ensures f).orte)
          (ergEnv (D.erg f) w ρ)) = true := by
        have hE := hens σ₂ w hy
        unfold EnsAmRueck at hE
        rw [eval_spurfrei (P.ensures f)
          (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
          (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
          σ₂ (σ₂.lese (vertragVon D f).ende (P.ensures f).orte)
          rfl rfl rfl rfl (ergEnv (D.erg f) w ρ)] at hE
        exact hE
      rw [if_neg (by rw [h1]; simp)] at hcon
      have h2 : (D.invs.find? (fun i => schuldet f i && !wahr? (eval
          ((D.invs.filter (schuldet f)).foldl
            (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
            (σ₂.lese (vertragVon D f).ende (P.ensures f).orte)) (P.invariante i)
          ((D.invs.filter (schuldet f)).foldl
            (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
            (σ₂.lese (vertragVon D f).ende (P.ensures f).orte)) .nil))) = none := by
        rw [List.find?_eq_none]
        intro i hi hp
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
        have hh := hinv σ₂ w hy i hi hp.1
        unfold InvHaelt at hh
        rw [eval_spurfrei (P.invariante i) σ₂
          ((D.invs.filter (schuldet f)).foldl
            (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
            (σ₂.lese (vertragVon D f).ende (P.ensures f).orte)) σ₂
          ((D.invs.filter (schuldet f)).foldl
            (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
            (σ₂.lese (vertragVon D f).ende (P.ensures f).orte))
          (by rw [foldl_lese_slots]; try rfl) (by rw [foldl_lese_globs]; try rfl)
          (by rw [foldl_lese_slots]; try rfl) (by rw [foldl_lese_globs]; try rfl) Env.nil] at hh
        rw [hh] at hp
        cases hp.2
      simp only [h2] at hcon
      cases hcon

/-- **THE CONTRACT HALF OF `RespektiertRahmen`, FOR `rufAt` -- PROVED.** An
    `ok` answer of `rufAt` passed the callee's `ensures` test, and that test
    differs from `EnsAmRueck` only by READS, which no expression sees
    (`eval_spurfrei`). So of the two halves of the handler class, only the
    FRAME half is left open for `rufAt`. -/
theorem rufAt_vertraege (P : Programm D) (O : Orakel D) (passes : Nat) :
    ∀ n : Nat, RespektiertVertraege P (rufAt P O passes n) := by
  intro n
  cases n with
  | zero => intro f σ ρ _ σ' v h; simp [rufAt] at h
  | succ m =>
      intro f σ ρ hreq
      rw [rufAt_succ_eq]
      simp only [rufSchritt]
      rw [if_neg (by rw [req_lese, show wahr? (eval σ (P.requires f) σ ρ) = true from hreq]; simp)]
      cases hy : execEnd (V := vertragVon D f) O passes (rufAt P O passes m) (P.rumpf f)
          (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ with
      | grund σ₂ r => dsimp only; intro σ' v h; cases h
      | leave hl σ₂ ρ₂ => exact absurd hl (by decide)
      | next hl σ₂ ρ₂ => exact absurd hl (by decide)
      | logik e => dsimp only; intro σ' v h; cases h
      | hardware e => dsimp only; intro σ' v h; cases h
      | zurueck σ₂ w =>
          dsimp only
          by_cases he : wahr? (eval
              (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) (P.ensures f)
              (σ₂.lese (vertragVon D f).ende (P.ensures f).orte)
              (ergEnv (D.erg f) w ρ)) = false
          · rw [if_pos he]; intro σ' v h; cases h
          · rw [if_neg he]
            cases hf : D.invs.find? (fun i => schuldet f i && !wahr? (eval
                ((D.invs.filter (schuldet f)).foldl
                  (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
                  (σ₂.lese (vertragVon D f).ende (P.ensures f).orte)) (P.invariante i)
                ((D.invs.filter (schuldet f)).foldl
                  (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
                  (σ₂.lese (vertragVon D f).ende (P.ensures f).orte)) .nil)) with
            | some i => dsimp only; intro σ' v h; cases h
            | none =>
                dsimp only
                intro σ' v h
                cases h
                unfold EnsAmRueck
                rw [eval_spurfrei (P.ensures f)
                  σ (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
                  ((D.invs.filter (schuldet f)).foldl
                    (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
                    (σ₂.lese (vertragVon D f).ende (P.ensures f).orte))
                  (σ₂.lese (vertragVon D f).ende (P.ensures f).orte)
                  rfl rfl (by rw [foldl_lese_slots]) (by rw [foldl_lese_globs])
                  (ergEnv (D.erg f) w ρ)]
                cases hx : wahr? (eval
                    (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) (P.ensures f)
                    (σ₂.lese (vertragVon D f).ende (P.ensures f).orte)
                    (ergEnv (D.erg f) w ρ))
                · exact absurd hx he
                · rfl

/-! ## 3. The patched handler -/

/-- **`rufAt` with every `logik` answer replaced by the hardware default.**
    The trick `rufAusL` (`ZielOrtGanz.lean`) already uses: a default that is
    NEITHER `ok` (so no frame or contract duty attaches to it) NOR `logik`
    (so the handler is in `OhneLogik` and in `OhneVorbedingung`). -/
def rufFrei (P : Programm D) (O : Orakel D) (passes n : Nat) :
    ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f :=
  fun g σ ρ =>
    match rufAt P O passes n g σ ρ with
    | .logik _ => .hardware .ieee
    | a => a

theorem rufFrei_ohneLogik (P : Programm D) (O : Orakel D) (passes n : Nat) :
    OhneLogik (rufFrei P O passes n) := by
  intro g σ ρ e
  unfold rufFrei
  cases hx : rufAt P O passes n g σ ρ <;> intro h <;> cases h

theorem rufFrei_ohneVorbedingung (P : Programm D) (O : Orakel D) (passes n : Nat) :
    OhneVorbedingung (rufFrei P O passes n) := by
  intro g σ ρ e h
  exact absurd h (rufFrei_ohneLogik P O passes n g σ ρ e)

/-- At an `ok` answer the patched handler IS `rufAt`. -/
theorem rufFrei_ok (P : Programm D) (O : Orakel D) (passes n : Nat) (g : D.Fn)
    (σ : World D) (ρ : Env D (D.params g)) (σ' : World D) (v : ErgVal D (D.erg g)) :
    rufFrei P O passes n g σ ρ = .ok σ' v → rufAt P O passes n g σ ρ = .ok σ' v := by
  unfold rufFrei
  cases hx : rufAt P O passes n g σ ρ with
  | ok σ₂ w => exact id
  | grund σ₂ r => intro h; cases h
  | logik e => intro h; cases h
  | hardware e => intro h; cases h

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
  | grund σ' r => exact Or.inl rfl
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
    | grund σ' r => exact Or.inl rfl
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
    `rufAt` in `RespektiertRahmen`?", which the CUTS of `Schlusssatz.lean`
    used to answer with "no, and here is the missing half". -/
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
