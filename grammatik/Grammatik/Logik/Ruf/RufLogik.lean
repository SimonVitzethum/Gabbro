/-
  File:      Grammatik/RufLogik.lean
  Subject:   **THE `logik` HALF OF PART 4's CONDITION** -- what the user's own
             obligation discharges of it, once the handler congruence
             (`HandlerKongruenz.lean`) is there to carry the obligation from
             the handler class it is quantified over to `rufAt`.

  WHERE THIS SITS. A statement about a call that is conditional on
  `(rufAt P O passes n f σ ρG).istFehler = false` meets the model's two error
  classes; the HARDWARE one is discharged for every program whose bodies carry no
  oracle form (`rufAt_ohneHardware`, `RufOhneHardware.lean`). What is left is the writer's
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
  `HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) σ.haelt`.
  `RahmenTreu.lean` proves it wherever that entry discipline holds
  (`rufAt_treu`, by the same induction over the grammar with the trace
  quality deleted from the conclusion): the frame and the held set never
  needed the trace, but collapsing a callee release to an equality needs the
  entry discipline -- part 4 as stated quantifies over ANY world, so
  `rufAt_nurAbstieg` still needs the entry discipline (or vacuous scopes)
  there. See `messung/muse/OPUS-BERICHT-RAHMEN.md` and `-KONGRUENZ.md`.
-/
module
public import Grammatik.Logik.Vertraege.RahmenTreu
public import Grammatik.Logik.Ruf.RufTiefe
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreFuss
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtInv
@[expose] public section


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
  rw [if_neg (by rw [req_lese, show wahr? (eval σ (P.requires f) σ ρ) = true from hq]; simp only [Bool.true_eq_false, not_false_eq_true])]
    at hcon
  cases hy : execEnd (V := vertragVon D f) O passes R (P.rumpf f)
      (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ with
  | why σ₂ r => simp only [hy, reduceCtorEq] at hcon
  | leave hl σ₂ ρ₂ => exact absurd hl (by decide)
  | next hl σ₂ ρ₂ => exact absurd hl (by decide)
  | logik e' => exact hbody e' hy
  | hardware e' => simp only [hy, reduceCtorEq] at hcon
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
      rw [if_neg (by rw [h1]; simp only [Bool.true_eq_false, not_false_eq_true])] at hcon
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
  | zero => intro f σ ρ _ σ' v h; simp only [rufAt, reduceCtorEq] at h
  | succ m =>
      intro f σ ρ hreq
      rw [rufAt_succ_eq]
      simp only [rufSchritt]
      rw [if_neg (by rw [req_lese, show wahr? (eval σ (P.requires f) σ ρ) = true from hreq]; simp only [Bool.true_eq_false, not_false_eq_true])]
      cases hy : execEnd (V := vertragVon D f) O passes (rufAt P O passes m) (P.rumpf f)
          (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ with
      | why σ₂ r => dsimp only; intro σ' v h; cases h
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
  | why σ₂ r => intro h; cases h
  | logik e => intro h; cases h
  | hardware e => intro h; cases h

end Gabbro.Grammatik
