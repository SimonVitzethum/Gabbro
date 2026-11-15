/-
  File:    Grammatik/Zielsatz/NeverAsm.lean -- `-> never` with an `asm` body that has `out`.

  THE DEFECT (emitter side, Rust only, not touched here). A function declared `-> never`
  whose body is `asm { … out { result } }` is contradictory: `-> never` lowers to
  `_Noreturn` (`prototyp_kern`, emit.rs), an `out { result }` operand lowers to
  `return result;` (the `asm` branch, emit.rs). Together that is not C. The checker
  accepts it: `S009` (`nie_rueckkehr`, schleifen.rs) returns early on every non-`Block`
  body (`let FnRumpf::Block(b) = &f.rumpf else { return };`), so an `asm` body is never
  held against its `-> never` declaration -- phase 2 reports 0 errors.

  THE MODEL SIDE (this file, Lean only). A foreign body is `a : D.Ax` (Syntax.lean); its
  declared result is `D.aerg a`, and an `out` that delivers a value is an oracle answer
  that FITS (`einpassenErg`, Semantik.lean). For `D.aerg a = some .never` no raw word
  fits, for any image (`antwortLeer_never`, EinpassenVoll.lean):
  * (a) `AxNeverGut` -- the goodness condition: a `never` axiom delivers no out value;
    proved for every declaration (`axNeverGut_gilt`), and at the oracle
    (`axiomAntwort_never_keine`);
  * (b) the call never continues: `execBlock` of such a `bindAxiom` ends in
    `hardware (annahme a)` (`execBlock_bindAxiom_never`) -- the model error -- never in
    a `logik` outcome (`bindAxiom_never_kein_logik`, consistent with `KeinLogikHaltG`);
    progress names the head `nieZurueck` (`kopf_nieZurueck_never`), never `hardware`
    (`kein_hardware_an_never`, consistent with `FortschrittG`/`fort_dann`).
  The acceptance side keeps admitting the PURE `-> never` axiom (`stelleOk_never_ax`,
  the contrast `w1v_bool` in ProbenW1.lean): forbidding the contradictory `out` is the
  checker's job (proposed sentence below, not implemented here).

  PROPOSED CHECKER SENTENCE (not implemented): a `-> never` function with an `asm` body
  that names `out { result }` is refused -- `_Noreturn` together with `return result` is
  not C; whoever reads the assembler's result declares a result type, whoever never
  returns writes no `out`.
-/
module
public import Grammatik.Zielsatz.Eigenschaften.BudgetZeuge
public import Grammatik.Logik.Vertraege.EinpassenVoll
@[expose] public section


namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
  {τ : Ty}

/-! ## 1. The goodness condition: a `never` axiom delivers no out value -/

/-- **Goodness: an axiom with a `never` result delivers no out value.** Its answer class
    is empty: no raw word of any oracle fits the declared result. A `-> never` foreign
    body with an `out` -- the contradictory source form -- has no fitting answer in the
    model; whatever the machine says, the call is the foreign code breaking its
    declaration. -/
def AxNeverGut (D : Deklaration) : Prop :=
  ∀ a : D.Ax, D.aerg a = some .never → AntwortLeer D (D.aerg a)

/-- The condition holds for every declaration: `einpassen` refuses every raw word at
    `never` (`antwortLeer_never`, EinpassenVoll.lean). -/
theorem axNeverGut_gilt : AxNeverGut D := by
  intro a h
  rw [h]
  exact antwortLeer_never

/-- No oracle answer to a `never` axiom ever fits -- for every oracle, world and
    argument. -/
theorem axiomAntwort_never_keine (O : Orakel D) (a : D.Ax) (h : D.aerg a = some .never)
    (σ : World D) (ρ : Env D (D.aparams a)) :
    einpassenErg O.zeiger (D.aerg a) (O.wirkt a σ ρ).2 = none :=
  axNeverGut_gilt a h O.zeiger _

/-! ## 2. The model error: the call never continues -/

/-- **The model error**: running a `bindAxiom` whose declared result is `never` ends in
    `hardware (annahme a)` for every oracle, budget, handler, world and argument -- the
    continuation (`rest`) never runs. -/
theorem execBlock_bindAxiom_never (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Block D V l (τ :: Γ) Λ Λ') (hne : τ = .never)
    (σ : World D) (ρ : Env D Γ) :
    execBlock O passes R (.bindAxiom a args he hw hg hd hgd rest) σ ρ =
      .hardware (.annahme a) := by
  have h2 : einpassenErg O.zeiger (D.aerg a)
      (O.wirkt a ((σ.lese Λ args.orte).fragt (.inl a))
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).2 = none :=
    axiomAntwort_never_keine O a (by rw [he, hne]) _ _
  simp only [execBlock, axiomAntwort, Boundary.Check.trivial_requiredB,
    Bool.false_eq_true, ↓reduceIte, h2]

/-- ... and never in a `logik` outcome: the stop is the foreign code's, not the user's
    logic -- consistent with `KeinLogikHaltG` (ZielOrtGanz.lean). -/
theorem bindAxiom_never_kein_logik (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Block D V l (τ :: Γ) Λ Λ') (hne : τ = .never)
    (σ : World D) (ρ : Env D Γ) (e : Logik D) :
    execBlock O passes R (.bindAxiom a args he hw hg hd hgd rest) σ ρ ≠ .logik e := by
  have hE := execBlock_bindAxiom_never O passes R a args he hw hg hd hgd rest hne σ ρ
  rw [hE]
  intro hcon
  cases hcon

/-! ## 3. Progress names it `nieZurueck`, never `hardware` -/

/-- The acceptance side keeps admitting the PURE `-> never` axiom: it is `StelleOk` by
    its declaration (the contrast `w1v_bool`, ProbenW1.lean). -/
theorem stelleOk_never_ax (a : D.Ax) (h : D.aerg a = some .never) :
    StelleOk D (.inl a) :=
  Or.inl h

/-- The head of a `never` axiom call is the named stop `nieZurueck` -- structurally, for
    every oracle, budget and world. -/
theorem kopf_nieZurueck_never (O : Orakel D) (passes : Nat) (σ : World D) (ρ : Env D Γ)
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Block D V l (τ :: Γ) Λ Λ') (h : D.aerg a = some .never) :
    KopfHalt O passes σ ρ .nieZurueck (.bindAxiom a args he hw hg hd hgd rest) :=
  h

/-- ... and never the named stop `hardware`: the answer class is empty, so the hardware
    clause (`¬ AntwortLeer`) fails. Consistent with `FortschrittG`: `fort_dann`
    (Fortschritt.lean) files the empty answer site as `nieZurueck` (`fort_nie`), never
    as `fort_hw`. -/
theorem kein_hardware_an_never (O : Orakel D) (passes : Nat) (σ : World D) (ρ : Env D Γ)
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Block D V l (τ :: Γ) Λ Λ') (h : D.aerg a = some .never) :
    ¬ KopfHalt O passes σ ρ .hardware (.bindAxiom a args he hw hg hd hgd rest) := by
  intro hH
  exact hH.2 (axNeverGut_gilt a h)

/-! ## 4. A standalone never fixture, independent of unrelated probe contracts -/

/-- One inhabited foreign name whose result has no value. -/
def nvD : Deklaration :=
  { BudgetZeuge.bD with
    Ax := Unit
    aparams := fun _ => []
    aerg := fun _ => some .never
    aschreibt := fun _ item => nomatch item
    agschreibt := fun _ item => nomatch item
    anbieter := fun item => nomatch item
    anbieter_passt := fun item => nomatch item }

def nvKopf : Block nvD (vertragVon nvD ()) false [] [] [] :=
  .bindAxiom (τ := .never) () .nil rfl (fun item => nomatch item) (fun item => nomatch item)
    (fun item => nomatch item) (fun item => nomatch item) .nil


/-- The standalone witness declaration (one axiom `-> never`) meets the
    goodness condition. -/
theorem nv_zeuge_gut : AxNeverGut nvD :=
  axNeverGut_gilt

/-- At the witness axiom no oracle answer fits. -/
theorem nv_zeuge_kein_out (O : Orakel nvD) (σ : World nvD)
    (ρ : Env nvD (nvD.aparams ())) :
    einpassenErg O.zeiger (nvD.aerg ()) (O.wirkt () σ ρ).2 = none :=
  axiomAntwort_never_keine O () rfl σ ρ

/-- Non-degeneracy: the witness HAS a `never` axiom, the site is admissible, and no
    oracle answer to it fits; both head classifications are proved jointly below. -/
theorem nv_zeuge_nicht_leer :
    ∃ a : nvD.Ax, nvD.aerg a = some .never ∧ StelleOk nvD (.inl a) ∧
      ∀ (O : Orakel nvD) (σ : World nvD) (ρ : Env nvD (nvD.aparams a)),
        einpassenErg O.zeiger (nvD.aerg a) (O.wirkt a σ ρ).2 = none :=
  ⟨(), rfl, Or.inl rfl, fun O σ ρ => axiomAntwort_never_keine O () rfl σ ρ⟩

/-- At the witness head both classifications hold together: `nieZurueck` structurally,
    never `hardware`. -/
theorem nv_zeuge_kopf_benannt (O : Orakel nvD) (passes : Nat) (σ : World nvD) :
    KopfHalt O passes σ (.nil : Env nvD []) .nieZurueck nvKopf ∧
      ¬ KopfHalt O passes σ (.nil : Env nvD []) .hardware nvKopf :=
  ⟨by rfl,
    kein_hardware_an_never O passes σ (.nil : Env nvD []) () .nil rfl
      (fun e => nomatch e) (fun e => nomatch e) (fun e => nomatch e) (fun e => nomatch e)
      .nil rfl⟩

#print axioms Gabbro.Grammatik.Zielsatz.AxNeverGut
#print axioms Gabbro.Grammatik.Zielsatz.axNeverGut_gilt
#print axioms Gabbro.Grammatik.Zielsatz.axiomAntwort_never_keine
#print axioms Gabbro.Grammatik.Zielsatz.execBlock_bindAxiom_never
#print axioms Gabbro.Grammatik.Zielsatz.bindAxiom_never_kein_logik
#print axioms Gabbro.Grammatik.Zielsatz.stelleOk_never_ax
#print axioms Gabbro.Grammatik.Zielsatz.kopf_nieZurueck_never
#print axioms Gabbro.Grammatik.Zielsatz.kein_hardware_an_never
#print axioms Gabbro.Grammatik.Zielsatz.nv_zeuge_gut
#print axioms Gabbro.Grammatik.Zielsatz.nv_zeuge_kein_out
#print axioms Gabbro.Grammatik.Zielsatz.nv_zeuge_nicht_leer
#print axioms Gabbro.Grammatik.Zielsatz.nv_zeuge_kopf_benannt

end Gabbro.Grammatik.Zielsatz
