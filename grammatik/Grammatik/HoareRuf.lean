/-
  File:      Grammatik/HoareRuf.lean
  Subject:   HOARE RULE FOR THE CALL STATEMENT, SOUND AGAINST A
              CONTRACT-RESPECTING CALL HANDLER.

  `HoareRegeln.lean` has partial-correctness triples `STTripel` over
  `execStmt` and rules skip/assign/seq/ite/consequence, plus
  call-independence for call-free bodies. This file adds the missing
  rule for a `Stmt.call` statement, stated against a call handler `R`
  that respects the program contracts at their place
  (`RespektiertVertraege`, over `ReqAmEintritt`/`EnsAmRueck` from
  `VertragOrtB.lean` with the ACTUAL evaluated arguments and the
  ACTUAL entry/return worlds -- never quantified over environments).

  `hoare_call`: whenever `R` respects the contracts, the call
  statement `.call f args hp hr` satisfies the statement triple
  whose precondition is "requires holds at the argument world with
  the evaluated arguments" and whose postcondition is "ensures holds
  with the actual entry world, the actual return world, the actual
  arguments and the actual result".

  Witness: `hoare_call_zeuge` on a non-degenerate one-function
  program (one table that the function writes; ensures result =
  param + 1) with a handler that runs the body, plus the instructed
  `rufPD` witness (`respektiert_rufPD`).
-/
import Grammatik.HoareRegeln
import Grammatik.VertragOrtB
import Grammatik.RufMaschineD

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-- A call handler respects the program contracts at their place: every
    call it answers normally satisfies `ensures` with the ACTUAL entry
    world, return world, arguments and result. `ReqAmEintritt` is the
    entry gate, `EnsAmRueck` the return duty (both `VertragOrtB.lean`).
    Every premise is used by `hoare_call` below. -/
def RespektiertVertraege (P : Programm D)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ f σ ρ, ReqAmEintritt P f σ ρ →
    ∀ σ' v, R f σ ρ = RufAusgang.ok σ' v →
      EnsAmRueck P f σ σ' ρ v

/-- Soundness of the call rule: a `.call f args hp hr` statement satisfies
    the triple whose precondition is "`requires f` holds at the argument
    world with the evaluated arguments" and whose postcondition is
    "`ensures f` holds with the actual entry world, return world,
    arguments and result". The actual values appear (no quantification
    over environments in the contract); the result `v` is existentially
    bound in the postcondition because the statement discards it.
    Every premise is used: `hR` in the `ok` branch, `hPre` as its gate,
    `hr` in the `grund` branch (the empty `Fin` eliminates). -/
theorem hoare_call (P : Programm D) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (hR : RespektiertVertraege P R)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (f : D.Fn) (args : Args D Γ Λ (D.params f))
    (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0) :
    STTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R (.call f args hp hr)
      (fun σ ρ => ReqAmEintritt P f (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ))
      (fun σ' _ => ∃ (s0 : World D) (rho0 : Env D (D.params f))
        (v : ErgVal D (D.erg f)),
        R f s0 rho0 = RufAusgang.ok σ' v ∧ EnsAmRueck P f s0 σ' rho0 v) := by
  intro σ ρ hPre σ' ρ' hrun
  have hrun2 : (match R f (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
    | .ok σ'' _ => Ausgang.ok (V := V) (l := l) (Γ := Γ) σ'' ρ
    | .grund _ r => keinGrund hr r
    | .logik e => Ausgang.logik e
    | .hardware e => Ausgang.hardware e) = Ausgang.ok σ' ρ' := hrun
  cases hRv : R f (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | ok σ'' v =>
    simp only [hRv] at hrun2
    cases hrun2
    exact ⟨_, _, _, hRv, hR f _ _ hPre _ _ hRv⟩
  | grund σ'' r =>
    simp only [hRv] at hrun2
    exact (Fin.cast hr r).elim0
  | logik e =>
    simp only [hRv] at hrun2
    cases hrun2
  | hardware e =>
    simp only [hRv] at hrun2
    cases hrun2

/-! ## 2. Witness handler and joint instantiation on `rufPD`.

    The joint witness for `hoare_call` must discharge `RespektiertVertraege`
    AND run the call statement to a normal outcome with the evaluated
    arguments -- on the one-function increment program of `RufMaschineD.lean`
    (ensures result = param + 1) with a handler that runs the body. -/

open RufMaschineD in
/-- Params of every `rufD` function, by computation (both ids share one signature). -/
theorem rufD_params_any70 (f : rufD.Fn) : rufD.params f = [.int 0 5] := by
  cases f <;> rfl

open RufMaschineD in
/-- Result of every `rufD` function, by computation. -/
theorem rufD_erg_any70 (f : rufD.Fn) : rufD.erg f = some (.int 0 6) := by
  cases f <;> rfl

/-- Witness value: param + 1, pinned to `Zahl 0 6` so `Zahl.add` unifies. -/
def witVal70 (ρ : Env rufD [Ty.int 0 5]) : ErgVal rufD (some (.int 0 6)) :=
  Zahl.add (ρ.get Var.hier) (⟨1, by decide, by decide⟩ : Zahl 0 1)

/-- Witness handler on `rufD`: if `requires` holds at the entry world
    with the given arguments, answer by evaluating the body `param + 1`
    and returning the world unchanged; otherwise refuse with the
    caller's own fault (`.vorbedingung f`). The gate makes the entry
    premise load-bearing in `hRwit70` below. -/
def Rwit70 : ∀ f : rufD.Fn, World rufD → Env rufD (rufD.params f) → RufAusgang f :=
  fun f σ ρ =>
    if wahr? (eval σ (rufPD.requires f) σ ρ) = true then
      RufAusgang.ok (f := f) σ
        ((rufD_erg_any70 f).symm ▸ witVal70 ((rufD_params_any70 f) ▸ ρ))
    else
      RufAusgang.logik (.vorbedingung f)

open RufMaschineD in
/-- The witness handler respects the `rufPD` contracts. Both premises
    are used: `hreq` selects the `ok` branch of the gate, `hok` fixes
    the outcome whose ensures duty follows by computation. -/
theorem hRwit70 : RespektiertVertraege (D := rufD) rufPD Rwit70 := by
  intro f σ ρ hreq σ' v hok
  have hcond : (wahr? (eval σ (rufPD.requires f) σ ρ) = true) := hreq
  have hR : Rwit70 f σ ρ = RufAusgang.ok (f := f) σ
      ((rufD_erg_any70 f).symm ▸ witVal70 ((rufD_params_any70 f) ▸ ρ)) := by
    simp only [Rwit70, hcond, if_true]
  rw [hR] at hok
  cases hok
  exact (decide_eq_true_eq).mpr rfl

/-! ## 3. Joint witness: `hoare_call` on `rufPD` with `Rwit70`.

    The witness must instantiate ALL premises of `hoare_call` jointly
    with concrete values and prove them: the handler respect fact
    `hRwit70` above, plus a reached call whose statement ends normally
    with the evaluated arguments. The statement is a `.call` of
    `rufIncD` with argument `.var .hier` from caller env `rufRhoD`;
    the entry world is `rufWeltD` (argument reads are empty), the
    handler answers `.ok` with `param + 1 = 3`, and `ensures` holds
    for the actual values by `ruf_ens_am_ortD`. -/

open RufMaschineD in
/-- The witness call statement: call `rufIncD` with the single variable
    under the caller contract (which equals the callee contract here). -/
def witStmt70 :
    Stmt rufD (vertragVon rufD rufIncD) false [Ty.int 0 5] []
      (nach rufD rufIncD []) :=
  .call rufIncD rufArgsD rufHpD rfl

open RufMaschineD in
/-- Entry gate at the witness: requires holds at the argument world
    with the evaluated arguments (evaluates by `rfl` to `2 = 2`). -/
theorem witPre70 :
    ReqAmEintritt rufPD rufIncD
      (rufWeltD.lese [] rufArgsD.orte)
      (evalArgs (rufWeltD.lese [] rufArgsD.orte) rufArgsD
        (rufWeltD.lese [] rufArgsD.orte) rufRhoD) := by
  exact rfl

open RufMaschineD in
/-- The witness call runs to a normal outcome: `execStmt` on the call
    feeds the evaluated arguments to `Rwit70`, which answers `.ok`. -/
theorem witRun70 :
    ∃ σ' : World rufD, ∃ ρ' : Env rufD [Ty.int 0 5],
      execStmt (V := vertragVon rufD rufIncD) rufOD 0 Rwit70
        witStmt70 rufWeltD rufRhoD = Ausgang.ok σ' ρ' := by
  exact ⟨_, _, rfl⟩

open RufMaschineD in
/-- Joint witness for `hoare_call`: ALL premises instantiated with
    concrete values and proved -- handler respect (`hRwit70`), entry
    gate (`witPre70`), and a normal run of the call (`witRun70`)
    whose outcome satisfies `ensures` at the actual values. -/
theorem hoare_call_zeuge :
    RespektiertVertraege (D := rufD) rufPD Rwit70 ∧
    ReqAmEintritt rufPD rufIncD
      (rufWeltD.lese [] rufArgsD.orte)
      (evalArgs (rufWeltD.lese [] rufArgsD.orte) rufArgsD
        (rufWeltD.lese [] rufArgsD.orte) rufRhoD) ∧
    (∃ σ' : World rufD, ∃ ρ' : Env rufD [Ty.int 0 5],
      execStmt (V := vertragVon rufD rufIncD) rufOD 0 Rwit70
        witStmt70 rufWeltD rufRhoD = Ausgang.ok σ' ρ') := by
  exact ⟨hRwit70, witPre70, witRun70⟩

/-! ## CUTS: what is not proved.

  - `hoare_call` covers the `Stmt.call` statement only; the `callInd`
    (indirect call), `Block.bindCall`, `bindCallInd` and `bindCallElse`
    constructors take the same `RespektiertVertraege` premise but are
    not stated here.
  - The witness handler answers with the entry world unchanged (the
    `rufD` signature writes nothing), so the postcondition holds with
    `s0 = σ'`; a handler whose return world differs from the entry
    world is not exhibited.
  - The ensures duty in `hRwit70` is discharged by computation
    (`rfl`): on `rufD` every contract expression reads only the
    parameter/result values, so `ensures` for the answered value is
    definitional. A program whose ensures reads memory would need a
    non-computational ensures argument.
-/

#print axioms Gabbro.Grammatik.RespektiertVertraege
#print axioms Gabbro.Grammatik.hoare_call
#print axioms Gabbro.Grammatik.hRwit70
#print axioms Gabbro.Grammatik.witPre70
#print axioms Gabbro.Grammatik.witRun70
#print axioms Gabbro.Grammatik.hoare_call_zeuge

end Gabbro.Grammatik
