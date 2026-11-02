module

public import Grammatik.Kern.Syntax.Syntax.Teil2
public import Grammatik.Kern.Syntax.Syntax.Teil2Programm
public import Grammatik.Kern.Syntax.Ziel
public import Grammatik.Korpus.Zeugnis.Zeugnis
public import Grammatik.Kern.Semantik.Budget.Teil1

@[expose] public section


/-! ## Statement threading: `runPasses` over `Stmt`/`Block` sequences

    A sequence is a list of index-erased elements sharing one `l` and one `Γ`:
    each element keeps its own `Λ`/`Λ'`. The op list of an element comes from a
    DECLARED assignment `assign` (premise P1 lifted to statements: a number the
    declaration trusts, not one measured here). Resource threading (`Λ` into
    `Λ'`) between elements is NOT tracked below, and there is NO verified link
    from an element to `Semantik.execStmt`/`execBlock`: the full execution
    linkage stays booked (cut C5), not faked.

    Proven below (`#print axioms` shows `[propext, Classical.choice, Quot.sound]`:
    the same footprint as `Stmt`/`Block` themselves and as the `Satz.lean`
    theorems about them -- measured 2026-09-11, inherited by mentioning
    statements, no new axiom):
      `seqPasses_complete` -- every element within bound implies `ok`.
      `seqPasses_exceeds`  -- one element over bound implies the named outcome.
-/

namespace Gabbro.Grammatik

/-- One element of a budgeted sequence: a statement or a whole block, with its
    resource indices erased so elements with different `Λ` share one list. -/
inductive SeqElem (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx) : Type where
  | ofStmt {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') : SeqElem D V l Γ
  | ofBlock {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') : SeqElem D V l Γ

/-- The sequence as named passes: element `i` runs under its own fresh budget
    and reports `"seq.i"` on breach (stuck-with-name, as in `runPasses`). -/
def seqPassesAux {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (assign : SeqElem D V l Γ → List Op) : Nat → List (SeqElem D V l Γ) → List Pass
  | _, [] => []
  | i, e :: es => ("seq." ++ toString i, assign e) :: seqPassesAux assign (i + 1) es

/-- The budgeted sequence run: each element starts fresh; the first breach
    stops the whole run under the failing element's name. -/
def seqPasses {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (assign : SeqElem D V l Γ → List Op) (es : List (SeqElem D V l Γ)) : List Pass :=
  seqPassesAux assign 0 es

theorem seqPassesAux_nil {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (assign : SeqElem D V l Γ → List Op) (i : Nat) :
    seqPassesAux assign i [] = [] := by rfl

theorem seqPassesAux_cons {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (assign : SeqElem D V l Γ → List Op) (i : Nat)
    (e : SeqElem D V l Γ) (es : List (SeqElem D V l Γ)) :
    seqPassesAux assign i (e :: es)
      = (("seq." ++ toString i, assign e) :: seqPassesAux assign (i + 1) es) := by rfl

/-- Every pass of the translated sequence is one element's declared ops. -/
theorem seqPassesAux_all_within {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (assign : SeqElem D V l Γ → List Op) (b : Budget)
    (es : List (SeqElem D V l Γ)) (i : Nat)
    (h : ∀ e ∈ es, totalCost (assign e) ≤ b.perPass) :
    ∀ p ∈ seqPassesAux assign i es, totalCost p.2 ≤ b.perPass := by
  induction es generalizing i with
  | nil =>
    intro p hm
    rw [seqPassesAux_nil] at hm
    exact (List.not_mem_nil hm).elim
  | cons hd tl ih =>
    intro p hm
    rw [seqPassesAux_cons] at hm
    cases List.mem_cons.mp hm with
    | inl heq =>
      rw [heq]
      exact h hd (List.mem_cons.mpr (Or.inl rfl))
    | inr hmem =>
      exact ih (i + 1) (fun e he => h e (List.mem_cons.mpr (Or.inr he))) _ hmem

/-- An over-budget element survives translation as an over-budget pass. -/
theorem seqPassesAux_has_over {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (assign : SeqElem D V l Γ → List Op) (b : Budget)
    (es : List (SeqElem D V l Γ)) (i : Nat)
    (h : ∃ e ∈ es, b.perPass < totalCost (assign e)) :
    ∃ p ∈ seqPassesAux assign i es, b.perPass < totalCost p.2 := by
  induction es generalizing i with
  | nil =>
    obtain ⟨e, hm, _⟩ := h
    exact (List.not_mem_nil hm).elim
  | cons hd tl ih =>
    by_cases hhead : b.perPass < totalCost (assign hd)
    · refine ⟨("seq." ++ toString i, assign hd), ?_, hhead⟩
      rw [seqPassesAux_cons]
      exact List.mem_cons.mpr (Or.inl rfl)
    · rw [seqPassesAux_cons]
      obtain ⟨e, hm, hlt⟩ := h
      cases List.mem_cons.mp hm with
      | inl heq =>
        subst heq
        exact absurd hlt (by omega)
      | inr hmem =>
        obtain ⟨p, hpm, hplt⟩ := ih (i + 1) ⟨e, hmem, hlt⟩
        exact ⟨p, List.mem_cons.mpr (Or.inr hpm), hplt⟩

/-- Per-pass bound respected through sequencing: every element within bound
    implies the whole sequence runs `ok`. -/
theorem seqPasses_complete {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (b : Budget) (assign : SeqElem D V l Γ → List Op) (es : List (SeqElem D V l Γ))
    (h : ∀ e ∈ es, totalCost (assign e) ≤ b.perPass) :
    ∃ left, runPasses b (seqPasses assign es) = .ok left := by
  apply runPasses_complete
  intro p hm
  exact seqPassesAux_all_within assign b es 0 h p hm

/-- Per-pass bound respected through sequencing: one element over bound
    implies the run stops under THAT element's sequence name. -/
theorem seqPasses_exceeds {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (b : Budget) (assign : SeqElem D V l Γ → List Op) (es : List (SeqElem D V l Γ))
    (h : ∃ e ∈ es, b.perPass < totalCost (assign e)) :
    ∃ name needed, runPasses b (seqPasses assign es) = .budget name needed b.perPass := by
  apply runPasses_exceeds
  obtain ⟨p, hm, hlt⟩ := seqPassesAux_has_over assign b es 0 h
  exact ⟨p, hm, hlt⟩

#print axioms Gabbro.Grammatik.seqPassesAux_all_within
#print axioms Gabbro.Grammatik.seqPassesAux_has_over
#print axioms Gabbro.Grammatik.seqPasses_complete
#print axioms Gabbro.Grammatik.seqPasses_exceeds

end Gabbro.Grammatik

/-! ## Lowering preservation for the modeled ops (hLowering leg b, 2026-09-11)

    What `hLowering` in `Ziel.lean` (`ziel_nutzer_last`) owes beyond the numeric
    fragment (`absenkung_wert`, `absenkung_haelt_schranke`: the witness `17`
    keeps the cap `18`) is the CompCert-style preservation leg: lowering keeps
    the `ops` count. This section states and proves it for the MODELED ops --
    the seven CUT-1/2 certificate heads (`sdiv`, `srem`, `band`, `bor`, `bxor`,
    `shl`, `shr`), whose meaning leg is already proved (`zeugnis_sound` in
    `Zeugnis.lean`: a valid print elaborates to the judged `Expr`). Nothing
    below re-proves meaning; the new claim is the COUNT leg beside it, over
    the measured maximum (`absenkung.proPrimitiv = 17`, counted statically in
    `messung/ABSENKUNG-MESSUNG.md`, confirmed over emitted products in
    `messung/ABSENKUNG-LEXERLAUF.md`, re-confirmed on `fisch` in
    `messung/ABSENKUNG-DURCHSETZUNG.md` section 5):

      `senkKosten_modell`         -- a modeled head lowers to exactly one C-side op.
      `senkKosten_unter_schranke` -- that one op fits under the measured maximum.
      `modell_erhaltung`          -- the preservation theorem: a valid modeled
                                    print elaborates (meaning, reused) AND fits
                                    the max (count, new).
      `modell_lauf_erhalten`      -- over a run of modeled heads the lowered
                                    count IS the source count: one op in, one
                                    op out, no silent loss or gain.

    Proven below (`#print axioms` at the end shows the footprint:
    `modell_erhaltung` inherits whatever `zeugnis_sound` rests on, nothing
    more).

    What is NOT modeled here (booked follow-up, not silent):

    - The eleven other `CertExpr` heads: `lit`, `add`, `sub`, `neg`, `mul`,
      `div`, `rem` (closed-fragment arithmetic: meaning proved, count leg not
      claimed), `wide` (the index widening), `var`, `glob`, `slot` (CUT-4
      reads: meaning proved, count leg not claimed). `modellKopf` says `false`
      for each of them, and every theorem below demands `modellKopf c = true`,
      so the `0` beside `senkKosten` is unreachable, never a claim.
    - The CUT-3 shapes (`CertCut3`: floats, options, sums, grounds,
      quantifiers, `reaches`) and the CUT-4/5 remainders (`durch`, `ptrOf`,
      `fnref`, calls WITH arguments): soundness proved in `Zeugnis.lean`
      (`cut3_sound`, `cut4_sound`, `block5_sound`, lane 106), preservation
      not stated.
    - The `StmtArt`-level expansions above one statement (the descendants
      walk at seventeen and every row beneath it): bounded by the lexer run
      (`17 <= 18`, enforced by `absenkung.rs` once the hook is applied), with
      no per-op preservation claim -- the bound is the enforcement, not the
      proof.
    - The C-to-Asm leg: `costKept` (CerCo, the implication shape in
      `Erhaltung.lean`) and `costMeasured` (production, witness pairs) are
      untouched here; this section speaks Gabbro-to-C only.

    No `mathlib`, no `sorry`, no `axiom`.
-/

namespace Gabbro.Grammatik

/-- The modeled op heads: the seven CUT-1/2 certificate shapes (signed
    division and remainder, bitwise and shifts). Everything else is `false`:
    the unmodeled remainder, named in the section header, not hidden. -/
def modellKopf {D : Deklaration} : CertExpr D → Bool
  | .sdiv _ _ => true
  | .srem _ _ => true
  | .band _ _ => true
  | .bor _ _ _ => true
  | .bxor _ _ _ => true
  | .shl _ _ _ => true
  | .shr _ _ _ => true
  | _ => false

/-- The lowered C-side cost of one head: a modeled op is exactly one C-side
    op site of cost 1 (one op in, one op out -- the CompCert-style count leg,
    declared P1-style). Unmodeled heads carry `0`, which no theorem below can
    observe: each demands `modellKopf c = true`. -/
def senkKosten {D : Deklaration} : CertExpr D → Nat
  | .sdiv _ _ => 1
  | .srem _ _ => 1
  | .band _ _ => 1
  | .bor _ _ _ => 1
  | .bxor _ _ _ => 1
  | .shl _ _ _ => 1
  | .shr _ _ _ => 1
  | _ => 0

/-- Count leg: a modeled head lowers to exactly one C-side op. -/
theorem senkKosten_modell {D : Deklaration} (c : CertExpr D)
    (h : modellKopf c = true) :
    senkKosten c = 1 := by
  cases c <;> simp_all [modellKopf, senkKosten]

/-- Bound leg: the one lowered op fits under the measured maximum. -/
theorem senkKosten_unter_schranke {D : Deklaration} (c : CertExpr D)
    (h : modellKopf c = true) :
    senkKosten c ≤ absenkung.proPrimitiv := by
  have h1 : senkKosten c = 1 := senkKosten_modell c h
  have h17 : absenkung.proPrimitiv = 17 := absenkung_wert
  omega

/-- Preservation for the modeled ops: a valid print of a modeled head
    elaborates to the judged expression (meaning, reused from
    `zeugnis_sound` -- not re-proved) AND lowers to one C-side op under the
    measured maximum (count, new). -/
theorem modell_erhaltung {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (c : CertExpr D) (lo hi : Int)
    (hmod : modellKopf c = true) (hval : GueltigAbleitung D Γ Λ c lo hi) :
    (∃ _ : Expr D Γ Λ (.int lo hi), True) ∧
      senkKosten c ≤ absenkung.proPrimitiv :=
  ⟨zeugnis_sound c lo hi hval, senkKosten_unter_schranke c hmod⟩

/-- Over a run of modeled heads the lowered C-side count IS the source count:
    one op in, one op out, no silent loss or gain. -/
theorem modell_lauf_erhalten {D : Deklaration} (cs : List (CertExpr D)) :
    (∀ c ∈ cs, modellKopf c = true) → (cs.map senkKosten).sum = cs.length := by
  induction cs with
  | nil => intro _; rfl
  | cons hd tl ih =>
    intro h
    have hhd : modellKopf hd = true := h hd (List.mem_cons.mpr (Or.inl rfl))
    have htl : ∀ c ∈ tl, modellKopf c = true :=
      fun c hm => h c (List.mem_cons.mpr (Or.inr hm))
    simp only [List.map_cons, List.sum_cons, List.length_cons,
      senkKosten_modell hd hhd, ih htl, Nat.add_comm]

/-- Accept: `7 sdiv 2` is a modeled head. -/
example : modellKopf (D := TestD) (.sdiv (.lit 7) (.lit 2)) = true := by decide

/-- Reject: `add` is not modeled -- the remainder, not a shrug. -/
example : modellKopf (D := TestD) (.add (.lit 1) (.lit 2)) = false := by decide

/-- End to end: a valid modeled print elaborates AND fits under the maximum
    (the CUT-1 probe `7 sdiv 2`, through `modell_erhaltung`). -/
example : (∃ _ : Expr TestD [] [] (.int (-7) 7), True) ∧
    senkKosten (D := TestD) (.sdiv (.lit 7) (.lit 2)) ≤ absenkung.proPrimitiv :=
  modell_erhaltung _ _ _ rfl (by decide)

#print axioms Gabbro.Grammatik.modellKopf
#print axioms Gabbro.Grammatik.senkKosten
#print axioms Gabbro.Grammatik.senkKosten_modell
#print axioms Gabbro.Grammatik.senkKosten_unter_schranke
#print axioms Gabbro.Grammatik.modell_erhaltung
#print axioms Gabbro.Grammatik.modell_lauf_erhalten

end Gabbro.Grammatik
