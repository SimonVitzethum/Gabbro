/-
  File:      Grammatik/ReferenzZeuge.lean
  Subject:   WITNESSES for `&T` (table pointers, `Ty.ptr` / `Expr.ptrOf`).

  WHAT WAS PRESENT (no change needed, pinned here by probes):
  * `Expr.ptrOf` / `Ty.ptr` (Syntax.lean), `zeiger_hat_waechter`,
    `zeiger_schreibt_mit_recht`, `exec_rahmen` (Satz.lean) -- proved;
  * `ecorr_ptrOf`, `ptrOk_sound`, `exOk_sound` (KorrespondenzAllg.lean) -- proved;
  * `kostenExpr .ptrOf = 0`, `kostenStmt .assignDurch` (KostenG.lean) -- defined;
  * `antwortTyB .ptr = true`, `einpassen_voll` at `.ptr`, `antwortB_iff`
    (EinpassenVoll.lean) -- a pointer type always answers (`()`), so the
    answer component (`antwortenB`, Zielsatz/Akzeptiert.lean) needs no new
    acceptance for `&T`.

  WHAT WAS MISSING (added here):
  * (a) No probe pinned the `ptrOf` arm of `exOk`: an arm that accepts a
    wrong row is worse than a missing arm (KorrespondenzWeitZeuge.lean
    header rule). `probe_ptrOf` is the positive probe plus three planted
    defects -- the nominal (`M140`-side) refusals: a different table number,
    a plain local, a global address.
  * (b) The nominal acceptance itself was unnamed: `ht : D.tabNr n = some t`
    travels as a proof obligation, with no Bool the transfer can decide.
    `ptrTypB` names it, `ptrTypB_iff` decides it exactly, `ptrTypB_zeuge`
    is the non-degenerate witness (accepts `0`, refuses `1`). The REST of
    `M140` (general shape equality at parameter slots) has no Lean
    counterpart by construction: ill-typed terms are unrepresentable, so
    there is nothing to decide.
  * (c) No joint witness instantiated the `&T` lemmas together on one
    fixture: `ecorr_ptrOf_zeuge` (correspondence through `exOk_sound`,
    with the wrong-table refusal beside it), `zeiger_hat_waechter_zeuge`,
    `zeiger_schreibt_mit_recht_zeuge` (the two Satz inversions on one
    `durch` / `assignDurch`), `antwort_ptr_zeuge` (answerable, against
    `.never`), `kosten_ptr_zeuge` (pointer costs `0`, the through-access
    counts).

  Fixture: the one of `KorrespondenzWeitZeuge.lean` (`wD`: one table of four
  `u32` slots, `tabNr 0 = some ()`; `wEL`, `wK`, `wV`, `wX`). One table
  suffices: number `1` names no table, which is exactly the nominal refusal.
  Everything is `decide`/`rfl`: no `sorry`, no `axiom`, no `native_decide`.
-/
import Grammatik.KorrespondenzWeitZeuge
import Grammatik.EinpassenVoll
import Grammatik.KostenG
import Grammatik.Satz

namespace Gabbro.Grammatik.ReferenzZeuge

open Gabbro.Grammatik
open Gabbro.Grammatik.WeitZeuge

/-! ## 1. The nominal acceptance of `&T` (the `M140` side in Lean) -/

/-- **The number `n` names the table `t`** -- the `ht` proof obligation of
    `Expr.ptrOf` / `Expr.durch` / `Stmt.assignDurch` as a Bool. -/
def ptrTypB {D : Deklaration} (n : Nat) (t : D.Tab) : Bool :=
  decide (D.tabNr n = some t)

/-- It decides exactly the naming equation. -/
theorem ptrTypB_iff {D : Deklaration} {n : Nat} {t : D.Tab} :
    ptrTypB (D := D) n t = true ↔ D.tabNr n = some t := by
  simp only [ptrTypB, decide_eq_true_eq]

/-- **WITNESS, non-degenerate**: on `wD`, number `0` names the table and
    number `1` names nothing -- the acceptance accepts one and refuses
    another. -/
theorem ptrTypB_zeuge :
    ptrTypB (D := wD) 0 () = true ∧ ptrTypB (D := wD) 1 () = false := by
  decide

/-! ## 2. The `ptrOf` arm: accepted and refused -/

/-- `&T` against its own table block, and three planted defects: a different
    table number (the nominal refusal), a plain local, a global address. -/
theorem probe_ptrOf :
    exOk wEL wK (Expr.ptrOf (D := wD) (Γ := wCtx) (Λ := []) () 0 rfl false)
        (.addr (.tab 0)) = true ∧
    exOk wEL wK (Expr.ptrOf (D := wD) (Γ := wCtx) (Λ := []) () 0 rfl false)
        (.addr (.tab 1)) = false ∧
    exOk wEL wK (Expr.ptrOf (D := wD) (Γ := wCtx) (Λ := []) () 0 rfl false)
        (.var 0) = false ∧
    exOk wEL wK (Expr.ptrOf (D := wD) (Γ := wCtx) (Λ := []) () 0 rfl false)
        (.addr (.glob 0)) = false := by
  decide

/-- **WITNESS for `ecorr_ptrOf`**: the accepted row corresponds (through
    `exOk_sound`), and the wrong table's row is refused beside it -- so the
    witness is not vacuous. -/
theorem ecorr_ptrOf_zeuge :
    exOk wEL wK (Expr.ptrOf (D := wD) (Γ := wCtx) (Λ := []) () 0 rfl false)
        (.addr (.tab 0)) = true ∧
    exOk wEL wK (Expr.ptrOf (D := wD) (Γ := wCtx) (Λ := []) () 0 rfl false)
        (.addr (.tab 1)) = false ∧
    ExprCorr wX wK (.addr (.tab 0))
      (Expr.ptrOf (D := wD) (Γ := wCtx) (Λ := []) () 0 rfl false) := by
  refine ⟨by decide, by decide, ?_⟩
  exact exOk_sound wX wK _ _ (by decide)

/-! ## 3. One pointer read and write on the fixture -/

/-- No guard is needed on `wD` (nothing is shared, nothing guarded). -/
theorem zDarfW : darf wD () [] :=
  fun _ hw => absurd hw List.not_mem_nil

/-- Index `0` of four slots. -/
def zIdxW : Expr wD [] [] (.index (wD.count ())) :=
  .weiter (by decide) (by decide) (.lit 0)

/-- The `rw` pointer to the table. -/
def zPtrW : Expr wD [] [] (.ptr 0 true) :=
  .ptrOf () 0 rfl true

/-- A `u32` value. -/
def zWertW : Expr wD [] [] wU32 :=
  .weiter (by decide) (by decide) (.lit 0)

/-- The read through the pointer. -/
def zDurchW : Expr wD [] [] wU32 :=
  .durch zPtrW () rfl () zIdxW zDarfW

/-- The write through the pointer. -/
def zSchreibW : Stmt wD wV false [] [] [] :=
  .assignDurch zPtrW () rfl () zIdxW zWertW rfl zDarfW

/-- **WITNESS for `zeiger_hat_waechter`**: the read carries the guard,
    beside the nominal refusal (number `1` names no table) so the pair is
    non-degenerate. -/
theorem zeiger_hat_waechter_zeuge : darf wD () [] ∧ ptrTypB (D := wD) 1 () = false :=
  ⟨zeiger_hat_waechter zDurchW rfl, by decide⟩

/-- A read-only sibling contract: same fixture, no write right. -/
def zV0 : Vertrag wD := { wV with schreibt := fun _ => false }

/-- **WITNESS for `zeiger_schreibt_mit_recht`**: the write carries the right
    under `wV`, beside a sibling contract that grants nothing -- so the pair
    accepts one and refuses another. -/
theorem zeiger_schreibt_mit_recht_zeuge : wV.schreibt () = true ∧ zV0.schreibt () = false :=
  ⟨zeiger_schreibt_mit_recht zSchreibW rfl, rfl⟩

/-! ## 4. Answers and cost at pointer type -/

/-- **WITNESS**: a pointer type answers (value `()`), against `.never`,
    which does not -- non-degenerate. -/
theorem antwort_ptr_zeuge :
    antwortTyB (D := wD) [] (.ptr 0 true) = true ∧
    antwortTyB (D := wD) [] .never = false ∧
    ∃ _ : Wert wD (.ptr 0 true), True := by
  refine ⟨rfl, rfl, ⟨(), trivial⟩⟩

/-- So its answer class is not empty -- beside the `.never` class, which is. -/
theorem antwort_ptr_nicht_leer : ¬ AntwortLeer wD (some (.ptr 0 true)) :=
  ((antwortB_iff (fs := []) (fun (g : wD.Fn) => nomatch g) (some (.ptr 0 true))).mp rfl)

/-- **WITNESS pair**: `.never` answers nothing. -/
theorem antwort_never_leer_zeuge : AntwortLeer wD (some .never) :=
  antwortLeer_never

/-- **WITNESS**: the pointer itself costs `0`; the through-read and the
    through-write count pointer, index and value. -/
theorem kosten_ptr_zeuge :
    kostenExpr (D := wD) zPtrW = 0 ∧
    kostenExpr (D := wD) zIdxW = 1 + kostenExpr (D := wD) ((.lit 0) : Expr wD [] [] (.int 0 0)) ∧
    kostenStmt (D := wD) (fun _ => 0) 0 zSchreibW =
      1 + kostenExpr (D := wD) zPtrW + kostenExpr (D := wD) zIdxW +
        kostenExpr (D := wD) zWertW := by
  refine ⟨rfl, rfl, rfl⟩

#print axioms Gabbro.Grammatik.ReferenzZeuge.ptrTypB_iff
#print axioms Gabbro.Grammatik.ReferenzZeuge.ptrTypB_zeuge
#print axioms Gabbro.Grammatik.ReferenzZeuge.probe_ptrOf
#print axioms Gabbro.Grammatik.ReferenzZeuge.ecorr_ptrOf_zeuge
#print axioms Gabbro.Grammatik.ReferenzZeuge.zeiger_hat_waechter_zeuge
#print axioms Gabbro.Grammatik.ReferenzZeuge.zeiger_schreibt_mit_recht_zeuge
#print axioms Gabbro.Grammatik.ReferenzZeuge.antwort_ptr_zeuge
#print axioms Gabbro.Grammatik.ReferenzZeuge.antwort_ptr_nicht_leer
#print axioms Gabbro.Grammatik.ReferenzZeuge.antwort_never_leer_zeuge
#print axioms Gabbro.Grammatik.ReferenzZeuge.kosten_ptr_zeuge

end Gabbro.Grammatik.ReferenzZeuge
