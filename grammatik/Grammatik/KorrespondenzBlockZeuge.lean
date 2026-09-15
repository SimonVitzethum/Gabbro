/-
  File:      Grammatik/KorrespondenzBlockZeuge.lean
  Subject:   PROBES for the BLOCK structure of the correspondence
             certificate (`KorrespondenzAllg.lean`: `blOk`, and the `stOk`
             arms that carry a block).

  WHY THIS FILE EXISTS. The block rows are the first rows of `korrOk` that
  carry OTHER ROWS, and a check over a row list can go wrong in ways a flat
  row cannot: it can take the `else` arm for the `then` arm, it can let an
  arm be SHORTER than the Gabbro block it is supposed to be, and it can
  bind a loop or a call result to a local that the rows after it do not
  read. So every new arm gets BOTH probes:
  * a POSITIVE probe -- the emitted form the arm is meant to accept;
  * a PLANTED DEFECT -- exactly the mistake the arm exists to catch.

  THE FIXTURES. The first is the one of `KorrespondenzWeitZeuge.lean`
  (`wD`, `wEL`, `wK`: one table `T` of four `u32` slots, two `u32`
  parameters in C locals `0` and `1`), so that the probes below add a
  block structure over a statement stock that is already probed. The
  second (`cD`, section 3) is the same declaration with ONE function,
  because `wD` has `Fn := Empty` and a call needs a callee.

  Everything is `decide`: the check is a Bool, and a probe that needed a
  proof would be probing something else.
-/
import Grammatik.KorrespondenzWeitZeuge

namespace Gabbro.Grammatik.BlockZeuge

open Gabbro.Grammatik Gabbro.Grammatik.WeitZeuge

/-! ## 1. The two arms of an `if` -/

/-- The C cell type of the fixture's locals. -/
abbrev bU32c : CTy := .int false .w32

/-- `a = 1;` -- ONE statement, and the `else` arm's is a different one, so
    "the two branches swapped" is a defect the probe can see. -/
def bArmT : Block wD wV false wCtx [] [] :=
  .cons (Stmt.assignVar .hier (.weiter (by decide) (by decide) (Expr.lit 1))) .nil

/-- `a = 2;` -/
def bArmE : Block wD wV false wCtx [] [] :=
  .cons (Stmt.assignVar .hier (.weiter (by decide) (by decide) (Expr.lit 2))) .nil

/-- `if (a < b) { a = 1; } else { a = 2; }` -/
def bIte : Stmt wD wV false wCtx [] [] := .ite (Expr.lt x0 x1) bArmT bArmE

def bRowT : GRow := .setVar 0 bU32c (.lit 1)
def bRowE : GRow := .setVar 0 bU32c (.lit 2)
def bCond : CX := .cmp .lt CIT.u32 (.var 0) (.var 1)

/-- The `if` row, accepted and refused. The PLANTED DEFECTS are the four
    ways a block check can be wrong where a flat one cannot: the two
    branches swapped, a statement DROPPED from one branch (in both
    branches, separately), a statement ADDED to one branch -- and, for
    completeness, the condition read as the opposite comparison. -/
theorem probe_ite :
    stOk wEL wFnum wZert wK bIte (.ite bCond [bRowT] [bRowE]) = true ∧
    stOk wEL wFnum wZert wK bIte (.ite bCond [bRowE] [bRowT]) = false ∧
    stOk wEL wFnum wZert wK bIte (.ite bCond [] [bRowE]) = false ∧
    stOk wEL wFnum wZert wK bIte (.ite bCond [bRowT] []) = false ∧
    stOk wEL wFnum wZert wK bIte (.ite bCond [bRowT, bRowE] [bRowE]) = false ∧
    stOk wEL wFnum wZert wK bIte
      (.ite (.cmp .ge CIT.u32 (.var 0) (.var 1)) [bRowT] [bRowE]) = false := by
  decide

/-- An `if` row against a statement that is NOT an `if` is refused, and a
    non-`if` row against the `if` statement is refused: the arm reads the
    Gabbro side, not only the C side. -/
theorem probe_ite_fremd :
    stOk wEL wFnum wZert wK bIte bRowT = false ∧
    stOk wEL wFnum wZert wK
      (Stmt.assignVar (V := wV) (l := false) (Λ := []) .hier
        (.weiter (by decide) (by decide) (Expr.lit 1)))
      (.ite bCond [bRowT] [bRowE]) = false := by
  decide

/-! ## 2. The block check itself

    `blOk` walks a `Block` (an arm, later a loop body) against its rows.
    It is the same reading `enOk` gives a terminal block, minus the
    `return` -- a block ENDS, it does not answer. -/

/-- `(void)a; a = 1;` -- the unused-parameter row and a statement. -/
theorem probe_blOk_void :
    blOk wEL wFnum wZert wK bArmT [.void 0, bRowT] = true ∧
    blOk wEL wFnum wZert wK bArmT [.void 7, bRowT] = false ∧
    blOk wEL wFnum wZert wK bArmT [bRowT] = true ∧
    blOk wEL wFnum wZert wK bArmT [] = false ∧
    blOk wEL wFnum wZert wK (Block.nil (D := wD) (V := wV) (l := false)
      (Γ := wCtx) (Λ := [])) [bRowT] = false ∧
    blOk wEL wFnum wZert wK (Block.nil (D := wD) (V := wV) (l := false)
      (Γ := wCtx) (Λ := [])) [] = true := by
  decide

/-- `let t = a; a = t;` inside a block: the `let` binds C local `2`, and the
    row after it must READ that local. PLANTED DEFECTS: the `let` bound to
    a local that is already a parameter (not fresh), and the `let` bound to
    a local the following row does not read. -/
def bLetBlock : Block wD wV false wCtx [] [] :=
  .bind (τ := wU32) x0 (.cons (Stmt.assignVar (.dort .hier) (Expr.var .hier)) .nil)

theorem probe_blOk_let :
    blOk wEL wFnum wZert wK bLetBlock
      [.bindLet 2 bU32c (.var 0), .setVar 0 bU32c (.var 2)] = true ∧
    blOk wEL wFnum wZert wK bLetBlock
      [.bindLet 1 bU32c (.var 0), .setVar 0 bU32c (.var 1)] = false ∧
    blOk wEL wFnum wZert wK bLetBlock
      [.bindLet 3 bU32c (.var 0), .setVar 0 bU32c (.var 2)] = false ∧
    blOk wEL wFnum wZert wK bLetBlock
      [.bindLet 2 bU32c (.var 1), .setVar 0 bU32c (.var 2)] = false := by
  decide

/-! ## 3. `let y = g(a);` -- the call whose ANSWER is bound

    `wD` has no functions at all (`Fn := Empty`), so the row that binds a
    call's answer needs its own fixture: `cD` is `wD` with ONE function
    `g(a : u32) -> u32` (signature `1`; signature `0` is the caller's).
    The certificate gives `g` C function number `0`, one parameter in C
    local `0`, and the exporter's map. -/

def cD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 4
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => wU32
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Bool
  decGlob := inferInstance
  gtyp := fun _ => wU32
  nutzlast := fun _ => []
  atomar := fun g => g
  geteilt := fun _ => false
  ggeteilt := fun _ => false
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => nomatch m
  braucht := fun _ => []
  gbraucht := fun _ => []
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 1
  sigNr := fun n =>
    match n with
    | 0 =>
      { params := [wU32, wU32], erg := none, gruende := 0, haelt := [],
        schreibt := fun _ => true, gschreibt := fun _ => true, konsumiert := [],
        produziert := [] }
    | _ =>
      { params := [wU32], erg := some wU32, gruende := 0, haelt := [],
        schreibt := fun _ => true, gschreibt := fun _ => true, konsumiert := [],
        produziert := [] }
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Empty
  aparams := fun a => nomatch a
  aerg := fun a => nomatch a
  aschreibt := fun a => nomatch a
  agschreibt := fun a => nomatch a
  Reg := Empty
  rtyp := fun r => nomatch r
  rklasse := fun r => nomatch r
  spiegel := fun r => nomatch r
  rzusage := fun r => nomatch r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g h => by simp at h

def cEL : EmitLay cD where
  lay := wLay
  tnr := fun _ => 0
  tnr_inj := fun t t' _ => by cases t; cases t'; rfl
  trec := fun _ => wRec
  lay_tab := fun _ => rfl
  trec_wf := fun _ => by decide
  trec_count := fun _ => rfl
  fnr := fun _ _ => 0
  fnr_lt := fun _ _ => by decide
  fnr_inj := fun _ f f' _ => by cases f; cases f'; rfl
  fnr_fits := fun _ _ => rfl
  gnr := fun g => cond g 1 0
  gnr_inj := fun g g' h => by
    cases g
    · cases g'
      · rfl
      · exact absurd h (by decide)
    · cases g'
      · exact absurd h (by decide)
      · rfl
  gty := fun _ => .int false .w32
  lay_glob := fun g => by cases g <;> rfl
  gty_fits := fun _ => rfl

def cK : CEnvLay cD wCtx := ⟨[0, 1], [], []⟩

/-- The CALLER's contract (signature `0`). -/
abbrev cV : Vertrag cD := Vertrag.vonSig cD (cD.sigNr 0)

/-- `g` is C function number `0`. -/
def cFnum : cD.Fn → Nat := fun _ => 0

/-- The certificate: one function, one `u32` parameter in C local `0`, the
    exporter's map (`callMapOk`). Its own rows are not read by the call
    row's arm, so they are empty here. -/
def cZert : KCert cD :=
  [{ params := [(0, bU32c)], locals := [], rows := [], vm := [0], pp := [], ks := [] }]

def cx0 : Expr cD wCtx [] wU32 := .var .hier

theorem cHp : RufPasst cD cV (cD.signatur ()) [] where
  hw := fun _ _ => rfl
  hg := fun _ _ => rfl
  hk := ⟨[], List.Perm.refl [], by simp⟩
  hh := fun L => nomatch L

/-- `let y = g(a); a = y;` -- the answer is bound to a fresh local AND the
    row after it reads exactly that local. -/
def cLetCall : Block cD cV false wCtx [] [] :=
  .bindCall () (.cons cx0 .nil) rfl cHp rfl
    (.cons (Stmt.assignVar (.dort .hier) (Expr.var .hier)) .nil)

/-- The call-with-answer row, accepted and refused. PLANTED DEFECTS, in
    order: the answer bound to a local the FOLLOWING ROW does not read
    (the wrong local -- the check sees it because the rows after the
    binder are read under the PUSHED map); the answer bound to a
    parameter (not fresh); the wrong C function number; the wrong
    argument; the wrong declared C type; and the answer DISCARDED, which
    is a different C statement and a different Gabbro form. -/
theorem probe_bindCall :
    blOk cEL cFnum cZert cK cLetCall
      [.call 0 [.var 0] (some (2, bU32c)), .setVar 0 bU32c (.var 2)] = true ∧
    blOk cEL cFnum cZert cK cLetCall
      [.call 0 [.var 0] (some (3, bU32c)), .setVar 0 bU32c (.var 2)] = false ∧
    blOk cEL cFnum cZert cK cLetCall
      [.call 0 [.var 0] (some (1, bU32c)), .setVar 0 bU32c (.var 1)] = false ∧
    blOk cEL cFnum cZert cK cLetCall
      [.call 1 [.var 0] (some (2, bU32c)), .setVar 0 bU32c (.var 2)] = false ∧
    blOk cEL cFnum cZert cK cLetCall
      [.call 0 [.var 1] (some (2, bU32c)), .setVar 0 bU32c (.var 2)] = false ∧
    blOk cEL cFnum cZert cK cLetCall
      [.call 0 [.var 0] (some (2, .int false .w16)), .setVar 0 bU32c (.var 2)] = false ∧
    blOk cEL cFnum cZert cK cLetCall
      [.call 0 [.var 0] none, .setVar 0 bU32c (.var 2)] = false := by
  decide

/-- The callee's map must be its C PARAMETER LIST (`callMapOk`): a
    certificate whose callee carries a map that is not the parameter list
    is refused at the call site, and so is a missing callee. -/
def cZertKrumm : KCert cD :=
  [{ params := [(0, bU32c)], locals := [], rows := [], vm := [1], pp := [], ks := [] }]

def cZertLeer : KCert cD := []

theorem probe_bindCall_karte :
    blOk cEL cFnum cZertKrumm cK cLetCall
      [.call 0 [.var 0] (some (2, bU32c)), .setVar 0 bU32c (.var 2)] = false ∧
    blOk cEL cFnum cZertLeer cK cLetCall
      [.call 0 [.var 0] (some (2, bU32c)), .setVar 0 bU32c (.var 2)] = false := by
  decide

/-! ## 4. `traverse` -- the counting loop

    The table `T` of the fixture has four slots, so the emitted header is
    `for (uint32_t v = 0; v < 4; v += 1)`. Three things the arm decides
    that `scorr_traverse` assumes: the bound is the table's count, the
    loop variable is fresh, and the BODY DOES NOT WRITE the loop
    variable. Each of the three is a planted defect below. -/

/-- The loop body's context: the index, then the two parameters. -/
abbrev bTravCtx : Ctx := Ty.index (wD.count ()) :: wCtx

/-- `traverse T { a = 1; }` -- the body writes a PARAMETER (C local `0`),
    not the loop variable. -/
def bTravBody : Block wD wV true bTravCtx [] [] :=
  .cons (Stmt.assignVar (.dort .hier) (.weiter (by decide) (by decide) (Expr.lit 1))) .nil

def bTrav : Stmt wD wV false wCtx [] [] := .traverse () Expr.wahr bTravBody

/-- The same loop, with a body that writes the LOOP VARIABLE (`v = 0;`).
    The model allows the statement; `scorr_traverse` does not cover it
    (`hw`), so the check must REFUSE its row -- and the refusal is the
    hygiene check, not a mismatch of the rows. -/
def bTravBodySchreibt : Block wD wV true bTravCtx [] [] :=
  .cons (Stmt.assignVar .hier (.weiter (by decide) (by decide) (Expr.lit 0))) .nil

def bTravSchreibt : Stmt wD wV false wCtx [] [] := .traverse () Expr.wahr bTravBodySchreibt

/-- The loop row, accepted and refused. PLANTED DEFECTS: the WRONG LOOP
    BOUND (too high, too low, and not a constant at all), the loop
    variable taken from the parameters (not fresh), the body one
    statement short, the body one statement too long, and the body's one
    statement replaced by a different one. -/
theorem probe_forTrav :
    stOk wEL wFnum wZert wK bTrav (.forTrav 2 CIT.u32 (.lit 4) [bRowT] 0) = true ∧
    stOk wEL wFnum wZert wK bTrav (.forTrav 2 CIT.u32 (.lit 5) [bRowT] 0) = false ∧
    stOk wEL wFnum wZert wK bTrav (.forTrav 2 CIT.u32 (.lit 3) [bRowT] 0) = false ∧
    stOk wEL wFnum wZert wK bTrav (.forTrav 2 CIT.u32 (.var 1) [bRowT] 0) = false ∧
    stOk wEL wFnum wZert wK bTrav (.forTrav 0 CIT.u32 (.lit 4) [bRowT] 0) = false ∧
    stOk wEL wFnum wZert wK bTrav (.forTrav 2 CIT.u32 (.lit 4) [] 0) = false ∧
    stOk wEL wFnum wZert wK bTrav (.forTrav 2 CIT.u32 (.lit 4) [bRowT, bRowT] 0) = false ∧
    stOk wEL wFnum wZert wK bTrav (.forTrav 2 CIT.u32 (.lit 4) [bRowE] 0) = false := by
  decide

/-- A loop whose body writes the loop variable is refused, and its row is
    the one that MATCHES the body -- so the refusal is `scorr_traverse`'s
    `hw` premise and nothing else. -/
theorem probe_forTrav_hygiene :
    stOk wEL wFnum wZert wK bTravSchreibt
      (.forTrav 2 CIT.u32 (.lit 4) [.setVar 2 bU32c (.lit 0)] 0) = false := by
  decide

/-- A loop row against a statement that is not a loop, and a loop
    statement against a row that is not a loop row. -/
theorem probe_forTrav_fremd :
    stOk wEL wFnum wZert wK bIte (.forTrav 2 CIT.u32 (.lit 4) [bRowT] 0) = false ∧
    stOk wEL wFnum wZert wK bTrav (.ite bCond [bRowT] [bRowE]) = false := by
  decide

/-! ## 5. The recursion NESTS: an `if` inside a `traverse` -/

def by0 : Expr wD bTravCtx [] wU32 := .var (.dort .hier)
def by1 : Expr wD bTravCtx [] wU32 := .var (.dort (.dort .hier))

def bNestT : Block wD wV true bTravCtx [] [] :=
  .cons (Stmt.assignVar (.dort .hier) (.weiter (by decide) (by decide) (Expr.lit 1))) .nil

def bNestE : Block wD wV true bTravCtx [] [] :=
  .cons (Stmt.assignVar (.dort .hier) (.weiter (by decide) (by decide) (Expr.lit 2))) .nil

/-- `traverse T { if (a < b) { a = 1; } else { a = 2; } }` -/
def bNestBody : Block wD wV true bTravCtx [] [] :=
  .cons (Stmt.ite (Expr.lt by0 by1) bNestT bNestE) .nil

def bNest : Stmt wD wV false wCtx [] [] := .traverse () Expr.wahr bNestBody

/-- Two levels of row list, and the check still reads both -- with the
    branches swapped at the INNER level as the planted defect. -/
theorem probe_nested :
    stOk wEL wFnum wZert wK bNest
      (.forTrav 2 CIT.u32 (.lit 4) [.ite bCond [bRowT] [bRowE]] 0) = true ∧
    stOk wEL wFnum wZert wK bNest
      (.forTrav 2 CIT.u32 (.lit 4) [.ite bCond [bRowE] [bRowT]] 0) = false ∧
    stOk wEL wFnum wZert wK bNest
      (.forTrav 2 CIT.u32 (.lit 4) [.ite bCond [bRowT] []] 0) = false ∧
    stOk wEL wFnum wZert wK bNest
      (.forTrav 2 CIT.u32 (.lit 5) [.ite bCond [bRowT] [bRowE]] 0) = false := by
  decide

#print axioms Gabbro.Grammatik.BlockZeuge.probe_ite
#print axioms Gabbro.Grammatik.BlockZeuge.probe_ite_fremd
#print axioms Gabbro.Grammatik.BlockZeuge.probe_forTrav
#print axioms Gabbro.Grammatik.BlockZeuge.probe_forTrav_hygiene
#print axioms Gabbro.Grammatik.BlockZeuge.probe_forTrav_fremd
#print axioms Gabbro.Grammatik.BlockZeuge.probe_nested
#print axioms Gabbro.Grammatik.BlockZeuge.probe_blOk_void
#print axioms Gabbro.Grammatik.BlockZeuge.probe_blOk_let
#print axioms Gabbro.Grammatik.BlockZeuge.probe_bindCall
#print axioms Gabbro.Grammatik.BlockZeuge.probe_bindCall_karte

end Gabbro.Grammatik.BlockZeuge
