/-
  File:      Grammatik/Parser/Elab/UebersetzeAllg3.lean
  Subject:   T3 PART 7: generic lowering, third part: statement runs (`lowSeqL`: `let`, `locks`, `if`,
             `traverse`, early `return`), bodies, `lowerAllg`, and the 104/108 pins and the chain.
             Split from `UebersetzeAllg2` (which keeps the single statements and calls); same namespace.
-/
module
public import Grammatik.Parser.Elab.ExportControl
public import Grammatik.Parser.Elab.UebersetzeSum
public import Grammatik.Bausteine.Arena.ArenaZucker
public import Grammatik.Parser.Namen.Oeffentlich
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
@[expose] public section


namespace Gabbro.Grammatik.Parser.UebersetzeAllg2

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000

/-! ## Returns -/

/-- The held resources are the contract end, as a `Perm`. -/
theorem endPerm_ok (u : UProg) (caller : Fin u.fns.length) :
    (resOf u caller).Perm (verOf u caller).ende := by
  show ((heldAt u (fnAt u caller)).map
    (Res.held (D := declOf u))).Perm (verOf u caller).ende
  rw [show (verOf u caller).ende =
    (vertragVon (declOf u) caller).ende from rfl, ende_eq u caller]

/-- The value of a return, at the function's held resources `resOf`. -/
def lowErg (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn) : URet →
    Except String (ErgExpr (declOf u) Γ (resOf u caller) (verOf u caller).erg)
  | .keins => .error "fn with a result falls off"
  | .empty =>
    match hE : (fnAt u caller).ergTy with
    | none =>
      have hV : (verOf u caller).erg = none := by
        show (vertragVon (declOf u) caller).erg = none
        rw [vErg_eq u caller, hE]
      have eK : ErgExpr (declOf u) Γ (resOf u caller) (verOf u caller).erg := by
        rw [hV]
        exact ErgExpr.empty
      .ok eK
    | some _ => .error "return without value with result"
  | .val s =>
    match hE : (fnAt u caller).ergTy with
    | some (.int lo hi) =>
      match lowWertAt u Γ (resOf u caller) fn lo hi s with
      | .error e => .error e
      | .ok v =>
        have eW : ErgExpr (declOf u) Γ (resOf u caller) (verOf u caller).erg := by
          rw [show (verOf u caller).erg =
            (vertragVon (declOf u) caller).erg from rfl,
            vErg_eq u caller, hE]
          show ErgExpr (declOf u) Γ (resOf u caller) (Option.some (.int lo hi))
          exact ErgExpr.val v
        .ok eW
    | some _ => .error "number returned for a non-number result"
    | none => .error "return with value without result"
  | .why _ => .error "reason as a value without G form"
  | .wert s =>
    match hE : (fnAt u caller).ergTy with
    | some τ =>
      match lowWertAtE u Γ (resOf u caller) fn none τ s with
      | .error e => .error e
      | .ok v =>
        have eW : ErgExpr (declOf u) Γ (resOf u caller) (verOf u caller).erg := by
          rw [show (verOf u caller).erg =
            (vertragVon (declOf u) caller).erg from rfl,
            vErg_eq u caller, hE]
          exact ErgExpr.val v
        .ok eW
    | none => .error "return with value without result"
  | .grund g =>
    match hE : (fnAt u caller).ergTy with
    | some (.why n) =>
      match lowGrund u Γ (resOf u caller) fn n g with
      | .error e => .error e
      | .ok v =>
        have eW : ErgExpr (declOf u) Γ (resOf u caller) (verOf u caller).erg := by
          rw [show (verOf u caller).erg =
            (vertragVon (declOf u) caller).erg from rfl,
            vErg_eq u caller, hE]
          exact ErgExpr.val v
        .ok eW
    | some _ => .error "reason returned for a non-reason result"
    | none => .error "return with value without result"
  | .sum v =>
    match hE : (fnAt u caller).ergTy with
    | some (.sum cs) =>
      match (fnAt u caller).resSum with
      | some (sidx, _) =>
        if hs : sidx < u.sums.length then
          if hc : (u.sums.get ⟨sidx, hs⟩).spec = cs then
            match lowSVal u Γ (resOf u caller) fn 0 sidx hs v with
            | .error e => .error e
            | .ok ev =>
              have eW : ErgExpr (declOf u) Γ (resOf u caller) (verOf u caller).erg := by
                rw [show (verOf u caller).erg =
                  (vertragVon (declOf u) caller).erg from rfl,
                  vErg_eq u caller, hE]
                show ErgExpr (declOf u) Γ (resOf u caller) (Option.some (.sum cs))
                exact ErgExpr.val (by rw [← hc]; exact ev)
              .ok eW
          else .error "result type foreign"
        else .error "tagged type unknown"
      | none => .error "tagged result without type"
    | some _ => .error "tagged value returned for a different result"
    | none => .error "return with value without result"
  | .opt o =>
    match hE : (fnAt u caller).ergTy with
    | some (.opt n) =>
      match (fnAt u caller).resOpt with
      | some (num, _) =>
        if hnum : num < u.tabs.length then
          if hn : (declOf u).count ⟨num, hnum⟩ = n then
            match lowOpt u Γ (resOf u caller) fn 0 num hnum o with
            | .error e => .error e
            | .ok v =>
              have eW : ErgExpr (declOf u) Γ (resOf u caller) (verOf u caller).erg := by
                rw [show (verOf u caller).erg =
                  (vertragVon (declOf u) caller).erg from rfl,
                  vErg_eq u caller, hE]
                show ErgExpr (declOf u) Γ (resOf u caller) (Option.some (.opt n))
                exact ErgExpr.val (by rw [← hn]; exact v)
              .ok eW
          else .error "option result table foreign"
        else .error "option table unknown"
      | none => .error "option result without table"
    | some _ => .error "option returned for a non-option result"
    | none => .error "return with value without result"
  | .bool b =>
    match hE : (fnAt u caller).ergTy with
    | some .bool =>
      match lowEns u Γ (resOf u caller) fn none b with
      | .error e => .error e
      | .ok v =>
        have eW : ErgExpr (declOf u) Γ (resOf u caller) (verOf u caller).erg := by
          rw [show (verOf u caller).erg =
            (vertragVon (declOf u) caller).erg from rfl,
            vErg_eq u caller, hE]
          exact ErgExpr.val v
        .ok eW
    | some _ => .error "truth value returned for a non-bool result"
    | none => .error "return with value without result"

/-- The return a body ends with when every path already ended (`URet.keins`, set by the elaborator only then,
    `uEndetTief`): unreachable, so any value of the result type; refused where none is at hand. -/
def keinsWert : Option Ty → Option URet
  | some (.int lo _) => some (.val (.lit lo))
  | some (.opt _) => some (.opt .nichts)
  | some .bool => some (.bool .fls)
  | _ => none

/-- The trailing return. -/
def lowEnd (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn) (r0 : URet) :
    Except String (Endblock (declOf u) (verOf u caller) false Γ (resOf u caller)) :=
  let r := match r0 with
    | .keins => (keinsWert (fnAt u caller).ergTy).getD .keins
    | r => r
  match r with
  | .why i =>
    if h : i < (verOf u caller).gruende then .ok (Endblock.retWhy (D := declOf u) ⟨i, h⟩ (endPerm_ok u caller))
    else .error "reason case outside the channel"
  | _ =>
  match lowErg u caller Γ fn r with
  | .error e => .error e
  | .ok e => .ok (Endblock.ret e (endPerm_ok u caller))

/-- `Λ` is exactly the function's held resources (not inside a `locks` block): where a `return` may
    stand (`Stmt.ret` needs `Λ` to be the contract end). -/
abbrev AtTop (u : UProg) (caller : Fin u.fns.length) (Λ : List (Res (declOf u))) : Type :=
  Option (PLift (Λ = resOf u caller))

/-- A `return` inside a block, at the top held list only. -/
def lowRetStmt {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (pe : AtTop u caller Λ) (r : URet) :
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ) :=
  match pe with
  | none => .error "lower: return under locks has no G form"
  | some ⟨h⟩ =>
    match r with
    | .why i =>
      if hi : i < (verOf u caller).gruende then
        .ok (by subst h; exact Stmt.retWhy (D := declOf u) ⟨i, hi⟩ (endPerm_ok u caller))
      else .error "reason case outside the channel"
    | _ =>
    match lowErg u caller Γ fn r with
    | .error e => .error e
    | .ok erg =>
      .ok (by subst h; exact Stmt.ret erg (endPerm_ok u caller))

/-- The rank rule of `locks L`: every held lock ranks below `L` (`H006`), as a Bool. -/
def rangOkB (u : UProg) (Λ : List (Res (declOf u))) (L : (declOf u).Lock) : Bool :=
  (heldLocksD u Λ).all fun M => decide ((declOf u).rang M < (declOf u).rang L)

theorem rangOkB_sound (u : UProg) (Λ : List (Res (declOf u))) (L : (declOf u).Lock)
    (h : rangOkB u Λ L = true) :
    ∀ M, Res.held (D := declOf u) M ∈ Λ → (declOf u).rang M < (declOf u).rang L := by
  intro M hM
  have hm := heldLocksD_mem u Λ M hM
  unfold rangOkB at h
  have := List.all_eq_true.mp h M hm
  exact of_decide_eq_true this

/-- The result type of a callee, for a binding (`he` of `Block.bindCall`); a callee without a value binds nothing. -/
def withErgN {α : Type} (u : UProg) (n : Nat)
    (K : (τ : Ty) → ((declOf u).sigNr n).erg = some τ → Except String α) : Except String α :=
  match hE : ((declOf u).sigNr n).erg with
  | none => .error "call without a value"
  | some τ => K τ hE

def withErg {α : Type} (u : UProg) (callee : Fin u.fns.length)
    (K : (τ : Ty) → (declOf u).erg callee = some τ → Except String α) : Except String α :=
  match hE : (declOf u).erg callee with
  | none => .error "call without a value"
  | some τ => K τ hE

/-- **`let i = alloc A (v) else { .. };`** as the sugar `Block.arenaAlloc` of `ArenaZucker`: the arena's table,
    its element field and its counter static form the `ArenaForm`; the stores need the write rights and the
    guards at both carriers. -/
def mkAllocBlock {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (t : Fin u.tabs.length) (g : Fin u.globs.length) (fh : FieldHit u t)
    (ev0 : Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2))
    (voll : Endblock (declOf u) (verOf u caller) l Γ Λ)
    (b : Block (declOf u) (verOf u caller) l (Ty.index ((declOf u).count t) :: Γ) Λ Λ) :
    Except String (Block (declOf u) (verOf u caller) l Γ Λ Λ) :=
  if hz : (declOf u).gtyp g = Ty.int 0 ((declOf u).count t) then
    if hp : 0 < (declOf u).count t then
      let A : ArenaForm (declOf u) := { tab := t, feld := fh.idx, zaehl := g, hz := hz, hpos := hp }
      have ev : Expr (declOf u) Γ Λ ((declOf u).typ t fh.idx) := by
        show Expr (declOf u) Γ Λ (typAt u t fh.idx)
        rw [fh.hint]
        exact ev0
      if hwT : writesAt u (fnAt u caller) t = true then
        if hwG : writesGAt u (fnAt u caller) g = true then
          if hLT : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ then
            if hLG : ∀ wdd ∈ (declOf u).gbraucht g, Res.von (declOf u) wdd ∈ Λ then
              have hwT' : (verOf u caller).schreibt t = true := by
                show (vertragVon (declOf u) caller).schreibt t = true
                rw [vSchreibt_eq u caller t]
                exact hwT
              have hwG' : (verOf u caller).gschreibt g = true := by
                show (vertragVon (declOf u) caller).gschreibt g = true
                rw [vGSchreibt_eq u caller g]
                exact hwG
              .ok (Block.arenaAlloc (D := declOf u) A ev hwT' hLT hwG' hLG voll b)
            else .error "access without held guard"
          else .error "access without held guard"
        else .error "write without right"
      else .error "write without right"
    else .error "arena of no slots"
  else .error "arena counter foreign"

/-! ## Runs of statements -/

/-- The new value of an exchange: the guarded values of an `update` body as nested `Expr.wenn`, at the static's
    type `τ`. -/
def lowTauschNeu (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (τ : Ty) :
    List (UEns × USide) → USide → Except String (Expr (declOf u) Γ Λ τ)
  | [], s => lowWertAtE u Γ Λ fn none τ s
  | (c, e) :: rest, s =>
    match lowEns u Γ Λ fn none c, lowWertAtE u Γ Λ fn none τ e, lowTauschNeu u Γ Λ fn τ rest s with
    | .ok c', .ok e', .ok r' => .ok (Expr.wenn c' e' r')
    | .error x, _, _ | _, .error x, _ | _, _, .error x => .error x


/-- **The five lowerings one fuel level down**, as a lowering at the next level calls them. The
    lowerings of statements, blocks, match arms, reason arms and end blocks call each other one fuel level
    down; giving the step at level `n + 1` the record of level `n` keeps every step a plain definition in
    its own file (`lowStufe` ties the levels), with exactly the results of the former `mutual` block. -/
structure LowStufe (u : UProg) (caller : Fin u.fns.length) where
  seq : {l : Bool} → (Γ : Ctx) → UFn → (Λ : List (Res (declOf u))) → AtTop u caller Λ → List UStmt →
    Except String (Block (declOf u) (verOf u caller) l Γ Λ Λ × List UStmt)
  struct : {l : Bool} → (Γ : Ctx) → UFn → (Λ : List (Res (declOf u))) → AtTop u caller Λ → UStmt → List UStmt →
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ × List UStmt)
  arms : {l : Bool} → (Γ : Ctx) → UFn → (Λ : List (Res (declOf u))) → AtTop u caller Λ →
    (cs : List (Option (Int × Int))) → List String → List UStmt →
    Except String (Arms (declOf u) (verOf u caller) l Γ Λ Λ cs × List UStmt)
  garms : {l : Bool} → (Γ : Ctx) → UFn → (Λ : List (Res (declOf u))) → AtTop u caller Λ → (m : Nat) →
    List UStmt → Except String (GrundArms (declOf u) (verOf u caller) l Γ Λ Λ m × List UStmt)
  ende : {l : Bool} → (Γ : Ctx) → UFn → (Λ : List (Res (declOf u))) → AtTop u caller Λ → List UStmt →
    Except String (Endblock (declOf u) (verOf u caller) l Γ Λ × List UStmt)

end Gabbro.Grammatik.Parser.UebersetzeAllg2
