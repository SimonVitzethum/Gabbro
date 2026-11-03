/-
  File:      Grammatik/Parser/Elab/UebersetzeAllg3.lean
  Subject:   T3 PART 7: generic lowering, third part: statement runs (`lowSeqL`: `let`, `locks`, `if`,
             `traverse`, early `return`), bodies, `lowerAllg`, and the 104/108 pins and the chain.
             Split from `UebersetzeAllg2` (which keeps the single statements and calls); same namespace.
-/
module

import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
public import Grammatik.Parser.Elab.UebersetzeAllg3.Returns
public import Grammatik.Parser.Elab.UebersetzeSum
public import Grammatik.Bausteine.Arena.ArenaZucker
public import Grammatik.Parser.Namen.Oeffentlich
import all Init.Data.Repr
@[expose] public section


namespace Gabbro.Grammatik.Parser.UebersetzeAllg2

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000

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

/-- **`let i = alloc A (v);`** without `else` as the sugar `Block.arenaAllocRequired` of
    `ArenaZucker`: the same arena form, rights and guards as `mkAllocBlock`, but the counter
    narrowing is required -- a full arena is `Logik.kapazitaet`, excluded by the caller's
    capacity duty (`KoerperGutS/SA`), never a failure continuation. -/
def mkAllocRequiredBlock {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (t : Fin u.tabs.length) (g : Fin u.globs.length) (fh : FieldHit u t)
    (ev0 : Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2))
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
              .ok (Block.arenaAllocRequired (D := declOf u) A ev hwT' hLT hwG' hLG b)
            else .error "access without held guard"
          else .error "access without held guard"
        else .error "write without right"
      else .error "write without right"
    else .error "arena of no slots"
  else .error "arena counter foreign"

/-- **`let i = alloc A (v) else { .. };` at the end of a body** as the sugar
    `Endblock.arenaAlloc` of `ArenaZucker`: the same arena form, rights and
    guards as `mkAllocBlock`, but the success continuation is an end block. -/
def mkAllocEndBlock {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (t : Fin u.tabs.length) (g : Fin u.globs.length) (fh : FieldHit u t)
    (ev0 : Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2))
    (voll : Endblock (declOf u) (verOf u caller) l Γ Λ)
    (b : Endblock (declOf u) (verOf u caller) l (Ty.index ((declOf u).count t) :: Γ) Λ) :
    Except String (Endblock (declOf u) (verOf u caller) l Γ Λ) :=
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
              .ok (Endblock.arenaAlloc (D := declOf u) A ev hwT' hLT hwG' hLG voll b)
            else .error "access without held guard"
          else .error "access without held guard"
        else .error "write without right"
      else .error "write without right"
    else .error "arena of no slots"
  else .error "arena counter foreign"

/-- **`let i = alloc A (v);` at the end of a body** as the sugar
    `Endblock.arenaAllocRequired` of `ArenaZucker`: the same arena form, rights
    and guards as `mkAllocRequiredBlock`, but the success continuation is an end
    block -- a full arena is `Logik.kapazitaet`, excluded by the caller's
    capacity duty, never a failure continuation. -/
def mkAllocRequiredEndBlock {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (t : Fin u.tabs.length) (g : Fin u.globs.length) (fh : FieldHit u t)
    (ev0 : Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2))
    (b : Endblock (declOf u) (verOf u caller) l (Ty.index ((declOf u).count t) :: Γ) Λ) :
    Except String (Endblock (declOf u) (verOf u caller) l Γ Λ) :=
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
              .ok (Endblock.arenaAllocRequired (D := declOf u) A ev hwT' hLT hwG' hLG b)
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
    its own file (`lowStufe` ties the levels), with exactly the results of the former `mutual` block.
    Calls change the held resources (`nach`), so runs thread the out-list: `seq` and `struct` return
    it (joins decide equality); match arms and structured bodies preserve it (decided); end blocks
    pin the entry list. -/
structure LowStufe (u : UProg) (caller : Fin u.fns.length) where
  seq : {l : Bool} → (Γ : Ctx) → UFn → (Λ : List (Res (declOf u))) → AtTop u caller Λ → List UStmt →
    Except String ((Σ Λ' : List (Res (declOf u)), Block (declOf u) (verOf u caller) l Γ Λ Λ') × List UStmt)
  struct : {l : Bool} → (Γ : Ctx) → UFn → (Λ : List (Res (declOf u))) → AtTop u caller Λ → UStmt → List UStmt →
    Except String ((Σ Λ' : List (Res (declOf u)), Stmt (declOf u) (verOf u caller) l Γ Λ Λ') × List UStmt)
  arms : {l : Bool} → (Γ : Ctx) → UFn → (Λ : List (Res (declOf u))) → AtTop u caller Λ →
    (cs : List (Option Ty)) → List String → List UStmt →
    Except String (Arms (declOf u) (verOf u caller) l Γ Λ Λ cs × List UStmt)
  garms : {l : Bool} → (Γ : Ctx) → UFn → (Λ : List (Res (declOf u))) → AtTop u caller Λ → (m : Nat) →
    List UStmt → Except String (GrundArms (declOf u) (verOf u caller) l Γ Λ Λ m × List UStmt)
  ende : {l : Bool} → (Γ : Ctx) → UFn → (Λ : List (Res (declOf u))) → AtTop u caller Λ → List UStmt →
    Except String (Endblock (declOf u) (verOf u caller) l Γ Λ × List UStmt)

end Gabbro.Grammatik.Parser.UebersetzeAllg2
