module

public import Grammatik.Parser.Elab.ExportControl
public import Grammatik.Parser.Elab.UebersetzeSum
public import Grammatik.Bausteine.Arena.ArenaZucker
public import Grammatik.Parser.Namen.Oeffentlich
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.UebersetzeAllg3.Seq
public import Grammatik.Parser.Elab.UebersetzeAllg3.Struct
public import Grammatik.Parser.Elab.UebersetzeAllg3.Arme
public import Grammatik.Parser.Elab.UebersetzeAllg3.Ende

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg2

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000

/-- The lowerings at fuel level `n`: level `0` refuses (nesting too deep), level `n + 1` runs every step
    over level `n`. -/
def lowStufe (u : UProg) (caller : Fin u.fns.length) : Nat → LowStufe u caller
  | 0 => ⟨fun _ _ _ _ _ => .error "lower: blocks nested too deep",
      fun _ _ _ _ _ _ => .error "lower: blocks nested too deep",
      fun _ _ _ _ _ _ _ => .error "lower: blocks nested too deep",
      fun _ _ _ _ _ _ => .error "lower: blocks nested too deep",
      fun _ _ _ _ _ => .error "lower: blocks nested too deep"⟩
  | n + 1 =>
    let R := lowStufe u caller n
    ⟨lowSeqStep u caller R, lowStructStep u caller R, lowArmsStep u caller R, lowGArmsStep u caller R,
      lowEndStep u caller R⟩

/-- A flat run of statements at `Λ`, up to (not including) the `zu`/`sonst` marker that ends it, or the
    end of the list; returns the block and what is left. A `let` binds for the rest of the run: its
    type is the COMPUTED range of the value (as the exporter pushes it) and the scope grows by it.
    Structural in the fuel. -/
def lowSeqL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn) (n : Nat)
    (Λ : List (Res (declOf u))) (pe : AtTop u caller Λ) (ss : List UStmt) :=
  (lowStufe u caller n).seq (l := l) Γ fn Λ pe ss

/-- The structured statements, each with the rest of the run after its body: `locks g { … }` (the lock
    by name, the rank rule; no `return` inside), `if c { … } else { … }` and `traverse` (its body is a
    block with `l = true`, the binder an index into the table, the invariant read in the OUTER scope). -/
def lowStructL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn) (n : Nat)
    (Λ : List (Res (declOf u))) (pe : AtTop u caller Λ) (s : UStmt) (ss : List UStmt) :=
  (lowStufe u caller n).struct (l := l) Γ fn Λ pe s ss

/-- The arms of a tagged match: one block per case of the specification, the payload of a case with one bound by
    the next binder name, separated by `ifElse`; the marker that closes the match is left to the caller. -/
def lowArmsT {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn) (n : Nat)
    (Λ : List (Res (declOf u))) (pe : AtTop u caller Λ) (cs : List (Option (Int × Int))) (bs : List String) (ss : List UStmt) :=
  (lowStufe u caller n).arms (l := l) Γ fn Λ pe cs bs ss

/-- The arms of a reason match: `m` blocks, one per reason, separated by `ifElse`; the marker that closes the
    match is left to the caller. -/
def lowGArmsL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn) (n : Nat)
    (Λ : List (Res (declOf u))) (pe : AtTop u caller Λ) (m : Nat) (ss : List UStmt) :=
  (lowStufe u caller n).garms (l := l) Γ fn Λ pe m ss

/-- The `else` branch of a narrowing as an end block: its statements and the ender (`return`, `leave`, `next`),
    which must not fall through; the marker `blkEnd` that closes the branch is left to the caller. -/
def lowEndL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn) (n : Nat)
    (Λ : List (Res (declOf u))) (pe : AtTop u caller Λ) (ss : List UStmt) :=
  (lowStufe u caller n).ende (l := l) Γ fn Λ pe ss

/-- The record of level `n` is the five lowerings at fuel `n`: proofs that unfold a step fold its calls back. -/
@[simp] theorem lowStufe_seq (u : UProg) (caller : Fin u.fns.length) (n : Nat) {l : Bool} (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (pe : AtTop u caller Λ) (ss : List UStmt) :
    (lowStufe u caller n).seq (l := l) Γ fn Λ pe ss = lowSeqL u caller Γ fn n Λ pe ss := rfl

@[simp] theorem lowStufe_struct (u : UProg) (caller : Fin u.fns.length) (n : Nat) {l : Bool} (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (pe : AtTop u caller Λ) (s : UStmt) (ss : List UStmt) :
    (lowStufe u caller n).struct (l := l) Γ fn Λ pe s ss = lowStructL u caller Γ fn n Λ pe s ss := rfl

@[simp] theorem lowStufe_arms (u : UProg) (caller : Fin u.fns.length) (n : Nat) {l : Bool} (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (pe : AtTop u caller Λ) (cs : List (Option (Int × Int))) (bs : List String)
    (ss : List UStmt) :
    (lowStufe u caller n).arms (l := l) Γ fn Λ pe cs bs ss = lowArmsT u caller Γ fn n Λ pe cs bs ss := rfl

@[simp] theorem lowStufe_garms (u : UProg) (caller : Fin u.fns.length) (n : Nat) {l : Bool} (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (pe : AtTop u caller Λ) (m : Nat) (ss : List UStmt) :
    (lowStufe u caller n).garms (l := l) Γ fn Λ pe m ss = lowGArmsL u caller Γ fn n Λ pe m ss := rfl

@[simp] theorem lowStufe_ende (u : UProg) (caller : Fin u.fns.length) (n : Nat) {l : Bool} (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (pe : AtTop u caller Λ) (ss : List UStmt) :
    (lowStufe u caller n).ende (l := l) Γ fn Λ pe ss = lowEndL u caller Γ fn n Λ pe ss := rfl

/-- One fuel level of each lowering is its step over the level below. -/
theorem lowStructL_succ (u : UProg) (caller : Fin u.fns.length) (n : Nat) {l : Bool} (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (pe : AtTop u caller Λ) (s : UStmt) (ss : List UStmt) :
    lowStructL (l := l) u caller Γ fn (n + 1) Λ pe s ss = lowStructStep u caller (lowStufe u caller n) Γ fn Λ pe s ss :=
  rfl

theorem lowEndL_succ (u : UProg) (caller : Fin u.fns.length) (n : Nat) {l : Bool} (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (pe : AtTop u caller Λ) (ss : List UStmt) :
    lowEndL (l := l) u caller Γ fn (n + 1) Λ pe ss = lowEndStep u caller (lowStufe u caller n) Γ fn Λ pe ss := rfl

end Gabbro.Grammatik.Parser.UebersetzeAllg2
