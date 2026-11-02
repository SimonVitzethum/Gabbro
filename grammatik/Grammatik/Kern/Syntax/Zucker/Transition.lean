module

public import Grammatik.Kern.Syntax.Zucker.Transport

public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)} {l : Bool}

/-- Ordered transition places and typed endpoints. The exporter must capture
    indices and endpoints in private function parameters before any store.
    A declaration grants no write permission merely by listing a place. -/
inductive TransitionWrite (D : Deklaration) (Γ : Ctx) (Λ : List (Res D)) where
  | slot (table : D.Tab) (field : D.Feld table) {lo hi : Int}
      (numeric : D.typ table field = .int lo hi)
      (index : Expr D Γ Λ (.index (D.count table)))
      (source target : Expr D Γ Λ (.int lo hi)) (guard : darf D table Λ)
  | glob (global : D.Glob) {lo hi : Int} (numeric : D.gtyp global = .int lo hi)
      (source target : Expr D Γ Λ (.int lo hi)) (guard : gdarf D global Λ)

namespace TransitionWrite

/-- All operands are already captured parameters. This syntax condition
    prevents a later write from re-reading an earlier write's target. -/
inductive Frozen : TransitionWrite D Γ Λ → Prop where
  | slot (table : D.Tab) (field : D.Feld table) {lo hi : Int}
      (numeric : D.typ table field = .int lo hi)
      (index : Var Γ (.index (D.count table)))
      (source target : Var Γ (.int lo hi)) (guard : darf D table Λ) :
      Frozen (.slot table field numeric (.var index) (.var source) (.var target) guard)
  | glob (global : D.Glob) {lo hi : Int} (numeric : D.gtyp global = .int lo hi)
      (source target : Var Γ (.int lo hi)) (guard : gdarf D global Λ) :
      Frozen (.glob global numeric (.var source) (.var target) guard)

/-- Write effects remain the ordinary function's permissions. -/
@[expose] def Permitted (V : Vertrag D) : TransitionWrite D Γ Λ → Prop
  | .slot table .. => V.schreibt table = true
  | .glob global .. => V.gschreibt global = true

/-- The source-state equality, read under the declaration's real guards. -/
@[expose] def sourceEq : TransitionWrite D Γ Λ → Expr D Γ Λ .bool
  | .slot table field numeric index source _ guard =>
      .eq ((Expr.slot table field index guard).umTyp numeric) source
  | .glob global numeric source _ guard =>
      .eq ((Expr.glob global guard).umTyp numeric) source

/-- The target-state equality refers to captured parameters, never body locals. -/
@[expose] def targetEq : TransitionWrite D Γ Λ → Expr D Γ Λ .bool
  | .slot table field numeric index _ target guard =>
      .eq ((Expr.slot table field index guard).umTyp numeric) target
  | .glob global numeric _ target guard =>
      .eq ((Expr.glob global guard).umTyp numeric) target

/-- An ordinary checked store, with its existing range, effect and guard rules. -/
@[expose] def statement (write : TransitionWrite D Γ Λ) (right : write.Permitted V) :
    Stmt D V l Γ Λ Λ :=
  match write with
  | .slot table field numeric index _ target guard =>
      .assignSlot table field index (target.umTyp numeric.symm) right guard
  | .glob global numeric _ target guard =>
      .assignGlob global (target.umTyp numeric.symm) right guard

end TransitionWrite

/-- The explicit clause and every entry-state equality are caller duties. -/
@[expose] def transitionRequires (writes : List (TransitionWrite D Γ Λ)) (clause : Expr D Γ Λ .bool) :
    Expr D Γ Λ .bool :=
  writes.foldr (fun write rest => .and write.sourceEq rest) clause

/-- The postcondition uses the same captured target values as the stores. -/
@[expose] def transitionEnsures (writes : List (TransitionWrite D Γ Λ)) : Expr D Γ Λ .bool :=
  writes.foldr (fun write rest => .and write.targetEq rest) .tru

/-- Ordered ordinary stores followed by the caller-selected continuation.
    With no writes this is a requires-only transition. -/
@[expose] def transitionEnd (V : Vertrag D) (writes : List (TransitionWrite D Γ Λ))
    (rights : ∀ write ∈ writes, write.Permitted V) (rest : Endblock D V l Γ Λ) :
    Endblock D V l Γ Λ :=
  match writes with
  | [] => rest
  | write :: tail =>
      .cons (write.statement (rights write List.mem_cons_self))
        (transitionEnd V tail (fun next member => rights next (List.mem_cons_of_mem _ member)) rest)

/-- The generated function returns normally with exactly its required resources. -/
@[expose] def transitionReturn (V : Vertrag D) (void : V.erg = none) (resources : Λ.Perm V.ende) :
    Endblock D V false Γ Λ :=
  .ret (by rw [void]; exact .empty) resources

/-- The declaration certificate describes the actual ordinary function
    fragment. Callers must additionally prove capture provenance and the
    distinct-target/postcondition obligation before exporting a source use. -/
structure TransitionExpansion (P : Programm D) (function : D.Fn) where
  writes : List (TransitionWrite D (D.params function) (Signatur.anfang D (D.signatur function)))
  clause : Expr D (D.params function) (Signatur.anfang D (D.signatur function)) .bool
  frozen : ∀ write ∈ writes, write.Frozen
  rights : ∀ write ∈ writes, write.Permitted (vertragVon D function)
  result_none : D.erg function = none
  resources : Signatur.anfang D (D.signatur function) = (vertragVon D function).ende
  requires_exact : P.requires function = transitionRequires writes clause
  ensures_exact : P.ensures function = (by
    simpa only [result_none, ErgCtx, resources] using transitionEnsures writes)
  body_exact : P.rumpf function = transitionEnd (vertragVon D function) writes rights
    (transitionReturn (vertragVon D function) result_none (by rw [resources]; exact List.Perm.refl _))


end Gabbro.Grammatik
