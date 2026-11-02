module

public import Grammatik.Parser.Elab.Export.ExportControl
public import Grammatik.Parser.Elab.UebersetzeSum
public import Grammatik.Bausteine.Arena.ArenaZucker
public import Grammatik.Parser.Namen.Oeffentlich
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
public import Grammatik.Kern.Syntax.Extensions.Zucker.TransitionShift

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg2

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000

/-! ## Generated transition functions

The function a transition declaration generates is NOT lowered statement by
statement: its requires, ensures and body are built as the typed expansion
(`transitionRequires`, `transitionEnsures`, `transitionEnd`, or the
primitive shift), over the captured parameters of the generated function.
The declaration clause and the capture provenance go through the ordinary
predicate reader. The function is admitted only if it is exactly what
`uGenerateTransition` generates for its declaration. -/

/-- The ensures type of a lowered function. -/
abbrev EnsTy (u : UProg) (f : Fin u.fns.length) :=
  Expr (declOf u) (ErgCtx ((declOf u).params f) ((declOf u).erg f))
    (vertragVon (declOf u) f).ende .bool

/-- The body type of a lowered function. -/
abbrev RumpTy (u : UProg) (f : Fin u.fns.length) :=
  Endblock (declOf u) (vertragVon (declOf u) f) false
    ((declOf u).params f)
    (Signatur.anfang (declOf u) ((declOf u).signatur f))

/-- The requires type of a lowered function. -/
abbrev ReqTy (u : UProg) (f : Fin u.fns.length) :=
  Expr (declOf u) ((declOf u).params f) (Signatur.anfang (declOf u) ((declOf u).signatur f)) .bool

/-- The cast of a lowered piece to its declaration type, with its law. -/
@[expose] def transCast {α β : Sort _} (h : α = β) (x : α) : β := cast h x

theorem transCast_heq {α β : Sort _} (h : α = β) (x : α) : HEq (transCast h x) x :=
  cast_heq h x

/-- The declaration and clause a generated function belongs to. -/
@[expose] def transitionOfFn (u : UProg) (c : Fin u.fns.length) : Option (UZustand × UTransition) :=
  u.zustaende.findSome? fun state =>
    (state.transitions.find? fun tr => !tr.primitive &&
        strEq (uTransitionFunction state.name tr.name) (fnAt u c).name).map fun tr => (state, tr)

/-- The captured parameter of the generated function by name and type. -/
@[expose] def lowCaptured (fn : UFn) (Γ : Ctx) (name : String) (τ : Ty) : Except String (Var Γ τ) :=
  match paramPos fn.params name with
  | .error e => .error e
  | .ok j => lowVar Γ j τ

/-- The typed snapshot store of the write at `position`: every operand is a
    captured parameter, the permission is the function's own contract. -/
@[expose] def lowTransitionWrite (u : UProg) (c : Fin u.fns.length) (position : Nat)
    (w : UTransitionWrite) :
    Except String { x : TransitionWrite (declOf u) (ctxOf u c) (resOf u c) //
      x.Frozen ∧ x.Permitted (vertragVon (declOf u) c) } :=
  match w.place with
  | .relative _ => .error "transition target scope unresolved"
  | .glob name =>
    match globIdx u.globs name with
    | .error e => .error e
    | .ok g =>
      match h : (globAt u g).ty with
      | .int lo hi =>
        match lowCaptured (fnAt u c) (ctxOf u c) (uTransitionSourceName position) (.int lo hi),
            lowCaptured (fnAt u c) (ctxOf u c) (uTransitionTargetName position) (.int lo hi) with
        | .error e, _ => .error e
        | _, .error e => .error e
        | .ok sv, .ok tv =>
          if hw : writesGAt u (fnAt u c) g = true then
            have hwV : (vertragVon (declOf u) c).gschreibt g = true := by
              rw [vGSchreibt_eq u c g]
              exact hw
            have hg : (declOf u).gtyp g = .int lo hi := by
              show (globAt u g).ty.toTy = _
              rw [h]
              rfl
            if hd : (∀ wdd ∈ (declOf u).gbraucht g, Res.von (declOf u) wdd ∈ resOf u c) then
              .ok ⟨TransitionWrite.glob g hg (Expr.var sv) (Expr.var tv) hd,
                TransitionWrite.Frozen.glob (D := declOf u) (Λ := resOf u c) g hg sv tv hd, hwV⟩
            else .error "access without held guard"
          else .error "write without right"
      | _ => .error "transition endpoints require an integer global"
  | .slot table field _ =>
    match tabIdx u.tabs table with
    | .error e => .error e
    | .ok t =>
      match fieldHit u t field with
      | .error e => .error e
      | .ok fh =>
        match lowCaptured (fnAt u c) (ctxOf u c) (uTransitionIndexName position)
            (.index ((declOf u).count t)),
          lowCaptured (fnAt u c) (ctxOf u c) (uTransitionSourceName position)
            (.int fh.range.1 fh.range.2),
          lowCaptured (fnAt u c) (ctxOf u c) (uTransitionTargetName position)
            (.int fh.range.1 fh.range.2) with
        | .error e, _, _ => .error e
        | _, .error e, _ => .error e
        | _, _, .error e => .error e
        | .ok iv, .ok sv, .ok tv =>
          if hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ resOf u c then
            if hw : writesAt u (fnAt u c) t = true then
              have hwV : (vertragVon (declOf u) c).schreibt t = true := by
                rw [vSchreibt_eq u c t]
                exact hw
              have numeric : (declOf u).typ t fh.idx = .int fh.range.1 fh.range.2 := fh.hint
              .ok ⟨TransitionWrite.slot t fh.idx numeric (Expr.var iv) (Expr.var sv) (Expr.var tv) hL,
                TransitionWrite.Frozen.slot (D := declOf u) (Λ := resOf u c) t fh.idx numeric iv sv tv hL, hwV⟩
            else .error "write without right"
          else .error "access without held guard"

/-- All writes of a declaration, in source order. -/
@[expose] def lowTransitionWrites (u : UProg) (c : Fin u.fns.length) :
    Nat → List UTransitionWrite →
    Except String { ws : List (TransitionWrite (declOf u) (ctxOf u c) (resOf u c)) //
      (∀ x ∈ ws, x.Frozen) ∧ (∀ x ∈ ws, x.Permitted (vertragVon (declOf u) c)) }
  | _, [] => .ok ⟨[], (by intro x h; cases h), (by intro x h; cases h)⟩
  | position, w :: rest =>
    match lowTransitionWrite u c position w with
    | .error e => .error e
    | .ok x =>
      match lowTransitionWrites u c (position + 1) rest with
      | .error e => .error e
      | .ok xs =>
        .ok ⟨x.1 :: xs.1,
          (by
            intro y hy
            rcases List.mem_cons.mp hy with same | member
            · subst same; exact x.2.1
            · exact xs.2.1 y member),
          (by
            intro y hy
            rcases List.mem_cons.mp hy with same | member
            · subst same; exact x.2.2
            · exact xs.2.2 y member)⟩

/-- The constant edge of a shift declaration: the endpoints must lie in the
    field's range, the edge in `D.erlaubt`, and the function must write the
    table under its held guard. -/
@[expose] def lowConstEdge (u : UProg) (c : Fin u.fns.length) (w : UTransitionWrite) :
    Except String (ConstEdge (declOf u) (vertragVon (declOf u) c) (ctxOf u c) (resOf u c)) :=
  match w.place, w.source, w.target with
  | .slot table field _, .lit a, .lit b =>
    match tabIdx u.tabs table with
    | .error e => .error e
    | .ok t =>
      match fieldHit u t field with
      | .error e => .error e
      | .ok fh =>
        match lowCaptured (fnAt u c) (ctxOf u c) (uTransitionIndexName 0)
            (.index ((declOf u).count t)) with
        | .error e => .error e
        | .ok iv =>
          if ha : fh.range.1 ≤ a ∧ a ≤ fh.range.2 then
            if hb : fh.range.1 ≤ b ∧ b ≤ fh.range.2 then
              if he : (declOf u).erlaubt t fh.idx a b = true then
                if hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ resOf u c then
                  if hw : writesAt u (fnAt u c) t = true then
                    have hwV : (vertragVon (declOf u) c).schreibt t = true := by
                      rw [vSchreibt_eq u c t]
                      exact hw
                    have numeric : (declOf u).typ t fh.idx = .int fh.range.1 fh.range.2 := fh.hint
                    .ok { table := t, field := fh.idx, lo := fh.range.1, hi := fh.range.2,
                          numeric := numeric, index := iv, source := a, target := b,
                          sourceRange := ha, targetRange := hb, erlaubt := he, right := hwV,
                          guard := hL }
                  else .error "write without right"
                else .error "access without held guard"
              else .error "constant transition edge is not in the state graph"
            else .error "value outside range"
          else .error "value outside range"
  | _, _, _ => .error "constant transition edge expected"

/-- The held resources at the start are the contract end. -/
theorem transitionResPerm (u : UProg) (c : Fin u.fns.length) :
    (resOf u c).Perm (vertragVon (declOf u) c).ende := by
  rw [endeRes_eq u c]

/-- The lowered types are the declaration's, in the lowering's own context. -/
theorem transitionReqEq (u : UProg) (c : Fin u.fns.length) :
    ReqTy u c = Expr (declOf u) (ctxOf u c) (resOf u c) .bool := by
  unfold ReqTy
  rw [ctxParams_eq u c, anfangRes_eq u c]

theorem transitionRumpEq (u : UProg) (c : Fin u.fns.length) :
    RumpTy u c = Endblock (declOf u) (vertragVon (declOf u) c) false (ctxOf u c) (resOf u c) := by
  unfold RumpTy
  rw [ctxParams_eq u c, anfangRes_eq u c]

theorem transitionEnsEq (u : UProg) (c : Fin u.fns.length) (hn : (declOf u).erg c = none) :
    EnsTy u c = Expr (declOf u) (ctxOf u c) (resOf u c) .bool := by
  unfold EnsTy
  rw [hn]
  simp only [ErgCtx]
  rw [← endeRes_eq u c, ctxParams_eq u c]

/-- A transition of stores: requires, ensures and body are the typed expansion. -/
@[expose] def lowerStoresAt (u : UProg) (c : Fin u.fns.length) (tr : UTransition) :
    Except String (EnsTy u c × RumpTy u c × ReqTy u c) :=
  match lowTransitionWrites u c 0 tr.writes with
  | .error e => .error e
  | .ok ws =>
    match lowEnsList u (ctxOf u c) (resOf u c) (fnAt u c) none (uTransitionAssumptions tr) with
    | .error e => .error e
    | .ok clause =>
      if hn : (declOf u).erg c = none then
        .ok (transCast (transitionEnsEq u c hn).symm (transitionEnsures ws.1),
          transCast (transitionRumpEq u c).symm
            (transitionEnd (vertragVon (declOf u) c) ws.1 ws.2.2
              (transitionReturn (vertragVon (declOf u) c) hn (transitionResPerm u c))),
          transCast (transitionReqEq u c).symm (transitionRequires ws.1 clause))
      else .error "transition function has a result"

/-- A constant edge: the body is the primitive shift under the generated requires. -/
@[expose] def lowerShiftAt (u : UProg) (c : Fin u.fns.length) (tr : UTransition) :
    Except String (EnsTy u c × RumpTy u c × ReqTy u c) :=
  match tr.writes with
  | [w] =>
    match lowConstEdge u c w with
    | .error e => .error e
    | .ok edge =>
      match lowEnsList u (ctxOf u c) (resOf u c) (fnAt u c) none (uTransitionAssumptions tr) with
      | .error e => .error e
      | .ok clause =>
        if hn : (declOf u).erg c = none then
          .ok (transCast (transitionEnsEq u c hn).symm (transitionEnsures [edge.write]),
            transCast (transitionRumpEq u c).symm
              (Endblock.cons edge.statement
                (transitionReturn (vertragVon (declOf u) c) hn (transitionResPerm u c))),
            transCast (transitionReqEq u c).symm (transitionRequires [edge.write] clause))
        else .error "transition function has a result"
  | _ => .error "constant transition edge expected"

/-- The lowering of a generated function: admitted only if it is exactly the
    function generated for its declaration (up to the computed lock floor),
    and it carries a requires. -/
@[expose] def lowerTransitionAt (u : UProg) (c : Fin u.fns.length) (state : UZustand)
    (tr : UTransition) : Except String (EnsTy u c × RumpTy u c × ReqTy u c) :=
  match uGenerateTransition u.tabs u.globs state.name tr with
  | .error e => .error e
  | .ok g =>
    if { fnAt u c with boden := none } = { g with boden := none } then
      if (fnAt u c).needs = [] then .error "generated transition function without requires"
      else if uTransitionShift tr then lowerShiftAt u c tr else lowerStoresAt u c tr
    else .error "generated transition function is not its declaration's expansion"

end Gabbro.Grammatik.Parser.UebersetzeAllg2
