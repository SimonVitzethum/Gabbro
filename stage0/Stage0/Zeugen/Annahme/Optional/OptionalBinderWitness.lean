/- Optional foreign binders through complete images and canonical source semantics. -/
module
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.AxiomElseProbes
@[expose] public section

namespace Gabbro.Stage0.OptionalBinderWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR Senke
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The value fixture binds its answer; the void fixture preserves local 23. -/
def result (valued : Bool) : Option Ty := if valued then some (.int 0 10) else none

def u (valued fallible : Bool) : UProg := { ControlProbe.u with
  axs := [{ name := "gate", params := [], kinds := [], res := result valued,
    gruende := if fallible then 1 else 0 }] }
abbrev D (valued fallible : Bool) := declOf (u valued fallible)
abbrev entry (valued fallible : Bool) : (D valued fallible).Fn := ⟨0, by decide⟩
abbrev gate (valued fallible : Bool) : (D valued fallible).Ax := ⟨0, by decide⟩

def admission (valued fallible : Bool) :
    RufPasst (D valued fallible) (vertragVon (D valued fallible) (entry valued fallible))
      ((D valued fallible).asignatur (gate valued fallible)) [] where
  hw t := Fin.elim0 t
  hg g := Fin.elim0 g
  hk := ⟨[], List.Perm.refl _, List.Sublist.refl _⟩
  hh l := Fin.elim0 l

def answer (valued fallible : Bool) :
    Expr (D valued fallible) (ErgCtx [.int 0 100] (result valued)) [] (.int 0 100) := by
  cases valued with
  | false => exact .var .here
  | true => exact .widen (by decide) (by decide) (.var .here)

def retN (valued fallible : Bool) {Γ : Ctx} (n : Int) (hl : 0 ≤ n) (hh : n ≤ 100) :
    Endblock (D valued fallible) (vertragVon (D valued fallible) (entry valued fallible)) false Γ [] :=
  .ret (.val (.widen hl hh (.lit n))) (.refl [])

/-- Reading the bound reason distinguishes this branch from success and fallthrough. -/
def handler (valued : Bool) :
    Endblock (D valued true) (vertragVon (D valued true) (entry valued true))
      false [.why 1, .int 0 100] [] :=
  .cons (.onWhy (.var .here)
    (.cons (.cons (.ret (.val (.widen (by decide) (by decide) (.lit 9))) (.refl [])) .nil) .nil))
    (retN valued true 99 (by decide) (by decide))

def fallibleEnd (valued : Bool) :
    Endblock (D valued true) (vertragVon (D valued true) (entry valued true))
      false [.int 0 100] [] :=
  .bindAxiomOptElse (result valued) (gate valued true) .nil rfl (admission valued true)
    (fun t => Fin.elim0 t) (fun g => Fin.elim0 g) (by decide) (handler valued)
    (.ret (.val (answer valued true)) (.refl []))

def fallibleBlock (valued : Bool) :
    Block (D valued true) (vertragVon (D valued true) (entry valued true))
      false [.int 0 100] [] [] :=
  .bindAxiomOptElse (result valued) (gate valued true) .nil rfl (admission valued true)
    (fun t => Fin.elim0 t) (fun g => Fin.elim0 g) (by decide) (handler valued)
    (.cons (.ret (.val (answer valued true)) (.refl [])) .nil)

def plainEnd : Endblock (D false false)
    (vertragVon (D false false) (entry false false)) false [.int 0 100] [] :=
  .bindAxiomOpt none (gate false false) .nil rfl (admission false false)
    (fun t => Fin.elim0 t) (fun g => Fin.elim0 g)
    (.ret (.val (answer false false)) (.refl []))

def plainBlock : Block (D false false)
    (vertragVon (D false false) (entry false false)) false [.int 0 100] [] [] :=
  .bindAxiomOpt none (gate false false) .nil rfl (admission false false)
    (fun t => Fin.elim0 t) (fun g => Fin.elim0 g)
    (.cons (.ret (.val (answer false false)) (.refl [])) .nil)

def body (valued fallible nested : Bool) :
    Endblock (D valued fallible) (vertragVon (D valued fallible) (entry valued fallible))
      false [] [] := by
  cases fallible with
  | true => exact .bind (.widen (by decide) (by decide) (.lit 23))
      (if nested then .cons (.ite .tru (fallibleBlock valued) .nil)
        (retN valued true 99 (by decide) (by decide)) else fallibleEnd valued)
  | false =>
    cases valued with
    | false => exact .bind (.widen (by decide) (by decide) (.lit 23))
        (if nested then .cons (.ite .tru plainBlock .nil)
          (retN false false 99 (by decide) (by decide)) else plainEnd)
    | true => exact retN true false 99 (by decide) (by decide)

def program (valued fallible nested : Bool) : Programm (D valued fallible) where
  invariante _ := .tru
  requires _ := .tru
  ensures _ := .tru
  rumpf f := by
    obtain ⟨f, hf⟩ := f
    have hz : f = 0 := by change f < 1 at hf; omega
    subst f
    exact body valued fallible nested

def binding (fallible : Bool) : TorB :=
  ⟨1, [none, none, none, none, none, none], if fallible then [(-9, 0)] else []⟩

def image (valued fallible nested : Bool) : Except String (List Runner.B) := do
  let b ← bild 1 (program valued fallible nested)
    (layU (u valued fallible) (fun _ => some (binding fallible)))
    [entry valued fallible] Fin.val (fun _ => "main") (entry valued fallible) .nil [] 1024 0
  pure b.bytes

def initial (valued fallible : Bool) : World (D valued fallible) where
  slots t := Fin.elim0 t
  globs g := Fin.elim0 g
  spur := []

def oracle (valued fallible : Bool) (raw : Runner.W) : Orakel (D valued fallible) where
  wirktL _ σ _ := ({ σ with spur := [] }, rohW (binding fallible) (if fallible then 1 else 0) raw)
  regLiesL r := Fin.elim0 r
  regSchreib r := Fin.elim0 r
  sichtbarL _ _ := true

def calls (valued fallible : Bool) (f : (D valued fallible).Fn)
    (_ : World (D valued fallible)) (_ : Env (D valued fallible) ((D valued fallible).params f)) :
    RufAusgang f := .logik .schleife

/-- Evaluate only the canonical semantics used by the generic lowering theorem. -/
def observed (valued fallible nested : Bool) (raw : Runner.W) : Int :=
  match execEnd (oracle valued fallible raw) 1 (calls valued fallible)
      (body valued fallible nested) (initial valued fallible) .nil with
  | .zurueck _ v => v.n
  | _ => -1

/-- Nonempty complete images exercise both generic binder cases and contexts. -/
theorem accepted_images :
    (image false false false).toOption.isSome = true ∧
    (image false false true).toOption.isSome = true ∧
    (image false true false).toOption.isSome = true ∧
    (image false true true).toOption.isSome = true ∧
    (image true true false).toOption.isSome = true ∧
    (image true true true).toOption.isSome = true := by decide_cbv

/-- Void keeps local 23, values bind 7, and both handlers consume reason 0. -/
theorem success_and_reason_paths :
    observed false false false 7 = 23 ∧ observed false false true 7 = 23 ∧
    observed false true false 7 = 23 ∧ observed false true true 7 = 23 ∧
    observed true true false 7 = 7 ∧ observed true true true 7 = 7 ∧
    observed false true false (BitVec.ofInt 64 (-9)) = 9 ∧
    observed false true true (BitVec.ofInt 64 (-9)) = 9 ∧
    observed true true false (BitVec.ofInt 64 (-9)) = 9 ∧
    observed true true true (BitVec.ofInt 64 (-9)) = 9 := by decide_cbv

/-- The current canonical void decoder also accepts unlisted errno words. -/
theorem unlisted_void_answer :
    observed false true false (BitVec.ofInt 64 (-8)) = 23 ∧
    observed false true true (BitVec.ofInt 64 (-8)) = 23 := by decide_cbv

/-- In particular, preserving local 23 cannot be implemented by deleting the call. -/
def observedTrace (valued fallible nested : Bool) (raw : Runner.W) : List (Ereignis (D valued fallible)) :=
  match execEnd (oracle valued fallible raw) 1 (calls valued fallible)
      (body valued fallible nested) (initial valued fallible) .nil with
  | .zurueck σ _ => σ.spur
  | _ => []

theorem oracle_effect_is_retained :
    observedTrace false false false 7 = [.fremd (.inl (gate false false))] ∧
    observedTrace false false true 7 = [.fremd (.inl (gate false false))] ∧
    observedTrace false true false 7 = [.fremd (.inl (gate false true))] ∧
    observedTrace false true true (BitVec.ofInt 64 (-9)) = [.fremd (.inl (gate false true))] := by
  decide_cbv

/-- Value decoding still rejects an answer outside its declared range. -/
theorem invalid_value_answer :
    observed true true false 11 = -1 ∧ observed true true true 11 = -1 := by decide_cbv

end Gabbro.Stage0.OptionalBinderWitness
