/- Nondegenerate wide foreign answers exercise all limbs in complete images. -/
module
public import Stage0.Senke.Tore.Answers
public import Stage0.Senke.Tore.FallibleRun
public import Stage0.Bindung.Proben
@[expose] public section

namespace Gabbro.Stage0.Senke.ForeignAreaProbe
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def answerTy (bits : Nat) : Ty := .int 0 (2 ^ bits - 1)
def u (bits : Nat) (fallible : Bool) : UProg := { ControlProbe.u with
  axs := [{name := "provider", params := [], kinds := [], res := some (answerTy bits),
    gruende := if fallible then 1 else 0}] }
abbrev D (bits : Nat) (fallible : Bool) := declOf (u bits fallible)
abbrev entry (bits : Nat) (fallible : Bool) : (D bits fallible).Fn := ⟨0, by decide⟩
abbrev gate (bits : Nat) (fallible : Bool) : (D bits fallible).Ax := ⟨0, by decide⟩

def retN (bits : Nat) (fallible : Bool) {Γ : Ctx} (n : Int) (lower : 0 ≤ n) (upper : n ≤ 100) :
    Endblock (D bits fallible) (vertragVon (D bits fallible) (entry bits fallible)) false Γ [] :=
  .ret (.val (.widen lower upper (.lit n))) (.refl [])

def admission (bits : Nat) (fallible : Bool) :
    RufPasst (D bits fallible) (vertragVon (D bits fallible) (entry bits fallible))
      ((D bits fallible).asignatur (gate bits fallible)) [] where
  hw t := Fin.elim0 t
  hg g := Fin.elim0 g
  hk := ⟨[], List.Perm.refl _, List.Sublist.refl _⟩
  hh l := Fin.elim0 l

/-- The compared value has a nonzero high limb and zero low limb. -/
def success (bits : Nat) (fallible : Bool) :
    Endblock (D bits fallible) (vertragVon (D bits fallible) (entry bits fallible))
      false [answerTy bits] [] :=
  .ite (.eq (.var .here) (.lit (2 ^ 80)))
    (retN bits fallible 17 (by decide) (by decide))
    (retN bits fallible 19 (by decide) (by decide))

def handler (bits : Nat) :
    Endblock (D bits true) (vertragVon (D bits true) (entry bits true)) false [.why 1] [] :=
  .cons (.onWhy (.var .here)
    (.cons (.cons (.ret (.val (.widen (by decide) (by decide) (.lit 9))) (.refl [])) .nil) .nil))
    (retN bits true 99 (by decide) (by decide))

def normal (bits : Nat) :
    Endblock (D bits false) (vertragVon (D bits false) (entry bits false)) false [] [] :=
  .bindAxiom (gate bits false) .nil rfl
    (fun t => Fin.elim0 t) (fun g => Fin.elim0 g)
    (fun t => Fin.elim0 t) (fun g => Fin.elim0 g) (success bits false)

def fallible (bits : Nat) :
    Endblock (D bits true) (vertragVon (D bits true) (entry bits true)) false [] [] :=
  .bindAxiomOptElse (some (answerTy bits)) (gate bits true) .nil rfl (admission bits true)
    (fun t => Fin.elim0 t) (fun g => Fin.elim0 g) (by decide)
    (handler bits) (success bits true)

def nested (bits : Nat) :
    Endblock (D bits true) (vertragVon (D bits true) (entry bits true)) false [] [] :=
  .cons (.ite .tru
    (.bindAxiomOptElse (some (answerTy bits)) (gate bits true) .nil rfl (admission bits true)
      (fun t => Fin.elim0 t) (fun g => Fin.elim0 g) (by decide) (handler bits)
      (.cons (.ite (.eq (.var .here) (.lit (2 ^ 80)))
        (.cons (.ret (.val (.widen (by decide) (by decide) (.lit 17))) (.refl [])) .nil)
        (.cons (.ret (.val (.widen (by decide) (by decide) (.lit 19))) (.refl [])) .nil)) .nil)) .nil)
    (retN bits true 99 (by decide) (by decide))

def program (bits : Nat) (canFail inBlock : Bool) : Programm (D bits canFail) where
  invariante _ := .tru
  requires _ := .tru
  ensures _ := .tru
  rumpf f := by
    obtain ⟨f, hf⟩ := f
    have zero : f = 0 := by change f < 1 at hf; omega
    subst f
    cases canFail with
    | false => exact normal bits
    | true => exact if inBlock then nested bits else fallible bits

def binding (canFail : Bool) : TorB :=
  ⟨39, regsIn 0, if canFail then [(-9, 0)] else [], some 0⟩

def image (bits : Nat) (canFail inBlock : Bool) : Except String (List Runner.B) := do
  let emitted ← bild 1 (program bits canFail inBlock)
    (layU (u bits canFail) (fun _ => some (binding canFail)))
    [entry bits canFail] Fin.val (fun _ => "main") (entry bits canFail) .nil [] 4096
  pure emitted.bytes

/-- Two-word and three-word answers, with live success and failure branches. -/
theorem multiword_images_zeuge :
    valueWords (answerTy 96) = 2 ∧ valueWords (answerTy 192) = 3 ∧
    (image 96 false false).isOk = true ∧ (image 96 true false).isOk = true ∧
    (image 96 true true).isOk = true ∧ (image 192 false false).isOk = true ∧
    (image 192 true false).isOk = true ∧ (image 192 true true).isOk = true := by
  decide +kernel

/-- A twelve-word value also exercises overlap when copied back down the frame. -/
theorem overlapping_multiword_image_zeuge :
    valueWords (answerTy 768) = 12 ∧ (image 768 false false).isOk = true := by
  decide +kernel

def oracle (bits : Nat) (canFail fail : Bool) : Orakel (D bits canFail) where
  wirkt _ σ _ := (σ, if fail then 1 else (2 ^ 80) * (if canFail then 2 else 1))
  regLies r := Fin.elim0 r
  regSchreib r := Fin.elim0 r
  sichtbar _ _ := true

def initial (bits : Nat) (canFail : Bool) : World (D bits canFail) where
  slots t := Fin.elim0 t
  globs g := Fin.elim0 g
  spur := []

def observed (bits : Nat) (canFail inBlock fail : Bool) : Int :=
  let calls := fun f (_ : World (D bits canFail)) (_ : Env (D bits canFail) ((D bits canFail).params f)) =>
    (RufAusgang.logik .schleife : RufAusgang f)
  match execEnd (oracle bits canFail fail) 1 calls
      ((program bits canFail inBlock).rumpf (entry bits canFail)) (initial bits canFail) .nil with
  | .zurueck _ value => value.n
  | _ => -1

/-- The canonical model observes the high limb and the distinct nominal error. -/
theorem multiword_paths_zeuge :
    observed 96 false false false = 17 ∧ observed 96 true false false = 17 ∧
    observed 96 true false true = 9 ∧ observed 96 true true false = 17 ∧
    observed 96 true true true = 9 ∧ observed 192 false false false = 17 := by
  decide +kernel

/-- Omitting the clause cannot silently project an answer to its low word. -/
theorem missing_area_refused_zeuge :
    plainForeignC (layU (u 96 false) (fun _ => some { binding false with resultArea := none }) 0)
      (gate 96 false) (.nil : Args (D 96 false) [] [] []) (answerTy 96) 8 0 = none ∧
    areaGut { binding false with resultArea := some 6 } 0 6 = false := by
  decide +kernel

end Gabbro.Stage0.Senke.ForeignAreaProbe
