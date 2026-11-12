/- Nondegenerate wide foreign answers exercise all limbs in complete images. -/
module
public import Stage0.Senke.Tore.Answers
public import Stage0.Senke.Tore.FallibleRun
public import Stage0.Bindung.Proben
public import Stage0.Senke.Welt.Schreib
import Grammatik.Kern.Taktik.KernelRfl
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
abbrev entry (bits : Nat) (fallible : Bool) : (D bits fallible).Fn := ⟨0, Nat.le_of_ble_eq_true rfl⟩
abbrev gate (bits : Nat) (fallible : Bool) : (D bits fallible).Ax := ⟨0, Nat.le_of_ble_eq_true rfl⟩

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
    (fun t => Fin.elim0 t) (fun g => Fin.elim0 g) (Nat.le_of_ble_eq_true rfl)
    (handler bits) (success bits true)

def nested (bits : Nat) :
    Endblock (D bits true) (vertragVon (D bits true) (entry bits true)) false [] [] :=
  .cons (.ite .tru
    (.bindAxiomOptElse (some (answerTy bits)) (gate bits true) .nil rfl (admission bits true)
      (fun t => Fin.elim0 t) (fun g => Fin.elim0 g) (Nat.le_of_ble_eq_true rfl) (handler bits)
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
    [entry bits canFail] Fin.val (fun _ => "main") (entry bits canFail) .nil [] 4096 0
  pure emitted.bytes

/-- Two-word and three-word answers, with live success and failure branches. -/
theorem multiword_images_zeuge :
    valueWords (answerTy 96) = 2 ∧ valueWords (answerTy 192) = 3 ∧
    (image 96 false false).isOk = true ∧ (image 96 true false).isOk = true ∧
    (image 96 true true).isOk = true ∧ (image 192 false false).isOk = true ∧
    (image 192 true false).isOk = true ∧ (image 192 true true).isOk = true := by
  (repeat' apply And.intro) <;> kernel_rfl

/-- The fixtures satisfy the canonical checker jointly with the emitted paths;
    the complete carrier enumeration is empty for this table-free program. -/
theorem multiword_admission_zeuge :
    Akzeptiert (program 96 false false) ⟨fun l => Fin.elim0 l, fun l => Fin.elim0 l⟩
      [entry 96 false] [] [] [entry 96 false] = true ∧
    Akzeptiert (program 96 true false) ⟨fun l => Fin.elim0 l, fun l => Fin.elim0 l⟩
      [entry 96 true] [] [] [entry 96 true] = true ∧
    Akzeptiert (program 96 true true) ⟨fun l => Fin.elim0 l, fun l => Fin.elim0 l⟩
      [entry 96 true] [] [] [entry 96 true] = true := by
  (repeat' apply And.intro) <;> kernel_rfl

/-- A twelve-word value also exercises overlap when copied back down the frame. -/
theorem overlapping_multiword_image_zeuge :
    valueWords (answerTy 768) = 12 ∧ (image 768 false false).isOk = true := by
  (repeat' apply And.intro) <;> kernel_rfl

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
  (repeat' apply And.intro) <;> kernel_rfl

/-- Omitting the clause cannot silently project an answer to its low word. -/
theorem missing_area_refused_zeuge :
    plainForeignC (layU (u 96 false) (fun _ => some { binding false with resultArea := none }) 0)
      (gate 96 false) (.nil : Args (D 96 false) [] [] []) (answerTy 96) 8 0 = none ∧
    areaGut { binding false with resultArea := some 6 } 0 6 = false := by
  (repeat' apply And.intro) <;> kernel_rfl

end Gabbro.Stage0.Senke.ForeignAreaProbe

namespace Gabbro.Stage0.Senke.ForeignAreaContractWitness
variable [RootNativeFloat.Hardware]
open Gabbro.Grammatik Runner.IR Runner.Mem ForeignAreaProbe
abbrev D := ForeignAreaProbe.D 96 false
def layout : Lay D := layU (u 96 false) (fun _ => some (binding false)) 0
def provider : Orakel D := oracle 96 false false
def value : Wert D (answerTy 96) := ⟨2 ^ 80, by decide, by decide⟩

/-- This is an explicit software service witness on the abstract runner
    relation, not a claim that a host system call implements this provider. -/
theorem area_contract_zeuge :
    @AreaContract D ({ toHardware := inferInstance, ans := fun _ _ _ _ => True } : Kern) layout provider := by
  letI : Kern := { toHardware := inferInstance, ans := fun _ _ _ _ => True }
  intro a b τ he j bound accepted σ ρ request m fp base K frame capacity separated below
    number arguments hidden unused world
  obtain ⟨a, ha⟩ := a
  have zero : a = 0 := by change a < 1 at ha; omega
  subst a
  have resultType : answerTy 96 = τ := by
    have same : some (answerTy 96) = some τ := he
    exact Option.some.inj same
  subst τ
  have bindingType : binding false = b := by
    have same : some (binding false) = some b := bound
    exact Option.some.inj same
  subst b
  let address := fp.toNat + 8 * base
  let words := encodeWords layout (answerTy 96) value
  let output := writeSpan m address words
  have width : words.length = valueWords (answerTy 96) := encodeWords_length _ _ _
  have fits : address + 8 * words.length ≤ 2 ^ 64 := by
    have room := frame.room
    dsimp only [address]
    omega
  have stored : StorageAt layout output address (answerTy 96) value := by
    apply writeValue_same (by simpa only [width] using fits)
    · intro i hi
      exact frame_rd_at frame (by dsimp only [address]; omega)
        (by dsimp only [address]; omega)
    · trivial
  have baseAddress : slot fp (BitVec.ofNat 64 base) = BitVec.ofNat 64 address := by
    apply BitVec.eq_of_toNat_eq
    rw [slot_toNat frame.room (by have := valueWords_pos (answerTy 96); omega)]
    simp only [BitVec.toNat_ofNat]
    have room := frame.room
    have positive : 0 < words.length := by rw [width]; exact valueWords_pos _
    dsimp only [address]
    omega
  have payload : ValueAt layout output fp base (answerTy 96) value := by
    refine ⟨stored.1, ?_⟩
    intro i hi
    rw [← slot_plus fp base i, baseAddress, ← BitVec.ofNat_add]
    simpa only [Nat.zero_add, absolute_slot] using stored.2 i hi
  refine ⟨0, 0, output, trivial, ?_, ?_, ?_⟩
  · refine AgreeW.stark (writeSpan_rd _ _ _) (writeSpan_wr _ _ _) ?_
    intro x outside outsideWorld
    apply writeSpan_out _ _ _ fits
    unfold inSlots at outside
    dsimp only [address]
    omega
  · exact ⟨(fun t => Fin.elim0 t), (fun g => Fin.elim0 g),
      world.2.2.keep (writeSpan_wr _ _ _)⟩
  · refine .inl ⟨value, ?_, Or.inl rfl, payload⟩
    kernel_rfl

/-- The exact layout/oracle pair jointly satisfies all inherited gate
    premises. Register-only obligations are impossible for an area profile. -/
theorem gate_contract_zeuge : @TorOK { toHardware := inferInstance, ans := fun _ _ _ _ => True } D layout provider := by
  letI : Kern := { toHardware := inferInstance, ans := fun _ _ _ _ => True }
  refine ⟨?_, ?_, ?_, area_contract_zeuge⟩
  · intro a b bound accepted
    have same : some (binding false) = some b := bound
    cases same
    simp [torGut, binding] at accepted
  · intro a b bound accepted
    have same : some (binding false) = some b := bound
    cases same
    simp [torGut, binding] at accepted
  · intro a n he
    obtain ⟨a, ha⟩ := a
    have zero : a = 0 := by change a < 1 at ha; omega
    subst a
    have impossible : some (answerTy 96) = some (.ref n) := he
    cases impossible

end Gabbro.Stage0.Senke.ForeignAreaContractWitness
