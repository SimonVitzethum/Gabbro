/-
  Subject: Nonempty byte-span witnesses. The source reader does not yet construct
  getBytes/putBytes, so these G fixtures also supply images for the real runner.
-/
import Stage0.Senke.Welt.Anordnung
import Stage0.Senke.Anweisung.Bytes.Put

namespace Gabbro.Stage0.Senke.ByteProbe
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR

/-- Twelve byte cells and one function, with ordinary declared write effects. -/
def u : UProg := {
  tabs := [{ name := "Bytes", count := 12, cols := [("byte", (0, 255))] }]
  locks := []
  fns := [{ name := "main", params := [], kinds := [], res := some (0, 256 ^ 8 - 1), held := [], puts := ["Bytes"], gives := [], body := [], ret := .val (.lit 0) }]
}

abbrev D := declOf u
abbrev tab : D.Tab := ⟨0, by decide⟩
abbrev field : D.Feld tab := ⟨0, by decide⟩
abbrev entry : D.Fn := ⟨0, by decide⟩

/-- The probe writes four bytes at offset two, then reads the same span back. -/
def body : Endblock D (vertragVon D entry) false [] [] :=
  .cons (.putBytes tab field rfl 4 (.lit 2) (by decide) (by decide)
    (.widen (by decide) (by decide) (.lit 16909098)) (by decide) (by intro w hw; change w ∈ [] at hw; cases hw))
    (.ret (.val (.widen (by decide) (by decide)
      (.getBytes (Γ := []) (Λ := []) tab field rfl 4 (.lit 2) (by decide) (by decide) (by intro w hw; change w ∈ [] at hw; cases hw)))) (.refl []))

def programOf (code : Endblock D (vertragVon D entry) false [] []) : Programm D where
  invariante _ := .tru
  requires _ := .tru
  ensures _ := .tru
  rumpf f := by
    obtain ⟨f, hf⟩ := f
    have hz : f = 0 := by change f < 1 at hf; omega
    subst f
    exact code

def program : Programm D := programOf body

def initial : World D where
  slots t _ f := by
    obtain ⟨t, ht⟩ := t
    have hz : t = 0 := by change t < 1 at ht; omega
    subst t
    obtain ⟨f, hf⟩ := f
    have hz : f = 0 := by change f < 1 at hf; omega
    subst f
    exact ⟨0, by decide, by decide⟩
  globs g := Fin.elim0 g
  spur := []

/-- This is a nonzero round trip with four distinct bytes at a nonzero index. -/
theorem byte_roundtrip_zeuge :
    let σ := initial.schreibBytes tab field rfl [] 2 (zahlZuBytes 4 16909098)
    (eval σ (.getBytes (Γ := []) (Λ := []) tab field rfl 4 (.lit 2) (by decide) (by decide) (by intro w hw; change w ∈ [] at hw; cases hw)) σ .nil).n = 16909098 ∧
    (σ.slots tab 0 field).n = 0 ∧ (σ.slots tab 6 field).n = 0 := by
  decide +kernel

/-- The same G program is lowered by the ordinary image builder. -/
def imageOf (code : Endblock D (vertragVon D entry) false [] []) : Except String (List Runner.B) := do
  let b ← bild (programOf code) (layU u (fun _ => none)) [entry] Fin.val (fun _ => "main") entry [] 1024
  pure b.bytes

def image : Except String (List Runner.B) := imageOf body

set_option maxRecDepth 100000 in
/-- Both byte constructors reach the regular function lowering with actual table cells. -/
theorem putBytes_ok_zeuge : image.isOk = true := by decide +kernel

/-- A full word with bit 63 set, built from literals supported by the IR. -/
def fullWord : Expr D [] [] (.int 0 (256 ^ 8 - 1)) :=
  .widen (by decide) (by decide)
    (.add (.mul (.mul (.mul (.lit 1048576) (.lit 1048576)) (.lit 1048576)) (.lit 8)) (.lit 42))

def body8 : Endblock D (vertragVon D entry) false [] [] :=
  .cons (.putBytes tab field rfl 8 (.lit 2) (by decide) (by decide) fullWord
    (by decide) (by intro w hw; change w ∈ [] at hw; cases hw))
    (.ret (.val (.getBytes tab field rfl 8 (.lit 2) (by decide) (by decide)
      (by intro w hw; change w ∈ [] at hw; cases hw))) (.refl []))

def image8 : Except String (List Runner.B) := imageOf body8

set_option maxRecDepth 100000 in
/-- Full-width extraction reaches the regular image builder as well. -/
theorem putBytes8_ok_zeuge : image8.isOk = true := by decide +kernel

/-- G reads the high byte as 128 and preserves both adjacent cells. -/
theorem byte_roundtrip8_zeuge :
    let σ := initial.schreibBytes tab field rfl [] 2 (zahlZuBytes 8 (2 ^ 63 + 42))
    (eval σ (.getBytes (Γ := []) (Λ := []) tab field rfl 8 (.lit 2) (by decide) (by decide)
      (by intro w hw; change w ∈ [] at hw; cases hw)) σ .nil).n = 2 ^ 63 + 42 ∧
    (σ.slots tab 9 field).n = 128 ∧ (σ.slots tab 1 field).n = 0 ∧ (σ.slots tab 10 field).n = 0 := by
  decide +kernel

/-- A wider read is refused before any code is produced. -/
theorem getBytes_wide_refused_zeuge :
    lowE (layU u (fun _ => none) 65536)
      (.getBytes (Γ := []) (Λ := []) tab field rfl 9 (.lit 2) (by decide) (by decide)
        (by intro w hw; change w ∈ [] at hw; cases hw)) 3 = none := rfl

/-- Capturing the operands matters when the destination overlaps their source bytes. -/
def overlapBody : Endblock D (vertragVon D entry) false [] [] :=
  .cons (.putBytes tab field rfl 4 (.lit 2) (by decide) (by decide)
      (.widen (by decide) (by decide) (.lit 16909098)) (by decide)
      (by intro w hw; change w ∈ [] at hw; cases hw))
    (.cons (.putBytes tab field rfl 4 (.lit 3) (by decide) (by decide)
      (.getBytes tab field rfl 4 (.lit 2) (by decide) (by decide)
        (by intro w hw; change w ∈ [] at hw; cases hw)) (by decide)
      (by intro w hw; change w ∈ [] at hw; cases hw))
      (.ret (.val (.widen (by decide) (by decide)
        (.getBytes tab field rfl 4 (.lit 3) (by decide) (by decide)
          (by intro w hw; change w ∈ [] at hw; cases hw)))) (.refl [])))

def imageOverlap : Except String (List Runner.B) := imageOf overlapBody

set_option maxRecDepth 100000 in
theorem putBytes_overlap_zeuge : imageOverlap.isOk = true := by decide +kernel

/-- A zero-width span at the end of the table reads and writes no cell. -/
def emptyBody : Endblock D (vertragVon D entry) false [] [] :=
  .cons (.putBytes tab field rfl 0 (.lit 12) (by decide) (by decide) (.lit 0) (by decide)
    (by intro w hw; change w ∈ [] at hw; cases hw))
    (.ret (.val (.widen (by decide) (by decide)
      (.getBytes tab field rfl 0 (.lit 12) (by decide) (by decide)
        (by intro w hw; change w ∈ [] at hw; cases hw)))) (.refl []))

def imageEmpty : Except String (List Runner.B) := imageOf emptyBody

set_option maxRecDepth 100000 in
theorem putBytes_empty_zeuge : imageEmpty.isOk = true := by decide +kernel

def shiftU : UProg := { u with
  zustaende := [{name := "State", stufen := ["Idle", "Busy"], paare := [(0, 1)]}]
  regiert := [("Bytes", "byte", "State")]
}

/-- A permitted transition with a representable field, index and layout reaches the lowering. -/
theorem shift_ok_zeuge :
    let t : (declOf shiftU).Tab := ⟨0, by decide⟩
    let f : (declOf shiftU).Feld t := ⟨0, by decide⟩
    let fn : (declOf shiftU).Fn := ⟨0, by decide⟩
    let s : Stmt (declOf shiftU) (vertragVon (declOf shiftU) fn) false [] [] [] :=
      .shift t f rfl (.widen (by decide) (by decide) (.lit 1)) 0 1 (by decide) (by decide) (by decide)
        (by intro w hw; change w ∈ [] at hw; cases hw)
    (lowS (fun _ => 0) (layU shiftU (fun _ => none) 65536) 3 ([], 0) [] (0, 0) s).isSome = true := by
  decide +kernel

/-- Open cells are not bounded by count and currently have no IR world representation. -/
def openU : UProg := { u with
  tabs := [{name := "Bytes", count := 0, cols := [("byte", (0, 255))], von := some "provider"}]
}

theorem open_refs_lowered_zeuge :
    let t : (declOf openU).Tab := ⟨0, by decide⟩
    let f : (declOf openU).Feld t := ⟨0, by decide⟩
    let fn : (declOf openU).Fn := ⟨0, by decide⟩
    let r : Expr (declOf openU) [.ref 0] [] (.ref 0) := .var .here
    let L := layU openU (fun _ => none) 65536
    (lowE L (.refEq r r) 4).isSome = true ∧
    (lowE L (.slotRef r t rfl rfl f (by intro w hw; change w ∈ [] at hw; cases hw)) 4).isSome = true ∧
    (lowS (fun _ => 0) L 3 ([], 0) [] (0, 0)
      (V := vertragVon (declOf openU) fn) (l := false)
      (.assignSlotRef r t rfl rfl f (.widen (by decide) (by decide) (.lit 7)) (by decide)
        (by intro w hw; change w ∈ [] at hw; cases hw))).isSome = true := by
  decide +kernel

end Gabbro.Stage0.Senke.ByteProbe
