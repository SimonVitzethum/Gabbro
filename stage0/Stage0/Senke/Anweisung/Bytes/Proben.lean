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

def program : Programm D where
  invariante _ := .tru
  requires _ := .tru
  ensures _ := .tru
  rumpf f := by
    obtain ⟨f, hf⟩ := f
    have hz : f = 0 := by change f < 1 at hf; omega
    subst f
    exact body

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
def image : Except String (List Runner.B) := do
  let b ← bild program (layU u (fun _ => none)) [entry] Fin.val (fun _ => "main") entry [] 1024
  pure b.bytes

set_option maxRecDepth 100000 in
/-- Both byte constructors reach the regular function lowering with actual table cells. -/
theorem putBytes_ok_zeuge : image.isOk = true := by decide +kernel

end Gabbro.Stage0.Senke.ByteProbe
