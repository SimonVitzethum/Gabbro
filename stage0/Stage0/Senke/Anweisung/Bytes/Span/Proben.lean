/- Whole-image witnesses cover chunk boundaries, partial high limbs and overlapping copies. -/
module
public import Stage0.Senke.Anweisung.Bytes.Proben
public import Stage0.Senke.Anweisung.Bytes.Span.Put
@[expose] public section

namespace Gabbro.Stage0.Senke.ByteSpanProbe
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def u : UProg := {
  tabs := [{ name := "Bytes", count := 40, cols := [("byte", (0, 255))] }]
  locks := []
  fns := [{ name := "main", params := [], kinds := [], res := some (0, 100), held := [],
    puts := ["Bytes"], gives := [], body := [], ret := .val (.lit 0) }]
}
abbrev D := declOf u
abbrev tab : D.Tab := ⟨0, by decide⟩
abbrev field : D.Feld tab := ⟨0, by decide⟩
abbrev entry : D.Fn := ⟨0, by decide⟩

def initial : World D where
  slots t _ f := by
    obtain ⟨t, ht⟩ := t
    have zero : t = 0 := by change t < 1 at ht; omega
    subst t
    obtain ⟨f, hf⟩ := f
    have zero : f = 0 := by change f < 1 at hf; omega
    subst f
    exact ⟨0, by decide, by decide⟩
  globs g := Fin.elim0 g
  spur := []

def read {Γ : Ctx} (n p : Nat) (bound : p + n ≤ 40) : Expr D Γ [] (.int 0 (256 ^ n - 1)) :=
  .getBytes tab field rfl n (.lit p) (by omega) (by exact_mod_cast bound)
    (by intro w hw; change w ∈ [] at hw; cases hw)

def returnBlock {Γ : Ctx} (good : Bool) : Block D (vertragVon D entry) false Γ [] [] :=
  .cons (.ret (.val (.widen (by split <;> decide) (by split <;> decide)
    (.lit (if good then 42 else 0)))) (.refl [])) .nil

/-- The second write reads overlapping source bytes. Both complete operands must
    have been captured before its first store, or later bytes would be corrupted. -/
def overlap (n : Nat) (small : n ≤ 17) (z : Int) (lower : 0 ≤ z) (upper : z ≤ 256 ^ n - 1) :
    Endblock D (vertragVon D entry) false [] [] :=
  .cons (.putBytes tab field rfl n (.lit 2) (by decide) (by change 2 + (n : Int) ≤ 40; omega)
    (.widen lower upper (.lit z)) (by decide)
    (by intro w hw; change w ∈ [] at hw; cases hw))
    (.cons (.putBytes tab field rfl n (.lit 3) (by decide) (by change 3 + (n : Int) ≤ 40; omega)
      (read n 2 (by omega)) (by decide)
      (by intro w hw; change w ∈ [] at hw; cases hw))
      (.cons (.ite (.eq (read n 3 (by omega)) (.lit z)) (returnBlock true) (returnBlock false))
        (.ret (.val (.widen (by decide) (by decide) (.lit 0))) (.refl []))))

def programOf (body : Endblock D (vertragVon D entry) false [] []) : Programm D where
  invariante _ := .tru
  requires _ := .tru
  ensures _ := .tru
  rumpf f := by
    obtain ⟨f, hf⟩ := f
    have zero : f = 0 := by change f < 1 at hf; omega
    subst f
    exact body

def imageOf (body : Endblock D (vertragVon D entry) false [] []) : Except String (List Runner.B) := do
  let b ← bild 1 (programOf body) (layU u (fun _ => none)) [entry] Fin.val (fun _ => "main") entry .nil [] 4096 0
  pure b.bytes

/-- Two kernels of eight and five bytes, with a nonzero partial high limb and
    an overlapping read/write that must capture the complete source first. -/
def image13 : Except String (List Runner.B) :=
  imageOf (overlap 13 (by decide) (2 ^ 103 + 2 ^ 64 + 42) (by decide) (by decide))

theorem byteSpan13_image_zeuge : image13.isOk = true := by decide +kernel

def images : List (Except String (List Runner.B)) :=
  [image13,
   imageOf (overlap 9 (by decide) (2 ^ 71 + 2 ^ 64 + 42) (by decide) (by decide)),
   imageOf (overlap 16 (by decide) (2 ^ 127 + 2 ^ 64 + 42) (by decide) (by decide)),
   imageOf (overlap 17 (by decide) (2 ^ 135 + 2 ^ 128 + 42) (by decide) (by decide)),
   imageOf (overlap 9 (by decide) 0 (by decide) (by decide))]

theorem byteSpan_images_zeuge : images.all (·.isOk) = true := by decide +kernel

/-- A two-chunk and a three-chunk value retain the first high byte and adjacent cells. -/
theorem byteSpan_model_zeuge :
    let z : Int := 2 ^ 135 + 2 ^ 128 + 42
    let σ := initial.schreibBytes tab field rfl [] 2 (zahlZuBytes 17 z)
    (eval σ (read 17 2 (by decide)) σ .nil).n = z ∧
      (σ.slots tab 18 field).n = 129 ∧ (σ.slots tab 1 field).n = 0 ∧
      (σ.slots tab 19 field).n = 0 := by decide +kernel

/-- The first unrepresentable byte offset is refused before code expansion. -/
theorem byteSpan_offset_refused_zeuge :
    readBytesWideL (layU u (fun _ => none) 65536) tab field
      (fun d => some ([], d)) (2 ^ 31) 4 = none := by rfl

/-- The write wrapper pins the identical limit independently of the value emitter. -/
theorem byteSpan_write_offset_refused_zeuge {D : Deklaration} (L : Lay D) (t : D.Tab)
    (f : D.Feld t) (upper : (2 ^ 31 : Int) ≤ D.count t) :
    putBytesWideL L (Γ := []) (Λ := []) t f 0 0 (2 ^ 31) (by decide) (by simpa using upper)
      (some ([], 4)) (some ([], 5)) 0 = none := by rfl

end Gabbro.Stage0.Senke.ByteSpanProbe
