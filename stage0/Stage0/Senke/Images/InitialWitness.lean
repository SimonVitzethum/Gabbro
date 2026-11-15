/- Small canonical-source fixture for complete initialized image bytes.
   No source parser/kernel execution or compiler build is performed by this fixture. -/
module
public import Stage0.Senke.Images.InitialRead
@[expose] public section

namespace Gabbro.Stage0.Senke.InitialProbe
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR

/-- A wide field, nested array, empty product and typed product sum payload. -/
def shape : Ty := .prod 101 [
  .int 0 (2 ^ 128 - 1), .arr (.arr .bool 2) 2, .prod 102 [],
  .sum [none, some (.prod 103 [.int 0 100, .bool])]]

def sourceUnit : UProg := {
  tabs := [{name := "Cells", count := 2, cols := [("matrix", (0, 0))],
    werte := [("matrix", .arr (.arr (.int 0 255) 2) 2)]}]
  locks := [{name := "CellsLock", rank := 0, guard := ["Cells"]}]
  fns := []
  globs := [
    {name := "PREFIX", ty := .int 0 255, init := 19},
    {name := "RECORD", ty := .wert shape, init := 0,
      initK := .product 101 [
        .zahl (2 ^ 80 + 7),
        .cons (.cons (.wahr true) (.cons (.wahr false) .nil))
          (.cons (.cons (.wahr false) (.cons (.wahr true) .nil)) .nil),
        .product 102 [], .fall 1 (.product 103 [.zahl 37, .wahr true])],
      placement := some ⟨["RECORD"], 64, none, true⟩},
    {name := "EMPTY", ty := .wert (.prod 104 []), init := 0, initK := .product 104 []}] }

theorem initialValid : GabbroV.sp0OkB sourceUnit = true := by decide +kernel

def layout : Lay (declOf sourceUnit) := {
  layU sourceUnit (fun _ => none) (Runner.Prog.IMG + 192) with
  sb := Runner.Prog.IMG + 32
  st := 128 }

def image : Bild (declOf sourceUnit) where
  code := [ci 1 2 4 0]
  A f := Fin.elim0 f
  fp0 := Runner.Prog.IMG + 32
  K := 50
  Ks := 16
  Y := layout
  depth := 0
  passes := 1
  roots := []
  args := []
  rootArgs := []
  baseReq := 64

def bytes : List Runner.B := image.initializedBytes sourceUnit initialValid

def memory : Runner.Mem where
  b a := (bytes[a.toNat - Runner.Prog.IMG]?).getD 0
  rd _ := true
  wr _ := true

private theorem loaded : BytesAt memory Runner.Prog.IMG bytes := by
  intro i hi
  refine ⟨rfl, rfl, ?_⟩
  have size : bytes.length = 432 := by decide +kernel
  have address : (BitVec.ofNat 64 (Runner.Prog.IMG + i)).toNat - Runner.Prog.IMG = i := by
    simp only [BitVec.toNat_ofNat]
    change i < bytes.length at hi
    simp only [Runner.Prog.IMG] at *
    omega
  change (bytes[(BitVec.ofNat 64 (Runner.Prog.IMG + i)).toNat - Runner.Prog.IMG]?).getD 0 = bytes[i]
  rw [address, List.getElem?_eq_getElem hi]
  rfl

private theorem storage : InitialLayout sourceUnit image.Y := by
  refine ⟨fun _ => rfl, fun _ _ => rfl, rfl, fun t => ?_⟩
  simp only [image, layout, Lay.count, layU, ite_self, Int.natCast_zero, Int.add_zero]

/-- All representation duties and nonzero declared source fields survive, including
    the high limb, nested Boolean array, empty marker and tagged product payload. -/
theorem initialWorldBytes_zeuge :
    GabbroV.sp0OkB sourceUnit = true ∧
    encodeWords layout shape ((initialWorld sourceUnit initialValid).globs ⟨1, by decide⟩) =
      [7, 65536, 1, 0, 0, 1, 0, 1, 37, 1] ∧
    encodeWords layout (.prod 104 []) ((initialWorld sourceUnit initialValid).globs ⟨2, by decide⟩) = [0] ∧
    (initialGlobals sourceUnit initialValid layout).length = 152 ∧
    (initialWorldBytes sourceUnit initialValid layout).length = 216 ∧
    layout.ga ⟨1, by decide⟩ = Runner.Prog.IMG + 256 ∧
    layout.elem ⟨0, by decide⟩ ⟨0, by decide⟩ 1 = Runner.Prog.IMG + 376 := by
  exact ⟨initialValid, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Every premise of the single-payload loaded-image theorem holds jointly. The fixture
    has a genuine alignment gap, a nonzero wide record, two full nested-array cells,
    complete startup bytes and a nonempty free-lock suffix. -/
theorem initializedBytes_loaded_zeuge :
    bytes.length = image.bytes.length ∧
    (bytes.take (image.Y.lo - Runner.Prog.IMG) = image.bytes.take (image.Y.lo - Runner.Prog.IMG)) ∧
    (bytes.drop (image.Y.hi - Runner.Prog.IMG) = image.bytes.drop (image.Y.hi - Runner.Prog.IMG)) ∧
    WeltAt memory image.Y (initialWorld sourceUnit initialValid) ∧
    BytesAt memory image.Y.hi (List.replicate (image.Y.sye - image.Y.hi) 0) := by
  have made : startStackBytes image.Ks (FB + FB) (image.args :: image.rootArgs) =
      some (List.replicate 128 0) := by decide +kernel
  have all := image.initializedBytes_loaded initialValid storage made (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) loaded
  exact ⟨image.initializedBytes_length initialValid storage (by decide +kernel) (by decide +kernel),
    image.initializedBytes_take initialValid (by decide +kernel),
    image.initializedBytes_drop initialValid storage (by decide +kernel) (by decide +kernel), all.2.2⟩

/-- The high word and the selected sum payload read from the emitted bytes. This
    cannot be satisfied by a zero image or a low-word-only initializer. -/
theorem initializedBytes_readback_zeuge :
    memory.rd64 (BitVec.ofNat 64 (Runner.Prog.IMG + 264)) = some 65536 ∧
    memory.rd64 (BitVec.ofNat 64 (Runner.Prog.IMG + 320)) = some 37 ∧
    memory.rd64 (BitVec.ofNat 64 (Runner.Prog.IMG + 336)) = some 0 ∧
    memory.rd64 (BitVec.ofNat 64 (Runner.Prog.IMG + 424)) = some 0 := by
  decide +kernel

/-- The existing source check still refuses an unspecified product initializer.
    No field is silently defaulted to make a world exist. -/
theorem product_without_initializer_refused_zeuge :
    GabbroV.sp0OkB {sourceUnit with globs := [
      {name := "MISSING", ty := .wert shape, init := 0, initK := .null}]} = false := by
  decide +kernel

end Gabbro.Stage0.Senke.InitialProbe
