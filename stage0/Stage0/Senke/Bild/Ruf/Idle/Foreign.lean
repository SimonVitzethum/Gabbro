module

public import Stage0.Senke.Bild.Ruf.Idle.ABI

@[expose] public section

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration}

private theorem ptrParam_tyR (types : List Ty) :
    ptrParam (types.map tyR) = ptrParam types := by
  have same : isPtr ∘ tyR = isPtr := funext isPtr_tyR
  simp only [ptrParam, List.findIdx?_map, same, List.getElem?_map]
  split
  · next index located =>
    cases present : types[index]? with
    | none => rfl
    | some type => cases type <;> rfl
  · rfl

private theorem pointerCount_tyR (types : List Ty) :
    ((types.map tyR).filter isPtr).length = (types.filter isPtr).length := by
  induction types with
  | nil => rfl
  | cons type tail ih =>
    simp only [List.map_cons, List.filter_cons, isPtr_tyR]
    split <;> simp only [List.length_cons, ih]

private theorem packJ_withIdle (L : Lay D) (t : D.Tab) (f : D.Feld t) (count row scratch tmp : Nat) :
    ∀ bytes, packJ L.withIdle t f count row scratch tmp bytes = packJ L t f count row scratch tmp bytes
  | 0 => rfl
  | bytes + 1 => by simp only [packJ, L.withIdle_elem, packJ_withIdle L t f count row scratch tmp bytes]

private theorem packI_withIdle (L : Lay D) (t : D.Tab) (f : D.Feld t) (count base scratch tmp : Nat) :
    ∀ words, packI L.withIdle t f count base scratch tmp words = packI L t f count base scratch tmp words
  | 0 => rfl
  | words + 1 => by
    simp only [packI, packJ_withIdle, packI_withIdle L t f count base scratch tmp words]

private theorem unpackK_withIdle (L : Lay D) (t : D.Tab) (f : D.Feld t) (base scratch : Nat) :
    ∀ count, unpackK L.withIdle t f base scratch count = unpackK L t f base scratch count
  | 0 => rfl
  | count + 1 => by simp only [unpackK, L.withIdle_elem, unpackK_withIdle L t f base scratch count]

private theorem byteType_tyR (ty : Ty) : (tyR ty = .int 0 255) ↔ ty = .int 0 255 := by
  cases ty <;> simp only [tyR, Ty.mapNumbers, reduceCtorEq]

/-- Buffer packing, register arguments and the selected syscall row keep their exact bytes. -/
theorem torC_withIdle (L : Lay D) {Γ : Ctx} {Λ : List (Res D)} (a : D.Ax)
    (args : Args D Γ Λ (D.aparams a)) (dest reserved : Nat) :
    torC L.withIdle a (ruA args) dest reserved = torC L a args dest reserved := by
  have binding : L.withIdle.tor a = L.tor a := rfl
  have width : (D.mitRuhe.aparams a).length = (D.aparams a).length := List.length_map tyR
  have types : (D.mitRuhe.aparams a).all wortTy = (D.aparams a).all wortTy := by
    change ((D.aparams a).map tyR).all _ = _
    simp only [List.all_map, Function.comp_def, wortTy_tyR]
  have pointer : ptrParam (D.mitRuhe.aparams a) = ptrParam (D.aparams a) := ptrParam_tyR _
  have count : ((D.mitRuhe.aparams a).filter isPtr).length = ((D.aparams a).filter isPtr).length :=
    pointerCount_tyR _
  have table : D.mitRuhe.tabNr = D.tabNr := rfl
  have bytes : L.withIdle.byte = L.byte := rfl
  have extent : D.mitRuhe.count = D.count := rfl
  have byteType (t : D.Tab) (f : D.Feld t) : (D.mitRuhe.typ t f = .int 0 255) ↔
      D.typ t f = .int 0 255 := byteType_tyR _
  simp only [torC, binding, width, types, pointer, count, table, bytes, extent,
    L.withIdle_count, lowR_withIdle, byteType, packI_withIdle, unpackK_withIdle]
  cases selected : L.tor a with
  | none => rfl
  | some row =>
    by_cases allowed : torGut row (D.aparams a).length = true ∧ (D.aparams a).all wortTy = true
    · simp only [allowed, and_self, ite_true]
      cases buffer : ptrParam (D.aparams a) with
      | none => rfl
      | some info =>
        obtain ⟨index, number, writable⟩ := info
        cases found : D.tabNr number with
        | none => rfl
        | some table =>
          cases field : L.byte table <;> rfl
    · simp only [allowed, ite_false]

theorem torC0_withIdle (L : Lay D) {Γ : Ctx} {Λ : List (Res D)} (a : D.Ax)
    (args : Args D Γ Λ (D.aparams a)) (dest reserved : Nat) :
    torC0 L.withIdle a (ruA args) dest reserved = torC0 L a args dest reserved := by
  have reasons : D.mitRuhe.agruende a = D.agruende a := rfl
  simp only [torC0, reasons, torC_withIdle]

private theorem chkC_tyR (result : Option Ty) (dest : Nat) :
    chkC (result.map tyR) dest = chkC result dest := by
  cases result with
  | none => rfl
  | some ty => cases ty <;> rfl

private theorem fallibleTy_tyR (ty : Ty) : fallibleTy (tyR ty) = fallibleTy ty := by
  cases ty <;> rfl

theorem plainForeignC_withIdle (L : Lay D) {Γ : Ctx} {Λ : List (Res D)} (a : D.Ax)
    (args : Args D Γ Λ (D.aparams a)) (ty : Ty) (dest reserved : Nat) :
    plainForeignC L.withIdle a (ruA args) (tyR ty) dest reserved =
      plainForeignC L a args ty dest reserved := by
  have area : usesArea L.withIdle a = usesArea L a := rfl
  have reasons : D.mitRuhe.agruende a = D.agruende a := rfl
  have checks : chkC (D.mitRuhe.aerg a) dest = chkC (D.aerg a) dest := chkC_tyR _ _
  have width : valueWords (tyR ty) = valueWords ty := valueWords_mapNumbers (· + 1) id _
  simp only [plainForeignC, area, reasons, areaC_withIdle, torC0_withIdle, checks, width]

theorem fallibleForeignC_withIdle (L : Lay D) {Γ : Ctx} {Λ : List (Res D)} (a : D.Ax)
    (args : Args D Γ Λ (D.aparams a)) (ty : Ty) (dest skip reserved : Nat) :
    fallibleForeignC L.withIdle a (ruA args) (tyR ty) dest skip reserved =
      fallibleForeignC L a args ty dest skip reserved := by
  have binding : L.withIdle.tor a = L.tor a := rfl
  have area : usesArea L.withIdle a = usesArea L a := rfl
  have reasons : D.mitRuhe.agruende a = D.agruende a := rfl
  have checks : chkC (some (tyR ty)) dest = chkC (some ty) dest := chkC_tyR (some ty) dest
  have receive : areaReceive (tyR ty) dest = areaReceive ty dest := by
    simp only [areaReceive, tyR, valueWords_mapNumbers]
  simp only [fallibleForeignC, binding, area, reasons, areaC_withIdle, torC_withIdle,
    fallibleTy_tyR, checks, receive]

end Gabbro.Stage0.Senke
