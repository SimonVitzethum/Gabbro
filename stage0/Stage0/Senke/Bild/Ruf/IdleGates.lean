module

public import Stage0.Senke.Bild.Ruf.GateTrace
import Stage0.Senke.Welt.Spans.IdleValue
import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre.Teil1

@[expose] public section

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR

variable {D : Deklaration}

private theorem ptrParam_tyR (types : List Ty) :
    ptrParam (types.map tyR) = ptrParam types := by
  have same : (isPtr ∘ tyR) = isPtr := by
    funext ty
    cases ty <;> rfl
  simp only [ptrParam, List.findIdx?_map, same]
  cases types.findIdx? isPtr with
  | none => rfl
  | some i =>
    simp only [List.getElem?_map]
    cases types[i]? with
    | none => rfl
    | some ty =>
      cases ty <;> try rfl
      case ptr p =>
        rcases p with ⟨bits, ⟨read, write, logical⟩, ⟨table⟩⟩
        cases bits <;> cases read <;> cases logical <;> rfl

private theorem WeltOhne.withIdle {L : Lay D} {m : Mem} {world : World D}
    {table : D.Tab} {field : D.Feld table} (stored : WeltOhne m L world table field) :
    WeltOhne m L.withIdle (worldR world) table field := by
  refine ⟨?_, fun g => (stored.2 g).withIdle⟩
  intro t f i bound different
  rw [Lay.withIdle_elem]
  exact (stored.1 t f i bound (fun j equal => different j (congrArg Zelle.withIdle equal))).withIdle

/-- The same declared software contract serves every gate in the goal machine.
    The transport preserves scalar replies, byte buffers and the full
    caller-owned result area. -/
theorem TorOK.withIdle [Kern] {L : Lay D} {O : Orakel D} (contract : TorOK L O) :
    TorOK L.withIdle O.mitRuhe := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b bound admitted scalar world args q m number registers unused stored
    rw [← worldR_worldZ world] at stored ⊢
    rw [← envR_envZ (Γ := D.aparams a) args] at registers ⊢
    rw [wirkt_mitRuhe]
    have scalar' : ptrParam (D.aparams a) = none := (ptrParam_tyR _).symm.trans scalar
    obtain ⟨w, x, after, answer, effects, represented, raw⟩ :=
      contract.ans a b bound (by simpa only [Deklaration.mitRuhe, List.length_map] using admitted)
        scalar' (worldZ world) (envZ args) q m number ((ArgsW.withIdle_iff _ _).mp registers)
        (by simpa only [Deklaration.mitRuhe, List.length_map] using unused)
        (WeltAt.withIdle_iff.mp stored)
    exact ⟨w, x, after, answer, effects, WeltAt.withIdle_iff.mpr represented, raw⟩
  · intro a b bound admitted j n write table field buffer tableNumber byteField byteType
      world args q m number registers unused stored packed
    rw [← worldR_worldZ world] at stored ⊢
    rw [← envR_envZ (Γ := D.aparams a) args] at registers ⊢
    rw [wirkt_mitRuhe]
    have buffer' : ptrParam (D.aparams a) = some (j, n, write) :=
      (ptrParam_tyR _).symm.trans buffer
    have byteType' : D.typ table field = .int 0 255 := by
      change tyR (D.typ table field) = .int 0 255 at byteType
      cases D.typ table field with
      | ptr pointer => rcases pointer with ⟨_, _, ⟨_⟩⟩; cases byteType
      | int lo hi => exact byteType
      | _ => cases byteType
    have packed' : ∀ i, i < pufW (D.count table).toNat →
        m.rd64 (reqArg q j + BitVec.ofNat 64 (8 * i)) =
          some (packV (fun k => wAt m (L.elem table field k)) (D.count table).toNat i 8) := by
      simpa only [Lay.withIdle_elem] using packed
    obtain ⟨w, x, after, answer, readMap, writeMap, effects, other, bytes, raw⟩ :=
      contract.puf a b bound (by simpa only [Deklaration.mitRuhe, List.length_map] using admitted)
        j n write table field buffer' tableNumber byteField byteType'
        (worldZ world) (envZ args) q m number ((ArgsW.withIdle_iff _ _).mp registers)
        (by simpa only [Deklaration.mitRuhe, List.length_map] using unused)
        (WeltAt.withIdle_iff.mp stored) packed'
    refine ⟨w, x, after, answer, readMap, writeMap, effects, other.withIdle, ?_, raw⟩
    intro k inside
    rw [Lay.withIdle_elem]
    exact (Enc.withIdle_iff L _ (D.typ table field) _).mpr (bytes k inside)
  · intro a n typed bound world args raw classified nonnegative
    rw [← worldR_worldZ world, ← envR_envZ (Γ := D.aparams a) args, wirkt_mitRuhe] at classified
    have result : D.aerg a = some (.ref n) := by
      change (D.aerg a).map tyR = some (.ref n) at typed
      obtain ⟨ty, found, equal⟩ := Option.map_eq_some_iff.mp typed
      cases ty with
      | ptr pointer => rcases pointer with ⟨_, _, ⟨_⟩⟩; cases equal
      | ref number => cases equal; exact found
      | _ => cases equal
    exact contract.ref_answer a n result bound (worldZ world) (envZ args) raw classified nonnegative
  · intro a b ty typed j bound admitted world args q m fp base K frame fits layout below
      number registers destination unused stored
    have present : (D.aerg a).map tyR = some ty := typed
    obtain ⟨result, sourceResult, rfl⟩ := Option.map_eq_some_iff.mp present
    rw [← worldR_worldZ world] at stored ⊢
    rw [← envR_envZ (Γ := D.aparams a) args] at registers ⊢
    have extent : base + valueWords result ≤ K := by
      simpa only [tyR, valueWords_mapNumbers] using fits
    have originalLayout : LayIn L := by
      refine ⟨?_, ?_, layout.2.2⟩
      · intro t f i inside
        simpa only [Lay.withIdle_elem, Deklaration.mitRuhe, tyR, valueWords_mapNumbers] using layout.1 t f i inside
      · intro g
        simpa only [Deklaration.mitRuhe, tyR, valueWords_mapNumbers] using layout.2.1 g
    obtain ⟨tag, extra, after, answer, effects, represented, reply⟩ :=
      contract.area a b result sourceResult j bound
        (by simpa only [Deklaration.mitRuhe, List.length_map] using admitted)
        (worldZ world) (envZ args) q m fp base K frame extent originalLayout below number
        ((ArgsW.withIdle_iff _ _).mp registers) destination
        (by simpa only [Deklaration.mitRuhe, List.length_map] using unused) (WeltAt.withIdle_iff.mp stored)
    refine ⟨tag, extra, after, answer, ?_, ?_, reply.withIdle⟩
    · have sameWidth : valueWords (tyR result) = valueWords result := valueWords_mapNumbers _ _ _
      rw [sameWidth]
      exact ⟨effects.rd, effects.wr, effects.b⟩
    · rw [wirkt_mitRuhe]
      exact WeltAt.withIdle_iff.mpr represented

end Gabbro.Stage0.Senke
