/- Joint byte-loading and source-environment witnesses; these do not activate image startup. -/
import Stage0.StartArgumentProben
import Stage0.Senke.Welt.StartEnv

namespace Gabbro.Stage0.Senke.StartImageProbe
open Gabbro.Grammatik Runner.IR Gabbro.Stage0.StartArgument
open Gabbro.Grammatik.Parser.UebersetzeAllg

def world : World (declOf witnessUnit) := {
  slots := fun t => Fin.elim0 t
  globs := fun g => Fin.elim0 g
  spur := [] }

def layout : Lay (declOf witnessUnit) := {
  col := fun t => Fin.elim0 t
  ga := fun g => Fin.elim0 g
  lo := 8192
  hi := 8192
  tor := fun a => Fin.elim0 a
  byte := fun t => Fin.elim0 t }

def first : Resolved witnessUnit "worker" [.lit 7, .tru] :=
  ((resolve witnessUnit "worker" [.lit 7, .tru]).toOption).get (by rfl)

def firstBytes : List Runner.B :=
  (startFrameBytes 16 8 (encodeEnv layout (first.environment world))).getD []

def loadedMemory (p : Nat) (bytes : List Runner.B) : Runner.Mem := {
  b := fun a => (bytes[a.toNat - p]?).getD 0
  rd := fun _ => true
  wr := fun _ => true }

theorem loadedMemory_at (p : Nat) (bytes : List Runner.B) (fit : p + bytes.length < 2 ^ 64) :
    BytesAt (loadedMemory p bytes) p bytes := by
  intro i hi
  refine ⟨rfl, rfl, ?_⟩
  change (bytes[(BitVec.ofNat 64 (p + i)).toNat - p]?).getD 0 = bytes[i]
  have address : (BitVec.ofNat 64 (p + i)).toNat - p = i := by
    simp only [BitVec.toNat_ofNat]
    omega
  rw [address, List.getElem?_eq_getElem hi]
  rfl

/-- The actual two-word source environment, frame bytes, mapping and permissions jointly hold. -/
theorem startEnvBytes_frame_zeuge :
    startFrameBytes 16 8 (encodeEnv layout (first.environment world)) = some firstBytes ∧
    FrameOK (loadedMemory 4096 firstBytes) 4096 16 ∧
    WordsAt (loadedMemory 4096 firstBytes) (slot 4096 4) 4
      (encodeEnv layout (first.environment world)) := by
  have made : startFrameBytes 16 8 (encodeEnv layout (first.environment world)) = some firstBytes := by rfl
  have loaded := loadedMemory_at 4096 firstBytes (by rw [startFrameBytes_length made]; decide)
  exact ⟨made, startEnvBytes_frame layout (first.environment world) (frameOffset := 4)
    (reserved := 0) made loaded (by decide)⟩

/-- Serialization retains three unequal words including high bits; this is not a low-word witness. -/
def limbWords : List Runner.W := [7, 65536, 18446744073709551615]
def limbBytes : List Runner.B := (startFrameBytes 16 8 limbWords).getD []

theorem startFrameBytes_read_zeuge :
    startFrameBytes 16 8 limbWords = some limbBytes ∧
    ∀ i (hi : i < limbWords.length),
      (loadedMemory 4096 limbBytes).rd64 (BitVec.ofNat 64 (4096 + 8 * (8 + i))) = some limbWords[i] := by
  have made : startFrameBytes 16 8 limbWords = some limbBytes := rfl
  exact ⟨made, startFrameBytes_read made (loadedMemory_at 4096 limbBytes (by rw [startFrameBytes_length made]; decide))⟩

#print axioms startEnvBytes_frame
#print axioms startEnvBytes_words
#print axioms sourceStartBytes_correct
#print axioms startEnvWords_depth
#print axioms startArguments_valid
#print axioms startEnvBytes_frame_zeuge
#print axioms startFrameBytes_read_zeuge
end Gabbro.Stage0.Senke.StartImageProbe
