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

def second : Resolved witnessUnit "worker" [.lit 2, .fls] :=
  ((resolve witnessUnit "worker" [.lit 2, .fls]).toOption).get (by rfl)

def sourceFirst : SourceStart witnessUnit [.concT witnessGroup] :=
  ⟨witnessGroup, by simp, ["worker"], [.lit 7, .tru], by simp [witnessGroup], "worker", rfl, first⟩

def sourceSecond : SourceStart witnessUnit [.concT witnessGroup] :=
  ⟨witnessGroup, by simp, ["worker"], [.lit 2, .fls], by simp [witnessGroup], "worker", rfl, second⟩

def frames : List (List Runner.W) :=
  [encodeEnv layout (first.environment world), encodeEnv layout (second.environment world)]

def frameImageBytes : List Runner.B := (startStackBytes 16 8 frames).getD []

/-- Repeated starts of one function occupy different frames in the same actual byte memory. -/
theorem startStackBytes_frame_zeuge :
    startStackBytes 16 8 frames = some frameImageBytes ∧
    WordsAt (loadedMemory 4096 frameImageBytes) (slot 4096 4) 4 (encodeEnv layout (first.environment world)) ∧
    WordsAt (loadedMemory 4096 frameImageBytes) (slot 4224 4) 4 (encodeEnv layout (second.environment world)) := by
  have made : startStackBytes 16 8 frames = some frameImageBytes := rfl
  have loaded := loadedMemory_at 4096 frameImageBytes (by rw [startStackBytes_length made]; decide)
  obtain ⟨b0, h0, l0⟩ := startStackBytes_frame made 4096 loaded 0 (by decide)
  obtain ⟨b1, h1, l1⟩ := startStackBytes_frame made 4096 loaded 1 (by decide)
  exact ⟨made, startEnvBytes_words layout (first.environment world) (frameOffset := 4)
    (reserved := 0) h0 l0, startEnvBytes_words layout (second.environment world)
    (frameOffset := 4) (reserved := 0) h1 l1⟩

/-- Full source provenance, representation validity and actual bytes hold jointly. -/
theorem sourceStartBytes_correct_zeuge :
    FrameOK (loadedMemory 4096 firstBytes) 4096 16 ∧
    (∀ ty (x : Var ((declOf witnessUnit).params first.function) ty),
      ValueValid layout ty ((first.environment world).get x)) ∧
    WordsAt (loadedMemory 4096 firstBytes) (slot 4096 4) 4 (encodeEnv layout (first.environment world)) := by
  have made : startFrameBytes 16 8 (encodeEnv layout (first.environment world)) = some firstBytes := rfl
  exact sourceStartBytes_correct sourceFirst layout world (frameOffset := 4) (reserved := 0)
    made (loadedMemory_at 4096 firstBytes (by rw [startFrameBytes_length made]; decide)) (by decide)

#print axioms startStackBytes_frame_zeuge
#print axioms sourceStartBytes_correct_zeuge

/-- Static source parameters leave the depth header and the following result area untouched. -/
theorem startFrameBytes_outside_zeuge :
    (loadedMemory 4096 firstBytes).rd64 (BitVec.ofNat 64 (4096 + 8 * 2)) = some 0 ∧
    (loadedMemory 4096 firstBytes).rd64 (BitVec.ofNat 64 (4096 + 8 * 10)) = some 0 := by
  have made : startFrameBytes 16 8 (encodeEnv layout (first.environment world)) = some firstBytes := rfl
  have loaded := loadedMemory_at 4096 firstBytes (by rw [startFrameBytes_length made]; decide)
  exact ⟨startFrameBytes_outside made loaded 2 (by decide) (Or.inl (by decide)),
    startFrameBytes_outside made loaded 10 (by decide) (Or.inr (by decide))⟩

/-- The real depth write preserves every source parameter word in the mapped frame. -/
theorem startEnvWords_depth_zeuge [Kern] :
    WordsAt (Runner.Mem.write (loadedMemory 4096 firstBytes) (slot 4096 2) 8 5)
      (slot 4096 4) 4 (encodeEnv layout (first.environment world)) := by
  obtain ⟨made, frame, parameters⟩ := startEnvBytes_frame_zeuge
  exact startEnvWords_depth (m := loadedMemory 4096 firstBytes) (fp := 4096)
    (K := 16) (frameOffset := 4) (reserved := 0)
    (words := encodeEnv layout (first.environment world)) 5 frame (by decide) (by decide) parameters

#print axioms startFrameBytes_outside_zeuge
#print axioms startEnvWords_depth_zeuge

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
