/- Canonical source start arguments become static parameter bytes through the shared encoder.
   This does not activate parameterized image startup or replace its full ABI proof. -/
import Stage0.StartArgument
import Stage0.Senke.Welt.StartBytes
import Stage0.Senke.Ausdruck.Aggregat.Encoding

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

/-- Every canonically accepted start expression has the shared representation validity.
    Reference/IEEE/aggregate obligations are not bypassed: those forms have no uStartArg rule. -/
theorem startExpression_valid (u : Gabbro.Grammatik.Parser.Uebersetze.UProg) (ty : Ty)
    (arg : Gabbro.Grammatik.Parser.SExpr)
    (accepted : Gabbro.Grammatik.Parser.Uebersetze.uStartArg u.tabs ty arg = true)
    (L : Lay (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf u))
    (world : World (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf u)) :
    ValueValid L ty (eval world (StartArgument.expression u ty arg accepted) world .nil) := by
  cases ty <;> try trivial

/-- The complete recovered source environment satisfies every shared value validity
    obligation; there is no unchecked per-parameter validity premise at serialization. -/
theorem startArguments_valid (u : Gabbro.Grammatik.Parser.Uebersetze.UProg)
    (types : List Ty) (args : List Gabbro.Grammatik.Parser.SExpr)
    (checked : types.length = args.length ∧ (types.zip args).all
      (fun p => Gabbro.Grammatik.Parser.Uebersetze.uStartArg u.tabs p.1 p.2) = true)
    (L : Lay (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf u))
    (world : World (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf u)) :
    ∀ ty (x : Var types ty), ValueValid L ty
      ((evalArgs world (StartArgument.arguments u types args checked) world .nil).get x) := by
  induction types generalizing args with
  | nil => intro ty x; cases x
  | cons ty types ih =>
    cases args with
    | nil => have impossible : types.length + 1 = 0 := checked.1; omega
    | cons arg args =>
      intro shape x
      cases x with
      | here => exact startExpression_valid u ty arg _ L world
      | there x => exact ih args _ shape x

/-- Complete parameter words read back under the exact relocated layout used by encodeEnv.
    `frameOffset` is the callee frame within the root's stack (currently FB). -/
theorem startEnvBytes_words {D : Deklaration} (L : Lay D) {Γ : Ctx} (ρ : Env D Γ)
    {slots frameOffset reserved p : Nat} {bytes : List Runner.B}
    (made : startFrameBytes slots (frameOffset + FB + reserved) (encodeEnv L ρ) = some bytes)
    {m : Runner.Mem} (loaded : BytesAt m p bytes) :
    WordsAt m (slot (BitVec.ofNat 64 p) (BitVec.ofNat 64 frameOffset))
      (FB + reserved) (encodeEnv L ρ) := by
  intro i hi
  have read := startFrameBytes_read made loaded i hi
  have address : slot (slot (BitVec.ofNat 64 p) (BitVec.ofNat 64 frameOffset))
      (BitVec.ofNat 64 (FB + reserved + i)) =
      BitVec.ofNat 64 (p + 8 * (frameOffset + FB + reserved + i)) := by
    apply BitVec.eq_of_toNat_eq
    have h8 : (8 : Runner.W).toNat = 8 := rfl
    simp only [slot, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h8]
    omega
  rw [address]
  exact read

/-- The same constructed stack bytes have the allocated permissions and the complete
    canonical argument span. No assumed initial EnvAt or truncated scalar encoding occurs. -/
theorem startEnvBytes_frame {D : Deklaration} (L : Lay D) {Γ : Ctx} (ρ : Env D Γ)
    {slots frameOffset reserved p : Nat} {bytes : List Runner.B}
    (made : startFrameBytes slots (frameOffset + FB + reserved) (encodeEnv L ρ) = some bytes)
    {m : Runner.Mem} (loaded : BytesAt m p bytes) (room : p + 8 * slots < 2 ^ 64) :
    FrameOK m (BitVec.ofNat 64 p) slots ∧
      WordsAt m (slot (BitVec.ofNat 64 p) (BitVec.ofNat 64 frameOffset))
        (FB + reserved) (encodeEnv L ρ) :=
  ⟨startFrameBytes_frame made loaded room, startEnvBytes_words L ρ made loaded⟩

/-- The checked source argument environment supplies both halves of the full ABI's
    envAt_encoding relation under the identical final layout and actual serialized bytes. -/
theorem sourceStartBytes_correct
    {u : Gabbro.Grammatik.Parser.Uebersetze.UProg}
    {items : List Gabbro.Grammatik.Parser.SItemTief} (start : StartArgument.SourceStart u items)
    (L : Lay (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf u))
    (world : World (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf u))
    {slots frameOffset reserved p : Nat} {bytes : List Runner.B}
    (made : startFrameBytes slots (frameOffset + FB + reserved)
      (encodeEnv L (start.resolved.environment world)) = some bytes)
    {m : Runner.Mem} (loaded : BytesAt m p bytes) (room : p + 8 * slots < 2 ^ 64) :
    FrameOK m (BitVec.ofNat 64 p) slots ∧
      (∀ ty (x : Var ((Gabbro.Grammatik.Parser.UebersetzeAllg.declOf u).params start.resolved.function) ty),
        ValueValid L ty ((start.resolved.environment world).get x)) ∧
      WordsAt m (slot (BitVec.ofNat 64 p) (BitVec.ofNat 64 frameOffset)) (FB + reserved)
        (encodeEnv L (start.resolved.environment world)) := by
  exact ⟨startFrameBytes_frame made loaded room,
    startArguments_valid u _ start.sourceArgs start.resolved.checked L world,
    startEnvBytes_words L _ made loaded⟩

/-- Bounds use the whole canonical context width, with no single-word parameter assumption. -/
theorem startEnvBytes_bound {D : Deklaration} (L : Lay D) {Γ : Ctx} (ρ : Env D Γ)
    {slots frameOffset reserved : Nat} {bytes : List Runner.B}
    (made : startFrameBytes slots (frameOffset + FB + reserved) (encodeEnv L ρ) = some bytes) :
    frameOffset + FB + reserved + contextWords Γ ≤ slots := by
  unfold startFrameBytes at made
  split at made
  · next room => simpa only [encodeEnv_length] using room
  · cases made

/-- Initializing the root's depth cache in header slot 2 preserves every parameter word,
    including the highest limb, because the complete parameter span lies above the header. -/
theorem startEnvWords_depth [Kern] {m : Runner.Mem} {fp : Runner.W}
    {K frameOffset reserved : Nat} {words : List Runner.W} (depth : Nat)
    (frame : FrameOK m fp K)
    (bound : frameOffset + FB + reserved + words.length ≤ K)
    (above : 3 ≤ frameOffset + FB + reserved)
    (parameters : WordsAt m (slot fp (BitVec.ofNat 64 frameOffset)) (FB + reserved) words) :
    WordsAt (Runner.Mem.write m (slot fp (BitVec.ofNat 64 2)) 8 depth)
      (slot fp (BitVec.ofNat 64 frameOffset)) (FB + reserved) words := by
  intro i hi
  have read := parameters i hi
  rw [slot_slot] at read ⊢
  rw [rd_other frame.room (by omega) (by omega) (by omega)]
  exact read

end Gabbro.Stage0.Senke
