/- Code slices and concrete entry to the consuming image. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Emission
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Runtime.Teil1a
public import Stage0.Senke.Anweisung.SchleifeTeile
public section

namespace Gabbro.Stage0.Senke.Consuming
open Gabbro.Grammatik Runner Runner.IR

variable [Kern] {D : Deklaration} {L : Lay D}

/-- Every straight-line piece is present at the offset computed by the same
    symbolic assembler that produced the admitted instruction list. -/
theorem assembled_codeAt {m : Mem} {pc : W} {code : List II}
    (before : List Piece) (block : List II) (after : List Piece)
    (assembled : assemble (before ++ .code block :: after) = some code)
    (image : CodeAt m pc code) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * width before)) block := by
  obtain ⟨leading, suffix, eq, len⟩ := assemble_block before block after assembled
  subst code
  apply codeAt_at (xs := leading) (zs := suffix)
  · simpa only [List.append_assoc] using image
  · rw [len]

/-- The fuel initializer is an actual runner instruction in the assembled
    fragment. Its write lies in the source-derived reserved pair, keeps the
    relocated lexical environment and the caller's protected words, and
    enters the header with the semantic fuel encoded without wraparound. -/
theorem «initialize» {P : Programm D} {f : D.Fn} {Γ : Ctx}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W}
    {fp pc rp cfp : W} {K Ks lo reserved counter saved fuel failure : Nat}
    {pr : List Nat} {count bound : Int} {invariant member edge measure body code : List II}
    {σ σ0 : World D} {ρ : Env D Γ} {ρ0 : Env D (D.params f)} {m : Mem}
    (assembled : assemble (pieces (frei Γ reserved) counter saved fuel failure
      count bound invariant member edge measure body) = some code)
    (layout : WIn L fp Ks K)
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (surround : Umf L A C dv m fp Ks K)
    (head : Kopf L f m fp K rp cfp ρ0 P σ0) (world : WeltAt m L σ)
    (abi : (functionFrame P f).internalResult ≤ lo) (low : lo ≤ counter)
    (allocated : counter < FB + reserved) (room : frei Γ reserved ≤ K)
    (fuelBound : fuel < 2 ^ 31)
    (kept : ∀ j ∈ pr, j < K ∧ j ≠ counter) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 16, fp⟩ m' ∧ AgreeW L fp lo K m m' ∧
      PreS L m' pc fp K (frei Γ reserved) code ρ reserved ∧
      Umf L A C dv m' fp Ks K ∧ Kopf L f m' fp K rp cfp ρ0 P σ0 ∧
      WeltAt m' L σ ∧ Keeps fp pr m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 counter)) = some (BitVec.ofNat 64 fuel) := by
  have literal : lit32 (fuel : Int) = true := lit32_nat fuelBound
  have initial : travCountC counter (fuel : Int) = [ci 1 counter fuel 0] := by
    simp only [travCountC, literal, ↓reduceIte]
  obtain ⟨leading, suffix, eq, len⟩ := assemble_block []
    (travCountC counter (fuel : Int))
    (pieces (frei Γ reserved) counter saved fuel failure count bound
      invariant member edge measure body).tail assembled
  have empty : leading = [] := List.eq_nil_of_length_eq_zero len
  subst leading
  simp only [List.nil_append, initial] at eq
  have pre' : PreS L m pc fp K (frei Γ reserved)
      ([ci 1 counter fuel 0] ++ suffix) ρ reserved := by rw [← eq]; exact pre
  obtain ⟨m', run, frame, tailPre, surround', head', world', keeps, read⟩ :=
    reserved_literal_entry layout pre' surround head world abi low allocated room literal kept
  refine ⟨m', run.forget, frame, ?_, surround', head', world', keeps, ?_⟩
  · exact ⟨pre.ctx, pre.small, frameOK_agreeW pre.frame frame,
      codeAt_agreeWIn layout frame pre.code pre.far, pre.far,
      tailPre.env, trivial, wstab_true _ _⟩
  · simpa only [BitVec.ofInt_natCast] using read

end Gabbro.Stage0.Senke.Consuming
