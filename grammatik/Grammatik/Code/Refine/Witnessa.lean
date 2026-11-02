module
public import Grammatik.Code.Refine.Witness
@[expose] public section


namespace Gabbro.Code.Lower.Wit

open Gabbro.Grammatik

/-! ## 5. At the 32-bit big-endian target -/

section C32

local instance conf32 : Conf := ⟨32, true, Or.inl rfl⟩

/-- The lowering covers the whole program: all four functions lower. -/
theorem wit32_lowers : ∀ f, ∃ func, lowerFn wLay wP f (wName f) = some func ∧ wMod.funs[wLay.fno f]? = some func := by
  intro f
  cases f
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩

/-- **The closing theorem, instantiated**: for every recursion depth, the lowered functions refine the
    source meaning of a call. -/
theorem wit32_callref (S : Sees) (passes : Nat) :
    ∀ n, CallRef wLay wMod S (rufAt wP wO passes n) :=
  lowerFn_callref wLay wLayOk wP wO passes wMod S wName wit32_lowers

/-- The loop is a loop: `wipe` lowers to eight blocks (entry, the four blocks of the counter loop, the
    two blocks of its body, the return). -/
theorem wit32_wipe_blocks : (lowerFn wLay wP WFn.wipe "wipe").map (·.blks.length) = some 8 := by rfl

/-- The calling function has the calls, the `narrow` and the `retry`: seventeen blocks. -/
theorem wit32_main_blocks : (lowerFn wLay wP WFn.main "main").map (·.blks.length) = some 17 := by rfl

/-- The three matches lower, at the other target too. -/
theorem wit32_mt_forms : (lowerFn wLay wP WFn.mt "mt").map (fun f =>
    usesTerm (fun | .sw .. => true | _ => false) f && usesTerm (fun | .brc .slt .. => true | _ => false) f &&
    usesOp .urem f && usesOp .udiv f) = some true := by decide +kernel

/-- The failure channel lowers at the other target too. -/
theorem wit32_fail_forms : (lowerFn wLay wP WFn.fail "fail").map (fun f => usesOp .mul f) = some true ∧
    (lowerFn wLay wP WFn.callf "callf").map (fun f => usesOp .urem f && usesOp .udiv f && usesOp .sub f) =
      some true := by
  constructor <;> decide +kernel

/-- The signed and bitwise forms lower at the other target too. -/
theorem wit32_bits_forms : (lowerFn wLay wP WFn.bits "bits").map (fun f =>
    usesOp .sdiv f && usesOp .srem f && usesOp .and f && usesOp .or f && usesOp .xor f && usesOp .shl f &&
    usesOp .lshr f) = some true := by decide +kernel

/-- The premise of `CallRef` is not vacuous: the source meaning of `get(1)` is an `ok`. -/
theorem wit32_get_ok : ∃ σ' v, rufAt wP wO 0 1 WFn.get w0 (argEnv 1 (by decide) (by decide)) =
    RufAusgang.ok σ' v := ⟨_, _, rfl⟩

/-- `put` lowers its division to an unsigned division, `get` its remainder to an unsigned remainder. -/
theorem wit32_put_udiv : (lowerFn wLay wP WFn.put "put").map (usesOp .udiv) = some true := by decide +kernel

theorem wit32_get_urem : (lowerFn wLay wP WFn.get "get").map (usesOp .urem) = some true := by decide +kernel

end C32

end Gabbro.Code.Lower.Wit
