/-
  File:      Grammatik/X86/BranchLayout.lean
  Subject:   Signed displacement bounds and layout facts for rel32 branches.

  Lane 423 (continuous reserve): exact encoded widths and checked
  displacement/layout facts for the existing rel32 branch and call
  encodings (`jump32`, `jumpIf32`, `call32`). Reuses the canonical
  `Codec` bytes, `Relokation` fit/patch arithmetic and `Ausfuehrung`
  witness memory; no second IR, executor, decoder or ISA model is
  created here.

  Consumer (single direct-compiler architecture): the future layout
  validator (`layoutOk`) and the bounded short-branch selection of
  DIRECT-COMPILER-DESIGN §2B. The certificate `ZweigBeleg` carries
  the FINAL start, FINAL length, selected form, resolved displacement
  and final target, so the checker recomputes next-RIP from carried
  data and never iterates a layout fixpoint. Length stability
  (`zweig_len_stabil_*`) is the precise reason rel32-only layouts
  need no relaxation round at all.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Relokation

namespace Gabbro.Grammatik.X86

/-! ## 1. Exact encoded widths of the rel32 branch/call forms. -/

/-- Exact length of an unconditional near jump: 1 opcode byte + 4
    displacement bytes. -/
theorem zweig_jump32_len (d : BitVec 32) :
    (encode (.jump32 d)).length = 5 := by
  simp [encode, length_leBytes32]

/-- Exact length of a conditional near jump: 2 opcode bytes + 4
    displacement bytes. -/
theorem zweig_jumpIf32_len (c : Bedingung) (d : BitVec 32) :
    (encode (.jumpIf32 c d)).length = 6 := by
  simp [encode, length_leBytes32]

/-- Exact length of a direct near call: 1 opcode byte + 4
    displacement bytes. -/
theorem zweig_call32_len (d : BitVec 32) :
    (encode (.call32 d)).length = 5 := by
  simp [encode, length_leBytes32]

/-- NO LAYOUT OPTIMISM (jump): changing the displacement never moves
    the encoded length, so resolving a displacement never shifts
    another instruction start. -/
theorem zweig_len_stabil_jump32 (d1 d2 : BitVec 32) :
    (encode (.jump32 d1)).length = (encode (.jump32 d2)).length := by
  rw [zweig_jump32_len, zweig_jump32_len]

/-- NO LAYOUT OPTIMISM (conditional jump): same, for `jumpIf32`. -/
theorem zweig_len_stabil_jumpIf32 (c : Bedingung) (d1 d2 : BitVec 32) :
    (encode (.jumpIf32 c d1)).length =
      (encode (.jumpIf32 c d2)).length := by
  rw [zweig_jumpIf32_len, zweig_jumpIf32_len]

/-- NO LAYOUT OPTIMISM (call): same, for `call32`. -/
theorem zweig_len_stabil_call32 (d1 d2 : BitVec 32) :
    (encode (.call32 d1)).length = (encode (.call32 d2)).length := by
  rw [zweig_call32_len, zweig_call32_len]

/-! ## 2. Signed displacement: bounds and rel32 fit. -/

/-- Signed value of a 32-bit displacement field: the two's-complement
    reading of the codec word. This is the value the layout equation
    and the relocation fit check speak about. -/
def dispSigned (d : BitVec 32) : Int :=
  if d.toNat < 2147483648 then (d.toNat : Int)
  else (d.toNat : Int) - 4294967296

/-- Every displacement field value lies in signed-32 range. -/
theorem dispSigned_schranke (d : BitVec 32) :
    -2147483648 ≤ dispSigned d ∧ dispSigned d < 2147483648 := by
  have h := d.isLt
  by_cases hc : d.toNat < 2147483648
  · simp only [dispSigned, if_pos hc]
    omega
  · simp only [dispSigned, if_neg hc]
    omega

/-- Every displacement field value passes the relocation fit check:
    width-level refusal never fires for a decoded rel32 field; the
    check bites only at layout level (target minus next-RIP). -/
theorem dispSigned_passt (d : BitVec 32) :
    rel32Passt (dispSigned d) = true := by
  have h := dispSigned_schranke d
  simp only [rel32Passt, decide_eq_true_eq]
  exact h

/-! ## 3. Codec/relocation byte bridge. -/

/-- The relocation encoder reproduces the codec word: the unsigned
    representative of the signed displacement is the field value. -/
theorem rel32Enc_dispSigned (d : BitVec 32) :
    rel32Enc (dispSigned d) = d.toNat := by
  have h := d.isLt
  by_cases hc : d.toNat < 2147483648
  · have heq2 : dispSigned d = (d.toNat : Int) := by
      unfold dispSigned
      rw [if_pos hc]
    unfold rel32Enc tcNat
    rw [if_pos (by omega : (0 : Int) ≤ dispSigned d), heq2]
    simp
  · have hneg : dispSigned d < 0 := by
      unfold dispSigned
      rw [if_neg hc]
      omega
    have heq : dispSigned d + ((4294967296 : Nat) : Int) =
        (d.toNat : Int) := by
      unfold dispSigned
      rw [if_neg hc]
      omega
    unfold rel32Enc tcNat
    rw [if_neg (by omega : ¬ (0 : Int) ≤ dispSigned d), heq]
    simp

/-- The relocation bytes of the signed displacement are exactly the
    codec bytes of the field: one layout vocabulary, not two. -/
theorem rel32Bytes_dispSigned (d : BitVec 32) :
    rel32Bytes (dispSigned d) = leBytes32 d := by
  have henc := rel32Enc_dispSigned d
  have hbyte : ∀ n : Nat, BitVec.ofNat 8 n = natByte (n % 256) := by
    intro n
    unfold natByte
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have h256 : (2 ^ 8 : Nat) = 256 := rfl
    rw [h256]
    omega
  unfold rel32Bytes leBytes32
  simp only [rel32Byte]
  rw [henc]
  simp only [hbyte]

/-- Codec bytes sign-extend back to the signed displacement, through
    the relocation round-trip: the final-layout dependency in one
    equation. -/
theorem leBytes32_decode_signed (d : BitVec 32) :
    rel32DecOpt (leBytes32 d) = some (dispSigned d) := by
  have hbridge := rel32Bytes_dispSigned d
  have hschranke := dispSigned_schranke d
  rw [← hbridge]
  exact rel32_rundgang _ hschranke.1 hschranke.2

/-! ## 4. Layout certificate with exact widths. -/

/-- Branch width class: only the wide rel32 form has native bytes.
    `kurz` names the future rel8 selection (EB / 70+code, 2 bytes);
    it has no decoder row and is always refused. -/
inductive ZweigForm where
  | weit
  | kurz
  deriving DecidableEq, Repr

/-- Displacement width in bytes: 4 for rel32, 1 for the future rel8. -/
def zweigBreite : ZweigForm → Nat
  | .weit => 4
  | .kurz => 1

/-- The accepted displacement width is four bytes. -/
theorem zweigBreite_weit : zweigBreite .weit = 4 := by
  rfl

/-- Full encoded length: opcode bytes plus displacement width.
    Unconditional jump/call carry 1 opcode byte, conditional jumps 2;
    the future short form would carry 1 opcode byte plus 1. -/
def zweigLaenge (bedingt : Bool) : ZweigForm → Nat
  | .weit => if bedingt then 6 else 5
  | .kurz => 2

/-- The wide lengths are exactly 5/6 by condition. -/
theorem zweigLaenge_weite (bedingt : Bool) :
    zweigLaenge bedingt .weit = if bedingt then 6 else 5 := by
  cases bedingt <;> rfl

/-- The carried lengths agree with the canonical encoder: jump. -/
theorem zweigLaenge_codec_jump32 (d : BitVec 32) :
    (encode (.jump32 d)).length = zweigLaenge false .weit := by
  rw [zweig_jump32_len]
  decide

/-- The carried lengths agree with the canonical encoder:
    conditional jump. -/
theorem zweigLaenge_codec_jumpIf32 (c : Bedingung) (d : BitVec 32) :
    (encode (.jumpIf32 c d)).length = zweigLaenge true .weit := by
  rw [zweig_jumpIf32_len]
  decide

/-- The carried lengths agree with the canonical encoder: call. -/
theorem zweigLaenge_codec_call32 (d : BitVec 32) :
    (encode (.call32 d)).length = zweigLaenge false .weit := by
  rw [zweig_call32_len]
  decide

/-- Layout certificate for one direct branch/call site: the FINAL
    instruction start, the FINAL encoded length, the selected form,
    the resolved displacement and the final target. The checker
    recomputes next-RIP from the carried final length, so no
    fixpoint iteration over layouts is ever assumed. -/
structure ZweigBeleg where
  start : Nat
  len : Nat
  form : ZweigForm
  disp : Int
  ziel : Nat
  deriving DecidableEq, Repr

/-- Checked certificate: the wide form only, the exact final length
    for the condition, the next-RIP equation over the FINAL length,
    and signed-32 fit. A short selection is refused until its codec
    row, decoder acceptance and stability proof exist. -/
def zweigOk (bedingt : Bool) (c : ZweigBeleg) : Bool :=
  if c.form = .weit then
    if c.len = zweigLaenge bedingt .weit then
      if (c.ziel : Int) = (c.start : Int) + (c.len : Int) + c.disp then
        rel32Passt c.disp
      else false
    else false
  else false

/-- ACCEPTANCE: a certificate with the wide form, exact final length,
    the next-RIP equation and fit is accepted. Every premise is used. -/
theorem zweigOk_weit (bedingt : Bool) (c : ZweigBeleg)
    (hform : c.form = .weit)
    (hlen : c.len = zweigLaenge bedingt .weit)
    (hgleich : (c.ziel : Int) = (c.start : Int) + (c.len : Int) + c.disp)
    (hfit : rel32Passt c.disp = true) :
    zweigOk bedingt c = true := by
  unfold zweigOk
  rw [if_pos hform, if_pos hlen, if_pos hgleich, hfit]

/-- REFUSAL: the future short form is never accepted: native rel8 is
    absent from the canonical decoder (OPEN). -/
theorem zweigOk_kurz (bedingt : Bool) (c : ZweigBeleg)
    (hform : c.form = .kurz) :
    zweigOk bedingt c = false := by
  have hne : ¬ c.form = ZweigForm.weit := by
    rw [hform]
    decide
  unfold zweigOk
  rw [if_neg hne]

/-- ADDRESS EQUATION: an accepted certificate satisfies the canonical
    rel32 target equation at its final start plus final length. This
    is the relocation/final-layout dependency: the checked
    displacement, fit and carried length jointly determine the
    machine-level target. Every premise is used. -/
theorem zweigBeleg_adresse (c : ZweigBeleg) (bedingt : Bool)
    (hok : zweigOk bedingt c = true) :
    BitVec.ofNat 64 c.ziel =
      BitVec.ofNat 64 (c.start + c.len) +
        BitVec.ofNat 64 (rel32Enc64 c.disp) := by
  unfold zweigOk at hok
  by_cases hf : c.form = ZweigForm.weit
  · rw [if_pos hf] at hok
    by_cases hl : c.len = zweigLaenge bedingt .weit
    · rw [if_pos hl] at hok
      by_cases hg : (c.ziel : Int) =
          (c.start : Int) + (c.len : Int) + c.disp
      · rw [if_pos hg] at hok
        have hfit := of_decide_eq_true hok
        have hdef : (c.ziel : Int) =
            ((c.start + c.len : Nat) : Int) + c.disp := by
          omega
        exact rel32_adress_gleichung (c.start + c.len) c.ziel c.disp
          hdef hfit.1 hfit.2
      · rw [if_neg hg] at hok
        exact (Bool.false_ne_true hok).elim
    · rw [if_neg hl] at hok
      exact (Bool.false_ne_true hok).elim
  · rw [if_neg hf] at hok
    exact (Bool.false_ne_true hok).elim

/-! ## 5. No hidden patch after validation. -/

/-- NO HIDDEN PATCH: patching the checked displacement into the image
    keeps the image length, so validation of the final bytes sees
    every byte it checked. Every premise is used. -/
theorem zweigPatch_laenge (img : List Byte) (off : Nat) (c : ZweigBeleg)
    (out : List Byte) (h : patchRel32 img off c.disp = some out) :
    out.length = img.length := by
  unfold patchRel32 at h
  split at h
  · exact patchAt_laenge img off (rel32Bytes c.disp) out h
  · cases h

/-! ## 6. Concrete probes: acceptance, refusals, rel8 absence. -/

/-- CONCRETE ACCEPT: start 4096, 5-byte jump, displacement -5,
    target 4096. -/
theorem zweig_zeuge_akzeptiert :
    zweigOk false ⟨4096, 5, .weit, -5, 4096⟩ = true := by
  decide

/-- CONCRETE REFUSALS: short form, out-of-range displacement and
    wrong carried length are each refused. -/
theorem zweig_zeuge_verweigert :
    zweigOk false ⟨4096, 5, .kurz, -5, 4096⟩ = false ∧
    zweigOk false ⟨4096, 5, .weit, 2147483648, 0⟩ = false ∧
    zweigOk false ⟨4096, 6, .weit, -5, 4096⟩ = false := by
  decide

/-- NATIVE rel8 ABSENT: short jump bytes (EB with two rel8 values)
    and a short conditional jump (0x70) are refused by the canonical
    decoder. Short-branch selection stays OPEN. -/
theorem zweig_rel8_verweigert :
    decode [natByte 235, natByte 127] = none ∧
    decode [natByte 112, natByte 5] = none := by
  exact ⟨by decide, by decide⟩

/-- JOINT WITNESS: the accepted certificate satisfies the address
    equation on concrete values. -/
theorem zweigBeleg_adresse_zeuge :
    BitVec.ofNat 64 4096 =
      BitVec.ofNat 64 (4096 + 5) + BitVec.ofNat 64 (rel32Enc64 (-5)) := by
  have h := zweigBeleg_adresse ⟨4096, 5, ZweigForm.weit, -5, 4096⟩
    false zweig_zeuge_akzeptiert
  simpa using h

/-! ## 7. Memory-changing witness over the call store. -/

/-- The call return-address slot is writable for eight bytes. -/
theorem zweig_schreibbar8 :
    schreibbar8 zeugeSpeicher (BitVec.ofNat 64 8184) = true := by
  decide

/-- The call return-address slot is readable for eight bytes. -/
theorem zweig_lesbar8 :
    lesbar8 zeugeSpeicher (BitVec.ofNat 64 8184) = true := by
  decide

/-- JOINT WITNESS: a direct call's return-address store reads back
    and observably changes the memory byte from zero. Branch and
    call targets themselves touch no memory; the call store is the
    memory-changing execution this layout performs. -/
theorem zweig_speicher_zeuge :
    ∃ (m' : Speicher),
      write64 zeugeSpeicher (BitVec.ofNat 64 8184) 4101 = some m' ∧
      read64 m' (BitVec.ofNat 64 8184) = some 4101 ∧
        m'.bytes (BitVec.ofNat 64 8184) ≠
          zeugeSpeicher.bytes (BitVec.ofNat 64 8184) := by
  have hwr : write64 zeugeSpeicher (BitVec.ofNat 64 8184) 4101 =
      some { zeugeSpeicher with
        bytes := writeBytes zeugeSpeicher (BitVec.ofNat 64 8184) 4101 } := by
    unfold write64
    rw [if_pos zweig_schreibbar8]
  refine ⟨_, hwr, read64_nach_write64 _ _ _ _ hwr zweig_lesbar8, ?_⟩
  have hhit := writeBytesN_hit zeugeSpeicher
    (BitVec.ofNat 64 8184) 4101 8 0 (by decide) (by decide)
  rw [addrOff_null] at hhit
  show writeBytesN zeugeSpeicher (BitVec.ofNat 64 8184) 4101 8
      (BitVec.ofNat 64 8184) ≠ zeugeSpeicher.bytes (BitVec.ofNat 64 8184)
  rw [hhit]
  decide

/- CUTS:
    - Proved here: exact rel32 branch/call lengths (5/6/5) with
      displacement-independent length stability (no layout optimism
      for rel32-only layouts); signed displacement bounds and fit;
      the codec/relocation byte bridge with sign-extending decode;
      the layout certificate with exact widths, the next-RIP equation
      over the final length, the address equation, patch
      length preservation, the short-form refusal, native-rel8
      absence probes, concrete accept/refusal probes, and a
      memory-changing witness over the call return-address store.
    - Explicitly OPEN: native rel8 selection (EB / 70+code, 2 bytes)
      has no codec row, no decoder acceptance and no stability proof;
      `zweigOk` refuses every short certificate unconditionally.
    - Multi-branch bounded relaxation (DESIGN §2B fuel rounds,
      compression stability across sites, fall-through/alignment) is
      not modelled: this module certifies one site at its final
      layout; convergence of whole-function narrowing stays future.
    - No step-level claim is duplicated here: the `direktZiel`
      equations for the reused `schritt` stay in `ControlFlow`;
      section mapping and entry containment stay in `Bild`; the
      modular target equation stays in `Relokation`.
    - No source correspondence, no TSO/GX bridge, no concurrency, no
      cost or time transfer, no ABI/loader acceptance and no hardware
      correspondence is claimed: validation runs on final bytes only.
-/

#print axioms zweig_jump32_len
#print axioms zweig_jumpIf32_len
#print axioms zweig_call32_len
#print axioms zweig_len_stabil_jump32
#print axioms zweig_len_stabil_jumpIf32
#print axioms zweig_len_stabil_call32
#print axioms dispSigned_schranke
#print axioms dispSigned_passt
#print axioms rel32Enc_dispSigned
#print axioms rel32Bytes_dispSigned
#print axioms leBytes32_decode_signed
#print axioms zweigBreite_weit
#print axioms zweigLaenge_weite
#print axioms zweigLaenge_codec_jump32
#print axioms zweigLaenge_codec_jumpIf32
#print axioms zweigLaenge_codec_call32
#print axioms zweigOk_weit
#print axioms zweigOk_kurz
#print axioms zweigBeleg_adresse
#print axioms zweigPatch_laenge
#print axioms zweig_zeuge_akzeptiert
#print axioms zweig_zeuge_verweigert
#print axioms zweig_rel8_verweigert
#print axioms zweigBeleg_adresse_zeuge
#print axioms zweig_schreibbar8
#print axioms zweig_lesbar8
#print axioms zweig_speicher_zeuge

end Gabbro.Grammatik.X86
