/-
  File:      Grammatik/X86/RelocatedExecution.lean
  Subject:   Relocated rel32 bytes to re-decoded instruction execution.

  Lane 561: connects the proved relocation arithmetic (`Relokation`),
  branch-layout displacement facts (`BranchLayout`), image sites (`Bild`),
  the canonical decoder (`Codec`) and actual-memory execution
  (`Byteschritt`/`Ausfuehrung`) into one checked patch-and-redecode
  correspondence for rel32 branch/call sites.

  Producer/consumer: the producers are the six modules above (nothing is
  redefined here: no second decoder, loader, executor or ISA model); the
  consumer is the future layout validator and the image-coverage proof
  (`DecodingCoverage`/`ValidatorSkeleton.valX86`), which can discharge one
  rel32 site by `patchSiteOk`.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Relokation
import Grammatik.X86.BranchLayout
import Grammatik.X86.Bild
import Grammatik.X86.Byteschritt
import Grammatik.X86.Vektor
import Grammatik.X86.ControlFlow

namespace Gabbro.Grammatik.X86

/-! ## 1. Relocatable site vocabulary: no second ISA. -/

/-- Relocatable rel32 site class: unconditional jump, direct call, or a
    conditional jump with its condition. Only these three have canonical
    rel32 bytes; every other class (abs64 data, rel8 short, other
    instructions) is an explicit cut (see CUTS). -/
inductive RelocArt where
  | sprung
  | ruf
  | bedingt (c : Bedingung)
  deriving DecidableEq, Repr

/-- Encoded length of a site class: 5 for jump/call, 6 for conditional. -/
def relocLen : RelocArt → Nat
  | .sprung => 5
  | .ruf => 5
  | .bedingt _ => 6

/-- The canonical instruction of a site class at displacement `d`. -/
def relocBefehl : RelocArt → BitVec 32 → Befehl
  | .sprung, d => .jump32 d
  | .ruf, d => .call32 d
  | .bedingt c, d => .jumpIf32 c d

/-- The final bytes of a site class at displacement `d`: exactly the
    canonical encoder output, never a second codec. -/
def relocBytes (a : RelocArt) (d : BitVec 32) : List Byte :=
  encode (relocBefehl a d)

/-! ## 2. Displacement bridge: `dispWort` meets `rel32Enc64`.

    Execution adds `dispWort d` (sign extension through `sext`) while
    relocation computes `rel32Enc64 (dispSigned d)` (two's-complement
    representative). Both branch on the same bit: bit 31 of the field
    value. The two helpers below pin that bit to the signed-32 boundary
    with core `Nat.testBit` lemmas only; `omega` cannot do this step. -/

/-- Every bit test is a halved division at bit zero. -/
theorem testBit_div_pow (n i : Nat) :
    n.testBit i = (n / 2 ^ i).testBit 0 := by
  induction i generalizing n with
  | zero => simp
  | succ k ih =>
    show n.testBit (Nat.succ k) = _
    rw [Nat.testBit_succ, ih]
    congr 1
    rw [Nat.div_div_eq_div_mul]
    congr 1
    have e : k + 1 = Nat.succ k := rfl
    rw [e, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2]

/-- Bit 31 of a 32-bit value is the signed-32 boundary. -/
theorem bit31_equiv (n : Nat) (h : n < 2 ^ 32) :
    n.testBit 31 = decide (2147483648 ≤ n) := by
  have h31 : n.testBit 31 = (n / 2 ^ 31).testBit 0 :=
    testBit_div_pow n 31
  rw [h31, Nat.testBit_zero]
  have hdiv : n / 2 ^ 31 < 2 := by
    have h0 : (0 : Nat) < 2 ^ 31 := by decide
    rw [Nat.div_lt_iff_lt_mul h0]
    omega
  have hmod : (n / 2 ^ 31) % 2 = n / 2 ^ 31 :=
    Nat.mod_eq_of_lt hdiv
  rw [hmod]
  have hiff : (n / 2 ^ 31 = 1) ↔ (2147483648 ≤ n) := by
    omega
  simp only [hiff]

/-- BRIDGE: the execution sign extension of a displacement field is the
    relocation 64-bit representative of its signed value. This is the one
    fact that lets a relocation address equation speak about `schritt`. -/
theorem dispWort_bridge (d : BitVec 32) :
    dispWort d = BitVec.ofNat 64 (rel32Enc64 (dispSigned d)) := by
  have hd := d.isLt
  have hlo : (trunc .b32 (BitVec.ofNat 64 d.toNat)).toNat = d.toNat := by
    have hw : (BitVec.ofNat 64 d.toNat).toNat = d.toNat := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    rw [trunc_nat, hw]
    have hb : Breite.bits .b32 = 32 := rfl
    rw [hb]
    exact Nat.mod_eq_of_lt hd
  have hbit' : d.toNat.testBit (signBit .b32) =
      decide (2147483648 ≤ d.toNat) := by
    rw [show signBit .b32 = 31 from rfl]
    exact bit31_equiv d.toNat hd
  unfold dispWort
  simp only [sext, hlo, hbit']
  by_cases hge : 2147483648 ≤ d.toNat
  · rw [if_pos (decide_eq_true hge)]
    have hb : Breite.bits .b32 = 32 := rfl
    rw [hb]
    have hds : dispSigned d = (d.toNat : Int) - 4294967296 := by
      unfold dispSigned
      rw [if_neg (by omega)]
    rw [hds]
    have hneg : ¬ (0 : Int) ≤ (d.toNat : Int) - 4294967296 := by
      omega
    unfold rel32Enc64 tcNat
    rw [if_neg hneg]
    have e : (((d.toNat : Int) - 4294967296 +
        ((18446744073709551616 : Nat) : Int))).toNat =
        d.toNat + (2 ^ 64 - 2 ^ 32) := by
      have e2 : (d.toNat : Int) - 4294967296 +
          ((18446744073709551616 : Nat) : Int) =
          ((d.toNat + (18446744073709551616 - 4294967296) : Nat) : Int) := by
        omega
      rw [e2, Int.toNat_natCast]
    rw [e]
  · rw [if_neg (by rw [decide_eq_false hge]; decide)]
    have hds : dispSigned d = (d.toNat : Int) := by
      unfold dispSigned
      rw [if_pos (by omega)]
    rw [hds]
    have hpos : (0 : Int) ≤ (d.toNat : Int) := by omega
    unfold rel32Enc64 tcNat
    rw [if_pos hpos, Int.toNat_natCast]

/-! ## 3. Site bytes: lengths, decoding, displacement realization. -/

/-- The final bytes have exactly the carried length of their class. -/
theorem relocBytes_len (a : RelocArt) (d : BitVec 32) :
    (relocBytes a d).length = relocLen a := by
  cases a with
  | sprung =>
    simp only [relocBytes, relocBefehl, relocLen]
    exact zweig_jump32_len d
  | ruf =>
    simp only [relocBytes, relocBefehl, relocLen]
    exact zweig_call32_len d
  | bedingt c =>
    simp only [relocBytes, relocBefehl, relocLen]
    exact zweig_jumpIf32_len c d

/-- The final bytes decode to the site instruction at its carried length:
    no re-encoding, one shared decoder. -/
theorem relocBytes_decode (a : RelocArt) (d : BitVec 32)
    (suffix : List Byte) :
    decode (relocBytes a d ++ suffix) =
      some (⟨relocBefehl a d, (relocBytes a d).length⟩, suffix) := by
  cases a with
  | sprung =>
    simp only [relocBytes, relocBefehl]
    exact roundtrip_jump32 d suffix
  | ruf =>
    simp only [relocBytes, relocBefehl]
    exact roundtrip_call32 d suffix
  | bedingt c =>
    simp only [relocBytes, relocBefehl]
    exact roundtrip_jumpIf32 c d suffix

/-- Every in-range signed displacement is some field's signed value: the
    patch direction (Int to bytes) never misses a checked displacement. -/
theorem dispVonFit (disp : Int) (hlo : -2147483648 ≤ disp)
    (hhi : disp < 2147483648) :
    ∃ d : BitVec 32, dispSigned d = disp := by
  refine ⟨BitVec.ofNat 32 (rel32Enc disp), ?_⟩
  by_cases hnn : 0 ≤ disp
  · have e1 : rel32Enc disp = disp.toNat := by
      unfold rel32Enc tcNat
      rw [if_pos hnn]
    have he : (BitVec.ofNat 32 (rel32Enc disp)).toNat = disp.toNat := by
      rw [BitVec.toNat_ofNat, e1, Nat.mod_eq_of_lt (by omega)]
    unfold dispSigned
    rw [he, if_pos (by omega)]
    omega
  · have e1 : rel32Enc disp = (disp + ((4294967296 : Nat) : Int)).toNat := by
      unfold rel32Enc tcNat
      rw [if_neg hnn]
    have he : (BitVec.ofNat 32 (rel32Enc disp)).toNat =
        (disp + ((4294967296 : Nat) : Int)).toNat := by
      rw [BitVec.toNat_ofNat, e1, Nat.mod_eq_of_lt (by omega)]
    have hge : 2147483648 ≤ (disp + ((4294967296 : Nat) : Int)).toNat := by
      omega
    unfold dispSigned
    rw [he, if_neg (by omega)]
    omega

/-! ## 4. Checked relocation site over virtual addresses. -/

/-- One checked relocation site: the effective load bias, the section's
    unbiased virtual base, the instruction-start offset inside the section,
    the site class, the resolved signed displacement and the intended
    mapped target (a virtual address, never a file offset). -/
structure PatchSite where
  bias : Nat
  vaddr : Nat
  off : Nat
  art : RelocArt
  disp : Int
  ziel : Nat
  deriving DecidableEq, Repr

/-- Loaded virtual address of the instruction start. -/
def siteStart (s : PatchSite) : Nat := s.bias + s.vaddr + s.off

/-- Loaded virtual address past the instruction: start plus the FINAL
    carried length of the class. -/
def siteNext (s : PatchSite) : Nat := siteStart s + relocLen s.art

/-- The checked site: the next-RIP equation over the final length, the
    signed-32 fit, machine-range bounds, and the interior-target refusal
    (a target strictly inside the site's own bytes decodes nothing sane).
    All five checks are decided data over the carried values. -/
def patchSiteOk (s : PatchSite) : Bool :=
  decide ((s.ziel : Int) = (siteStart s : Int) + (relocLen s.art : Int) +
    s.disp ∧
    rel32Passt s.disp = true ∧
    siteNext s < 2 ^ 64 ∧ s.ziel < 2 ^ 64 ∧
    (s.ziel ≤ siteStart s ∨ siteNext s ≤ s.ziel))

/-- ACCEPTANCE: the five checks jointly admit the site. -/
theorem patchSiteOk_akzeptiert (s : PatchSite)
    (hgleich : (s.ziel : Int) = (siteStart s : Int) + (relocLen s.art : Int) +
      s.disp)
    (hfit : rel32Passt s.disp = true)
    (hnext : siteNext s < 2 ^ 64) (hziel : s.ziel < 2 ^ 64)
    (haussen : s.ziel ≤ siteStart s ∨ siteNext s ≤ s.ziel) :
    patchSiteOk s = true := by
  unfold patchSiteOk
  exact decide_eq_true ⟨hgleich, hfit, hnext, hziel, haussen⟩

/-- REFUSAL: an out-of-range displacement admits no site. -/
theorem patchSiteOk_disp_aussen (s : PatchSite)
    (h : rel32Passt s.disp = false) :
    patchSiteOk s = false := by
  unfold patchSiteOk
  refine decide_eq_false (fun hcon => ?_)
  have hq := hcon.2.1
  rw [h] at hq
  exact Bool.false_ne_true hq

/-- REFUSAL: a target strictly inside the site's own bytes admits no
    site: it is neither the site start (or earlier) nor a later
    instruction start. -/
theorem patchSiteOk_innen (s : PatchSite)
    (h1 : siteStart s < s.ziel) (h2 : s.ziel < siteNext s) :
    patchSiteOk s = false := by
  unfold patchSiteOk
  refine decide_eq_false (fun hcon => ?_)
  rcases hcon.2.2.2.2 with h | h <;> omega

/-- PATCH-AND-REDECODE TARGET: the decoded instruction's executed target
    is the intended mapped target, as a machine word and as a Nat. Uses
    the relocation address equation through the displacement bridge, with
    next-RIP formation over the carried final length. -/
theorem patchSite_ziel (s : PatchSite) (d : BitVec 32)
    (hdisp : dispSigned d = s.disp)
    (hgleich : (s.ziel : Int) = (siteStart s : Int) + (relocLen s.art : Int) +
      s.disp)
    (hfit : rel32Passt s.disp = true)
    (hnext : siteNext s < 2 ^ 64)
    (hziel : s.ziel < 2 ^ 64) :
    direktZiel (BitVec.ofNat 64 (siteStart s)) (relocLen s.art) d =
      BitVec.ofNat 64 s.ziel ∧
    (direktZiel (BitVec.ofNat 64 (siteStart s)) (relocLen s.art) d).toNat =
      s.ziel := by
  have hfitI := of_decide_eq_true hfit
  have hnext' : siteStart s + relocLen s.art < 2 ^ 64 := by
    have h := hnext
    unfold siteNext at h
    exact h
  have hstart : siteStart s < 2 ^ 64 := by omega
  have hlen : relocLen s.art < 2 ^ 64 := by
    cases s.art
    · show (5 : Nat) < 2 ^ 64
      decide
    · show (5 : Nat) < 2 ^ 64
      decide
    · show (6 : Nat) < 2 ^ 64
      decide
  have hnach : BitVec.ofNat 64 (siteStart s) +
      BitVec.ofNat 64 (relocLen s.art) =
      BitVec.ofNat 64 (siteStart s + relocLen s.art) := by
    apply BitVec.eq_of_toNat_eq
    rw [rel32_next_rip _ _ hstart hlen hnext', BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hnext']
  have hdef : (s.ziel : Int) =
      ((siteStart s + relocLen s.art : Nat) : Int) + s.disp := by
    omega
  have hadr := rel32_adress_gleichung (siteStart s + relocLen s.art) s.ziel
    s.disp hdef hfitI.1 hfitI.2
  have hmain : direktZiel (BitVec.ofNat 64 (siteStart s)) (relocLen s.art) d =
      BitVec.ofNat 64 s.ziel := by
    unfold direktZiel ripNach
    rw [dispWort_bridge, hdisp, hnach]
    exact hadr.symm
  refine ⟨hmain, ?_⟩
  rw [hmain, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hziel]

/-! ## 5. Actual-memory execution: `byteschritt` reaches the target. -/

/-- EXECUTION (jump): a state whose fetched window is the relocated site
    bytes steps to the intended mapped target. Fetch, decode and step all
    run on actual memory bytes; the relocation metadata only selects which
    bytes are checked. -/
theorem patchSite_sprung_schritt (s : PatchSite) (d : BitVec 32)
    (hdisp : dispSigned d = s.disp)
    (hgleich : (s.ziel : Int) = (siteStart s : Int) + (relocLen s.art : Int) +
      s.disp)
    (hfit : rel32Passt s.disp = true)
    (hnext : siteNext s < 2 ^ 64)
    (hziel : s.ziel < 2 ^ 64)
    (hart : s.art = .sprung)
    (z : Zustand) (suffix : List Byte)
    (hwin : geholt z = relocBytes .sprung d ++ suffix)
    (hexe : ausfuehrbarN z.speicher z.rip (relocBytes .sprung d).length =
      true)
    (hrip : z.rip = BitVec.ofNat 64 (siteStart s)) :
    byteschritt z = .weiter { z with rip := BitVec.ofNat 64 s.ziel } := by
  have hwin' : geholt z = encode (.jump32 d) ++ suffix := hwin
  have hexe' : ausfuehrbarN z.speicher z.rip (encode (.jump32 d)).length =
      true := hexe
  have hkan := kanonisch_schritt_ueberein (.jump32 d) z suffix hwin' hexe'
  have hlenok : laengeOk (encode (.jump32 d)).length = true := by
    simp only [laengeOk, decide_eq_true_eq]
    exact encode_len (.jump32 d)
  have hs : schritt (⟨.jump32 d, (encode (.jump32 d)).length⟩ : Decodiert) z = some ({ z with rip := ripNach z.rip (encode (.jump32 d)).length + dispWort d } : Zustand) :=
    schritt_jump32 _ z d hlenok rfl
  have hnach_eq : ripNach z.rip (encode (.jump32 d)).length + dispWort d =
      BitVec.ofNat 64 s.ziel := by
    have e1 : (encode (.jump32 d)).length = relocLen s.art := by
      rw [hart]
      exact zweig_jump32_len d
    rw [hrip, e1]
    exact (patchSite_ziel s d hdisp hgleich hfit hnext hziel).1
  have hbs : byteschritt z = .weiter ({ z with rip := ripNach z.rip (encode (.jump32 d)).length + dispWort d } : Zustand) := by
    have h1 := hkan.2
    rw [hs] at h1
    simpa using h1
  have hfin : ({ z with rip := ripNach z.rip (encode (.jump32 d)).length + dispWort d } : Zustand) = { z with rip := BitVec.ofNat 64 s.ziel } := by
    rw [hnach_eq]
  rw [hbs, hfin]

/-- EXECUTION (call): a state whose fetched window is the relocated site
    bytes stores the return address and steps to the intended mapped
    target. This is the memory-changing execution of the correspondence:
    the stack write is a real `write64`, not metadata. -/
theorem patchSite_ruf_schritt (s : PatchSite) (d : BitVec 32) (m : Speicher)
    (hdisp : dispSigned d = s.disp)
    (hgleich : (s.ziel : Int) = (siteStart s : Int) + (relocLen s.art : Int) +
      s.disp)
    (hfit : rel32Passt s.disp = true)
    (hnext : siteNext s < 2 ^ 64)
    (hziel : s.ziel < 2 ^ 64)
    (hart : s.art = .ruf)
    (z : Zustand) (suffix : List Byte)
    (hwin : geholt z = relocBytes .ruf d ++ suffix)
    (hexe : ausfuehrbarN z.speicher z.rip (relocBytes .ruf d).length = true)
    (hrip : z.rip = BitVec.ofNat 64 (siteStart s))
    (hwr : write64 z.speicher
      (z.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach z.rip (encode (.call32 d)).length) = some m) :
    byteschritt z = .weiter
      (schrittCall z Register.rsp m
        (z.register Register.rsp - BitVec.ofNat 64 8)
        (BitVec.ofNat 64 s.ziel)) := by
  have hwin' : geholt z = encode (.call32 d) ++ suffix := hwin
  have hexe' : ausfuehrbarN z.speicher z.rip (encode (.call32 d)).length =
      true := hexe
  have hkan := kanonisch_schritt_ueberein (.call32 d) z suffix hwin' hexe'
  have hlenok : laengeOk (encode (.call32 d)).length = true := by
    simp only [laengeOk, decide_eq_true_eq]
    exact encode_len (.call32 d)
  have hs : schritt (⟨.call32 d, (encode (.call32 d)).length⟩ : Decodiert) z =
      some (schrittCall z Register.rsp m
        (z.register Register.rsp - BitVec.ofNat 64 8)
        (ripNach z.rip (encode (.call32 d)).length + dispWort d)) :=
    schritt_call32_erfolg _ z d m hlenok rfl hwr
  have hnach_eq : ripNach z.rip (encode (.call32 d)).length + dispWort d =
      BitVec.ofNat 64 s.ziel := by
    have e1 : (encode (.call32 d)).length = relocLen s.art := by
      rw [hart]
      exact zweig_call32_len d
    rw [hrip, e1]
    exact (patchSite_ziel s d hdisp hgleich hfit hnext hziel).1
  have hbs : byteschritt z = .weiter (schrittCall z Register.rsp m
      (z.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach z.rip (encode (.call32 d)).length + dispWort d)) := by
    have h1 := hkan.2
    rw [hs] at h1
    simpa using h1
  have hfin : schrittCall z Register.rsp m
      (z.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach z.rip (encode (.call32 d)).length + dispWort d) =
      schrittCall z Register.rsp m
        (z.register Register.rsp - BitVec.ofNat 64 8)
        (BitVec.ofNat 64 s.ziel) := by
    rw [hnach_eq]
  rw [hbs, hfin]

/-- EXECUTION (conditional taken): the taken branch steps to the intended
    mapped target. -/
theorem patchSite_bedingt_genommen_schritt (s : PatchSite) (d : BitVec 32)
    (c : Bedingung)
    (hdisp : dispSigned d = s.disp)
    (hgleich : (s.ziel : Int) = (siteStart s : Int) + (relocLen s.art : Int) +
      s.disp)
    (hfit : rel32Passt s.disp = true)
    (hnext : siteNext s < 2 ^ 64)
    (hziel : s.ziel < 2 ^ 64)
    (hart : s.art = .bedingt c)
    (z : Zustand) (suffix : List Byte)
    (hwin : geholt z = relocBytes (.bedingt c) d ++ suffix)
    (hexe : ausfuehrbarN z.speicher z.rip (relocBytes (.bedingt c) d).length =
      true)
    (hrip : z.rip = BitVec.ofNat 64 (siteStart s))
    (hbed : bedingung c z.flags = true) :
    byteschritt z = .weiter { z with rip := BitVec.ofNat 64 s.ziel } := by
  have hwin' : geholt z = encode (.jumpIf32 c d) ++ suffix := hwin
  have hexe' : ausfuehrbarN z.speicher z.rip (encode (.jumpIf32 c d)).length =
      true := hexe
  have hkan := kanonisch_schritt_ueberein (.jumpIf32 c d) z suffix hwin' hexe'
  have hlenok : laengeOk (encode (.jumpIf32 c d)).length = true := by
    simp only [laengeOk, decide_eq_true_eq]
    exact encode_len (.jumpIf32 c d)
  have hs : schritt (⟨.jumpIf32 c d, (encode (.jumpIf32 c d)).length⟩ : Decodiert) z = some ({ z with rip := ripNach z.rip (encode (.jumpIf32 c d)).length + dispWort d } : Zustand) :=
    schritt_jumpIf32_genommen _ z c d hlenok rfl hbed
  have hnach_eq : ripNach z.rip (encode (.jumpIf32 c d)).length + dispWort d =
      BitVec.ofNat 64 s.ziel := by
    have e1 : (encode (.jumpIf32 c d)).length = relocLen s.art := by
      rw [hart]
      exact zweig_jumpIf32_len c d
    rw [hrip, e1]
    exact (patchSite_ziel s d hdisp hgleich hfit hnext hziel).1
  have hbs : byteschritt z = .weiter ({ z with rip := ripNach z.rip (encode (.jumpIf32 c d)).length + dispWort d } : Zustand) := by
    have h1 := hkan.2
    rw [hs] at h1
    simpa using h1
  have hfin : ({ z with rip := ripNach z.rip (encode (.jumpIf32 c d)).length + dispWort d } : Zustand) = { z with rip := BitVec.ofNat 64 s.ziel } := by
    rw [hnach_eq]
  rw [hbs, hfin]

/-- EXECUTION (conditional not taken): fall-through lands on the address
    past the site. The target premises are unneeded here: no control
    transfer happens, so only the length bound is carried. -/
theorem patchSite_bedingt_nicht_schritt (s : PatchSite) (d : BitVec 32)
    (c : Bedingung)
    (hart : s.art = .bedingt c)
    (hnext : siteNext s < 2 ^ 64)
    (z : Zustand) (suffix : List Byte)
    (hwin : geholt z = relocBytes (.bedingt c) d ++ suffix)
    (hexe : ausfuehrbarN z.speicher z.rip (relocBytes (.bedingt c) d).length =
      true)
    (hrip : z.rip = BitVec.ofNat 64 (siteStart s))
    (hbed : bedingung c z.flags = false) :
    byteschritt z = .weiter { z with rip := BitVec.ofNat 64 (siteNext s) } := by
  have hwin' : geholt z = encode (.jumpIf32 c d) ++ suffix := hwin
  have hexe' : ausfuehrbarN z.speicher z.rip (encode (.jumpIf32 c d)).length =
      true := hexe
  have hkan := kanonisch_schritt_ueberein (.jumpIf32 c d) z suffix hwin' hexe'
  have hlenok : laengeOk (encode (.jumpIf32 c d)).length = true := by
    simp only [laengeOk, decide_eq_true_eq]
    exact encode_len (.jumpIf32 c d)
  have hs : schritt (⟨.jumpIf32 c d, (encode (.jumpIf32 c d)).length⟩ : Decodiert) z = some ({ z with rip := ripNach z.rip (encode (.jumpIf32 c d)).length } : Zustand) :=
    schritt_jumpIf32_nicht _ z c d hlenok rfl hbed
  have hnext' : siteStart s + relocLen s.art < 2 ^ 64 := by
    have h := hnext
    unfold siteNext at h
    exact h
  have hstart : siteStart s < 2 ^ 64 := by omega
  have hlen : relocLen s.art < 2 ^ 64 := by
    rw [hart]
    show (6 : Nat) < 2 ^ 64
    decide
  have e1 : (encode (.jumpIf32 c d)).length = relocLen s.art := by
    rw [hart]
    exact zweig_jumpIf32_len c d
  have hfall : ripNach z.rip (encode (.jumpIf32 c d)).length =
      BitVec.ofNat 64 (siteNext s) := by
    have hnach' : BitVec.ofNat 64 (siteStart s) +
        BitVec.ofNat 64 (relocLen s.art) =
        BitVec.ofNat 64 (siteStart s + relocLen s.art) := by
      apply BitVec.eq_of_toNat_eq
      rw [rel32_next_rip _ _ hstart hlen hnext', BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hnext']
    unfold ripNach siteNext
    rw [hrip, e1, hnach']
  have hbs : byteschritt z = .weiter ({ z with rip := ripNach z.rip (encode (.jumpIf32 c d)).length } : Zustand) := by
    have h1 := hkan.2
    rw [hs] at h1
    simpa using h1
  have hfin : ({ z with rip := ripNach z.rip (encode (.jumpIf32 c d)).length } : Zustand) = { z with rip := BitVec.ofNat 64 (siteNext s) } := by
    rw [hfall]
  rw [hbs, hfin]

/-! ## 6. Image sites: final bytes read from the loaded image. -/

/-- Loaded five-byte window at a virtual address: the actual bytes the
    decoder fetches, through the checked image mapping. Written with
    explicit `+ 0` so per-byte mapping facts match syntactically. -/
def fenster5 (bild : Bild) (bias start : Nat) : List Byte :=
  [ladenByte bild bias (start + 0), ladenByte bild bias (start + 1),
    ladenByte bild bias (start + 2), ladenByte bild bias (start + 3),
    ladenByte bild bias (start + 4)]

/-- Loaded six-byte window at a virtual address. -/
def fenster6 (bild : Bild) (bias start : Nat) : List Byte :=
  [ladenByte bild bias (start + 0), ladenByte bild bias (start + 1),
    ladenByte bild bias (start + 2), ladenByte bild bias (start + 3),
    ladenByte bild bias (start + 4), ladenByte bild bias (start + 5)]

/-- One window byte through the checked mapping: the section found at the
    loaded address plus file-backed coverage gives the mapped file byte.
    The file index is section-relative, never bias-relative. -/
theorem ladenByte_fenster (bild : Bild) (bias : Nat) (sec : Abschnitt)
    (off i : Nat) (b : Byte)
    (hfind : abteilFinden bild.abschnitte bias (bias + sec.vaddr + off + i) =
      some sec)
    (hbacked : off + i < sec.dateiLen)
    (hdatei : dateiByte bild.datei (sec.dateiOff + (off + i)) = b) :
    ladenByte bild bias (bias + sec.vaddr + off + i) = b := by
  have h := geladenByte_datei bild bias (bias + sec.vaddr + off + i) sec
    hfind (by omega)
  have e : bias + sec.vaddr + off + i - (bias + sec.vaddr) = off + i := by
    omega
  rw [e] at h
  rw [h]
  exact hdatei

/-- IMAGE DECODE (jump): the loaded window at a found, file-backed site
    whose file bytes are the relocated bytes decodes to the site
    instruction. The bytes are checked against the actual file list, never
    against relocation metadata. -/
theorem bildSite_sprung_dekode (bild : Bild) (bias : Nat) (sec : Abschnitt)
    (off : Nat) (d : BitVec 32)
    (hfind : ∀ i : Nat, i < 5 →
      abteilFinden bild.abschnitte bias (bias + sec.vaddr + off + i) =
        some sec)
    (hbacked : ∀ i : Nat, i < 5 → off + i < sec.dateiLen)
    (hb0 : dateiByte bild.datei (sec.dateiOff + off) = natByte 233)
    (hb1 : dateiByte bild.datei (sec.dateiOff + (off + 1)) =
      natByte (d.toNat % 256))
    (hb2 : dateiByte bild.datei (sec.dateiOff + (off + 2)) =
      natByte ((d.toNat / 256) % 256))
    (hb3 : dateiByte bild.datei (sec.dateiOff + (off + 3)) =
      natByte ((d.toNat / 65536) % 256))
    (hb4 : dateiByte bild.datei (sec.dateiOff + (off + 4)) =
      natByte ((d.toNat / 16777216) % 256)) :
    decode (fenster5 bild bias (bias + sec.vaddr + off)) =
      some (⟨.jump32 d, 5⟩, []) := by
  have l0 := ladenByte_fenster bild bias sec off 0 (natByte 233)
    (hfind 0 (by decide)) (hbacked 0 (by decide)) (by simpa using hb0)
  have l1 := ladenByte_fenster bild bias sec off 1 _
    (hfind 1 (by decide)) (hbacked 1 (by decide)) hb1
  have l2 := ladenByte_fenster bild bias sec off 2 _
    (hfind 2 (by decide)) (hbacked 2 (by decide)) hb2
  have l3 := ladenByte_fenster bild bias sec off 3 _
    (hfind 3 (by decide)) (hbacked 3 (by decide)) hb3
  have l4 := ladenByte_fenster bild bias sec off 4 _
    (hfind 4 (by decide)) (hbacked 4 (by decide)) hb4
  have hfen : fenster5 bild bias (bias + sec.vaddr + off) =
      relocBytes .sprung d := by
    unfold fenster5 relocBytes relocBefehl encode leBytes32
    rw [l0, l1, l2, l3, l4]
  rw [hfen]
  have hdec := relocBytes_decode .sprung d []
  simpa [relocBytes_len, relocLen, relocBefehl] using hdec

/-- IMAGE DECODE (call): same shape with the call opcode. -/
theorem bildSite_ruf_dekode (bild : Bild) (bias : Nat) (sec : Abschnitt)
    (off : Nat) (d : BitVec 32)
    (hfind : ∀ i : Nat, i < 5 →
      abteilFinden bild.abschnitte bias (bias + sec.vaddr + off + i) =
        some sec)
    (hbacked : ∀ i : Nat, i < 5 → off + i < sec.dateiLen)
    (hb0 : dateiByte bild.datei (sec.dateiOff + off) = natByte 232)
    (hb1 : dateiByte bild.datei (sec.dateiOff + (off + 1)) =
      natByte (d.toNat % 256))
    (hb2 : dateiByte bild.datei (sec.dateiOff + (off + 2)) =
      natByte ((d.toNat / 256) % 256))
    (hb3 : dateiByte bild.datei (sec.dateiOff + (off + 3)) =
      natByte ((d.toNat / 65536) % 256))
    (hb4 : dateiByte bild.datei (sec.dateiOff + (off + 4)) =
      natByte ((d.toNat / 16777216) % 256)) :
    decode (fenster5 bild bias (bias + sec.vaddr + off)) =
      some (⟨.call32 d, 5⟩, []) := by
  have l0 := ladenByte_fenster bild bias sec off 0 (natByte 232)
    (hfind 0 (by decide)) (hbacked 0 (by decide)) (by simpa using hb0)
  have l1 := ladenByte_fenster bild bias sec off 1 _
    (hfind 1 (by decide)) (hbacked 1 (by decide)) hb1
  have l2 := ladenByte_fenster bild bias sec off 2 _
    (hfind 2 (by decide)) (hbacked 2 (by decide)) hb2
  have l3 := ladenByte_fenster bild bias sec off 3 _
    (hfind 3 (by decide)) (hbacked 3 (by decide)) hb3
  have l4 := ladenByte_fenster bild bias sec off 4 _
    (hfind 4 (by decide)) (hbacked 4 (by decide)) hb4
  have hfen : fenster5 bild bias (bias + sec.vaddr + off) =
      relocBytes .ruf d := by
    unfold fenster5 relocBytes relocBefehl encode leBytes32
    rw [l0, l1, l2, l3, l4]
  rw [hfen]
  have hdec := relocBytes_decode .ruf d []
  simpa [relocBytes_len, relocLen, relocBefehl] using hdec

/-- IMAGE DECODE (conditional): the six-byte window with the two-byte
    opcode prefix decodes to the conditional site instruction. -/
theorem bildSite_bedingt_dekode (bild : Bild) (bias : Nat) (sec : Abschnitt)
    (off : Nat) (c : Bedingung) (d : BitVec 32)
    (hfind : ∀ i : Nat, i < 6 →
      abteilFinden bild.abschnitte bias (bias + sec.vaddr + off + i) =
        some sec)
    (hbacked : ∀ i : Nat, i < 6 → off + i < sec.dateiLen)
    (hb0 : dateiByte bild.datei (sec.dateiOff + off) = natByte 15)
    (hb1 : dateiByte bild.datei (sec.dateiOff + (off + 1)) =
      natByte (128 + condCode c))
    (hb2 : dateiByte bild.datei (sec.dateiOff + (off + 2)) =
      natByte (d.toNat % 256))
    (hb3 : dateiByte bild.datei (sec.dateiOff + (off + 3)) =
      natByte ((d.toNat / 256) % 256))
    (hb4 : dateiByte bild.datei (sec.dateiOff + (off + 4)) =
      natByte ((d.toNat / 65536) % 256))
    (hb5 : dateiByte bild.datei (sec.dateiOff + (off + 5)) =
      natByte ((d.toNat / 16777216) % 256)) :
    decode (fenster6 bild bias (bias + sec.vaddr + off)) =
      some (⟨.jumpIf32 c d, 6⟩, []) := by
  have l0 := ladenByte_fenster bild bias sec off 0 (natByte 15)
    (hfind 0 (by decide)) (hbacked 0 (by decide)) (by simpa using hb0)
  have l1 := ladenByte_fenster bild bias sec off 1 _
    (hfind 1 (by decide)) (hbacked 1 (by decide)) hb1
  have l2 := ladenByte_fenster bild bias sec off 2 _
    (hfind 2 (by decide)) (hbacked 2 (by decide)) hb2
  have l3 := ladenByte_fenster bild bias sec off 3 _
    (hfind 3 (by decide)) (hbacked 3 (by decide)) hb3
  have l4 := ladenByte_fenster bild bias sec off 4 _
    (hfind 4 (by decide)) (hbacked 4 (by decide)) hb4
  have l5 := ladenByte_fenster bild bias sec off 5 _
    (hfind 5 (by decide)) (hbacked 5 (by decide)) hb5
  have hfen : fenster6 bild bias (bias + sec.vaddr + off) =
      relocBytes (.bedingt c) d := by
    unfold fenster6 relocBytes relocBefehl encode leBytes32
    rw [l0, l1, l2, l3, l4, l5]
  rw [hfen]
  have hdec := relocBytes_decode (.bedingt c) d []
  simpa [relocBytes_len, relocLen, relocBefehl] using hdec

/-! ## 7. Supported site classes: data fields are an explicit cut. -/

/-- Only code-operand sites decode: a standalone data field (abs64 value,
    jump table entry, any non-instruction bytes) is never admitted here,
    even when its bytes coincide with an opcode. -/
def siteArtOk : RelArt → RelocArt → Bool
  | .codeOperand, _ => true
  | .datenFeld, _ => false

/-- Code-operand sites are admitted, for every site class. -/
theorem siteArtOk_code_akzeptiert (a : RelocArt) :
    siteArtOk .codeOperand a = true := by
  cases a <;> rfl

/-- Data-field sites are refused, for every site class. -/
theorem siteArtOk_daten_verweigert (a : RelocArt) :
    siteArtOk .datenFeld a = false := by
  cases a <;> rfl

/-! ## 8. Joint witnesses: forward, backward, nonzero bias. -/

/-- Witness code section: five executable bytes at 0x1000. -/
def zeugenCode5 : Abschnitt :=
  { dateiOff := 0, dateiLen := 5, vaddr := 0x1000, memLen := 5,
    lesbar := true, schreibbar := false, ausfuehrbar := true, ausr := 4096 }

/-- Forward-jump image: `jump +16` at 0x1000, target 0x1015. -/
def bildVor : Bild :=
  { datei := [natByte 233, natByte 16, natByte 0, natByte 0, natByte 0]
    abschnitte := [zeugenCode5]
    reloks := []
    eintraege := [0x1000]
    modus := .fest }

/-- The forward image is accepted. -/
theorem bildVor_wohlgeformt : wohlgeformt .p48 bildVor = true := by
  decide

/-- Forward site: bias 0, base 0x1000, offset 0, jump +16 to 0x1015. -/
def siteVor : PatchSite := ⟨0, 0x1000, 0, .sprung, 16, 0x1015⟩

/-- FORWARD ACCEPT: the checked site admits the forward jump. -/
theorem vor_akzeptiert : patchSiteOk siteVor = true := by
  decide

/-- FORWARD JOINT: the loaded window decodes to the jump, and the
    executed target is the intended mapped target. Final bytes are read
    from the image, never from relocation metadata. -/
theorem vor_gelenk :
    decode (fenster5 bildVor 0 0x1000) =
      some (⟨.jump32 (BitVec.ofNat 32 16), 5⟩, []) ∧
    direktZiel (BitVec.ofNat 64 0x1000) 5 (BitVec.ofNat 32 16) =
      BitVec.ofNat 64 0x1015 := by
  have hfind : ∀ i : Nat, i < 5 →
      abteilFinden bildVor.abschnitte 0 (0 + zeugenCode5.vaddr + 0 + i) =
        some zeugenCode5 := by
    intro i hi
    have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> decide
  have hbacked : ∀ i : Nat, i < 5 → 0 + i < zeugenCode5.dateiLen := by
    intro i hi
    have e : zeugenCode5.dateiLen = 5 := rfl
    omega
  have hb0 : dateiByte bildVor.datei (zeugenCode5.dateiOff + 0) =
      natByte 233 := by
    decide
  have hb1 : dateiByte bildVor.datei (zeugenCode5.dateiOff + (0 + 1)) =
      natByte ((BitVec.ofNat 32 16).toNat % 256) := by
    decide
  have hb2 : dateiByte bildVor.datei (zeugenCode5.dateiOff + (0 + 2)) =
      natByte (((BitVec.ofNat 32 16).toNat / 256) % 256) := by
    decide
  have hb3 : dateiByte bildVor.datei (zeugenCode5.dateiOff + (0 + 3)) =
      natByte (((BitVec.ofNat 32 16).toNat / 65536) % 256) := by
    decide
  have hb4 : dateiByte bildVor.datei (zeugenCode5.dateiOff + (0 + 4)) =
      natByte (((BitVec.ofNat 32 16).toNat / 16777216) % 256) := by
    decide
  have hdec := bildSite_sprung_dekode bildVor 0 zeugenCode5 0
    (BitVec.ofNat 32 16) hfind hbacked hb0 hb1 hb2 hb3 hb4
  have hz := (patchSite_ziel siteVor (BitVec.ofNat 32 16) (by decide)
    (by decide) (by decide) (by decide) (by decide)).1
  have eaddr : 0 + zeugenCode5.vaddr + 0 = 0x1000 := rfl
  rw [eaddr] at hdec
  have es : siteStart siteVor = 0x1000 := rfl
  have ea : siteVor.art = RelocArt.sprung := rfl
  rw [es, ea] at hz
  have el : relocLen RelocArt.sprung = 5 := rfl
  rw [el] at hz
  exact ⟨hdec, hz⟩

/-- Backward-jump section: twenty-one executable bytes at 0x1000. -/
def secRueck : Abschnitt :=
  { dateiOff := 0, dateiLen := 21, vaddr := 0x1000, memLen := 21,
    lesbar := true, schreibbar := false, ausfuehrbar := true,
    ausr := 4096 }

/-- Backward-jump image: sixteen padding bytes, then `jump -16` at file
    offset 16 (loaded 0x1010, target 0x1005). -/
def bildRueck : Bild :=
  { datei := List.replicate 16 (natByte 0) ++
      [natByte 233, natByte 240, natByte 255, natByte 255, natByte 255]
    abschnitte := [secRueck]
    reloks := []
    eintraege := [0x1010]
    modus := .fest }

/-- The backward image is accepted. -/
theorem bildRueck_wohlgeformt : wohlgeformt .p48 bildRueck = true := by
  decide

/-- Backward site: start 0x1010, jump -16 to 0x1005. -/
def siteRueck : PatchSite := ⟨0, 0x1000, 16, .sprung, -16, 0x1005⟩

/-- BACKWARD ACCEPT: the checked site admits the backward jump. -/
theorem rueck_akzeptiert : patchSiteOk siteRueck = true := by
  decide

/-- BACKWARD JOINT: decode plus executed target on the backward site. -/
theorem rueck_gelenk :
    decode (fenster5 bildRueck 0 0x1010) =
      some (⟨.jump32 (BitVec.ofNat 32 4294967280), 5⟩, []) ∧
    direktZiel (BitVec.ofNat 64 0x1010) 5
        (BitVec.ofNat 32 4294967280) =
      BitVec.ofNat 64 0x1005 := by
  have hsec : bildRueck.abschnitte[0]? = some secRueck := by
    decide
  have hfind : ∀ i : Nat, i < 5 →
      abteilFinden bildRueck.abschnitte 0
        (0 + secRueck.vaddr + 16 + i) = some secRueck := by
    intro i hi
    have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> decide
  have hbacked : ∀ i : Nat, i < 5 → 16 + i < secRueck.dateiLen := by
    intro i hi
    have e : secRueck.dateiLen = 21 := rfl
    omega
  have hb0 : dateiByte bildRueck.datei (secRueck.dateiOff + 16) =
      natByte 233 := by
    decide
  have hb1 : dateiByte bildRueck.datei (secRueck.dateiOff + (16 + 1)) =
      natByte ((BitVec.ofNat 32 4294967280).toNat % 256) := by
    decide
  have hb2 : dateiByte bildRueck.datei (secRueck.dateiOff + (16 + 2)) =
      natByte (((BitVec.ofNat 32 4294967280).toNat / 256) % 256) := by
    decide
  have hb3 : dateiByte bildRueck.datei (secRueck.dateiOff + (16 + 3)) =
      natByte (((BitVec.ofNat 32 4294967280).toNat / 65536) % 256) := by
    decide
  have hb4 : dateiByte bildRueck.datei (secRueck.dateiOff + (16 + 4)) =
      natByte (((BitVec.ofNat 32 4294967280).toNat / 16777216) % 256) := by
    decide
  have hdec := bildSite_sprung_dekode bildRueck 0 secRueck
    16 (BitVec.ofNat 32 4294967280) hfind hbacked hb0 hb1 hb2 hb3 hb4
  have hz := (patchSite_ziel siteRueck (BitVec.ofNat 32 4294967280)
    (by decide) (by decide) (by decide) (by decide) (by decide)).1
  have eaddr : 0 + secRueck.vaddr + 16 = 0x1010 := rfl
  rw [eaddr] at hdec
  have es : siteStart siteRueck = 0x1010 := rfl
  have ea : siteRueck.art = RelocArt.sprung := rfl
  rw [es, ea] at hz
  have el : relocLen RelocArt.sprung = 5 := rfl
  rw [el] at hz
  exact ⟨hdec, hz⟩

/-- Biased image: `jump -5` at section base 0x1000, loaded under bias
    0x100000 (start 0x101000, target 0x101000). -/
def bildVersetzt : Bild :=
  { datei := [natByte 233, natByte 251, natByte 255, natByte 255,
      natByte 255]
    abschnitte := [zeugenCode5]
    reloks := []
    eintraege := [0x101000]
    modus := .param 0x100000 }

/-- The biased image is accepted at its parametric base. -/
theorem bildVersetzt_wohlgeformt :
    wohlgeformt .p48 bildVersetzt = true := by
  decide

/-- Biased site: bias 0x100000, base 0x1000, jump -5 to 0x101000. -/
def siteVersetzt : PatchSite :=
  ⟨0x100000, 0x1000, 0, .sprung, -5, 0x101000⟩

/-- BIASED ACCEPT: the checked site admits the relocated jump. -/
theorem versetzt_akzeptiert : patchSiteOk siteVersetzt = true := by
  decide

/-- BIASED JOINT: decode plus executed target under nonzero load bias. -/
theorem versetzt_gelenk :
    decode (fenster5 bildVersetzt 0x100000 0x101000) =
      some (⟨.jump32 (BitVec.ofNat 32 4294967291), 5⟩, []) ∧
    direktZiel (BitVec.ofNat 64 0x101000) 5
        (BitVec.ofNat 32 4294967291) =
      BitVec.ofNat 64 0x101000 := by
  have hfind : ∀ i : Nat, i < 5 →
      abteilFinden bildVersetzt.abschnitte 0x100000
        (0x100000 + zeugenCode5.vaddr + 0 + i) = some zeugenCode5 := by
    intro i hi
    have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> decide
  have hbacked : ∀ i : Nat, i < 5 → 0 + i < zeugenCode5.dateiLen := by
    intro i hi
    have e : zeugenCode5.dateiLen = 5 := rfl
    omega
  have hb0 : dateiByte bildVersetzt.datei (zeugenCode5.dateiOff + 0) =
      natByte 233 := by
    decide
  have hb1 : dateiByte bildVersetzt.datei (zeugenCode5.dateiOff + (0 + 1)) =
      natByte ((BitVec.ofNat 32 4294967291).toNat % 256) := by
    decide
  have hb2 : dateiByte bildVersetzt.datei (zeugenCode5.dateiOff + (0 + 2)) =
      natByte (((BitVec.ofNat 32 4294967291).toNat / 256) % 256) := by
    decide
  have hb3 : dateiByte bildVersetzt.datei (zeugenCode5.dateiOff + (0 + 3)) =
      natByte (((BitVec.ofNat 32 4294967291).toNat / 65536) % 256) := by
    decide
  have hb4 : dateiByte bildVersetzt.datei (zeugenCode5.dateiOff + (0 + 4)) =
      natByte (((BitVec.ofNat 32 4294967291).toNat / 16777216) % 256) := by
    decide
  have hdec := bildSite_sprung_dekode bildVersetzt 0x100000 zeugenCode5 0
    (BitVec.ofNat 32 4294967291) hfind hbacked hb0 hb1 hb2 hb3 hb4
  have hz := (patchSite_ziel siteVersetzt (BitVec.ofNat 32 4294967291)
    (by decide) (by decide) (by decide) (by decide) (by decide)).1
  have eaddr : 0x100000 + zeugenCode5.vaddr + 0 = 0x101000 := rfl
  rw [eaddr] at hdec
  have es : siteStart siteVersetzt = 0x101000 := rfl
  have ea : siteVersetzt.art = RelocArt.sprung := rfl
  rw [es, ea] at hz
  have el : relocLen RelocArt.sprung = 5 := rfl
  rw [el] at hz
  exact ⟨hdec, hz⟩

/-! ## 9. Call witness with memory change, and planted refusals. -/

/-- Call code section: `call +16` at 0x1000. -/
def zeugenCodeRuf : Abschnitt :=
  { dateiOff := 0, dateiLen := 5, vaddr := 0x1000, memLen := 5,
    lesbar := true, schreibbar := false, ausfuehrbar := true, ausr := 4096 }

/-- Call stack section: eight writable bytes at 0x1FF8, three file-backed. -/
def zeugenStapelRuf : Abschnitt :=
  { dateiOff := 5, dateiLen := 3, vaddr := 0x1FF8, memLen := 8,
    lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := 1 }

/-- Call image: `call +16` plus three zero data bytes. -/
def bildRuf : Bild :=
  { datei := [natByte 232, natByte 16, natByte 0, natByte 0, natByte 0, natByte 0, natByte 0, natByte 0]
    abschnitte := [zeugenCodeRuf, zeugenStapelRuf]
    reloks := []
    eintraege := [0x1000]
    modus := .fest }

/-- The call image is accepted. -/
theorem bildRuf_wohlgeformt : wohlgeformt .p48 bildRuf = true := by
  decide

/-- Call site: bias 0, base 0x1000, call +16 to 0x1015. -/
def siteRuf : PatchSite := ⟨0, 0x1000, 0, .ruf, 16, 0x1015⟩

/-- CALL ACCEPT: the checked site admits the direct call. -/
theorem ruf_akzeptiert : patchSiteOk siteRuf = true := by
  decide

/-- Call witness registers: stack top at 0x2000, everything else zero. -/
def regRuf : Register → Wort := fun q =>
  if q = Register.rsp then BitVec.ofNat 64 0x2000 else BitVec.ofNat 64 0

/-- Call witness state: loaded image, instruction at 0x1000. -/
def zustandRuf : Zustand :=
  { register := regRuf
    flags := witnessFlags
    rip := BitVec.ofNat 64 0x1000
    speicher := geladen bildRuf 0 }

/-- CALL JOINT: the byte step stores the return address 0x1005 at the
    stack slot, reads it back, observably changes the memory byte from
    zero, and lands on the intended target. Memory change and control
    transfer come from actual loaded bytes through `byteschritt`. -/
theorem ruf_schritt_zeuge :
    ∃ m : Speicher, byteschritt zustandRuf =
      .weiter (schrittCall zustandRuf Register.rsp m
        (zustandRuf.register Register.rsp - BitVec.ofNat 64 8)
        (BitVec.ofNat 64 0x1015)) ∧
      read64 m (BitVec.ofNat 64 0x1FF8) = some (BitVec.ofNat 64 0x1005) ∧
      m.bytes (BitVec.ofNat 64 0x1FF8) ≠
        zustandRuf.speicher.bytes (BitVec.ofNat 64 0x1FF8) := by
  have hwin : geholt zustandRuf =
      relocBytes .ruf (BitVec.ofNat 32 16) ++ [] := by
    decide
  have hexe : ausfuehrbarN zustandRuf.speicher zustandRuf.rip
      (relocBytes .ruf (BitVec.ofNat 32 16)).length = true := by
    decide
  have eadr : zustandRuf.register Register.rsp - BitVec.ofNat 64 8 =
      BitVec.ofNat 64 0x1FF8 := by
    decide
  have enach : ripNach zustandRuf.rip
      (encode (.call32 (BitVec.ofNat 32 16))).length =
      BitVec.ofNat 64 0x1005 := by
    decide
  have hschr : schreibbar8 zustandRuf.speicher
      (BitVec.ofNat 64 0x1FF8) = true := by
    decide
  have hles : lesbar8 zustandRuf.speicher
      (BitVec.ofNat 64 0x1FF8) = true := by
    decide
  have hwr : write64 zustandRuf.speicher (BitVec.ofNat 64 0x1FF8)
      (BitVec.ofNat 64 0x1005) = some { zustandRuf.speicher with bytes := writeBytes zustandRuf.speicher (BitVec.ofNat 64 0x1FF8) (BitVec.ofNat 64 0x1005) } := by
    unfold write64
    rw [if_pos hschr]
  have hwr0 : write64 zustandRuf.speicher
      (zustandRuf.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach zustandRuf.rip
        (encode (.call32 (BitVec.ofNat 32 16))).length) = some { zustandRuf.speicher with bytes := writeBytes zustandRuf.speicher (BitVec.ofNat 64 0x1FF8) (BitVec.ofNat 64 0x1005) } := by
    rw [eadr, enach]
    exact hwr
  have hhit := writeBytesN_hit zustandRuf.speicher (BitVec.ofNat 64 0x1FF8)
    (BitVec.ofNat 64 0x1005) 8 0 (by decide) (by decide)
  have hnull := addrOff_null (BitVec.ofNat 64 0x1FF8)
  rw [hnull] at hhit
  have hhit2 : writeBytes zustandRuf.speicher (BitVec.ofNat 64 0x1FF8)
      (BitVec.ofNat 64 0x1005) (BitVec.ofNat 64 0x1FF8) =
      wortByte (BitVec.ofNat 64 0x1005) 0 := hhit
  have hinit : zustandRuf.speicher.bytes (BitVec.ofNat 64 0x1FF8) =
      BitVec.ofNat 8 0 := by
    decide
  refine ⟨{ zustandRuf.speicher with bytes := writeBytes zustandRuf.speicher (BitVec.ofNat 64 0x1FF8) (BitVec.ofNat 64 0x1005) }, ?_, ?_, ?_⟩
  · exact patchSite_ruf_schritt siteRuf (BitVec.ofNat 32 16) _
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl
      zustandRuf [] hwin hexe rfl hwr0
  · exact read64_nach_write64 _ _ _ _ hwr hles
  · show writeBytes zustandRuf.speicher (BitVec.ofNat 64 0x1FF8)
        (BitVec.ofNat 64 0x1005) (BitVec.ofNat 64 0x1FF8) ≠
        zustandRuf.speicher.bytes (BitVec.ofNat 64 0x1FF8)
    rw [hhit2, hinit]
    decide

/-- REFUSAL (out of range): displacement 2^31 admits no site. -/
theorem aussen_verweigert :
    patchSiteOk ⟨0, 0x1000, 0, .sprung, 2147483648, 0x1000⟩ = false := by
  decide

/-- REFUSAL (out of range): no patch bytes are computed either. -/
theorem aussen_rel32Fuer :
    rel32Fuer 4101 (4101 + 2147483648) = none := by
  decide

/-- REFUSAL (interior target): 0x1002 satisfies the next-RIP equation
    (0x1000 + 5 - 3) but lies strictly inside the site's own bytes. -/
theorem innen_verweigert :
    patchSiteOk ⟨0, 0x1000, 0, .sprung, -3, 0x1002⟩ = false := by
  decide

/- CUTS:
    - Proved here: site vocabulary over the canonical encoder (`RelocArt`,
      `relocLen`, `relocBefehl`, `relocBytes` with lengths and decoder
      round-trip); the `dispWort`-to-`rel32Enc64` displacement bridge;
      every in-range displacement realized by a field (`dispVonFit`); the
      checked site (`patchSiteOk`) with acceptance, out-of-range and
      interior-target refusals; the patch-and-redecode target equation
      (`patchSite_ziel`, word and Nat); actual-memory `byteschritt`
      execution to the target for jump, call (memory-changing), taken and
      not-taken conditional; loaded-window image decode for all three
      classes through the checked mapping (`ladenByte_fenster`,
      `bildSite_*_dekode`); the code-operand-only class cut
      (`siteArtOk`); joint forward/backward/nonzero-bias witnesses over
      accepted images; a joint call witness with return-address store,
      read-back, observable byte change and target; planted out-of-range
      and interior-target refusals.
    - Explicitly OPEN (unsupported site classes): abs64/data-field sites
      (`patchAbs64` bytes never decode here; `siteArtOk` refuses
      `datenFeld`); rel8 short selection (no codec row, refused by
      `zweigOk_kurz`); any instruction outside jump/call/conditional (no
      `RelocArt` case, no claim).
    - No whole-image layout: one site at its final layout only;
      multi-site convergence, fall-through coverage and the full
      `DecodingCoverage`/`valX86` closing theorem stay with the consumer.
    - No loader execution: `geladen` is the pure mapping function; loader
      behaviour, entry handoff and OS interaction are not modelled.
    - No source correspondence, no TSO/GX bridge, no concurrency, no cost
      or time transfer: validation runs on final bytes only.
    - No second decoder, loader, executor, ISA or IR is created here:
      every fact reuses the producer modules.
-/

#print axioms testBit_div_pow
#print axioms bit31_equiv
#print axioms dispWort_bridge
#print axioms relocBytes_len
#print axioms relocBytes_decode
#print axioms dispVonFit
#print axioms patchSiteOk_akzeptiert
#print axioms patchSiteOk_disp_aussen
#print axioms patchSiteOk_innen
#print axioms patchSite_ziel
#print axioms patchSite_sprung_schritt
#print axioms patchSite_ruf_schritt
#print axioms patchSite_bedingt_genommen_schritt
#print axioms patchSite_bedingt_nicht_schritt
#print axioms ladenByte_fenster
#print axioms bildSite_sprung_dekode
#print axioms bildSite_ruf_dekode
#print axioms bildSite_bedingt_dekode
#print axioms siteArtOk_code_akzeptiert
#print axioms siteArtOk_daten_verweigert
#print axioms bildVor_wohlgeformt
#print axioms vor_akzeptiert
#print axioms vor_gelenk
#print axioms bildRueck_wohlgeformt
#print axioms rueck_akzeptiert
#print axioms rueck_gelenk
#print axioms bildVersetzt_wohlgeformt
#print axioms versetzt_akzeptiert
#print axioms versetzt_gelenk
#print axioms bildRuf_wohlgeformt
#print axioms ruf_akzeptiert
#print axioms ruf_schritt_zeuge
#print axioms aussen_verweigert
#print axioms aussen_rel32Fuer
#print axioms innen_verweigert

end Gabbro.Grammatik.X86
