/-
  File:      Grammatik/X86/PipelineLinkMulti.lean
  Subject:   Multi-unit linking convergence and operand kinds.

  FOLLOW-UP of lane 1171 (`PipelineLink.lean`, two units, one rel32
  operand per closing): n-unit concatenation with tiling sections,
  several operands per closing, abs64 and rel8 operand re-decode,
  call and conditional-jump field agreement, with the invariant that
  no relocation changes a byte outside its operand.

  Reused, never duplicated (no second decoder, loader, executor,
  ISA model or IR):
  - two-unit base: `PipelineLink.LinkEinheit`, `linkPatch_*`
    (rel32/abs64 range, site, frame, length);
  - patching/codec: `Relokation.patchAt_*`, `patchRel32`,
    `patchAbs64`, `rel32Bytes`, `abs64Bytes`, `abs64_rundgang`;
  - field agreement bridge: `BranchLayout.dispSigned`,
    `rel32Bytes_dispSigned`, `RelocatedExecution.dispVonFit`,
    `Codec.roundtrip_jump32/_call32/_jumpIf32`;
  - rel8 vocabulary: `Rel8Reach.rel8Passt`, `disp8Signed`;
  - mapping: `Bild.geladenByte_datei`, `ValidatorSkeleton`
    coverage, `LoadedExecution.wohlgeformt_wx`;
  - run: `RelocatedExecution.ruf_schritt_zeuge`.
-/
import Grammatik.X86.PipelineLink
import Grammatik.X86.ComposePatchBytes
import Grammatik.X86.Rel8Reach
import Grammatik.X86.BranchLayout

namespace Gabbro.Grammatik.X86

/-- Relocation operand kind at link time: rel32 displacement, abs64
    value, or rel8 short displacement. The rel32/abs64 cases patch
    exactly what `PipelineLink.linkPatch` patches (proved equal
    below); rel8 is the one new kind. -/
inductive MultiFeld where
  | rel32 (disp : Int)
  | abs64 (wert : Wort)
  | rel8 (disp : Int)
  deriving DecidableEq, Repr

/-- One rel8 displacement byte: two's complement mod 256. -/
def rel8Byte (d : Int) : Byte := natByte (tcNat d 256)

/-- The bytes one operand writes: the canonical splits, never a
    second codec. -/
def multiBytes : MultiFeld → List Byte
  | .rel32 d => rel32Bytes d
  | .abs64 v => abs64Bytes v
  | .rel8 d => [rel8Byte d]

/-- A rel32 operand is four bytes wide. -/
theorem multiBytes_rel32_laenge (d : Int) :
    (multiBytes (.rel32 d)).length = 4 := by
  simp [multiBytes, rel32Bytes_laenge]

/-- An abs64 operand is eight bytes wide. -/
theorem multiBytes_abs64_laenge (v : Wort) :
    (multiBytes (.abs64 v)).length = 8 := by
  simp [multiBytes, abs64Bytes_laenge]

/-- A rel8 operand is one byte wide. -/
theorem multiBytes_rel8_laenge (d : Int) :
    (multiBytes (.rel8 d)).length = 1 := rfl

/-- Apply one relocation operand at file offset `off`. rel32 refuses
    out-of-range displacements, rel8 refuses out-of-range short
    displacements, abs64 patches any in-range site; anything else
    is `none`, never guessed. -/
def multiPatch (img : List Byte) (off : Nat) : MultiFeld → Option (List Byte)
  | .rel32 d => patchRel32 img off d
  | .abs64 v => patchAbs64 img off v
  | .rel8 d => if rel8Passt d then patchAt img off [rel8Byte d] else none

/-- The rel32 case patches exactly what the two-unit link patches:
    reuse, not a second rule. -/
theorem multiPatch_rel32_gleich (img : List Byte) (off : Nat) (d : Int) :
    multiPatch img off (.rel32 d) = linkPatch img off (.rel32 d) := rfl

/-- The abs64 case patches exactly what the two-unit link patches. -/
theorem multiPatch_abs64_gleich (img : List Byte) (off : Nat) (v : Wort) :
    multiPatch img off (.abs64 v) = linkPatch img off (.abs64 v) := rfl

/-! ## 1. One applied operand: range, site bytes, frame, length.

    The rel32/abs64 legs reuse the two-unit link facts by the
    equalities above; only the rel8 leg patches directly, through
    the accepted `patchAt_*` producer facts. -/

/-- A successful multi patch lies inside the image. -/
theorem multiPatch_bereich (img : List Byte) (off : Nat) (f : MultiFeld)
    (out : List Byte) (h : multiPatch img off f = some out) :
    off + (multiBytes f).length ≤ img.length := by
  cases f with
  | rel32 d =>
    rw [multiPatch_rel32_gleich] at h
    simp only [multiBytes]
    exact linkPatch_bereich img off (.rel32 d) out h
  | abs64 v =>
    rw [multiPatch_abs64_gleich] at h
    simp only [multiBytes]
    exact linkPatch_bereich img off (.abs64 v) out h
  | rel8 d =>
    simp only [multiPatch, multiBytes] at h ⊢
    by_cases hc : rel8Passt d = true
    · rw [if_pos hc] at h
      exact patchAt_bereich img off [rel8Byte d] out h
    · rw [if_neg hc] at h
      cases h

/-- A successful multi patch writes exactly the operand bytes. -/
theorem multiPatch_stelle (img : List Byte) (off : Nat) (f : MultiFeld)
    (out : List Byte) (h : multiPatch img off f = some out)
    (k : Nat) (hk : k < (multiBytes f).length) :
    out[off + k]? = (multiBytes f)[k]? := by
  cases f with
  | rel32 d =>
    rw [multiPatch_rel32_gleich] at h
    simp only [multiBytes] at hk ⊢
    rw [rel32Bytes_laenge] at hk
    exact linkPatch_stelle img off (.rel32 d) out h k hk
  | abs64 v =>
    rw [multiPatch_abs64_gleich] at h
    simp only [multiBytes] at hk ⊢
    rw [abs64Bytes_laenge] at hk
    exact linkPatch_stelle img off (.abs64 v) out h k hk
  | rel8 d =>
    simp only [multiPatch] at h
    simp only [multiBytes] at hk ⊢
    by_cases hc : rel8Passt d = true
    · rw [if_pos hc] at h
      exact patchAt_stelle img off [rel8Byte d] out h k (by simpa using hk)
    · rw [if_neg hc] at h
      cases h

/-- FRAME: bytes outside the operand keep their image bytes. No
    relocation, rel32, abs64 or rel8, touches anything else. -/
theorem multiPatch_rahmen (img : List Byte) (off : Nat) (f : MultiFeld)
    (out : List Byte) (h : multiPatch img off f = some out)
    (i : Nat) (haussen : ∀ k, k < (multiBytes f).length → i ≠ off + k) :
    out[i]? = img[i]? := by
  cases f with
  | rel32 d =>
    rw [multiPatch_rel32_gleich] at h
    simp only [multiBytes] at haussen
    exact linkPatch_rahmen img off (.rel32 d) out h i haussen
  | abs64 v =>
    rw [multiPatch_abs64_gleich] at h
    simp only [multiBytes] at haussen
    exact linkPatch_rahmen img off (.abs64 v) out h i haussen
  | rel8 d =>
    simp only [multiPatch] at h
    simp only [multiBytes] at haussen
    by_cases hc : rel8Passt d = true
    · rw [if_pos hc] at h
      exact patchAt_rahmen img off [rel8Byte d] out h i haussen
    · rw [if_neg hc] at h
      cases h

/-- A successful multi patch keeps the image length. -/
theorem multiPatch_laenge (img : List Byte) (off : Nat) (f : MultiFeld)
    (out : List Byte) (h : multiPatch img off f = some out) :
    out.length = img.length := by
  cases f with
  | rel32 d =>
    rw [multiPatch_rel32_gleich] at h
    exact linkPatch_laenge img off (.rel32 d) out h
  | abs64 v =>
    rw [multiPatch_abs64_gleich] at h
    exact linkPatch_laenge img off (.abs64 v) out h
  | rel8 d =>
    simp only [multiPatch] at h
    by_cases hc : rel8Passt d = true
    · rw [if_pos hc] at h
      exact patchAt_laenge img off [rel8Byte d] out h
    · rw [if_neg hc] at h
      cases h

/-! ## 2. rel8 byte round-trip: the patched byte reads back. -/

/-- Encode/round-trip for every in-range short displacement: the
    patched byte reads back to exactly `d`. Both bounds are
    load-bearing: `hlo` keeps the negative representative in byte,
    `hhi` keeps the non-negative one below 128. -/
theorem rel8Byte_rundgang (d : Int) (hlo : -128 ≤ d) (hhi : d < 128) :
    disp8Signed (rel8Byte d) = d := by
  have h256 : (2 ^ 8 : Nat) = 256 := rfl
  by_cases h : 0 ≤ d
  · have e1 : tcNat d 256 = d.toNat := by
      unfold tcNat
      rw [if_pos h]
    have hmod : d.toNat % 256 = d.toNat := Nat.mod_eq_of_lt (by omega)
    unfold rel8Byte disp8Signed natByte
    rw [e1, BitVec.toNat_ofNat, h256, hmod, if_pos (by omega : d.toNat < 128)]
    exact Int.toNat_of_nonneg h
  · have e1 : tcNat d 256 = (d + ((256 : Nat) : Int)).toNat := by
      unfold tcNat
      rw [if_neg h]
    have hmod : (d + ((256 : Nat) : Int)).toNat % 256 =
        (d + ((256 : Nat) : Int)).toNat :=
      Nat.mod_eq_of_lt (by omega)
    unfold rel8Byte disp8Signed natByte
    rw [e1, BitVec.toNat_ofNat, h256, hmod,
      if_neg (by omega : ¬ (d + ((256 : Nat) : Int)).toNat < 128)]
    omega

/-! ## 3. Field agreement: patched operands re-decoded.

    The determinism tails (patched window bytes plus an admitted
    re-decode determine the field) factored per site class, so the
    single-patch legs below and the multi-operand closing in §6
    share them. Each goes through the accepted byte bridge
    (`rel32Bytes_dispSigned`) and decoder determinism, never
    through decoder internals. -/

/-- FIELD AGREEMENT, unconditional jump: a five-byte window with the
    jump opcode and the displacement bytes that re-decodes to a
    five-byte jump carries the patched displacement; the length
    equation holds, the form is covered, and the exact five-byte
    region re-decodes. Every premise is load-bearing: `hfit` feeds
    the bridge, `htake` fixes the window bytes, `hdec` drives the
    determinism. -/
theorem feld_agreement_sprung (w : List Byte) (istart : Nat) (disp : Int)
    (d : BitVec 32) (rest : List Byte)
    (hfit : rel32Passt disp = true)
    (htake : (w.drop istart).take 5 = natByte 233 :: rel32Bytes disp)
    (hdec : decode (w.drop istart) = some ((⟨.jump32 d, 5⟩, rest))) :
    dispSigned d = disp ∧
    5 + rest.length = (w.drop istart).length ∧
    decktAb ⟨.jump32 d, 5⟩ ∧
    decode ((w.drop istart).take 5 ++ rest) =
      some ((⟨.jump32 d, 5⟩, rest)) := by
  have hfitI := of_decide_eq_true hfit
  obtain ⟨d₀, hd₀⟩ := dispVonFit disp hfitI.1 hfitI.2
  have hbridge : rel32Bytes disp = leBytes32 d₀ := by
    rw [← hd₀]
    exact rel32Bytes_dispSigned d₀
  obtain ⟨heq0, hok, hshape, pre, hbs, hplen⟩ :=
    decode_abdeckung (w.drop istart) _ rest hdec
  have heq : 5 + rest.length = (w.drop istart).length := heq0
  obtain ⟨hrest, hwhole⟩ :=
    decode_fenster_kongruenz (w.drop istart) _ rest hdec
  have hlaenge : (⟨.jump32 d, 5⟩ : Decodiert).laenge = 5 := rfl
  rw [hlaenge, htake] at hwhole
  have hdec' : decode ((natByte 233 :: rel32Bytes disp) ++ rest) =
      some ((⟨.jump32 d, 5⟩, rest)) := by
    rw [hwhole]
    exact hdec
  have hregion : decode ((w.drop istart).take 5 ++ rest) =
      some ((⟨.jump32 d, 5⟩, rest)) := by
    rw [htake]
    exact hdec'
  rw [hbridge] at hdec'
  have hcanon := relocBytes_decode .sprung d₀ rest
  have henc : relocBytes .sprung d₀ = natByte 233 :: leBytes32 d₀ := rfl
  have hlen5 : (natByte 233 :: leBytes32 d₀).length = 5 := by
    simp [length_leBytes32]
  rw [henc, hlen5] at hcanon
  have hinj := Option.some_inj.mp (hcanon.symm.trans hdec')
  have hpair : (⟨relocBefehl .sprung d₀, 5⟩ : Decodiert) = ⟨.jump32 d, 5⟩ :=
    congrArg Prod.fst hinj
  have hbeq : relocBefehl .sprung d₀ = .jump32 d := by
    have h := congrArg Decodiert.befehl hpair
    dsimp only at h
    exact h
  have heqdd : d₀ = d := by
    simp only [relocBefehl] at hbeq
    cases hbeq
    rfl
  rw [heqdd] at hd₀
  exact ⟨hd₀, heq, hshape, hregion⟩

/-- FIELD AGREEMENT, direct call: a five-byte window with the call
    opcode and the displacement bytes that re-decodes to a five-byte
    call carries the patched displacement; same legs as the jump. -/
theorem feld_agreement_ruf (w : List Byte) (istart : Nat) (disp : Int)
    (d : BitVec 32) (rest : List Byte)
    (hfit : rel32Passt disp = true)
    (htake : (w.drop istart).take 5 = natByte 232 :: rel32Bytes disp)
    (hdec : decode (w.drop istart) = some ((⟨.call32 d, 5⟩, rest))) :
    dispSigned d = disp ∧
    5 + rest.length = (w.drop istart).length ∧
    decktAb ⟨.call32 d, 5⟩ ∧
    decode ((w.drop istart).take 5 ++ rest) =
      some ((⟨.call32 d, 5⟩, rest)) := by
  have hfitI := of_decide_eq_true hfit
  obtain ⟨d₀, hd₀⟩ := dispVonFit disp hfitI.1 hfitI.2
  have hbridge : rel32Bytes disp = leBytes32 d₀ := by
    rw [← hd₀]
    exact rel32Bytes_dispSigned d₀
  obtain ⟨heq0, hok, hshape, pre, hbs, hplen⟩ :=
    decode_abdeckung (w.drop istart) _ rest hdec
  have heq : 5 + rest.length = (w.drop istart).length := heq0
  obtain ⟨hrest, hwhole⟩ :=
    decode_fenster_kongruenz (w.drop istart) _ rest hdec
  have hlaenge : (⟨.call32 d, 5⟩ : Decodiert).laenge = 5 := rfl
  rw [hlaenge, htake] at hwhole
  have hdec' : decode ((natByte 232 :: rel32Bytes disp) ++ rest) =
      some ((⟨.call32 d, 5⟩, rest)) := by
    rw [hwhole]
    exact hdec
  have hregion : decode ((w.drop istart).take 5 ++ rest) =
      some ((⟨.call32 d, 5⟩, rest)) := by
    rw [htake]
    exact hdec'
  rw [hbridge] at hdec'
  have hcanon := relocBytes_decode .ruf d₀ rest
  have henc : relocBytes .ruf d₀ = natByte 232 :: leBytes32 d₀ := rfl
  have hlen5 : (natByte 232 :: leBytes32 d₀).length = 5 := by
    simp [length_leBytes32]
  rw [henc, hlen5] at hcanon
  have hinj := Option.some_inj.mp (hcanon.symm.trans hdec')
  have hpair : (⟨relocBefehl .ruf d₀, 5⟩ : Decodiert) = ⟨.call32 d, 5⟩ :=
    congrArg Prod.fst hinj
  have hbeq : relocBefehl .ruf d₀ = .call32 d := by
    have h := congrArg Decodiert.befehl hpair
    dsimp only at h
    exact h
  have heqdd : d₀ = d := by
    simp only [relocBefehl] at hbeq
    cases hbeq
    rfl
  rw [heqdd] at hd₀
  exact ⟨hd₀, heq, hshape, hregion⟩

/-- FIELD AGREEMENT, conditional jump: a six-byte window with the
    two condition-opcode bytes and the displacement bytes that
    re-decodes to a six-byte conditional jump carries the patched
    displacement AND the condition: the decoded condition is the
    patched site's condition, never a neighbouring one. -/
theorem feld_agreement_bedingt (w : List Byte) (istart : Nat)
    (c : Bedingung) (disp : Int) (d : BitVec 32) (rest : List Byte)
    (hfit : rel32Passt disp = true)
    (htake : (w.drop istart).take 6 =
      natByte 15 :: natByte (128 + condCode c) :: rel32Bytes disp)
    (hdec : decode (w.drop istart) =
      some ((⟨.jumpIf32 c d, 6⟩, rest))) :
    dispSigned d = disp ∧
    6 + rest.length = (w.drop istart).length ∧
    decktAb ⟨.jumpIf32 c d, 6⟩ ∧
    decode ((w.drop istart).take 6 ++ rest) =
      some ((⟨.jumpIf32 c d, 6⟩, rest)) := by
  have hfitI := of_decide_eq_true hfit
  obtain ⟨d₀, hd₀⟩ := dispVonFit disp hfitI.1 hfitI.2
  have hbridge : rel32Bytes disp = leBytes32 d₀ := by
    rw [← hd₀]
    exact rel32Bytes_dispSigned d₀
  obtain ⟨heq0, hok, hshape, pre, hbs, hplen⟩ :=
    decode_abdeckung (w.drop istart) _ rest hdec
  have heq : 6 + rest.length = (w.drop istart).length := heq0
  obtain ⟨hrest, hwhole⟩ :=
    decode_fenster_kongruenz (w.drop istart) _ rest hdec
  have hlaenge : (⟨.jumpIf32 c d, 6⟩ : Decodiert).laenge = 6 := rfl
  rw [hlaenge, htake] at hwhole
  have hdec' : decode ((natByte 15 :: natByte (128 + condCode c) ::
      rel32Bytes disp) ++ rest) =
      some ((⟨.jumpIf32 c d, 6⟩, rest)) := by
    rw [hwhole]
    exact hdec
  have hregion : decode ((w.drop istart).take 6 ++ rest) =
      some ((⟨.jumpIf32 c d, 6⟩, rest)) := by
    rw [htake]
    exact hdec'
  rw [hbridge] at hdec'
  have hcanon := relocBytes_decode (.bedingt c) d₀ rest
  have henc : relocBytes (.bedingt c) d₀ =
      natByte 15 :: natByte (128 + condCode c) :: leBytes32 d₀ := rfl
  have hlen6 : (natByte 15 :: natByte (128 + condCode c) ::
      leBytes32 d₀).length = 6 := by
    simp [length_leBytes32]
  rw [henc, hlen6] at hcanon
  have hinj := Option.some_inj.mp (hcanon.symm.trans hdec')
  have hpair : (⟨relocBefehl (.bedingt c) d₀, 6⟩ : Decodiert) =
      ⟨.jumpIf32 c d, 6⟩ :=
    congrArg Prod.fst hinj
  have hbeq : relocBefehl (.bedingt c) d₀ = .jumpIf32 c d := by
    have h := congrArg Decodiert.befehl hpair
    dsimp only at h
    exact h
  have heqdd : d₀ = d := by
    simp only [relocBefehl] at hbeq
    cases hbeq
    rfl
  rw [heqdd] at hd₀
  exact ⟨hd₀, heq, hshape, hregion⟩

/-! ## 4. Patched windows: opcode plus field bytes as take equations.

    The bridge between per-byte patch facts (site/frame) and the
    agreement legs above, which take window equations. -/

/-- A patched jump window takes to opcode plus displacement bytes. -/
theorem fenster_sprung (w : List Byte) (istart : Nat) (disp : Int)
    (hop : w[istart]? = some (natByte 233))
    (hfeld : ∀ k, k < 4 → w[istart + 1 + k]? = (rel32Bytes disp)[k]?) :
    (w.drop istart).take 5 = natByte 233 :: rel32Bytes disp := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 5
  · by_cases hi0 : i = 0
    · subst hi0
      have hL0 : ((w.drop istart).take 5)[0]? = w[istart]? := by simp
      have hR0 : (natByte 233 :: rel32Bytes disp)[0]? =
          some (natByte 233) := by simp
      rw [hL0, hR0, hop]
    · obtain ⟨k, rfl, hk⟩ : ∃ k, i = k + 1 ∧ k < 4 :=
        ⟨i - 1, by omega, by omega⟩
      have hL1 : ((w.drop istart).take 5)[k + 1]? =
          w[istart + 1 + k]? := by
        have e : istart + (k + 1) = istart + 1 + k := by omega
        simp only [List.getElem?_take, List.getElem?_drop]
        rw [if_pos hi, e]
      rw [hL1, hfeld k hk]
      simp
  · have hLnone : ((w.drop istart).take 5)[i]? = none := by
      rw [List.getElem?_take, if_neg hi]
    have hRnone : (natByte 233 :: rel32Bytes disp)[i]? = none := by
      have hle : (natByte 233 :: rel32Bytes disp).length ≤ i := by
        simp [rel32Bytes_laenge]
        omega
      exact List.getElem?_eq_none hle
    rw [hLnone, hRnone]

/-- A patched call window takes to opcode plus displacement bytes. -/
theorem fenster_ruf (w : List Byte) (istart : Nat) (disp : Int)
    (hop : w[istart]? = some (natByte 232))
    (hfeld : ∀ k, k < 4 → w[istart + 1 + k]? = (rel32Bytes disp)[k]?) :
    (w.drop istart).take 5 = natByte 232 :: rel32Bytes disp := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 5
  · by_cases hi0 : i = 0
    · subst hi0
      have hL0 : ((w.drop istart).take 5)[0]? = w[istart]? := by simp
      have hR0 : (natByte 232 :: rel32Bytes disp)[0]? =
          some (natByte 232) := by simp
      rw [hL0, hR0, hop]
    · obtain ⟨k, rfl, hk⟩ : ∃ k, i = k + 1 ∧ k < 4 :=
        ⟨i - 1, by omega, by omega⟩
      have hL1 : ((w.drop istart).take 5)[k + 1]? =
          w[istart + 1 + k]? := by
        have e : istart + (k + 1) = istart + 1 + k := by omega
        simp only [List.getElem?_take, List.getElem?_drop]
        rw [if_pos hi, e]
      rw [hL1, hfeld k hk]
      simp
  · have hLnone : ((w.drop istart).take 5)[i]? = none := by
      rw [List.getElem?_take, if_neg hi]
    have hRnone : (natByte 232 :: rel32Bytes disp)[i]? = none := by
      have hle : (natByte 232 :: rel32Bytes disp).length ≤ i := by
        simp [rel32Bytes_laenge]
        omega
      exact List.getElem?_eq_none hle
    rw [hLnone, hRnone]

/-- A patched conditional window takes to both opcode bytes plus the
    displacement bytes. -/
theorem fenster_bedingt (w : List Byte) (istart : Nat) (c : Bedingung)
    (disp : Int)
    (hop0 : w[istart]? = some (natByte 15))
    (hop1 : w[istart + 1]? = some (natByte (128 + condCode c)))
    (hfeld : ∀ k, k < 4 → w[istart + 2 + k]? = (rel32Bytes disp)[k]?) :
    (w.drop istart).take 6 =
      natByte 15 :: natByte (128 + condCode c) :: rel32Bytes disp := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 6
  · by_cases hi0 : i = 0
    · subst hi0
      have hL0 : ((w.drop istart).take 6)[0]? = w[istart]? := by simp
      have hR0 : (natByte 15 :: natByte (128 + condCode c) ::
          rel32Bytes disp)[0]? = some (natByte 15) := by simp
      rw [hL0, hR0, hop0]
    · by_cases hi1 : i = 1
      · subst hi1
        have hL1 : ((w.drop istart).take 6)[1]? = w[istart + 1]? := by simp
        have hR1 : (natByte 15 :: natByte (128 + condCode c) ::
            rel32Bytes disp)[1]? =
            some (natByte (128 + condCode c)) := by simp
        rw [hL1, hR1, hop1]
      · obtain ⟨k, rfl, hk⟩ : ∃ k, i = k + 2 ∧ k < 4 :=
          ⟨i - 2, by omega, by omega⟩
        have hL : ((w.drop istart).take 6)[k + 2]? =
            w[istart + 2 + k]? := by
          have e : istart + (k + 2) = istart + 2 + k := by omega
          simp only [List.getElem?_take, List.getElem?_drop]
          rw [if_pos hi, e]
        rw [hL, hfeld k hk]
        simp
  · have hLnone : ((w.drop istart).take 6)[i]? = none := by
      rw [List.getElem?_take, if_neg hi]
    have hRnone : (natByte 15 :: natByte (128 + condCode c) ::
        rel32Bytes disp)[i]? = none := by
      have hle : (natByte 15 :: natByte (128 + condCode c) ::
          rel32Bytes disp).length ≤ i := by
        simp [rel32Bytes_laenge]
        omega
      exact List.getElem?_eq_none hle
    rw [hLnone, hRnone]

/-- A patched abs64 window takes to the value bytes. -/
theorem fenster_abs64 (w : List Byte) (off : Nat) (v : Wort)
    (hfeld : ∀ k, k < 8 → w[off + k]? = (abs64Bytes v)[k]?) :
    (w.drop off).take 8 = abs64Bytes v := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 8
  · have hL : ((w.drop off).take 8)[i]? = w[off + i]? := by
      simp only [List.getElem?_take, List.getElem?_drop]
      rw [if_pos hi]
    rw [hL]
    exact hfeld i hi
  · have hLnone : ((w.drop off).take 8)[i]? = none := by
      rw [List.getElem?_take, if_neg hi]
    have hRnone : (abs64Bytes v)[i]? = none := by
      have hle : (abs64Bytes v).length ≤ i := by
        rw [abs64Bytes_laenge]
        omega
      exact List.getElem?_eq_none hle
    rw [hLnone, hRnone]

/-- A patched rel8 window takes to the displacement byte. -/
theorem fenster_rel8 (w : List Byte) (off : Nat) (d : Int)
    (hbyte : w[off]? = some (rel8Byte d)) :
    (w.drop off).take 1 = [rel8Byte d] := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 1
  · have hi0 : i = 0 := by omega
    subst hi0
    have hL : ((w.drop off).take 1)[0]? = w[off]? := by simp
    have hR : ([rel8Byte d])[0]? = some (rel8Byte d) := by simp
    rw [hL, hR, hbyte]
  · have hLnone : ((w.drop off).take 1)[i]? = none := by
      rw [List.getElem?_take, if_neg hi]
    have hRnone : ([rel8Byte d])[i]? = none := by
      have hle : ([rel8Byte d]).length ≤ i := by
        simp
        omega
      exact List.getElem?_eq_none hle
    rw [hLnone, hRnone]

/-! ## 5. Single-patch re-decode legs per operand kind.

    Opcode survival (frame) plus field bytes (site) give the window
    take equation, and the agreement legs of §3 close the re-decode.
    The jump leg is the reused producer closing
    (`verknuepft_rel32_schliesst`); call, conditional, abs64 and
    rel8 are proved here, through the same bridge and determinism. -/

/-- RE-DECODE, direct call: a patched call operand re-decodes to the
    patched displacement, through the accepted producer facts and
    the call agreement. -/
theorem multi_ruf_schliesst (img : List Byte) (istart : Nat)
    (disp : Int) (out : List Byte) (d : BitVec 32) (rest : List Byte)
    (himg : img[istart]? = some (natByte 232))
    (hpatch : patchRel32 img (istart + 1) disp = some out)
    (hdec : decode (out.drop istart) = some ((⟨.call32 d, 5⟩, rest))) :
    dispSigned d = disp ∧
    5 + rest.length = (out.drop istart).length ∧
    rel32Passt disp = true ∧
    out[istart]? = some (natByte 232) ∧
    (∀ k, k < 4 → out[istart + 1 + k]? = (rel32Bytes disp)[k]?) ∧
    decktAb ⟨.call32 d, 5⟩ ∧
    decode ((out.drop istart).take 5 ++ rest) =
      some ((⟨.call32 d, 5⟩, rest)) := by
  have hfit := patchRel32_passt img (istart + 1) disp out hpatch
  have hpatchAt : patchAt img (istart + 1) (rel32Bytes disp) = some out := by
    unfold patchRel32 at hpatch
    rw [if_pos hfit] at hpatch
    exact hpatch
  have hop_out : out[istart]? = some (natByte 232) := by
    have hfr : ∀ k, k < (rel32Bytes disp).length →
        istart ≠ istart + 1 + k := fun k _ => by omega
    have h :=
      patchAt_rahmen img (istart + 1) (rel32Bytes disp) out hpatchAt istart hfr
    rw [h]
    exact himg
  have hsite : ∀ k, k < 4 → out[istart + 1 + k]? = (rel32Bytes disp)[k]? :=
    fun k hk => patchRel32_stelle img (istart + 1) disp out hpatch k hk
  have htake := fenster_ruf out istart disp hop_out hsite
  obtain ⟨hdisp, heq, hdeckt, hregion⟩ :=
    feld_agreement_ruf out istart disp d rest hfit htake hdec
  exact ⟨hdisp, heq, hfit, hop_out, hsite, hdeckt, hregion⟩

/-- RE-DECODE, conditional jump: a patched conditional operand
    re-decodes to the patched displacement with the patched
    condition; the decoded condition is the site's condition. -/
theorem multi_bedingt_schliesst (img : List Byte) (istart : Nat)
    (c : Bedingung) (disp : Int) (out : List Byte) (d : BitVec 32)
    (rest : List Byte)
    (himg0 : img[istart]? = some (natByte 15))
    (himg1 : img[istart + 1]? = some (natByte (128 + condCode c)))
    (hpatch : patchRel32 img (istart + 2) disp = some out)
    (hdec : decode (out.drop istart) =
      some ((⟨.jumpIf32 c d, 6⟩, rest))) :
    dispSigned d = disp ∧
    6 + rest.length = (out.drop istart).length ∧
    rel32Passt disp = true ∧
    out[istart]? = some (natByte 15) ∧
    out[istart + 1]? = some (natByte (128 + condCode c)) ∧
    (∀ k, k < 4 → out[istart + 2 + k]? = (rel32Bytes disp)[k]?) ∧
    decktAb ⟨.jumpIf32 c d, 6⟩ ∧
    decode ((out.drop istart).take 6 ++ rest) =
      some ((⟨.jumpIf32 c d, 6⟩, rest)) := by
  have hfit := patchRel32_passt img (istart + 2) disp out hpatch
  have hpatchAt : patchAt img (istart + 2) (rel32Bytes disp) = some out := by
    unfold patchRel32 at hpatch
    rw [if_pos hfit] at hpatch
    exact hpatch
  have hop0_out : out[istart]? = some (natByte 15) := by
    have hfr : ∀ k, k < (rel32Bytes disp).length →
        istart ≠ istart + 2 + k := fun k _ => by omega
    have h :=
      patchAt_rahmen img (istart + 2) (rel32Bytes disp) out hpatchAt istart hfr
    rw [h]
    exact himg0
  have hop1_out : out[istart + 1]? =
      some (natByte (128 + condCode c)) := by
    have hfr : ∀ k, k < (rel32Bytes disp).length →
        istart + 1 ≠ istart + 2 + k := fun k _ => by omega
    have h := patchAt_rahmen img (istart + 2) (rel32Bytes disp) out
      hpatchAt (istart + 1) hfr
    rw [h]
    exact himg1
  have hsite : ∀ k, k < 4 → out[istart + 2 + k]? = (rel32Bytes disp)[k]? :=
    fun k hk => patchRel32_stelle img (istart + 2) disp out hpatch k hk
  have htake := fenster_bedingt out istart c disp hop0_out hop1_out hsite
  obtain ⟨hdisp, heq, hdeckt, hregion⟩ :=
    feld_agreement_bedingt out istart c disp d rest hfit htake hdec
  exact ⟨hdisp, heq, hfit, hop0_out, hop1_out, hsite, hdeckt, hregion⟩

/-- RE-DECODE, abs64: a patched eight-byte window reads back to the
    patched value, through the canonical split. An abs64 operand is
    data, never a decoded instruction: no `decode` claim is made
    here (see the refusal `multi_abs64_nicht_code`). -/
theorem multi_abs64_liest (img : List Byte) (off : Nat) (v : Wort)
    (out : List Byte)
    (hpatch : multiPatch img off (.abs64 v) = some out) :
    abs64Wort ((out.drop off).take 8) = some v := by
  have hpatchAt : patchAt img off (abs64Bytes v) = some out := hpatch
  have hsite : ∀ k, k < 8 → out[off + k]? = (abs64Bytes v)[k]? :=
    fun k hk => patchAt_stelle img off (abs64Bytes v) out hpatchAt k
      (by rwa [abs64Bytes_laenge])
  have htake := fenster_abs64 out off v hsite
  rw [htake]
  exact abs64_rundgang v

/-- A successful rel8 patch passed its signed-8 fit check. -/
theorem multiPatch_rel8_passt (img : List Byte) (off : Nat) (d : Int)
    (out : List Byte) (h : multiPatch img off (.rel8 d) = some out) :
    rel8Passt d = true := by
  simp only [multiPatch] at h
  by_cases hc : rel8Passt d = true
  · exact hc
  · rw [if_neg hc] at h
    cases h

/-- RE-DECODE, rel8: a patched short-displacement byte reads back to
    the patched value. A rel8 operand is one byte, never a decoded
    instruction (`decode_nichts_kurzsprung`): no `decode` claim is
    made here. -/
theorem multi_rel8_liest (img : List Byte) (off : Nat) (d : Int)
    (out : List Byte)
    (hpatch : multiPatch img off (.rel8 d) = some out) :
    out[off]? = some (rel8Byte d) ∧ disp8Signed (rel8Byte d) = d := by
  have hfit := multiPatch_rel8_passt img off d out hpatch
  have hfitI := of_decide_eq_true hfit
  simp only [multiPatch] at hpatch
  rw [if_pos hfit] at hpatch
  have hbyte : out[off]? = some (rel8Byte d) := by
    have h0 := patchAt_stelle img off [rel8Byte d] out hpatch 0 (by simp)
    simpa using h0
  exact ⟨hbyte, rel8Byte_rundgang d hfitI.1 hfitI.2⟩

/-! ## 6. n units: concatenation, tiling sections, checked image.

    The linked file is the concatenation in link order; the
    sections tile it without gap or overlap, each at its own
    virtual base, through the ACTUAL `geladen` mapping. -/

/-- Linked file bytes of n units: concatenation in link order. -/
def verknuepfeAlle (us : List LinkEinheit) : List Byte :=
  (us.map LinkEinheit.bytes).flatten

theorem verknuepfeAlle_nil : verknuepfeAlle [] = [] := rfl

theorem verknuepfeAlle_cons (u : LinkEinheit) (us : List LinkEinheit) :
    verknuepfeAlle (u :: us) = u.bytes ++ verknuepfeAlle us := by
  simp [verknuepfeAlle]

theorem verknuepfeAlle_append (us vs : List LinkEinheit) :
    verknuepfeAlle (us ++ vs) =
      verknuepfeAlle us ++ verknuepfeAlle vs := by
  simp [verknuepfeAlle]

theorem verknuepfeAlle_laenge (us : List LinkEinheit) :
    (verknuepfeAlle us).length =
      (us.map (fun u => u.bytes.length)).sum := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    simp only [verknuepfeAlle_cons, List.length_append, ih,
      List.map_cons, List.sum_cons]

/-- Two-unit concatenation is the two-unit link. -/
theorem verknuepfeAlle_zwei (a b : LinkEinheit) :
    verknuepfeAlle [a, b] = verknuepfeDatei a b := by
  simp [verknuepfeAlle, verknuepfeDatei]

/-- One separately lowered unit with its code/data kind: code units
    are executable and never writable, data units writable and never
    executable (W^X by construction, proved in `mAbschnitt_wx`). -/
structure MEinheit where
  bytes : List Byte
  vaddr : Nat
  code : Bool
  deriving DecidableEq, Repr

/-- The section of one unit at file offset `off`. -/
def mAbschnitt (off : Nat) (u : MEinheit) : Abschnitt :=
  { dateiOff := off, dateiLen := u.bytes.length, vaddr := u.vaddr,
    memLen := u.bytes.length, lesbar := true, schreibbar := !u.code,
    ausfuehrbar := u.code, ausr := 1 }

/-- The sections of n units: file offsets tile the concatenation in
    link order, each at its own virtual base. -/
def mAbschnitteAux (off : Nat) : List MEinheit → List Abschnitt
  | [] => []
  | u :: us => mAbschnitt off u :: mAbschnitteAux (off + u.bytes.length) us

/-- The sections of n units from file offset zero. -/
def mAbschnitte (us : List MEinheit) : List Abschnitt :=
  mAbschnitteAux 0 us

/-- The file bytes of n units. -/
def mDatei (us : List MEinheit) : List Byte :=
  (us.map MEinheit.bytes).flatten

/-- The linked image of n units over explicit file bytes (patched or
    not), with the entry vector. `reloks` stays empty: every
    relocation is already applied by `multiPatchAlle`, never
    pending. -/
def mBild (us : List MEinheit) (datei : List Byte)
    (eintrag : Nat) : Bild :=
  { datei := datei
    abschnitte := mAbschnitte us
    reloks := []
    eintraege := [eintrag]
    modus := .fest }

/-- TILING: every section of the n-unit image lies inside the file,
    at or after the running offset -- the sections tile the
    concatenation in order, with no gap and no overlap. -/
theorem mAbschnitteAux_tiling (off : Nat) (us : List MEinheit)
    (s : Abschnitt) (hmem : s ∈ mAbschnitteAux off us) :
    off ≤ s.dateiOff ∧
      s.dateiOff + s.dateiLen ≤ off + (mDatei us).length := by
  induction us generalizing off with
  | nil =>
    simp [mAbschnitteAux] at hmem
  | cons u us ih =>
    simp only [mAbschnitteAux, List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · simp only [mAbschnitt, mDatei, List.map_cons, List.flatten_cons,
        List.length_append]
      constructor <;> omega
    · obtain ⟨h1, h2⟩ := ih (off + u.bytes.length) hmem
      simp only [mDatei, List.map_cons, List.flatten_cons,
        List.length_append] at h2 ⊢
      constructor <;> omega

/-- W^X by construction: no member section is writable and
    executable at once. -/
theorem mAbschnitt_wx (off : Nat) (u : MEinheit) :
    wxOk (mAbschnitt off u) = true := by
  unfold wxOk mAbschnitt
  cases u.code <;> simp

/-- MAPPING: a found virtual address loads the mapped file byte,
    through the ACTUAL `geladen` mapping of the n-unit image. -/
theorem mBild_byte_geladen (us : List MEinheit) (datei : List Byte)
    (eintrag bias va : Nat) (s : Abschnitt)
    (hfind : abteilFinden (mBild us datei eintrag).abschnitte bias va =
      some s)
    (hhi : va < bias + s.vaddr + s.dateiLen) :
    ladenByte (mBild us datei eintrag) bias va =
      dateiByte (mBild us datei eintrag).datei
        (s.dateiOff + (va - (bias + s.vaddr))) :=
  geladenByte_datei _ _ _ _ hfind hhi

/-- W^X: every member section of a well-formed n-unit image is not
    writable-and-executable. -/
theorem mBild_wx (p : Profil) (us : List MEinheit) (datei : List Byte)
    (eintrag : Nat) (s : Abschnitt)
    (hmem : s ∈ (mBild us datei eintrag).abschnitte)
    (hwf : wohlgeformt p (mBild us datei eintrag) = true) :
    wxOk s = true :=
  wohlgeformt_wx p _ s hmem hwf

/-! ## 7. Several operands per closing: the fold and its frame. -/

/-- One closing operand: file offset plus field. -/
abbrev SchliessOp := Nat × MultiFeld

/-- File offset of a closing operand. -/
def opStelle : SchliessOp → Nat := Prod.fst

/-- Width of a closing operand in bytes. -/
def opWeite (op : SchliessOp) : Nat := (multiBytes op.2).length

/-- Apply several relocation operands in list order. Overlapping or
    overrunning sites are refused (`none`), never merged or
    wrapped. -/
def multiPatchAlle : List Byte → List SchliessOp → Option (List Byte)
  | img, [] => some img
  | img, op :: rest =>
    match multiPatch img op.1 op.2 with
    | none => none
    | some mid => multiPatchAlle mid rest

/-- A multi-operand closing keeps the image length. -/
theorem multiPatchAlle_laenge (img : List Byte) (ops : List SchliessOp)
    (out : List Byte) (h : multiPatchAlle img ops = some out) :
    out.length = img.length := by
  induction ops generalizing img out with
  | nil =>
    simp only [multiPatchAlle] at h
    cases h
    rfl
  | cons op rest ih =>
    simp only [multiPatchAlle] at h
    cases h1 : multiPatch img op.1 op.2 with
    | none =>
      rw [h1] at h
      cases h
    | some mid =>
      rw [h1] at h
      have hlen := multiPatch_laenge img op.1 op.2 mid h1
      have hrest := ih mid out h
      omega

/-- FRAME OVER ALL OPERANDS: no relocation changes a byte outside
    its operand -- a byte outside every operand keeps its image
    byte through the whole closing. This is the invariant every
    link closing below carries. -/
theorem multiPatchAlle_rahmen (img : List Byte) (ops : List SchliessOp)
    (out : List Byte) (h : multiPatchAlle img ops = some out)
    (i : Nat)
    (haussen : ∀ op ∈ ops, ∀ k, k < opWeite op → i ≠ opStelle op + k) :
    out[i]? = img[i]? := by
  induction ops generalizing img out with
  | nil =>
    simp only [multiPatchAlle] at h
    cases h
    rfl
  | cons op rest ih =>
    simp only [multiPatchAlle] at h
    cases h1 : multiPatch img op.1 op.2 with
    | none =>
      rw [h1] at h
      cases h
    | some mid =>
      rw [h1] at h
      have hhead : ∀ k, k < (multiBytes op.2).length → i ≠ op.1 + k :=
        fun k hk => haussen op (List.mem_cons.mpr (Or.inl rfl)) k hk
      have hmid : mid[i]? = img[i]? :=
        multiPatch_rahmen img op.1 op.2 mid h1 i hhead
      have hrest : ∀ op' ∈ rest, ∀ k, k < opWeite op' →
          i ≠ opStelle op' + k := by
        intro op' hm k hk
        exact haussen op' (List.mem_cons.mpr (Or.inr hm)) k hk
      have htail : out[i]? = mid[i]? := ih mid out h hrest
      rw [htail, hmid]

/-- The head operand's bytes survive a tail disjoint from its range:
    later operands never clobber an earlier site. -/
theorem multiPatchAlle_kopf_stelle (img : List Byte) (op : SchliessOp)
    (rest : List SchliessOp) (out : List Byte)
    (h : multiPatchAlle img (op :: rest) = some out)
    (hdis : ∀ op' ∈ rest, ∀ k, k < opWeite op → ∀ j, j < opWeite op' →
      opStelle op + k ≠ opStelle op' + j)
    (k : Nat) (hk : k < opWeite op) :
    out[opStelle op + k]? = (multiBytes op.2)[k]? := by
  simp only [multiPatchAlle] at h
  cases h1 : multiPatch img op.1 op.2 with
  | none =>
    rw [h1] at h
    cases h
  | some mid =>
    rw [h1] at h
    have hmid : mid[op.1 + k]? = (multiBytes op.2)[k]? :=
      multiPatch_stelle img op.1 op.2 mid h1 k hk
    have haussen : ∀ op' ∈ rest, ∀ j, j < opWeite op' →
        opStelle op + k ≠ opStelle op' + j :=
      fun op' hm j hj => hdis op' hm k hk j hj
    have htail : out[opStelle op + k]? = mid[opStelle op + k]? :=
      multiPatchAlle_rahmen mid rest out h (opStelle op + k) haussen
    rw [htail]
    exact hmid

/-- Decided pairwise disjointness of closing operands: every later
    operand's byte range is ordered against every earlier one.
    Overlap refuses at link time, never merges. -/
def opsDisjunktB : List SchliessOp → Bool
  | [] => true
  | op :: rest =>
    rest.all (fun op' => decide (disjunktStellen (opStelle op)
      (opWeite op) (opStelle op') (opWeite op'))) &&
    opsDisjunktB rest

/-- Unfold one fold step at a concrete operand. -/
theorem multiPatchAlle_cons (img : List Byte) (off : Nat) (f : MultiFeld)
    (rest : List SchliessOp) :
    multiPatchAlle img ((off, f) :: rest) =
      match multiPatch img off f with
      | none => none
      | some mid => multiPatchAlle mid rest := rfl

/-- The empty closing changes nothing. -/
theorem multiPatchAlle_nil' (img : List Byte) :
    multiPatchAlle img [] = some img := rfl

/-- Soundness: a decided disjoint closing has pairwise disjoint byte
    ranges. Every premise is used: `hne` rules out the diagonal,
    the `all` part orders head against tail, `ih` orders the tail. -/
theorem opsDisjunktB_gilt (ops : List SchliessOp)
    (h : opsDisjunktB ops = true)
    (op₁ : SchliessOp) (hm₁ : op₁ ∈ ops) (op₂ : SchliessOp)
    (hm₂ : op₂ ∈ ops) (hne : op₁ ≠ op₂) :
    disjunktStellen (opStelle op₁) (opWeite op₁) (opStelle op₂)
      (opWeite op₂) := by
  induction ops generalizing op₁ op₂ with
  | nil =>
    simp at hm₁
  | cons hd rest ih =>
    simp only [opsDisjunktB, Bool.and_eq_true] at h
    obtain ⟨hall, hrest⟩ := h
    simp only [List.mem_cons] at hm₁ hm₂
    rcases hm₁ with heq₁ | hm₁
    · rcases hm₂ with heq₂ | hm₂
      · exact absurd (heq₁.trans heq₂.symm) hne
      · have hall2 : decide (disjunktStellen (opStelle hd) (opWeite hd)
            (opStelle op₂) (opWeite op₂)) = true :=
          List.all_eq_true.mp hall op₂ hm₂
        rw [heq₁]
        exact of_decide_eq_true hall2
    · rcases hm₂ with heq₂ | hm₂
      · have hall1 : decide (disjunktStellen (opStelle hd) (opWeite hd)
            (opStelle op₁) (opWeite op₁)) = true :=
          List.all_eq_true.mp hall op₁ hm₁
        rw [heq₂]
        rcases of_decide_eq_true hall1 with hle | hle
        · exact Or.inr hle
        · exact Or.inl hle
      · exact ih hrest op₁ hm₁ op₂ hm₂ hne

/-! ## 8. The multi-operand link closing. -/

/-- **MULTI-OPERAND LINK CORRECTNESS.** For n separately lowered
    units linked in order, five applied operands (jump, call,
    conditional, abs64 data, rel8 short) with pairwise-separated
    byte ranges, their re-decodes and the checked linked image over
    the PATCHED bytes: every re-decoded displacement is the patched
    value with the patched condition, every taken window re-decodes,
    the data and short bytes read back, the sections are W^X, the
    executed mapping loads the patched file bytes, every site lies
    in range, and no byte outside the operands changed. Every
    premise is load-bearing (see the proof). -/
theorem mehrere_korrekt
    (us : List MEinheit) (datei out : List Byte) (eintrag : Nat)
    (pj pc pd pa pr ij ic id : Nat)
    (dj dc dd : Int) (v : Wort) (dr : Int) (c : Bedingung)
    (ej ec ed : BitVec 32) (restj restc restd : List Byte)
    (s : Abschnitt) (va i : Nat)
    (halle : multiPatchAlle datei [(pj, .rel32 dj), (pc, .rel32 dc),
      (pd, .rel32 dd), (pa, .abs64 v), (pr, .rel8 dr)] = some out)
    (hdisj : ∀ op' ∈ [(pc, .rel32 dc), (pd, .rel32 dd), (pa, .abs64 v),
      (pr, .rel8 dr)], ∀ k, k < opWeite (pj, .rel32 dj) →
      ∀ j, j < opWeite op' →
      opStelle (pj, .rel32 dj) + k ≠ opStelle op' + j)
    (hdisc : ∀ op' ∈ [(pd, .rel32 dd), (pa, .abs64 v), (pr, .rel8 dr)],
      ∀ k, k < opWeite (pc, .rel32 dc) →
      ∀ j, j < opWeite op' →
      opStelle (pc, .rel32 dc) + k ≠ opStelle op' + j)
    (hdisd : ∀ op' ∈ [(pa, .abs64 v), (pr, .rel8 dr)],
      ∀ k, k < opWeite (pd, .rel32 dd) →
      ∀ j, j < opWeite op' →
      opStelle (pd, .rel32 dd) + k ≠ opStelle op' + j)
    (hdisa : ∀ op' ∈ [(pr, .rel8 dr)],
      ∀ k, k < opWeite (pa, .abs64 v) →
      ∀ j, j < opWeite op' →
      opStelle (pa, .abs64 v) + k ≠ opStelle op' + j)
    (hrahmen : ∀ p ∈ [ij, ic, id, id + 1],
      ∀ op ∈ [(pj, .rel32 dj), (pc, .rel32 dc), (pd, .rel32 dd),
        (pa, .abs64 v), (pr, .rel8 dr)],
      ∀ k, k < opWeite op → p ≠ opStelle op + k)
    (hj0 : datei[ij]? = some (natByte 233))
    (hc0 : datei[ic]? = some (natByte 232))
    (hd0 : datei[id]? = some (natByte 15))
    (hd1 : datei[id + 1]? = some (natByte (128 + condCode c)))
    (hpj : pj = ij + 1) (hpc : pc = ic + 1) (hpd : pd = id + 2)
    (hdecj : decode (out.drop ij) = some ((⟨.jump32 ej, 5⟩, restj)))
    (hdecc : decode (out.drop ic) = some ((⟨.call32 ec, 5⟩, restc)))
    (hdecd : decode (out.drop id) =
      some ((⟨.jumpIf32 c ed, 6⟩, restd)))
    (hwf : wohlgeformt .p48 (mBild us out eintrag) = true)
    (hmem : s ∈ (mBild us out eintrag).abschnitte)
    (hfind : abteilFinden (mBild us out eintrag).abschnitte 0 va =
      some s)
    (hhi : va < 0 + s.vaddr + s.dateiLen)
    (haussen : ∀ op ∈ [(pj, .rel32 dj), (pc, .rel32 dc),
      (pd, .rel32 dd), (pa, .abs64 v), (pr, .rel8 dr)],
      ∀ k, k < opWeite op → i ≠ opStelle op + k) :
    dispSigned ej = dj ∧
    dispSigned ec = dc ∧
    dispSigned ed = dd ∧
    decktAb ⟨.jump32 ej, 5⟩ ∧
    decktAb ⟨.call32 ec, 5⟩ ∧
    decktAb ⟨.jumpIf32 c ed, 6⟩ ∧
    decode ((out.drop ij).take 5 ++ restj) =
      some ((⟨.jump32 ej, 5⟩, restj)) ∧
    decode ((out.drop ic).take 5 ++ restc) =
      some ((⟨.call32 ec, 5⟩, restc)) ∧
    decode ((out.drop id).take 6 ++ restd) =
      some ((⟨.jumpIf32 c ed, 6⟩, restd)) ∧
    abs64Wort ((out.drop pa).take 8) = some v ∧
    out[pr]? = some (rel8Byte dr) ∧
    disp8Signed (rel8Byte dr) = dr ∧
    wxOk s = true ∧
    ladenByte (mBild us out eintrag) 0 va =
      dateiByte out (s.dateiOff + (va - (0 + s.vaddr))) ∧
    pj + 4 ≤ datei.length ∧
    pc + 4 ≤ datei.length ∧
    pd + 4 ≤ datei.length ∧
    out[i]? = datei[i]? := by
  have kopfj : ∀ k, k < opWeite (pj, .rel32 dj) →
      out[opStelle (pj, .rel32 dj) + k]? = (multiBytes (.rel32 dj))[k]? :=
    fun k hk => multiPatchAlle_kopf_stelle datei (pj, .rel32 dj)
      [(pc, .rel32 dc), (pd, .rel32 dd), (pa, .abs64 v), (pr, .rel8 dr)]
      out halle hdisj k hk
  have hopj_frame : out[ij]? = datei[ij]? :=
    multiPatchAlle_rahmen datei _ out halle ij (fun op hm k hk =>
      hrahmen ij (List.mem_cons.mpr (Or.inl rfl)) op hm k hk)
  have hopc_frame : out[ic]? = datei[ic]? :=
    multiPatchAlle_rahmen datei _ out halle ic (fun op hm k hk =>
      hrahmen ic (by simp : ic ∈ [ij, ic, id, id + 1]) op hm k hk)
  have hopd0_frame : out[id]? = datei[id]? :=
    multiPatchAlle_rahmen datei _ out halle id (fun op hm k hk =>
      hrahmen id (by simp : id ∈ [ij, ic, id, id + 1]) op hm k hk)
  have hopd1_frame : out[id + 1]? = datei[id + 1]? :=
    multiPatchAlle_rahmen datei _ out halle (id + 1) (fun op hm k hk =>
      hrahmen (id + 1) (by simp : id + 1 ∈ [ij, ic, id, id + 1])
        op hm k hk)
  have hframe : out[i]? = datei[i]? :=
    multiPatchAlle_rahmen datei _ out halle i haussen
  rw [multiPatchAlle_cons] at halle
  cases h1 : multiPatch datei pj (.rel32 dj) with
  | none =>
    simp only [h1] at halle
    cases halle
  | some mid1 =>
    simp only [h1] at halle
    have kopfc : ∀ k, k < opWeite (pc, .rel32 dc) →
        out[opStelle (pc, .rel32 dc) + k]? =
          (multiBytes (.rel32 dc))[k]? :=
      fun k hk => multiPatchAlle_kopf_stelle mid1 (pc, .rel32 dc)
        [(pd, .rel32 dd), (pa, .abs64 v), (pr, .rel8 dr)]
        out halle hdisc k hk
    rw [multiPatchAlle_cons] at halle
    cases h2 : multiPatch mid1 pc (.rel32 dc) with
    | none =>
      simp only [h2] at halle
      cases halle
    | some mid2 =>
      simp only [h2] at halle
      have kopfd : ∀ k, k < opWeite (pd, .rel32 dd) →
          out[opStelle (pd, .rel32 dd) + k]? =
            (multiBytes (.rel32 dd))[k]? :=
        fun k hk => multiPatchAlle_kopf_stelle mid2 (pd, .rel32 dd)
          [(pa, .abs64 v), (pr, .rel8 dr)] out halle hdisd k hk
      rw [multiPatchAlle_cons] at halle
      cases h3 : multiPatch mid2 pd (.rel32 dd) with
      | none =>
        simp only [h3] at halle
        cases halle
      | some mid3 =>
        simp only [h3] at halle
        have kopfa : ∀ k, k < opWeite (pa, .abs64 v) →
            out[opStelle (pa, .abs64 v) + k]? =
              (multiBytes (.abs64 v))[k]? :=
          fun k hk => multiPatchAlle_kopf_stelle mid3 (pa, .abs64 v)
            [(pr, .rel8 dr)] out halle hdisa k hk
        rw [multiPatchAlle_cons] at halle
        cases h4 : multiPatch mid3 pa (.abs64 v) with
        | none =>
          simp only [h4] at halle
          cases halle
        | some mid4 =>
          simp only [h4] at halle
          have kopfr : ∀ k, k < opWeite (pr, .rel8 dr) →
              out[opStelle (pr, .rel8 dr) + k]? =
                (multiBytes (.rel8 dr))[k]? :=
            fun k hk => multiPatchAlle_kopf_stelle mid4 (pr, .rel8 dr)
              [] out halle
              (fun op' hm _ _ _ _ => by simp at hm) k hk
          rw [multiPatchAlle_cons] at halle
          cases h5 : multiPatch mid4 pr (.rel8 dr) with
          | none =>
            simp only [h5] at halle
            cases halle
          | some mid5 =>
            simp only [h5] at halle
            rw [multiPatchAlle_nil'] at halle
            cases halle
            have h1r : patchRel32 datei pj dj = some mid1 := h1
            have h2r : patchRel32 mid1 pc dc = some mid2 := h2
            have h3r : patchRel32 mid2 pd dd = some mid3 := h3
            have hfitj : rel32Passt dj = true :=
              patchRel32_passt datei pj dj mid1 h1r
            have hfitc : rel32Passt dc = true :=
              patchRel32_passt mid1 pc dc mid2 h2r
            have hfitd : rel32Passt dd = true :=
              patchRel32_passt mid2 pd dd mid3 h3r
            have hfitr : rel8Passt dr = true :=
              multiPatch_rel8_passt mid4 pr dr out h5
            have hfitrI := of_decide_eq_true hfitr
            have hlen1 : mid1.length = datei.length :=
              multiPatch_laenge datei pj (.rel32 dj) mid1 h1
            have hlen2 : mid2.length = mid1.length :=
              multiPatch_laenge mid1 pc (.rel32 dc) mid2 h2
            have hrangej : pj + 4 ≤ datei.length :=
              multiPatch_bereich datei pj (.rel32 dj) mid1 h1
            have hrangec : pc + 4 ≤ datei.length := by
              have hr := multiPatch_bereich mid1 pc (.rel32 dc) mid2 h2
              simp only [multiBytes_rel32_laenge] at hr
              omega
            have hranged : pd + 4 ≤ datei.length := by
              have hr := multiPatch_bereich mid2 pd (.rel32 dd) mid3 h3
              simp only [multiBytes_rel32_laenge] at hr
              omega
            have hopj : out[ij]? = some (natByte 233) := by
              rw [hopj_frame]
              exact hj0
            have hopc : out[ic]? = some (natByte 232) := by
              rw [hopc_frame]
              exact hc0
            have hopd0 : out[id]? = some (natByte 15) := by
              rw [hopd0_frame]
              exact hd0
            have hopd1 : out[id + 1]? =
                some (natByte (128 + condCode c)) := by
              rw [hopd1_frame]
              exact hd1
            have hfieldj : ∀ k, k < 4 →
                out[ij + 1 + k]? = (rel32Bytes dj)[k]? := by
              intro k hk
              have hkop2 : out[pj + k]? = (rel32Bytes dj)[k]? :=
                kopfj k hk
              rw [hpj] at hkop2
              exact hkop2
            have hfieldc : ∀ k, k < 4 →
                out[ic + 1 + k]? = (rel32Bytes dc)[k]? := by
              intro k hk
              have hkop2 : out[pc + k]? = (rel32Bytes dc)[k]? :=
                kopfc k hk
              rw [hpc] at hkop2
              exact hkop2
            have hfieldd : ∀ k, k < 4 →
                out[id + 2 + k]? = (rel32Bytes dd)[k]? := by
              intro k hk
              have hkop2 : out[pd + k]? = (rel32Bytes dd)[k]? :=
                kopfd k hk
              rw [hpd] at hkop2
              exact hkop2
            have hfielda : ∀ k, k < 8 →
                out[pa + k]? = (abs64Bytes v)[k]? := by
              intro k hk
              have hkop2 : out[pa + k]? = (abs64Bytes v)[k]? :=
                kopfa k hk
              exact hkop2
            have hw1 : opWeite (pr, .rel8 dr) = 1 := rfl
            have hkopr0 : out[pr + 0]? = (multiBytes (.rel8 dr))[0]? :=
              kopfr 0 (by rw [hw1]; decide)
            have hbyter : out[pr]? = some (rel8Byte dr) := by
              simpa [multiBytes] using hkopr0
            have htakej := fenster_sprung out ij dj hopj hfieldj
            have htakec := fenster_ruf out ic dc hopc hfieldc
            have htaked :=
              fenster_bedingt out id c dd hopd0 hopd1 hfieldd
            have htakea := fenster_abs64 out pa v hfielda
            obtain ⟨hagj, hlenj, hdecktj, hregj⟩ :=
              feld_agreement_sprung out ij dj ej restj hfitj htakej hdecj
            obtain ⟨hagc, hlenc, hdecktc, hregc⟩ :=
              feld_agreement_ruf out ic dc ec restc hfitc htakec hdecc
            obtain ⟨hagd, hlend, hdecktd, hregd⟩ :=
              feld_agreement_bedingt out id c dd ed restd hfitd htaked hdecd
            have habs : abs64Wort ((out.drop pa).take 8) = some v := by
              rw [htakea]
              exact abs64_rundgang v
            refine ⟨hagj, hagc, hagd, hdecktj, hdecktc, hdecktd,
              hregj, hregc, hregd, habs, hbyter,
              rel8Byte_rundgang dr hfitrI.1 hfitrI.2,
              mBild_wx .p48 us out eintrag s hmem hwf,
              mBild_byte_geladen us out eintrag 0 va s hfind hhi,
              hrangej, hrangec, hranged, hframe⟩

/-! ## 9. Joint witness: four units, five operands, one closing.

    Unit A is a five-byte jump, unit B a five-byte call, unit C
    nine data bytes (abs64 value plus rel8 byte), unit D a six-byte
    conditional jump. The five operands apply at disjoint sites;
    every window re-decodes or reads back through the closing. -/

/-- Witness unit A: a five-byte jump with zero displacement. -/
def zeugenMultiA : MEinheit :=
  { bytes := [natByte 233, natByte 0, natByte 0, natByte 0, natByte 0]
    vaddr := 0x1000, code := true }

/-- Witness unit B: a five-byte call with zero displacement. -/
def zeugenMultiB : MEinheit :=
  { bytes := [natByte 232, natByte 0, natByte 0, natByte 0, natByte 0]
    vaddr := 0x2000, code := true }

/-- Witness unit C: nine data bytes (abs64 site plus rel8 site). -/
def zeugenMultiC : MEinheit :=
  { bytes := [natByte 0, natByte 0, natByte 0, natByte 0, natByte 0,
      natByte 0, natByte 0, natByte 0, natByte 0]
    vaddr := 0x3000, code := false }

/-- Witness unit D: a six-byte conditional jump (`e`) with zero
    displacement. -/
def zeugenMultiD : MEinheit :=
  { bytes := [natByte 15, natByte 132, natByte 0, natByte 0, natByte 0,
      natByte 0]
    vaddr := 0x4000, code := true }

/-- Witness units in link order. -/
def zeugenMultiUnits : List MEinheit :=
  [zeugenMultiA, zeugenMultiB, zeugenMultiC, zeugenMultiD]

/-- Witness linked file: the four units' bytes in order. -/
def zeugenMultiDatei : List Byte :=
  [natByte 233, natByte 0, natByte 0, natByte 0, natByte 0,
    natByte 232, natByte 0, natByte 0, natByte 0, natByte 0,
    natByte 0, natByte 0, natByte 0, natByte 0, natByte 0,
    natByte 0, natByte 0, natByte 0, natByte 0,
    natByte 15, natByte 132, natByte 0, natByte 0, natByte 0,
    natByte 0]

/-- Witness patched file: jump `+16`, call `-5`, abs64 value,
    rel8 `+16`, conditional `+16`. -/
def zeugenMultiOut : List Byte :=
  [natByte 233, natByte 16, natByte 0, natByte 0, natByte 0,
    natByte 232, natByte 251, natByte 255, natByte 255, natByte 255,
    natByte 8, natByte 7, natByte 6, natByte 5, natByte 4,
    natByte 3, natByte 2, natByte 1, natByte 16,
    natByte 15, natByte 132, natByte 16, natByte 0, natByte 0,
    natByte 0]

/-- Witness jump field: `+16`. -/
def zeugenMultiF16 : BitVec 32 := BitVec.ofNat 32 16

/-- Witness call field: `-5`. -/
def zeugenMultiFM5 : BitVec 32 := BitVec.ofNat 32 4294967291

/-- Witness abs64 value. -/
def zeugenMultiV : Wort := 0x0102030405060708

/-- The linked file is the units' bytes in order. -/
theorem zeugenMulti_datei : mDatei zeugenMultiUnits = zeugenMultiDatei := by
  decide

/-- All five operands apply: the patched bytes at every site. -/
theorem zeugenMulti_patch :
    multiPatchAlle zeugenMultiDatei
      [(1, .rel32 16), (6, .rel32 (-5)), (21, .rel32 16),
        (10, .abs64 zeugenMultiV), (18, .rel8 16)] =
      some zeugenMultiOut := by
  decide

/-- The opcode bytes survive in the unpatched file. -/
theorem zeugenMulti_opcodes :
    zeugenMultiDatei[0]? = some (natByte 233) ∧
    zeugenMultiDatei[5]? = some (natByte 232) ∧
    zeugenMultiDatei[19]? = some (natByte 15) ∧
    zeugenMultiDatei[20]? = some (natByte (128 + condCode .e)) := by
  decide

/-- The patched jump window re-decodes to `jump32 +16`. -/
theorem zeugenMulti_dek_sprung :
    decode (zeugenMultiOut.drop 0) =
      some ((⟨.jump32 zeugenMultiF16, 5⟩, zeugenMultiOut.drop 5)) := by
  decide

/-- The patched call window re-decodes to `call32 -5`. -/
theorem zeugenMulti_dek_ruf :
    decode (zeugenMultiOut.drop 5) =
      some ((⟨.call32 zeugenMultiFM5, 5⟩, zeugenMultiOut.drop 10)) := by
  decide

/-- The patched conditional window re-decodes to `jumpIf32 e +16`. -/
theorem zeugenMulti_dek_bedingt :
    decode (zeugenMultiOut.drop 19) =
      some ((⟨.jumpIf32 .e zeugenMultiF16, 6⟩, [])) := by
  decide

/-- The displacement fields carry the site displacements. -/
theorem zeugenMulti_felder :
    dispSigned zeugenMultiF16 = 16 ∧
    dispSigned zeugenMultiFM5 = -5 := by
  decide

/-- The checked linked image over the PATCHED bytes is well-formed. -/
theorem zeugenMulti_bild_wohlgeformt : wohlgeformt .p48
    (mBild zeugenMultiUnits zeugenMultiOut 0x1000) = true := by
  decide

/-- The linked image's decode coverage holds (all code units decode,
    the data unit is not decoded). -/
theorem zeugenMulti_deckung : bildDeckung
    (mBild zeugenMultiUnits zeugenMultiOut 0x1000) = true := by
  decide

/-- Unit A's section is found at its linked virtual address. -/
theorem zeugenMulti_find : abteilFinden
    (mBild zeugenMultiUnits zeugenMultiOut 0x1000).abschnitte 0 0x1000 =
    some (mAbschnitt 0 zeugenMultiA) := by
  decide

/-- The witness address lies in the file-backed part of A's section. -/
theorem zeugenMulti_innen : 0x1000 <
    0 + (mAbschnitt 0 zeugenMultiA).vaddr +
      (mAbschnitt 0 zeugenMultiA).dateiLen := by
  decide

/-- Unit A's section is a member of the linked image. -/
theorem zeugenMulti_mem : mAbschnitt 0 zeugenMultiA ∈
    (mBild zeugenMultiUnits zeugenMultiOut 0x1000).abschnitte := by
  decide

/-- The five witness operand ranges are pairwise separated (jump
    against its tail). -/
theorem zeugenMulti_hdisj :
    ∀ op' ∈ [(6, .rel32 (-5 : Int)), (21, .rel32 (16 : Int)),
      (10, .abs64 zeugenMultiV), (18, .rel8 (16 : Int))],
      ∀ k, k < opWeite (1, .rel32 (16 : Int)) →
      ∀ j, j < opWeite op' →
      opStelle (1, .rel32 (16 : Int)) + k ≠ opStelle op' + j := by
  decide

/-- The five witness operand ranges are pairwise separated (call
    against its tail). -/
theorem zeugenMulti_hdisc :
    ∀ op' ∈ [(21, .rel32 (16 : Int)), (10, .abs64 zeugenMultiV),
      (18, .rel8 (16 : Int))],
      ∀ k, k < opWeite (6, .rel32 (-5 : Int)) →
      ∀ j, j < opWeite op' →
      opStelle (6, .rel32 (-5 : Int)) + k ≠ opStelle op' + j := by
  decide

/-- The five witness operand ranges are pairwise separated
    (conditional against its tail). -/
theorem zeugenMulti_hdisd :
    ∀ op' ∈ [(10, .abs64 zeugenMultiV), (18, .rel8 (16 : Int))],
      ∀ k, k < opWeite (21, .rel32 (16 : Int)) →
      ∀ j, j < opWeite op' →
      opStelle (21, .rel32 (16 : Int)) + k ≠ opStelle op' + j := by
  decide

/-- The five witness operand ranges are pairwise separated (abs64
    against its tail). -/
theorem zeugenMulti_hdisa :
    ∀ op' ∈ [(18, .rel8 (16 : Int))],
      ∀ k, k < opWeite (10, .abs64 zeugenMultiV) →
      ∀ j, j < opWeite op' →
      opStelle (10, .abs64 zeugenMultiV) + k ≠ opStelle op' + j := by
  decide

/-- The decided check agrees: the witness closing is disjoint. -/
theorem zeugenMulti_disjunkt :
    opsDisjunktB [(1, .rel32 (16 : Int)), (6, .rel32 (-5 : Int)),
      (21, .rel32 (16 : Int)), (10, .abs64 zeugenMultiV),
      (18, .rel8 (16 : Int))] = true := by
  decide

/-- Every opcode byte lies outside every witness operand. -/
theorem zeugenMulti_hrahmen :
    ∀ p ∈ [0, 5, 19, 20],
      ∀ op ∈ [(1, .rel32 (16 : Int)), (6, .rel32 (-5 : Int)),
        (21, .rel32 (16 : Int)), (10, .abs64 zeugenMultiV),
        (18, .rel8 (16 : Int))],
      ∀ k, k < opWeite op → p ≠ opStelle op + k := by
  decide

/-- Byte 0 (the jump opcode) lies outside every witness operand. -/
theorem zeugenMulti_haussen :
    ∀ op ∈ [(1, .rel32 (16 : Int)), (6, .rel32 (-5 : Int)),
      (21, .rel32 (16 : Int)), (10, .abs64 zeugenMultiV),
      (18, .rel8 (16 : Int))],
      ∀ k, k < opWeite op → 0 ≠ opStelle op + k := by
  decide

/-! ## 10. Planted refusals: overlap, overrun, ranges, symbol, W^X,
    forged opcode, non-site shapes. Unsupported shapes are REFUSED,
    never guessed. -/

/-- OVERLAP REFUSAL: the decided disjointness check refuses
    overlapping sites, never merges them. -/
theorem multiUeberlapp_verweigert :
    opsDisjunktB [(1, .rel32 (16 : Int)), (2, .rel32 16)] = false := by
  decide

/-- OVERRUN REFUSAL: a four-byte operand two bytes before the end of
    a three-byte image is refused, never wrapped. -/
theorem multiUeberlauf_verweigert :
    multiPatchAlle [natByte 233, natByte 0, natByte 0]
      [(2, .rel32 (16 : Int))] = none := by
  decide

/-- RANGE REFUSAL (rel32): an out-of-range displacement patches
    nothing. -/
theorem multiAussen32_verweigert :
    multiPatch zeugenMultiDatei 1 (.rel32 2147483648) = none := by
  decide

/-- RANGE REFUSAL (rel8): a short displacement past `+127` patches
    nothing. -/
theorem multiAussen8_verweigert :
    multiPatch zeugenMultiDatei 18 (.rel8 128) = none := by
  decide

/-- SYMBOL REFUSAL: an unlisted relocation id resolves nothing. -/
theorem multiSymbol_verweigert :
    loeseSymbol [(0, 0x1000)] 7 = none := by
  decide

/-- FORGED-OPCODE REFUSAL: a non-canonical head byte refuses
    re-decode. -/
theorem multiOpcode_falsch_verweigert :
    decode ([natByte 6] ++ rel32Bytes 16) = none := by
  decide

/-- NON-JUMP/CALL/CONDITIONAL SITE: a `ret` window decodes to `ret`,
    never to a relocation site -- other instructions are refused
    as sites, never guessed into one. -/
theorem multiKeinSprung_verweigert :
    decode [natByte 195, natByte 16, natByte 0, natByte 0, natByte 0] =
      some ((⟨.ret, 1⟩,
        [natByte 16, natByte 0, natByte 0, natByte 0])) := by
  decide

/-- SHORT FORM NEVER DECODES: a rel8 operand has no decoder row, so
    short re-decode is byte read-back only (`multi_rel8_liest`). -/
theorem multiRel8_nicht_dekodiert :
    decode [natByte 235, natByte 16] = none := by
  decide

/-! ## 11. Joint inhabitation: premises jointly held, run reached. -/

/-- JOINT WITNESS for `mehrere_korrekt`: all premises instantiated
    jointly on the non-degenerate four-unit link (jump unit, call
    unit, data unit carrying the abs64 value and the rel8 byte,
    conditional-jump unit), the closing's conclusions derived
    through it, a reached memory-changing run through actual bytes
    (`ruf_schritt_zeuge`: return address stored, byte observably
    changed), and the planted refusals. -/
theorem mehrere_korrekt_zeuge :
    ∃ (us : List MEinheit) (datei out : List Byte) (eintrag : Nat)
      (pj pc pd pa pr ij ic id : Nat)
      (dj dc dd : Int) (v : Wort) (dr : Int) (c : Bedingung)
      (ej ec ed : BitVec 32) (restj restc restd : List Byte)
      (s : Abschnitt) (va i : Nat),
      multiPatchAlle datei [(pj, .rel32 dj), (pc, .rel32 dc),
        (pd, .rel32 dd), (pa, .abs64 v), (pr, .rel8 dr)] = some out ∧
      (∀ op' ∈ [(pc, .rel32 dc), (pd, .rel32 dd), (pa, .abs64 v),
        (pr, .rel8 dr)], ∀ k, k < opWeite (pj, .rel32 dj) →
        ∀ j, j < opWeite op' →
        opStelle (pj, .rel32 dj) + k ≠ opStelle op' + j) ∧
      (∀ op' ∈ [(pd, .rel32 dd), (pa, .abs64 v), (pr, .rel8 dr)],
        ∀ k, k < opWeite (pc, .rel32 dc) →
        ∀ j, j < opWeite op' →
        opStelle (pc, .rel32 dc) + k ≠ opStelle op' + j) ∧
      (∀ op' ∈ [(pa, .abs64 v), (pr, .rel8 dr)],
        ∀ k, k < opWeite (pd, .rel32 dd) →
        ∀ j, j < opWeite op' →
        opStelle (pd, .rel32 dd) + k ≠ opStelle op' + j) ∧
      (∀ op' ∈ [(pr, .rel8 dr)],
        ∀ k, k < opWeite (pa, .abs64 v) →
        ∀ j, j < opWeite op' →
        opStelle (pa, .abs64 v) + k ≠ opStelle op' + j) ∧
      datei[ij]? = some (natByte 233) ∧
      datei[ic]? = some (natByte 232) ∧
      datei[id]? = some (natByte 15) ∧
      datei[id + 1]? = some (natByte (128 + condCode c)) ∧
      pj = ij + 1 ∧ pc = ic + 1 ∧ pd = id + 2 ∧
      decode (out.drop ij) = some ((⟨.jump32 ej, 5⟩, restj)) ∧
      decode (out.drop ic) = some ((⟨.call32 ec, 5⟩, restc)) ∧
      decode (out.drop id) = some ((⟨.jumpIf32 c ed, 6⟩, restd)) ∧
      wohlgeformt .p48 (mBild us out eintrag) = true ∧
      s ∈ (mBild us out eintrag).abschnitte ∧
      abteilFinden (mBild us out eintrag).abschnitte 0 va = some s ∧
      va < 0 + s.vaddr + s.dateiLen ∧
      (∀ op ∈ [(pj, .rel32 dj), (pc, .rel32 dc),
        (pd, .rel32 dd), (pa, .abs64 v), (pr, .rel8 dr)],
        ∀ k, k < opWeite op → i ≠ opStelle op + k) ∧
      dispSigned ej = dj ∧
      dispSigned ec = dc ∧
      dispSigned ed = dd ∧
      decktAb ⟨.jump32 ej, 5⟩ ∧
      decktAb ⟨.call32 ec, 5⟩ ∧
      decktAb ⟨.jumpIf32 c ed, 6⟩ ∧
      decode ((out.drop ij).take 5 ++ restj) =
        some ((⟨.jump32 ej, 5⟩, restj)) ∧
      decode ((out.drop ic).take 5 ++ restc) =
        some ((⟨.call32 ec, 5⟩, restc)) ∧
      decode ((out.drop id).take 6 ++ restd) =
        some ((⟨.jumpIf32 c ed, 6⟩, restd)) ∧
      abs64Wort ((out.drop pa).take 8) = some v ∧
      out[pr]? = some (rel8Byte dr) ∧
      disp8Signed (rel8Byte dr) = dr ∧
      wxOk s = true ∧
      ladenByte (mBild us out eintrag) 0 va =
        dateiByte out (s.dateiOff + (va - (0 + s.vaddr))) ∧
      pj + 4 ≤ datei.length ∧
      pc + 4 ≤ datei.length ∧
      pd + 4 ≤ datei.length ∧
      out[i]? = datei[i]? ∧
      (∃ m : Speicher, byteschritt zustandRuf =
        .weiter (schrittCall zustandRuf Register.rsp m
          (zustandRuf.register Register.rsp - BitVec.ofNat 64 8)
          (BitVec.ofNat 64 0x1015)) ∧
        read64 m (BitVec.ofNat 64 0x1FF8) =
          some (BitVec.ofNat 64 0x1005) ∧
        m.bytes (BitVec.ofNat 64 0x1FF8) ≠
          zustandRuf.speicher.bytes (BitVec.ofNat 64 0x1FF8)) ∧
      multiPatchAlle [natByte 233, natByte 0, natByte 0]
        [(2, .rel32 (16 : Int))] = none ∧
      multiPatch zeugenMultiDatei 1 (.rel32 2147483648) = none ∧
      multiPatch zeugenMultiDatei 18 (.rel8 128) = none ∧
      loeseSymbol [(0, 0x1000)] 7 = none ∧
      wohlgeformt .p48 wxVerletzt = false ∧
      decode ([natByte 6] ++ rel32Bytes 16) = none := by
  have hconn := mehrere_korrekt zeugenMultiUnits zeugenMultiDatei
    zeugenMultiOut 0x1000 1 6 21 10 18 0 5 19
    16 (-5) 16 zeugenMultiV 16 .e
    zeugenMultiF16 zeugenMultiFM5 zeugenMultiF16
    (zeugenMultiOut.drop 5) (zeugenMultiOut.drop 10) []
    (mAbschnitt 0 zeugenMultiA) 0x1000 0
    zeugenMulti_patch zeugenMulti_hdisj zeugenMulti_hdisc
    zeugenMulti_hdisd zeugenMulti_hdisa zeugenMulti_hrahmen
    zeugenMulti_opcodes.1 zeugenMulti_opcodes.2.1
    zeugenMulti_opcodes.2.2.1 zeugenMulti_opcodes.2.2.2
    rfl rfl rfl
    zeugenMulti_dek_sprung zeugenMulti_dek_ruf zeugenMulti_dek_bedingt
    zeugenMulti_bild_wohlgeformt zeugenMulti_mem zeugenMulti_find
    zeugenMulti_innen zeugenMulti_haussen
  obtain ⟨hagj, hagc, hagd, hdecktj, hdecktc, hdecktd,
    hregj, hregc, hregd, habs, hbyter, hrund, hwx, hmap,
    hrangej, hrangec, hranged, hframe⟩ := hconn
  exact ⟨zeugenMultiUnits, zeugenMultiDatei, zeugenMultiOut, 0x1000,
    1, 6, 21, 10, 18, 0, 5, 19,
    16, (-5), 16, zeugenMultiV, 16, .e,
    zeugenMultiF16, zeugenMultiFM5, zeugenMultiF16,
    (zeugenMultiOut.drop 5), (zeugenMultiOut.drop 10), [],
    (mAbschnitt 0 zeugenMultiA), 0x1000, 0,
    zeugenMulti_patch, zeugenMulti_hdisj, zeugenMulti_hdisc,
    zeugenMulti_hdisd, zeugenMulti_hdisa,
    zeugenMulti_opcodes.1, zeugenMulti_opcodes.2.1,
    zeugenMulti_opcodes.2.2.1, zeugenMulti_opcodes.2.2.2,
    rfl, rfl, rfl,
    zeugenMulti_dek_sprung, zeugenMulti_dek_ruf, zeugenMulti_dek_bedingt,
    zeugenMulti_bild_wohlgeformt, zeugenMulti_mem, zeugenMulti_find,
    zeugenMulti_innen, zeugenMulti_haussen,
    hagj, hagc, hagd, hdecktj, hdecktc, hdecktd,
    hregj, hregc, hregd, habs, hbyter, hrund, hwx, hmap,
    hrangej, hrangec, hranged, hframe,
    ruf_schritt_zeuge, multiUeberlauf_verweigert,
    multiAussen32_verweigert, multiAussen8_verweigert,
    multiSymbol_verweigert, verknuepft_wx_verweigert,
    multiOpcode_falsch_verweigert⟩

/- CUTS:
   - Proved here: one-operand application for three kinds
     (`multiPatch_bereich`/`_stelle`/`_rahmen`/`_laenge`, rel32/abs64
     by reuse of the two-unit `linkPatch_*` facts, rel8 directly
     through the accepted `patchAt_*` producer facts); the rel8
     byte round-trip (`rel8Byte_rundgang`); field agreement for
     jump, call and conditional (`feld_agreement_sprung`/`_ruf`/
     `_bedingt`: re-decoded displacement equals the patched value,
     the conditional keeps the patched condition, through the
     accepted byte bridge and decoder determinism); patched-window
     take equations (`fenster_*`); single-patch re-decode legs
     (`multi_ruf_schliesst`, `multi_bedingt_schliesst`,
     `multi_abs64_liest`, `multi_rel8_liest`; the jump leg is the
     reused `verknuepft_rel32_schliesst`); n-unit concatenation
     (`verknuepfeAlle_*`) with tiling sections (`mAbschnitteAux_tiling`)
     and the checked n-unit image (`mBild_*`: W^X, executed
     mapping); the multi-operand fold (`multiPatchAlle_*`: length,
     the frame invariant -- no relocation changes a byte outside
     its operand -- head-site survival, disjointness soundness);
     the five-operand closing (`mehrere_korrekt`); planted
     refusals for overlap, overrun, out-of-range rel32/rel8,
     unlisted symbol, W^X violation, forged opcode,
     non-jump/call/conditional sites and short forms without a
     decoder row; the joint `_zeuge` witness with a reached
     memory-changing run.
   - Explicitly OPEN (never assumed here): source correspondence --
     units arrive already lowered, nothing here claims the bytes are
     the emitted form of any source block or that duties, contracts,
     costs, locks or call logs refine anything (consumer: pipeline
     and validator lanes); `valX86_sound` and any full
     source-to-final-loaded-byte closing theorem; hardware
     correspondence -- fetch runs over the model `Speicher`
     function, not silicon; TSO/GX bridge, concurrency, budget/work
     transfer, allocator behaviour (other lanes).
   - Explicitly OPEN link scope: exactly the five operand shapes of
     one closing (jump/call/conditional rel32, abs64 data, rel8
     short); fall-through coverage across unit boundaries beyond
     the re-decoded windows, rel8 short selection convergence,
     conditional-field agreement outside jump/call/conditional,
     overlapping sites (refused by `opsDisjunktB`, never merged),
     and any instruction outside jump/call/conditional stay with
     the extension codec lanes. abs64 and rel8 operands are data
     and one byte respectively: they read back through
     `abs64Wort`/`disp8Signed`, never through `decode`.
   - No loader execution, entry handoff or OS interaction is
     modelled: `geladen` stays the pure mapping function; entries
     are contained by `wohlgeformt`, never executed here.
   - No second decoder, loader, executor, ISA model or IR is created
     here: every fact reuses the named producer theorems.
-/

#print axioms multiPatch_bereich
#print axioms multiPatch_stelle
#print axioms multiPatch_rahmen
#print axioms multiPatch_laenge
#print axioms rel8Byte_rundgang
#print axioms feld_agreement_sprung
#print axioms feld_agreement_ruf
#print axioms feld_agreement_bedingt
#print axioms fenster_sprung
#print axioms fenster_ruf
#print axioms fenster_bedingt
#print axioms fenster_abs64
#print axioms fenster_rel8
#print axioms multi_ruf_schliesst
#print axioms multi_bedingt_schliesst
#print axioms multi_abs64_liest
#print axioms multi_rel8_liest
#print axioms verknuepfeAlle_laenge
#print axioms mAbschnitteAux_tiling
#print axioms mAbschnitt_wx
#print axioms mBild_byte_geladen
#print axioms mBild_wx
#print axioms multiPatchAlle_laenge
#print axioms multiPatchAlle_rahmen
#print axioms multiPatchAlle_kopf_stelle
#print axioms opsDisjunktB_gilt
#print axioms mehrere_korrekt
#print axioms mehrere_korrekt_zeuge

end Gabbro.Grammatik.X86
