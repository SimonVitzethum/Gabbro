/-
  File:      Grammatik/X86/ComposePatchBytes.lean
  Subject:   Composition closing: displacement/relocation patching to
             byte-level re-verification.

  Lane 846: compose the already-accepted producer modules (`Relokation`
  finite patching, `BranchLayout` displacement facts, `RelocatedExecution`
  site vocabulary) with the consumer side (`DecodingCoverage` arbitrary-input
  decoder facts, `Byteschritt` fetch/execute permission checks) into one
  checked closing step over patched regions. Nothing is re-proved here:
  every fact reuses the producer/consumer lemmas by name. No second
  decoder, loader, executor, ISA or IR is created.

  Producer/consumer interface closed: `Relokation.patchAt` / `patchRel32`
  (byte patching) produces the patched image; `DecodingCoverage.decode_abdeckung`
  / `decode_fenster_kongruenz` (re-decode carries its own length) and
  `Byteschritt.kanonisch_schritt_ueberein` / `byteschritt_weiter` (execute
  permission plus actual-memory step) consume it.
-/
import Grammatik.X86.Relokation
import Grammatik.X86.BranchLayout
import Grammatik.X86.RelocatedExecution
import Grammatik.X86.DecodingCoverage
import Grammatik.X86.Byteschritt

namespace Gabbro.Grammatik.X86

/-- A successful rel32 field patch passed its signed-32 fit check: the
    producer (`Relokation.patchRel32`) refuses out-of-range displacements
    with `none`, so `some` carries the fit. -/
theorem patchRel32_passt (img : List Byte) (off : Nat) (disp : Int)
    (out : List Byte) (h : patchRel32 img off disp = some out) :
    rel32Passt disp = true := by
  unfold patchRel32 at h
  by_cases hc : rel32Passt disp = true
  · exact hc
  · rw [if_neg hc] at h
    cases h

/-! ## 1. Generic whole-region patch-to-redecode closing.

    Producer `Relokation.patchAt` writes the canonical site bytes
    (`RelocatedExecution.relocBytes`, all three `RelocArt` classes);
    consumer `DecodingCoverage.decode_abdeckung` re-reads the patched
    window with the independent decoder. The closing ties them: the
    re-decoded window is exactly the patched region, at exactly its
    length, with the frame outside preserved. -/

/-- COMPOSITION CLOSING (patched bytes to re-verification): for an
    ARBITRARY admitted patch of a canonical relocation-site encoding and
    an ARBITRARY admitted re-decode of the patched window to the same
    site instruction, the taken patched region is the site bytes, the
    length equation holds on the patched window, the exact region
    re-decodes, the site lies in range, the site bytes and the outside
    frame are as patched, and the form is covered. -/
theorem ComposePatchBytes_verbindung
    (img : List Byte) (istart : Nat) (a : RelocArt) (d : BitVec 32)
    (out : List Byte) (rest : List Byte)
    (hpatch : patchAt img istart (relocBytes a d) = some out)
    (hdec : decode (out.drop istart) =
      some ((⟨relocBefehl a d, relocLen a⟩, rest))) :
    (out.drop istart).take (relocLen a) = relocBytes a d ∧
    relocLen a + rest.length = (out.drop istart).length ∧
    decode ((out.drop istart).take (relocLen a) ++ rest) =
      some ((⟨relocBefehl a d, relocLen a⟩, rest)) ∧
    istart + (relocBytes a d).length ≤ img.length ∧
    (∀ k, k < (relocBytes a d).length →
      out[istart + k]? = (relocBytes a d)[k]?) ∧
    (∀ i, (∀ k, k < (relocBytes a d).length → i ≠ istart + k) →
      out[i]? = img[i]?) ∧
    decktAb ⟨relocBefehl a d, relocLen a⟩ := by
  have hlen0 : (relocBytes a d).length = relocLen a := relocBytes_len a d
  obtain ⟨heq, hok, hshape, pre, hbs, hplen⟩ :=
    decode_abdeckung (out.drop istart) _ rest hdec
  have hrange := patchAt_bereich img istart (relocBytes a d) out hpatch
  have hsite := fun k hk =>
    patchAt_stelle img istart (relocBytes a d) out hpatch k hk
  have hrahmen := fun i hi =>
    patchAt_rahmen img istart (relocBytes a d) out hpatch i hi
  have htake : (out.drop istart).take (relocLen a) = relocBytes a d := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < relocLen a
    · have hk : i < (relocBytes a d).length := by
        rw [hlen0]
        exact hi
      rw [List.getElem?_take, if_pos hi, List.getElem?_drop]
      exact hsite i hk
    · have hlen_le : (relocBytes a d).length ≤ i := by
        rw [hlen0]
        omega
      rw [List.getElem?_take, if_neg hi,
        List.getElem?_eq_none hlen_le]
  have hlaenge : (⟨relocBefehl a d, relocLen a⟩ : Decodiert).laenge =
      relocLen a := rfl
  obtain ⟨hrest, hwhole⟩ :=
    decode_fenster_kongruenz (out.drop istart) _ rest hdec
  rw [hlaenge] at hwhole
  have hregion : decode ((out.drop istart).take (relocLen a) ++ rest) =
      some ((⟨relocBefehl a d, relocLen a⟩, rest)) := by
    rw [htake] at hwhole
    rw [htake, hwhole]
    exact hdec
  exact ⟨htake, heq, hregion, hrange, hsite, hrahmen, hshape⟩

/-! ## 2. Permission-carrying execution through the patched region.

    Consumer `Byteschritt.kanonisch_schritt_ueberein` runs the canonical
    encoding from actual executable memory. The closing feeds it the
    patched region: the state's fetched window is the re-verified taken
    bytes, execute permission covers exactly the patched length, and the
    existing `schritt` outcome is the reached successor. The patch-range
    conjunct keeps the producer premise load-bearing. -/

/-- EXECUTION THROUGH THE PATCHED REGION: for an ARBITRARY admitted
    patch, an ARBITRARY state whose fetched window is the re-verified
    patched region with execute permission over the patched length, and
    an ARBITRARY admitted `schritt` outcome on the site instruction, the
    byte step reaches that successor, and the site lies in range. -/
theorem ComposePatchBytes_schritt
    (img out : List Byte) (istart : Nat) (a : RelocArt) (d : BitVec 32)
    (suffix : List Byte) (z z' : Zustand)
    (hpatch : patchAt img istart (relocBytes a d) = some out)
    (htake : (out.drop istart).take (relocLen a) = relocBytes a d)
    (hwin : geholt z = (out.drop istart).take (relocLen a) ++ suffix)
    (hexe : ausfuehrbarN z.speicher z.rip (relocBytes a d).length = true)
    (hsch : schritt ⟨relocBefehl a d, relocLen a⟩ z = some z') :
    byteschritt z = .weiter z' ∧
    istart + (relocBytes a d).length ≤ img.length := by
  have hrange := patchAt_bereich img istart (relocBytes a d) out hpatch
  rw [htake] at hwin
  obtain ⟨hf, hbs⟩ :=
    kanonisch_schritt_ueberein (relocBefehl a d) z suffix hwin hexe
  have hll : (encode (relocBefehl a d)).length = relocLen a :=
    relocBytes_len a d
  rw [hll, hsch] at hbs
  refine ⟨by simpa using hbs, hrange⟩

/-! ## 3. Field-level displacement agreement for the jump site.

    The whole-region closing above patches full site encodings. The
    relocation producer (`Relokation.patchRel32`) patches only the four
    displacement bytes behind an existing opcode. This leg closes that
    shape: the re-decoded displacement equals the patched value. The
    proof goes through the accepted byte bridge
    (`BranchLayout.rel32Bytes_dispSigned`) and decoder determinism
    (the same bytes decode to one instruction), never through decoder
    internals. -/

/-- FIELD AGREEMENT (patched displacement re-decoded): for an ARBITRARY
    image with a jump opcode at `istart`, an ARBITRARY admitted rel32
    field patch behind it, and an ARBITRARY admitted re-decode of the
    window to a five-byte jump, the decoded displacement IS the patched
    value; the length equation holds, the fit holds, the opcode byte
    survives, the field bytes are as patched, the form is covered, and
    the exact five-byte region re-decodes. -/
theorem ComposePatchBytes_feld_verbindung
    (img : List Byte) (istart : Nat) (disp : Int) (out : List Byte)
    (d : BitVec 32) (rest : List Byte)
    (himg : img[istart]? = some (natByte 233))
    (hpatch : patchRel32 img (istart + 1) disp = some out)
    (hdec : decode (out.drop istart) = some ((⟨.jump32 d, 5⟩, rest))) :
    dispSigned d = disp ∧
    5 + rest.length = (out.drop istart).length ∧
    rel32Passt disp = true ∧
    out[istart]? = some (natByte 233) ∧
    (∀ k, k < 4 → out[istart + 1 + k]? = (rel32Bytes disp)[k]?) ∧
    decktAb ⟨.jump32 d, 5⟩ ∧
    decode ((out.drop istart).take 5 ++ rest) =
      some ((⟨.jump32 d, 5⟩, rest)) := by
  have hfit := patchRel32_passt img (istart + 1) disp out hpatch
  have hfitI := of_decide_eq_true hfit
  obtain ⟨d₀, hd₀⟩ := dispVonFit disp hfitI.1 hfitI.2
  have hbridge : rel32Bytes disp = leBytes32 d₀ := by
    rw [← hd₀]
    exact rel32Bytes_dispSigned d₀
  have hpatchAt : patchAt img (istart + 1) (rel32Bytes disp) = some out := by
    unfold patchRel32 at hpatch
    rw [if_pos hfit] at hpatch
    exact hpatch
  have hsite : ∀ k, k < 4 → out[istart + 1 + k]? = (rel32Bytes disp)[k]? :=
    fun k hk => patchRel32_stelle img (istart + 1) disp out hpatch k hk
  have hop_out : out[istart]? = some (natByte 233) := by
    have hfr : ∀ k, k < (rel32Bytes disp).length →
        istart ≠ istart + 1 + k := fun k _ => by omega
    have h :=
      patchAt_rahmen img (istart + 1) (rel32Bytes disp) out hpatchAt istart hfr
    rw [h]
    exact himg
  obtain ⟨heq0, hok, hshape, pre, hbs, hplen⟩ :=
    decode_abdeckung (out.drop istart) _ rest hdec
  have heq : 5 + rest.length = (out.drop istart).length := heq0
  have htake5 : (out.drop istart).take 5 = natByte 233 :: rel32Bytes disp := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < 5
    · by_cases hi0 : i = 0
      · subst hi0
        have hL0 : ((out.drop istart).take 5)[0]? = out[istart]? := by simp
        have hR0 : (natByte 233 :: rel32Bytes disp)[0]? =
            some (natByte 233) := by simp
        rw [hL0, hR0, hop_out]
      · obtain ⟨k, rfl, hk⟩ : ∃ k, i = k + 1 ∧ k < 4 :=
          ⟨i - 1, by omega, by omega⟩
        have hL1 : ((out.drop istart).take 5)[k + 1]? =
            out[istart + 1 + k]? := by
          have e : istart + (k + 1) = istart + 1 + k := by omega
          simp only [List.getElem?_take, List.getElem?_drop]
          rw [if_pos hi, e]
        rw [hL1, hsite k hk]
        simp
    · have hLnone : ((out.drop istart).take 5)[i]? = none := by
        rw [List.getElem?_take, if_neg hi]
      have hRnone : (natByte 233 :: rel32Bytes disp)[i]? = none := by
        have hle : (natByte 233 :: rel32Bytes disp).length ≤ i := by
          simp [rel32Bytes_laenge]
          omega
        exact List.getElem?_eq_none hle
      rw [hLnone, hRnone]
  obtain ⟨hrest, hwhole⟩ :=
    decode_fenster_kongruenz (out.drop istart) _ rest hdec
  have hlaenge : (⟨.jump32 d, 5⟩ : Decodiert).laenge = 5 := rfl
  rw [hlaenge, htake5] at hwhole
  have hdec' : decode ((natByte 233 :: rel32Bytes disp) ++ rest) =
      some ((⟨.jump32 d, 5⟩, rest)) := by
    rw [hwhole]
    exact hdec
  have hregion : decode ((out.drop istart).take 5 ++ rest) =
      some ((⟨.jump32 d, 5⟩, rest)) := by
    rw [htake5]
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
  exact ⟨hd₀, heq, hfit, hop_out, hsite, hshape, hregion⟩

/-! ## 4. Planted refusal cases: overrun and forged opcode. -/

/-- OVERRUN REFUSAL: a five-byte site patch two bytes before the end of
    a three-byte image is refused, never wrapped. -/
theorem ComposePatchBytes_ueberlauf_verweigert :
    patchAt [natByte 233, natByte 0, natByte 0] 2
      [natByte 16, natByte 0, natByte 0, natByte 0, natByte 0] = none := by
  decide

/-- FORGED-OPCODE REFUSAL: a five-byte window with a non-canonical head
    byte refuses re-decode, while the intact opcode would decode. -/
theorem ComposePatchBytes_opcode_falsch_verweigert :
    decode [natByte 6, natByte 16, natByte 0, natByte 0, natByte 0] =
      none := by
  decide

/-! ## 5. Joint witness: premises inhabited, closing reached,
    memory changed, refusals planted. -/

/-- Witness image: a five-byte jump with a zero displacement. -/
def patchZeugenBild : List Byte :=
  [natByte 233, natByte 0, natByte 0, natByte 0, natByte 0]

/-- Witness displacement field: +16. -/
def patchZeugenDisp : BitVec 32 := BitVec.ofNat 32 16

/-- Witness patched image: the same jump with displacement +16. -/
def patchZeugenGepatcht : List Byte :=
  [natByte 233, natByte 16, natByte 0, natByte 0, natByte 0]

/-- JOINT WITNESS for `ComposePatchBytes_verbindung`: both premises
    instantiated jointly on one non-degenerate patched jump (opcode plus
    displacement), the re-verified region and the displacement agreement
    derived through the closing, a reached memory-changing call run
    through actual bytes, and planted refusals at patch level
    (overrun), decode level (forged opcode), permission level
    (readable but not executable) and execution level (mutated byte
    refuses while the intact bytes step; a patched displacement byte
    moves the executed target). -/
theorem ComposePatchBytes_verbindung_zeuge :
    (patchAt patchZeugenBild 0 (relocBytes .sprung patchZeugenDisp) =
        some patchZeugenGepatcht ∧
      decode (patchZeugenGepatcht.drop 0) =
        some ((⟨relocBefehl .sprung patchZeugenDisp, relocLen .sprung⟩, []))) ∧
    ((patchZeugenGepatcht.drop 0).take (relocLen .sprung) =
        relocBytes .sprung patchZeugenDisp ∧
      dispSigned patchZeugenDisp = 16 ∧
      relocLen .sprung + ([] : List Byte).length =
        (patchZeugenGepatcht.drop 0).length) ∧
    (∃ m : Speicher, byteschritt zustandRuf =
        .weiter (schrittCall zustandRuf Register.rsp m
          (zustandRuf.register Register.rsp - BitVec.ofNat 64 8)
          (BitVec.ofNat 64 0x1015)) ∧
        read64 m (BitVec.ofNat 64 0x1FF8) =
          some (BitVec.ofNat 64 0x1005) ∧
        m.bytes (BitVec.ofNat 64 0x1FF8) ≠
          zustandRuf.speicher.bytes (BitVec.ofNat 64 0x1FF8)) ∧
    (patchAt [natByte 233, natByte 0, natByte 0] 2
        [natByte 16, natByte 0, natByte 0, natByte 0, natByte 0] = none) ∧
    (decode [natByte 6, natByte 16, natByte 0, natByte 0, natByte 0] =
        none) ∧
    (ausgangRip (byteschritt ohneExecStart) = none ∧
      ohneExecStart.speicher.lesbar (BitVec.ofNat 64 4096) = true) ∧
    (ausgangRip (byteschritt ketteStartFalsch) = none ∧
      ausgangRip (byteschritt ketteStart) =
        some (BitVec.ofNat 64 4106)) ∧
    (ausgangRip (byteschritt (sprungStart (natByte 16))) =
        some (BitVec.ofNat 64 4117) ∧
      ausgangRip (byteschritt (sprungStart (natByte 17))) =
        some (BitVec.ofNat 64 4118)) := by
  have hp : patchAt patchZeugenBild 0 (relocBytes .sprung patchZeugenDisp) =
      some patchZeugenGepatcht := by
    decide
  have hd : decode (patchZeugenGepatcht.drop 0) =
      some ((⟨relocBefehl .sprung patchZeugenDisp, relocLen .sprung⟩, [])) := by
    decide
  have himg : patchZeugenBild[0]? = some (natByte 233) := by
    decide
  have hpF : patchRel32 patchZeugenBild 1 16 = some patchZeugenGepatcht := by
    decide
  have hdF : decode (patchZeugenGepatcht.drop 0) =
      some ((⟨.jump32 patchZeugenDisp, 5⟩, [])) := by
    decide
  refine ⟨⟨hp, hd⟩, ⟨?_, ?_, ?_⟩, ruf_schritt_zeuge, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ComposePatchBytes_verbindung patchZeugenBild 0 .sprung patchZeugenDisp
      patchZeugenGepatcht [] hp hd).1
  · exact (ComposePatchBytes_feld_verbindung patchZeugenBild 0 16 patchZeugenGepatcht
      patchZeugenDisp [] himg hpF hdF).1
  · exact (ComposePatchBytes_verbindung patchZeugenBild 0 .sprung patchZeugenDisp
      patchZeugenGepatcht [] hp hd).2.1
  · exact ComposePatchBytes_ueberlauf_verweigert
  · exact ComposePatchBytes_opcode_falsch_verweigert
  · exact ohne_exec_verweigert
  · exact opcode_geaendert_verweigert
  · exact sprungziel_folgt_byte

/- CUTS:
   - Proved here: `patchRel32_passt` (successful field patch implies
     fit); the generic whole-region closing
     `ComposePatchBytes_verbindung` (patched region re-decoded at its
     length, range/site/frame/coverage, over all three `RelocArt`
     classes); the permission-carrying execution leg
     `ComposePatchBytes_schritt` (fetched patched window plus execute
     permission reaches the `schritt` successor); the field-level
     displacement agreement `ComposePatchBytes_feld_verbindung` for
     the jump site (re-decoded displacement equals the patched value,
     through `rel32Bytes_dispSigned` and decoder determinism, never
     through decoder internals); planted overrun and forged-opcode
     refusals; the joint `_zeuge` witness (concrete jump patch with
     both premises decided, derived region/agreement/length facts, a
     reached memory-changing call run with return-address store and
     observed byte change, and patch/decode/permission/execution
     refusals plus the patched-byte-moves-target pair).
   - Explicitly OPEN (never assumed): whole-image layout convergence
     and the `valX86` closing theorem (consumer `ValidatorSkeleton`
     business); call/conditional field-level agreement (same
     determinism pattern as the jump leg, not carried out here);
     TSO/GX bridge, concurrency, source correspondence, contracts,
     cost/time, allocator behaviour (other lanes).
   - No second decoder, loader, executor, ISA, IR or interpreter is
     created here: every fact reuses the named producer/consumer
     lemmas.
-/

#print axioms patchRel32_passt
#print axioms ComposePatchBytes_verbindung
#print axioms ComposePatchBytes_schritt
#print axioms ComposePatchBytes_feld_verbindung
#print axioms ComposePatchBytes_ueberlauf_verweigert
#print axioms ComposePatchBytes_opcode_falsch_verweigert
#print axioms ComposePatchBytes_verbindung_zeuge

end Gabbro.Grammatik.X86
