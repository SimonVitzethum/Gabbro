/-
  File:      Grammatik/X86/Cvtsi2sdW64.lean
  Subject:   Hardware completion: CVTSI2SD from the 64-bit integer source.

  Lane 789: int64-to-binary64 conversion with the width obligation
  (REX.W = 1) and RNE rounding, pinned bytes, refusal of unadmitted
  widths. Reuses the accepted canonical vocabulary (`Typen`: `Zustand`;
  `ScalarFloat`: `FpZustand`/`fpSchritt`/`cvtsiErg`; `Gleitprofil`:
  `ofInt`/`rundeExakt`/RNE profile; `ScalarFloatHardwareForms`:
  `fpHwEncodeCvtsi`/`fpHwDecode`/`fpHwByteschritt`) and the accepted
  byte-facing dispatcher; no new evaluator, no new IEEE arithmetic,
  no source/checker/emitter edit.

  Manual provenance (local snapshot `.tmp/HARDWARE-REFERENCES/`):
  Intel SDM combined Vols 1-4, edition 325462-093US September 2026
  (`REFERENCES.json`, sha256 `a4a62e6...f9168ee5`):
  - CVTSI2SD opcode rows, txt lines 48890-48895: `F2 0F 2A /r`
    (`r32/m32`) and `F2 REX.W 0F 2A /r` (`r/m64`).
  - Description, txt lines 48921-48924: signed doubleword/quadword to
    double; low quadword stored, high quadword unchanged; inexact
    results rounded per MXCSR rounding control.
  - Operation, txt lines 48969-48976: `DEST[63:0]` conversion with
    the 64-bit (`SRC[63:0]`) versus 32-bit (`SRC[31:0]`) width split,
    `DEST[MAXVL-1:64]` unmodified (legacy SSE preserve).
-/
import Grammatik.X86.ScalarFloat
import Grammatik.X86.ScalarFloatHardwareForms

namespace Gabbro.Grammatik.X86

/-- Lane marker: the 64-bit integer source width handled here. -/
def cvtsiW64Breite : Nat := 64

/-- The lane marker is the quadword width. -/
theorem cvtsiW64Breite_ist64 : cvtsiW64Breite = 64 := rfl

/-! ## 1. Pinned bytes: the REX.W = 1 register row.

  The canonical 5-byte row is the accepted `fpHwEncodeCvtsi`
  (F2 prefix, REX.W = 1, 0F escape, opcode 2A, ModRM mod = 11).
  Decoding inverts encoding over the full register file; the pilot
  refuses the row (disjointness for the lane-575 dispatcher shape). -/

/-- The W64 row is five bytes long. -/
theorem cvtsiW64_len (dst : XmmReg) (src : Register) :
    (fpHwEncodeCvtsi dst src).length = 5 :=
  fpHwLen_cvtsi dst src

/-- Encode/decode round trip for the W64 row. -/
theorem cvtsiW64_roundtrip (dst : XmmReg) (src : Register)
    (suffix : List Byte) :
    fpHwDecode (fpHwEncodeCvtsi dst src ++ suffix) =
      some (⟨.cvtsi2sd dst src, (fpHwEncodeCvtsi dst src).length⟩,
        suffix) :=
  fpHwRoundtrip_cvtsi dst src suffix

/-- The pilot refuses the W64 row: no accepted pilot form is shadowed. -/
theorem cvtsiW64_pilot_weist_zurueck :
    decode (fpHwEncodeCvtsi .xmm0 .rax) = none :=
  fpHwPilot_weist_cvtsi_zurueck

/-! ## 2. Width obligation: REX.W = 0 and memory sources refuse.

  The accepted REX decoder pins the obligation: a conversion with
  REX.W = 0 selects the doubleword source (txt line 48890: `r32/m32`)
  while the accepted `cvtsi2sd` converts the whole 64-bit register,
  so those bytes refuse; a memory-source conversion has no `FpBefehl`
  constructor and no second evaluator, so those bytes refuse too. -/

/-- W = 0 refuses: it selects the doubleword source. -/
theorem cvtsiW64_w0_verweigert (suffix : List Byte) :
    fpHwDecode (natByte 242 :: natByte 64 :: natByte 15 :: natByte 42 ::
      modrmReg 0 1 :: suffix) = none :=
  fpHwDecode_cvtsiW0_verweigert suffix

/-- Memory-source conversion refuses: register sources only. -/
theorem cvtsiW64_speicher_verweigert (d : BitVec 32)
    (suffix : List Byte) :
    fpHwDecode (natByte 242 :: natByte 72 :: natByte 15 :: natByte 42 ::
      modrmMem 0 0 :: leBytes32 d ++ suffix) = none :=
  fpHwDecode_cvtsiSpeicher_verweigert d suffix

/-! ## 3. RNE rounding: the converted word IS the kernel round.

  `cvtsiErg` is definitionally `ofInt f64` (hence `rundeExakt`,
  round-to-nearest-ties-to-even from the exact integer value), and
  the step runs only under the admitted MXCSR profile, whose
  rounding-control bits are RNE (`mxcsrRundungRNE`). Inexact results
  are therefore rounded per MXCSR.RC (txt line 48923); NaN payloads
  are class-only (inherited cut of `Gleitprofil` §7). -/

/-- The conversion result IS the kernel RNE round of the whole
    signed 64-bit source value. -/
theorem cvtsiW64_ist_rne (w : Wort) :
    cvtsiErg w = Gleitkomma.ofInt Gleitkomma.f64 w.toInt := rfl

/-- The kernel round is the exact-value RNE path. -/
theorem cvtsiW64_rne_pfand (z : Int) :
    Gleitkomma.ofInt Gleitkomma.f64 z =
      Gleitkomma.rundeExakt Gleitkomma.f64 ⟨z, 0⟩ := rfl

/-- The admitted profile carries RNE rounding control. -/
theorem cvtsiW64_profil_rne (k : FPKontext)
    (h : fpEintritt k = true) :
    mxcsrRundungRNE k.mxcsr = true := by
  unfold fpEintritt mxcsrGueltig at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hrne, _⟩, _⟩, _⟩ := h
  exact hrne

/-- Small exact value: `42` becomes the `42.0` pattern. -/
theorem cvtsiW64_42 : muster64 (cvtsiErg 42) = 0x4045000000000000 :=
  cvtsiErg_42

/-! ## 4. Fetched execution: the W64 row through the common path.

  Nothing is redefined: each fact runs the accepted `fpSchritt`
  equation for the fetched form (via the accepted gated byte step
  `fpHwByteschritt`) and projects one observable out of it. The
  fetch equation travels as an explicit premise, so every conclusion
  is reached from bytes in actual memory, never from a
  caller-supplied `FpDecodiert`. -/

/-- Fetched W64 conversion computes the RNE model value. -/
theorem cvtsiW64_rechnet (dst : XmmReg) (src : Register)
    (t t1 : FpZustand) (d : FpDecodiert) (rest : List Byte)
    (hf : fpHwFetchDekodiert t = some (d, rest))
    (hform : d.befehl = .cvtsi2sd dst src)
    (hfp : fpEintritt t.fp = true)
    (hgate : fpHwCvttZugelassen d.befehl t = true)
    (hout : fpHwByteschritt t = .weiter t1) :
    xmmTief t1.xmm dst =
      muster64 (Gleitkomma.ofInt Gleitkomma.f64
        (t.kern.register src).toInt) := by
  have hok := (fpHwFetchDekodiert_erfolg t d rest hf).2.2.1
  have hstep := fpHwByteschritt_schritt t t1 d rest hf hgate hout
  have heq := fpSchritt_cvtsi2sd d t dst src hok hfp hform
  rw [hstep] at heq
  obtain rfl := Option.some_inj.mp heq
  rw [xmmSchreibeTief_tief, cvtsiW64_ist_rne]

/-- Fetched W64 conversion preserves flags. -/
theorem cvtsiW64_flags (dst : XmmReg) (src : Register)
    (t t1 : FpZustand) (d : FpDecodiert) (rest : List Byte)
    (hf : fpHwFetchDekodiert t = some (d, rest))
    (hform : d.befehl = .cvtsi2sd dst src)
    (hfp : fpEintritt t.fp = true)
    (hgate : fpHwCvttZugelassen d.befehl t = true)
    (hout : fpHwByteschritt t = .weiter t1) :
    t1.kern.flags = t.kern.flags := by
  have hok := (fpHwFetchDekodiert_erfolg t d rest hf).2.2.1
  have hstep := fpHwByteschritt_schritt t t1 d rest hf hgate hout
  exact fpSchritt_cvtsi2sd_flags d t t1 dst src hok hfp hform hstep

/-- Fetched W64 conversion changes no memory byte. -/
theorem cvtsiW64_speicher (dst : XmmReg) (src : Register)
    (t t1 : FpZustand) (d : FpDecodiert) (rest : List Byte)
    (hf : fpHwFetchDekodiert t = some (d, rest))
    (hform : d.befehl = .cvtsi2sd dst src)
    (hfp : fpEintritt t.fp = true)
    (hgate : fpHwCvttZugelassen d.befehl t = true)
    (hout : fpHwByteschritt t = .weiter t1) :
    t1.kern.speicher = t.kern.speicher := by
  have hok := (fpHwFetchDekodiert_erfolg t d rest hf).2.2.1
  have hstep := fpHwByteschritt_schritt t t1 d rest hf hgate hout
  exact fpSchritt_cvtsi2sd_speicher d t t1 dst src hok hfp hform hstep

/-- Fetched W64 conversion keeps the destination high half
    (legacy SSE preserve, txt line 48976). -/
theorem cvtsiW64_hoch (dst : XmmReg) (src : Register)
    (t t1 : FpZustand) (d : FpDecodiert) (rest : List Byte)
    (hf : fpHwFetchDekodiert t = some (d, rest))
    (hform : d.befehl = .cvtsi2sd dst src)
    (hfp : fpEintritt t.fp = true)
    (hgate : fpHwCvttZugelassen d.befehl t = true)
    (hout : fpHwByteschritt t = .weiter t1) :
    xmmHoch t1.xmm dst = xmmHoch t.xmm dst := by
  have hok := (fpHwFetchDekodiert_erfolg t d rest hf).2.2.1
  have hstep := fpHwByteschritt_schritt t t1 d rest hf hgate hout
  exact fpSchritt_cvtsi2sd_hoch d t t1 dst src hok hfp hform hstep

/-! ## 5. Connection: fetched W64 bytes execute the RNE conversion.

  One theorem ties the width obligation (REX.W = 1 bytes round-trip
  through `fpHwDecode`, W = 0 and memory rows refused in §2), the
  RNE value (§3), and the common byte-facing execution (§4) with its
  precise frames: low half converted, flags and memory preserved,
  high half preserved, RIP advanced past the decode length. -/

/-- The W64 connection: fetched REX.W bytes convert the whole
    signed 64-bit source with RNE rounding, preserving flags,
    memory and the destination high half. Every premise is used. -/
theorem Cvtsi2sdW64_verbindung (dst : XmmReg) (src : Register)
    (t t1 : FpZustand) (d : FpDecodiert) (rest : List Byte)
    (hf : fpHwFetchDekodiert t = some (d, rest))
    (hform : d.befehl = .cvtsi2sd dst src)
    (hfp : fpEintritt t.fp = true)
    (hgate : fpHwCvttZugelassen d.befehl t = true)
    (hout : fpHwByteschritt t = .weiter t1) :
    xmmTief t1.xmm dst =
        muster64 (Gleitkomma.ofInt Gleitkomma.f64
          (t.kern.register src).toInt)
      ∧ t1.kern.flags = t.kern.flags
      ∧ t1.kern.speicher = t.kern.speicher
      ∧ xmmHoch t1.xmm dst = xmmHoch t.xmm dst
      ∧ t1.kern.rip = ripNach t.kern.rip d.laenge := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact cvtsiW64_rechnet dst src t t1 d rest hf hform hfp hgate hout
  · exact cvtsiW64_flags dst src t t1 d rest hf hform hfp hgate hout
  · exact cvtsiW64_speicher dst src t t1 d rest hf hform hfp hgate hout
  · exact cvtsiW64_hoch dst src t t1 d rest hf hform hfp hgate hout
  · have hok := (fpHwFetchDekodiert_erfolg t d rest hf).2.2.1
    have hstep := fpHwByteschritt_schritt t t1 d rest hf hgate hout
    have heq := fpSchritt_cvtsi2sd d t dst src hok hfp hform
    rw [hstep] at heq
    obtain rfl := Option.some_inj.mp heq
    rfl

/-! ## 6. Joint witness: fetched conversion then store.

  The premises of `Cvtsi2sdW64_verbindung` are inhabited JOINTLY on
  the accepted W2 image (REX.W conversion of `rax = 42` to `42.0`
  followed by a REX MOVSD store): fetch, form, profile, gate and
  step hold together, the connection concludes, and the second
  fetched step changes actual memory (the word reads back, one byte
  observably changed). Non-degenerate: a reached two-step run with
  a real memory change plus planted width refusals (§2). -/

/-- Joint witness for the W64 connection: all premises together,
    the converted value, and a reached memory-changing store run. -/
theorem Cvtsi2sdW64_verbindung_zeuge :
    ∃ (dst : XmmReg) (src : Register) (t t1 t2 : FpZustand)
      (d : FpDecodiert) (rest : List Byte),
      fpHwFetchDekodiert t = some (d, rest)
      ∧ d.befehl = .cvtsi2sd dst src
      ∧ fpEintritt t.fp = true
      ∧ fpHwCvttZugelassen d.befehl t = true
      ∧ fpHwByteschritt t = .weiter t1
      ∧ xmmTief t1.xmm dst =
          muster64 (Gleitkomma.ofInt Gleitkomma.f64
            (t.kern.register src).toInt)
      ∧ fpHwByteschritt t1 = .weiter t2
      ∧ read64 t2.kern.speicher (BitVec.ofNat 64 8192) =
          some 0x4045000000000000
      ∧ t.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) ≠
          t2.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) := by
  refine ⟨.xmm0, .rax, fpHwW2T, fpHwW2T1, fpHwW2T2,
    ⟨.cvtsi2sd .xmm0 .rax, 5⟩,
    fpHwEncodeMovsdSpeichere .rbx .xmm0 0,
    fpHwW2_fetch1, rfl, fpHwW2Fp, fpHwW2Gate1, fpHwW2_schritt1, ?_,
    fpHwW2_schritt2, fpHwW2_liest, fpHwW2_aendert⟩
  have h := (Cvtsi2sdW64_verbindung .xmm0 .rax fpHwW2T fpHwW2T1
    ⟨.cvtsi2sd .xmm0 .rax, 5⟩
    (fpHwEncodeMovsdSpeichere .rbx .xmm0 0)
    fpHwW2_fetch1 rfl fpHwW2Fp fpHwW2Gate1 fpHwW2_schritt1).1
  exact h

/- CUTS: what is not proved here.

   Proved here (all over the REUSED canonical vocabulary -- no new
   machine, no new decoder row, no new evaluator, no new IEEE
   arithmetic, no source claim):
   - pinned W64 bytes (§1): the accepted 5-byte REX.W = 1 register
     row (`fpHwEncodeCvtsi`/`fpHwDecode` round trip over the full
     register file, pilot disjointness for the lane-575 dispatcher);
   - width obligation (§2): REX.W = 0 bytes refuse (doubleword
     source, txt line 48890) and memory-source bytes refuse (no
     `FpBefehl` constructor, no second evaluator);
   - RNE rounding (§3): the converted word IS `ofInt f64` (hence
     `rundeExakt`, round-to-nearest-ties-to-even from the exact
     integer), the admitted MXCSR profile carries RNE control, and
     `42` computes to `42.0`;
   - fetched execution (§4) and the connection (§5): the fetched
     REX.W row through the accepted gated byte step computes the
     RNE model value, preserving flags, memory and the destination
     high half (txt line 48976), with RIP past the decode length;
   - joint witness (§6): all connection premises together on the
     accepted W2 image, plus a reached second fetched store step
     with a real memory change (word reads back, one byte changed).
   NOT proved here, and not claimed:
   - No silicon correspondence: byte shapes (F2 prefix before REX,
     0F escape, opcode 2A, ModRM mod = 11) are STATED from the SDM
     opcode/description/operation pages as an implementation
     contract in the BYTE-PILOT.md style, never verified against
     hardware. Encoder round-trip consistency is not hardware
     fidelity.
   - NaN relation is class-level only (inherited gap of
     `Gleitprofil` §7): payload equality of computed results is
     never concluded. SNaN has no model form; sticky MXCSR flags,
     DAZ/FTZ execution and unmasked traps stay unmodelled.
   - Deliberate subset refusals (validator incompleteness, never
     wrong execution): the 32-bit (W = 0) and memory-source widths
     have no accepted execution here; VEX/EVEX, packed lanes, x87
     and FMA have no row: syntactically absent, refused.
   - No TSO/concurrency, cost/timing, ABI/loader/entry/budget or
     whole-image claim: everything is sequential over one
     `Speicher`; the unified-dispatcher integration stays with its
     consumer lanes.
   - No source, checker, emitter or goal claim: the model-op link
     (`cvtsiErg` IS `ofInt f64`) is consumed from `ScalarFloat`,
     never restated as a new source bridge.
   - The `decide` proofs are closed concrete evaluations over
     kernel-computable definitions (never `native_decide`).
-/

#print axioms cvtsiW64Breite
#print axioms cvtsiW64Breite_ist64
#print axioms cvtsiW64_len
#print axioms cvtsiW64_roundtrip
#print axioms cvtsiW64_pilot_weist_zurueck
#print axioms cvtsiW64_w0_verweigert
#print axioms cvtsiW64_speicher_verweigert
#print axioms cvtsiW64_ist_rne
#print axioms cvtsiW64_rne_pfand
#print axioms cvtsiW64_profil_rne
#print axioms cvtsiW64_42
#print axioms cvtsiW64_rechnet
#print axioms cvtsiW64_flags
#print axioms cvtsiW64_speicher
#print axioms cvtsiW64_hoch
#print axioms Cvtsi2sdW64_verbindung
#print axioms Cvtsi2sdW64_verbindung_zeuge

end Gabbro.Grammatik.X86
