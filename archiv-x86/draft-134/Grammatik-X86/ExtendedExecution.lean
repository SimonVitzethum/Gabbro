/-
  File:      Grammatik/X86/ExtendedExecution.lean
  Subject:   One unified byte-facing execution path over the accepted
             extension decoders.

  Lane 575: the canonical pilot (`Codec.decode` / `Ausfuehrung.schritt`,
  all 14 forms) plus exactly one new-form family per accepted helper --
  narrow (`NarrowCodec`), multiply/divide (`MulDivCodec` / `MulDiv`),
  shifts (`ShiftCodec`), SETcc/CMOVcc (`ControlCodec`), scalar SSE2
  DOUBLE (`ScalarFloatCodec` / `ScalarFloat`) and packed integer
  (`VectorCodec`) -- assembled into ONE selected-profile decoder
  (`decodeExt`) and ONE byte step from actual executable memory
  (`extByteschritt`). State embedding is the canonical `Zustand`
  inside the accepted `FpZustand`; the old evaluator is never
  redefined (`laufAlt` lifts it). No hardware, source, LOCK/SIMD-beyond
  the rows, or whole-image closure is claimed here (see CUTS).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Codec
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Byteschritt
import Grammatik.X86.NarrowCodec
import Grammatik.X86.MulDiv
import Grammatik.X86.MulDivCodec
import Grammatik.X86.ShiftCodec
import Grammatik.X86.ControlCodec
import Grammatik.X86.ScalarFloat
import Grammatik.X86.ScalarFloatCodec
import Grammatik.X86.VectorCodec
import Grammatik.X86.FeatureProfile

namespace Gabbro.Grammatik.X86

/-- One unified instruction: the pilot plus exactly one new-form
    family per accepted helper. SETcc/CMOVcc carry their actual
    decoded length (4) as checked data. -/
inductive ExtInstr where
  | pilot : Decodiert → ExtInstr
  | narrow : NarrowDec → ExtInstr
  | muldiv : MulDivDecodiert → ExtInstr
  | shift : ShiftDecodiert → ExtInstr
  | setcc : Bedingung → Register → Nat → ExtInstr
  | cmov : Bedingung → Register → Register → Nat → ExtInstr
  | fp : FpDecodiert → ExtInstr
  | vec : VectorDec → ExtInstr
  deriving DecidableEq, Repr

/-- Consumed length of one unified instruction (checked data). -/
def extLen : ExtInstr → Nat
  | .pilot d => d.laenge
  | .narrow d => d.laenge
  | .muldiv d => d.laenge
  | .shift d => d.laenge
  | .setcc _ _ l => l
  | .cmov _ _ _ l => l
  | .fp d => d.laenge
  | .vec d => d.laenge

/-- Unified decoder: the pilot first, each accepted extension only
    where every earlier decoder refuses. No pilot form is shadowed;
    no extension row is re-decided. Later fallbacks run only on
    earlier `none`, so dispatch is disjoint by construction. -/
def decodeExt : List Byte → Option (ExtInstr × List Byte) :=
  fun bs =>
    match decode bs with
    | some (d, rest) => some (.pilot d, rest)
    | none =>
      match decodeNarrow bs with
      | some (n, rest) => some (.narrow n, rest)
      | none =>
        match decodeMulDiv bs with
        | some (m, rest) => some (.muldiv m, rest)
        | none =>
          match decodeShift bs with
          | some (f, rest) =>
            some (.shift ⟨f, shiftLaenge f⟩, rest)
          | none =>
            match decodeSetCC bs with
            | some ((c, dst), rest) => some (.setcc c dst 4, rest)
            | none =>
              match decodeCmov bs with
              | some ((c, dst, src), rest) =>
                some (.cmov c dst src 4, rest)
              | none =>
                match fpDecode bs with
                | some (f, rest) => some (.fp f, rest)
                | none =>
                  match decodeVector bs with
                  | some (v, rest) => some (.vec v, rest)
                  | none => none

/-- The unified decoder agrees with the pilot wherever the pilot
    accepts: no existing form is shadowed. -/
theorem decodeExt_kanonisch (bs : List Byte) (d : Decodiert)
    (rest : List Byte) (h : decode bs = some (d, rest)) :
    decodeExt bs = some (.pilot d, rest) := by
  unfold decodeExt
  rw [h]

/-- Where the pilot refuses, a covered narrow row is taken. -/
theorem decodeExt_narrow (bs : List Byte) (n : NarrowDec)
    (rest : List Byte) (h1 : decode bs = none)
    (h2 : decodeNarrow bs = some (n, rest)) :
    decodeExt bs = some (.narrow n, rest) := by
  unfold decodeExt
  rw [h1, h2]

/-- Where pilot and narrow refuse, a covered multiply/divide row is taken. -/
theorem decodeExt_muldiv (bs : List Byte) (m : MulDivDecodiert)
    (rest : List Byte) (h1 : decode bs = none)
    (h2 : decodeNarrow bs = none)
    (h3 : decodeMulDiv bs = some (m, rest)) :
    decodeExt bs = some (.muldiv m, rest) := by
  unfold decodeExt
  rw [h1, h2, h3]

/-- Where pilot, narrow and multiply/divide refuse, a shift row is taken. -/
theorem decodeExt_shift (bs : List Byte) (f : ShiftForm)
    (rest : List Byte) (h1 : decode bs = none)
    (h2 : decodeNarrow bs = none) (h3 : decodeMulDiv bs = none)
    (h4 : decodeShift bs = some (f, rest)) :
    decodeExt bs = some (.shift ⟨f, shiftLaenge f⟩, rest) := by
  unfold decodeExt
  rw [h1, h2, h3, h4]

/-- Where all earlier decoders refuse, a SETcc row is taken. -/
theorem decodeExt_setcc (bs : List Byte) (c : Bedingung) (dst : Register)
    (rest : List Byte) (h1 : decode bs = none)
    (h2 : decodeNarrow bs = none) (h3 : decodeMulDiv bs = none)
    (h4 : decodeShift bs = none)
    (h5 : decodeSetCC bs = some ((c, dst), rest)) :
    decodeExt bs = some (.setcc c dst 4, rest) := by
  unfold decodeExt
  rw [h1, h2, h3, h4, h5]

/-- Where all earlier decoders refuse, a CMOVcc row is taken. -/
theorem decodeExt_cmov (bs : List Byte) (c : Bedingung)
    (dst src : Register) (rest : List Byte) (h1 : decode bs = none)
    (h2 : decodeNarrow bs = none) (h3 : decodeMulDiv bs = none)
    (h4 : decodeShift bs = none) (h5 : decodeSetCC bs = none)
    (h6 : decodeCmov bs = some ((c, dst, src), rest)) :
    decodeExt bs = some (.cmov c dst src 4, rest) := by
  unfold decodeExt
  rw [h1, h2, h3, h4, h5, h6]

/-- Where all earlier decoders refuse, a scalar FP row is taken. -/
theorem decodeExt_fp (bs : List Byte) (f : FpDecodiert)
    (rest : List Byte) (h1 : decode bs = none)
    (h2 : decodeNarrow bs = none) (h3 : decodeMulDiv bs = none)
    (h4 : decodeShift bs = none) (h5 : decodeSetCC bs = none)
    (h6 : decodeCmov bs = none)
    (h7 : fpDecode bs = some (f, rest)) :
    decodeExt bs = some (.fp f, rest) := by
  unfold decodeExt
  rw [h1, h2, h3, h4, h5, h6, h7]

/-- Where all earlier decoders refuse, a packed-integer row is taken. -/
theorem decodeExt_vec (bs : List Byte) (v : VectorDec)
    (rest : List Byte) (h1 : decode bs = none)
    (h2 : decodeNarrow bs = none) (h3 : decodeMulDiv bs = none)
    (h4 : decodeShift bs = none) (h5 : decodeSetCC bs = none)
    (h6 : decodeCmov bs = none) (h7 : fpDecode bs = none)
    (h8 : decodeVector bs = some (v, rest)) :
    decodeExt bs = some (.vec v, rest) := by
  unfold decodeExt
  rw [h1, h2, h3, h4, h5, h6, h7, h8]

/-- Where every decoder refuses, the unified decoder refuses. -/
theorem decodeExt_nichts (bs : List Byte) (h1 : decode bs = none)
    (h2 : decodeNarrow bs = none) (h3 : decodeMulDiv bs = none)
    (h4 : decodeShift bs = none) (h5 : decodeSetCC bs = none)
    (h6 : decodeCmov bs = none) (h7 : fpDecode bs = none)
    (h8 : decodeVector bs = none) :
    decodeExt bs = none := by
  unfold decodeExt
  rw [h1, h2, h3, h4, h5, h6, h7, h8]

/-! ## Pinned rows: one byte string per family through the whole chain.

  Each pin evaluates the COMPLETE fallback chain on closed bytes:
  the pilot refuses every extension row, and the unified decoder
  takes each row exactly once. Cross-family shadowing is refused by
  construction (later arms run only on earlier `none`). -/

/-- Pin: the pilot row decodes through the unified decoder unchanged. -/
theorem pin_ext_pilot_ret :
    decodeExt (encode .ret) = some (.pilot ⟨.ret, 1⟩, []) := by
  have h := roundtrip_ret ([] : List Byte)
  simp [encode] at h
  exact decodeExt_kanonisch _ _ _ h

/-- Pin: the narrow row is refused by the pilot and taken whole. -/
theorem pin_ext_narrow_mov32 :
    decodeExt (encodeNarrow (.mov32rr .rax .rcx)) =
      some (.narrow ⟨.mov32rr .rax .rcx, 3⟩, []) := by
  decide

/-- Pin: the multiply row is refused by the pilot and taken whole. -/
theorem pin_ext_muldiv_mul :
    decodeExt (mulDivEncode (.mulRax .rcx)) =
      some (.muldiv ⟨.mulRax .rcx, 3⟩, []) := by
  decide

/-- Pin: the shift row is refused by the pilot and taken whole. -/
theorem pin_ext_shift_shl :
    decodeExt (encodeShift (.imm .shl .rax 1)) =
      some (.shift ⟨.imm .shl .rax 1, 4⟩, []) := by
  decide

/-- Pin: the SETcc row is refused by the pilot and taken whole. -/
theorem pin_ext_setcc :
    decodeExt (encodeSetCC .e .rax) =
      some (.setcc .e .rax 4, []) := by
  decide

/-- Pin: the CMOVcc row is refused by the pilot and taken whole. -/
theorem pin_ext_cmov :
    decodeExt (encodeCmov .e .rax .rcx) =
      some (.cmov .e .rax .rcx 4, []) := by
  decide

/-- Pin: the scalar FP row is refused by the pilot and taken whole. -/
theorem pin_ext_fp_movsd :
    decodeExt (fpEncodeMovsdRR .xmm0 .xmm1) =
      some (.fp ⟨.movsdRR .xmm0 .xmm1, 4⟩, []) := by
  decide

/-- Pin: the packed-integer row is refused by the pilot and taken whole. -/
theorem pin_ext_vec_pxor :
    decodeExt (encodeVector (.pxorRR .xmm0 .xmm1)) =
      some (.vec ⟨.pxorRR .xmm0 .xmm1, 5⟩, []) := by
  decide

/-- Pin: empty input is refused by the whole chain. -/
theorem pin_ext_nichts_leer : decodeExt [] = none := by
  decide

/-- Pin: an unknown opcode is refused by the whole chain. -/
theorem pin_ext_nichts_unbekannt : decodeExt [natByte 255] = none := by
  decide

/-! ## No shadowing: the pilot refuses every extension witness row.

  Each refusal is evaluated on closed bytes: the unified pins above
  therefore take each row in its own arm, never in the pilot arm. -/

/-- The pilot refuses the narrow witness row. -/
theorem pin_pilot_weist_narrow_zurueck :
    decode (encodeNarrow (.mov32rr .rax .rcx)) = none := by
  decide

/-- The pilot refuses the multiply witness row. -/
theorem pin_pilot_weist_muldiv_zurueck :
    decode (mulDivEncode (.mulRax .rcx)) = none := by
  decide

/-- The pilot refuses the shift witness row (general form in
    `ShiftCodec.pilot_verweigert_shift`; this is its closed instance). -/
theorem pin_pilot_weist_shift_zurueck :
    decode (encodeShift (.imm .shl .rax 1)) = none := by
  decide

/-- The pilot refuses the SETcc witness row. -/
theorem pin_pilot_weist_setcc_zurueck :
    decode (encodeSetCC .e .rax) = none := by
  decide

/-- The pilot refuses the CMOVcc witness row. -/
theorem pin_pilot_weist_cmov_zurueck :
    decode (encodeCmov .e .rax .rcx) = none := by
  decide

/-- The pilot refuses the scalar FP witness row. -/
theorem pin_pilot_weist_fp_zurueck :
    decode (fpEncodeMovsdRR .xmm0 .xmm1) = none := by
  decide

/-- The pilot refuses the packed-integer witness row. -/
theorem pin_pilot_weist_vec_zurueck :
    decode (encodeVector (.pxorRR .xmm0 .xmm1)) = none := by
  decide



/-! ## One step: exact evaluation selection over the accepted helpers.

  The pilot runs through the accepted lift (`laufAlt`); narrow,
  shift, multiply/divide, SETcc and CMOVcc run their accepted
  evaluator on the `kern` half; scalar FP and packed integer run
  their accepted step on the whole `FpZustand`. Nothing is
  redefined here: every arm names its helper. -/

/-- Unified step outcome: success carries the successor, `halt` is the
    hardware trap (divide error), `verweigert` is an explicit refusal.
    There is no silent halt and no termination constructor. -/
inductive ExtAusgang where
  | weiter : FpZustand → ExtAusgang
  | halt : ExtAusgang
  | verweigert : ExtAusgang

/-- One unified step on the extended state under the selected
    readiness profile. `none` of any helper is `verweigert`; the
    divide trap is `halt`. -/
def stepExt (i : ExtInstr) (t : FpZustand) (b : BereitProfil) : ExtAusgang :=
  match i with
  | .pilot d =>
    match laufAlt d t with
    | some t' => .weiter t'
    | none => .verweigert
  | .narrow n =>
    match stepNarrow n t.kern with
    | some s' => .weiter { t with kern := s' }
    | none => .verweigert
  | .muldiv m =>
    match mulDivSchritt m t.kern with
    | .ok s' => .weiter { t with kern := s' }
    | .hardwareHalt => .halt
    | .misslungen => .verweigert
  | .shift d =>
    match shiftSchritt d t.kern with
    | some s' => .weiter { t with kern := s' }
    | none => .verweigert
  | .setcc c dst l =>
    match setccSchrittBytes l t.kern dst c with
    | some s' => .weiter { t with kern := s' }
    | none => .verweigert
  | .cmov c dst src l =>
    match cmovSchrittBytes l t.kern dst src c with
    | some s' => .weiter { t with kern := s' }
    | none => .verweigert
  | .fp f =>
    match fpSchritt f t with
    | some t' => .weiter t'
    | none => .verweigert
  | .vec v =>
    match stepVector v t b with
    | some t' => .weiter t'
    | none => .verweigert

/-- Selection: the pilot arm IS the accepted lift. -/
theorem stepExt_pilot (d : Decodiert) (t t' : FpZustand)
    (b : BereitProfil) (h : laufAlt d t = some t') :
    stepExt (.pilot d) t b = .weiter t' := by
  have e : stepExt (.pilot d) t b =
      match laufAlt d t with
      | some t' => ExtAusgang.weiter t'
      | none => .verweigert := rfl
  rw [e, h]

/-- Selection: pilot refusal is unified refusal. -/
theorem stepExt_pilot_verweigert (d : Decodiert) (t : FpZustand)
    (b : BereitProfil) (h : laufAlt d t = none) :
    stepExt (.pilot d) t b = .verweigert := by
  have e : stepExt (.pilot d) t b =
      match laufAlt d t with
      | some t' => ExtAusgang.weiter t'
      | none => .verweigert := rfl
  rw [e, h]

/-- Selection: the narrow arm IS the accepted narrow evaluator. -/
theorem stepExt_narrow (n : NarrowDec) (t : FpZustand)
    (b : BereitProfil) (s' : Zustand)
    (h : stepNarrow n t.kern = some s') :
    stepExt (.narrow n) t b = .weiter { t with kern := s' } := by
  have e : stepExt (.narrow n) t b =
      match stepNarrow n t.kern with
      | some s' => ExtAusgang.weiter { t with kern := s' }
      | none => .verweigert := rfl
  rw [e, h]

/-- Selection: narrow refusal is unified refusal. -/
theorem stepExt_narrow_verweigert (n : NarrowDec) (t : FpZustand)
    (b : BereitProfil) (h : stepNarrow n t.kern = none) :
    stepExt (.narrow n) t b = .verweigert := by
  have e : stepExt (.narrow n) t b =
      match stepNarrow n t.kern with
      | some s' => ExtAusgang.weiter { t with kern := s' }
      | none => .verweigert := rfl
  rw [e, h]

/-- Selection: the multiply/divide arm IS the accepted evaluator. -/
theorem stepExt_muldiv_ok (m : MulDivDecodiert) (t : FpZustand)
    (b : BereitProfil) (s' : Zustand)
    (h : mulDivSchritt m t.kern = .ok s') :
    stepExt (.muldiv m) t b = .weiter { t with kern := s' } := by
  have e : stepExt (.muldiv m) t b =
      match mulDivSchritt m t.kern with
      | .ok s' => ExtAusgang.weiter { t with kern := s' }
      | .hardwareHalt => .halt
      | .misslungen => .verweigert := rfl
  rw [e, h]

/-- Selection: the divide trap IS the unified halt. -/
theorem stepExt_muldiv_halt (m : MulDivDecodiert) (t : FpZustand)
    (b : BereitProfil)
    (h : mulDivSchritt m t.kern = .hardwareHalt) :
    stepExt (.muldiv m) t b = .halt := by
  have e : stepExt (.muldiv m) t b =
      match mulDivSchritt m t.kern with
      | .ok s' => ExtAusgang.weiter { t with kern := s' }
      | .hardwareHalt => .halt
      | .misslungen => .verweigert := rfl
  rw [e, h]

/-- Selection: multiply/divide refusal is unified refusal. -/
theorem stepExt_muldiv_misslungen (m : MulDivDecodiert) (t : FpZustand)
    (b : BereitProfil)
    (h : mulDivSchritt m t.kern = .misslungen) :
    stepExt (.muldiv m) t b = .verweigert := by
  have e : stepExt (.muldiv m) t b =
      match mulDivSchritt m t.kern with
      | .ok s' => ExtAusgang.weiter { t with kern := s' }
      | .hardwareHalt => .halt
      | .misslungen => .verweigert := rfl
  rw [e, h]

/-- Selection: the shift arm IS the accepted shift evaluator. -/
theorem stepExt_shift (d : ShiftDecodiert) (t : FpZustand)
    (b : BereitProfil) (s' : Zustand)
    (h : shiftSchritt d t.kern = some s') :
    stepExt (.shift d) t b = .weiter { t with kern := s' } := by
  have e : stepExt (.shift d) t b =
      match shiftSchritt d t.kern with
      | some s' => ExtAusgang.weiter { t with kern := s' }
      | none => .verweigert := rfl
  rw [e, h]

/-- Selection: shift refusal is unified refusal. -/
theorem stepExt_shift_verweigert (d : ShiftDecodiert) (t : FpZustand)
    (b : BereitProfil) (h : shiftSchritt d t.kern = none) :
    stepExt (.shift d) t b = .verweigert := by
  have e : stepExt (.shift d) t b =
      match shiftSchritt d t.kern with
      | some s' => ExtAusgang.weiter { t with kern := s' }
      | none => .verweigert := rfl
  rw [e, h]

/-- Selection: the SETcc arm IS the accepted byte step. -/
theorem stepExt_setcc (c : Bedingung) (dst : Register) (l : Nat)
    (t : FpZustand) (b : BereitProfil) (s' : Zustand)
    (h : setccSchrittBytes l t.kern dst c = some s') :
    stepExt (.setcc c dst l) t b = .weiter { t with kern := s' } := by
  have e : stepExt (.setcc c dst l) t b =
      match setccSchrittBytes l t.kern dst c with
      | some s' => ExtAusgang.weiter { t with kern := s' }
      | none => .verweigert := rfl
  rw [e, h]

/-- Selection: SETcc refusal is unified refusal. -/
theorem stepExt_setcc_verweigert (c : Bedingung) (dst : Register)
    (l : Nat) (t : FpZustand) (b : BereitProfil)
    (h : setccSchrittBytes l t.kern dst c = none) :
    stepExt (.setcc c dst l) t b = .verweigert := by
  have e : stepExt (.setcc c dst l) t b =
      match setccSchrittBytes l t.kern dst c with
      | some s' => ExtAusgang.weiter { t with kern := s' }
      | none => .verweigert := rfl
  rw [e, h]

/-- Selection: the CMOVcc arm IS the accepted byte step. -/
theorem stepExt_cmov (c : Bedingung) (dst src : Register) (l : Nat)
    (t : FpZustand) (b : BereitProfil) (s' : Zustand)
    (h : cmovSchrittBytes l t.kern dst src c = some s') :
    stepExt (.cmov c dst src l) t b =
      .weiter { t with kern := s' } := by
  have e : stepExt (.cmov c dst src l) t b =
      match cmovSchrittBytes l t.kern dst src c with
      | some s' => ExtAusgang.weiter { t with kern := s' }
      | none => .verweigert := rfl
  rw [e, h]

/-- Selection: CMOVcc refusal is unified refusal. -/
theorem stepExt_cmov_verweigert (c : Bedingung) (dst src : Register)
    (l : Nat) (t : FpZustand) (b : BereitProfil)
    (h : cmovSchrittBytes l t.kern dst src c = none) :
    stepExt (.cmov c dst src l) t b = .verweigert := by
  have e : stepExt (.cmov c dst src l) t b =
      match cmovSchrittBytes l t.kern dst src c with
      | some s' => ExtAusgang.weiter { t with kern := s' }
      | none => .verweigert := rfl
  rw [e, h]

/-- Selection: the scalar FP arm IS the accepted FP step. -/
theorem stepExt_fp (f : FpDecodiert) (t t' : FpZustand)
    (b : BereitProfil) (h : fpSchritt f t = some t') :
    stepExt (.fp f) t b = .weiter t' := by
  have e : stepExt (.fp f) t b =
      match fpSchritt f t with
      | some t' => ExtAusgang.weiter t'
      | none => .verweigert := rfl
  rw [e, h]

/-- Selection: scalar FP refusal is unified refusal. -/
theorem stepExt_fp_verweigert (f : FpDecodiert) (t : FpZustand)
    (b : BereitProfil) (h : fpSchritt f t = none) :
    stepExt (.fp f) t b = .verweigert := by
  have e : stepExt (.fp f) t b =
      match fpSchritt f t with
      | some t' => ExtAusgang.weiter t'
      | none => .verweigert := rfl
  rw [e, h]

/-- Selection: the packed-integer arm IS the accepted vector step. -/
theorem stepExt_vec (v : VectorDec) (t t' : FpZustand)
    (b : BereitProfil) (h : stepVector v t b = some t') :
    stepExt (.vec v) t b = .weiter t' := by
  have e : stepExt (.vec v) t b =
      match stepVector v t b with
      | some t' => ExtAusgang.weiter t'
      | none => .verweigert := rfl
  rw [e, h]

/-- Selection: packed-integer refusal is unified refusal. -/
theorem stepExt_vec_verweigert (v : VectorDec) (t : FpZustand)
    (b : BereitProfil) (h : stepVector v t b = none) :
    stepExt (.vec v) t b = .verweigert := by
  have e : stepExt (.vec v) t b =
      match stepVector v t b with
      | some t' => ExtAusgang.weiter t'
      | none => .verweigert := rfl
  rw [e, h]

/-! ## Fetch and byte-step from actual executable memory.

  The fetched window is the state's ACTUAL bytes at `rip`
  (`Byteschritt.geholt`: executable prefix only, capped at 15).
  Admission checks the consumed length against the fetched window,
  the decode-length guard, and execute permission of the consumed
  prefix -- exactly the `fetchDekodiert` discipline, lifted to the
  unified decoder. No caller-supplied decoded value ever becomes a
  trusted fetch. -/

/-- Unified admission: consumed length plus remaining suffix is the
    fetched window, the length passes the guard, and the consumed
    prefix is executable. -/
def extZugelassen (t : FpZustand) (fenster : List Byte) (i : ExtInstr)
    (rest : List Byte) : Bool :=
  decide (extLen i + rest.length = fenster.length) &&
    laengeOk (extLen i) &&
    ausfuehrbarN t.kern.speicher t.kern.rip (extLen i)

/-- Admission carries the length equation. -/
theorem extZugelassen_summe (t : FpZustand) (fenster : List Byte)
    (i : ExtInstr) (rest : List Byte)
    (h : extZugelassen t fenster i rest = true) :
    extLen i + rest.length = fenster.length := by
  unfold extZugelassen at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hsum, _⟩, _⟩ := h
  exact of_decide_eq_true hsum

/-- Admission carries the length guard. -/
theorem extZugelassen_laenge (t : FpZustand) (fenster : List Byte)
    (i : ExtInstr) (rest : List Byte)
    (h : extZugelassen t fenster i rest = true) :
    laengeOk (extLen i) = true := by
  unfold extZugelassen at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨_, hlen⟩, _⟩ := h
  exact hlen

/-- Admission carries execute permission of the consumed prefix. -/
theorem extZugelassen_ausfuehrbar (t : FpZustand) (fenster : List Byte)
    (i : ExtInstr) (rest : List Byte)
    (h : extZugelassen t fenster i rest = true) :
    ausfuehrbarN t.kern.speicher t.kern.rip (extLen i) = true := by
  unfold extZugelassen at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨_, hexe⟩ := h
  exact hexe

/-- Fetch and decode: the unified decoder over the given window,
    gated by unified admission. The second arm binds the pair whole
    (no pattern shadowing) so the admission evidence stays exact. -/
def fetchExt (t : FpZustand) (fenster : List Byte) :
    Option (ExtInstr × List Byte) :=
  match decodeExt fenster with
  | none => none
  | some p =>
    if extZugelassen t fenster p.1 p.2 then some p else none

/-- A successful fetch decodes to the admitted instruction: length
    equation, length guard and execute permission all hold. -/
theorem fetchExt_erfolg (t : FpZustand) (fenster : List Byte)
    (i : ExtInstr) (rest : List Byte)
    (h : fetchExt t fenster = some (i, rest)) :
    decodeExt fenster = some (i, rest) ∧
      extLen i + rest.length = fenster.length ∧
      laengeOk (extLen i) = true ∧
      ausfuehrbarN t.kern.speicher t.kern.rip (extLen i) = true := by
  have e : fetchExt t fenster =
      match decodeExt fenster with
      | none => (none : Option (ExtInstr × List Byte))
      | some p =>
        if extZugelassen t fenster p.1 p.2 then some p else none := rfl
  rw [e] at h
  cases hdec : decodeExt fenster with
  | none =>
    simp [hdec] at h
  | some p =>
    rw [hdec] at h
    by_cases hz : extZugelassen t fenster p.1 p.2 = true
    · simp [hz] at h
      rw [h] at hz
      exact ⟨by rw [h],
        extZugelassen_summe t fenster _ _ hz,
        extZugelassen_laenge t fenster _ _ hz,
        extZugelassen_ausfuehrbar t fenster _ _ hz⟩
    · simp [hz] at h

/-- One byte step from actual memory: fetch, decode, then the unified
    step. Takes ONLY the state and the readiness profile: a forged
    `ExtInstr` cannot inject an instruction. Any fetch or step
    failure is `verweigert`; the divide trap is `halt`. -/
def extByteschritt (t : FpZustand) (b : BereitProfil) : ExtAusgang :=
  match fetchExt t (geholt t.kern) with
  | none => .verweigert
  | some (i, _) => stepExt i t b

/-- Selection: a fetched instruction steps through the unified step. -/
theorem extByteschritt_weiter (t : FpZustand) (b : BereitProfil)
    (i : ExtInstr) (rest : List Byte) (o : ExtAusgang)
    (hf : fetchExt t (geholt t.kern) = some (i, rest))
    (hs : stepExt i t b = o) :
    extByteschritt t b = o := by
  have e : extByteschritt t b =
      match fetchExt t (geholt t.kern) with
      | none => ExtAusgang.verweigert
      | some (j, _) => stepExt j t b := rfl
  rw [e, hf]
  exact hs

/-- Selection: fetch refusal is byte-step refusal. -/
theorem extByteschritt_verweigert (t : FpZustand) (b : BereitProfil)
    (hf : fetchExt t (geholt t.kern) = none) :
    extByteschritt t b = .verweigert := by
  have e : extByteschritt t b =
      match fetchExt t (geholt t.kern) with
      | none => ExtAusgang.verweigert
      | some (j, _) => stepExt j t b := rfl
  rw [e, hf]

/-! ## Reached witness: a mixed pilot-integer/scalar-FP run from bytes.

  The image holds two instructions back to back: a pilot `store64`
  (7 bytes) and a scalar-FP `movsdSpeichere` (8 bytes). Both are
  fetched from ACTUAL executable memory, decoded through the unified
  chain, and both change ACTUAL data memory. The second store lands
  only because RIP advanced past the first instruction's exact
  length. -/

/-- Witness image: pilot store (cell 1) then FP store (cell 2). -/
def extWitBild : List Byte :=
  encode (.store64 .rbx .rax (BitVec.ofNat 32 0)) ++
    fpEncodeMovsdSpeichere .rcx .xmm0 (BitVec.ofNat 32 0)

/-- Witness code bytes: the image at 4096, zeroes elsewhere. -/
def extWitBytes (a : Adresse) : Byte :=
  if a.toNat < 4096 then BitVec.ofNat 8 0
  else
    match extWitBild[a.toNat - 4096]? with
    | some b => b
    | none => BitVec.ofNat 8 0

/-- Witness execute permission: exactly the 15 image bytes. -/
def extWitCode (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4096 + 15)

/-- Witness data permission: two eight-byte cells at 8192. -/
def extWitDaten (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8192 + 16)

/-- Witness memory: code is execute-only, data read/write-only. Fetch
    therefore uses execute permission alone, never data-read. -/
def extWitSpeicher : Speicher :=
  { bytes := extWitBytes, lesbar := extWitDaten,
    schreibbar := extWitDaten, ausfuehrbar := extWitCode }

/-- Witness registers: the value in rax, cell addresses in rbx/rcx. -/
def extWitReg : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 42
  else if q = Register.rbx then BitVec.ofNat 64 8192
  else if q = Register.rcx then BitVec.ofNat 64 8200
  else if q = Register.rsp then BitVec.ofNat 64 8704
  else BitVec.ofNat 64 0

/-- Witness XMM file: the value as a double-word in xmm0. -/
def extWitXmm : XmmDatei := fun q =>
  if q = .xmm0 then vecJoin (BitVec.ofNat 64 42) (BitVec.ofNat 64 0)
  else (BitVec.ofNat 128 0)

/-- Witness core state: code at 4096. -/
def extWitKern : Zustand :=
  { register := extWitReg, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := extWitSpeicher }

/-- Witness start state: reset FP control word (admitted profile). -/
def extWitStart : FpZustand := ⟨extWitKern, extWitXmm, kontextReset⟩

/-- Witness readiness: OS vector state present. -/
def extWitBereit : BereitProfil := ⟨kontextReset.mxcsr, true⟩

/-- Read one data byte out of a step outcome. -/
def extZelle (o : ExtAusgang) (a : Adresse) : Option Byte :=
  match o with
  | .weiter t => some (t.kern.speicher.bytes a)
  | _ => none

/-- Read RIP out of a step outcome. -/
def extRip (o : ExtAusgang) : Option Wort :=
  match o with
  | .weiter t => some t.kern.rip
  | _ => none

/-- Two byte-steps in sequence; refusal or trap stops the run. -/
def extSchritt2 (t : FpZustand) (b : BereitProfil) : ExtAusgang :=
  match extByteschritt t b with
  | .weiter t1 => extByteschritt t1 b
  | x => x

/-- First step: the pilot store lands 42 in cell 1, from fetched bytes. -/
theorem extWit_erster_speichert :
    extZelle (extByteschritt extWitStart extWitBereit)
      (BitVec.ofNat 64 8192) = some (BitVec.ofNat 8 42) := by
  decide

/-- Both steps: cell 1 and cell 2 hold 42 after the reached run. -/
theorem extWit_zwei_schritte_speichern :
    extZelle (extSchritt2 extWitStart extWitBereit)
        (BitVec.ofNat 64 8192) = some (BitVec.ofNat 8 42) ∧
      extZelle (extSchritt2 extWitStart extWitBereit)
        (BitVec.ofNat 64 8200) = some (BitVec.ofNat 8 42) := by
  decide

/-- The run advances RIP past both instructions: 4096 + 7 + 8. -/
theorem extWit_rip_nach_zwei :
    extRip (extSchritt2 extWitStart extWitBereit) =
      some (BitVec.ofNat 64 4111) := by
  decide

/-- The start cells read zero: the run really changes memory. -/
theorem extWit_anfang_null :
    extWitStart.kern.speicher.bytes (BitVec.ofNat 64 8192) =
        BitVec.ofNat 8 0 ∧
      extWitStart.kern.speicher.bytes (BitVec.ofNat 64 8200) =
        BitVec.ofNat 8 0 := by
  decide

/-! ## Planted refusals: unsupported bytes and unadmitted profiles. -/

/-- Past the image there is nothing executable: fetch refuses. -/
theorem extWit_nachBild_verweigert :
    extByteschritt
      { extWitStart with kern :=
        { extWitKern with rip := BitVec.ofNat 64 4111 } }
      extWitBereit = .verweigert := by
  rfl

/-- Readiness without OS vector state. -/
def extWitUnbereit : BereitProfil := ⟨kontextReset.mxcsr, false⟩

/-- Without OS vector state the packed-integer arm refuses, in every
    state: validator admission, never a hardware fault. -/
theorem extWit_vec_ohne_os_verweigert (t : FpZustand) :
    stepExt (.vec ⟨.pxorRR .xmm0 .xmm1, 5⟩) t extWitUnbereit =
      .verweigert := by
  apply stepExt_vec_verweigert
  apply stepVector_profil_verweigert
  · rfl
  · rfl

/-- Joint witness: the reached two-step run changes two ACTUAL memory
    cells from fetched bytes, advances RIP past both instructions,
    starts from zeroed cells -- and past the image the same stepper
    refuses. Non-degenerate: a store-changing reached execution plus
    a planted refusal, jointly instantiated. -/
theorem extWit_zwei_schritte_zeuge :
    extZelle (extSchritt2 extWitStart extWitBereit)
          (BitVec.ofNat 64 8192) = some (BitVec.ofNat 8 42) ∧
      extZelle (extSchritt2 extWitStart extWitBereit)
          (BitVec.ofNat 64 8200) = some (BitVec.ofNat 8 42) ∧
      extRip (extSchritt2 extWitStart extWitBereit) =
        some (BitVec.ofNat 64 4111) ∧
      extWitStart.kern.speicher.bytes (BitVec.ofNat 64 8192) =
        BitVec.ofNat 8 0 ∧
      extByteschritt
          { extWitStart with kern :=
            { extWitKern with rip := BitVec.ofNat 64 4111 } }
          extWitBereit = .verweigert := by
  refine ⟨extWit_zwei_schritte_speichern.1,
    extWit_zwei_schritte_speichern.2, extWit_rip_nach_zwei,
    extWit_anfang_null.1, extWit_nachBild_verweigert⟩

/- CUTS:
   Proved here: ONE unified byte-facing execution path over the
   accepted helpers -- the pilot (`Codec.decode` /
   `Ausfuehrung.schritt`, all 14 forms) plus narrow, multiply/divide,
   shift, SETcc/CMOVcc, scalar SSE2 DOUBLE and packed integer, each
   through its accepted decoder and evaluator only. Dispatch is the
   sequential fallback (`decodeExt_*`): the pilot is never shadowed,
   pinned per family with pilot-refusal evidence. Exact evaluation
   selection (`stepExt_*`): the old evaluator is lifted, never
   redefined. Fetch and execute permission follow the `fetchDekodiert`
   discipline (`fetchExt_erfolg`); a mixed pilot/FP reached run
   changes actual memory from fetched bytes with a joint witness and
   planted refusals.
   NOT proved here, and not claimed:
   - No hardware correspondence: encodings are the stated canonical
     subsets with self-consistency only, not x86 truth.
   - No LOCK prefix, no SIMD beyond PXOR/PADDQ and the four scalar
     DOUBLE byte rows, no source/IR correspondence, no TSO/W/GX
     bridge, no ABI/loader/entry/budget connection.
   - High XMM registers and REX-extended FP/vector forms are refused
     by absence (inherited from the accepted codecs).
   - The divide trap (`halt`) is a named hardware outcome carried,
     not a proved silicon behaviour.
-/

#print axioms decodeExt
#print axioms stepExt
#print axioms fetchExt
#print axioms extByteschritt
#print axioms fetchExt_erfolg
#print axioms extWit_zwei_schritte_speichern
#print axioms extWit_zwei_schritte_zeuge
#print axioms extWit_vec_ohne_os_verweigert

end Gabbro.Grammatik.X86