/-
  File:      Grammatik/X86/StringOps.lean
  Subject:   String instructions with REP prefixes and the direction flag
              (MOVS/STOS/LODS/SCAS/CMPS, CLD/STD) over the coherent machine.

  Lane 1361: decoder + encoder (round trip), TSO-sequence semantics
  (per element: load then store, precise fault state), the DF-augmented
  extended step embedding `HwSchritt` fragments, and a reached two-core
  witness with owner-only forwarding and a memory-changing drain.
  Accepted definitions are reused unchanged, never redefined (see CUTS).
-/
import Grammatik.X86.Kern.Typen
import Grammatik.X86.Kern.Codec
import Grammatik.X86.Speicher.Speicher
import Grammatik.X86.TSO.Kern.TSO
import Grammatik.X86.Kern.Ausfuehrung
import Grammatik.X86.Befehle.Arithmetik.NarrowOps
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Hw.Kapstein.HwKapsteinDecoder

namespace Gabbro.Grammatik.X86

/-- String operation kind: the five A4-AF memory forms. -/
inductive StrOp where
  | movs | stos | lods | scas | cmps
  deriving DecidableEq, Repr, Inhabited

/-- REP prefix: none, F3 (REP; on CMPS/SCAS this carries REPE
    semantics), F2 (REPNE). F3 has no separate REPE encoding. -/
inductive RepPraefix where
  | kein | rep | repne
  deriving DecidableEq, Repr, Inhabited

/-- One decoded string instruction: op, width, REP prefix, length. -/
structure StrDecodiert where
  op : StrOp
  breite : Breite
  rep : RepPraefix
  laenge : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Direction-flag instructions CLD (FC) and STD (FD). -/
inductive StrDirOp where
  | cld | std
  deriving DecidableEq, Repr, Inhabited

/-- Family instruction: a string op or a direction-flag op. -/
inductive StrInstr where
  | str : StrDecodiert → StrInstr
  | dir : StrDirOp → Nat → StrInstr
  deriving DecidableEq, Repr, Inhabited

/-! ## 1. Decoder: optional F2/F3, optional 66H, optional REX,
    then the A4-AF opcode or FC/FD. LOCK (F0) refuses; doubled
    prefixes, 66H/REX on byte opcodes and prefixed CLD/STD refuse.
    REX.W overrides 66H; other REX bits are accepted and ignored
    (no register field exists on these opcodes). -/

/-- Canonical opcode byte of a string op in its byte form. -/
def strOpcodeB8 : StrOp → Nat
  | .movs => 164 | .cmps => 166 | .stos => 170 | .lods => 172
  | .scas => 174

/-- Canonical opcode byte of a string op in its sized form. -/
def strOpcodeSized : StrOp → Nat
  | .movs => 165 | .cmps => 167 | .stos => 171 | .lods => 173
  | .scas => 175

/-- Width of a sized string op: REX.W wins over 66H, else 32 bit. -/
def strSizedBreite (opSize rexW : Bool) : Breite :=
  if rexW then .b64 else if opSize then .b16 else .b32

/-- Opcode dispatch shared by every prefix shape. -/
def strDecodeOp (pfx : RepPraefix) (opSize rexW : Bool) (len : Nat)
    (opc : Nat) (rest : List Byte) : Option (StrInstr × List Byte) :=
  match opc with
  | 164 => if opSize || rexW then none
      else some (.str ⟨.movs, .b8, pfx, len⟩, rest)
  | 165 => some (.str ⟨.movs, strSizedBreite opSize rexW, pfx, len⟩, rest)
  | 166 => if opSize || rexW then none
      else some (.str ⟨.cmps, .b8, pfx, len⟩, rest)
  | 167 => some (.str ⟨.cmps, strSizedBreite opSize rexW, pfx, len⟩, rest)
  | 170 => if opSize || rexW then none
      else some (.str ⟨.stos, .b8, pfx, len⟩, rest)
  | 171 => some (.str ⟨.stos, strSizedBreite opSize rexW, pfx, len⟩, rest)
  | 172 => if opSize || rexW then none
      else some (.str ⟨.lods, .b8, pfx, len⟩, rest)
  | 173 => some (.str ⟨.lods, strSizedBreite opSize rexW, pfx, len⟩, rest)
  | 174 => if opSize || rexW then none
      else some (.str ⟨.scas, .b8, pfx, len⟩, rest)
  | 175 => some (.str ⟨.scas, strSizedBreite opSize rexW, pfx, len⟩, rest)
  | 252 =>
    match pfx with
    | .kein =>
      if opSize || rexW then none else some (.dir .cld len, rest)
    | _ => none
  | 253 =>
    match pfx with
    | .kein =>
      if opSize || rexW then none else some (.dir .std len, rest)
    | _ => none
  | _ => none

/-- Byte decoder for the string family. -/
def strDecode : List Byte → Option (StrInstr × List Byte)
  | [] => none
  | b0 :: rest0 =>
    if byteNat b0 == 240 then none
    else
      let pfx : RepPraefix :=
        if byteNat b0 == 243 then .rep
        else if byteNat b0 == 242 then .repne else .kein
      let rest1 : List Byte :=
        if byteNat b0 == 243 || byteNat b0 == 242 then rest0
        else b0 :: rest0
      let nrep : Nat :=
        if byteNat b0 == 243 || byteNat b0 == 242 then 1 else 0
      match rest1 with
      | [] => none
      | b1 :: rest2 =>
        let opSize : Bool := byteNat b1 == 102
        let rest3 : List Byte :=
          if opSize then rest2 else b1 :: rest2
        let n66 : Nat := if opSize then 1 else 0
        match rest3 with
        | [] => none
        | b2 :: rest4 =>
          let isRex : Bool := decide (64 ≤ byteNat b2 ∧ byteNat b2 < 80)
          -- The W bit counts only on a real REX byte: reading it off
          -- the opcode byte refuses valid forms (found by round trip).
          let rexW : Bool := isRex && decide (8 ≤ byteNat b2 % 16)
          let rest5 : List Byte :=
            if isRex then rest4 else b2 :: rest4
          let nrex : Nat := if isRex then 1 else 0
          match rest5 with
          | [] => none
          | opc :: rest6 =>
            strDecodeOp pfx opSize rexW (nrep + n66 + nrex + 1)
              (byteNat opc) rest6

/-! ## 2. Encoder (round trip), decode pins and planted refusals. -/

/-- Canonical encoding of one string op: REP prefix, width prefix,
    opcode. Byte form takes no width prefix. -/
def strEncodeD (op : StrOp) (b : Breite) (pfx : RepPraefix) : List Byte :=
  let pre : List Byte :=
    match pfx with
    | .kein => [] | .rep => [natByte 243] | .repne => [natByte 242]
  let wpre : List Byte :=
    match b with
    | .b8 => [] | .b16 => [natByte 102] | .b32 => [] | .b64 => [natByte 72]
  let opc : Nat :=
    match b with
    | .b8 => strOpcodeB8 op | _ => strOpcodeSized op
  pre ++ wpre ++ [natByte opc]

/-- Canonical encoding of a family instruction. -/
def strEncode : StrInstr → List Byte
  | .str d => strEncodeD d.op d.breite d.rep
  | .dir .cld _ => [natByte 252]
  | .dir .std _ => [natByte 253]

/-- Round trip: every canonical encoding decodes to itself. -/
theorem strRoundtrip (op : StrOp) (b : Breite) (pfx : RepPraefix)
    (rest : List Byte) :
    strDecode (strEncodeD op b pfx ++ rest) =
      some (.str ⟨op, b, pfx, (strEncodeD op b pfx).length⟩, rest) := by
  cases op <;> cases b <;> cases pfx <;> rfl

/-- CLD decodes from its byte. -/
theorem strPin_cld (rest : List Byte) :
    strDecode ([natByte 252] ++ rest) = some (.dir .cld 1, rest) := rfl

/-- STD decodes from its byte. -/
theorem strPin_std (rest : List Byte) :
    strDecode ([natByte 253] ++ rest) = some (.dir .std 1, rest) := rfl

/-- REP MOVSB decodes with length 2. -/
theorem strPin_rep_movsb (rest : List Byte) :
    strDecode ([natByte 243, natByte 164] ++ rest) =
      some (.str ⟨.movs, .b8, .rep, 2⟩, rest) := rfl

/-- REX.W MOVSQ decodes with length 2. -/
theorem strPin_movsq (rest : List Byte) :
    strDecode ([natByte 72, natByte 165] ++ rest) =
      some (.str ⟨.movs, .b64, .kein, 2⟩, rest) := rfl

/-- 66H CMPSW decodes with length 2. -/
theorem strPin_cmpsw (rest : List Byte) :
    strDecode ([natByte 102, natByte 167] ++ rest) =
      some (.str ⟨.cmps, .b16, .kein, 2⟩, rest) := rfl

/-- REPNE SCASB decodes with length 2. -/
theorem strPin_repne_scasb (rest : List Byte) :
    strDecode ([natByte 242, natByte 174] ++ rest) =
      some (.str ⟨.scas, .b8, .repne, 2⟩, rest) := rfl

/-- Empty input refuses. -/
theorem strNichts_leer : strDecode [] = none := rfl

/-- A non-string opcode refuses. -/
theorem strNichts_nop : strDecode [natByte 144] = none := rfl

/-- LOCK on a string op refuses. -/
theorem strNichts_lock : strDecode [natByte 240, natByte 164] = none := rfl

/-- A lone REP prefix refuses. -/
theorem strNichts_rep_allein : strDecode [natByte 243] = none := rfl

/-- A doubled REP prefix refuses. -/
theorem strNichts_rep_doppelt :
    strDecode [natByte 243, natByte 242, natByte 164] = none := rfl

/-- A REP-prefixed CLD refuses. -/
theorem strNichts_rep_cld : strDecode [natByte 243, natByte 252] = none :=
  rfl

/-- A width prefix on a byte opcode refuses. -/
theorem strNichts_66_byte : strDecode [natByte 102, natByte 164] = none :=
  rfl

/- CUTS:
   Skeleton only: vocabulary above. Decoder, semantics, adapter and
   witness follow. NOT proved here: everything (see lane report).
-/

#print axioms StrDecodiert

end Gabbro.Grammatik.X86
