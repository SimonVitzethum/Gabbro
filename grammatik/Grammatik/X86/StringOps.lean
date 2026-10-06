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

/-! ## 3. Semantics: one element is a TSO load/store sequence.
    Widths reuse `Breite.bytes`; register merges reuse the accepted
    `mergeRegNarrow` (8/16-bit merge, 32-bit zero-extends, 64-bit
    whole); only ZF is modelled for the comparing ops (CF/SF/OF/PF/AF
    stay FREE, see CUTS). -/

/-- Little-endian assembly of a byte list into a word. -/
def wortAusBytes : List Byte → Wort
  | [] => BitVec.ofNat 64 0
  | b :: rest => BitVec.ofNat 64 b.toNat + 256 * wortAusBytes rest

/-- Little-endian split of the low `w` bytes of a word. -/
def wortZuBytes : Wort → Nat → List Byte
  | _, 0 => []
  | v, n + 1 => BitVec.ofNat 8 v.toNat :: wortZuBytes (v >>> 8) n

/-- Load `w` consecutive bytes ascending from `a` through TSO
    (owner forwarding included, `none` = unreadable). -/
def strLadeAux (s : TSOZustand) (c : Nat) (a : Adresse) (i w : Nat) :
    Option (List Byte) :=
  match w with
  | 0 => some []
  | n + 1 =>
    match loadByte s c (addrOff a i) with
    | none => none
    | some b =>
      match strLadeAux s c a (i + 1) n with
      | none => none
      | some rest => some (b :: rest)

/-- Issue a byte list ascending at `a` through TSO (`none` = fault). -/
def strGebeAux (s : TSOZustand) (c : Nat) (a : Adresse) : List Byte →
    Nat → Option TSOZustand
  | [], _ => some s
  | b :: rest, i =>
    match issueByte s c (addrOff a i) b with
    | none => none
    | some s1 => strGebeAux s1 c a rest (i + 1)

/-- One string element: per element a load then a store through TSO.
    Returns the new TSO state, the new RAX and a ZF update (`none` =
    the op leaves ZF alone). `none` = the faulting access refused. -/
def strElement (d : StrDecodiert) (rsi rdi : Adresse) (rax : Wort)
    (s : TSOZustand) (c : Nat) :
    Option (TSOZustand × Wort × Option Bool) :=
  let w := d.breite.bytes
  match d.op with
  | .movs =>
    match strLadeAux s c rsi 0 w with
    | none => none
    | some vs =>
      match strGebeAux s c rdi vs 0 with
      | none => none
      | some s1 => some (s1, rax, none)
  | .stos =>
    match strGebeAux s c rdi (wortZuBytes rax w) 0 with
    | none => none
    | some s1 => some (s1, rax, none)
  | .lods =>
    match strLadeAux s c rsi 0 w with
    | none => none
    | some vs =>
      some (s, mergeRegNarrow d.breite rax (wortAusBytes vs), none)
  | .scas =>
    match strLadeAux s c rdi 0 w with
    | none => none
    | some vs => some (s, rax, some (decide (vs = wortZuBytes rax w)))
  | .cmps =>
    match strLadeAux s c rsi 0 w with
    | none => none
    | some vs1 =>
      match strLadeAux s c rdi 0 w with
      | none => none
      | some vs2 => some (s, rax, some (decide (vs1 = vs2)))

/-- String registers threaded through a run. -/
structure StrReg where
  rsi : Adresse
  rdi : Adresse
  rcx : Wort
  rax : Wort
  deriving DecidableEq, Repr, Inhabited

/-- Pointer step for one element: DF sets the sign, width the stride. -/
def strSchrittZeiger (df : Bool) (p : Adresse) (w : Nat) : Adresse :=
  if df then p - BitVec.ofNat 64 w else p + BitVec.ofNat 64 w

/-- Forward step steps toward smaller addresses. -/
theorem strSchrittZeiger_vor (p : Adresse) (w : Nat) :
    strSchrittZeiger false p w = p + BitVec.ofNat 64 w := rfl

/-- Backward step steps toward larger addresses. -/
theorem strSchrittZeiger_zurueck (p : Adresse) (w : Nat) :
    strSchrittZeiger true p w = p - BitVec.ofNat 64 w := rfl

/-- Register update past one element: the used pointers step by the
    width from DF, RCX counts only under REP, RAX carries loads. -/
def strWeiter (d : StrDecodiert) (df : Bool) (raxNeu : Wort)
    (r : StrReg) : StrReg :=
  let w := d.breite.bytes
  let rsiNeu :=
    match d.op with
    | .movs => strSchrittZeiger df r.rsi w
    | .lods => strSchrittZeiger df r.rsi w
    | .cmps => strSchrittZeiger df r.rsi w
    | _ => r.rsi
  let rdiNeu :=
    match d.op with
    | .movs => strSchrittZeiger df r.rdi w
    | .stos => strSchrittZeiger df r.rdi w
    | .scas => strSchrittZeiger df r.rdi w
    | .cmps => strSchrittZeiger df r.rdi w
    | _ => r.rdi
  let rcxNeu :=
    match d.rep with
    | .kein => r.rcx
    | _ => r.rcx - BitVec.ofNat 64 1
  ⟨rsiNeu, rdiNeu, rcxNeu, raxNeu⟩

/-- STOS steps RDI and leaves RSI alone. -/
theorem strWeiter_stos_rdi (d : StrDecodiert) (df : Bool) (raxNeu : Wort)
    (r : StrReg) (hop : d.op = .stos) :
    (strWeiter d df raxNeu r).rdi =
      strSchrittZeiger df r.rdi d.breite.bytes ∧
    (strWeiter d df raxNeu r).rsi = r.rsi := by
  unfold strWeiter
  rw [hop]
  exact ⟨rfl, rfl⟩

/-- Without REP, RCX is untouched by the step. -/
theorem strWeiter_kein_rcx (d : StrDecodiert) (df : Bool) (raxNeu : Wort)
    (r : StrReg) (hrep : d.rep = .kein) :
    (strWeiter d df raxNeu r).rcx = r.rcx := by
  unfold strWeiter
  rw [hrep]

/-! ## 4. Repetition: RCX count, ZF early stop, precise faults.
    F3 on SCAS/CMPS means REPE; other ops count only (named silicon
    assumptions, see CUTS). A fault returns the element index with the
    registers AT the faulting element. -/

/-- Early stop before an element: REPE stops on clear ZF, REPNE on
    set ZF, only for the comparing ops. -/
def strStoppt (d : StrDecodiert) (zf : Bool) : Bool :=
  match d.op with
  | .scas | .cmps =>
    match d.rep with
    | .rep => !zf
    | .repne => zf
    | .kein => false
  | _ => false

/-- Element count: one step without REP, RCX steps with REP. -/
def strAnzahl (d : StrDecodiert) (rcx : Wort) : Nat :=
  match d.rep with
  | .kein => 1
  | _ => rcx.toNat

/-- A REP-prefixed zero count runs zero elements. -/
theorem strAnzahl_rep_null (d : StrDecodiert) (h : d.rep ≠ .kein) :
    strAnzahl d (BitVec.ofNat 64 0) = 0 := by
  unfold strAnzahl
  cases e : d.rep with
  | kein => exact absurd e h
  | rep => rfl
  | repne => rfl

/-- Run result: final TSO state and registers with the threaded ZF,
    plus the faulting element index (`none` = clean finish). -/
structure StrLaufErg where
  tso : TSOZustand
  reg : StrReg
  zf : Bool
  fehler : Option Nat

/-- Run at most `n` elements from element `k`: ZF stop first, then one
    TSO element, then registers step past it. -/
def strLauf (d : StrDecodiert) (df : Bool) (n k : Nat) (r : StrReg)
    (zf0 : Bool) (s : TSOZustand) (c : Nat) : StrLaufErg :=
  match n with
  | 0 => ⟨s, r, zf0, none⟩
  | m + 1 =>
    if strStoppt d zf0 then ⟨s, r, zf0, none⟩
    else
      match strElement d r.rsi r.rdi r.rax s c with
      | none => ⟨s, r, zf0, some k⟩
      | some (s1, rax1, zfSet) =>
        let zf1 :=
          match zfSet with
          | none => zf0
          | some b => b
        strLauf d df m (k + 1) (strWeiter d df rax1 r) zf1 s1 c

/-- Zero elements change nothing and fault nothing. -/
theorem strLauf_null (d : StrDecodiert) (df : Bool) (k : Nat)
    (r : StrReg) (zf0 : Bool) (s : TSOZustand) (c : Nat) :
    strLauf d df 0 k r zf0 s c = ⟨s, r, zf0, none⟩ := rfl

/-- A REP-prefixed zero RCX does nothing: no access, no fault. -/
theorem strLauf_rep_null (d : StrDecodiert) (df : Bool) (k : Nat)
    (r : StrReg) (zf0 : Bool) (s : TSOZustand) (c : Nat)
    (h : d.rep ≠ .kein) (hrcx : r.rcx = BitVec.ofNat 64 0) :
    strLauf d df (strAnzahl d r.rcx) k r zf0 s c =
      ⟨s, r, zf0, none⟩ := by
  have h0 : strAnzahl d r.rcx = 0 := by
    rw [hrcx]
    unfold strAnzahl
    cases e : d.rep with
    | kein => exact absurd e h
    | rep => rfl
    | repne => rfl
  rw [h0]
  rfl

/-- Precise faults: a fault index lies between the start element and
    the start plus the element budget. Registers at the fault are the
    loop's own registers (stepped once per finished element). -/
theorem strLauf_fehler_grenzen (d : StrDecodiert) (df : Bool) (n k : Nat)
    (r : StrReg) (zf0 : Bool) (s : TSOZustand) (c : Nat) (j : Nat)
    (h : (strLauf d df n k r zf0 s c).fehler = some j) :
    k ≤ j ∧ j ≤ k + n := by
  induction n generalizing k r zf0 s with
  | zero => simp [strLauf] at h
  | succ n ih =>
    simp only [strLauf] at h
    split at h
    · next hs =>
      cases h
    · next hs =>
      cases he : strElement d r.rsi r.rdi r.rax s c with
      | none =>
        simp only [he] at h
        have hjk := Option.some.inj h
        subst hjk
        omega
      | some v =>
        obtain ⟨s1, rax1, zfSet⟩ := v
        simp only [he] at h
        have hih := ih (k + 1) _ _ _ h
        omega

/-- CLD clears DF, STD sets it. -/
def strDirSchritt : Bool → StrDirOp → Bool
  | _, .cld => false
  | _, .std => true

/-- CLD clears any incoming DF. -/
theorem strDirSchritt_cld (df : Bool) :
    strDirSchritt df .cld = false := by
  cases df <;> rfl

/-- STD sets any incoming DF. -/
theorem strDirSchritt_std (df : Bool) :
    strDirSchritt df .std = true := by
  cases df <;> rfl

/- CUTS:
   Skeleton only: vocabulary above. Decoder, semantics, adapter and
   witness follow. NOT proved here: everything (see lane report).
-/

#print axioms StrDecodiert

end Gabbro.Grammatik.X86
