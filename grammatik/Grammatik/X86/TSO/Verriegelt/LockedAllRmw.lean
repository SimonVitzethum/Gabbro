/-
  File:      Grammatik/X86/LockedAllRmw.lean
  Subject:   Every LOCK-prefixed read-modify-write instruction: one family
             vocabulary with canonical encode/decode, an extended decoder
             chain over the accepted `kapDecode`, and a machine adapter
             that admits exactly the accepted 662 rows and refuses the rest.

  Lane 1367: the opcode ledgers (wave R, reports 1337/1347) show the chain
  decodes only LOCK+REX.W XADD (0F C1) / CMPXCHG (0F B1) / MFENCE and
  refuses every other LOCK RMW shape. This module names the whole family
  (Group-1 ADD/OR/ADC/SBB/AND/SUB/XOR direct and 80/81/83 forms,
  INC/DEC/NEG/NOT, BTS/BTR/BTC, plain and narrow XADD/CMPXCHG,
  CMPXCHG8B/16B), gives each class canonical bytes with closed pins,
  values that ARE the accepted evaluators, and a `HwAdapter` that lifts
  the accepted `hwLockSchritt` on the mapped rows. Nothing new executes
  beyond the accepted 662 rows (see CUTS).
-/
import Grammatik.X86.Hw.Familien.HwLockRmw
import Grammatik.X86.Hw.Kapstein.HwKapsteinDecoder
import Grammatik.X86.Befehle.Ganzzahl.IntCarryForms
import Grammatik.X86.Befehle.Ganzzahl.IntBitTest
import Grammatik.X86.Kern.Ganzzahl
import Grammatik.X86.Kern.Wort

namespace Gabbro.Grammatik.X86

/-- Every LOCK-capable read-modify-write operation class (`or`, `and`
    and `not` take an underscore: the bare names are keywords). -/
inductive LockAllOp where
  | add | or_ | adc | sbb | and_ | sub | xor_
  | inc | dec | neg | not_
  | bts | btr | btc
  | xadd | cmpxchg | cmpxchg8b
  deriving DecidableEq, Repr

/-- Parsed architectural #UD grounds of the family decoder: LOCK on a
    register destination, and LOCK on a form that writes nothing. -/
inductive LockAllUd where
  | regZiel
  | keinSchreiben
  deriving DecidableEq, Repr

/-- One family form: operation, width, LOCK presence, raw REX byte,
    mod field, reg digit, base digit, SIB-36 presence, displacement,
    immediate tail, and total consumed length. -/
structure LockAllForm where
  op : LockAllOp
  w : Breite
  lock : Bool
  rex : Option Nat
  mod : Nat
  feld : Nat
  basis : Nat
  sib : Bool
  disp : BitVec 32
  imm : List Byte
  len : Nat
  deriving DecidableEq, Repr

/-- One parsed family instruction: an admitted form, or a parsed
    architectural #UD, each with its consumed length. -/
inductive LockAllAnweisung where
  | ok (f : LockAllForm) (len : Nat)
  | ud (g : LockAllUd) (len : Nat)
  deriving DecidableEq, Repr

/-! ## 1. Value layer: the accepted evaluators, never redefined.

  Group-1 values ARE `addB`/`orB`/`adcWert`/`sbbWert`/`andB`/`subB`/
  `xorB`; INC/DEC ARE `incWert`/`decWert`; NEG IS `negW`; NOT IS
  `notB`; BTS/BTR/BTC ARE `btRoh`; XADD installs the modular sum.
  The compare-exchange value takes the observed word, the RAX
  expectation and the source: success installs the source, failure
  keeps the word (the write-back still needs write permission: the
  machine layer owns that guard, following `hwLock_cmpxchg_nein`). -/

/-- Locked-memory result word: the accepted value function per class.
    `alt` is the observed memory word, `src` the register source (the
    bit offset for BTS/BTR/BTC, the addend for XADD), `c` the
    carry-in for ADC/SBB. -/
def lockAllWert (op : LockAllOp) (w : Breite) (alt src : Wort)
    (c : Bool) : Wort :=
  match op with
  | .add => addB w alt src
  | .or_ => orB w alt src
  | .adc => adcWert w alt src c
  | .sbb => sbbWert w alt src c
  | .and_ => andB w alt src
  | .sub => subB w alt src
  | .xor_ => xorB w alt src
  | .inc => incWert w alt
  | .dec => decWert w alt
  | .neg => negW w alt
  | .not_ => notB w alt
  | .bts => btRoh .bts w alt src.toNat
  | .btr => btRoh .btr w alt src.toNat
  | .btc => btRoh .btc w alt src.toNat
  | .xadd => addB w alt src
  | .cmpxchg => src
  | .cmpxchg8b => src

/-- Compare-exchange value: the source on match, the word otherwise. -/
def lockAllWertCmp (w : Breite) (alt rax src : Wort) : Wort :=
  if alt == rax then trunc w src else trunc w alt

/-- Carry flag of the bit-test classes: the selected bit. Every other
    class leaves the flag question to the accepted flag snapshots
    (`adcFlags`, `logikFlags`, ...), never invented here. -/
def lockAllCf (op : LockAllOp) (w : Breite) (alt src : Wort) :
    Option Bool :=
  match op with
  | .bts => some (btBit w alt src.toNat)
  | .btr => some (btBit w alt src.toNat)
  | .btc => some (btBit w alt src.toNat)
  | _ => none

/-- Each arm IS its accepted evaluator (lift, never a copy). -/
theorem lockAllWert_add (w : Breite) (alt src : Wort) (c : Bool) :
    lockAllWert .add w alt src c = addB w alt src := rfl

theorem lockAllWert_or (w : Breite) (alt src : Wort) (c : Bool) :
    lockAllWert .or_ w alt src c = orB w alt src := rfl

theorem lockAllWert_adc (w : Breite) (alt src : Wort) (c : Bool) :
    lockAllWert .adc w alt src c = adcWert w alt src c := rfl

theorem lockAllWert_sbb (w : Breite) (alt src : Wort) (c : Bool) :
    lockAllWert .sbb w alt src c = sbbWert w alt src c := rfl

theorem lockAllWert_and (w : Breite) (alt src : Wort) (c : Bool) :
    lockAllWert .and_ w alt src c = andB w alt src := rfl

theorem lockAllWert_sub (w : Breite) (alt src : Wort) (c : Bool) :
    lockAllWert .sub w alt src c = subB w alt src := rfl

theorem lockAllWert_xor (w : Breite) (alt src : Wort) (c : Bool) :
    lockAllWert .xor_ w alt src c = xorB w alt src := rfl

theorem lockAllWert_inc (w : Breite) (alt src : Wort) (c : Bool) :
    lockAllWert .inc w alt src c = incWert w alt := rfl

theorem lockAllWert_dec (w : Breite) (alt src : Wort) (c : Bool) :
    lockAllWert .dec w alt src c = decWert w alt := rfl

theorem lockAllWert_neg (w : Breite) (alt src : Wort) (c : Bool) :
    lockAllWert .neg w alt src c = negW w alt := rfl

theorem lockAllWert_not (w : Breite) (alt src : Wort) (c : Bool) :
    lockAllWert .not_ w alt src c = notB w alt := rfl

theorem lockAllWert_bts (w : Breite) (alt src : Wort) (c : Bool) :
    lockAllWert .bts w alt src c = btRoh .bts w alt src.toNat := rfl

theorem lockAllWert_btr (w : Breite) (alt src : Wort) (c : Bool) :
    lockAllWert .btr w alt src c = btRoh .btr w alt src.toNat := rfl

theorem lockAllWert_btc (w : Breite) (alt src : Wort) (c : Bool) :
    lockAllWert .btc w alt src c = btRoh .btc w alt src.toNat := rfl

theorem lockAllWert_xadd (w : Breite) (alt src : Wort) (c : Bool) :
    lockAllWert .xadd w alt src c = addB w alt src := rfl

theorem lockAllCf_bts (w : Breite) (alt src : Wort) :
    lockAllCf .bts w alt src = some (btBit w alt src.toNat) := rfl

theorem lockAllCf_add (w : Breite) (alt src : Wort) :
    lockAllCf .add w alt src = none := rfl

/-! ## 2. Canonical encoder: one byte shape per class.

  Canonical choices (the decoder admits more, see §3): LOCK first,
  then 66H, then REX.W; mod=2 base-plus-disp32 over rbp without SIB;
  Group-1 via the direct 00 to 3F memory-destination forms; INC/DEC via
  FE/FF digits 0 and 1; NOT/NEG via F6/F7 digits 2 and 3; BTS/BTR/BTC via 0F AB/B3/BB;
  the imm8 group via 0F BA; XADD via 0F C0/C1; CMPXCHG via 0F B0/B1;
  CMPXCHG8B/16B via 0F C7 /1. The encoder is canonical only: it
  always writes mod=2 (see CUTS). -/

/-- Canonical prefix bytes: LOCK, operand-size override, REX.W. -/
def lockAllPrefix (lock : Bool) (w : Breite) : List Byte :=
  (if lock then [natByte 240] else []) ++
  (match w with | .b16 => [natByte 102] | _ => []) ++
  (match w with | .b64 => [rexByte 0 0] | _ => [])

/-- Direct Group-1 base opcode (the even member; +1 unless 8-bit). -/
def lockAllDirektOp : LockAllOp → Nat
  | .add => 0 | .or_ => 8 | .adc => 16 | .sbb => 24
  | .and_ => 32 | .sub => 40 | .xor_ => 48
  | _ => 0

/-- Canonical mod=2 ModRM byte over a reg digit and a base digit. -/
def lockAllModrm (feld basis : Nat) : Byte :=
  natByte (128 + 8 * (feld % 8) + basis % 8)

/-- Canonical encoding of one family form (mod=2, disp32, SIB-36
    exactly when `sib`). -/
def encodeLockAll (f : LockAllForm) : List Byte :=
  let pref := lockAllPrefix f.lock f.w
  let tail := lockAllModrm f.feld f.basis ::
    (if f.sib then [natByte 36] else []) ++ leBytes32 f.disp
  match f.op with
  | .add => pref ++ natByte (lockAllDirektOp .add + (if f.w == .b8 then 0 else 1)) :: tail
  | .or_ => pref ++ natByte (lockAllDirektOp .or_ + (if f.w == .b8 then 0 else 1)) :: tail
  | .adc => pref ++ natByte (lockAllDirektOp .adc + (if f.w == .b8 then 0 else 1)) :: tail
  | .sbb => pref ++ natByte (lockAllDirektOp .sbb + (if f.w == .b8 then 0 else 1)) :: tail
  | .and_ => pref ++ natByte (lockAllDirektOp .and_ + (if f.w == .b8 then 0 else 1)) :: tail
  | .sub => pref ++ natByte (lockAllDirektOp .sub + (if f.w == .b8 then 0 else 1)) :: tail
  | .xor_ => pref ++ natByte (lockAllDirektOp .xor_ + (if f.w == .b8 then 0 else 1)) :: tail
  | .inc =>
    let m := lockAllModrm 0 f.basis
    pref ++ (if f.w == .b8 then natByte 254 else natByte 255) :: m ::
      (if f.sib then [natByte 36] else []) ++ leBytes32 f.disp
  | .dec =>
    let m := lockAllModrm 1 f.basis
    pref ++ (if f.w == .b8 then natByte 254 else natByte 255) :: m ::
      (if f.sib then [natByte 36] else []) ++ leBytes32 f.disp
  | .neg =>
    let m := lockAllModrm 3 f.basis
    pref ++ (if f.w == .b8 then natByte 246 else natByte 247) :: m ::
      (if f.sib then [natByte 36] else []) ++ leBytes32 f.disp
  | .not_ =>
    let m := lockAllModrm 2 f.basis
    pref ++ (if f.w == .b8 then natByte 246 else natByte 247) :: m ::
      (if f.sib then [natByte 36] else []) ++ leBytes32 f.disp
  | .bts => pref ++ [natByte 15, natByte 171] ++ tail
  | .btr => pref ++ [natByte 15, natByte 179] ++ tail
  | .btc => pref ++ [natByte 15, natByte 187] ++ tail
  | .xadd =>
    pref ++ [natByte 15, if f.w == .b8 then natByte 192 else natByte 193] ++ tail
  | .cmpxchg =>
    pref ++ [natByte 15, if f.w == .b8 then natByte 176 else natByte 177] ++ tail
  | .cmpxchg8b =>
    let m := lockAllModrm 1 f.basis
    pref ++ [natByte 15, natByte 199] ++ m ::
      (if f.sib then [natByte 36] else []) ++ leBytes32 f.disp

/-! ## 3. Canonical rows: one closed form per class. -/

/-- LOCK ADD dword [rbp+0], eax. -/
def canonAdd32 : LockAllForm :=
  ⟨.add, .b32, true, none, 2, 0, 5, false, BitVec.ofNat 32 0, [], 7⟩

/-- LOCK ADD qword [rbp+0], rax. -/
def canonAdd64 : LockAllForm :=
  ⟨.add, .b64, true, some 72, 2, 0, 5, false, BitVec.ofNat 32 0, [], 8⟩

/-- LOCK XADD qword [rbp+0], rax. -/
def canonXadd64 : LockAllForm :=
  ⟨.xadd, .b64, true, some 72, 2, 0, 5, false, BitVec.ofNat 32 0, [], 9⟩

/-- LOCK CMPXCHG qword [rbp+0], rax. -/
def canonCmpxchg64 : LockAllForm :=
  ⟨.cmpxchg, .b64, true, some 72, 2, 0, 5, false, BitVec.ofNat 32 0, [], 9⟩

/-- LOCK BTS dword [rbp+0], eax. -/
def canonBts32 : LockAllForm :=
  ⟨.bts, .b32, true, none, 2, 0, 5, false, BitVec.ofNat 32 0, [], 8⟩

/-- LOCK INC qword [rbp+0]. -/
def canonInc64 : LockAllForm :=
  ⟨.inc, .b64, true, some 72, 2, 0, 5, false, BitVec.ofNat 32 0, [], 8⟩

/-- LOCK NEG dword [rbp+0]. -/
def canonNeg32 : LockAllForm :=
  ⟨.neg, .b32, true, none, 2, 3, 5, false, BitVec.ofNat 32 0, [], 7⟩

/-- Plain (unlocked) XADD qword [rbp+0], rax: decodes, never admits. -/
def canonXaddPlain64 : LockAllForm :=
  ⟨.xadd, .b64, false, some 72, 2, 0, 5, false, BitVec.ofNat 32 0, [], 8⟩

/-- LOCK CMPXCHG8B qword [rbp+0]. -/
def canonC7B : LockAllForm :=
  ⟨.cmpxchg8b, .b32, true, none, 2, 1, 5, false, BitVec.ofNat 32 0, [], 8⟩

/-- LOCK ADD word [rbp+0], ax (operand-size prefix). -/
def canonAdd16 : LockAllForm :=
  ⟨.add, .b16, true, none, 2, 0, 5, false, BitVec.ofNat 32 0, [], 8⟩

/-- Encode pins: each canonical form assembles its exact bytes. -/
theorem enc_add32 :
    encodeLockAll canonAdd32 =
      [natByte 240, natByte 1, natByte 133, natByte 0, natByte 0,
        natByte 0, natByte 0] := rfl

theorem enc_add64 :
    encodeLockAll canonAdd64 =
      [natByte 240, natByte 72, natByte 1, natByte 133, natByte 0,
        natByte 0, natByte 0, natByte 0] := rfl

theorem enc_xadd64 :
    encodeLockAll canonXadd64 =
      [natByte 240, natByte 72, natByte 15, natByte 193, natByte 133,
        natByte 0, natByte 0, natByte 0, natByte 0] := rfl

theorem enc_cmpxchg64 :
    encodeLockAll canonCmpxchg64 =
      [natByte 240, natByte 72, natByte 15, natByte 177, natByte 133,
        natByte 0, natByte 0, natByte 0, natByte 0] := rfl

theorem enc_bts32 :
    encodeLockAll canonBts32 =
      [natByte 240, natByte 15, natByte 171, natByte 133, natByte 0,
        natByte 0, natByte 0, natByte 0] := rfl

theorem enc_inc64 :
    encodeLockAll canonInc64 =
      [natByte 240, natByte 72, natByte 255, natByte 133, natByte 0,
        natByte 0, natByte 0, natByte 0] := rfl

theorem enc_neg32 :
    encodeLockAll canonNeg32 =
      [natByte 240, natByte 247, natByte 157, natByte 0, natByte 0,
        natByte 0, natByte 0] := rfl

theorem enc_xaddPlain64 :
    encodeLockAll canonXaddPlain64 =
      [natByte 72, natByte 15, natByte 193, natByte 133, natByte 0,
        natByte 0, natByte 0, natByte 0] := rfl

theorem enc_c7b :
    encodeLockAll canonC7B =
      [natByte 240, natByte 15, natByte 199, natByte 141, natByte 0,
        natByte 0, natByte 0, natByte 0] := rfl

theorem enc_add16 :
    encodeLockAll canonAdd16 =
      [natByte 240, natByte 102, natByte 1, natByte 133, natByte 0,
        natByte 0, natByte 0, natByte 0] := rfl

/-! ## 4. Family decoder: LOCK shapes with exact lengths.

  Prefixes LOCK, 66H and REX in any order, each at most once; REX.W
  overrides 66H, like silicon. The ModRM tail covers mod 0 and mod 2
  with disp32, plus the SIB-36 subset the accepted decoder uses.
  Stated refusals (none): mod 1 with disp8 (no accepted equation pins
  the 32-bit handoff for a sign-extended disp8), mod 0 rm 5
  (RIP-relative has no accepted base-plus-disp32 address model), other
  SIB bytes, and non-LOCK Group-1 and INC/DEC/NEG/NOT (owned by the
  carry and core families). LOCK on a register destination parses to
  the regZiel marker; LOCK on a form that writes nothing parses to
  keinSchreiben; both mirror the 662 parsed-UD discipline. -/

/-- Prefix scan: LOCK flag, width, raw REX byte and rest. -/
def lockAllPraefixAux : List Byte → Bool → Breite → Option Nat →
    Option (Bool × Breite × Option Nat × List Byte)
  | [], _, _, _ => none
  | b :: rest, lk, w, rex =>
    let v := byteNat b
    if v == 240 then
      match lk with
      | true => none
      | false => lockAllPraefixAux rest true w rex
    else if v == 102 then
      match w with
      | .b16 => none
      | _ => lockAllPraefixAux rest lk .b16 rex
    else if 64 ≤ v ∧ v < 80 then
      match rex with
      | some _ => none
      | none =>
        lockAllPraefixAux rest lk (if 72 ≤ v then .b64 else w) (some v)
    else some (lk, w, rex, b :: rest)

/-- Group digit to Group-1 operation (7 is CMP: no write). -/
def lockAllGruppe : Nat → Option LockAllOp
  | 0 => some .add | 1 => some .or_ | 2 => some .adc | 3 => some .sbb
  | 4 => some .and_ | 5 => some .sub | 6 => some .xor_
  | _ => none

/-- Address tail after the ModRM byte: SIB-36 presence, displacement
    and rest. Only mod 0 (disp-less) and mod 2 (disp32) are admitted. -/
def lockAllSchwanz (mod rm : Nat) : List Byte →
    Option (Bool × BitVec 32 × List Byte)
  | [] => none
  | s :: rest =>
    if rm == 4 then
      if byteNat s != 36 then none
      else if mod == 0 then some (true, BitVec.ofNat 32 0, rest)
      else if mod == 2 then
        match parseLe32 rest with
        | some (d, r) => some (true, d, r)
        | none => none
      else none
    else if mod == 0 then
      if rm == 5 then none
      else some (false, BitVec.ofNat 32 0, s :: rest)
    else if mod == 2 then
      match parseLe32 (s :: rest) with
      | some (d, r) => some (false, d, r)
      | none => none
    else none

/-- Memory-operand core shared by every opcode class. `opOf` maps the
    ModRM reg digit to the operation and its write flag; `auchNackt`
    admits unlocked XADD, CMPXCHG, CMPXCHG8B and bit-test shapes;
    `immLen` is the immediate tail; `vor` the bytes before ModRM. -/
def lockAllMem (lock : Bool) (w : Breite) (rex : Option Nat)
    (opOf : Nat → Option (LockAllOp × Bool)) (auchNackt : Bool)
    (immLen : Nat) (vor : Nat) :
    List Byte → Option (LockAllAnweisung × List Byte)
  | [] => none
  | m :: rest =>
    let mod := byteNat m / 64
    let rg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    if mod == 3 then
      if !lock then none
      else if rest.length < immLen then none
      else some (.ud .regZiel (vor + 1 + immLen), rest.drop immLen)
    else
      match opOf rg with
      | none => none
      | some (op, schreibend) =>
        match lockAllSchwanz mod rm rest with
        | none => none
        | some (sib, d, rest1) =>
          if rest1.length < immLen then none
          else
            let rest2 := rest1.drop immLen
            let sibN := if sib then 1 else 0
            let dispN := if mod == 2 then 4 else 0
            let n := vor + 1 + sibN + dispN + immLen
            if !lock ∧ !auchNackt then none
            else if !schreibend then
              some (.ud .keinSchreiben n, rest2)
            else
              some (.ok ⟨op, w, lock, rex, mod, rg, rm, sib, d,
                rest1.take immLen, n⟩ n, rest2)

/-- Opcode dispatch after the prefixes. `vor` counts prefix bytes. -/
def decodeLockAllNach (lock : Bool) (w : Breite) (rex : Option Nat)
    (vor : Nat) : List Byte → Option (LockAllAnweisung × List Byte)
  | [] => none
  | b :: rest =>
    let n := byteNat b
    if n == 15 then
      match rest with
      | [] => none
      | o2 :: rest2 =>
        let o := byteNat o2
        if o == 171 then
          if w == .b8 then none
          else lockAllMem lock w rex (fun _ => some (.bts, true)) true
            0 (vor + 2) rest2
        else if o == 179 then
          if w == .b8 then none
          else lockAllMem lock w rex (fun _ => some (.btr, true)) true
            0 (vor + 2) rest2
        else if o == 187 then
          if w == .b8 then none
          else lockAllMem lock w rex (fun _ => some (.btc, true)) true
            0 (vor + 2) rest2
        else if o == 186 then
          if w == .b8 then none
          else lockAllMem lock w rex
            (fun dg => match dg with
              | 5 => some (.bts, true)
              | 6 => some (.btr, true)
              | 7 => some (.btc, true)
              | _ => none) true 1 (vor + 2) rest2
        else if o == 192 then
          lockAllMem lock .b8 rex (fun _ => some (.xadd, true)) true
            0 (vor + 2) rest2
        else if o == 193 then
          lockAllMem lock w rex (fun _ => some (.xadd, true)) true
            0 (vor + 2) rest2
        else if o == 176 then
          lockAllMem lock .b8 rex (fun _ => some (.cmpxchg, true)) true
            0 (vor + 2) rest2
        else if o == 177 then
          lockAllMem lock w rex (fun _ => some (.cmpxchg, true)) true
            0 (vor + 2) rest2
        else if o == 199 then
          if w == .b16 then none
          else
            let ww := if w == .b64 then .b64 else .b32
            lockAllMem lock ww rex
              (fun dg => if dg == 1 then some (.cmpxchg8b, true)
                else none) true 0 (vor + 2) rest2
        else none
    else if n < 62 then
      -- Direct forms: r 0 and 1 write memory (8-bit and wide), r 2
      -- and 3 write a register, r 4 and 5 are accumulator
      -- immediates without any ModRM byte.
      let g := n / 8
      let r := n % 8
      if r == 4 || r == 5 then
        if !lock then none
        else some (.ud .keinSchreiben (vor + 1), rest)
      else
        let schreibend :=
          match lockAllGruppe g with
          | some _ => r == 0 || r == 1
          | none => false
        let ww := if r == 0 || r == 2 then .b8 else w
        let opOf : Nat → Option (LockAllOp × Bool) :=
          fun _ =>
            match lockAllGruppe g with
            | some op => some (op, schreibend)
            | none => some (.add, false)
        lockAllMem lock ww rex opOf false 0 (vor + 1) rest
    else if n == 128 then
      lockAllMem lock .b8 rex
        (fun dg => match lockAllGruppe dg with
          | some op => some (op, true)
          | none => some (.add, false)) false 1 (vor + 1) rest
    else if n == 129 then
      lockAllMem lock w rex
        (fun dg => match lockAllGruppe dg with
          | some op => some (op, true)
          | none => some (.add, false)) false
        (if w == .b16 then 2 else 4) (vor + 1) rest
    else if n == 131 then
      lockAllMem lock w rex
        (fun dg => match lockAllGruppe dg with
          | some op => some (op, true)
          | none => some (.add, false)) false 1 (vor + 1) rest
    else if n == 254 then
      lockAllMem lock .b8 rex
        (fun dg => match dg with
          | 0 => some (.inc, true)
          | 1 => some (.dec, true)
          | _ => none) false 0 (vor + 1) rest
    else if n == 255 then
      lockAllMem lock w rex
        (fun dg => match dg with
          | 0 => some (.inc, true)
          | 1 => some (.dec, true)
          | _ => none) false 0 (vor + 1) rest
    else if n == 246 then
      lockAllMem lock .b8 rex
        (fun dg => match dg with
          | 2 => some (.not_, true)
          | 3 => some (.neg, true)
          | _ => none) false 0 (vor + 1) rest
    else if n == 247 then
      lockAllMem lock w rex
        (fun dg => match dg with
          | 2 => some (.not_, true)
          | 3 => some (.neg, true)
          | _ => none) false 0 (vor + 1) rest
    else none

/-- Top-level family decode: prefixes, then opcode dispatch. -/
def decodeLockAll (bs : List Byte) :
    Option (LockAllAnweisung × List Byte) :=
  match lockAllPraefixAux bs false .b32 none with
  | none => none
  | some (lock, w, rex, rest0) =>
    decodeLockAllNach lock w rex (bs.length - rest0.length) rest0

/-! ## 5. Closed pins: canonical rows decode, the old chain refuses.

  Each canonical row decodes to its exact form (a checked byte round
  trip together with the §3 encode pins), and the accepted `kapDecode`
  refuses every row outside its 662 subset. -/

theorem dec_add32 :
    decodeLockAll [natByte 240, natByte 1, natByte 133, natByte 0,
      natByte 0, natByte 0, natByte 0] =
      some (.ok canonAdd32 7, []) := by
  decide

theorem dec_add64 :
    decodeLockAll [natByte 240, natByte 72, natByte 1, natByte 133,
      natByte 0, natByte 0, natByte 0, natByte 0] =
      some (.ok canonAdd64 8, []) := by
  decide

theorem dec_xadd64 :
    decodeLockAll [natByte 240, natByte 72, natByte 15, natByte 193,
      natByte 133, natByte 0, natByte 0, natByte 0, natByte 0] =
      some (.ok canonXadd64 9, []) := by
  decide

theorem dec_cmpxchg64 :
    decodeLockAll [natByte 240, natByte 72, natByte 15, natByte 177,
      natByte 133, natByte 0, natByte 0, natByte 0, natByte 0] =
      some (.ok canonCmpxchg64 9, []) := by
  decide

theorem dec_bts32 :
    decodeLockAll [natByte 240, natByte 15, natByte 171, natByte 133,
      natByte 0, natByte 0, natByte 0, natByte 0] =
      some (.ok canonBts32 8, []) := by
  decide

theorem dec_inc64 :
    decodeLockAll [natByte 240, natByte 72, natByte 255, natByte 133,
      natByte 0, natByte 0, natByte 0, natByte 0] =
      some (.ok canonInc64 8, []) := by
  decide

theorem dec_neg32 :
    decodeLockAll [natByte 240, natByte 247, natByte 157, natByte 0,
      natByte 0, natByte 0, natByte 0] =
      some (.ok canonNeg32 7, []) := by
  decide

theorem dec_xaddPlain64 :
    decodeLockAll [natByte 72, natByte 15, natByte 193, natByte 133,
      natByte 0, natByte 0, natByte 0, natByte 0] =
      some (.ok canonXaddPlain64 8, []) := by
  decide

theorem dec_c7b :
    decodeLockAll [natByte 240, natByte 15, natByte 199, natByte 141,
      natByte 0, natByte 0, natByte 0, natByte 0] =
      some (.ok canonC7B 8, []) := by
  decide

theorem dec_add16 :
    decodeLockAll [natByte 240, natByte 102, natByte 1, natByte 133,
      natByte 0, natByte 0, natByte 0, natByte 0] =
      some (.ok canonAdd16 8, []) := by
  decide

/-- The old chain refuses LOCK ADD dword (no Group-1 LOCK row). -/
theorem kap_weist_add32_zurueck :
    kapDecode [natByte 240, natByte 1, natByte 133, natByte 0,
      natByte 0, natByte 0, natByte 0] = none := by
  decide

/-- The old chain refuses LOCK ADD qword. -/
theorem kap_weist_add64_zurueck :
    kapDecode [natByte 240, natByte 72, natByte 1, natByte 133,
      natByte 0, natByte 0, natByte 0, natByte 0] = none := by
  decide

/-- The old chain refuses LOCK BTS dword. -/
theorem kap_weist_bts32_zurueck :
    kapDecode [natByte 240, natByte 15, natByte 171, natByte 133,
      natByte 0, natByte 0, natByte 0, natByte 0] = none := by
  decide

/-- The old chain refuses LOCK INC qword. -/
theorem kap_weist_inc64_zurueck :
    kapDecode [natByte 240, natByte 72, natByte 255, natByte 133,
      natByte 0, natByte 0, natByte 0, natByte 0] = none := by
  decide

/-- The old chain refuses LOCK NEG dword. -/
theorem kap_weist_neg32_zurueck :
    kapDecode [natByte 240, natByte 247, natByte 157, natByte 0,
      natByte 0, natByte 0, natByte 0] = none := by
  decide

/-- The old chain refuses plain XADD qword (LOCK selects the row). -/
theorem kap_weist_xaddPlain64_zurueck :
    kapDecode [natByte 72, natByte 15, natByte 193, natByte 133,
      natByte 0, natByte 0, natByte 0, natByte 0] = none := by
  decide

/-- The old chain refuses LOCK CMPXCHG8B. -/
theorem kap_weist_c7b_zurueck :
    kapDecode [natByte 240, natByte 15, natByte 199, natByte 141,
      natByte 0, natByte 0, natByte 0, natByte 0] = none := by
  decide

/-- The old chain refuses LOCK ADD word. -/
theorem kap_weist_add16_zurueck :
    kapDecode [natByte 240, natByte 102, natByte 1, natByte 133,
      natByte 0, natByte 0, natByte 0, natByte 0] = none := by
  decide

/-! ## 6. Extended chain over the accepted `kapDecode`.

  The accepted chain runs first: every byte string it decodes keeps
  its exact arm (no pilot or extension form is shadowed). Where it
  refuses, the family decoder takes its rows; where both refuse, the
  extended chain refuses. -/

/-- One decoded row of the extended chain: the accepted chain first,
    the family decoder only where the accepted chain refuses. -/
inductive KapAllDekodiert where
  | alt : KapDekodiert → KapAllDekodiert
  | neu : LockAllAnweisung → KapAllDekodiert
  deriving DecidableEq, Repr

/-- The extended priority chain over bytes. -/
def kapDecodeAll (bs : List Byte) :
    Option (KapAllDekodiert × List Byte) :=
  match kapDecode bs with
  | some (k, rest) => some (.alt k, rest)
  | none =>
    match decodeLockAll bs with
    | some (a, rest) => some (.neu a, rest)
    | none => none

/-- The extended chain agrees with the accepted chain wherever the
    accepted chain takes a row. -/
theorem kapDecodeAll_stimmt_alt (bs : List Byte) (k : KapDekodiert)
    (rest : List Byte) (h : kapDecode bs = some (k, rest)) :
    kapDecodeAll bs = some (.alt k, rest) := by
  unfold kapDecodeAll
  rw [h]

/-- Where the accepted chain refuses, a covered family row is taken. -/
theorem kapDecodeAll_neu (bs : List Byte) (a : LockAllAnweisung)
    (rest : List Byte) (h1 : kapDecode bs = none)
    (h2 : decodeLockAll bs = some (a, rest)) :
    kapDecodeAll bs = some (.neu a, rest) := by
  unfold kapDecodeAll
  rw [h1, h2]

/-- Where both chains refuse, the extended chain refuses. -/
theorem kapDecodeAll_nichts (bs : List Byte)
    (h1 : kapDecode bs = none) (h2 : decodeLockAll bs = none) :
    kapDecodeAll bs = none := by
  unfold kapDecodeAll
  rw [h1, h2]

/-- Old-arm pin: the accepted LOCK XADD witness keeps its exact arm
    through the extended chain. -/
theorem kapAllKette_lock :
    kapDecodeAll kapW_lock =
      some (.alt (KapDekodiert.lock
        (LockAnweisung.ok (.xadd64 .rax .rbp 0) 9)), []) :=
  kapDecodeAll_stimmt_alt _ _ _ kapKette_lock

/-- New-arm pins: each refused row takes the family arm. -/
theorem kapAll_neu_add32 :
    kapDecodeAll [natByte 240, natByte 1, natByte 133, natByte 0,
      natByte 0, natByte 0, natByte 0] =
      some (.neu (.ok canonAdd32 7), []) :=
  kapDecodeAll_neu _ _ _ kap_weist_add32_zurueck dec_add32

theorem kapAll_neu_add64 :
    kapDecodeAll [natByte 240, natByte 72, natByte 1, natByte 133,
      natByte 0, natByte 0, natByte 0, natByte 0] =
      some (.neu (.ok canonAdd64 8), []) :=
  kapDecodeAll_neu _ _ _ kap_weist_add64_zurueck dec_add64

theorem kapAll_neu_bts32 :
    kapDecodeAll [natByte 240, natByte 15, natByte 171, natByte 133,
      natByte 0, natByte 0, natByte 0, natByte 0] =
      some (.neu (.ok canonBts32 8), []) :=
  kapDecodeAll_neu _ _ _ kap_weist_bts32_zurueck dec_bts32

theorem kapAll_neu_inc64 :
    kapDecodeAll [natByte 240, natByte 72, natByte 255, natByte 133,
      natByte 0, natByte 0, natByte 0, natByte 0] =
      some (.neu (.ok canonInc64 8), []) :=
  kapDecodeAll_neu _ _ _ kap_weist_inc64_zurueck dec_inc64

theorem kapAll_neu_neg32 :
    kapDecodeAll [natByte 240, natByte 247, natByte 157, natByte 0,
      natByte 0, natByte 0, natByte 0] =
      some (.neu (.ok canonNeg32 7), []) :=
  kapDecodeAll_neu _ _ _ kap_weist_neg32_zurueck dec_neg32

theorem kapAll_neu_xaddPlain64 :
    kapDecodeAll [natByte 72, natByte 15, natByte 193, natByte 133,
      natByte 0, natByte 0, natByte 0, natByte 0] =
      some (.neu (.ok canonXaddPlain64 8), []) :=
  kapDecodeAll_neu _ _ _ kap_weist_xaddPlain64_zurueck dec_xaddPlain64

theorem kapAll_neu_c7b :
    kapDecodeAll [natByte 240, natByte 15, natByte 199, natByte 141,
      natByte 0, natByte 0, natByte 0, natByte 0] =
      some (.neu (.ok canonC7B 8), []) :=
  kapDecodeAll_neu _ _ _ kap_weist_c7b_zurueck dec_c7b

theorem kapAll_neu_add16 :
    kapDecodeAll [natByte 240, natByte 102, natByte 1, natByte 133,
      natByte 0, natByte 0, natByte 0, natByte 0] =
      some (.neu (.ok canonAdd16 8), []) :=
  kapDecodeAll_neu _ _ _ kap_weist_add16_zurueck dec_add16

/-! ## 7. Machine adapter: exactly the accepted rows execute.

  The map onto the accepted 662 vocabulary admits 64-bit locked XADD
  and CMPXCHG in mod-2 base-plus-disp32 (with the SIB-36 subset) under
  a canonical 662 REX byte. Every other form maps to none and refuses
  the step: narrower widths, other addressing modes, missing LOCK,
  Group-1, INC/DEC/NEG/NOT, bit-test and CMPXCHG8B execute nothing
  here. The old evaluator is lifted, never redefined. -/

/-- Map one 64-bit word row onto the accepted vocabulary. -/
def lockAllAufLockWort
    (mk : Register → Register → BitVec 32 → LockForm)
    (f : LockAllForm) : Option LockForm :=
  match f.w with
  | .b64 =>
    match f.lock with
    | true =>
      match f.rex with
      | none => none
      | some rv =>
        match rexLockBits (natByte rv) with
        | none => none
        | some (rh, bh) =>
          if f.mod != 2 then none
          else
            match codeReg (rh * 8 + f.feld),
              codeReg (bh * 8 + (if f.sib then 4 else f.basis)) with
            | some rs, some rb => some (mk rs rb f.disp)
            | _, _ => none
    | false => none
  | _ => none

/-- Map onto the accepted 662 vocabulary (see above). -/
def lockAllAufLock (f : LockAllForm) : Option LockForm :=
  match f.op with
  | .xadd => lockAllAufLockWort .xadd64 f
  | .cmpxchg => lockAllAufLockWort .cmpxchg64 f
  | .add => none | .or_ => none | .adc => none | .sbb => none
  | .and_ => none | .sub => none | .xor_ => none
  | .inc => none | .dec => none | .neg => none | .not_ => none
  | .bts => none | .btr => none | .btc => none
  | .cmpxchg8b => none

/-- Every non-XADD non-CMPXCHG form maps to none. -/
theorem lockAllAufLock_ablehnung (f : LockAllForm)
    (h1 : f.op ≠ .xadd) (h2 : f.op ≠ .cmpxchg) :
    lockAllAufLock f = none := by
  unfold lockAllAufLock
  cases e : f.op with
  | xadd => exact absurd e h1
  | cmpxchg => exact absurd e h2
  | add => rfl | or_ => rfl | adc => rfl | sbb => rfl
  | and_ => rfl | sub => rfl | xor_ => rfl
  | inc => rfl | dec => rfl | neg => rfl | not_ => rfl
  | bts => rfl | btr => rfl | btc => rfl
  | cmpxchg8b => rfl

/-- A narrower width maps to none. -/
theorem lockAllAufLockWort_schmal
    (mk : Register → Register → BitVec 32 → LockForm)
    (f : LockAllForm) (h : f.w ≠ .b64) :
    lockAllAufLockWort mk f = none := by
  unfold lockAllAufLockWort
  cases e : f.w with
  | b64 => exact absurd e h
  | b8 => rfl | b16 => rfl | b32 => rfl

/-- A missing LOCK maps to none (no atomicity without LOCK). -/
theorem lockAllAufLockWort_ohne_lock
    (mk : Register → Register → BitVec 32 → LockForm)
    (f : LockAllForm) (h : f.lock = false) :
    lockAllAufLockWort mk f = none := by
  unfold lockAllAufLockWort
  cases e : f.w with
  | b64 =>
    cases e2 : f.lock with
    | true =>
      rw [e2] at h
      cases h
    | false => rfl
  | b8 => rfl | b16 => rfl | b32 => rfl

/-- One family step on the coherent machine: mapped rows ride the
    accepted `hwLockSchritt`; everything else refuses with none. -/
def hwLockAllSchritt (m : HwMaschine) (c : Nat)
    (a : LockAllAnweisung) : Option HwMaschine :=
  match a with
  | .ud _ _ => none
  | .ok f len =>
    match lockAllAufLock f with
    | some lf => hwLockSchritt m c (.ok lf len)
    | none => none

/-- The family producer plug over the parsed family instruction. -/
def adapterLockAll : HwAdapter LockAllAnweisung :=
  ⟨fun m c a => hwLockAllSchritt m c a⟩

/-- A parsed UD never steps. -/
theorem hwLockAllSchritt_ud (m : HwMaschine) (c : Nat)
    (g : LockAllUd) (len : Nat) :
    hwLockAllSchritt m c (.ud g len) = none := rfl

/-- A mapped row IS the accepted plug step on the mapped form. -/
theorem hwLockAllSchritt_aufgenommen (m : HwMaschine) (c : Nat)
    (f : LockAllForm) (len : Nat) (lf : LockForm)
    (h : lockAllAufLock f = some lf) :
    hwLockAllSchritt m c (.ok f len) =
      hwLockSchritt m c (.ok lf len) := by
  simp only [hwLockAllSchritt, h]

/-- An unmapped row refuses the family step. -/
theorem hwLockAllSchritt_abgelehnt (m : HwMaschine) (c : Nat)
    (f : LockAllForm) (len : Nat)
    (h : lockAllAufLock f = none) :
    hwLockAllSchritt m c (.ok f len) = none := by
  simp only [hwLockAllSchritt, h]

/-- Every admitted family step preserves well-formedness: only core
    data moves through the accepted re-embedding, profiles stay. -/
theorem adapterLockAll_wf (m : HwMaschine) (c : Nat)
    (a : LockAllAnweisung) (m' : HwMaschine) (hwf : HwWf m)
    (h : adapterLockAll.schritt m c a = some m') :
    HwWf m' := by
  have h2 : hwLockAllSchritt m c a = some m' := h
  cases a with
  | ud g len =>
    rw [hwLockAllSchritt_ud] at h2
    cases h2
  | ok f len =>
    simp only [hwLockAllSchritt] at h2
    cases hm : lockAllAufLock f with
    | none =>
      rw [hm] at h2
      cases h2
    | some lf =>
      rw [hm] at h2
      exact adapterLockRmw_wf m c _ m' h2 hwf

/-! ## 8. Joint witness: the family step runs the two-core LOCK run.

  The canonical 64-bit XADD form maps onto the accepted 662 XADD row,
  so the family step replays the accepted two-core locked-add run
  (word 10 to 15 on core 0, 15 to 22 on core 1 after the drain) with
  owner-only forwarding of the foreign buffered byte. Unmapped rows
  and parsed UD refuse beside the run. -/

/-- The canonical XADD form maps onto the accepted 662 XADD row. -/
theorem aufLock_canonXadd64 :
    lockAllAufLock canonXadd64 = some (.xadd64 .rax .rbp 0) := by
  decide

/-- Unmapped canonical rows map to none. -/
theorem aufLock_canonAdd32_nichts :
    lockAllAufLock canonAdd32 = none := by
  decide

theorem aufLock_canonInc64_nichts :
    lockAllAufLock canonInc64 = none := by
  decide

theorem aufLock_canonBts32_nichts :
    lockAllAufLock canonBts32 = none := by
  decide

theorem aufLock_canonXaddPlain64_nichts :
    lockAllAufLock canonXaddPlain64 = none := by
  decide

/-- Core 0 family step is the accepted core 0 step. -/
theorem hwLockAll_nach1 :
    hwLockAllSchritt hwLockWitStart 0 (.ok canonXadd64 9) =
      hwLockWitNach1 := by
  have e := hwLockAllSchritt_aufgenommen hwLockWitStart 0
    canonXadd64 9 _ aufLock_canonXadd64
  rw [e]
  rfl

/-- After the drain, the core 1 family step is the accepted step. -/
def hwLockAllNach2 : Option HwMaschine :=
  match hwLockWitBereit2 with
  | some m2 => hwLockAllSchritt m2 1 (.ok canonXadd64 9)
  | none => none

theorem hwLockAll_nach2 :
    hwLockAllNach2 = hwLockWitNach2 := by
  have e (m2 : HwMaschine) :=
    hwLockAllSchritt_aufgenommen m2 1
      canonXadd64 9 _ aufLock_canonXadd64
  unfold hwLockAllNach2 hwLockWitNach2
  cases h : hwLockWitBereit2 with
  | none => rfl
  | some m2 =>
    show hwLockAllSchritt m2 1 (.ok canonXadd64 9) =
      hwLockSchritt m2 1
        (.ok (.xadd64 .rax .rbp 0) 9)
    exact e m2

/-- Step one moves the word 10 to 15 through the family step. -/
theorem hwLockAll_nach1_wort :
    hwLockWort hwLockWitAdr
      (hwLockAllSchritt hwLockWitStart 0 (.ok canonXadd64 9)) =
      some 15 := by
  rw [hwLockAll_nach1]
  exact hwLockWit_nach1_wort

/-- Step one returns the old word through rax. -/
theorem hwLockAll_nach1_rax :
    hwLockReg 0 .rax
      (hwLockAllSchritt hwLockWitStart 0 (.ok canonXadd64 9)) =
      some 10 := by
  rw [hwLockAll_nach1]
  exact hwLockWit_nach1_rax

/-- Owner-only forwarding through the family step. -/
theorem hwLockAll_nach1_sicht :
    hwLockSicht (hwLockAllSchritt hwLockWitStart 0 (.ok canonXadd64 9))
        1 hwLockWitFremdAdr =
        some (some (BitVec.ofNat 8 99)) ∧
      hwLockSicht (hwLockAllSchritt hwLockWitStart 0 (.ok canonXadd64 9))
        0 hwLockWitFremdAdr =
        some (some (BitVec.ofNat 8 0)) := by
  rw [hwLockAll_nach1]
  exact ⟨hwLockWit_nach1_eigen_sicht, hwLockWit_nach1_fremd_sicht⟩

/-- Step two moves the word 15 to 22 on the other core. -/
theorem hwLockAll_nach2_wort :
    hwLockWort hwLockWitAdr hwLockAllNach2 = some 22 := by
  rw [hwLockAll_nach2]
  exact hwLockWit_nach2_wort

/-- Step two returns the old word through core 1 rax. -/
theorem hwLockAll_nach2_rax1 :
    hwLockReg 1 .rax hwLockAllNach2 = some 15 := by
  rw [hwLockAll_nach2]
  exact hwLockWit_nach2_rax1

/-- Group-1 refuses the family step. -/
theorem hwLockAll_add32_nichts :
    hwLockAllSchritt hwLockWitStart 0 (.ok canonAdd32 7) = none :=
  hwLockAllSchritt_abgelehnt _ _ _ _ aufLock_canonAdd32_nichts

/-- A parsed UD refuses the family step. -/
theorem hwLockAll_ud_nichts :
    hwLockAllSchritt hwLockWitStart 0 (.ud .regZiel 5) = none :=
  hwLockAllSchritt_ud _ _ _ _

/-- An unlocked XADD refuses the family step (no LOCK, no atomicity). -/
theorem hwLockAll_xaddPlain64_nichts :
    hwLockAllSchritt hwLockWitStart 0 (.ok canonXaddPlain64 8) =
      none :=
  hwLockAllSchritt_abgelehnt _ _ _ _ aufLock_canonXaddPlain64_nichts

/-- Joint family witness on the coherent machine: a reached two-core
    locked-add run (word 10 to 15 to 22 in canonical memory, old words
    through rax on both cores, owner-only forwarding of the foreign
    byte) beside the Group-1, UD and unlocked-XADD refusals and the
    new-arm chain evidence. Non-degenerate: both steps change actual
    shared memory. -/
theorem lockAll_zeuge :
    hwLockWort hwLockWitAdr
        (hwLockAllSchritt hwLockWitStart 0 (.ok canonXadd64 9)) =
        some 15 ∧
      hwLockReg 0 .rax
        (hwLockAllSchritt hwLockWitStart 0 (.ok canonXadd64 9)) =
        some 10 ∧
      hwLockSicht
        (hwLockAllSchritt hwLockWitStart 0 (.ok canonXadd64 9)) 1
        hwLockWitFremdAdr = some (some (BitVec.ofNat 8 99)) ∧
      hwLockSicht
        (hwLockAllSchritt hwLockWitStart 0 (.ok canonXadd64 9)) 0
        hwLockWitFremdAdr = some (some (BitVec.ofNat 8 0)) ∧
      hwLockWort hwLockWitAdr hwLockAllNach2 = some 22 ∧
      hwLockReg 1 .rax hwLockAllNach2 = some 15 ∧
      HwWf hwLockWitStart ∧
      hwLockAllSchritt hwLockWitStart 0 (.ok canonAdd32 7) = none ∧
      hwLockAllSchritt hwLockWitStart 0 (.ud .regZiel 5) = none ∧
      hwLockAllSchritt hwLockWitStart 0 (.ok canonXaddPlain64 8) =
        none ∧
      kapDecodeAll [natByte 240, natByte 72, natByte 255, natByte 133,
          natByte 0, natByte 0, natByte 0, natByte 0] =
        some (.neu (.ok canonInc64 8), []) := by
  refine ⟨hwLockAll_nach1_wort, hwLockAll_nach1_rax,
    hwLockAll_nach1_sicht.1, hwLockAll_nach1_sicht.2,
    hwLockAll_nach2_wort, hwLockAll_nach2_rax1, hwLockWitStart_wf,
    hwLockAll_add32_nichts, hwLockAll_ud_nichts,
    hwLockAll_xaddPlain64_nichts, kapAll_neu_inc64⟩

/- CUTS:
    Proved here: the whole LOCK read-modify-write family as one
    vocabulary (`LockAllOp` over `Breite`) with canonical per-class
    byte encodings and closed encode pins; a family decoder with
    exact consumed lengths, closed decode pins on ten canonical rows
    (a checked byte round trip with the encode pins), and closed
    refusal pins of the accepted `kapDecode` on all eight new rows;
    the extended chain `kapDecodeAll` (accepted chain first, family
    arm where it refuses, exact-agreement and no-shadow theorems,
    one old-arm pin reusing `kapKette_lock`, eight new-arm pins);
    pure value functions that ARE the accepted evaluators
    (`addB`/`orB`/`adcWert`/`sbbWert`/`andB`/`subB`/`xorB`,
    `incWert`/`decWert`, `negW`, `notB`, `btRoh`, `btBit`) with one
    rfl-agreement theorem per arm; the map `lockAllAufLock` onto the
    accepted 662 rows with general non-map, narrow-width and
    missing-LOCK refusals; the family step `hwLockAllSchritt` and the
    producer plug `adapterLockAll` with `HwWf` preservation, exact
    step agreement and UD/refusal selection; and the reached
    non-degenerate two-core joint witness `lockAll_zeuge` (word 10
    to 15 to 22 across two cores, owner-only forwarding, all
    refusals beside the run).
    Silicon provenance: the 662 XADD/CMPXCHG/MFENCE rows are the
    accepted rows (Intel SDM 325462-093US via lane 662); the new
    opcode numbers, prefix order rule, ModRM mod 2 layout, SIB-36
    subset, Group digits, imm sizes and the LOCK-on-register and
    LOCK-without-write UD rules are standard SDM Vol. 2A/2B entries
    encoded here as self-consistent tables, checked only against
    their own round-trip pins, not against silicon beyond the
    clone-local extracts. Named silicon assumptions: cache-line and
    split-lock behaviour are inherited unchanged from the accepted
    `HwLockFetch` layer; flag snapshots for the newly decoded (but
    never executed) rows are NOT defined here beyond the reused
    value and CF functions.
    NOT proved here, and not claimed:
    - No hardware correspondence beyond self-consistency for any new
      row: encodings are checked tables, not x86 truth.
    - No execution of Group-1, INC/DEC/NEG/NOT, bit-test or
      CMPXCHG8B rows: the adapter refuses them (stated admission
      refusals). Their value functions stand ready for the producer
      that discharges the memory, flag and ordering guards.
    - Narrower widths (8/16/32-bit XADD/CMPXCHG have accepted value
      functions but no admitted step), mod-1 disp8 rows, mod-0 rm-5
      RIP-relative rows, non-36 SIB bytes and redundant-prefix
      repetitions stay refused at the decoder (see §4); the encoder
      is canonical (mod 2) only.
    - No universal encode/decode round trip: only the ten closed
      canonical rows are pinned.
    - No W/GX refinement and no per-access linearisation: the bridge
      owns them. No cycle, latency, progress or retry-bound claim.
    - Maintainer extension point: widen `decodeLock` in
      `TSO/Verriegelt/LockedInstructionExecution.lean` with the new
      rows of `decodeLockAll`, lift the §1 value functions into the
      accepted step, and extend `kapDecode` with a family arm behind
      `kapDecodeAll_neu`.
-/

#print axioms lockAllWert_add
#print axioms lockAllWert_bts
#print axioms lockAllCf_bts
#print axioms enc_xadd64
#print axioms dec_xadd64
#print axioms kap_weist_xaddPlain64_zurueck
#print axioms kapDecodeAll_stimmt_alt
#print axioms kapDecodeAll_neu
#print axioms kapAllKette_lock
#print axioms kapAll_neu_inc64
#print axioms lockAllAufLock_ablehnung
#print axioms lockAllAufLockWort_schmal
#print axioms lockAllAufLockWort_ohne_lock
#print axioms hwLockAllSchritt_aufgenommen
#print axioms hwLockAllSchritt_abgelehnt
#print axioms adapterLockAll_wf
#print axioms aufLock_canonXadd64
#print axioms hwLockAll_nach1_wort
#print axioms hwLockAll_nach2_wort
#print axioms lockAll_zeuge

end Gabbro.Grammatik.X86
