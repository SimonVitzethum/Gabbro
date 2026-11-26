/-
  File:      core/Core/Ziel/Korrektheit/WaechterAnalyse.lean
  Subject:   THE COMPUTABLE GUARD CHECKER (design decision `pruefer-waechter`): a decidable static
             interval analysis of the guard demands (`teilen`, `liesArray`, `textIndex`, `substring`)
             over the instruction sequence, with a static value abstraction of the temporary
             registers, as the language checker will run it.

  The analysis is flow-insensitive and entirely static: every transfer is a constant read off
  the instruction (literals, text lengths, array element types), so one fold over the code
  already is a post-fixpoint — no iteration, no fuel, no widening. Unknown same-kind writes
  (arithmetic results, division results, locals read back) poison their slot to top (`none`),
  which is always sound. Control flow needs no case split: the joined environment
  overapproximates every reachable frame on every path, including jumps, calls, interrupts
  and restarts.

  The named decidable fragment (`waechterFragmentCode`) is the class on which the analysis
  is complete: no access or lifecycle instructions, every guard instruction sits in the
  linear prefix before the first control-flow instruction, and every operand slot it reads
  is written exactly once in the whole code, before the guard, by a constant write. On
  this class runtime values at the guard are exactly the analysed constants, so a held
  guard implies a passing static check. Outside the class completeness fails: value- and
  path-dependent guards are undecidable (`PrueferRestUnentscheidbarAussage`, Rice transfer).
-/
module

public import Core.Ast.Semantik.Runtime.Befehl
public import Core.Ast.TextValue.Bytes

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse

open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Ast
open Gabbro.Core.Aussenfrage

/-- A static integer contribution: an unknown same-kind write poisons the slot to top. -/
inductive IntBeitrag where
  | unbekannt
  | intervall (lo hi : Int)
  deriving DecidableEq, Repr

/-- A static text-length contribution: an unknown same-kind write poisons the slot to top. -/
inductive TextBeitrag where
  | unbekannt
  | laenge (lo hi : Nat)
  deriving DecidableEq, Repr

/-- Every temporary slot an instruction may write. Calls reset temporaries (sound to ignore
    in the join) and returns restore saved ones (covered by the saved-temporary invariant);
    access instructions are excluded globally. An outside answer poisons its target slot:
    `frage` binds its answer and `verbrauche` takes the next arrived answer into its slot,
    so both write unknown values there. The frame transfer is currently the identity for
    these forms; poisoning is the conservative reading that stays sound when the answer
    binding lands. -/
def schreibtTemp : Befehl → List Nat
  | .literal dst _ | .negativ dst _ | .binaer _ dst | .wahrheitswert dst _ | .lesen dst _
  | .negieren dst | .verneinen dst | .teilen dst | .vergleichen _ dst => [dst]
  | .baueArray dst _ _ | .liesArray dst _ _ | .baueTupel dst _ | .liesTupelfeld dst _ _
  | .baueRecord dst _ _ _ _ | .liesRecordFeld dst _ _ _ _ | .baueVariante dst _ _ _ _
  | .textLiteral dst _ | .textConcat dst _ _ | .textIndex dst _ | .substring dst _
  | .textLength dst _ | .optionIstBesetzt dst _ => [dst]
  | .aussen (.frage ziel _ _) => [ziel]
  | .aussen (.verbrauche ziel) => [ziel]
  | _ => []

/-- The static integer information one instruction writes to one slot: `none` means the
    instruction does not write a temporary there; every other temporary write poisons the
    slot (`unbekannt`), which is always sound. -/
def beitragInt : Befehl → Nat → Option IntBeitrag
  | .literal dst val, s => if s = dst then some (.intervall val val) else none
  | .negativ dst betrag, s =>
    if s = dst then some (.intervall (-(betrag : Int)) (-(betrag : Int))) else none
  | .liesArray basis (.int lo hi) _, s =>
    if s = basis then some (.intervall lo hi) else none
  | .liesArray basis _ _, s =>
    if s = basis then some .unbekannt else none
  | .textIndex basis _, s => if s = basis then some (.intervall 0 255) else none
  | .textLength basis capacity, s =>
    if s = basis then some (.intervall 0 capacity) else none
  | b, s => if s ∈ schreibtTemp b then some .unbekannt else none

/-- The static text-length information one instruction writes to one slot. -/
def beitragText : Befehl → Nat → Option TextBeitrag
  | .textLiteral dst decoded, s =>
    if s = dst then some (.laenge (sourceUtf8 decoded).size (sourceUtf8 decoded).size) else none
  | .textConcat dst a b, s => if s = dst then some (.laenge 0 (a + b)) else none
  | .substring dst capacity, s => if s = dst then some (.laenge 0 capacity) else none
  | b, s => if s ∈ schreibtTemp b then some .unbekannt else none

/-- Join one integer interval into the running hull; unknown writes are handled
    separately by `slotUnbekanntInt`, so the join only ever widens. -/
def huelleIntAux : Option (Int × Int) → Option IntBeitrag → Option (Int × Int)
  | acc, some (.intervall lo hi) => match acc with
    | none => some (lo, hi)
    | some (a, b) => some (min a lo, max b hi)
  | acc, _ => acc

/-- The hull of every static integer interval written to the slot. -/
def huelleInt (code : List Befehl) (slot : Nat) : Option (Int × Int) :=
  code.foldr (fun b acc => huelleIntAux acc (beitragInt b slot)) none

/-- Whether an unknown integer write reaches the slot anywhere in the code. -/
def slotUnbekanntInt (code : List Befehl) (slot : Nat) : Bool :=
  code.any fun b => match beitragInt b slot with
    | some .unbekannt => true
    | _ => false

/-- The joined integer environment of the whole code at one slot: the hull of every static
    contribution, top (`none`) when an unknown write reaches the slot. -/
def umgebungInt (code : List Befehl) (slot : Nat) : Option (Int × Int) :=
  match slotUnbekanntInt code slot with
  | true => none
  | false => huelleInt code slot

/-- Join one text-length interval into the running hull. -/
def huelleTextAux : Option (Nat × Nat) → Option TextBeitrag → Option (Nat × Nat)
  | acc, some (.laenge lo hi) => match acc with
    | none => some (lo, hi)
    | some (a, b) => some (min a lo, max b hi)
  | acc, _ => acc

/-- The hull of every static text-length interval written to the slot. -/
def huelleText (code : List Befehl) (slot : Nat) : Option (Nat × Nat) :=
  code.foldr (fun b acc => huelleTextAux acc (beitragText b slot)) none

/-- Whether an unknown text write reaches the slot anywhere in the code. -/
def slotUnbekanntText (code : List Befehl) (slot : Nat) : Bool :=
  code.any fun b => match beitragText b slot with
    | some .unbekannt => true
    | _ => false

/-- The joined text-length environment of the whole code at one slot. -/
def umgebungText (code : List Befehl) (slot : Nat) : Option (Nat × Nat) :=
  match slotUnbekanntText code slot with
  | true => none
  | false => huelleText code slot

/-- The static guard check of one instruction under the joined environments. -/
def pruefeBedarf (code : List Befehl) : Befehl → Bool
  | .teilen links =>
    match umgebungInt code (links + 1) with
    | some (lo, hi) => decide (1 ≤ lo ∨ hi ≤ -1)
    | none => false
  | .liesArray basis _ count =>
    match umgebungInt code (basis + 1) with
    | some (lo, hi) => decide (0 ≤ lo ∧ hi < (count : Int))
    | none => false
  | .textIndex basis _ =>
    match umgebungText code basis, umgebungInt code (basis + 1) with
    | some (laenge, _), some (lo, hi) => decide (0 ≤ lo ∧ hi < (laenge : Int))
    | _, _ => false
  | .substring basis _ =>
    match umgebungText code basis, umgebungInt code (basis + 1), umgebungInt code (basis + 2) with
    | some (laenge, _), some (loErste, hiErste), some (loLetzte, hiLetzte) =>
      decide (0 ≤ loErste ∧ hiErste ≤ loLetzte ∧ hiLetzte ≤ (laenge : Int))
    | _, _, _ => false
  | _ => true

/-- Access and lifecycle instructions are outside the guard analysis and refused. -/
def keinFremdzugriff : Befehl → Bool
  | .zugriff _ | .faden _ => false
  | _ => true

/-- The computable guard verdict over an instruction sequence. -/
def waechterPruefeCode (code : List Befehl) : Bool :=
  code.all keinFremdzugriff && code.all (pruefeBedarf code)

/-- Instructions that end the linear prefix: anything that does not advance `pc` by exactly
    one. Definitions skip over their function body, calls and returns leave the linear flow,
    and `ende` stops the context. -/
def istSteuerung : Befehl → Bool
  | .springeWenn .. | .springe .. | .definiere .. | .rufe .. | .rueckVoid | .zurueck ..
  | .whileTest .. | .forAnfang .. | .forTest .. | .forNaechster .. | .zurueckSprung ..
  | .starte .. | .ende | .waehleVariante .. | .zugriff _ | .faden _ => true
  | _ => false

/-- Instructions allowed in the linear prefix: linear `pc` advance and no halt. Region
    binding can halt on a bad region, so it is excluded from the exact prefix. -/
def prefixRein : Befehl → Bool
  | b => !istSteuerung b && match b with
    | .bindeRegion .. => false
    | _ => true

/-- The kind of an operand slot a guard reads. -/
inductive OperandenArt where
  | ganz
  | text
  deriving DecidableEq, Repr, BEq

/-- Every temporary slot a guard instruction reads: the dividend matters too, since the
    guard only fires when all reads succeed. Array contents do not affect the guard. -/
def bedarfStellen : Befehl → List (Nat × OperandenArt)
  | .teilen links => [(links, .ganz), (links + 1, .ganz)]
  | .liesArray basis _ _ => [(basis + 1, .ganz)]
  | .textIndex basis _ => [(basis, .text), (basis + 1, .ganz)]
  | .substring basis _ => [(basis, .text), (basis + 1, .ganz), (basis + 2, .ganz)]
  | _ => []

/-- Constant integer writes: their runtime value is exactly the analysed one. -/
def konstIntSchreibung : Befehl → List Nat
  | .literal dst _ | .negativ dst _ => [dst]
  | _ => []

/-- Constant text writes: their runtime length is exactly the analysed one. -/
def konstTextSchreibung : Befehl → List Nat
  | .textLiteral dst _ => [dst]
  | _ => []

/-- All positions (other than `ausser`) in the code that may write the slot. -/
def schreibungenAn (code : List Befehl) (ausser slot : Nat) : List Nat :=
  (List.range code.length).filter fun i =>
    i != ausser && match code[i]? with
      | some b => (schreibtTemp b).contains slot
      | none => false

/-- One operand slot is covered when it is written exactly once in the whole code, before
    the guard, by a constant write — then its runtime value at the guard is exactly the
    analysed constant on every path that reaches the guard with a present value. -/
def operandAbgedeckt (code : List Befehl) (pos : Nat) : Nat × OperandenArt → Bool
  | (slot, .ganz) => match schreibungenAn code pos slot with
    | [i] => decide (i < pos) && match code[i]? with
      | some b => (konstIntSchreibung b).contains slot
      | none => false
    | _ => false
  | (slot, .text) => match schreibungenAn code pos slot with
    | [i] => decide (i < pos) && match code[i]? with
      | some b => (konstTextSchreibung b).contains slot
      | none => false
    | _ => false

/-- The named decidable fragment: no access instructions, every guard instruction sits in
    the linear prefix before the first control-flow instruction, and every slot it reads
    is covered by exactly one preceding constant write. -/
def waechterFragmentCodeAux : List Befehl → List Befehl → Nat → Bool → Bool
  | [], _, _, _ => true
  | b :: rest, code, pos, inPrefix =>
    let inPrefix' := inPrefix && prefixRein b
    (inPrefix' || bedarfStellen b == []) &&
    ((bedarfStellen b).all (operandAbgedeckt code pos)) &&
    waechterFragmentCodeAux rest code (pos + 1) inPrefix'

/-- The named decidable fragment on which the guard checker is complete. -/
def waechterFragmentCode (code : List Befehl) : Bool :=
  code.all keinFremdzugriff && waechterFragmentCodeAux code code 0 true

end Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse
