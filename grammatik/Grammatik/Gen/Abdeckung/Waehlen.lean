/-
  File:      Grammatik/Gen/Abdeckung/Waehlen.lean
  Subject:   The CHOICE of cell programs and the GENERATOR that emits them WITH THEIR PROOFS: the tables of the bodies with
             one body per cell-relevant summary (`Rumpf.schluessel`), the members the cell driver ranges over, and
             `Spez.erzeuge`, which emits a program only as a `Gutes` (the Lean model's Bool accepts it) or a `Schlechtes c`
             (exactly component `c` refuses it), each carrying the proof as a field. Used by `ZellenLauf.lean`.
-/
import Grammatik.Gen.Abdeckung.Messung
import Grammatik.Gen.Abdeckung.Zellen
import Grammatik.Gen.Familie.ZellFamilie

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

/-- **The tables of the bodies, one body per cell-relevant summary** (`Rumpf.schluessel`): scanning the sizes upward, a
    body is kept only if no smaller body of the same function has its summary. -/
def Spez.tabellenD (z : Spez) (nb : Nat) :
    List (Σ f : z.deklaration.Fn, List (List (Rumpf z.deklaration f))) :=
  letI : Zahlen := z.zahlen
  (z.tabellen nb false false).map fun t =>
    ⟨t.1, (t.2.foldl
      (fun (acc : List (List (Rumpf z.deklaration t.1)) × List (List Bool)) bucket =>
        let r := bucket.foldl
          (fun (a : List (Rumpf z.deklaration t.1) × List (List Bool)) b =>
            let k := b.schluessel
            if a.2.contains k then a else (a.1 ++ [b], a.2 ++ [k])) ([], acc.2)
        (acc.1 ++ [r.1], r.2)) ([], [])).1⟩


/-- **The members** the cell driver ranges over: the sixteen of the family and the cell members. -/
def mitglieder : List Spez := familie ++ zellFamilie

/-! ## The generator with the proof IN its output

  A program of the cell sweep is born together with the proof of its class: `Gutes` holds the program, the lock family,
  the starts AND the proof that the Lean model's Bool `AkzeptiertX` accepts it; `Schlechtes c` holds the proof that
  exactly component `c` refuses it. The generator can only build these values by deciding the class (`if h : … then`),
  so nothing it emits is unproved, and nothing is checked afterwards. The only oracle is the Lean model's own Bool
  (`komp`, `AkzeptiertX`); the Rust checker is not consulted. -/

/-- The functions and locks of a member, as the lists the checker is asked over. -/
def Spez.fnListe (z : Spez) : List z.deklaration.Fn := List.finRange z.fns.length

def Spez.lockListe (z : Spez) : List z.deklaration.Lock := List.finRange z.locks.length

/-- The Lean model's Bool `AkzeptiertX` on a skeleton of a member, with the instances named once. -/
def Spez.gutB (z : Spez) (h : Haut z.deklaration) (S : SperrInv z.deklaration) (ws : List z.deklaration.Fn) : Bool :=
  @AkzeptiertX z.deklaration z.aufz.decFn h.programm S z.fnListe z.lockListe z.traegerListe ws

/-- `nurAnB`: component `c` refuses the program and the other nine accept it. -/
def Spez.nurB (z : Spez) (c : Fin 10) (h : Haut z.deklaration) (S : SperrInv z.deklaration)
    (ws : List z.deklaration.Fn) : Bool :=
  @nurAnB z.deklaration z.aufz z.zahlen c h.programm S z.fnListe z.lockListe z.traegerListe ws

/-- A valid program with its proof. -/
structure Gutes (z : Spez) where
  haut : Haut z.deklaration
  S : SperrInv z.deklaration
  ws : List z.deklaration.Fn
  gueltig : z.gutB haut S ws = true

/-- A program refused by exactly component `c`, with its proof. -/
structure Schlechtes (z : Spez) (c : Fin 10) where
  haut : Haut z.deklaration
  S : SperrInv z.deklaration
  ws : List z.deklaration.Fn
  nurAn : z.nurB c haut S ws = true

/-- The proof of a `Gutes` is the statement of the goal theorem's checker: the Lean model accepts the program. -/
theorem Gutes.akzeptiert {z : Spez} (g : Gutes z) :
    @AkzeptiertX z.deklaration z.aufz.decFn g.haut.programm g.S z.fnListe z.lockListe z.traegerListe g.ws = true :=
  g.gueltig

/-- The proof of a `Schlechtes` is `NurAn`: component `c` refuses, the other nine accept. -/
theorem Schlechtes.istNurAn {z : Spez} {c : Fin 10} (s : Schlechtes z c) :
    @NurAn z.deklaration z.aufz c s.haut.programm s.S z.fnListe z.lockListe z.traegerListe s.ws :=
  (@nurAnB_iff z.deklaration z.aufz z.zahlen c s.haut.programm s.S z.fnListe z.lockListe z.traegerListe s.ws).1 s.nurAn

/-- What the generator emits: a valid program or a single-fault program, each with its proof. -/
inductive Erzeugt (z : Spez)
  | gut (g : Gutes z)
  | schlecht (c : Fin 10) (s : Schlechtes z c)

/-- The lock families and starts the sweep asks the question for: the declared starts (the first root alone, every
    root), one more start, a single start, a doubled start; the maximal lock family and the one that protects a
    carrier its lock does not guard. These are PARAMETERS of the generator, as in `genGueltig`/`genBad`. -/
def Spez.parameter (z : Spez) : List (SperrInv z.deklaration × List z.deklaration.Fn) :=
  let fns : List z.deklaration.Fn := List.finRange z.fns.length
  let wsA : List z.deklaration.Fn := z.wurzeln.take 1
  let wsB : List z.deklaration.Fn := z.wurzeln
  let wsListe : List (List z.deklaration.Fn) :=
    (if wsA == wsB then [wsA] else [wsA, wsB]).flatMap fun ws =>
      [ws] ++ fns.map (fun w => ws ++ [w])
    ++ fns.map (fun w => [w]) ++ fns.map (fun w => [w, w])
  let Ss : List (SperrInv z.deklaration) := [z.sperreMax, SperrInv.leer z.deklaration] ++ z.schlechteSperre.toList
  Ss.flatMap fun S => wsListe.map fun ws => (S, ws)

/-- **The generator, one skeleton**: the skeleton under the lock family `S` and the starts `ws`, emitted with the proof of
    its class when it is valid or refused by exactly one component, else nothing. The class is decided here, once, by
    the Lean model's Bool; the value cannot be built without the proof. -/
def Spez.erzeugeAus (z : Spez) (h : Haut z.deklaration) (S : SperrInv z.deklaration)
    (ws : List z.deklaration.Fn) : Option (Erzeugt z) :=
  letI : Zahlen := z.zahlen
  match hv : z.gutB h S ws with
  | true => some (.gut ⟨h, S, ws, hv⟩)
  | false =>
    match (List.finRange 10).filter (fun c => z.nurB c h S ws) with
    | [c] =>
      match hn : z.nurB c h S ws with
      | true => some (.schlecht c ⟨h, S, ws, hn⟩)
      | false => none
    | _ => none

/-- **The generator**: every skeleton of exact size `k` of the tables `tbls` (built once per member by
    `Spez.tabellenD`), under `S` and `ws`, as `erzeugeAus` emits them. -/
def Spez.erzeuge (z : Spez) (tbls : List (Σ f : z.deklaration.Fn, List (List (Rumpf z.deklaration f)))) (k : Nat)
    (S : SperrInv z.deklaration) (ws : List z.deklaration.Fn) : List (Erzeugt z) :=
  letI : Zahlen := z.zahlen
  (hautT tbls k).filterMap fun h => z.erzeugeAus h S ws

end Gabbro.Grammatik.Gen
