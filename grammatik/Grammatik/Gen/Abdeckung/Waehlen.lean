/-
  File:      Grammatik/Gen/Abdeckung/Waehlen.lean
  Subject:   The CHOICE of cell programs and the GENERATOR that emits them WITH THEIR PROOFS: the tables of the bodies with
             one body per cell-relevant summary (`Rumpf.schluessel`), the members the cell driver ranges over, and
             `Spez.erzeugeF`, which emits a program only as a `Gutes` (the Lean model's Bool accepts it) or a `Schlechtes c`
             (exactly component `c` refuses it), each carrying the proof as a field. Used by `ZellenBefund.lean`.
-/
import Grammatik.Gen.Abdeckung.Messung
import Grammatik.Gen.Abdeckung.Zellen
import Grammatik.Gen.Familie.ZellFamilie
import Grammatik.Gen.Erzeuger.Strom
import Grammatik.Gen.Abdeckung.Satz.KoerperOrte
import Grammatik.Gen.Erzeuger.Entdoppelt
import Grammatik.Gen.Erzeuger.Kompakt.Merken

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

/-- **The tables of the bodies, one body per cell-relevant summary** (`Rumpf.schluessel`): the bodies of the generator
    one per key (`rumpfTK`), scanned by size upward; a body is kept only if no smaller body of the same function has its
    summary. (The floors are a property of the whole program, `Spez.bodenOk`.) -/
def Spez.tabellenD (z : Spez) (nb : Nat) :
    List (Σ f : z.deklaration.Fn, List (List (Rumpf z.deklaration f))) :=
  letI : Zahlen := z.zahlen
  (Aufz.fn (D := z.deklaration)).map fun f =>
    ⟨f, entdoppelt Rumpf.schluessel (fun _ => false) (rumpfTK (fun _ _ => true) f nb)⟩

/-- **A member in the language's form**: one signature per function (the language numbers a function's signature by
    the function, `declOf` of the Lean front end), and a function of a unit with locks declares a floor (the language
    derives one above every rank when no lock is taken on its paths, never none). -/
def Spez.einzeln (z : Spez) : Spez :=
  let hoch : Int := (z.locks.map (·.rang)).foldl max 0 + 1
  { z with
    sigs := z.fns.map fun i =>
      let s := z.sigs.getD i {}
      if !z.locks.isEmpty && s.boden.isNone then { s with boden := some hoch } else s
    fns := List.range z.fns.length }

/-- **The members** the cell driver ranges over: the sixteen of the family, the hand-written cell members and the rule
    members, each in the language's form. -/
def mitglieder : List Spez := (familie ++ zellFamilie ++ regelMitglieder).map Spez.einzeln

/-! ## The generator with the proof IN its output

  A program of the cell sweep is born together with the proof of its class: `Gutes` holds the program, the lock family,
  the starts AND the proof that the Lean model's Bool `AkzeptiertX` accepts it; `Schlechtes c` holds the proof that
  exactly component `c` refuses it. The generator can only build these values by deciding the class (`if h : … then`),
  so nothing it emits is unproved, and nothing is checked afterwards. The only oracle is the Lean model's own Bool
  (`komp`, `AkzeptiertX`); the Rust checker is not consulted. -/

/-- The functions and locks of a member, as the lists the checker is asked over. -/
def Spez.fnListe (z : Spez) : List z.deklaration.Fn := List.finRange z.fns.length

def Spez.lockListe (z : Spez) : List z.deklaration.Lock := List.finRange z.locks.length

/-- **The roots of a program**: the declared starts and every function the hardware enters. An `entry` item is a root
    of the unit (`UProg.hands` are roots too), so the model's Bool is asked over both. -/
def Spez.wurzelnVon (z : Spez) (P : Programm z.deklaration) (ws : List z.deklaration.Fn) : List z.deklaration.Fn :=
  ws ++ z.fnListe.filter fun f => P.unterbricht f

/-- The Lean model's Bool `AkzeptiertX` on a program of a member, with the instances named once. -/
def Spez.gutB (z : Spez) (P : Programm z.deklaration) (S : SperrInv z.deklaration) (ws : List z.deklaration.Fn) : Bool :=
  @AkzeptiertX z.deklaration z.aufz.decFn P S z.fnListe z.lockListe z.traegerListe ws

/-- `nurAnB`: component `c` refuses the program and the other nine accept it. -/
def Spez.nurB (z : Spez) (c : Fin 10) (P : Programm z.deklaration) (S : SperrInv z.deklaration)
    (ws : List z.deklaration.Fn) : Bool :=
  @nurAnB z.deklaration z.aufz z.zahlen c P S z.fnListe z.lockListe z.traegerListe ws

/-- Every body derives the declared floor: the floor is not written in the language, it is the least rank the body
    takes (`Druck/Einheit.lean`), so only such programs are programs of the source. -/
def Spez.bodenOk (z : Spez) (P : Programm z.deklaration) : Bool :=
  z.fnListe.all fun f => Programm.bodenP P f == (z.deklaration.signatur f).boden

/-- A valid program of the source with its proof: the lock family is the one the source has (`protects`). -/
structure Gutes (z : Spez) where
  prog : Programm z.deklaration
  ws : List z.deklaration.Fn
  ohneAx : z.axs = []
  boden : z.bodenOk prog = true
  gueltig : z.gutB prog z.sperreMax (z.wurzelnVon prog ws) = true

/-- A program of the source the model refuses, with its proof. -/
structure Abgelehntes (z : Spez) where
  prog : Programm z.deklaration
  ws : List z.deklaration.Fn
  ohneAx : z.axs = []
  boden : z.bodenOk prog = true
  abgelehnt : z.gutB prog z.sperreMax (z.wurzelnVon prog ws) = false

/-- The proof of a `Gutes` is the statement of the goal theorem's checker: the Lean model accepts the program. -/
theorem Gutes.akzeptiert {z : Spez} (g : Gutes z) :
    @AkzeptiertX z.deklaration z.aufz.decFn g.prog z.sperreMax z.fnListe z.lockListe z.traegerListe
      (z.wurzelnVon g.prog g.ws) = true :=
  g.gueltig

/-- What the generator emits: a valid program or a refused one, each with its proof. -/
inductive Erzeugt (z : Spez)
  | gut (g : Gutes z)
  | abgelehnt (a : Abgelehntes z)

/-- The starts the sweep asks the question for: the declared starts (the first root alone, every root), one more
    start, a single start, a doubled start. A PARAMETER of the generator, as in `genGueltig`/`genBad`. -/
def Spez.parameter (z : Spez) : List (List z.deklaration.Fn) :=
  let fns : List z.deklaration.Fn := List.finRange z.fns.length
  let wsA : List z.deklaration.Fn := z.wurzeln.take 1
  let wsB : List z.deklaration.Fn := z.wurzeln
  (if wsA == wsB then [wsA] else [wsA, wsB]).flatMap (fun ws => [ws] ++ fns.map (fun w => ws ++ [w]))
    ++ fns.map (fun w => [w]) ++ fns.map (fun w => [w, w])

/-- **The generator, one program**: the program under the starts `ws`, emitted with the proof of its class (valid or
    refused) when it is a program of the source, else nothing. The class is decided here, once, by
    the Lean model's Bool; the value cannot be built without the proof. -/
def Spez.erzeugeAus (z : Spez) (h : Programm z.deklaration) (ws : List z.deklaration.Fn) : Option (Erzeugt z) :=
  letI : Zahlen := z.zahlen
  if hax : z.axs = [] then
    match hb : z.bodenOk h with
    | false => none
    | true =>
      match hv : z.gutB h z.sperreMax (z.wurzelnVon h ws) with
      | true => some (.gut ⟨h, ws, hax, hb, hv⟩)
      | false => some (.abgelehnt ⟨h, ws, hax, hb, hv⟩)
  else none

/-- **Programs with contracts**: the skeleton's program (every contract `true`) and, for every function, the programs
    whose `requires` or whose `ensures` is one expression of size at most `nc` from the generator's expression stream,
    every other contract staying `true`. One contract at a time is what the cells of a contract carrier need (`0.0 1.1`,
    `2.3 ..0`). -/
def Spez.vertragsF {β : Type} (z : Spez) (nc : Nat) (h : Haut z.deklaration) (b : β) (s : β → Programm z.deklaration → β) :
    β :=
  letI : Zahlen := z.zahlen
  let P := h.programm
  z.fnListe.foldl (fun b f =>
    let b := (List.range (nc + 1)).foldl (fun b n => (reqS f nc n).foldl (fun b e =>
      s b { P with requires := fun g => if hg : g = f then hg ▸ e else Expr.tru }) b) b
    (List.range (nc + 1)).foldl (fun b n => (ensS f nc n).foldl (fun b e =>
      s b { P with ensures := fun g => if hg : g = f then hg ▸ e else Expr.tru }) b) b) (s b P)

/-- **The generator, one program after the other**: the skeletons of exact size `k` of the tables `tbls` (built once
    per member by `Spez.tabellenD`) come from the stream `hautF`, never as a list; each skeleton's contract variants up
    to size `nc`, under every parameter, go to the consumer as `erzeugeAus` emits them, each with its proof. -/
def Spez.erzeugeF (z : Spez) (tbls : List (Σ f : z.deklaration.Fn, List (List (Rumpf z.deklaration f)))) (nc : Nat) :
    Strom (Erzeugt z) := fun β k b s =>
  letI : Zahlen := z.zahlen
  hautF tbls β k b fun b h => z.vertragsF nc h b (fun b P =>
    (z.parameter.filterMap fun ws => z.erzeugeAus P ws).foldl s b)

/-- The bounds (bodies, skeleton size) of member `i`: the sixteen family members 5:6, the cell members 16-20 larger,
    the rule members 8 per body (a lock taken around a call or a read needs 8). -/
def grenzenVon (i : Nat) : Nat × Nat :=
  if i = 16 then (6, 14) else if 17 ≤ i ∧ i ≤ 19 then (6, 12) else if i = 20 then (7, 12)
  else if i ≥ familie.length + zellFamilie.length + regelSigs.length then (8, 16)
  else if i ≥ familie.length + zellFamilie.length then (8, 8) else (5, 6)

/-- The contract size the test sets are stated for (`mGen ncZiel`): a witness without a contract holds for every
    size, a witness with one needs its contract of size at most this. -/
def ncZiel : Nat := 2

end Gabbro.Grammatik.Gen
