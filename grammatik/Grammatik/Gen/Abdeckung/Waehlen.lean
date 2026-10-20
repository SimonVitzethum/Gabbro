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

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

/-- The floor the language derives from a body: the least rank of the locks the body itself takes (`none` if it takes none).
    The language does not write a floor; the model's signature carries one, so a unit can be printed faithfully only
    when the declared floor is this one. -/
def Rumpf.bodenAbgeleitet {D : Deklaration} [Aufz D] {f : D.Fn} (b : Rumpf D f) : Option Int :=
  ((Aufz.lock (D := D)).filter fun L =>
    !(mE ⟨fun _ => true, fun _ => true, fun L' => !(decide (L' = L))⟩ b)).map D.rang
    |>.foldl (fun a r => match a with | none => some r | some m => some (if m < r then m else r)) none

/-- The declared floor of a function. -/
def Spez.bodenSoll (z : Spez) (f : z.deklaration.Fn) : Option Int := (z.sigRoh (z.fns.get (show Fin z.fns.length from f))).boden

/-- **The tables of the bodies, one body per cell-relevant summary** (`Rumpf.schluessel`): scanning the sizes upward, a
    body is kept only if no smaller body of the same function has its summary. With `treu`, only the bodies whose derived
    floor is the declared one are kept: the SOURCE-FAITHFUL tables, whose programs the printer can write. -/
def Spez.tabellenD (z : Spez) (nb : Nat) (treu : Bool := false) :
    List (Σ f : z.deklaration.Fn, List (List (Rumpf z.deklaration f))) :=
  letI : Zahlen := z.zahlen
  (z.tabellen nb false false).map fun t =>
    ⟨t.1, entdoppelt Rumpf.schluessel (fun b => treu && b.bodenAbgeleitet != z.bodenSoll t.1) t.2⟩

/-- **The members** the cell driver ranges over: the sixteen of the family, the hand-written cell members and the rule members. -/
def mitglieder : List Spez := familie ++ zellFamilie ++ regelMitglieder

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

/-- The lock families the generator asks the question for, by name: only `quelle` has source syntax (the carriers
    each lock guards, `protects`, and no invariant: `Parser.Cover.Differenz.sperrFamilie`), so only a program under
    `quelle` can be printed; `leer` and `schlecht` stay Lean-level tests. -/
inductive Sperrart
  | quelle
  | leer
  | schlecht
  deriving DecidableEq, Repr

/-- The family of a name; `schlecht` is the one that protects a carrier its lock does not guard (`schlechteSperre`),
    which the parameters ask only where it exists. -/
def Spez.familie (z : Spez) : Sperrart → SperrInv z.deklaration
  | .quelle => z.sperreMax
  | .leer => SperrInv.leer z.deklaration
  | .schlecht => z.schlechteSperre.getD (SperrInv.leer z.deklaration)

/-- A valid program with its proof. -/
structure Gutes (z : Spez) where
  prog : Programm z.deklaration
  art : Sperrart
  ws : List z.deklaration.Fn
  gueltig : z.gutB prog (z.familie art) (z.wurzelnVon prog ws) = true

/-- A program refused by exactly component `c`, with its proof. -/
structure Schlechtes (z : Spez) (c : Fin 10) where
  prog : Programm z.deklaration
  art : Sperrart
  ws : List z.deklaration.Fn
  nurAn : z.nurB c prog (z.familie art) (z.wurzelnVon prog ws) = true

/-- The lock family of a valid program. -/
abbrev Gutes.S {z : Spez} (g : Gutes z) : SperrInv z.deklaration := z.familie g.art

/-- The lock family of a single-fault program. -/
abbrev Schlechtes.S {z : Spez} {c : Fin 10} (s : Schlechtes z c) : SperrInv z.deklaration := z.familie s.art

/-- The proof of a `Gutes` is the statement of the goal theorem's checker: the Lean model accepts the program. -/
theorem Gutes.akzeptiert {z : Spez} (g : Gutes z) :
    @AkzeptiertX z.deklaration z.aufz.decFn g.prog g.S z.fnListe z.lockListe z.traegerListe (z.wurzelnVon g.prog g.ws) = true :=
  g.gueltig

/-- The proof of a `Schlechtes` is `NurAn`: component `c` refuses, the other nine accept. -/
theorem Schlechtes.istNurAn {z : Spez} {c : Fin 10} (s : Schlechtes z c) :
    @NurAn z.deklaration z.aufz c s.prog s.S z.fnListe z.lockListe z.traegerListe (z.wurzelnVon s.prog s.ws) :=
  (@nurAnB_iff z.deklaration z.aufz z.zahlen c s.prog s.S z.fnListe z.lockListe z.traegerListe (z.wurzelnVon s.prog s.ws)).1 s.nurAn

/-- What the generator emits: a valid program or a single-fault program, each with its proof. -/
inductive Erzeugt (z : Spez)
  | gut (g : Gutes z)
  | schlecht (c : Fin 10) (s : Schlechtes z c)

/-- The lock families and starts the sweep asks the question for: the declared starts (the first root alone, every
    root), one more start, a single start, a doubled start; the maximal lock family and the one that protects a
    carrier its lock does not guard. These are PARAMETERS of the generator, as in `genGueltig`/`genBad`. -/
def Spez.parameter (z : Spez) : List (Sperrart × List z.deklaration.Fn) :=
  let fns : List z.deklaration.Fn := List.finRange z.fns.length
  let wsA : List z.deklaration.Fn := z.wurzeln.take 1
  let wsB : List z.deklaration.Fn := z.wurzeln
  let wsListe : List (List z.deklaration.Fn) :=
    (if wsA == wsB then [wsA] else [wsA, wsB]).flatMap fun ws =>
      [ws] ++ fns.map (fun w => ws ++ [w])
    ++ fns.map (fun w => [w]) ++ fns.map (fun w => [w, w])
  let Ss : List Sperrart := [.quelle, .leer] ++ (if z.schlechteSperre.isSome then [.schlecht] else [])
  Ss.flatMap fun S => wsListe.map fun ws => (S, ws)

/-- **The generator, one program**: the program under the lock family `S` and the starts `ws`, emitted with the proof of
    its class when it is valid or refused by exactly one component, else nothing. The class is decided here, once, by
    the Lean model's Bool; the value cannot be built without the proof. -/
def Spez.erzeugeAus (z : Spez) (h : Programm z.deklaration) (S : Sperrart)
    (ws : List z.deklaration.Fn) : Option (Erzeugt z) :=
  letI : Zahlen := z.zahlen
  match hv : z.gutB h (z.familie S) (z.wurzelnVon h ws) with
  | true => some (.gut ⟨h, S, ws, hv⟩)
  | false =>
    match (List.finRange 10).filter (fun c => z.nurB c h (z.familie S) (z.wurzelnVon h ws)) with
    | [c] =>
      match hn : z.nurB c h (z.familie S) (z.wurzelnVon h ws) with
      | true => some (.schlecht c ⟨h, S, ws, hn⟩)
      | false => none
    | _ => none

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
    (z.parameter.filterMap fun p => z.erzeugeAus P p.1 p.2).foldl s b)

/-- The bounds (bodies, skeleton size) of member `i`: the sixteen family members 5:6, the cell members 16-20 larger,
    the rule members 5:9. -/
def grenzenVon (i : Nat) : Nat × Nat :=
  if i = 16 then (6, 14) else if 17 ≤ i ∧ i ≤ 19 then (6, 12) else if i = 20 then (7, 12)
  else if i ≥ familie.length + zellFamilie.length then (5, 9) else (5, 6)

end Gabbro.Grammatik.Gen
