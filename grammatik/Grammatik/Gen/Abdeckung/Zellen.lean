/-
  File:      Grammatik/Gen/Abdeckung/Zellen.lean
  Subject:   THE CELLS of the ten components of `AkzeptiertX`, as computable data read off the program.

  A component is a conjunction, over tuples of functions, carriers, locks and starts, of a test on a few Bool ATOMS.
  A CELL is such a tuple's atom vector (`Zelle`); `Zelle.kern` is the test as a function of the vector ONLY. A
  program has a cell when some tuple of it has that vector; the component refuses the program exactly when it has a
  cell with `urteil = true` and `kern = false` (a BAD cell). Theorem 4 (`Adaequanz/Muster.lean`) asks for one
  single-fault program per isolable bad cell and valid programs for the good ones; this file makes the cells
  computable so that a set of programs can be MEASURED against them (`gen-zelle`, `Gen/Abdeckung/ZellenEins.lean`).

  The atoms are the ones the definitions of `Akzeptiert.lean` / `AtomarAkzeptiert.lean` use, with two kinds of
  derived atom where a definition nests a quantifier under a disjunction (`getrenntW`, `schreibGetrenntW`, `geteiltVB`
  in the footprint and race components): the derived atom enters the verdict cell as ONE bit, and its own cells
  (`urteil = false`, kinds listed below) say what makes it true. This is why the atom counts differ from the
  `atome` table of `Adaequanz/Gabbro/Zaehlung.lean`, which counted every leaf atom of every nesting as one flat tuple.

  NOTHING HERE IS TRUSTED, and NO RUST CHECKER IS CONSULTED. The only oracle is the Lean model's own Bool,
  `komp c` = component `c` of `AkzeptiertX`. The transcription is checked by evaluation against it:
  `zellenStimmen` compares, for one program, `komp c` with the verdict recomputed from the cells of component `c`,
  and each derived atom with its own cells. A program the generator produces and for which this is `false` is a
  transcription error of this file. Which programs and which forms were exercised is reported by the driver.

  The kinds (`komp`, `art`; atoms in order; the test `kern`):
    0,0  (f, g)      fragment    [gOk f without its indirect-call test, f calls through sig g, a contract carrier of g
                                  is outside f's widened footprint]                    a ∧ ¬(b ∧ c)
    1,0  (w, f, g)   closedness  (w over ALL functions) [reach w f, f calls g, reach w g]                     ¬a ∨ ¬b ∨ c
    2,0  (f, c)      footprint   [sigB f c, getrennt c, a guard lock of c protects c, geteilt c]   a ∨ b ∨ c ∨ d
         for every carrier c of f's footprint
    2,1  (f, c)      footprint of the registers read   [sigB f c, getrennt c]          a ∨ b
    2,2  (c, w1, w2) getrennt c  [w1 = w2 and declared once, some function w1 reaches has c in its footprint,
                                  some function w2 reaches writes c]                   a ∨ ¬b ∨ ¬c          (derived)
    2,3  (c)         geteilt c   [atomic, no guard lock, in no contract]                a ∧ b ∧ c            (derived)
    3,0  (f, L)      lock ranks  [f takes L, rank of L is above f's floor]              ¬a ∨ b
    4,0  (L, c)      lock sites  [c ∈ protected carriers of L, L guards c]              ¬a ∨ b
    5,0  (w)         roots       [w holds a lock by signature, w has reasons]           ¬a ∧ ¬b
    6,0  (w)         pool        [w declared twice, holds a lock, has reasons]          ¬a ∨ (¬b ∧ ¬c)
    6,1  (w, f, c)   pool        [w declared twice, reach w f, f writes c, c guarded or atomic]   ¬a ∨ ¬b ∨ ¬c ∨ d
    7,0  (c)         race        [c guarded or atomic, schreibGetrennt c]               a ∨ b
    7,1  (c, w1, w2) schreibGetrennt c  [w1 = w2, a function w1 reaches writes c,
                                  a function w2 reaches writes c or has it in its footprint]   a ∨ ¬b ∨ ¬c   (derived)
    8,0  (f, x)      answers     [x is an answer site of f, x a foreign body that never returns, the answer type has a value]
                                                                                       ¬a ∨ b ∨ c
    9,0  (w, f, L)   masks       (w over ALL functions) [w a handler, reach w f, f takes L, L masks interrupts]   ¬a ∨ ¬b ∨ ¬c ∨ d
-/
import Grammatik.Gen.Erzeuger.Gueltig

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

/-- A cell of a component: which component, which kind of tuple, the atom vector, and whether a false test refuses
    the component (`urteil`) or only decides a derived atom. -/
structure Zelle where
  komp : Nat
  art : Nat
  urteil : Bool
  atome : List Bool
  deriving DecidableEq, Hashable, Repr

/-- **The test of a cell**, from its atom vector alone; `none` for a (component, kind, length) that no clause knows. An
    unknown shape is NEVER a pass: `Zelle.kern` below is only read where `definiert` holds, and the table
    `zellTafel` is proved to be inside the clauses (`zellAlle_definiert`). -/
def Zelle.kern? (z : Zelle) : Option Bool :=
  match z.komp, z.art, z.atome with
  | 0, 0, [a, b, c] => some (a && !(b && c))
  | 1, 0, [a, b, c] => some (!a || !b || c)
  | 2, 0, [a, b, c, d] => some (a || b || c || d)
  | 2, 1, [a, b] => some (a || b)
  | 2, 2, [a, b, c] => some (a || !b || !c)
  | 2, 3, [a, b, c] => some (a && b && c)
  | 3, 0, [a, b] => some (!a || b)
  | 4, 0, [a, b] => some (!a || b)
  | 5, 0, [a, b] => some (!a && !b)
  | 6, 0, [a, b, c] => some (!a || (!b && !c))
  | 6, 1, [a, b, c, d] => some (!a || !b || !c || d)
  | 7, 0, [a, b] => some (a || b)
  | 7, 1, [a, b, c] => some (a || !b || !c)
  | 8, 0, [a, b, c] => some (!a || b || c)
  | 9, 0, [a, b, c, d] => some (!a || !b || !c || d)
  | _, _, _ => none

/-- The test as a Bool, where a clause knows the shape; an unknown shape reads as `false`, so it can never hide a bad
    cell behind a pass. -/
def Zelle.kern (z : Zelle) : Bool := z.kern?.getD false

/-- A cell whose shape a clause knows. -/
def Zelle.definiert (z : Zelle) : Bool := z.kern?.isSome

/-- The cell is BAD: a test that refuses the component fails. -/
def Zelle.schlecht (z : Zelle) : Bool := z.urteil && !z.kern

section Atome

variable {D : Deklaration} [Aufz D] [Zahlen]

/-- `f` takes the lock `L` somewhere in its body. -/
def nimmtB (P : Programm D) (f : D.Fn) (L : D.Lock) : Bool :=
  !(mE ⟨fun _ => true, fun _ => true, fun L' => !(decide (L' = L))⟩ (P.rumpf f))

/-- `f` calls indirectly through a pointer of signature `n`. -/
def indB (P : Programm D) (f : D.Fn) (n : Nat) : Bool :=
  !(mE ⟨fun _ => true, fun n' => !(decide (n' = n)), fun _ => true⟩ (P.rumpf f))

/-- The contract carriers of `g`. -/
def vertragsOrte (P : Programm D) (g : D.Fn) : List (D.Tab ⊕ D.Glob) :=
  (P.requires g).orte ++ (P.ensures g).orte

/-- The cells that decide `getrenntW c`. -/
def getrenntZellen (P : Programm D) (fs ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : List Zelle :=
  ws.flatMap fun w1 => ws.map fun w2 =>
    ⟨2, 2, false, [decide (w1 = w2) && !(mehrfachB ws w1),
      fs.any fun f => reachB P fs w1 f && istIn (fussOrteG P f) c,
      fs.any fun g => reachB P fs w2 g && TraegerSchreibt g c]⟩

/-- The cell that decides `geteiltVB c`. -/
def geteiltZelle (P : Programm D) (fs : List D.Fn) (c : D.Tab ⊕ D.Glob) : Zelle :=
  ⟨2, 3, false, [atomarB c, (waechterVon c).isEmpty, vertragsFreiB P fs c]⟩

/-- The cells that decide `schreibGetrenntW c`. -/
def schreibGetrenntZellen (P : Programm D) (fs ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : List Zelle :=
  ws.flatMap fun w1 => ws.map fun w2 =>
    ⟨7, 1, false, [decide (w1 = w2),
      fs.any fun g => reachB P fs w1 g && TraegerSchreibt g c,
      fs.any fun h => reachB P fs w2 h && (TraegerSchreibt h c || istIn (fussOrteG P h) c)]⟩

/-- **The cells of component `c`** of `AkzeptiertX` in the program `P`, under the lock family `S`, the member lists
    `fs ls cs` and the declared starts `ws`. -/
def zellen (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) : Fin 10 → List Zelle
  | 0 => fs.flatMap fun f => fs.map fun g =>
      ⟨0, 0, true, [(P.rumpf f).gOk (fun _ => true) (fun _ => true), indB P f (D.sig g),
        (vertragsOrte P g).any fun o => !(istIn (fussOrteG P f) o)]⟩
  | 1 => fs.flatMap fun w => fs.flatMap fun f => fs.map fun g =>
      ⟨1, 0, true, [reachB P fs w f, ruftB P f g, reachB P fs w g]⟩
  | 2 =>
      (fs.flatMap fun f => (fussOrte P f).flatMap fun c =>
        [⟨2, 0, true, [sigB f c, getrenntW P fs ws c,
          (waechterVon c).any (fun L => istIn (S.orte L) c), geteiltVB P fs c]⟩] ++
        getrenntZellen P fs ws c ++ [geteiltZelle P fs c]) ++
      (fs.flatMap fun f => ((P.rumpf f).regs.flatMap D.rtraeger).flatMap fun c =>
        [⟨2, 1, true, [sigB f c, getrenntW P fs ws c]⟩] ++ getrenntZellen P fs ws c)
  | 3 => fs.flatMap fun f => ls.map fun L =>
      ⟨3, 0, true, [nimmtB P f L, (bodenM f).sperre L]⟩
  | 4 => ls.flatMap fun L => cs.map fun c =>
      ⟨4, 0, true, [istIn (S.orte L) c, decide (L ∈ waechterVon c)]⟩
  | 5 => ws.map fun w => ⟨5, 0, true, [!(D.haelt w).isEmpty, !(decide (D.gruende w = 0))]⟩
  | 6 =>
      (ws.map fun w => ⟨6, 0, true, [mehrfachB ws w, !(D.haelt w).isEmpty, !(decide (D.gruende w = 0))]⟩) ++
      (ws.flatMap fun w => fs.flatMap fun f => cs.map fun c =>
        ⟨6, 1, true, [mehrfachB ws w, reachB P fs w f, TraegerSchreibt f c, ausgenommenB c]⟩)
  | 7 => cs.flatMap fun c =>
      [⟨7, 0, true, [ausgenommenB c, schreibGetrenntW P fs ws c]⟩] ++ schreibGetrenntZellen P fs ws c
  | 8 => fs.flatMap fun f => ((Aufz.ax (D := D)).map Sum.inl ++ (Aufz.reg (D := D)).map Sum.inr).map fun x =>
      ⟨8, 0, true, [decide (x ∈ (P.rumpf f).ants),
        match x with | .inl a => decide (D.aerg a = some Ty.never) | .inr _ => false,
        match x with | .inl a => antwortB fs (D.aerg a) | .inr r => antwortB fs (some (D.rtyp r))]⟩
  | 9 => fs.flatMap fun w => fs.flatMap fun f => ls.map fun L =>
      ⟨9, 0, true, [P.unterbricht w, reachB P fs w f, nimmtB P f L, D.maskiert L]⟩

/-- The verdict of component `c` recomputed from its cells: no verdict cell is bad. -/
def urteilAusZellen (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) (c : Fin 10) : Bool :=
  (zellen P S fs ls cs ws c).all fun z => !z.schlecht

/-- **The self-check of the transcription**, for one program: every component's verdict equals the verdict of its
    cells, and the derived atoms equal their own cells. -/
def zellenStimmen (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) : Bool :=
  (List.finRange 10).all (fun c => (zellen P S fs ls cs ws c).all Zelle.definiert) &&
  (List.finRange 10).all (fun c => urteilAusZellen P S fs ls cs ws c == komp P S fs ls cs ws c) &&
  cs.all (fun c =>
    (getrenntW P fs ws c == (getrenntZellen P fs ws c).all Zelle.kern) &&
    (schreibGetrenntW P fs ws c == (schreibGetrenntZellen P fs ws c).all Zelle.kern) &&
    (geteiltVB P fs c == (geteiltZelle P fs c).kern))

/-- Where the transcription disagrees with the checker, for one program: the components whose verdict differs
    (`c`), and for each carrier the derived atoms that differ (`100 + c` for `getrennt`, `200 + c` for
    `schreibGetrennt`, `300 + c` for `geteilt`, with `c` the position in `cs`). Empty when `zellenStimmen`. -/
def zellenAbweichung (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) : List Nat :=
  ((List.range 10).filter fun i =>
    match (List.finRange 10).find? (fun c => c.val == i) with
    | some c => urteilAusZellen P S fs ls cs ws c != komp P S fs ls cs ws c
    | none => false) ++
  ((List.range cs.length).flatMap fun i =>
    match cs[i]? with
    | none => []
    | some c =>
      (if getrenntW P fs ws c == (getrenntZellen P fs ws c).all Zelle.kern then [] else [100 + i]) ++
      (if schreibGetrenntW P fs ws c == (schreibGetrenntZellen P fs ws c).all Zelle.kern then [] else [200 + i]) ++
      (if geteiltVB P fs c == (geteiltZelle P fs c).kern then [] else [300 + i]))

/-- The least rank of the locks a body itself takes (`none` if it takes none). -/
def Rumpf.bodenAbgeleitet {f : D.Fn} (b : Rumpf D f) : Option Int :=
  ((Aufz.lock (D := D)).filter fun L =>
    !(mE ⟨fun _ => true, fun _ => true, fun L' => !(decide (L' = L))⟩ b)).map D.rang
    |>.foldl (fun a r => match a with | none => some r | some m => some (if m < r then m else r)) none

/-- The smaller of two optional ranks. -/
def minOpt : Option Int → Option Int → Option Int
  | none, b => b
  | a, none => a
  | some a, some b => some (if a < b then a else b)

/-- The functions a body calls DIRECTLY (by name, not through a pointer). -/
def ruftDirektB (P : Programm D) (f g : D.Fn) : Bool :=
  !(mE ⟨fun h => !(decide (h = g)), fun _ => true, fun _ => true⟩ (P.rumpf f))

/-- `n` rounds of the floor relation: the least rank taken by the function itself or by a function it reaches by `n`
    direct calls. -/
def Programm.bodenRunden (P : Programm D) : Nat → D.Fn → Option Int
  | 0 => fun f => Rumpf.bodenAbgeleitet (P.rumpf f)
  | n + 1 => fun f => ((Aufz.fn (D := D)).filter (ruftDirektB P f)).foldl
      (fun a g => minOpt a (Programm.bodenRunden P n g)) (Rumpf.bodenAbgeleitet (P.rumpf f))

/-- **The floor the language derives** (`floorOf` of the Lean front end, `resolve_floors`): `none` in a unit without
    locks; else the least rank of a lock taken on a path of direct calls from the function, or one above the highest
    rank of the unit when no path takes a lock. The language does not write a floor; the model's signature carries one,
    and a program of the source carries this one. -/
def Programm.bodenP (P : Programm D) (f : D.Fn) : Option Int :=
  if (Aufz.lock (D := D)).isEmpty then none
  else some (match Programm.bodenRunden P (Aufz.fn (D := D)).length f with
    | some c => c
    | none => ((Aufz.lock (D := D)).map D.rang).foldl max 0 + 1)

end Atome

/-! ## The universe of cells: ONE table, with its proofs -/

/-- **The table of the kinds of cells**: (component, kind, whether a false test refuses the component, number of
    atoms). It is the ONLY place the arities are written; `zellAlle` and every count below are computed from it, and
    `zellAlle_definiert` stops the build when a row has no clause in `Zelle.kern?`. -/
def zellTafel : List (Nat × Nat × Bool × Nat) :=
  [(0, 0, true, 3), (1, 0, true, 3), (2, 0, true, 4), (2, 1, true, 2), (2, 2, false, 3), (2, 3, false, 3),
   (3, 0, true, 2), (4, 0, true, 2), (5, 0, true, 2), (6, 0, true, 3), (6, 1, true, 4), (7, 0, true, 2),
   (7, 1, false, 3), (8, 0, true, 3), (9, 0, true, 4)]

/-- All assignments of `n` atoms. -/
def belegungen : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (belegungen n).flatMap fun r => [false :: r, true :: r]

/-- **The universe**: every assignment of every kind. -/
def zellAlle : List Zelle :=
  zellTafel.flatMap fun (c, a, u, n) => (belegungen n).map fun v => ⟨c, a, u, v⟩

/-- Every cell of the universe has a clause: no shape of the table is unknown to `Zelle.kern?`. -/
theorem zellAlle_definiert : zellAlle.all Zelle.definiert = true := by decide

/-- The universe has 124 cells ... -/
theorem zellAlle_laenge : zellAlle.length = 124 := by decide

/-- ... of which 20 are bad (a verdict test fails): the number of single-fault programs of the global patterns. -/
theorem zellAlle_schlecht : (zellAlle.filter Zelle.schlecht).length = 20 := by decide

/-- The components of the table are exactly the ten of `AkzeptiertX`. -/
theorem zellTafel_komponenten : (zellTafel.map (·.1)).eraseDups = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by decide

end Gabbro.Grammatik.Gen
