/-
  File:      Grammatik/Gen/Fein/Lauf.lean
  Subject:   The driver `gen-fein` of the fine-cell witness search (untrusted: every witness it prints is a program
             the kernel checks, `Gen/Fein/Druck.lean`). Started by `instrumente/fein-suche.sh`, which documents the
             workflow.

  A RUN is (method, member source, member, body bound, expression fuel) and always targets EVERY cell of the
  universe `uF`, so its result does not depend on which cells are open and is never computed twice: it is cached as
  one file of the run directory DIR (`messung/fein/laeufe`), one line `j cell cell ...` per packed program.

    gen-fein suche  M Q I NB EC DIR              the run, unless DIR holds it
    gen-fein stufen M Q I VON BIS EC S DIR       the runs at body bounds VON, VON+1, ...: the next bound only while
                                                 the last run brought at least S cells no run in DIR had
    gen-fein deckung DIR OUT                     the greedy cover of `uF` by the cached programs: OUT/wahl.txt
                                                 (`run j` per chosen program) and OUT/offen.txt (the cells no
                                                 cached program has)
    gen-fein zeuge RUN J OUTDIR                  the witness file of program J of RUN (recomputed: the run is
                                                 deterministic)
    gen-fein zeit Q I N CAP                      the table sizes and times of member I up to size N

  Methods: `gefiltert` (`packen`: the novelty-filtered tables, contracts 2, loop cap 3), `voll` (`packenZiel` over
  the unfiltered tables `genTZ`), `vertreter` (`packenZiel` over the tables of representatives `genTK`). Members:
  Q = m the family `mitglieder`, Q = f the fine members `feinMitglieder`. Every method packs 8 bodies per program.
-/
import Grammatik.Gen.Fein.Suche
import Grammatik.Gen.Fein.Druck
import Grammatik.Gen.Fein.Mitglieder
import Std.Data.HashSet

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Gen.Fein

def zelleT (c : FZelle) : String :=
  s!"{c.art}.{c.fam}.{c.kon}.{if c.l then 1 else 0}.{String.intercalate "-" (c.daten.map toString)}"

def quelle (q : String) : List Spez := if q = "f" then feinMitglieder else mitglieder

def quelleT (q : String) : String := if q = "f" then "Fein.feinMitglieder" else "mitglieder"

/-- A run of the search. -/
structure Lauf where
  methode : String
  q : String
  i : Nat
  nb : Nat
  ec : Nat

/-- The name of a run: its cache file `DIR/name.txt`. -/
def Lauf.name (l : Lauf) : String := s!"{l.methode}-{l.q}{l.i}-nb{l.nb}-ec{l.ec}"

/-- The run a name stands for. -/
def Lauf.aus (n : String) : Option Lauf :=
  match n.splitOn "-" with
  | [m, qi, nb, ec] =>
    let q := qi.take 1 |>.toString
    match (qi.drop 1).toString.toNat?, (nb.drop 2).toString.toNat?, (ec.drop 2).toString.toNat? with
    | some i, some b, some e => some ⟨m, q, i, b, e⟩
    | _, _, _ => none
  | _ => none

/-- The packed programs of a run. -/
def Lauf.gute (l : Lauf) (z : Spez) : List (Gutes z) :=
  if l.methode = "gefiltert" then packen z l.nb 2 3 8
  else packenZiel z l.nb l.ec 8 (l.methode = "vertreter") fun _ => true

/-- The cells of the packed programs of a run, as text. -/
def Lauf.zellen (l : Lauf) : List (List String) :=
  let z := (quelle l.q).getD l.i {}
  (l.gute z).map fun g => ((z.einsatz g.prog g.ws g.ohneAx g.boden).feinZellen.eraseDups).map zelleT

/-- The cached runs of DIR: per file, its lines `j cells`. -/
def gespeichert (dir : String) : IO (List (String × List (Nat × List String))) := do
  let mut out := []
  for e in ← System.FilePath.readDir dir do
    if e.fileName.endsWith ".txt" then
      let n := (e.fileName.dropEnd 4).toString
      let ls := (← IO.FS.lines e.path).toList.filterMap fun l =>
        match l.splitOn " " with
        | j :: cs => j.toNat?.map fun j => (j, cs.filter (· ≠ ""))
        | [] => none
      out := (n, ls) :: out
  return out

/-- Every cell some cached run has. -/
def bekannt (dir : String) : IO (Std.HashSet String) := do
  return (← gespeichert dir).foldl (fun s (_, ls) => ls.foldl (fun s (_, cs) => cs.foldl (·.insert ·) s) s) {}

/-- `suche`: the run from the cache, or computed and cached. Answers its cells and whether it was cached. -/
def suche (l : Lauf) (dir : String) : IO (List String × Bool) := do
  let f : System.FilePath := s!"{dir}/{l.name}.txt"
  if ← f.pathExists then
    let ls ← IO.FS.lines f
    return ((ls.toList.flatMap fun x => (x.splitOn " ").drop 1).filter (· ≠ ""), true)
  let t0 ← IO.monoMsNow
  let zs := l.zellen
  let text := String.join ((zs.zipIdx).map fun (cs, j) => s!"{j} {String.intercalate " " cs}\n")
  IO.FS.writeFile s!"{f}.tmp" text
  IO.FS.rename s!"{f}.tmp" f
  IO.eprintln s!"{l.name}: {zs.length} programs ({(← IO.monoMsNow) - t0} ms)"
  return (zs.flatten, false)

/-- `stufen`: the runs at growing body bounds while each brings at least `s` new cells. -/
def stufen (m q : String) (i von bis ec s : Nat) (dir : String) : IO Unit := do
  for nb in List.range' von (bis + 1 - von) do
    let alt ← bekannt dir
    let (cs, cached) ← suche ⟨m, q, i, nb, ec⟩ dir
    let neu := (cs.eraseDups.filter fun c => !alt.contains c).length
    IO.println s!"{m}-{q}{i}-nb{nb}-ec{ec}: {cs.eraseDups.length} cells, {neu} new{if cached then " (cached)" else ""}"
    (← IO.getStdout).flush
    if !cached && neu < s then return

/-- `deckung`: the greedy cover of the universe by the cached programs. -/
def deckung (dir out : String) : IO Unit := do
  let u : Std.HashSet String := uF.foldl (fun s c => s.insert (zelleT c)) {}
  let kand : Array (String × Nat × List String) := ((← gespeichert dir).flatMap fun (n, ls) =>
    ls.map fun (j, cs) => (n, j, cs.filter u.contains)).toArray
  let mut gedeckt : Std.HashSet String := {}
  let mut wahl : Array (String × Nat) := #[]
  repeat
    let mut best := 0
    let mut bi := 0
    for h : k in [0:kand.size] do
      let n := (kand[k].2.2.filter fun c => !gedeckt.contains c).eraseDups.length
      if n > best then best := n; bi := k
    if best = 0 then break
    let (n, j, cs) := kand[bi]!
    wahl := wahl.push (n, j)
    gedeckt := cs.foldl (·.insert ·) gedeckt
  let offen := (uF.map zelleT).filter fun c => !gedeckt.contains c
  IO.FS.writeFile s!"{out}/wahl.txt" (String.join (wahl.toList.map fun (n, j) => s!"{n} {j}\n"))
  IO.FS.writeFile s!"{out}/offen.txt" (String.join (offen.map (· ++ "\n")))
  IO.println s!"programs {kand.size}, chosen {wahl.size}, cells {gedeckt.size} of {uF.length}, open {offen.length}"

/-- The module name of a witness: the run and the program, no character a module name may not hold. -/
def stammVon (l : Lauf) (j : Nat) : String := s!"F{l.methode}{l.q}{l.i}n{l.nb}e{l.ec}_{j}"

/-- `zeuge`: the witness file of program `j` of a run. -/
def zeuge (n : String) (j : Nat) (outdir : String) : IO UInt32 := do
  match Lauf.aus n with
  | none => IO.eprintln s!"no run: {n}"; return 2
  | some l =>
    let z := (quelle l.q).getD l.i {}
    match (l.gute z)[j]? with
    | none => IO.eprintln s!"{n}: no program {j}"; return 1
    | some g =>
      let stamm := stammVon l j
      let zs := (z.einsatz g.prog g.ws g.ohneAx g.boden).feinZellen.eraseDups
      match leanFein z (quelleT l.q) l.i stamm g.prog g.ws zs with
      | .error m => IO.eprintln s!"{stamm}: {m}"; return 1
      | .ok t => IO.FS.writeFile s!"{outdir}/{stamm}.lean" t; return 0

def zeit (q : String) (i n cap : Nat) : IO Unit := do
  let z := (quelle q).getD i {}
  letI : Zahlen := z.zahlen
  let D := z.deklaration
  for f in z.fnListe do
    for k in List.range (min n eGrenze + 1) do
      let t0 ← IO.monoMsNow
      let t := genEF (D := D) Kenner.fein k k (D.params f) (Signatur.anfang D (D.signatur f))
      let gr := t.map List.length
      IO.eprintln s!"expressions {k}: {gr} ({(← IO.monoMsNow) - t0} ms)"
    for k in List.range (n + 1) do
      let t0 ← IO.monoMsNow
      let t := genTF Kenner.fein (vertragVon D f) cap k k false (D.params f) (Signatur.anfang D (D.signatur f))
      let gr := t.map fun e => (e.1.length, e.2.1.length, e.2.2.length)
      IO.eprintln s!"tables {k}: {gr} ({(← IO.monoMsNow) - t0} ms)"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["suche", m, q, i, nb, ec, d] => let _ ← suche ⟨m, q, i.toNat!, nb.toNat!, ec.toNat!⟩ d; return 0
  | ["stufen", m, q, i, von, bis, ec, s, d] =>
    stufen m q i.toNat! von.toNat! bis.toNat! ec.toNat! s.toNat! d; return 0
  | ["deckung", d, out] => deckung d out; return 0
  | ["zeuge", n, j, out] => zeuge n j.toNat! out
  | ["zeit", q, i, n, cap] => zeit q i.toNat! n.toNat! cap.toNat!; return 0
  | _ => IO.eprintln "usage: see the header of Grammatik/Gen/Fein/Lauf.lean"; return 2
