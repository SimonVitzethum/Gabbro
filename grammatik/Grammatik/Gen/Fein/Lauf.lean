/-
  File:      Grammatik/Gen/Fein/Lauf.lean
  Subject:   The driver `gen-fein` (untrusted; what it writes the kernel checks):
               (Q = m: the members `mitglieder`, Q = f: the fine members `feinMitglieder`)
               gen-fein sammeln Q A B NB NC CAP      for every member in A ..< B and every valid candidate (`kandidaten`),
                                                one line `member index cells`
               gen-fein drucke Q LISTE NB NC CAP DIR for every line `member index stamm` of LISTE, the witness file
                                                DIR/stamm.lean (`leanFein`)
               gen-fein packen Q A B NB NC CAP K DIR  the packed witnesses (`packen`, K bodies per function) of
                                                the members A ..< B as files DIR/F<Q><member>_<n>.lean, their cells
                                                to stdout
               gen-fein zeit Q I N CAP          the table sizes and times of member I up to size N
-/
import Grammatik.Gen.Fein.Suche
import Grammatik.Gen.Fein.Druck
import Grammatik.Gen.Fein.Mitglieder

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Gen.Fein

def zelleT (c : FZelle) : String :=
  s!"{c.art}.{c.fam}.{c.kon}.{if c.l then 1 else 0}.{String.intercalate "-" (c.daten.map toString)}"


def quelle (q : String) : List Spez := if q = "f" then feinMitglieder else mitglieder

def quelleT (q : String) : String := if q = "f" then "Fein.feinMitglieder" else "mitglieder"

def sammeln (q : String) (a b nb nc cap : Nat) : IO Unit := do
  for i in List.range' a (b - a) do
    let z := (quelle q).getD i {}
    let t0 ← IO.monoMsNow
    let ks := kandidaten z nb nc cap
    IO.eprintln s!"member {i}: {ks.length} candidates built ({(← IO.monoMsNow) - t0} ms)"
    let mut j := 0
    let mut ok := 0
    for P in ks do
      match gutVon z P with
      | none => pure ()
      | some g =>
        let e := z.einsatz g.prog g.ws g.ohneAx g.boden
        IO.println s!"{i} {j} {String.intercalate " " (e.feinZellen.eraseDups.map zelleT)}"
        ok := ok + 1
      j := j + 1
    (← IO.getStdout).flush
    IO.eprintln s!"member {i}: {ks.length} candidates, {ok} valid ({(← IO.monoMsNow) - t0} ms)"

def drucke (q : String) (liste : String) (nb nc cap : Nat) (dir : String) : IO UInt32 := do
  let mut fehler := 0
  for zeile in (← IO.FS.lines liste).toList do
    match zeile.splitOn " " with
    | [i, j, stamm] =>
      let z := (quelle q).getD i.toNat! {}
      match (kandidaten z nb nc cap)[j.toNat!]? with
      | none => IO.eprintln s!"{stamm}: no candidate"; fehler := fehler + 1
      | some P =>
        match gutVon z P with
        | none => IO.eprintln s!"{stamm}: not valid"; fehler := fehler + 1
        | some g =>
          let e := z.einsatz g.prog g.ws g.ohneAx g.boden
          match leanFein z (quelleT q) i.toNat! stamm g.prog g.ws e.feinZellen.eraseDups with
          | .error m => IO.eprintln s!"{stamm}: {m}"; fehler := fehler + 1
          | .ok t => IO.FS.writeFile s!"{dir}/{stamm}.lean" t
    | _ => pure ()
  return (if fehler = 0 then 0 else 1)

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

/-- `packen`: the packed witnesses of the members `a ..< b`, each written as a witness file to `dir`, its cells to
    stdout (`member index cells`). -/
def packenL (q : String) (a b nb nc cap k : Nat) (dir : String) : IO UInt32 := do
  let mut fehler := 0
  for i in List.range' a (b - a) do
    let z := (quelle q).getD i {}
    let t0 ← IO.monoMsNow
    let gs := packen z nb nc cap k
    let mut j := 0
    for g in gs do
      let e := z.einsatz g.prog g.ws g.ohneAx g.boden
      let zs := e.feinZellen.eraseDups
      let stamm := s!"F{q}{i}_{j}"
      match leanFein z (quelleT q) i stamm g.prog g.ws zs with
      | .error m => IO.eprintln s!"{stamm}: {m}"; fehler := fehler + 1
      | .ok t =>
        IO.FS.writeFile s!"{dir}/{stamm}.lean" t
        IO.println s!"{stamm} {String.intercalate " " (zs.map zelleT)}"
      j := j + 1
    (← IO.getStdout).flush
    IO.eprintln s!"member {i}: {gs.length} packed witnesses ({(← IO.monoMsNow) - t0} ms)"
  return (if fehler = 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["sammeln", q, a, b, nb, nc, cap] => sammeln q a.toNat! b.toNat! nb.toNat! nc.toNat! cap.toNat!; return 0
  | ["drucke", q, l, nb, nc, cap, d] => drucke q l nb.toNat! nc.toNat! cap.toNat! d
  | ["packen", q, a, b, nb, nc, cap, k, d] =>
    packenL q a.toNat! b.toNat! nb.toNat! nc.toNat! cap.toNat! k.toNat! d
  | ["zeit", q, i, n, cap] => zeit q i.toNat! n.toNat! cap.toNat!; return 0
  | _ => IO.eprintln "usage: gen-fein sammeln Q A B NB NC CAP | gen-fein drucke Q LISTE NB NC CAP DIR"; return 2
