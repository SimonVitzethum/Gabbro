/- Pure generator metadata shared by collection and its classification witnesses. -/
module

public import Grammatik.Gen.Abdeckung.ZellenBefund

@[expose] public section

namespace Gabbro.Grammatik.Gen

/-- The cell of a text, from the universe. -/
def zelleAus (t : String) : Option Zelle := zellAlle.find? (·.text == t)

/-- What the records of all members say together. -/
structure Summe where
  zahlen : Nat × Nat × Nat := (0, 0, 0)
  gut : List Zelle := []
  schlecht : List Zelle := []
  maskiert : List Zelle := []
  schlGedruckt : List Zelle := []
  quellen : List (String × String) := []
  kand : List (String × List Zelle × Except String Unit) := []
  grund : Std.HashMap String Nat := {}
  formen : Std.HashMap String Nat := {}
  fremd : List String := []
  /-- Lean witness files: of valid programs (stem, cells, printed) and of isolated bad cells (stem, cell, printed) -/
  leanG : List (String × List Zelle × Bool) := []
  /-- Fragment records use bare stems; copying adds the Gap/ directory. -/
  leanGap : List (String × List Zelle × Bool) := []
  leanB : List (String × List Zelle × List Zelle × Bool) := []

/-- One record line. -/
def Summe.zeile (s : Summe) (l : String) : Summe :=
  let zelle := fun t => match zelleAus t with | some x => (some x, s) | none => (none, { s with fremd := s.fremd ++ [t] })
  let neu := fun (xs : List Zelle) (x : Zelle) => if xs.contains x then xs else xs ++ [x]
  match l.splitOn "\t" with
  | ["Z", a, b, c] => let (x, y, w) := s.zahlen; { s with zahlen := (x + a.toNat!, y + b.toNat!, w + c.toNat!) }
  | ["G", t, _] => match zelle t with | (some x, s) => { s with gut := neu s.gut x } | (none, s) => s
  | ["B", t, _] => match zelle t with | (some x, s) => { s with schlecht := neu s.schlecht x } | (none, s) => s
  | ["X", t, _] => match zelle t with | (some x, s) => { s with maskiert := neu s.maskiert x } | (none, s) => s
  | ["S", t, _] => match zelle t with | (some x, s) => { s with schlGedruckt := neu s.schlGedruckt x } | (none, s) => s
  | ["Q", f, k] => { s with quellen := s.quellen ++ [(f, k)] }
  | ["K", st, key, r] =>
    let ts := if key.isEmpty then [] else key.splitOn ";"
    let zs := ts.filterMap zelleAus
    let s := if zs.length == ts.length then s else { s with fremd := s.fremd ++ ts.filter (zelleAus · |>.isNone) }
    { s with kand := s.kand ++ [(st, zs, if r == "ok" then .ok () else .error r)] }
  | ["LG", st, key, r] =>
    let zs := (if key.isEmpty then [] else key.splitOn ";").filterMap zelleAus
    { s with leanG := s.leanG ++ [(st, zs, r == "ok")] }
  | ["LGAP", st, key, r] =>
    let zs := (if key.isEmpty then [] else key.splitOn ";").filterMap zelleAus
    { s with leanGap := s.leanGap ++ [(st, zs, r == "ok")] }
  | ["LB", st, bad, key, r] =>
    let bs := (if bad.isEmpty then [] else bad.splitOn ";").filterMap zelleAus
    let zs := (if key.isEmpty then [] else key.splitOn ";").filterMap zelleAus
    { s with leanB := s.leanB ++ [(st, bs, zs, r == "ok")] }
  | ["R", m, n] => { s with grund := s.grund.insert m (s.grund.getD m 0 + n.toNat!) }
  | ["F", m, n] => { s with formen := s.formen.insert m (s.formen.getD m 0 + n.toNat!) }
  | _ => s

end Gabbro.Grammatik.Gen
