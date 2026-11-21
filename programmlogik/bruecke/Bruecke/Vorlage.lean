module
public import Bruecke.Kette.Stufe0
public import Bruecke.Vorlage.Formen
public import Bruecke.Vorlage.Zeige
public import Grammatik.Parser.Elab.UebersetzePipeline
@[expose] public section

/-!
# GabbroV's generator: the Lean files of a unit's duties

`dateien modul src` runs Stage 0's front end on the source text once (`stufe0Einheit`: the unit
Stage 0 compiles, without the checker that follows it) and writes the duties of the unit as Lean modules under the module
prefix `modul` (the tool `gabbrov`, `Vorlage/Haupt.lean`). The unit is pinned AS DATA (owner,
2026-11-21): the files never evaluate the front end in the kernel; the generic theorem
`nutzer_aus_stage0` takes `c : Compiled quelle` with `c.unit = u` as its named premise, and the module
`M/Pruefung.lean` checks it by running Stage 0's front end (`stufe0Einheit`, `#guard`).

Layout, so that units of 500 000 lines stay usable (every file small, Lake builds them in
parallel, no step quantifies over function positions):

* `M/Quelle.lean`        the source text, as pieces;
* `M/Daten/S<k>.lean`    the elaborated functions of chunk `k` (`f<i> : UFn`) and their list;
* `M/Daten.lean`         the unit `u` (its function list is the append of the chunks) and the rank;
* `M/Pflicht/F<i>.lean`  for function `i`: its Body as GabbroV reads it, printed as a Lean term and
  in source notation, the reading equation, the decided checks and the goal `ziel<i>`;
* `M/Beweis/F<i>.lean`   YOUR proof of `ziel<i>`; written once as a stub, never overwritten;
* `M/Sammlung/S<k>.lean` the duties of chunk `k` assembled;
* `M.lean`               the unit checks and premise (b) of the goal theorem.

A function or a check outside the bridge is a NAMED refusal in the files; premise (b) is then
not stated.
-/

namespace Gabbro.Bruecke.Vorlage

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- One generated file: module path relative to the output root (`/`-separated, without
    `.lean`), its text, and whether an existing file is replaced (`false`: the user's own). -/
structure Datei where
  pfad : String
  text : String
  ersetzen : Bool := true

/-- Functions per chunk. -/
def stueckGroesse : Nat := 16

/-- A printed term on one line. `repr` prints a proof field as `_`; every proof field of the
    elaborated unit is a decidable fact about its data, so it is written `by decide`. -/
def breit (x : Std.Format) : String := (x.pretty 1000000).replace " := _ " " := by decide "

/-- A Lean string literal for `s`. -/
def literal (s : String) : String := (repr s).pretty 1000000

/-- The characters cut into pieces that end at a newline or after at most 60 characters. -/
def stueckeL : Nat → List Char → List (List Char)
  | 0, cs => if cs.isEmpty then [] else [cs]
  | fuel + 1, cs =>
    if cs.isEmpty then [] else
    let vor := cs.take 60
    let bis := match vor.findIdx? (· == '\n') with
      | some i => i + 1
      | none => vor.length
    cs.take bis :: stueckeL fuel (cs.drop bis)

def stuecke (src : String) : List String :=
  (stueckeL (src.length + 1) src.toList).map String.ofList

/-- The list `xs` cut into consecutive pieces of at most `k` elements. -/
def teile {α : Type} (k : Nat) (xs : List α) : List (List α) :=
  if k = 0 then [xs] else go xs.length xs
where
  go : Nat → List α → List (List α)
    | 0, _ => []
    | fuel + 1, ys => if ys.isEmpty then [] else ys.take k :: go fuel (ys.drop k)

/-- A balanced tree over `ns` joined by `verbinde` (depth logarithmic in the length). -/
def baum (verbinde : String → String → String) (leer : String) : Nat → List String → String
  | _, [] => leer
  | _, [n] => n
  | 0, ns => ns.foldr (fun a acc => verbinde a acc) leer
  | fuel + 1, ns =>
    let h := ns.length / 2
    verbinde (baum verbinde leer fuel (ns.take h)) (baum verbinde leer fuel (ns.drop h))

/-- A balanced Lean expression joining the names `ns` with the infix `op`. -/
def balanciert (op leer : String) (fuel : Nat) (ns : List String) : String :=
  baum (fun a b => "(" ++ a ++ " " ++ op ++ " " ++ b ++ ")") leer fuel ns

def kopf (modul : String) (imports : List String) (doc : String) : String :=
  "module\n" ++ String.join (imports.map fun i => "public import " ++ i ++ "\n") ++
  "@[expose] public section\n\n" ++ "/-! " ++ doc ++ " -/\n\n" ++
  "namespace " ++ modul ++ "\n\n" ++
  "open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze\n" ++
  "open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Bruecke\n\n" ++
  "set_option maxRecDepth 100000\n\n"

def fuss (modul : String) : String := "end " ++ modul ++ "\n"

/-- The source text, kept as pieces (no long literal). -/
def quelleDatei (modul src : String) : Datei :=
  let zeilen := String.intercalate ",\n   " ((stuecke src).map fun s => literal s ++ ".toList")
  { pfad := modul.replace "." "/" ++ "/Quelle"
    text := kopf modul ["Bruecke.Kette.Einheit"] "The source text of the unit, byte for byte (written by `gabbrov`)." ++
      "def zeilen : List (List Char) :=\n  [" ++ zeilen ++ "]\n\n" ++
      "def quelle : String := String.ofList zeilen.flatten\n\n" ++ fuss modul }

/-- The elaborated unit without its function list: its printed form with the function list
    replaced by `fnsAusdruck` and the cache `merk` left to its default (all caches are equal). -/
def einheitText (u : UProg) (fnsAusdruck : String) : String :=
  let t := breit (repr { u with fns := [] })
  (t.replace ", merk := by decide" "").replace ", fns := [], " (", fns := " ++ fnsAusdruck ++ ", ")

def fnName (i : Nat) : String := "f" ++ toString i

def stueckModul (modul : String) (k : Nat) : String := modul ++ ".Daten.S" ++ toString k

def datenStueck (modul : String) (k : Nat) (fs : List (Nat × UFn)) : Datei :=
  { pfad := (stueckModul modul k).replace "." "/"
    text := kopf modul ["Bruecke.Kette.Einheit"]
        ("The elaborated functions of chunk " ++ toString k ++ " (written by `gabbrov`).") ++
      String.join (fs.map fun (i, f) =>
        "/-- `" ++ f.name ++ "` -/\ndef " ++ fnName i ++ " : UFn :=\n  " ++ breit (repr f) ++ "\n\n") ++
      "def stueck" ++ toString k ++ " : List UFn := [" ++
        String.intercalate ", " (fs.map fun (i, _) => fnName i) ++ "]\n\n" ++ fuss modul }

def datenDatei (modul : String) (u : UProg) (anzahl : Nat) (rang : List (String × Nat)) : Datei :=
  let namen := (List.range anzahl).map fun k => "stueck" ++ toString k
  { pfad := modul.replace "." "/" ++ "/Daten"
    text := kopf modul ((List.range anzahl).map (stueckModul modul))
        "The elaborated unit `u` as data and the rank of its call graph (written by `gabbrov`)." ++
      "def u : UProg :=\n  " ++ einheitText u (balanciert "++" "[]" 64 namen) ++ "\n\n" ++
      "/-- The rank of every function: every direct call goes to a lower rank. -/\n" ++
      "def rangTafel : List (String × Nat) :=\n  " ++ breit (repr rang) ++ "\n\n" ++
      "def rk (n : String) : Nat := (rangTafel.lookup n).getD 0\n\n" ++ fuss modul }

/-- The source contract of a function in a comment line, as far as it is printable. -/
def vertrag (f : UFn) : String :=
  "`" ++ f.name ++ "`" ++
  (if f.needs.isEmpty then "" else ", " ++ toString f.needs.length ++ " requires clause(s)") ++
  (if f.gives.isEmpty then ", no ensures" else ", " ++ toString f.gives.length ++ " ensures clause(s)")

def pflichtModul (modul : String) (i : Nat) : String := modul ++ ".Pflicht.F" ++ toString i
def beweisModul (modul : String) (i : Nat) : String := modul ++ ".Beweis.F" ++ toString i

def pflichtDatei (modul : String) (i : Nat) (f : UFn) (body : List Gabbro.Body.Stmt) : Datei :=
  let si := toString i
  { pfad := (pflichtModul modul i).replace "." "/"
    text := kopf modul [modul ++ ".Daten"] ("The duty of " ++ vertrag f ++ " (written by `gabbrov`; regenerated on every run).") ++
      "/-- The body of `" ++ f.name ++ "` as GabbroV reads it:\n\n```\n" ++ zeigeKoerper body ++ "```\n-/\n" ++
      "def body" ++ si ++ " : List Gabbro.Body.Stmt :=\n  " ++ breit (repr body) ++ "\n\n" ++
      "theorem body" ++ si ++ "_eq : zuBodyZ u " ++ fnName i ++ " = some body" ++ si ++ " := by\n  with_unfolding_all rfl\n\n" ++
      "/-- The decided checks of `" ++ f.name ++ "`. -/\n" ++
      "theorem pruefung" ++ si ++ " : stimmigFnB u " ++ fnName i ++ " = true ∧ bindFrischB " ++ fnName i ++
        " = true ∧ rangFnB rk " ++ fnName i ++ " = true := by\n  with_unfolding_all decide\n\n" ++
      "/-- **What you prove about `" ++ f.name ++ "`**: from a well-formed entry state satisfying the\n" ++
      "    precondition, under the contracts of its callees, the body ends and meets the postcondition. -/\n" ++
      "def ziel" ++ si ++ " : Prop := meetsU u (wfU u) " ++ fnName i ++ " body" ++ si ++ "\n\n" ++ fuss modul }

/-- The user's proof file: written once, never replaced. -/
def beweisDatei (modul : String) (i : Nat) (f : UFn) : Datei :=
  let si := toString i
  { pfad := (beweisModul modul i).replace "." "/"
    ersetzen := false
    text := kopf modul [pflichtModul modul i] ("Your proof of the duty of `" ++ f.name ++
        "`. `gabbrov` writes this file once and never replaces it.") ++
      "theorem beweis" ++ si ++ " : ziel" ++ si ++ " := by\n" ++
      "  intro ρ s hwf hpre\n  exact?\n\n" ++ fuss modul }

def sammlungModul (modul : String) (k : Nat) : String := modul ++ ".Sammlung.S" ++ toString k

def sammlungDatei (modul : String) (k : Nat) (fs : List Nat) : Datei :=
  let glied (i : Nat) : String :=
    let si := toString i
    "⟨pruefung" ++ si ++ ".1, pruefung" ++ si ++ ".2.1, pruefung" ++ si ++ ".2.2, body" ++ si ++ ", body" ++ si ++
      "_eq, beweis" ++ si ++ "⟩"
  let beweis := fs.foldr (fun i acc => "fnPflicht_cons " ++ glied i ++ "\n    (" ++ acc ++ ")") "fnPflicht_nil"
  { pfad := (sammlungModul modul k).replace "." "/"
    text := kopf modul (fs.map (beweisModul modul)) ("The duties of chunk " ++ toString k ++ " (written by `gabbrov`).") ++
      "theorem sammlung" ++ toString k ++ " : ∀ f ∈ stueck" ++ toString k ++ ", FnPflicht u rk f :=\n  " ++
        beweis ++ "\n\n" ++ fuss modul }

def wurzelDatei (modul : String) (anzahl : Nat) (ablehnungen : List String) : Datei :=
  let namen := (List.range anzahl).map fun k => "stueck" ++ toString k
  let beweise := (List.range anzahl).map fun k => "sammlung" ++ toString k
  let rumpf :=
    if ablehnungen.isEmpty then
      "theorem fns_eq : u.fns = " ++ balanciert "++" "[]" 64 namen ++ " := rfl\n\n" ++
      "theorem alle : ∀ f ∈ u.fns, FnPflicht u rk f := by\n  rw [fns_eq]\n  exact " ++
        baum (fun a b => "(fnPflicht_append " ++ a ++ " " ++ b ++ ")") "fnPflicht_nil" 64 beweise ++ "\n\n" ++
      "theorem einheit : EinheitTeil u := ⟨by decide, by decide, by decide⟩\n\n" ++
      "theorem pflichten : PflichtenEinheit u := ⟨einheit, rk, alle⟩\n\n" ++
      "/-- **Premise (b) of the goal theorem** for the unit Stage 0 compiles from `quelle`. -/\n" ++
      "theorem nutzer (c : Gabbro.Stage0.Compiled quelle) (hu : c.unit = u) :\n" ++
      "    ∃ (P : Gabbro.Grammatik.Programm (declOf u)) (fs : List (declOf u).Fn) (hn : nullB u = true),\n" ++
      "      lowerAllg u = .ok (P, fs) ∧ Gabbro.Grammatik.Zielsatz.NutzerPflicht (einheitAllg u P hn) :=\n" ++
      "  nutzer_aus_stage0 pflichten c hu\n\n"
    else
      "/-! REFUSED: premise (b) is not stated, because the bridge does not carry this unit yet:\n" ++
        String.join (ablehnungen.map fun r => "  * " ++ r ++ "\n") ++ "-/\n\n"
  { pfad := modul.replace "." "/"
    text := kopf modul (["Bruecke.Kette.Stufe0", modul ++ ".Quelle", modul ++ ".Daten"] ++
        (if ablehnungen.isEmpty then (List.range anzahl).map (sammlungModul modul) else []))
        ("The unit checks and premise (b) of the goal theorem (written by `gabbrov`). That `u` is the\n" ++
         "    unit Stage 0 compiles from `quelle` is the premise `c.unit = u` of `nutzer`; the module\n" ++
         "    `" ++ modul ++ ".Pruefung` checks it by running Stage 0's front end.") ++ rumpf ++ fuss modul }

/-- The check of the anchoring premise, by running Stage 0's front end; no theorem imports it. -/
def pruefungDatei (modul : String) : Datei :=
  { pfad := modul.replace "." "/" ++ "/Pruefung"
    text := (kopf modul ["Bruecke.Kette.Stufe0", modul ++ ".Quelle", modul ++ ".Daten"]
        "Checks that `u` is the unit Stage 0's front end builds from `quelle` (written by `gabbrov`).").replace
        "@[expose] public section"
        ("meta import Bruecke.Kette.Stufe0\nmeta import " ++ modul ++ ".Quelle\nmeta import " ++ modul ++
          ".Daten\n@[expose] public section") ++
      "#guard stufe0Einheit quelle == .ok u\n\n" ++ fuss modul }

/-- The rank of every function of an acyclic call graph, in linear time (Kahn's order): a function
    without callees has rank 0, every other one more than the highest of its callees. Functions on a
    cycle keep rank 0; `rangFnB` then fails for them and the generator names the refusal. The ranks
    are data of the generated files only: `rangFnB` checks them in every function's module. -/
def raenge (u : UProg) : List (String × Nat) := Id.run do
  let namen : Std.HashSet String := u.fns.foldl (fun s f => s.insert f.name) {}
  let rufe : List (String × List String) :=
    u.fns.map fun f => (f.name, (calleesOf f).filter namen.contains)
  let rufTafel : Std.HashMap String (List String) := rufe.foldl (fun m p => m.insert p.1 p.2) {}
  let mut offen : Std.HashMap String Nat := {}
  let mut rufer : Std.HashMap String (List String) := {}
  for (n, cs) in rufe do
    offen := offen.insert n cs.length
    for c in cs do
      rufer := rufer.insert c (n :: rufer.getD c [])
  let mut rang : Std.HashMap String Nat := {}
  let mut warte : Array String := (rufe.filter fun p => p.2.isEmpty).toArray.map (·.1)
  let mut i := 0
  for _ in [0:rufe.length + 1] do
    if h : i < warte.size then
      let n := warte[i]
      i := i + 1
      let r := ((rufTafel.getD n []).map fun c => rang.getD c 0 + 1).foldl max 0
      rang := rang.insert n r
      for k in rufer.getD n [] do
        let o := offen.getD k 1 - 1
        offen := offen.insert k o
        if o == 0 then warte := warte.push k
  return u.fns.map fun f => (f.name, rang.getD f.name 0)

/-- **The generator.** All files of the unit of `src` under the module prefix `modul`, or the
    front end's refusal. -/
def dateien (modul src : String) : Except String (List Datei) := do
  let u ← match stufe0Einheit src with
    | .ok u => pure u
    | .error e => throw ("Stage 0's front end refuses the source: " ++ e)
  let fs := u.fns.zipIdx.map fun (f, i) => (i, f)
  let stuecke := teile stueckGroesse fs
  let anzahl := stuecke.length
  let rang := raenge u
  let rangTafel : Std.HashMap String Nat := rang.foldl (fun m p => m.insert p.1 p.2) {}
  let rk : String → Nat := fun n => rangTafel.getD n 0
  let gelesen := fs.map fun (i, f) => (i, f, match grosseSchleife u f with
    | some _ => none
    | none => zuBodyZ u f)
  let fnAbl := gelesen.filterMap fun (_, f, b) =>
    let gruende := (match b, grosseSchleife u f with
      | some _, _ => []
      | none, some g => [g]
      | none, none => [koerperAblehnung f]) ++
      fnAblehnungen u f ++ (if bindFrischB f then [] else ["a local binder is not fresh"]) ++
      (if rangFnB rk f then [] else ["recursive call (the generator states rank duties only)"])
    if gruende.isEmpty then none else some (f.name ++ ": " ++ String.intercalate "; " gruende)
  let einheitAbl :=
    (if nullB u then [] else ["initial table or static memory outside the supported numeric ranges"]) ++
    (if stimmigUnitB u then [] else stimmigAblehnungen u |>.filter (fun r => !(r.splitOn ": ").length > 1)) ++
    (if ohneTransitionenB u then [] else ["a state declares a generated transition"])
  let ablehnungen := einheitAbl ++ fnAbl
  let pflichten := gelesen.filterMap fun (i, f, b) =>
    b.map fun body => [pflichtDatei modul i f body, beweisDatei modul i f]
  let sammlungen := if ablehnungen.isEmpty then
      stuecke.zipIdx.map fun (st, k) => sammlungDatei modul k (st.map (·.1)) else []
  pure ([quelleDatei modul src, wurzelDatei modul anzahl ablehnungen, datenDatei modul u anzahl rang,
      pruefungDatei modul] ++
    stuecke.zipIdx.map (fun (st, k) => datenStueck modul k st) ++ pflichten.flatten ++ sammlungen)

end Gabbro.Bruecke.Vorlage
