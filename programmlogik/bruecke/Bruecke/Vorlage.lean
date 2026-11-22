module
public import Bruecke.Zertifikat.WP
public import Grammatik.Parser.Elab.UebersetzePipeline
@[expose] public section

/-!
# GabbroV's generator: the Lean files of a unit's certificate

`dateien modul src` runs Stage 0's front end on the source text once (`stufe0Einheit`, the unit
Stage 0 compiles) and writes the certificate of that unit as Lean modules under the module prefix
`modul` (the tool `gabbrov`, `Vorlage/Haupt.lean`). The duties are the model's certificate
(`LogikPflichten`, exactly premise (b) by `logikPflichten_iff`) over the program the lowering builds
from the unit: ONE theorem (`nutzerA_aus_ziele`) covers every language form; nothing is read into
another language and no form is refused. The unit is pinned as data; the run facts `c.unit = u` and
`ohneAltGlobalB c.expanded` are facts of Stage 0's run, checked in `M/Pruefung.lean`.

* `M/Quelle.lean`        the source text, as pieces;
* `M/Daten/S<k>.lean`    the elaborated functions of chunk `k` and their list;
* `M/Daten.lean`         the unit `u` and its length;
* `M/Pflicht/F<i>.lean`  the duty `ziel<i>` of function `i`: its logic (`ZielF`);
* `M/Beweis/F<i>.lean`   YOUR proof of `ziel<i>`; written once, never overwritten;
* `M/Sammlung/S<k>.lean` the duties of chunk `k` collected;
* `M.lean`               premise (b) of Stage 0's image theorem (`nutzerBild`).
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

/-- The string modules whose bodies the kernel unfolds when it evaluates the lowering. -/
def stringModule : List String :=
  ["Init.Data.String.Basic",
   "Init.Data.String.Bootstrap",
   "Init.Data.String.Decode",
   "Init.Data.String.Defs",
   "Init.Data.String.Extra",
   "Init.Data.String.FindPos",
   "Init.Data.String.Hashable",
   "Init.Data.String.Iter",
   "Init.Data.String.Iter.Basic",
   "Init.Data.String.Iter.Intercalate",
   "Init.Data.String.Iterate",
   "Init.Data.String.Iterator",
   "Init.Data.String.Legacy",
   "Init.Data.String.Length",
   "Init.Data.String.Modify",
   "Init.Data.String.OrderInstances",
   "Init.Data.String.Pattern",
   "Init.Data.String.Pattern.Basic",
   "Init.Data.String.Pattern.Char",
   "Init.Data.String.Pattern.Pred",
   "Init.Data.String.Pattern.String",
   "Init.Data.String.PosRaw",
   "Init.Data.String.Search",
   "Init.Data.String.Slice",
   "Init.Data.String.Stream",
   "Init.Data.String.Subslice",
   "Init.Data.String.Substring",
   "Init.Data.String.TakeDrop",
   "Init.Data.String.Termination",
   "Init.Data.String.ToSlice"]

/-- The guardian's form of a unit: ONE module with the source, the data, every duty and every logic
    statement (no proof files), so that a whole unit is checked by one `lean` process. The parts are the
    generated modules' bodies, in their dependency order. -/
def einDatei (modul : String) (ds : List Datei) : Datei :=
  let basis := modul.replace "." "/"
  let rang (d : Datei) : Option Nat :=
    if d.pfad == basis ++ "/Quelle" then some 0
    else if (d.pfad.splitOn (basis ++ "/Daten/S")).length > 1 then some 1
    else if d.pfad == basis ++ "/Daten" then some 2
    else if (d.pfad.splitOn (basis ++ "/Pflicht/F")).length > 1 then some 3
    else if (d.pfad.splitOn (basis ++ "/Logik/F")).length > 1 then some 4
    else none
  let rumpf (d : Datei) : String :=
    let nachKopf := match d.text.splitOn "set_option maxRecDepth 100000\n\n" with
      | _ :: rest => "set_option maxRecDepth 100000\n\n".intercalate rest
      | [] => d.text
    match nachKopf.splitOn ("end " ++ modul ++ "\n") with
    | teile@(_ :: _ :: _) => "".intercalate teile.dropLast
    | _ => nachKopf
  let teile := (List.range 5).flatMap fun k => (ds.filter (rang · == some k)).map rumpf
  { pfad := basis ++ "/Ein"
    text := "module\npublic import Bruecke.Zertifikat.WP\npublic import Bruecke.Zertifikat.Logik\n" ++
      String.join (stringModule.map fun i => "import all " ++ i ++ "\n") ++
      "@[expose] public section\n\nnamespace " ++ modul ++ "\n\n" ++
      "open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze\n" ++
      "open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Bruecke\n\n" ++
      "set_option maxRecDepth 100000\n\n" ++ "\n".intercalate teile ++ "\nend " ++ modul ++ "\n" }

def kopf (modul : String) (imports : List String) (doc : String) (alle : List String := []) : String :=
  "module\n" ++ String.join (imports.map fun i => "public import " ++ i ++ "\n") ++
  String.join (alle.map fun i => "import all " ++ i ++ "\n") ++
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
    text := kopf modul ["Bruecke.Zertifikat.WP"] "The source text of the unit, byte for byte (written by `gabbrov`)." ++
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
    text := kopf modul ["Bruecke.Zertifikat.WP"]
        ("The elaborated functions of chunk " ++ toString k ++ " (written by `gabbrov`).") ++
      String.join (fs.map fun (i, f) =>
        "/-- `" ++ f.name ++ "` -/\ndef " ++ fnName i ++ " : UFn :=\n  " ++ breit (repr f) ++ "\n\n") ++
      "def stueck" ++ toString k ++ " : List UFn := [" ++
        String.intercalate ", " (fs.map fun (i, _) => fnName i) ++ "]\n\n" ++ fuss modul }

def datenDatei (modul : String) (u : UProg) (anzahl : Nat) : Datei :=
  let namen := (List.range anzahl).map fun k => "stueck" ++ toString k
  { pfad := modul.replace "." "/" ++ "/Daten"
    text := kopf modul ((List.range anzahl).map (stueckModul modul))
        "The elaborated unit `u` as data (written by `gabbrov`)." ++
      "def u : UProg :=\n  " ++ einheitText u (balanciert "++" "[]" 64 namen) ++ "\n\n" ++
      "theorem laenge : u.fns.length = " ++ toString u.fns.length ++ " := rfl\n\n" ++ fuss modul }

/-- The source contract of a function in a comment line. -/
def vertrag (f : UFn) : String :=
  "`" ++ f.name ++ "`" ++
  (if f.needs.isEmpty then "" else ", " ++ toString f.needs.length ++ " requires clause(s)") ++
  (if f.gives.isEmpty then ", no ensures" else ", " ++ toString f.gives.length ++ " ensures clause(s)")

def pflichtModul (modul : String) (i : Nat) : String := modul ++ ".Pflicht.F" ++ toString i
def beweisModul (modul : String) (i : Nat) : String := modul ++ ".Beweis.F" ++ toString i

def pflichtDatei (modul : String) (i : Nat) (f : UFn) : Datei :=
  let si := toString i
  { pfad := (pflichtModul modul i).replace "." "/"
    text := kopf modul [modul ++ ".Daten"] ("The duty of " ++ vertrag f ++ " (written by `gabbrov`; regenerated on every run).") ++
      "theorem lt" ++ si ++ " : " ++ si ++ " < u.fns.length := by rw [laenge]; decide\n\n" ++
      "/-- **What you prove about `" ++ f.name ++ "`**: its logic over the program Stage 0 lowers from `u`\n" ++
      "    (`ZielF`): from `requires`, every return meets `ensures` and the owed invariants, and no call\n" ++
      "    stops on a precondition or a logic stop, at every budget, under every call meaning, oracle and\n" ++
      "    environment move the goal theorem quantifies. Nothing else is owed. -/\n" ++
      "def ziel" ++ si ++ " : Prop := ZielF u ⟨" ++ si ++ ", lt" ++ si ++ "⟩\n\n" ++ fuss modul }

def logikModul (modul : String) (i : Nat) : String := modul ++ ".Logik.F" ++ toString i

/-- What remains of the duty after the language's automation: `logik<i>`, the program's logic as one
    statement, and `logik<i>.genuegt : logik<i> → ziel<i>` (regenerated on every run). -/
def logikDatei (modul : String) (i : Nat) (f : UFn) : Datei :=
  let si := toString i
  { pfad := (logikModul modul i).replace "." "/"
    text := kopf modul [pflichtModul modul i, "Bruecke.Zertifikat.Logik"]
        ("The program's logic owed by `" ++ f.name ++ "`: what the language's proof of its duty leaves " ++
         "(written by `gabbrov`; regenerated on every run). `True` when nothing remains.") stringModule ++
      "gabbrov_logik logik" ++ si ++ " : ziel" ++ si ++ "\n\n" ++ fuss modul }

/-- The user's proof file: written once, never replaced. -/
def beweisDatei (modul : String) (i : Nat) (f : UFn) : Datei :=
  let si := toString i
  { pfad := (beweisModul modul i).replace "." "/"
    ersetzen := false
    text := kopf modul [logikModul modul i] ("Your proof of the duty of `" ++ f.name ++
        "`. `gabbrov` writes this file once and never replaces it.") ++
      "/-- The language proves everything but `logik" ++ si ++ "` (`#print logik" ++ si ++ "` shows it); `trivial`\n" ++
      "    proves it when nothing remains. Otherwise replace `trivial` by your proof of the program's logic. -/\n" ++
      "theorem beweis" ++ si ++ " : ziel" ++ si ++ " := logik" ++ si ++ ".genuegt (by trivial)\n\n" ++ fuss modul }

def sammlungModul (modul : String) (k : Nat) : String := modul ++ ".Sammlung.S" ++ toString k

def indexListe (is : List Nat) : String := "[" ++ String.intercalate ", " (is.map toString) ++ "]"

def sammlungDatei (modul : String) (k : Nat) (is : List Nat) : Datei :=
  let beweis := is.foldr (fun i acc => "zielI_cons (fun _ => beweis" ++ toString i ++ ")\n    (" ++ acc ++ ")") "zielI_nil"
  { pfad := (sammlungModul modul k).replace "." "/"
    text := kopf modul (is.map (beweisModul modul)) ("The duties of chunk " ++ toString k ++ " (written by `gabbrov`).") ++
      "theorem sammlung" ++ toString k ++ " : ∀ i ∈ " ++ indexListe is ++ ", ZielI u i :=\n  " ++
        beweis ++ "\n\n" ++ fuss modul }

def wurzelDatei (modul : String) (u : UProg) (stuecke : List (List Nat)) (altFrei : Bool) : Datei :=
  let ks := List.range stuecke.length
  let listen := stuecke.map indexListe
  let beweis := baum (fun a b => "(zielI_append " ++ a ++ " " ++ b ++ ")") "zielI_nil" 64
    (ks.map fun k => "sammlung" ++ toString k)
  let rumpf :=
    "theorem bereich_eq : List.range " ++ toString u.fns.length ++ " = " ++
      balanciert "++" "[]" 64 listen ++ " := rfl\n\n" ++
    "/-- Every function's duty. -/\n" ++
    "theorem alle : ∀ f, ZielF u f :=\n  alle_ziele laenge (by rw [bereich_eq]; exact " ++ beweis ++ ")\n\n" ++
    (if altFrei then
      "/-- **Premise (b) of Stage 0's image theorem** (`NutzerPflichtA (output.einheit Q)`, also of\n" ++
      "    `output.goalUnit Q`) for every compilation of `quelle` whose unit is `u`, every language form:\n" ++
      "    the run facts `hu` and `hold` (checked in `Pruefung`), the environment contract of the foreign\n" ++
      "    bodies (`hax`) and Stage 0's decision of the data parts on the judged unit (`hent`). -/\n" ++
      "theorem nutzerBild (c : Gabbro.Stage0.Compiled quelle) (hu : c.unit = u)\n" ++
      "    (hold : ohneAltGlobalB c.expanded = true) (Q : AxEns (declOf c.unit))\n" ++
      "    (sp : Speicher (declOf c.unit)) (args : Env (declOf c.unit) ((declOf c.unit).params c.main))\n" ++
      "    (roots gestartet : List (Σ w : (declOf c.unit).Fn, Env (declOf c.unit) ((declOf c.unit).params w)))\n" ++
      "    (checks : List (CheckDecl (declOf c.unit))) (hax : ∀ a, Gabbro.Grammatik.WP.AxLokalAn Q a)\n" ++
      "    (hent : entschiedenB\n" ++
      "      (Gabbro.Stage0.OldSource.einheitDer c.unit c.program Q sp c.main args roots gestartet checks)\n" ++
      "      (List.finRange c.unit.locks.length) = true) :\n" ++
      "    Gabbro.Grammatik.Zielsatz.NutzerPflichtA\n" ++
      "      (Gabbro.Stage0.OldSource.einheitDer c.unit c.program Q sp c.main args roots gestartet checks) :=\n" ++
      "  nutzerA_aus_ziele alle c hu hold Q sp args roots gestartet checks hax hent\n\n"
     else
      "/-! REFUSED: a postcondition reads `old` of a static; Stage 0 restores it in the compiled program,\n" ++
      "    and the duties above are stated over the unrestored lowering. -/\n\n")
  { pfad := modul.replace "." "/"
    text := kopf modul ([modul ++ ".Quelle", modul ++ ".Daten"] ++ ks.map (sammlungModul modul))
        ("Premise (b) of the goal theorem for the unit Stage 0 compiles from `quelle` (written by `gabbrov`).\n" ++
         "    That `u` is that unit is the premise `c.unit = u`; `" ++ modul ++ ".Pruefung` checks it by running\n" ++
         "    Stage 0's front end.") ++ rumpf ++ fuss modul }

/-- The checks of the run facts, by running Stage 0's front end; no theorem imports it. -/
def pruefungDatei (modul : String) : Datei :=
  { pfad := modul.replace "." "/" ++ "/Pruefung"
    text := (kopf modul ["Bruecke.Zertifikat.WP", modul ++ ".Quelle", modul ++ ".Daten"]
        "Checks the run facts of `nutzerBild` by running Stage 0's front end (written by `gabbrov`).").replace
        "@[expose] public section"
        ("meta import Bruecke.Zertifikat.WP\nmeta import " ++ modul ++ ".Quelle\nmeta import " ++ modul ++
          ".Daten\n@[expose] public section") ++
      "#guard stufe0Einheit quelle == .ok u\n\n" ++
      "-- No postcondition reads `old` of a static (the run fact `hold` of `nutzerBild`).\n" ++
      "#guard stufe0AltFreiB quelle\n\n" ++
      "-- The lowering accepts `u`: the duties are not vacuous.\n" ++
      "#guard (match lowerAllg u with | .ok _ => true | .error _ => false)\n\n" ++ fuss modul }

/-- **The generator.** All files of the unit of `src` under the module prefix `modul`, or the
    front end's refusal. -/
def dateien (modul src : String) : Except String (List Datei) := do
  let u ← match stufe0Einheit src with
    | .ok u => pure u
    | .error e => throw ("Stage 0's front end refuses the source: " ++ e)
  match lowerAllg u with
  | .error e => throw ("Stage 0's lowering refuses the unit (Stage 0 compiles no image of it): " ++ e)
  | .ok _ => pure ()
  let fs := u.fns.zipIdx.map fun (f, i) => (i, f)
  let stuecke := teile stueckGroesse fs
  let pflichten := fs.map fun (i, f) => [pflichtDatei modul i f, logikDatei modul i f, beweisDatei modul i f]
  let sammlungen := stuecke.zipIdx.map fun (st, k) => sammlungDatei modul k (st.map (·.1))
  pure ([quelleDatei modul src, wurzelDatei modul u (stuecke.map (·.map (·.1))) (stufe0AltFreiB src),
      datenDatei modul u stuecke.length, pruefungDatei modul] ++
    stuecke.zipIdx.map (fun (st, k) => datenStueck modul k st) ++ pflichten.flatten ++ sammlungen)

end Gabbro.Bruecke.Vorlage
