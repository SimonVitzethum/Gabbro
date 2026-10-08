/-
  File:      Grammatik/GabbroV/GvParserFragment3.lean
  Subject:   GabbroV bridge: two more elaboration cases (agent 02,
             follow-up).

  After the inert-item case (`GvParserFragment.lean`, 108), the remaining
  elaboration blockers over all 157 corpus files are measured in
  REPORT-02.md (new histogram: OK 10, parse 48, elab 99). Of those, two
  are actionable as new elaboration cases without touching `Parser/`:
  dropped prototypes (`protoT`: 13 first-offense, 26 files total) and
  normalized exclusive bounds (`lo ..< hi` with known bounds: moves 122
  and 151 forward). Every other remaining blocker needs a G form that
  does not exist (control flow, `let`, shifts, calls as values, shared
  or masking locks, reasons, atomics, devices, missing types) or an
  unsound weakening (dropping guards, requires, entry handlers); each is
  recorded in REPORT-02.md with its evidence, not implemented.
  Both cases build cumulatively on `elabU02`.
-/
import Grammatik.GabbroV.GvParserFragment
import Grammatik.Parser.Uebersetze

namespace Gabbro.Grammatik.GabbroV.GvParserFragment3

open Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.GabbroV.GvParserFragment

/-- **Is this a prototype?** (`protoT`: a bodiless function
    declaration). Callers of it fail loudly as "Ruf unbekannt"
    (measured on 72); uncalled ones are inert, like dropped statics. -/
def istProto : SItemTief → Bool
  | .protoT .. => true
  | _ => false

/-- **Drop top-level prototypes.** -/
def dropProto : List SItemTief → List SItemTief
  | [] => []
  | it :: rest =>
    if istProto it then dropProto rest else it :: dropProto rest

/-- **Elaborate like `elabU02` after dropping prototypes.** -/
def elabU03 (items : List SItemTief) : Except String UProg :=
  elabU02 (dropProto (uMembers items))

/-- **Dropping changes nothing on prototype-free lists.** -/
theorem dropProto_id (l : List SItemTief)
    (h : ∀ it ∈ l, istProto it = false) :
    dropProto l = l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    have hhd : istProto hd = false :=
      h hd (List.mem_cons.mpr (Or.inl rfl))
    have htl : ∀ it ∈ tl, istProto it = false := fun it hm =>
      h it (List.mem_cons.mpr (Or.inr hm))
    simp [dropProto, hhd, ih htl]

/-- **On units whose unwrapped items are prototype-free the new
    elaborator IS `elabU02`.** -/
theorem elabU03_stimmt (items : List SItemTief)
    (h : dropProto (uMembers items) = uMembers items) :
    elabU03 items = elabU02 (uMembers items) := by
  show elabU02 (dropProto (uMembers items)) = elabU02 (uMembers items)
  rw [h]

/-- **Joint witness for `elabU03_stimmt`**: 104's items are
    prototype-free and both elaborators agree on them. -/
theorem elabU03_stimmt_zeuge :
    dropProto (uMembers items104) = uMembers items104 ∧
    elabU03 items104 = elabU02 items104 :=
  ⟨rfl, rfl⟩

#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment3.dropProto_id
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment3.elabU03_stimmt
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment3.elabU03_stimmt_zeuge

/-- **A failing item check fails `elabU02`.** Relay of
    `elabU_bei_RestFehler` through the inert strip. -/
theorem elabU02_bei_RestFehler (ms : List SItemTief) (e : String)
    (hR : uRestFehler (uMembers (ohneInert (uMembers ms))) = .error e) :
    elabU02 ms = .error e :=
  elabU_bei_RestFehler _ e hR

/-- **Units that still carry an off-fragment item are still refused.**
    Only inert items and prototypes are forgiven. -/
theorem elabU03_verweigert_noch (items : List SItemTief)
    (h : ∃ it ∈ uMembers (ohneInert (uMembers (dropProto (uMembers items)))),
      istGegenstand it = true) :
    ∃ e, elabU03 items = .error e := by
  have hR := uRestFehler_faellt _ h
  exact ⟨_, elabU02_bei_RestFehler _ _ hR⟩

/-- **Synthetic witness items**: one table, one uncalled prototype, one
    clean function. Non-degenerate: a real table and a real body. -/
def wProtoItems : List SItemTief :=
  [.modulT "beispiel::zeuge"
    [.tabelleT "T" (.some (.lit 1)) .none .none false
      [.tPlatz [{ fname := "v", ftyp := .atom "u32",
                  pos := .none, bezug := .none, wo := .none,
                  reserviert := false, byOps := false }]],
    .protoT { art := "impl", name := "h", params := [],
              ergebnis := .none, fehler := .none, klauseln := [] },
    .funktionT
      { art := "impl", name := "f", params := [],
        ergebnis := .none, fehler := .none, klauseln := [] }
      (.block [] .none)]]

/-- **The witness program**: the table and the function; the prototype
    is gone. -/
def wProtoProg : UProg :=
  { tabellen := [{ name := "T", count := 1,
                   felder := [("v", 0, 4294967295)], bools := [] }],
    sperren := [],
    fns := [{ name := "f", params := [], parten := [],
              ergebnis := .none, ergBool := false,
              held := [], schreibt := [], sichert := [],
              saetze := [], rueck := .keine }],
    wurzeln := [] }

/-- **Refused before**: `elabU02` stops at the prototype. -/
theorem wProto_vorher :
    beqElabU (elabU02 wProtoItems)
      (.error "Gegenstand ohne G-Form") = true := by
  decide

/-- **Elaborates now**: `elabU03` yields exactly the pasted program. -/
theorem wProto_jetzt :
    beqElabU (elabU03 wProtoItems) (.ok wProtoProg) = true := by
  decide

#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment3.elabU02_bei_RestFehler
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment3.elabU03_verweigert_noch
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment3.wProto_vorher
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment3.wProto_jetzt

/-! ## Case 2: exclusive bounds with known bounds -/

/-- **The unit's constant scope** (the same computation `elabU` uses
    for counts). -/
def konstWerte (items : List SItemTief) : List (String × Int) :=
  let ms := uMembers items
  uConstsRech (uKonstFns ms) ms []

/-- Look a constant up by name. -/
def konstSucht : List (String × Int) → String → Option Int
  | [], _ => none
  | (m, v) :: rest, n =>
    if strEq m n then some v else konstSucht rest n

/-- A bound expression as a number: a literal, or a known constant. -/
def schrankeZahl (ks : List (String × Int)) : SExpr → Option Nat
  | .lit n => some n
  | .variable c =>
    match konstSucht ks c with
    | .some v => if 0 ≤ v then some v.toNat else none
    | .none => none
  | _ => none

/-- **Normalize one type**: `lo ..< hi` becomes `lo .. hi-1` once both
    bounds are known numbers and the range is non-empty (exact same set
    of integers); inclusive bounds with known constants are substituted
    as written. Anything else passes through and stays loudly refused
    downstream. -/
def normTyp (ks : List (String × Int)) : STyp → STyp
  | .bereich t lo hi true =>
    match schrankeZahl ks lo, schrankeZahl ks hi with
    | .some a, .some b =>
      if a < b then .bereich t (.lit a) (.lit (b - 1)) false
      else .bereich t lo hi true
    | _, _ => .bereich t lo hi true
  | .bereich t lo hi false =>
    match schrankeZahl ks lo, schrankeZahl ks hi with
    | .some a, .some b => .bereich t (.lit a) (.lit b) false
    | _, _ => .bereich t lo hi false
  | t => t

/-- Normalize declaration-level type positions (function parameter and
    result types, slot field types, alias bodies). Bodies holding types
    are dead for other reasons (`let`, `narrow`), so nothing is lost. -/
def normFeld (ks : List (String × Int)) (f : SFeld) : SFeld :=
  { f with ftyp := normTyp ks f.ftyp }

def normTeil (ks : List (String × Int)) : STabTeil → STabTeil
  | .tPlatz fds => .tPlatz (fds.map (normFeld ks))
  | t => t

def normSig (ks : List (String × Int)) (s : FnSig) : FnSig :=
  { s with
    params := s.params.map (fun p => (p.1, normTyp ks p.2)),
    ergebnis := s.ergebnis.map (normTyp ks) }

def normAlias (ks : List (String × Int)) : STyp → STyp :=
  normTyp ks

def normItem (ks : List (String × Int)) : SItemTief → SItemTief
  | .tabelleT n c a b g parts =>
    .tabelleT n c a b g (parts.map (normTeil ks))
  | .funktionT s k => .funktionT (normSig ks s) k
  | .typT f n ps o r => .typT f n (ps.map (normTyp ks)) o
    (r.map (normAlias ks))
  | it => it

/-- **Normalize a whole unit** (unwrap like `elabU`, then rewrite). -/
def normProg (items : List SItemTief) : List SItemTief :=
  let ks := konstWerte items
  (uMembers items).map (normItem ks)

/-- **Elaborate like `elabU02` after bound normalization.** -/
def elabU04 (items : List SItemTief) : Except String UProg :=
  elabU02 (normProg items)

/-- **On units the normalization leaves alone the new elaborator IS
    `elabU02`.** -/
theorem elabU04_stimmt (items : List SItemTief)
    (h : normProg items = uMembers items) :
    elabU04 items = elabU02 (uMembers items) := by
  show elabU02 (normProg items) = elabU02 (uMembers items)
  rw [h]

/-- **Joint witness for `elabU04_stimmt`**: 104 normalizes to itself
    (inclusive literal bounds only) and both elaborators agree. -/
theorem elabU04_stimmt_zeuge :
    normProg (uMembers items104) = uMembers items104 ∧
    elabU04 items104 = elabU02 items104 :=
  ⟨rfl, rfl⟩

/-- **Units that still carry an off-fragment item are still refused.**
    Normalization never invents elaborability. -/
theorem elabU04_verweigert_noch (items : List SItemTief)
    (h : ∃ it ∈ uMembers (ohneInert (uMembers (normProg items))),
      istGegenstand it = true) :
    ∃ e, elabU04 items = .error e := by
  have hR := uRestFehler_faellt _ h
  exact ⟨_, elabU02_bei_RestFehler _ _ hR⟩

/-- **Synthetic witness items**: one table and one function whose
    parameter uses an exclusive bound. -/
def wExklusivItems : List SItemTief :=
  [.modulT "beispiel::zeuge"
    [.tabelleT "T" (.some (.lit 2)) .none .none false
      [.tPlatz [{ fname := "v", ftyp := .atom "u32",
                  pos := .none, bezug := .none, wo := .none,
                  reserviert := false, byOps := false }]],
    .funktionT
      { art := "impl", name := "f",
        params := [("i",
          .bereich (.atom "u32") (.lit 0) (.lit 2) true)],
        ergebnis := .some
          (.bereich (.atom "u32") (.lit 0) (.lit 100) false),
        fehler := .none, klauseln := [] }
      (.block [] (.some (.ret (.some (.variable "i")))))]]

/-- **The witness program**: the parameter reads `0 .. 1`. -/
def wExklusivProg : UProg :=
  { tabellen := [{ name := "T", count := 2,
                   felder := [("v", 0, 4294967295)], bools := [] }],
    sperren := [],
    fns := [{ name := "f", params := [("i", .int 0 1)],
              parten := [.int], ergebnis := .some (0, 100),
              ergBool := false, held := [], schreibt := [],
              sichert := [], saetze := [],
              rueck := .wert (.param "i") }],
    wurzeln := [] }

/-- **Refused before**: `elabU02` has no exclusive-bound form. -/
theorem wExklusiv_vorher :
    beqElabU (elabU02 wExklusivItems)
      (.error "Typ ohne G-Form") = true := by
  decide

/-- **Elaborates now**: `elabU04` yields exactly the pasted program. -/
theorem wExklusiv_jetzt :
    beqElabU (elabU04 wExklusivItems) (.ok wExklusivProg) = true := by
  decide

#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment3.elabU04_stimmt
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment3.elabU04_stimmt_zeuge
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment3.elabU04_verweigert_noch
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment3.wExklusiv_vorher
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment3.wExklusiv_jetzt

/-
  CUTS (agent 02, follow-up -- two more elaboration cases):
  1. PROVED here: prototype-drop (`istProto`, `dropProto`, `elabU03`)
     with identity, agreement (`dropProto_id`, `elabU03_stimmt`, 104),
     refusal relay (`elabU02_bei_RestFehler`,
     `elabU03_verweigert_noch`) and a synthetic witness pair
     (`wProto_vorher`, `wProto_jetzt`); exclusive-bound normalization
     with known bounds (`konstWerte`, `konstSucht`, `schrankeZahl`,
     `normTyp`, `normFeld`, `normTeil`, `normSig`, `normAlias`,
     `normItem`, `normProg`, `elabU04`) with agreement
     (`elabU04_stimmt`, 104), refusal (`elabU04_verweigert_noch`) and a
     synthetic witness pair (`wExklusiv_vorher`, `wExklusiv_jetzt`).
     Corpus movement measured by probes: protoT-drop moves 72 to a
     loud `Ruf unbekannt` (no silent acceptance); normalization moves
     122 (`Typ` to `Writes-Klausel`) and 151 (`Typ` to `Wert`). No
     corpus unit flips fully on any single remaining case (exhaustive
     flip probes over all 157 files); all other remaining blockers
     need missing G forms or unsound weakenings (REPORT-02.md).
  2. NOT proved: anything beyond the elaborator; `SAnw`-internal type
     positions (dead for other reasons); inclusive-const substitution
     has no observable first-error effect today; nested modules
     re-unwrap (as in `elabU02`).
-/

end Gabbro.Grammatik.GabbroV.GvParserFragment3
