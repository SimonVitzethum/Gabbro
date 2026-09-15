/-
  File:      Grammatik/Parser/Uebersetze.lean
  Subject:   T3 PART 4: from the parsed surface tree to the G program.

  The Lean parser covers the whole surface (lanes 135/154/157);
  the Rust exporter `gabbro lean-g` (lane 144,
  `crates/gabbro-check/src/lean_g.rs`) turns a checked unit into
  the G program term `gP : Programm gD` (see
  `grammatik/Grammatik/Export104.lean`). This file closes the
  loop in Lean: an elaborator from the parsed surface tree
  (`SItemTief` list) to the same declaration/program shape the
  exporter produces.

  Two stages, like the exporter (collect, then translate):

  * surface to U: `elabU` maps the fragment `lean_g.rs`
    exports -- tables, locks with `Held`, `impl` fns with
    pointer/index/range params, comparison contracts over slot
    reads/`old`/`result`/literals, straight-line bodies of slot
    writes, direct calls, trailing return -- to plain data
    (`UProg`). Every other form is an explicit `.error`
    (the `Except String` channel; no new diagnostic codes).
  * U to G: `lowerU` assembles the `Programm gD` term over the
    exporter's declaration universe `G104_referenz.gD`.

  The 104 instance: `tt104` (token literal), `items104` (parse
  result literal), `uExp104` (elaboration result literal), with
  one kernel check per stage (`u104lex`, `u104parse`,
  `u104elab`) plus the lowering pin (`u104lower : ... = ...
  := rfl`, proof irrelevance covering the proof terms), the
  data agreement (`u104data`, same shape as `export104_data`)
  and the fragment/footprint checks on the Lean-parsed program
  (`u104fragment`, `u104fuss`).
-/
import Grammatik.Export104
import Grammatik.Parser.ElementTief

namespace Gabbro.Grammatik.Parser.Uebersetze

set_option maxRecDepth 100000

/-- An index into a table: a literal or an index parameter. -/
inductive UIdx
  | lit : Int → UIdx
  | param : String → UIdx
  deriving DecidableEq, Repr

/-- One side of an `ensures` comparison: a literal, a numeric
    parameter, a slot read through a pointer parameter (`slot`)
    or at a table (`tab`), the entry value (`alt`), or the
    function result (`erg`). -/
inductive USide
  | lit : Int → USide
  | param : String → USide
  | slot : String → String → UIdx → USide
  | tab : String → String → UIdx → USide
  | alt : String → String → UIdx → USide
  | erg : USide
  deriving DecidableEq, Repr

/-- One `ensures` predicate: a comparison, truth values, or a
    boolean combination (the `tr_ensures` fragment). -/
inductive UEns
  | cmp : String → USide → USide → UEns
  | wahr : UEns
  | falsch : UEns
  | und : UEns → UEns → UEns
  | oder : UEns → UEns → UEns
  | nicht : UEns → UEns
  deriving DecidableEq, Repr

/-- A call argument: a pointer variable passed through
    (`var`), a fresh `rw`-to-`r` pointer to a table with the
    callee's rights (`freshPtr`, the pass-a-fresh-pointer idiom
    of the hand translation), or a value (`wert`: a literal, a
    numeric parameter or a slot read). -/
inductive UArg
  | var : String → UArg
  | freshPtr : String → Bool → UArg
  | wert : USide → UArg
  deriving DecidableEq, Repr

/-- One body statement: a slot write through a pointer (`assign`)
    or at a table (`assignTab`), or a direct call. -/
inductive UStmt
  | assign : String → String → UIdx → USide → UStmt
  | assignTab : String → String → UIdx → USide → UStmt
  | call : String → List UArg → UStmt
  deriving DecidableEq, Repr

/-- The trailing return: nothing, or a value (a literal, a
    numeric parameter or a slot read). -/
inductive URet
  | keine : URet
  | wert : USide → URet
  deriving DecidableEq, Repr

/-- One elaborated table: slot count and one integer range per
    slot field (the `TableModel` of `lean_g.rs`). -/
structure UTab where
  name : String
  count : Int
  felder : List (String × (Int × Int))
  deriving DecidableEq, Repr

/-- One elaborated lock: rank and the guarded table names (the
    `LockModel` of `lean_g.rs`; the `held` budget travels
    nowhere, like `costs`). -/
structure ULock where
  name : String
  rank : Int
  schutz : List String
  deriving DecidableEq, Repr

/-- A parameter kind: a pointer to a table, an index into one,
    or a plain integer range (kept beside the `Ty` so an index
    parameter stays recognizable after `Ty.index` unfolds it to
    `.int 0 (n - 1)`). -/
inductive UParamArt
  | ptr : Nat → Bool → UParamArt
  | index : Nat → UParamArt
  | int : UParamArt
  deriving DecidableEq, Repr

/-- The elaboration context of one function body or contract:
    parameter names, kinds and types in order, the tables and
    locks, the held lock names, the optional result range and
    the function name (for errors). -/
structure UCtx where
  pnamen : List String
  parten : List UParamArt
  ptypen : List Ty
  tabellen : List UTab
  sperren : List ULock
  gehalten : List String
  ergebnis : Option (Int × Int)
  fname : String

/-- One elaborated function: parameters with their `Ty`,
    the optional result range, the held lock names, the written
    table names, the `ensures` list and the body (the
    `CheckedFn` of `lean_g.rs`). -/
structure UFn where
  name : String
  params : List (String × Ty)
  parten : List UParamArt
  ergebnis : Option (Int × Int)
  held : List String
  schreibt : List String
  sichert : List UEns
  saetze : List UStmt
  rueck : URet
  deriving DecidableEq, Repr

/-- The elaborated program: tables, locks, functions. -/
structure UProg where
  tabellen : List UTab
  sperren : List ULock
  fns : List UFn
  deriving DecidableEq, Repr

/-- The members: a single module wrapper is unwrapped, a bare
    list passes through (104 wraps everything in
    `module beispiel::referenz`). -/
def uMembers : List SItemTief → List SItemTief
  | [.modulT _ ms] => ms
  | ms => ms

/-- The constant scope: `const N : u32 = v;` travels as
    (`N`, `v`); any other `const` form has no G form
    (`LG005`: a count must be a numeral). -/
def uConsts : List SItemTief → List (String × Int)
  | [] => []
  | .konstT n _ (.einzeln (.lit v)) :: rest =>
    (n, Int.ofNat v) :: uConsts rest
  | _ :: rest => uConsts rest

/-- The type-alias scope: `type A = u32 in lo .. hi;` travels
    as (`A`, (`lo`, `hi`)); any other `type` body has no G form
    (`LG002`: a range where G needs a `Ty`). -/
def uAliase : List SItemTief → List (String × (Int × Int))
  | [] => []
  | .typT _ n _ _ (.some (.bereich _ (.lit lo) (.lit hi) false)) :: rest =>
    (n, (Int.ofNat lo, Int.ofNat hi)) :: uAliase rest
  | _ :: rest => uAliase rest

/-- Lookup in an association list, with an explicit error. -/
def uSuch (was : String) (xs : List (String × α)) (n : String) : Except String α :=
  match xs with
  | [] => .error (was ++ " unbekannt: " ++ n)
  | (m, v) :: rest => if strEq m n then .ok v else uSuch was rest n

/-- A table by name: its number (position, what `ptr` names)
    and its slot count (what `index` names). -/
def uTabNrAux : List UTab → Nat → String → Except String (Nat × Int)
  | [], _, n => .error ("Tabelle unbekannt: " ++ n)
  | t :: rest, k, n =>
    if strEq t.name n then .ok (k, t.count)
    else uTabNrAux rest (k + 1) n

def uTabNr (tabs : List UTab) (n : String) : Except String (Nat × Int) :=
  uTabNrAux tabs 0 n

/-- A surface type as G sees it: a pointer to a table, an index
    into one, or an integer range (the `ParamTy`/`int_range` of
    `lean_g.rs`). Named address spaces other than `normal`,
    rights other than `r`/`rw`, the optional index and every
    other shape are explicit errors. -/
def uTyp (aliase : List (String × (Int × Int))) (tabs : List UTab) : STyp → Except String Ty
  | .atom a =>
    match uSuch "Typ" aliase a with
    | .ok (lo, hi) => .ok (.int lo hi)
    | .error e => .error e
  | .bereich _ (.lit lo) (.lit hi) false =>
    .ok (.int (Int.ofNat lo) (Int.ofNat hi))
  | .index false t =>
    match uTabNr tabs t with
    | .ok (_, c) => .ok (.index c)
    | .error e => .error e
  | .ptr raum rechte (.atom t) =>
    if !strEq raum "normal" then .error "Adressraum ohne G-Form"
    else if strEq rechte "rw" then
      match uTabNr tabs t with
      | .ok (num, _) => .ok (.ptr num true)
      | .error e => .error e
    else if strEq rechte "r" then
      match uTabNr tabs t with
      | .ok (num, _) => .ok (.ptr num false)
      | .error e => .error e
    else .error "Zeigerrecht ohne G-Form"
  | _ => .error "Typ ohne G-Form"

/-- A slot field type as an integer range (the field loop of
    `read_table`; `wrapping` and everything else are explicit
    errors). -/
def uFeldTyp (aliase : List (String × (Int × Int))) : STyp → Except String (Int × Int)
  | .atom a => uSuch "Typ" aliase a
  | .bereich _ (.lit lo) (.lit hi) false =>
    .ok (Int.ofNat lo, Int.ofNat hi)
  | _ => .error "Feldtyp ohne G-Form"

/-- A count: a literal or a named constant (the `numeral` of
    `lean_g.rs`). -/
def uAnzahl (consts : List (String × Int)) : SExpr → Except String Int
  | .lit v => .ok (Int.ofNat v)
  | .variable c => uSuch "Konstante" consts c
  | _ => .error "Anzahl ohne G-Form"

/-- One slot field: no bit position, no `offset_into`, no
    `where`, neither `reserved` nor `by ops` (all without G
    form, like the refused arms of `read_table`). -/
def uFeld (aliase : List (String × (Int × Int))) : SFeld → Except String (String × (Int × Int))
  | { fname, ftyp, pos := .none, bezug := .none, wo := .none,
      reserviert := false, byOps := false } =>
    match uFeldTyp aliase ftyp with
    | .ok r => .ok (fname, r)
    | .error e => .error e
  | _ => .error "Slotfeld ohne G-Form"

def uFelder : List (String × (Int × Int)) → List SFeld →
    Except String (List (String × (Int × Int)))
  | _, [] => .error "Tabelle ohne Felder"
  | aliase, f :: rest =>
    match uFeld aliase f with
    | .error e => .error e
    | .ok p =>
      match uFelder aliase rest with
      | .error _ => .ok [p]
      | .ok ps => .ok (p :: ps)

/-- One table: `count` and one integer range per slot field.
/// Invariants, `ops`, tree edges, the occupancy mark, an
    `owner` mark, a `backed`/`shared` flag and a missing slot
    are explicit errors (the refused arms of `read_table`). -/
def uTabelle (consts : List (String × Int))
    (aliase : List (String × (Int × Int))) : SItemTief → Except String UTab
  | .tabelleT n (.some cnt) .none .none false [.tPlatz fds] =>
    match uAnzahl consts cnt with
    | .error e => .error e
    | .ok c =>
      match uFelder aliase fds with
      | .error e => .error e
      | .ok fs => .ok { name := n, count := c, felder := fs }
  | _ => .error "Tabelle ohne G-Form"

/-- A `protects` carrier by table or by field name (the guard
    loop of `read_lock`): a table name, or a field of exactly
    one table. -/
def uTraegerTab : List UTab → String → Except String String
  | [], c => .error ("Schutz unbekannt: " ++ c)
  | t :: rest, c =>
    if strEq t.name c then .ok t.name
    else if t.felder.any (fun (f, _) => strEq f c) then .ok t.name
    else uTraegerTab rest c

def uSchutzAux : List UTab → List SExpr → Except String (List String)
  | _, [] => .ok []
  | tabs, .variable c :: rest =>
    match uTraegerTab tabs c with
    | .error e => .error e
    | .ok t =>
      match uSchutzAux tabs rest with
      | .error e => .error e
      | .ok ts => .ok (t :: ts)
  | _, _ :: _ => .error "Schutztraeger ohne G-Form"

/-- One lock: a numeric rank and the guarded tables. Masking
    and the shared hold have no G form; the `held` budget is
    ignored like `costs` (both travel nowhere). -/
def uSperre (tabs : List UTab) : SItemTief → Except String ULock
  | .sperreT n ps (.lit rk) _ .none .none =>
    match uSchutzAux tabs ps with
    | .error e => .error e
    | .ok ts => .ok { name := n, rank := Int.ofNat rk, schutz := ts }
  | _ => .error "Sperre ohne G-Form"

/-- A parameter position by name (the `param_index` of
    `lean_g.rs`; unknown names are `LG005` errors). -/
def uParamNrAux : List String → Nat → String → Except String Nat
  | [], _, p => .error ("Name unbekannt: " ++ p)
  | q :: rest, k, p =>
    if strEq q p then .ok k else uParamNrAux rest (k + 1) p

def uParamNr (ctx : UCtx) (p : String) : Except String Nat :=
  uParamNrAux ctx.pnamen 0 p

/-- The kind of the parameter at a position. -/
def uArtBei : List UParamArt → Nat → Except String UParamArt
  | [], _ => .error "Parameter ausserhalb"
  | a :: _, 0 => .ok a
  | _ :: rest, n + 1 => uArtBei rest n

/-- Every guard of the table is held (the `holds_guards` of
    `lean_g.rs`: the generation-time half of the guard
    proof). -/
def uHaeltWaechter (ctx : UCtx) (t : String) : Except String Unit :=
  let bedarf : List String :=
    ctx.sperren.filterMap (fun l => if l.schutz.any (strEq · t) then some l.name else none)
  if bedarf.all (fun b => ctx.gehalten.any (strEq · b)) then .ok ()
  else .error "Zugriff ohne gehaltenen Waechter"

/-- The slot count of a table by name. -/
def uAnzahlTab (tabs : List UTab) (t : String) : Except String Int :=
  match tabs.find? (fun x => strEq x.name t) with
  | .some x => .ok x.count
  | .none => .error ("Tabelle unbekannt: " ++ t)

/-- An index into a table: a literal inside `count`, or an
    index parameter for the same table (the `tr_index` of
    `lean_g.rs`). -/
def uIndex (ctx : UCtx) (t : String) (num : Nat) : SExpr → Except String UIdx
  | .lit v =>
    match uAnzahlTab ctx.tabellen t with
    | .error e => .error e
    | .ok c =>
      if Int.ofNat v < c then .ok (.lit (Int.ofNat v))
      else .error "Index ausserhalb count"
  | .variable p =>
    match uParamNr ctx p with
    | .error e => .error e
    | .ok j =>
      match uArtBei ctx.parten j with
      | .ok (.index m) =>
        if m == num then .ok (.param p) else .error "Index fremder Tabelle"
      | _ => .error "Index ohne G-Form"
  | _ => .error "Index ohne G-Form"

/-- A slot read `p.slots[i].f` / `T.slots[i].f`: the basis
    (pointer parameter or table name), the table, the field and
    the index (the `slot_access` of `lean_g.rs`). -/
inductive UBasis
  | durch : String → UBasis
  | tabelle : String → UBasis
  deriving DecidableEq, Repr

def uZugriff (ctx : UCtx) : SExpr →
    Except String (UBasis × String × String × UIdx)
  | .feld (.index (.feld (.variable b) s) idx) f =>
    if !strEq s "slots" then .error "Platz ohne G-Form"
    else
      match uParamNr ctx b with
      | .ok j =>
        match uArtBei ctx.parten j with
        | .ok (.ptr num _) =>
          match ctx.tabellen[num]? with
          | .none => .error "Zeigertabelle unbekannt"
          | .some tb =>
            if !(tb.felder.any (fun (g, _) => strEq g f)) then
              .error "Feld unbekannt"
            else match uHaeltWaechter ctx tb.name with
              | .error e => .error e
              | .ok _ =>
                match uIndex ctx tb.name num idx with
                | .error e => .error e
                | .ok ix => .ok (.durch b, tb.name, f, ix)
        | _ => .error "Platz ohne G-Form"
      | .error _ =>
        match ctx.tabellen.find? (fun x => strEq x.name b) with
        | .none => .error ("Name unbekannt: " ++ b)
        | .some tb =>
          if !(tb.felder.any (fun (g, _) => strEq g f)) then
            .error "Feld unbekannt"
          else match uHaeltWaechter ctx tb.name with
            | .error e => .error e
            | .ok _ =>
              match uTabNrAux ctx.tabellen 0 tb.name with
              | .error e => .error e
              | .ok (num, _) =>
                match uIndex ctx tb.name num idx with
                | .error e => .error e
                | .ok ix => .ok (.tabelle b, tb.name, f, ix)
  | _ => .error "Platz ohne G-Form"

/-- One side of an `ensures` comparison (the `tr_side` of
    `lean_g.rs`): literals, numeric parameters, slot reads,
    `old` and `result` travel; a pointer parameter in a
    comparison and everything else are explicit errors. -/
def uSeite (ctx : UCtx) : SExpr → Except String USide
  | .lit v => .ok (.lit (Int.ofNat v))
  | .variable p =>
    match uParamNr ctx p with
    | .error e => .error e
    | .ok j =>
      match uArtBei ctx.parten j with
      | .ok (.ptr _ _) => .error "Zeiger im Vergleich ohne G-Form"
      | .ok _ => .ok (.param p)
      | .error e => .error e
  | .ergebnis =>
    match ctx.ergebnis with
    | .some _ => .ok .erg
    | .none => .error "result ohne Ergebnis ohne G-Form"
  | .alt o =>
    match uZugriff ctx o with
    | .error e => .error e
    | .ok (.durch b, _, f, ix) => .ok (.alt b f ix)
    | .ok (.tabelle b, _, f, ix) => .ok (.alt b f ix)
  | e =>
    match uZugriff ctx e with
    | .error _ => .error "Vergleichsseite ohne G-Form"
    | .ok (.durch b, _, f, ix) => .ok (.slot b f ix)
    | .ok (.tabelle b, _, f, ix) => .ok (.tab b f ix)

/-- A comparison operator with G form (`==`, `!=`, `<`, `<=`,
    `>`, `>=`; G folds all but `lt`/`le`/`eq`). -/
def uIstVgl : String → Bool
  | "==" => true
  | "!=" => true
  | "<" => true
  | "<=" => true
  | ">" => true
  | ">=" => true
  | _ => false

/-- One `ensures` predicate (the `tr_ensures` of `lean_g.rs`). -/
def uSichert (ctx : UCtx) : SExpr → Except String UEns
  | .bin op l r =>
    if uIstVgl op then
      match uSeite ctx l with
      | .error e => .error e
      | .ok a =>
        match uSeite ctx r with
        | .error e => .error e
        | .ok b => .ok (.cmp op a b)
    else if strEq op "&&" then
      match uSichert ctx l with
      | .error e => .error e
      | .ok a =>
        match uSichert ctx r with
        | .error e => .error e
        | .ok b => .ok (.und a b)
    else if strEq op "||" then
      match uSichert ctx l with
      | .error e => .error e
      | .ok a =>
        match uSichert ctx r with
        | .error e => .error e
        | .ok b => .ok (.oder a b)
    else .error "Operator ohne G-Form"
  | .un "!" q =>
    match uSichert ctx q with
    | .error e => .error e
    | .ok a => .ok (.nicht a)
  | .wahr => .ok .wahr
  | .falsch => .ok .falsch
  | _ => .error "Ensures-Klausel ohne G-Form"

/-- A value in a body: a literal, a numeric parameter or a
    slot read (the `tr_value` of `lean_g.rs` at
    `in_ensures := false`: `result` and `old` have no G form
    here). -/
def uWertBody (ctx : UCtx) : SExpr → Except String USide
  | .lit v => .ok (.lit (Int.ofNat v))
  | .variable p =>
    match uParamNr ctx p with
    | .error e => .error e
    | .ok j =>
      match uArtBei ctx.parten j with
      | .ok (.ptr _ _) => .error "Zeiger als Wert ohne G-Form"
      | .ok _ => .ok (.param p)
      | .error e => .error e
  | e =>
    match uZugriff ctx e with
    | .error _ => .error "Wert ohne G-Form"
    | .ok (.durch b, _, f, ix) => .ok (.slot b f ix)
    | .ok (.tabelle b, _, f, ix) => .ok (.tab b f ix)

/-- Sequence: the first error wins (like the exporter's
    straight-line `?`). -/
def uSeq : List (Except String α) → Except String (List α)
  | [] => .ok []
  | .error e :: _ => .error e
  | .ok x :: rest =>
    match uSeq rest with
    | .error e => .error e
    | .ok xs => .ok (x :: xs)

/-- One function head: name, parameters (names, kinds, types),
    the optional result range and the held lock names (pass one
    of `collect` in `lean_g.rs`). -/
structure UFnKopf where
  name : String
  pnamen : List String
  parten : List UParamArt
  ptypen : List Ty
  ergebnis : Option (Int × Int)
  gehalten : List String

/-- A parameter with its kind (the `param_ty` of `lean_g.rs`). -/
def uParam (aliase : List (String × (Int × Int))) (tabs : List UTab) :
    String × STyp → Except String (String × Ty × UParamArt)
  | (n, .ptr raum rechte (.atom t)) =>
    if !strEq raum "normal" then .error "Adressraum ohne G-Form"
    else if strEq rechte "rw" then
      match uTabNr tabs t with
      | .error e => .error e
      | .ok (num, _) => .ok (n, .ptr num true, .ptr num true)
    else if strEq rechte "r" then
      match uTabNr tabs t with
      | .error e => .error e
      | .ok (num, _) => .ok (n, .ptr num false, .ptr num false)
    else .error "Zeigerrecht ohne G-Form"
  | (n, .index false t) =>
    match uTabNr tabs t with
    | .error e => .error e
    | .ok (num, c) => .ok (n, .index c, .index num)
  | (n, t) =>
    match uTyp aliase tabs t with
    | .error e => .error e
    | .ok ty => .ok (n, ty, .int)

/-- A result range (the `int_range` of `lean_g.rs` on the
    result type). -/
def uErgBereich (aliase : List (String × (Int × Int))) : STyp →
    Except String (Int × Int)
  | .atom a => uSuch "Typ" aliase a
  | .bereich _ (.lit lo) (.lit hi) false =>
    .ok (Int.ofNat lo, Int.ofNat hi)
  | _ => .error "Ergebnis ohne G-Form"

/-- `requires Held(L)`: exactly the signature-held locks (the
    requires loop of `check_fn`; every other requires-clause is
    an explicit error). -/
def uGehaltenAux : List ULock → List SExpr → Except String (List String)
  | _, [] => .ok []
  | locks, .variable l :: rest =>
    match locks.find? (fun x => strEq x.name l) with
    | .none => .error ("Sperre unbekannt: " ++ l)
    | .some _ =>
      match uGehaltenAux locks rest with
      | .error e => .error e
      | .ok ls => .ok (l :: ls)
  | _, _ :: _ => .error "Requires-Klausel ohne G-Form"

def uGehalten (locks : List ULock) : List SKlausel →
    Except String (List String)
  | [] => .ok []
  | .voraus (.ruf "Held" args) :: rest =>
    match uGehaltenAux locks args with
    | .error e => .error e
    | .ok ls =>
      match uGehalten locks rest with
      | .error e => .error e
      | .ok ms => .ok (ls ++ ms)
  | .voraus _ :: _ => .error "Requires-Klausel ohne G-Form"
  | _ :: rest => uGehalten locks rest

/-- A name position in a list (for `writes` through a
    parameter). -/
def uStelle : List String → String → Except String Nat
  | [], p => .error ("Name unbekannt: " ++ p)
  | q :: rest, p =>
    if strEq q p then .ok 0
    else
      match uStelle rest p with
      | .error e => .error e
      | .ok k => .ok (k + 1)

/-- The table a `writes` place names (the `write_table` of
    `lean_g.rs`): `writes k.slots` through a pointer parameter,
    or `writes T.slots` at a table. -/
def uSchreibtOrt (kopf : UFnKopf) (tabs : List UTab) : SExpr →
    Except String String
  | .feld (.variable b) s =>
    if !strEq s "slots" then .error "Writes-Klausel ohne G-Form"
    else
      match uStelle kopf.pnamen b with
      | .ok j =>
        match uArtBei kopf.parten j with
        | .ok (.ptr num _) =>
          match tabs[num]? with
          | .some tb => .ok tb.name
          | .none => .error "Zeigertabelle unbekannt"
        | _ => .error "Writes-Klausel ohne G-Form"
      | .error _ =>
        match tabs.find? (fun x => strEq x.name b) with
        | .some tb => .ok tb.name
        | .none => .error ("Name unbekannt: " ++ b)
  | _ => .error "Writes-Klausel ohne G-Form"

/-- The effect arms: `locks L` names held locks, `writes`
    names written tables, `reads`/`pure`/`diverges` are no form
    (ignored, like `lean_g.rs`); every other arm is an explicit
    error. -/
structure UEffekte where
  sperren : List String
  schreibt : List String

def uEffekteAux (kopf : UFnKopf) (tabs : List UTab) (locks : List ULock) :
    List SEffekt → Except String UEffekte
  | [] => .ok { sperren := [], schreibt := [] }
  | .sperrt false (.variable l) :: rest =>
    match locks.find? (fun x => strEq x.name l) with
    | .none => .error ("Sperre unbekannt: " ++ l)
    | .some _ =>
      match uEffekteAux kopf tabs locks rest with
      | .error e => .error e
      | .ok r => .ok { r with sperren := l :: r.sperren }
  | .schreibt o :: rest =>
    match uSchreibtOrt kopf tabs o with
    | .error e => .error e
    | .ok t =>
      match uEffekteAux kopf tabs locks rest with
      | .error e => .error e
      | .ok r => .ok { r with schreibt := t :: r.schreibt }
  | .liest _ :: rest => uEffekteAux kopf tabs locks rest
  | .rein :: rest => uEffekteAux kopf tabs locks rest
  | .weichtAb :: rest => uEffekteAux kopf tabs locks rest
  | _ :: _ => .error "Effekt ohne G-Form"

def uEffekte (kopf : UFnKopf) (tabs : List UTab) (locks : List ULock) :
    List SKlausel → Except String UEffekte
  | ks =>
    let es := uWirkungen ks
    if es.isEmpty && !(uHatWirkung ks) then .error "Funktion ohne effects"
    else uEffekteAux kopf tabs locks es
where
  uWirkungen : List SKlausel → List SEffekt
    | [] => []
    | .wirkung es :: rest => es ++ uWirkungen rest
    | _ :: rest => uWirkungen rest
  uHatWirkung : List SKlausel → Bool
    | [] => false
    | .wirkung _ :: _ => true
    | _ :: rest => uHatWirkung rest

/-- Clauses without G counterpart (the refused row of
    `check_fn`): the `or` channel, `refines`, `maintains`,
    `deadline`, `decreases`, `by`, `arch`, `advances`,
    `retires`. `costs`, `section` and `payload` travel nowhere
    and are ignored, like in `lean_g.rs`. -/
def uOhneKlauselForm : List SKlausel → Except String Unit
  | [] => .ok ()
  | .verfeinert _ :: _ => .error "Klausel ohne G-Form"
  | .erhaelt _ :: _ => .error "Klausel ohne G-Form"
  | .frist _ :: _ => .error "Klausel ohne G-Form"
  | .faellt _ :: _ => .error "Klausel ohne G-Form"
  | .induktion _ :: _ => .error "Klausel ohne G-Form"
  | .rechenart _ :: _ => .error "Klausel ohne G-Form"
  | .schreitetVor _ _ :: _ => .error "Klausel ohne G-Form"
  | .ziehtZurueck _ :: _ => .error "Klausel ohne G-Form"
  | _ :: rest => uOhneKlauselForm rest

/-- Deduplicate while keeping order (the `seen` loop of
    `check_fn`). -/
def uEindeutigAux : List String → List String → List String
  | [], _ => []
  | x :: rest, seen =>
    if seen.any (strEq · x) then uEindeutigAux rest seen
    else x :: uEindeutigAux rest (x :: seen)

def uEindeutig (xs : List String) : List String :=
  uEindeutigAux xs []

/-- Pass one: the head of an `impl` function (non-`impl`,
    bodiless and clause-carrying forms are explicit errors).
    Returns the head and the written tables. -/
def elabKopf (_consts : List (String × Int))
    (aliase : List (String × (Int × Int))) (tabs : List UTab)
    (locks : List ULock) : FnSig → Except String (UFnKopf × List String)
  | { art, name, params, ergebnis, fehler := .none, klauseln } =>
    if !strEq art "impl" then .error "Funktion nicht impl"
    else
      match uOhneKlauselForm klauseln with
      | .error e => .error e
      | .ok _ =>
        match uSeq (params.map (uParam aliase tabs)) with
        | .error e => .error e
        | .ok ps =>
          let pnamen := ps.map (·.1)
          let ptypen := ps.map (·.2.1)
          let parten := ps.map (·.2.2)
          match uGehalten locks klauseln with
          | .error e => .error e
          | .ok gehalten =>
            let kopf : UFnKopf :=
              { name, pnamen, parten, ptypen, ergebnis := .none,
                gehalten := uEindeutig gehalten }
            match uEffekte kopf tabs locks klauseln with
            | .error e => .error e
            | .ok eff =>
              if !(eff.sperren.all (fun l =>
                kopf.gehalten.any (strEq · l))) then
                .error "locks ohne requires Held ohne G-Form"
              else
                let schreibt := uEindeutig eff.schreibt
                match ergebnis with
                | .none => .ok (kopf, schreibt)
                | .some t =>
                  match uErgBereich aliase t with
                  | .error e => .error e
                  | .ok r =>
                    .ok ({ kopf with ergebnis := .some r }, schreibt)
  | _ => .error "Funktion mit or-Kanal ohne G-Form"

/-- One call argument against the callee's parameter kind (the
    `tr_arg` of `lean_g.rs`): a pointer variable through, a
    fresh pointer where the rights differ, an index literal or
    parameter, a value otherwise. -/
def uArg (ctx : UCtx) (tabs : List UTab) : UParamArt → SExpr →
    Except String UArg
  | .ptr num w, .variable p =>
    match uParamNr ctx p with
    | .error e => .error e
    | .ok j =>
      match uArtBei ctx.parten j with
      | .ok (.ptr num2 w2) =>
        if num == num2 then
          if w == w2 then .ok (.var p)
          else
            match tabs[num]? with
            | .some tb => .ok (.freshPtr tb.name w)
            | .none => .error "Zeigertabelle unbekannt"
        else .error "Argument fremder Tabelle"
      | _ => .error "Zeigerargument ohne G-Form"
  | .index num, a =>
    match tabs[num]? with
    | .none => .error "Indextabelle unbekannt"
    | .some tb =>
      match uIndex ctx tb.name num a with
      | .error e => .error e
      | .ok (.lit v) => .ok (.wert (.lit v))
      | .ok (.param p) => .ok (.wert (.param p))
  | .int, a =>
    match uWertBody ctx a with
    | .error e => .error e
    | .ok s => .ok (.wert s)
  | _, _ => .error "Argument ohne G-Form"

def uArgs (ctx : UCtx) (tabs : List UTab) : List UParamArt → List SExpr →
    Except String (List UArg)
  | [], [] => .ok []
  | k :: ks, a :: rest =>
    match uArg ctx tabs k a with
    | .error e => .error e
    | .ok x =>
      match uArgs ctx tabs ks rest with
      | .error e => .error e
      | .ok xs => .ok (x :: xs)
  | _, _ => .error "Argumentzahl ohne G-Form"

/-- One body statement: an assignment or a direct call (the
    `tr_stmt` of `lean_g.rs`; compound assignment, mid-body
    `return` and every other statement are explicit errors). -/
def uAnw (ctx : UCtx) (tabs : List UTab) (koepfe : List UFnKopf) :
    SAnw → Except String UStmt
  | .zuweis ziel "=" wert =>
    match uZugriff ctx ziel with
    | .error e => .error e
    | .ok (.durch b, _, f, ix) =>
      match uStelle ctx.pnamen b with
      | .error e => .error e
      | .ok j =>
        match uArtBei ctx.parten j with
        | .ok (.ptr _ true) =>
          match uWertBody ctx wert with
          | .error e => .error e
          | .ok v => .ok (.assign b f ix v)
        | _ => .error "Schreiben durch Lesezeiger ohne G-Form"
    | .ok (.tabelle b, _, f, ix) =>
      match uWertBody ctx wert with
      | .error e => .error e
      | .ok v => .ok (.assignTab b f ix v)
  | .ruf c args =>
    match koepfe.find? (fun k => strEq k.name c) with
    | .none => .error ("Ruf unbekannt: " ++ c)
    | .some callee =>
      if !(callee.gehalten.all (fun l =>
        ctx.gehalten.any (strEq · l))) ||
         !(ctx.gehalten.all (fun l =>
        callee.gehalten.any (strEq · l))) then
        .error "Ruf ueber fremde Sperrmenge ohne G-Form"
      else
        match uArgs ctx tabs callee.parten args with
        | .error e => .error e
        | .ok xs => .ok (.call c xs)
  | _ => .error "Anweisung ohne G-Form"

/-- The trailing return (the `check_body`/`tr_body` of
    `lean_g.rs`): a result falls off nowhere, and a missing
    result returns nowhere. -/
def uEnde (ctx : UCtx) : Option SEnde → Except String URet
  | .none =>
    match ctx.ergebnis with
    | .some _ => .error "Funktion mit Ergebnis faellt durch"
    | .none => .ok .keine
  | .some (.ret .none) =>
    match ctx.ergebnis with
    | .some _ => .error "Rueckgabe ohne Wert mit Ergebnis"
    | .none => .ok .keine
  | .some (.ret (.some v)) =>
    match ctx.ergebnis with
    | .none => .error "Rueckgabe mit Wert ohne Ergebnis"
    | .some _ =>
      match uWertBody ctx v with
      | .error e => .error e
      | .ok s => .ok (.wert s)
  | .some _ => .error "Blockende ohne G-Form"

/-- Pass two: contracts and body of one function. -/
def elabFn (ctx : UCtx) (koepfe : List UFnKopf) (klauseln : List SKlausel)
    (koerper : SAnw) : Except String (List UEns × List UStmt × URet) :=
  match uSeq ((klauseln.filterMap (fun
    | .sichert e => some (uSichert ctx e)
    | _ => none))) with
  | .error e => .error e
  | .ok sichert =>
    match koerper with
    | .block ss ende =>
      match uSeq (ss.map (uAnw ctx ctx.tabellen koepfe)) with
      | .error e => .error e
      | .ok saetze =>
        match uEnde ctx ende with
        | .error e => .error e
        | .ok r => .ok (sichert, saetze, r)
    | _ => .error "Funktionsrumpf ohne G-Form"

/-- The context of a function from its head. -/
def uCtxVon (tabs : List UTab) (locks : List ULock) (kopf : UFnKopf)
    (fname : String) : UCtx :=
  { pnamen := kopf.pnamen, parten := kopf.parten,
    ptypen := kopf.ptypen, tabellen := tabs, sperren := locks,
    gehalten := kopf.gehalten, ergebnis := kopf.ergebnis,
    fname }

/-- One whole function: head (pass one) plus contracts and
    body (pass two). -/
def elabUFunktion (consts : List (String × Int))
    (aliase : List (String × (Int × Int))) (tabs : List UTab)
    (locks : List ULock) (koepfe : List UFnKopf) (sig : FnSig)
    (koerper : SAnw) : Except String UFn :=
  match elabKopf consts aliase tabs locks sig with
  | .error e => .error e
  | .ok (kopf, schreibt) =>
    let ctx := uCtxVon tabs locks kopf sig.name
    match elabFn ctx koepfe sig.klauseln koerper with
    | .error e => .error e
    | .ok (sichert, saetze, r) =>
      .ok { name := sig.name,
            params := kopf.pnamen.zip kopf.ptypen,
            parten := kopf.parten,
            ergebnis := kopf.ergebnis, held := kopf.gehalten,
            schreibt, sichert, saetze, rueck := r }

/-- Items outside the fragment: everything but constants,
    type aliases, tables, locks and functions is an explicit
    error (the refused rows of `collect`). -/
def uRestFehler : List SItemTief → Except String Unit
  | [] => .ok ()
  | .konstT _ _ _ :: rest => uRestFehler rest
  | .typT _ _ _ _ _ :: rest => uRestFehler rest
  | .tabelleT _ _ _ _ _ _ :: rest => uRestFehler rest
  | .sperreT _ _ _ _ _ _ :: rest => uRestFehler rest
  | .funktionT _ _ :: rest => uRestFehler rest
  | _ :: _ => .error "Gegenstand ohne G-Form"

/-- The elaborator: a parsed surface tree to the exported
    fragment (tables, locks, `impl` functions). -/
def elabU : List SItemTief → Except String UProg
  | items =>
    let ms := uMembers items
    let consts := uConsts ms
    let aliase := uAliase ms
    match uRestFehler ms with
    | .error e => .error e
    | .ok _ =>
      let tabItems := ms.filter (fun
        | .tabelleT _ _ _ _ _ _ => true | _ => false)
      match uSeq (tabItems.map (uTabelle consts aliase)) with
      | .error e => .error e
      | .ok [] => .error "Einheit ohne Tabelle"
      | .ok tabs =>
        let lockItems := ms.filter (fun
          | .sperreT _ _ _ _ _ _ => true | _ => false)
        match uSeq (lockItems.map (uSperre tabs)) with
        | .error e => .error e
        | .ok locks =>
          let fnItems := ms.filterMap (fun
            | .funktionT sig koerper => some (sig, koerper)
            | _ => none)
          match uSeq (fnItems.map (fun (s, _) =>
            elabKopf consts aliase tabs locks s)) with
          | .error e => .error e
          | .ok [] => .error "Einheit ohne Funktion"
          | .ok kopfPaare =>
            let koepfe := kopfPaare.map (·.1)
            match uSeq (fnItems.map (fun (s, b) =>
              elabUFunktion consts aliase tabs locks koepfe s b)) with
            | .error e => .error e
            | .ok fns =>
              .ok { tabellen := tabs, sperren := locks, fns }

/-! ## Lowering: from U to the exporter's declaration universe -/

/-- The body context of `einzahlen`: its parameters. -/
abbrev UCtxEin := G104_referenz.gCtx_einzahlen

/-- The held resources of `einzahlen`. -/
abbrev ULEin := G104_referenz.gL_einzahlen

/-- The `ensures` type of `einzahlen`. -/
abbrev UEnsEin :=
  Expr G104_referenz.gD (ErgCtx (G104_referenz.gD.params G104_referenz.g_einzahlen) (G104_referenz.gD.erg G104_referenz.g_einzahlen))
    (vertragVon G104_referenz.gD G104_referenz.g_einzahlen).ende .bool

/-- The body type of `einzahlen`. -/
abbrev UKoerpEin :=
  Endblock G104_referenz.gD (vertragVon G104_referenz.gD G104_referenz.g_einzahlen) false G104_referenz.gCtx_einzahlen G104_referenz.gL_einzahlen

/-- A parameter variable of `einzahlen` by position and type
    (positions are the known signature; anything else is an
    explicit error). -/
def varNumEin : (j : Nat) → (τ : Ty) → Except String (Var UCtxEin τ)
  | 0, .ptr 0 true => .ok .hier
  | 1, .int 0 1 => .ok (.dort .hier)
  | 2, .int 0 10 => .ok (.dort (.dort .hier))
  | _, _ => .error "Parameter ohne G-Form"

/-- An index into `Konto` in `einzahlen`: the `i` parameter or
    a literal inside `count` (the `tr_index` of `lean_g.rs`,
    with the range check as an explicit error). -/
def lowerIdxEin : UIdx →
    Except String (Expr G104_referenz.gD UCtxEin ULEin (.index (G104_referenz.gD.count G104_referenz.GTab.Konto)))
  | .param "i" => .ok (Expr.var (Var.dort Var.hier))
  | .lit n =>
    if h1 : 0 ≤ n then
      if h2 : n ≤ 1 then .ok (Expr.weiter h1 h2 (Expr.lit n))
      else .error "Index ausserhalb count"
    else .error "Index ausserhalb count"
  | _ => .error "Index ohne G-Form"

/-- The field range recorded for (`Konto`, `stand`) must be
    the exporter's `(0, 100)`; otherwise the G term below
    would ascribe the wrong type silently. -/
def uFeldWeite (tabs : List UTab) (t f : String) (lo hi : Int) :
    Except String Unit :=
  match tabs.find? (fun x => strEq x.name t) with
  | .none => .error ("Tabelle unbekannt: " ++ t)
  | .some tb =>
    match tb.felder.find? (fun (g, _) => strEq g f) with
    | .none => .error "Feld unbekannt"
    | .some (_, (a, b)) =>
      if a == lo && b == hi then .ok () else .error "Feldweite fremd"
/-- One side in `einzahlen`, with its range (the `tr_side` of
    `lean_g.rs`; a pointer parameter in a comparison is an
    explicit error). -/
structure USeiteT where
  weit : Int × Int
  term : Expr G104_referenz.gD UCtxEin ULEin (.int weit.1 weit.2)

def lowerSeiteEin (tabs : List UTab) (pnamen : List String)
    (ptypen : List Ty) : USide → Except String USeiteT
  | .lit n => .ok { weit := (n, n), term := Expr.lit n }
  | .param p =>
    match uStelle ["k", "i", "b"] p with
    | .error e => .error e
    | .ok j =>
      match pnamen[j]?, ptypen[j]? with
      | .some q, .some (Ty.int lo hi) =>
        if !strEq q p then .error "Parameter verdreht"
        else
          match varNumEin j (.int lo hi) with
          | .error e => .error e
          | .ok v => .ok { weit := (lo, hi), term := Expr.var v }
      | _, _ => .error "Parameter ohne G-Form"
  | .slot b f ix =>
    if !(strEq b "k" && strEq f "stand") then .error "Platz ohne G-Form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxEin ix with
        | .error e => .error e
        | .ok i =>
          .ok { weit := (0, 100),
                term := Expr.durch (Expr.var Var.hier)
                  G104_referenz.GTab.Konto rfl
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_einzahlen_Konto }
  | .tab b f ix =>
    if !(strEq b "Konto" && strEq f "stand") then .error "Platz ohne G-Form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxEin ix with
        | .error e => .error e
        | .ok i =>
          .ok { weit := (0, 100),
                term := Expr.slot G104_referenz.GTab.Konto
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_einzahlen_Konto }
  | .alt b f ix =>
    if !((strEq b "k" || strEq b "Konto") && strEq f "stand") then
      .error "Platz ohne G-Form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxEin ix with
        | .error e => .error e
        | .ok i =>
          .ok { weit := (0, 100),
                term := Expr.altSlot G104_referenz.GTab.Konto
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_einzahlen_Konto }
  | .erg => .error "result im Rumpf ohne G-Form"
/-- One comparison in `einzahlen` (the `tr_cmp` of `lean_g.rs`;
    G folds all but `lt`/`le`/`eq`). -/
def lowerVglEin (tabs : List UTab) (pnamen : List String)
    (ptypen : List Ty) : String → USide → USide → Except String UEnsEin
  | op, a, b =>
    match lowerSeiteEin tabs pnamen ptypen a with
    | .error e => .error e
    | .ok s1 =>
      match lowerSeiteEin tabs pnamen ptypen b with
      | .error e => .error e
      | .ok s2 =>
        match op with
        | "==" => .ok (Expr.eq s1.term s2.term)
        | "!=" => .ok (Expr.nicht (Expr.eq s1.term s2.term))
        | "<" => .ok (Expr.lt s1.term s2.term)
        | "<=" => .ok (Expr.le s1.term s2.term)
        | ">" => .ok (Expr.lt s2.term s1.term)
        | ">=" => .ok (Expr.le s2.term s1.term)
        | _ => .error "Operator ohne G-Form"

/-- One `ensures` predicate in `einzahlen`. -/
def lowerSichertEin (tabs : List UTab) (pnamen : List String)
    (ptypen : List Ty) : UEns → Except String UEnsEin
  | .cmp op a b => lowerVglEin tabs pnamen ptypen op a b
  | .wahr => .ok Expr.wahr
  | .falsch => .ok Expr.falsch
  | .und a b =>
    match lowerSichertEin tabs pnamen ptypen a with
    | .error e => .error e
    | .ok x =>
      match lowerSichertEin tabs pnamen ptypen b with
      | .error e => .error e
      | .ok y => .ok (Expr.und x y)
  | .oder a b =>
    match lowerSichertEin tabs pnamen ptypen a with
    | .error e => .error e
    | .ok x =>
      match lowerSichertEin tabs pnamen ptypen b with
      | .error e => .error e
      | .ok y => .ok (Expr.oder x y)
  | .nicht a =>
    match lowerSichertEin tabs pnamen ptypen a with
    | .error e => .error e
    | .ok x => .ok (Expr.nicht x)

/-- The `ensures` conjunction in `einzahlen` (empty is `.wahr`,
    like the exporter's conjunction). -/
def lowerSichertListeEin (tabs : List UTab) (pnamen : List String)
    (ptypen : List Ty) : List UEns → Except String UEnsEin
  | [] => .ok Expr.wahr
  | e :: rest =>
    match lowerSichertEin tabs pnamen ptypen e with
    | .error err => .error err
    | .ok x =>
      match lowerSichertListeEin tabs pnamen ptypen rest with
      | .error err => .error err
      | .ok y =>
        match y with
        | Expr.wahr => .ok x
        | _ => .ok (Expr.und x y)

/-- A value at an expected range in `einzahlen` (the
    `tr_value`/`fit` of `lean_g.rs`: literals widen with their
    proofs from the data, parameters widen from their recorded
    range, slot reads widen from the field range). -/
def lowerWertEin (tabs : List UTab) (pnamen : List String)
    (ptypen : List Ty) (lo hi : Int) : USide →
    Except String (Expr G104_referenz.gD UCtxEin ULEin (.int lo hi))
  | .lit n =>
    if h1 : lo ≤ n then
      if h2 : n ≤ hi then .ok (Expr.weiter h1 h2 (Expr.lit n))
      else .error "Literal ausserhalb"
    else .error "Literal ausserhalb"
  | .param p =>
    match uStelle ["k", "i", "b"] p with
    | .error e => .error e
    | .ok j =>
      match pnamen[j]?, ptypen[j]? with
      | .some q, .some (Ty.int a b) =>
        if !strEq q p then .error "Parameter verdreht"
        else
          match varNumEin j (.int a b) with
          | .error e => .error e
          | .ok v =>
            if h1 : lo ≤ a then
              if h2 : b ≤ hi then .ok (Expr.weiter h1 h2 (Expr.var v))
              else .error "Parameter ausserhalb"
            else .error "Parameter ausserhalb"
      | _, _ => .error "Parameter ohne G-Form"
  | s =>
    match lowerSeiteEin tabs pnamen ptypen s with
    | .error e => .error e
    | .ok t =>
      if h1 : lo ≤ t.weit.1 then
        if h2 : t.weit.2 ≤ hi then .ok (Expr.weiter h1 h2 t.term)
        else .error "Wert ausserhalb"
      else .error "Wert ausserhalb"

/-- The statement type of `einzahlen` (all straight-line steps
    keep the held resources). -/
abbrev UStmtEin :=
  Stmt G104_referenz.gD (vertragVon G104_referenz.gD G104_referenz.g_einzahlen) false UCtxEin ULEin ULEin

/-- A slot write in `einzahlen` (the assignment arm of
    `tr_stmt`; through a pointer it needs the `rw` right). -/
def lowerAssignEin (tabs : List UTab) (pnamen : List String)
    (ptypen : List Ty) : String → String → UIdx → USide →
    Except String UStmtEin
  | b, f, ix, v =>
    if !((strEq b "k" || strEq b "Konto") && strEq f "stand") then
      .error "Schreibplatz ohne G-Form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerWertEin tabs pnamen ptypen 0 100 v with
        | .error e => .error e
        | .ok w =>
          match lowerIdxEin ix with
          | .error e => .error e
          | .ok i =>
            if strEq b "k" then
              .ok (Stmt.assignDurch (Expr.var Var.hier)
                G104_referenz.GTab.Konto rfl
                G104_referenz.GKontoFeld.stand i w (by decide)
                G104_referenz.gDarf_einzahlen_Konto)
            else
              .ok (Stmt.assignSlot G104_referenz.GTab.Konto
                G104_referenz.GKontoFeld.stand i w
                (by decide) G104_referenz.gDarf_einzahlen_Konto)

/-- The arguments of a `lies` call in `einzahlen`: the fresh
    `rw`-to-`r` pointer and the index (the `tr_arg` of
    `lean_g.rs` for this pair; any other shape is an explicit
    error). -/
def lowerArgsLies (tabs : List UTab) (pnamen : List String)
    (ptypen : List Ty) : List UArg →
    Except String (Args G104_referenz.gD UCtxEin ULEin (G104_referenz.gD.params G104_referenz.g_lies))
  | [.freshPtr "Konto" false, .wert (.param "i")] =>
    match pnamen[1]?, ptypen[1]? with
    | .some q, .some (Ty.int 0 1) =>
      if !strEq q "i" then .error "Argument verdreht"
      else
        match tabs.find? (fun x => strEq x.name "Konto") with
        | .none => .error "Tabelle unbekannt: Konto"
        | .some tb =>
          if tb.count != 2 then .error "Anzahl fremd"
          else
            .ok (Args.cons (Expr.ptrOf G104_referenz.GTab.Konto 0 rfl false)
              (Args.cons (Expr.var (Var.dort Var.hier)) Args.nil))
    | _, _ => .error "Argument ohne G-Form"
  | _ => .error "Argument ohne G-Form"

/-- Straight-line steps after a `lies` call: assignments and
    the return only (a second call has no `RufPasst` proof in
    this lowering -- an explicit error). -/
def lowerNachLies (tabs : List UTab) (pnamen : List String)
    (ptypen : List Ty) : List UStmt → URet →
    Except String
      (Endblock G104_referenz.gD (vertragVon G104_referenz.gD G104_referenz.g_einzahlen) false UCtxEin
        (nach G104_referenz.gD G104_referenz.g_lies ULEin))
  | [], .keine => .ok (.ret .keine (List.Perm.refl _))
  | [], .wert _ => .error "Rueckgabe mit Wert ohne Ergebnis"
  | .assign b f ix v :: rest, r =>
    match lowerAssignEin tabs pnamen ptypen b f ix v with
    | .error e => .error e
    | .ok s =>
      match lowerNachLies tabs pnamen ptypen rest r with
      | .error e => .error e
      | .ok t => .ok (.cons s t)
  | .assignTab b f ix v :: rest, r =>
    match lowerAssignEin tabs pnamen ptypen b f ix v with
    | .error e => .error e
    | .ok s =>
      match lowerNachLies tabs pnamen ptypen rest r with
      | .error e => .error e
      | .ok t => .ok (.cons s t)
  | .call _ _ :: _, _ => .error "Ruf nach Ruf ohne G-Form"

/-- The body of `einzahlen`: straight-line writes, at most
    one direct `lies` call, and the trailing return (the
    `tr_body` of `lean_g.rs`). -/
def lowerSaetzeEin (tabs : List UTab) (pnamen : List String)
    (ptypen : List Ty) : List UStmt → URet → Except String UKoerpEin
  | [], .keine => .ok (.ret .keine (List.Perm.refl _))
  | [], .wert _ => .error "Rueckgabe mit Wert ohne Ergebnis"
  | .assign b f ix v :: rest, r =>
    match lowerAssignEin tabs pnamen ptypen b f ix v with
    | .error e => .error e
    | .ok s =>
      match lowerSaetzeEin tabs pnamen ptypen rest r with
      | .error e => .error e
      | .ok t => .ok (.cons s t)
  | .assignTab b f ix v :: rest, r =>
    match lowerAssignEin tabs pnamen ptypen b f ix v with
    | .error e => .error e
    | .ok s =>
      match lowerSaetzeEin tabs pnamen ptypen rest r with
      | .error e => .error e
      | .ok t => .ok (.cons s t)
  | .call "lies" args :: rest, r =>
    match lowerArgsLies tabs pnamen ptypen args with
    | .error e => .error e
    | .ok a =>
      match lowerNachLies tabs pnamen ptypen rest r with
      | .error e => .error e
      | .ok t =>
        .ok (.cons (.call G104_referenz.g_lies a G104_referenz.gHp_einzahlen_lies rfl) t)
  | .call _ _ :: _, _ => .error "Ruf ohne G-Form"

/-! ## Lowering `lies` -/

/-- The body context of `lies`: its parameters. -/
abbrev UCtxLies := G104_referenz.gCtx_lies

/-- The held resources of `lies`. -/
abbrev ULLies := G104_referenz.gL_lies

/-- The `ensures` context of `lies`: the result first. -/
abbrev UCtxEnsLies :=
  ErgCtx (G104_referenz.gD.params G104_referenz.g_lies)
    (G104_referenz.gD.erg G104_referenz.g_lies)

/-- The `ensures` type of `lies`. -/
abbrev UEnsLies :=
  Expr G104_referenz.gD UCtxEnsLies
    (vertragVon G104_referenz.gD G104_referenz.g_lies).ende .bool

/-- The body type of `lies`. -/
abbrev UKoerpLies :=
  Endblock G104_referenz.gD (vertragVon G104_referenz.gD G104_referenz.g_lies)
    false G104_referenz.gCtx_lies G104_referenz.gL_lies

/-- A parameter variable of `lies` by position and type. -/
def varNumLies : (j : Nat) → (τ : Ty) → Except String (Var UCtxLies τ)
  | 0, .ptr 0 false => .ok Var.hier
  | 1, .int 0 1 => .ok (Var.dort Var.hier)
  | _, _ => .error "Parameter ohne G-Form"

/-- A variable of the `lies` `ensures` context: the result or
    a parameter (positions are the known signature). -/
def varEnsLies : (j : Nat) → (τ : Ty) →
    Except String (Var UCtxEnsLies τ)
  | 0, .int 0 100 => .ok Var.hier
  | 1, .ptr 0 false => .ok (Var.dort Var.hier)
  | 2, .int 0 1 => .ok (Var.dort (Var.dort Var.hier))
  | _, _ => .error "Parameter ohne G-Form"

/-- One side in the `lies` body, with its range. -/
structure USeiteL where
  weit : Int × Int
  term : Expr G104_referenz.gD UCtxLies ULLies (.int weit.1 weit.2)

/-- An index into `Konto` in `lies`. -/
def lowerIdxLies : UIdx →
    Except String
      (Expr G104_referenz.gD UCtxLies ULLies
        (.index (G104_referenz.gD.count G104_referenz.GTab.Konto)))
  | .param "i" => .ok (Expr.var (Var.dort Var.hier))
  | .lit n =>
    if h1 : 0 ≤ n then
      if h2 : n ≤ 1 then .ok (Expr.weiter h1 h2 (Expr.lit n))
      else .error "Index ausserhalb count"
    else .error "Index ausserhalb count"
  | _ => .error "Index ohne G-Form"

def lowerSeiteLies (tabs : List UTab) (pnamen : List String)
    (ptypen : List Ty) : USide → Except String USeiteL
  | .lit n => .ok { weit := (n, n), term := Expr.lit n }
  | .param p =>
    match uStelle ["k", "i"] p with
    | .error e => .error e
    | .ok j =>
      match pnamen[j]?, ptypen[j]? with
      | .some q, .some (Ty.int lo hi) =>
        if !strEq q p then .error "Parameter verdreht"
        else
          match varNumLies j (.int lo hi) with
          | .error e => .error e
          | .ok v => .ok { weit := (lo, hi), term := Expr.var v }
      | _, _ => .error "Parameter ohne G-Form"
  | .slot b f ix =>
    if !(strEq b "k" && strEq f "stand") then .error "Platz ohne G-Form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxLies ix with
        | .error e => .error e
        | .ok i =>
          .ok { weit := (0, 100),
                term := Expr.durch (Expr.var Var.hier)
                  G104_referenz.GTab.Konto rfl
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_lies_Konto }
  | .tab b f ix =>
    if !(strEq b "Konto" && strEq f "stand") then .error "Platz ohne G-Form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxLies ix with
        | .error e => .error e
        | .ok i =>
          .ok { weit := (0, 100),
                term := Expr.slot G104_referenz.GTab.Konto
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_lies_Konto }
  | _ => .error "Seite im Rumpf ohne G-Form"

/-- One side in the `lies` `ensures`, with its range (`result`
    travels here; the recorded result range must be the
    exporter's `(0, 100)`). -/
structure USeiteE where
  weit : Int × Int
  term : Expr G104_referenz.gD UCtxEnsLies ULLies (.int weit.1 weit.2)

def lowerSeiteEnsLies (tabs : List UTab) (pnamen : List String)
    (ptypen : List Ty) (ergebnis : Option (Int × Int)) :
    USide → Except String USeiteE
  | .lit n => .ok { weit := (n, n), term := Expr.lit n }
  | .param p =>
    match uStelle ["k", "i"] p with
    | .error e => .error e
    | .ok j =>
      match pnamen[j]?, ptypen[j]? with
      | .some q, .some (Ty.int lo hi) =>
        if !strEq q p then .error "Parameter verdreht"
        else
          match varEnsLies (j + 1) (.int lo hi) with
          | .error e => .error e
          | .ok v => .ok { weit := (lo, hi), term := Expr.var v }
      | _, _ => .error "Parameter ohne G-Form"
  | .slot b f ix =>
    if !(strEq b "k" && strEq f "stand") then .error "Platz ohne G-Form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxEnsLies ix with
        | .error e => .error e
        | .ok i =>
          .ok { weit := (0, 100),
                term := Expr.durch (Expr.var (Var.dort Var.hier))
                  G104_referenz.GTab.Konto rfl
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_lies_Konto }
  | .tab b f ix =>
    if !(strEq b "Konto" && strEq f "stand") then .error "Platz ohne G-Form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxEnsLies ix with
        | .error e => .error e
        | .ok i =>
          .ok { weit := (0, 100),
                term := Expr.slot G104_referenz.GTab.Konto
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_lies_Konto }
  | .alt b f ix =>
    if !((strEq b "k" || strEq b "Konto") && strEq f "stand") then
      .error "Platz ohne G-Form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxEnsLies ix with
        | .error e => .error e
        | .ok i =>
          .ok { weit := (0, 100),
                term := Expr.altSlot G104_referenz.GTab.Konto
                  G104_referenz.GKontoFeld.stand i
                  G104_referenz.gDarf_lies_Konto }
  | .erg =>
    match ergebnis with
    | .some (0, 100) => .ok { weit := (0, 100), term := Expr.var Var.hier }
    | _ => .error "Ergebnisweite fremd"
where
  lowerIdxEnsLies : UIdx →
    Except String
      (Expr G104_referenz.gD UCtxEnsLies ULLies
        (.index (G104_referenz.gD.count G104_referenz.GTab.Konto)))
    | .param "i" => .ok (Expr.var (Var.dort (Var.dort Var.hier)))
    | .lit n =>
      if h1 : 0 ≤ n then
        if h2 : n ≤ 1 then .ok (Expr.weiter h1 h2 (Expr.lit n))
        else .error "Index ausserhalb count"
      else .error "Index ausserhalb count"
    | _ => .error "Index ohne G-Form"

/-- One comparison and one `ensures` predicate in `lies`. -/
def lowerVglLies (tabs : List UTab) (pnamen : List String)
    (ptypen : List Ty) (ergebnis : Option (Int × Int)) :
    String → USide → USide → Except String UEnsLies
  | op, a, b =>
    match lowerSeiteEnsLies tabs pnamen ptypen ergebnis a with
    | .error e => .error e
    | .ok s1 =>
      match lowerSeiteEnsLies tabs pnamen ptypen ergebnis b with
      | .error e => .error e
      | .ok s2 =>
        match op with
        | "==" => .ok (Expr.eq s1.term s2.term)
        | "!=" => .ok (Expr.nicht (Expr.eq s1.term s2.term))
        | "<" => .ok (Expr.lt s1.term s2.term)
        | "<=" => .ok (Expr.le s1.term s2.term)
        | ">" => .ok (Expr.lt s2.term s1.term)
        | ">=" => .ok (Expr.le s2.term s1.term)
        | _ => .error "Operator ohne G-Form"

def lowerSichertLies (tabs : List UTab) (pnamen : List String)
    (ptypen : List Ty) (ergebnis : Option (Int × Int)) :
    UEns → Except String UEnsLies
  | .cmp op a b => lowerVglLies tabs pnamen ptypen ergebnis op a b
  | .wahr => .ok Expr.wahr
  | .falsch => .ok Expr.falsch
  | .und a b =>
    match lowerSichertLies tabs pnamen ptypen ergebnis a with
    | .error e => .error e
    | .ok x =>
      match lowerSichertLies tabs pnamen ptypen ergebnis b with
      | .error e => .error e
      | .ok y => .ok (Expr.und x y)
  | .oder a b =>
    match lowerSichertLies tabs pnamen ptypen ergebnis a with
    | .error e => .error e
    | .ok x =>
      match lowerSichertLies tabs pnamen ptypen ergebnis b with
      | .error e => .error e
      | .ok y => .ok (Expr.oder x y)
  | .nicht a =>
    match lowerSichertLies tabs pnamen ptypen ergebnis a with
    | .error e => .error e
    | .ok x => .ok (Expr.nicht x)

def lowerSichertListeLies (tabs : List UTab) (pnamen : List String)
    (ptypen : List Ty) (ergebnis : Option (Int × Int)) :
    List UEns → Except String UEnsLies
  | [] => .ok Expr.wahr
  | e :: rest =>
    match lowerSichertLies tabs pnamen ptypen ergebnis e with
    | .error err => .error err
    | .ok x =>
      match lowerSichertListeLies tabs pnamen ptypen ergebnis rest with
      | .error err => .error err
      | .ok y =>
        match y with
        | Expr.wahr => .ok x
        | _ => .ok (Expr.und x y)

/-- A value at an expected range in the `lies` body. -/
def lowerWertLies (tabs : List UTab) (pnamen : List String)
    (ptypen : List Ty) (lo hi : Int) : USide →
    Except String (Expr G104_referenz.gD UCtxLies ULLies (.int lo hi))
  | .lit n =>
    if h1 : lo ≤ n then
      if h2 : n ≤ hi then .ok (Expr.weiter h1 h2 (Expr.lit n))
      else .error "Literal ausserhalb"
    else .error "Literal ausserhalb"
  | .param p =>
    match uStelle ["k", "i"] p with
    | .error e => .error e
    | .ok j =>
      match pnamen[j]?, ptypen[j]? with
      | .some q, .some (Ty.int a b) =>
        if !strEq q p then .error "Parameter verdreht"
        else
          match varNumLies j (Ty.int a b) with
          | .error e => .error e
          | .ok v =>
            if h1 : lo ≤ a then
              if h2 : b ≤ hi then .ok (Expr.weiter h1 h2 (Expr.var v))
              else .error "Parameter ausserhalb"
            else .error "Parameter ausserhalb"
      | _, _ => .error "Parameter ohne G-Form"
  | s =>
    match lowerSeiteLies tabs pnamen ptypen s with
    | .error e => .error e
    | .ok t =>
      if h1 : lo ≤ t.weit.1 then
        if h2 : t.weit.2 ≤ hi then .ok (Expr.weiter h1 h2 t.term)
        else .error "Wert ausserhalb"
      else .error "Wert ausserhalb"

/-- The body of `lies`: empty with a trailing value return
    (a read-only function; statements have no lowered proofs
    here -- an explicit error). A same-range slot read returns
    bare (the no-op arm of the exporter's `fit`); every other
    value widens. -/
def lowerSaetzeLies (tabs : List UTab) (pnamen : List String)
    (ptypen : List Ty) : List UStmt → URet → Except String UKoerpLies
  | [], .wert (.slot b f ix) =>
    if !(strEq b "k" && strEq f "stand") then
      .error "Rueckgabe ohne G-Form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxLies ix with
        | .error e => .error e
        | .ok i =>
          .ok (Endblock.ret
            (ErgExpr.wert (Expr.durch (Expr.var Var.hier)
              G104_referenz.GTab.Konto rfl
              G104_referenz.GKontoFeld.stand i
              G104_referenz.gDarf_lies_Konto))
            (List.Perm.refl _))
  | [], .wert (.tab b f ix) =>
    if !(strEq b "Konto" && strEq f "stand") then
      .error "Rueckgabe ohne G-Form"
    else
      match uFeldWeite tabs "Konto" "stand" 0 100 with
      | .error e => .error e
      | .ok _ =>
        match lowerIdxLies ix with
        | .error e => .error e
        | .ok i =>
          .ok (Endblock.ret
            (ErgExpr.wert (Expr.slot G104_referenz.GTab.Konto
              G104_referenz.GKontoFeld.stand i
              G104_referenz.gDarf_lies_Konto))
            (List.Perm.refl _))
  | [], .wert s =>
    match lowerWertLies tabs pnamen ptypen 0 100 s with
    | .error e => .error e
    | .ok v => .ok (Endblock.ret (ErgExpr.wert v) (List.Perm.refl _))
  | _, _ => .error "Lies-Rumpf ohne G-Form"

/-! ## Program assembly -/

/-- Assemble the lowered pieces to a program (same shape as
    `gP`: no contract content in `requires`, per-function
    `ensures` and bodies). -/
def uProgBaue (e1 : UEnsEin) (e2 : UEnsLies) (b1 : UKoerpEin)
    (b2 : UKoerpLies) : Programm G104_referenz.gD where
  invariante := fun i => nomatch i
  requires := fun _ => Expr.wahr
  ensures
    | G104_referenz.GFn.einzahlen => e1
    | G104_referenz.GFn.lies => e2
  rumpf
    | G104_referenz.GFn.einzahlen => b1
    | G104_referenz.GFn.lies => b2

/-- The lowered program: the two functions assembled to the
    exporter's `gP`/`gFs` (signatures stay in `gD`; the
    elaborated signature data is checked against `gD` entry by
    entry, so a divergent `UFn` is an explicit error). -/
def lowerProg : UProg →
    Except String
      (Programm G104_referenz.gD × List G104_referenz.GFn)
  | { tabellen := [tab], sperren := [lock], fns := [fe, fl] } =>
    if !(strEq tab.name "Konto" && strEq lock.name "M" &&
        strEq fe.name "einzahlen" && strEq fl.name "lies") then
      .error "Programmform ohne G-Form"
    else if !(decide (fe.params.map (·.2) =
        G104_referenz.gD.params G104_referenz.g_einzahlen)) then
      .error "Signatur einzahlen fremd"
    else if !(decide (fl.params.map (·.2) =
        G104_referenz.gD.params G104_referenz.g_lies)) then
      .error "Signatur lies fremd"
    else if !(decide (fe.ergebnis = none)) then
      .error "Ergebnis einzahlen fremd"
    else if !(decide (fl.ergebnis = some (0, 100))) then
      .error "Ergebnis lies fremd"
    else if !(fe.held == ["M"] && fl.held == ["M"]) then
      .error "Held-Menge fremd"
    else if !(fe.schreibt == ["Konto"] && fl.schreibt == []) then
      .error "Schreibmenge fremd"
    else
      let pnamenEin := fe.params.map (·.1)
      let ptypenEin := fe.params.map (·.2)
      match lowerSichertListeEin [tab] pnamenEin ptypenEin fe.sichert with
      | .error e => .error e
      | .ok e1 =>
        let pnamenLies := fl.params.map (·.1)
        let ptypenLies := fl.params.map (·.2)
        match lowerSichertListeLies [tab] pnamenLies ptypenLies
            fl.ergebnis fl.sichert with
        | .error e => .error e
        | .ok e2 =>
          match lowerSaetzeEin [tab] pnamenEin ptypenEin
              fe.saetze fe.rueck with
          | .error e => .error e
          | .ok b1 =>
            match lowerSaetzeLies [tab] pnamenLies ptypenLies
                fl.saetze fl.rueck with
            | .error e => .error e
            | .ok b2 =>
              .ok (uProgBaue e1 e2 b1 b2,
                [G104_referenz.GFn.einzahlen, G104_referenz.GFn.lies])
  | _ => .error "Programmform ohne G-Form"

/-! ## The 104 instance: tokens -/

/-- The token list of `beispiele/104-referenz.gab` (comment-free;
    `u104lex` checks it against the lexer). -/
def tt104 : List Token :=
  [.wort "module", .ident "beispiel", .zeichen "::", .ident "referenz",
   .zeichen "{",
   .wort "const", .ident "NKONTO", .zeichen ":", .wort "u32",
   .zeichen "=", .zahl 2, .zeichen ";",
   .wort "type", .ident "Betrag", .zeichen "=",
   .wort "u32", .wort "in", .zahl 0, .zeichen "..", .zahl 10,
   .zeichen ";",
   .wort "type", .ident "Stand", .zeichen "=",
   .wort "u32", .wort "in", .zahl 0, .zeichen "..", .zahl 100,
   .zeichen ";",
   .wort "table", .ident "Konto", .wort "count", .ident "NKONTO",
   .zeichen "{", .wort "slot", .zeichen "{", .ident "stand",
   .zeichen ":", .ident "Stand", .zeichen ",", .zeichen "}",
   .zeichen "}",
   .wort "lock", .ident "M", .wort "protects", .zeichen "{",
   .ident "stand", .zeichen "}", .wort "rank", .zahl 0,
   .wort "held", .zeichen "<=", .zahl 50, .wort "ops", .zeichen ";",
   .wort "impl", .wort "fn", .ident "einzahlen", .zeichen "(",
   .ident "k", .zeichen ":", .wort "ptr", .zeichen "<",
   .wort "normal", .zeichen ",", .wort "rw", .zeichen ">",
   .ident "Konto", .zeichen ",",
   .ident "i", .zeichen ":", .wort "index", .wort "into",
   .ident "Konto", .zeichen ",",
   .ident "b", .zeichen ":", .ident "Betrag", .zeichen ")",
   .wort "requires", .ident "Held", .zeichen "(", .ident "M",
   .zeichen ")",
   .wort "ensures", .wort "old", .zeichen "(", .ident "k",
   .zeichen ".", .wort "slots", .zeichen "[", .ident "i",
   .zeichen "]", .zeichen ".", .ident "stand", .zeichen ")",
   .zeichen "<=", .ident "k", .zeichen ".", .wort "slots",
   .zeichen "[", .ident "i", .zeichen "]", .zeichen ".",
   .ident "stand",
   .wort "effects", .zeichen "{", .wort "reads", .ident "k",
   .zeichen ".", .wort "slots", .zeichen ",", .wort "writes",
   .ident "k", .zeichen ".", .wort "slots", .zeichen ",",
   .wort "locks", .ident "M", .zeichen "}",
   .wort "costs", .zeichen "<=", .zahl 16, .wort "ops",
   .zeichen "{", .ident "k", .zeichen ".", .wort "slots",
   .zeichen "[", .ident "i", .zeichen "]", .zeichen ".",
   .ident "stand", .zeichen "=", .zahl 100, .zeichen ";",
   .ident "lies", .zeichen "(", .ident "k", .zeichen ",",
   .ident "i", .zeichen ")", .zeichen ";", .zeichen "}",
   .wort "impl", .wort "fn", .ident "lies", .zeichen "(",
   .ident "k", .zeichen ":", .wort "ptr", .zeichen "<",
   .wort "normal", .zeichen ",", .wort "r", .zeichen ">",
   .ident "Konto", .zeichen ",",
   .ident "i", .zeichen ":", .wort "index", .wort "into",
   .ident "Konto", .zeichen ")", .zeichen "->", .ident "Stand",
   .wort "requires", .ident "Held", .zeichen "(", .ident "M",
   .zeichen ")",
   .wort "ensures", .wort "result", .zeichen "==", .ident "k",
   .zeichen ".", .wort "slots", .zeichen "[", .ident "i",
   .zeichen "]", .zeichen ".", .ident "stand",
   .wort "effects", .zeichen "{", .wort "reads", .ident "k",
   .zeichen ".", .wort "slots", .zeichen ",", .wort "locks",
   .ident "M", .zeichen "}",
   .wort "costs", .zeichen "<=", .zahl 8, .wort "ops",
   .zeichen "{", .wort "return", .ident "k", .zeichen ".",
   .wort "slots", .zeichen "[", .ident "i", .zeichen "]",
   .zeichen ".", .ident "stand", .zeichen ";", .zeichen "}",
   .zeichen "}", .ende]

/-- The comment-free 104 source text, pinned as CHARACTERS in short
    pieces. One 669-byte `String` literal costs the kernel 8,96 GB and
    55 s here (measured 2026-09-15); the pieces cost a fraction of it, and
    `lex_ofList` carries the pin to the `String` without running Lean 4.33's
    UTF-8 decoder at all. See O13 and `Parser/Lexer.lean`. -/
def srcZeilen104K : List (List Char) :=
  ["module beispiel::referenz { const NKONTO ".toList,
   ": u32 = 2; type Betrag = u32 in 0 .. 10; ".toList,
   "type Stand = u32 in 0 .. 100; table ".toList,
   "Konto count NKONTO { slot { stand : ".toList,
   "Stand, } } lock M protects { stand } ".toList,
   "rank 0 held <= 50 ops; impl fn ".toList,
   "einzahlen(k : ptr<normal, rw> Konto, i : ".toList,
   "index into Konto, b : Betrag) requires ".toList,
   "Held(M) ensures old(k.slots[i].stand) <= ".toList,
   "k.slots[i].stand effects { reads ".toList,
   "k.slots, writes k.slots, locks M } costs ".toList,
   "<= 16 ops { k.slots[i].stand = 100; ".toList,
   "lies(k, i); } impl fn lies(k : ".toList,
   "ptr<normal, r> Konto, i : index into ".toList,
   "Konto) -> Stand requires Held(M) ensures ".toList,
   "result == k.slots[i].stand effects { ".toList,
   "reads k.slots, locks M } costs <= 8 ops ".toList,
   "{ return k.slots[i].stand; } }".toList]

/-- The same text as characters. -/
def srcQuelle104K : List Char := srcZeilen104K.flatten

set_option maxHeartbeats 3200000 in
/-- The comment-free 104 text lexes to `tt104`, over the characters. -/
theorem u104lexL : lexL srcQuelle104K = .ok tt104 := by
  decide

/-- The same, about the `String` -- a rewrite, not a reduction (O13). -/
theorem u104lex : lex (String.ofList srcQuelle104K) = .ok tt104 := by
  rw [lex_ofList]
  exact u104lexL

/-! ## The 104 instance: parse tree -/

/-- The slot read `k.slots[i].stand` shared by every 104
    contract and body (see `sonde04`/`sonde05`). -/
def uStand104 : SExpr :=
  .feld (.index (.feld (.variable "k") "slots") (.variable "i")) "stand"

/-- The parsed surface tree of `beispiele/104-referenz.gab`
    (`u104parse` checks it against the reader). -/
def items104 : List SItemTief :=
  [.modulT "beispiel::referenz" [
    .konstT "NKONTO" (.atom "u32") (.einzeln (.lit 2)),
    .typT [] "Betrag" [] []
      (.some (.bereich (.atom "u32") (.lit 0) (.lit 10) false)),
    .typT [] "Stand" [] []
      (.some (.bereich (.atom "u32") (.lit 0) (.lit 100) false)),
    .tabelleT "Konto" (.some (.variable "NKONTO")) .none .none false
      [.tPlatz [{ fname := "stand", ftyp := .atom "Stand",
                  pos := .none, bezug := .none, wo := .none,
                  reserviert := false, byOps := false }]],
    .sperreT "M" [.variable "stand"] (.lit 0)
      (.some (.lit 50)) .none .none,
    .funktionT
      { art := "impl", name := "einzahlen",
        params := [("k", .ptr "normal" "rw" (.atom "Konto")),
          ("i", .index false "Konto"), ("b", .atom "Betrag")],
        ergebnis := .none, fehler := .none,
        klauseln := [.voraus (.ruf "Held" [.variable "M"]),
          .sichert (.bin "<=" (.alt uStand104) uStand104),
          .wirkung [.liest (.feld (.variable "k") "slots"),
            .schreibt (.feld (.variable "k") "slots"),
            .sperrt false (.variable "M")],
          .kosten (.lit 16)] }
      (.block [.zuweis uStand104 "=" (.lit 100),
        .ruf "lies" [.variable "k", .variable "i"]] .none),
    .funktionT
      { art := "impl", name := "lies",
        params := [("k", .ptr "normal" "r" (.atom "Konto")),
          ("i", .index false "Konto")],
        ergebnis := .some (.atom "Stand"), fehler := .none,
        klauseln := [.voraus (.ruf "Held" [.variable "M"]),
          .sichert (.bin "==" .ergebnis uStand104),
          .wirkung [.liest (.feld (.variable "k") "slots"),
            .sperrt false (.variable "M")],
          .kosten (.lit 8)] }
      (.block [] (.some (.ret (.some uStand104))))]]

theorem u104parse : beqTopTief (parseTopTief tt104) (.ok items104) = true := by
  decide

/-! ## The 104 instance: elaboration -/

/-- The elaborated 104 program (`u104elab` checks it against
    the elaborator). -/
def uExp104 : UProg :=
  { tabellen := [{ name := "Konto", count := 2,
                   felder := [("stand", (0, 100))] }],
    sperren := [{ name := "M", rank := 0, schutz := ["Konto"] }],
    fns := [
      { name := "einzahlen",
        params := [("k", .ptr 0 true), ("i", .index 2),
          ("b", .int 0 10)],
        parten := [.ptr 0 true, .index 0, .int],
        ergebnis := .none,
        held := ["M"], schreibt := ["Konto"],
        sichert := [.cmp "<="
          (.alt "k" "stand" (.param "i"))
          (.slot "k" "stand" (.param "i"))],
        saetze := [.assign "k" "stand" (.param "i") (.lit 100),
          .call "lies" [.freshPtr "Konto" false,
            .wert (.param "i")]],
        rueck := .keine },
      { name := "lies",
        params := [("k", .ptr 0 false), ("i", .index 2)],
        parten := [.ptr 0 false, .index 0],
        ergebnis := .some (0, 100),
        held := ["M"], schreibt := [],
        sichert := [.cmp "==" .erg
          (.slot "k" "stand" (.param "i"))],
        saetze := [],
        rueck := .wert (.slot "k" "stand" (.param "i")) }] }

/-! ## Shape equality on U (Bool pins, like `beqTopTief`) -/

def beqIntPair : Int × Int → Int × Int → Bool
  | (a, b), (c, d) => a == c && b == d

def beqOptIntPair : Option (Int × Int) → Option (Int × Int) → Bool
  | none, none => true
  | some a, some b => beqIntPair a b
  | _, _ => false

def beqOptIntPairList : List (Option (Int × Int)) →
    List (Option (Int × Int)) → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqOptIntPair x y && beqOptIntPairList xs ys
  | _, _ => false

/-- Shape equality on `Ty` as a `Bool` (kernel evaluation,
    no nested `decide`). -/
def beqTy : Ty → Ty → Bool
  | .int a b, .int c d => a == c && b == d
  | .bool, .bool => true
  | .opt n, .opt m => n == m
  | .sum cs, .sum ds => beqOptIntPairList cs ds
  | .grund n, .grund m => n == m
  | .never, .never => true
  | .fl a b, .fl c d => beqIntPair a c && beqIntPair b d
  | .fnptr n, .fnptr m => n == m
  | .ptr t w, .ptr s v => t == s && w == v
  | _, _ => false

def beqUIdx : UIdx → UIdx → Bool
  | .lit a, .lit b => a == b
  | .param a, .param b => strEq a b
  | _, _ => false

def beqUSide : USide → USide → Bool
  | .lit a, .lit b => a == b
  | .param a, .param b => strEq a b
  | .slot a f x, .slot b g y =>
    strEq a b && strEq f g && beqUIdx x y
  | .tab a f x, .tab b g y =>
    strEq a b && strEq f g && beqUIdx x y
  | .alt a f x, .alt b g y =>
    strEq a b && strEq f g && beqUIdx x y
  | .erg, .erg => true
  | _, _ => false

def beqUEns : UEns → UEns → Bool
  | .cmp o a b, .cmp p c d =>
    strEq o p && beqUSide a c && beqUSide b d
  | .wahr, .wahr => true
  | .falsch, .falsch => true
  | .und a b, .und c d => beqUEns a c && beqUEns b d
  | .oder a b, .oder c d => beqUEns a c && beqUEns b d
  | .nicht a, .nicht b => beqUEns a b
  | _, _ => false

def beqUEnsList : List UEns → List UEns → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqUEns x y && beqUEnsList xs ys
  | _, _ => false

def beqUArg : UArg → UArg → Bool
  | .var a, .var b => strEq a b
  | .freshPtr a w, .freshPtr b v => strEq a b && w == v
  | .wert a, .wert b => beqUSide a b
  | _, _ => false

def beqUArgList : List UArg → List UArg → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqUArg x y && beqUArgList xs ys
  | _, _ => false

def beqUStmt : UStmt → UStmt → Bool
  | .assign a f x s, .assign b g y t =>
    strEq a b && strEq f g && beqUIdx x y && beqUSide s t
  | .assignTab a f x s, .assignTab b g y t =>
    strEq a b && strEq f g && beqUIdx x y && beqUSide s t
  | .call a xs, .call b ys => strEq a b && beqUArgList xs ys
  | _, _ => false

def beqUStmtList : List UStmt → List UStmt → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqUStmt x y && beqUStmtList xs ys
  | _, _ => false

def beqURet : URet → URet → Bool
  | .keine, .keine => true
  | .wert a, .wert b => beqUSide a b
  | _, _ => false

def beqUParamArt : UParamArt → UParamArt → Bool
  | .ptr a w, .ptr b v => a == b && w == v
  | .index a, .index b => a == b
  | .int, .int => true
  | _, _ => false

def beqUParamArtList : List UParamArt → List UParamArt → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqUParamArt x y && beqUParamArtList xs ys
  | _, _ => false

def beqTyParam : String × Ty → String × Ty → Bool
  | (a, x), (b, y) => strEq a b && beqTy x y

def beqTyParamList : List (String × Ty) → List (String × Ty) → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqTyParam x y && beqTyParamList xs ys
  | _, _ => false

def beqFeld : String × (Int × Int) → String × (Int × Int) → Bool
  | (a, x), (b, y) => strEq a b && beqIntPair x y

def beqFeldList : List (String × (Int × Int)) →
    List (String × (Int × Int)) → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqFeld x y && beqFeldList xs ys
  | _, _ => false

def beqStrList : List String → List String → Bool
  | [], [] => true
  | x :: xs, y :: ys => strEq x y && beqStrList xs ys
  | _, _ => false

def beqOptWeite : Option (Int × Int) → Option (Int × Int) → Bool
  | none, none => true
  | some a, some b => beqIntPair a b
  | _, _ => false

def beqUTab : UTab → UTab → Bool
  | a, b => strEq a.name b.name && a.count == b.count &&
    beqFeldList a.felder b.felder

def beqUTabList : List UTab → List UTab → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqUTab x y && beqUTabList xs ys
  | _, _ => false

def beqULock : ULock → ULock → Bool
  | a, b => strEq a.name b.name && a.rank == b.rank &&
    beqStrList a.schutz b.schutz

def beqULockList : List ULock → List ULock → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqULock x y && beqULockList xs ys
  | _, _ => false

def beqUFn : UFn → UFn → Bool
  | a, b => strEq a.name b.name &&
    beqTyParamList a.params b.params &&
    beqUParamArtList a.parten b.parten &&
    beqOptWeite a.ergebnis b.ergebnis &&
    beqStrList a.held b.held && beqStrList a.schreibt b.schreibt &&
    beqUEnsList a.sichert b.sichert &&
    beqUStmtList a.saetze b.saetze && beqURet a.rueck b.rueck

def beqUFnList : List UFn → List UFn → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqUFn x y && beqUFnList xs ys
  | _, _ => false

def beqUProg : UProg → UProg → Bool
  | a, b => beqUTabList a.tabellen b.tabellen &&
    beqULockList a.sperren b.sperren && beqUFnList a.fns b.fns

/-- Shape equality on elaboration outcomes, as a `Bool`. -/
def beqElabU : Except String UProg → Except String UProg → Bool
  | .ok a, .ok b => beqUProg a b
  | .error e1, .error e2 => e1 == e2
  | _, _ => false

theorem u104elab : beqElabU (elabU items104) (.ok uExp104) = true := by
  decide

/-! ## The 104 instance: lowering pin, data, checks -/

/-- The lowered 104 program is the exporter's `gP`/`gFs`
    (definitional: proof irrelevance covers the proof terms). -/
theorem u104lower :
    lowerProg uExp104 =
      .ok (G104_referenz.gP, G104_referenz.gFs) := rfl

/-- Projections of the elaborated program (the left column of
    the data agreement below). -/
def uAnzahl104 (u : UProg) : Int :=
  match u.tabellen with
  | [t] => t.count
  | _ => -1

def uWeite104 (u : UProg) : Int × Int :=
  match u.tabellen with
  | [{ name := _, count := _, felder := [(_, w)] }] => w
  | _ => (-1, -1)

def uRang104 (u : UProg) : Int :=
  match u.sperren with
  | [l] => l.rank
  | _ => -1

def uFn104 (u : UProg) (n : String) : Option UFn :=
  u.fns.find? (fun f => strEq f.name n)

def uParams104 (u : UProg) (n : String) : List Ty :=
  match uFn104 u n with
  | .some f => f.params.map (·.2)
  | .none => []

def uHeld104 (u : UProg) (n : String) : List String :=
  match uFn104 u n with
  | .some f => f.held
  | .none => []

def uSchreibt104 (u : UProg) (n : String) : List String :=
  match uFn104 u n with
  | .some f => f.schreibt
  | .none => []

/-- Declaration data agreement, construct by construct: the
    elaborated data agrees with the exporter's `gD` (via
    `u104lower`) and with the hand translation's `r4D` -- same
    shape as `export104_data`. -/
theorem u104data :
    uAnzahl104 uExp104 = 2 ∧
    r4D.count () = 2 ∧
    uWeite104 uExp104 = (0, 100) ∧
    r4D.typ () () = .int 0 100 ∧
    uRang104 uExp104 = 0 ∧
    r4D.rang () = 0 ∧
    uParams104 uExp104 "einzahlen" = [.ptr 0 true, .index 2, .int 0 10] ∧
    r4D.params r4Ein = [.ptr 0 true, .index 2, .int 0 10] ∧
    uParams104 uExp104 "lies" = [.ptr 0 false, .index 2] ∧
    r4D.params r4Lies = [.ptr 0 false, .index 2] ∧
    uHeld104 uExp104 "einzahlen" = ["M"] ∧
    r4D.haelt r4Ein = [()] ∧
    uSchreibt104 uExp104 "einzahlen" = ["Konto"] ∧
    r4D.schreibt r4Ein () = true ∧
    uSchreibt104 uExp104 "lies" = [] ∧
    r4D.schreibt r4Lies () = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl⟩

/-- The fragment check on the Lean-parsed program. -/
theorem u104fragment :
    (match lowerProg uExp104 with
     | .ok (P, fs) => programmImFragmentG P fs
     | .error _ => false) = true := by
  decide

/-- The footprint check on the Lean-parsed program. -/
theorem u104fuss :
    (match lowerProg uExp104 with
     | .ok (P, fs) => fussOrtGB P fs
     | .error _ => false) = true := by
  decide

end Gabbro.Grammatik.Parser.Uebersetze

/-
  CUTS: what is not proved here, and every deliberate
  difference against `crates/gabbro-check/src/lean_g.rs`.

  1. No single whole-pipeline `decide`: `lex` + `parseTopTief`
     + `elabU` + `lowerProg` in one kernel evaluation exceeds
     the heartbeat budget (the lane-135 finding), and
     `Except String UProg` has no `DecidableEq` instance for a
     propositional pin. The loop closes in stages instead,
     each with its own kernel check: `u104lex` (source to
     tokens), `u104parse` (tokens to `items104`, a `beqTopTief`
     pin like `tEnd`), `u104elab` (surface to `uExp104`, a
     `beqElabU` pin), `u104lower` (U to `(gP, gFs)` by `rfl`,
     proof irrelevance covering the proof terms). Chaining
     them is prose, as in `Export104.lean` (whose equality
     across declaration types is not even statable).
  2. `beqTy`/`beqUIdx`/`beqUSide`/`beqUEns`/`beqUArg`/
     `beqUStmt`/`beqURet`/`beqUTab`/`beqULock`/`beqUFn`/
     `beqUProg`/`beqElabU` are not proved sound or complete
     (the same cut as `beqSItemTief` in `ElementTief.lean`).
  3. The lowering targets the exporter's declaration universe
     `G104_referenz.gD` only: any table but `Konto`, any lock
     but `M`, any field but `stand`, any function but
     `einzahlen`/`lies` is an explicit error. The surface to U
     stage (`elabU`) is generic over the fragment; the proof
     carrying lowerers (`varNumEin`, `varNumLies`,
     `varEnsLies`, the `darf`/`RufPasst` witnesses) are keyed
     to the known signatures.
  4. Lowering restrictions beyond `elabU` (each an explicit
     error): at most one call per body and none after a call
     (no second `RufPasst` proof); `lies` bodies are empty
     with a value return (a statement in a read-only function
     has no lowered guard proof here); calls only to `lies`
     from `einzahlen` (the one named `RufPasst` proof);
     the `lies` return of a same-range slot read is direct
     (the no-op arm of the exporter's `fit`), every other
     value widens through `weiter`.
  5. Against `lean_g.rs`, deliberately: bare-word types are
     refused (no full-range rule; 104 needs none); slot
     extras (`@bitpos`, `offset_into`, `where`, `reserved`,
     `by ops`) are refused where the exporter ignores some;
     `use` items and nested modules are refused; an index
     literal is range-checked against `count`. Mirrored
     exactly: the refused clause rows, the one-directional
     `locks`-without-`Held` refusal, writes deduplication,
     the `rw`-to-`r` fresh pointer, the fall-off rule, and
     ignoring `reads`/`costs`/`section`/`payload`.
  6. The `u104fragment`/`u104fuss` match form carries a
     `false` error branch; `u104lower` shows it dead for 104.
  7. Corpus text is quoted comment-free (comments lex away,
     the probe precedent); `u104lex` runs at 3200000
     heartbeats, `u104parse`/`u104elab`/`u104fragment`/
     `u104fuss` at default.
-/

#print axioms Gabbro.Grammatik.Parser.Uebersetze.u104lex
#print axioms Gabbro.Grammatik.Parser.Uebersetze.u104parse
#print axioms Gabbro.Grammatik.Parser.Uebersetze.u104elab
#print axioms Gabbro.Grammatik.Parser.Uebersetze.u104lower
#print axioms Gabbro.Grammatik.Parser.Uebersetze.u104data
#print axioms Gabbro.Grammatik.Parser.Uebersetze.u104fragment
#print axioms Gabbro.Grammatik.Parser.Uebersetze.u104fuss
