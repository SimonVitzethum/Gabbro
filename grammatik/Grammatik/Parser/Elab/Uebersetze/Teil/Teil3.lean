module

public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil2
public import Grammatik.Parser.Elab.Uebersetze.Kontext.Eigner
public import Grammatik.Parser.Elab.Uebersetze.Folds.ConstEvaluation
public import Grammatik.Parser.Elab.Uebersetze.Folds.FloatLiterals

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

/-- The constant scope of a unit: in source order, each constant may use the ones before it. A literal
    keeps the old rule (any declared type); any other expression needs a builtin-word type and the
    evaluator above. -/
def uConstsRech (fns : List UKonstFn) : List SItemTief → List (String × Int) → List (String × Int)
  | [], acc => acc
  | .constT n _ (.one (.lit v)) :: rest, acc =>
    uConstsRech fns rest (acc ++ [(n, Int.ofNat v)])
  | .constT n (.atom w) (.one e) :: rest, acc =>
    match uTypName [] w with
    | .ok (lo, hi) =>
      match uKonstWert lo hi fns acc 64 e with
      | some v => uConstsRech fns rest (acc ++ [(n, v)])
      | none => uConstsRech fns rest acc
    | .error _ => uConstsRech fns rest acc
  | _ :: rest, acc => uConstsRech fns rest acc

/-- A table by name: its number (position, what `ptr` names)
    and its slot count (what `index` names). -/
def uTabNrAux : List UTab → Nat → String → Except String (Nat × Int)
  | [], _, n => .error ("table unknown: " ++ n)
  | t :: rest, k, n =>
    if strEq t.name n then .ok (k, t.count)
    else uTabNrAux rest (k + 1) n

def uTabNr (tabs : List UTab) (n : String) : Except String (Nat × Int) :=
  uTabNrAux tabs 0 n

/-- A surface type as text, for a refusal that names what it refuses. -/
def sTypText : STyp → String
  | .atom a => a
  | .path ps => ".".intercalate ps
  | .ptr r w t => "ptr<" ++ r ++ ", " ++ w ++ "> " ++ sTypText t
  | .index o t => (if o then "option " else "") ++ "index into " ++ t
  | .range b _ _ _ => sTypText b ++ " in .."
  | .array t _ => "[" ++ sTypText t ++ "; ..]"
  | .wrap t => "wrap " ++ sTypText t
  | .embed b n _ => sTypText b ++ " embed " ++ n
  | .raw n => "raw " ++ n
  | .str _ => "string"
  | .entry n _ => "entry " ++ n
  | .dyn n _ => "dyn " ++ n

/-- Normalize the complete table access rights. Owner identities resolve
    against the unit's declared owner namespace; anything else (unknown
    components, unresolved/conflicting owners, execute rights) fails closed.
    With the empty namespace every `own` spelling is refused by name. -/
def uTableRight (eigner : List String := []) (text : String) : Except String DataRights :=
  match DataRights.decode (uEignerNr eigner) text with
  | some rights => .ok rights
  | none => .error ("pointer rights without checked data/owner form: " ++ text)

/-- Export retains the complete decoded rights: both flags and any resolved
    owner identity, never via the read/write flags alone. -/
theorem uTableRight_sound (eigner : List String) (text : String) (rights : DataRights)
    (h : uTableRight eigner text = .ok rights) :
    DataRights.decode (uEignerNr eigner) text = some rights := by
  cases hd : DataRights.decode (uEignerNr eigner) text with
  | none => simp [uTableRight, hd] at h
  | some r =>
    have he : r = rights := by simpa [uTableRight, hd] using h
    subst he; exact hd

/-- Resolve a logical space against the declaration order. Unknown names are refused. -/
def uDataSpace (spaces : List String) (name : String) : Except String Nat :=
  match spaces.zipIdx.find? (fun entry => strEq entry.1 name) with
  | some (_, index) => .ok index
  | none => .error ("unknown data space: " ++ name)

/-- A surface type as G sees it: a pointer to a table, an index
    into one, or an integer range (the `ParamTy`/`int_range` of
    `lean_g.rs`). `own@m` rights resolve against the unit's declared owner
    namespace (`eigner`); bare `own` stays refused (it is the consumes/allocs
    sugar and needs the C09 signature flow). Unknown named address spaces,
    failing rights unions, the optional index and every other shape are
    explicit errors. -/
def uTypIn (alias : List (String × (Int × Int))) (tabs : List UTab) (named : List (String × Ty)) (spaces : List String := []) (eigner : List String := []) : STyp → Except String Ty
  | .atom "bool" => .ok .bool
  | .atom "f32" | .atom "f64" => .ok uFloatTy
  | .atom a =>
    match named.find? (fun entry => strEq entry.1 a) with
    | some (_, τ) => .ok τ
    | none =>
      match uTypName alias a with
      | .ok (lo, hi) => .ok (.int lo hi)
      | .error e => .error e
  | .range base lo hi o =>
    match uTypIn alias tabs named spaces (eigner := eigner) base, uSchranke alias lo, uSchranke alias hi with
    | .ok (.int _ _), some a, some b => .ok (.int a (if o then b - 1 else b))
    | .ok (.fl ..), _, _ => do
      if o then throw "float range: exclusive upper bound has no closed G export"
      let low ← uFloatBound alias lo
      let high ← uFloatBound alias hi
      pure (.fl low high)
    | .error e, _, _ => .error e
    | _, _, _ => .error "range requires a numeric type and known bounds"
  | .index true t =>
    match uTabNr tabs t with
    | .ok (_, count) => .ok (.opt count)
    | .error error => .error error
  | .index false t =>
    match uTabNr tabs t with
    | .ok (num, c) =>
      if ((tabs[num]?).bind (·.von)).isSome then .ok (.ref num) else .ok (.index c)
    | .error e => .error e
  | .ptr raum rechte (.atom t) =>
    if strEq t "u8" then .error "live byte capability requires C01 value flow, C08 grant generations and C09 loans"
    else do
      let space ← uDataSpace spaces raum
      let rights ← uTableRight eigner rechte
      let (num, _) ← uTabNr tabs t
      pure (.ptr ⟨space, rights, .table num⟩)
  | .ptr _ _ _ => .error "live byte capability requires C01 value flow, C08 grant generations and C09 loans"
  | .entry _ _ => .error "entry handle requires C08/C14 binding and C09 forwarding flow"
  | .array t n =>
    match uTypIn alias tabs named spaces (eigner := eigner) t, uSchranke alias n with
    | .ok τ, some k => if 0 ≤ k then .ok (.arr τ k.toNat) else .error "array of a negative length"
    | .error e, _ => .error e
    | _, none => .error "array length without G form"
  | .str n =>
    match uSchranke alias n with
    | some k => if 0 ≤ k then .ok (.str k.toNat) else .error "string of a negative maximum"
    | none => .error "string maximum without G form"
  | t => .error ("type without G form: " ++ sTypText t)

/-- The canonical reader in a declaration environment without named value schemas. -/
def uTyp (alias : List (String × (Int × Int))) (tabs : List UTab) (spaces : List String := []) (eigner : List String := []) : STyp → Except String Ty :=
  uTypIn alias tabs [] spaces (eigner := eigner)

/-- Collect constant functions independently of their statement body shape. -/
def uKonstFnsWith (alias : List (String × (Int × Int))) : List SItemTief → List UKonstFn
  | [] => []
  | .fnT sig body :: rest =>
    if strEq sig.art "const" then
      match sig.res with
      | some result =>
        match uTyp alias [] result, sig.params.mapM (fun (n, ty) => (uTyp alias [] ty).map (fun t => (n, t))) with
        | .ok resultType, .ok parameters =>
          { name := sig.name, params := parameters, erg := resultType, rumpf := body, signature := sig } :: uKonstFnsWith alias rest
        | _, _ => uKonstFnsWith alias rest
      | none => uKonstFnsWith alias rest
    else uKonstFnsWith alias rest
  | _ :: rest => uKonstFnsWith alias rest

/-- Builtin-only collector retained as the canonical initial discovery pass. -/
def uKonstFns (items : List SItemTief) : List UKonstFn := uKonstFnsWith [] items

/-- A slot field type as an integer range (the field loop of
    `read_table`; `wrapping` and everything else are explicit
    errors). -/
def uFeldTyp (alias : List (String × (Int × Int))) (ty : STyp) : Except String (Int × Int) :=
  match uTyp alias [] [] [] ty with
  | .ok (.int lo hi) => .ok (lo, hi)
  | .ok _ => .error ("field type without G form: " ++ sTypText ty)
  | .error e => .error e

/-- C13: the declared STORAGE width in bits of a type as written: a builtin unsigned word (with or without a range),
    a `wrapping` field of one, or an alias of one (`uAliasBreiten`); `0` for everything else. It is the width the
    declaration chose, never the width the range of the type happens to fit. -/
def uSpeicherBreite (alias : List (String × (Int × Int))) : STyp → Nat
  | .atom a =>
    if 0 < uAtomBreite a then uAtomBreite a
    else
      match uSuch "type" alias (a ++ "#bits") with
      | .ok (w, _) => w.toNat
      | .error _ => 0
  | .range t _ _ _ => uSpeicherBreite alias t
  | .wrap t => uSpeicherBreite alias t
  | _ => 0

/-- C13: the widths of the fields of a table, for the fields of a bare unsigned word type. -/
def uFeldBreiten (alias : List (String × (Int × Int))) (fds : List SFeld) : List (String × Nat) :=
  fds.filterMap fun fd =>
    let w := uSpeicherBreite alias fd.ftyp
    if 0 < w then some (fd.fname, w) else none

mutual
/-- A constant row folded at its element type: numbers by the constant evaluator, nested rows element by element. -/
def uKonstZeile (alias : List (String × (Int × Int))) (fns : List UKonstFn) (consts : List (String × Int))
    (ty : Ty) (value : SKonstWert) (leaf : Ty → SExpr → Option USide := fun _ _ => none) : Option USide :=
  match ty, value with
  | .int lo hi, .one e => (uKonstWert lo hi fns consts 64 e).map USide.lit
  | .arr τ _, .rows ks => uKonstZeilen alias fns consts τ ks leaf
  | τ, .one e => leaf τ e
  | _, _ => none
termination_by sizeOf value
decreasing_by all_goals simp_wf; omega
def uKonstZeilen (alias : List (String × (Int × Int))) (fns : List UKonstFn) (consts : List (String × Int))
    (ty : Ty) (values : List SKonstWert) (leaf : Ty → SExpr → Option USide := fun _ _ => none) : Option USide :=
  match ty, values with
  | _, [] => some .arrNil
  | τ, k :: ks =>
    match uKonstZeile alias fns consts τ k leaf, uKonstZeilen alias fns consts τ ks leaf with
    | some a, some r => some (.arrCons a r)
    | _, _ => none
termination_by sizeOf values
decreasing_by all_goals simp_wf; omega
end

/-- Collect canonical literals at their declared type. The default selects arrays; production
    enables all values and supplies its nominal schemas and leaf adapter. Both modes use the
    same type lookup and evaluator, so no initializer has a second collection path. -/
def uKonstArrays (alias : List (String × (Int × Int))) (fns : List UKonstFn) (consts : List (String × Int))
    (ms : List SItemTief) (named : List (String × Ty) := [])
    (leaf : Ty → SExpr → Option USide := fun _ _ => none)
    (values : Bool := false) : List (String × USide) :=
  ms.filterMap fun
    | .constT n t v => if values || (match t with | .array _ _ => true | _ => false) then
      match uTypIn alias [] named [] [] t with
      | .ok τ => (uKonstZeile alias fns consts τ v leaf).map fun l => (n, .typed τ l)
      | .error _ => none
      else none
    | _ => none

/-- A count: a literal or a named constant (the `numeral` of
    `lean_g.rs`). -/
def uAnzahl (consts : List (String × Int)) : SExpr → Except String Int
  | .lit v => .ok (Int.ofNat v)
  | .variable c => uSuch "const" consts c
  | expression =>
    match uSchranke (consts.map (fun pair => (pair.1, (pair.2, pair.2)))) expression with
    | some value => if 0 ≤ value then .ok value else .error "source export: negative constant count"
    | none => .error "source export: count is not a canonical constant bound"

/-- The kind of a slot field. -/
inductive UFeldArt
  | zahl : UFeldArt
  | bool : UFeldArt
  /-- `option index into T`: the number of `T`. -/
  | opt : Nat → UFeldArt
  /-- An aggregate value (`[T; N]`, `string max N`): its type. -/
  | wert : Ty → UFeldArt
  /-- `u32 wrapping`: a number field whose writes are taken modulo `m` (SUGAR over `rem`, SYNTAX.md). -/
  | wrap : Int → UFeldArt
  /-- A field of a tagged type, its name as written (read with the types, `uSumTabs`). -/
  | summe : String → UFeldArt
  /-- `index into T`: a number in `0 ..< count T`, the name of `T` as written (its count is read with the tables). -/
  | idx : String → UFeldArt

/-- One slot field: no bit position, no `offset_into`, no `where`, no `reserved` (all without G
    form, like the refused arms of `read_table`). `by ops` is a writer discipline the CHECKER holds
    and has no meaning in the model -- the exporter reads the field as written (`lean_g.rs`) -- so it
    travels. A `bool` or option field is recorded as such (the second component). -/
def uFeld (alias : List (String × (Int × Int))) (tnames : List String) :
    SFeld → Except String ((String × (Int × Int)) × UFeldArt)
  | { fname, ftyp, pos := .none, bezug := .none, wo := .none,
      reserviert := false, byOps := _ } =>
    match ftyp with
    | .atom "bool" => .ok ((fname, (0, 1)), UFeldArt.bool)
    | .index true tn =>
      match tnames.findIdx? (fun x => strEq x tn) with
      | .some num => .ok ((fname, (0, 1)), UFeldArt.opt num)
      | .none => .error ("table unknown: " ++ tn)
    | .atom "f32" | .atom "f64" | .array _ _ | .str _ =>
      match uTyp alias [] ftyp with
      | .ok τ => .ok ((fname, (0, 0)), UFeldArt.wert τ)
      | .error e => .error e
    | .atom a =>
      match uFeldTyp alias (.atom a) with
      | .ok r => .ok ((fname, r), UFeldArt.zahl)
      | .error _ => .ok ((fname, (0, 0)), UFeldArt.summe a)
    | .index false tn =>
      if tnames.any (strEq · tn) then .ok ((fname, (0, 0)), UFeldArt.idx tn) else .error ("table unknown: " ++ tn)
    | .wrap t =>
      match uFeldTyp alias t with
      | .ok (0, hi) => .ok ((fname, (0, hi)), UFeldArt.wrap (hi + 1))
      | .ok _ => .error "wrapping field of a range that does not start at 0 without G form"
      | .error e => .error e
    | _ =>
      match uFeldTyp alias ftyp with
      | .ok r => .ok ((fname, r), UFeldArt.zahl)
      | .error e => .error e
  | _ => .error "slot field without G form"

def uFelder : List (String × (Int × Int)) → List String → List SFeld →
    Except String (List ((String × (Int × Int)) × UFeldArt))
  | _, _, [] => .error "table without fields"
  | alias, tnames, [f] => (uFeld alias tnames f).map ([·])
  | alias, tnames, f :: rest =>
    match uFeld alias tnames f, uFelder alias tnames rest with
    | .ok p, .ok ps => .ok (p :: ps)
    | .error e, _ | _, .error e => .error e

/-- A table of `count` slots with its fields, its invariants and its tree edges. -/
def uTabelleSlots (consts : List (String × Int)) (alias : List (String × (Int × Int))) (tnames : List String)
    (n : String) (cnt : SExpr) (sh : Bool) (fds : List SFeld) (invs : List STabTeil) (kanten : List (String × String)) (o : Option String := none) :
    Except String UTab :=
  if !invs.all (fun p => match p with | .tInv _ => true | _ => false) then .error "table without G form" else
  match uAnzahl consts cnt with
  | .error e => .error e
  | .ok c =>
    -- `Self` in a field type is the table itself
    let fds := fds.map fun fd => match fd.ftyp with
      | .index o t => if strEq t "Self" then { fd with ftyp := .index o n } else fd
      | _ => fd
    match uFelder alias tnames fds with
    | .error e => .error e
    | .ok fs =>
      .ok { name := n, count := c, cols := fs.map (·.1),
            bools := (fs.filter (fun p => match p.2 with | .bool => true | _ => false)).map (·.1.1),
            opts := fs.filterMap (fun p => match p.2 with | .opt num => some (p.1.1, num) | _ => none),
            werte := fs.filterMap (fun p => match p.2 with | .wert τ => some (p.1.1, τ) | _ => none),
            wraps := fs.filterMap (fun p => match p.2 with | .wrap m => some (p.1.1, m) | _ => none),
            sumNamen := fs.filterMap (fun p => match p.2 with | .summe a => some (p.1.1, a) | _ => none),
            idxNamen := fs.filterMap (fun p => match p.2 with | .idx tn => some (p.1.1, tn) | _ => none),
            kanten := kanten, shared := sh, breiten := uFeldBreiten alias fds, owner := o }

/-- One table: `count` and one integer range per slot field.
/// Invariants, `ops`, tree edges, the occupancy mark,
    a `backed`/`shared` flag and a missing slot
    are explicit errors (the refused arms of `read_table`).
    The `owner` mark travels in `UTab.owner` (`D.eigner`/`braucht`). -/
def uTabelle (consts : List (String × Int))
    (alias : List (String × (Int × Int))) (tnames : List String) : SItemTief → Except String UTab
  | .tableT n .none (.some cnt) .none o sh parts =>
    -- `tree { parent p, child c }` names the fields `reaches … via` and the tree domains read; it adds no carrier
    match parts.filter (fun p => match p with | .tTree _ => false | _ => true) with
    | .tSlot fds :: invs => uTabelleSlots consts alias tnames n cnt sh fds invs
        (parts.flatMap (fun p => match p with | .tTree ks => ks | _ => [])) o
    | _ => .error "table without G form"
  | .tableT n (.some p) .none .none o sh (.tSlot fds :: invs) =>
    if !invs.all (fun p => match p with | .tInv _ => true | _ => false) then .error "table without G form" else
    match uFelder alias tnames fds with
    | .error e => .error e
    | .ok fs =>
      if fs.all (fun p => match p.2 with | .zahl => true | _ => false) then
        .ok { name := n, count := 0, cols := fs.map (·.1), shared := sh, von := some p,
               breiten := uFeldBreiten alias fds, owner := o }
      else .error "open table with a field other than a number without G form"
  | _ => .error "table without G form"

/-- A `protects` carrier: a table name, a field of exactly one table (the guard loop of `read_lock`), or
    a static (`gbraucht`, the lock guards that static). -/
def uTraegerTab (globs : List UGlob) : List UTab → String → Except String String
  | [], c =>
    if globs.any (fun g => strEq g.name c) then .ok c
    else .error ("guard unknown: " ++ c)
  | t :: rest, c =>
    if strEq t.name c then (if t.arena then .error "arena under a lock without G form" else .ok t.name)
    else if t.cols.any (fun (f, _) => strEq f c) then .ok t.name
    else uTraegerTab globs rest c

def uSchutzAux (globs : List UGlob) : List UTab → List SExpr → Except String (List String)
  | _, [] => .ok []
  | tabs, .variable c :: rest =>
    match uTraegerTab globs tabs c with
    | .error e => .error e
    | .ok t =>
      match uSchutzAux globs tabs rest with
      | .error e => .error e
      | .ok ts => .ok (t :: ts)
  | _, _ :: _ => .error "guard carrier without G form"

/-- One lock: a numeric rank and the guarded tables. Masking
    and the shared hold have no G form; the `held` budget is
    ignored like `costs` (both travel nowhere). -/
def uSperre (globs : List UGlob) (tabs : List UTab) (item : SItemTief)
    (consts : List (String × Int) := []) : Except String ULock :=
  match item with
  | .lockT n ps expression _ .none m _ => do
    let rank ← uAnzahl consts expression
    if rank < 0 then throw "source export: negative lock rank"
    let masks ← match m with
      | .none => .ok false
      | .some w => if strEq w "irqs" then .ok true else .error "lock masks something but irqs: no G form"
    let guarded ← uSchutzAux globs tabs ps
    pure {name := n, rank, guard := guarded, masks}
  | .lockT n .. => .error ("lock without G form: " ++ n)
  | _ => .error "lock without G form"

/-- A parameter position by name (the `param_index` of
    `lean_g.rs`; unknown names are `LG005` errors). -/
def uParamNrAux : List String → Nat → String → Except String Nat
  | [], _, p => .error ("name unknown: " ++ p)
  | q :: rest, k, p =>
    if strEq q p then .ok k else uParamNrAux rest (k + 1) p

def uParamNr (ctx : UCtx) (p : String) : Except String Nat :=
  uParamNrAux ctx.names 0 p

/-- The kind of the parameter at a position. -/
def uArtBei : List UParamArt → Nat → Except String UParamArt
  | [], _ => .error "parameter outside"
  | a :: _, 0 => .ok a
  | _ :: rest, n + 1 => uArtBei rest n

/-- The open table a local reference `r` points into (`some n` for a local of kind `ref n`). -/
def uRefLokal (ctx : UCtx) (r : String) : Option Nat :=
  match uParamNr ctx r with
  | .error _ => none
  | .ok j =>
    match uArtBei ctx.kinds j with
    | .ok (.ref n) => some n
    | _ => none

/-- Every guard of the table is held (the `holds_guards` of
    `lean_g.rs`: the generation-time half of the guard
    proof). -/
def uHaeltWaechter (ctx : UCtx) (t : String) : Except String Unit :=
  let bedarf : List String :=
    ctx.locks.filterMap (fun l => if l.guard.any (strEq · t) then some l.name else none)
  if bedarf.all (fun b => ctx.held.any (strEq · b)) then .ok ()
  else .error "access without held guard"

/-- The slot count of a table by name. -/
def uAnzahlTab (tabs : List UTab) (t : String) : Except String Int :=
  match tabs.find? (fun x => strEq x.name t) with
  | .some x => .ok x.count
  | .none => .error ("table unknown: " ++ t)

/-- Two tables of the same slot count: an index into one is an index into the other (`Ty.index` is the
    count, as in the model). -/
def uGleicheAnzahl (tabs : List UTab) (m n : Nat) : Bool :=
  match tabs[m]?, tabs[n]? with
  | some a, some b => a.count == b.count
  | _, _ => false

/-- An index into a table: a literal inside `count`, or an
    index parameter for a table of the same count (the `tr_index` of
    `lean_g.rs`). -/
def uIndex (ctx : UCtx) (t : String) (num : Nat) : SExpr → Except String UIdx
  | .lit v =>
    match uAnzahlTab ctx.tabs t with
    | .error e => .error e
    | .ok c =>
      if Int.ofNat v < c then .ok (.lit (Int.ofNat v))
      else .error "index outside count"
  | .variable p =>
    match uParamNr ctx p with
    | .error e => .error e
    | .ok j =>
      match uArtBei ctx.kinds j with
      | .ok (.index m) =>
        if m == num || uGleicheAnzahl ctx.tabs m num then .ok (.param p) else .error "index of foreign table"
      | .ok .int => .ok (.param p)
      | _ => .error "index without G form"
  | _ => .error "index without G form"

/-- A slot read `p.slots[i].f` / `T.slots[i].f`: the basis
    (pointer parameter or table name), the table, the field and
    the index (the `slot_access` of `lean_g.rs`). -/
inductive UBasis
  | thru : String → UBasis
  | tabelle : String → UBasis
  deriving DecidableEq, Repr

end Gabbro.Grammatik.Parser.Uebersetze
