/-
  File:      Grammatik/CParser/CParse.lean
  Subject:   A2, PART 2: `parseC` -- the emitted C TEXT as the C unit the
             semantics of `CFormen.lean` speaks about.

  WHY. The closing theorem (`Schlusssatz.lean`, `Schlusssatz104.lean`)
  takes the C side as the elaboration of the CERTIFICATE (`kProg K.zert`).
  That the emitted TEXT means the same thing was assumption A2 -- a hand
  transcription, checked by nobody. With `parseC <the emitted text> =
  some <the certificate's functions>` decided by the kernel, A2 is gone
  for that program; what stays is "the C compiler's front end reads this
  subset as `parseC` does", which is part of A1.

  THE SUBSET, and nothing beyond it. `parseC` reads exactly the forms the
  emitted C of the CLOSED CHAINS uses (`beispiele/104`, `beispiele/108`;
  the census `instrumente/pruefe-cformen.py` names the corpus-wide forms,
  and `messung/muse/OPUS-BERICHT-CPARSER.md` tabulates both):

  * the prelude: the four `#include`s, and the TWO `_Static_assert` pins
    of PLAN-BITS §5b -- a text without both pins is refused, because the
    pins are what A3 leans on;
  * `#define NAME <integer>` and `#define NAME (<integer or macro>)`;
  * `typedef struct { <scalar fields> } T_slot;` and
    `typedef struct { T_slot slots[N]; } T;` -- the table's layout is
    COMPUTED from the declarations (`natLay`), not transcribed;
  * `static T T_speicher;` -- the named table object;
  * `void f(void);` -- a foreign declaration (the lock primitive), noted
    and never called;
  * `static <ret> f(<params>) <attrs>;` and the matching definition;
  * statements: `(void)x;`, `p->slots[i].f = e;`, `T_speicher.slots[i].f
    = e;`, `(void)f(args);`, `f(args);`, `return;`, `return e;`;
  * expressions: integer literals, locals, `p->slots[i].f`,
    `T_speicher.slots[i].f`.

  EVERYTHING ELSE IS `none`. No arithmetic (a `+` in C carries a
  computation type that only type inference gives, and a parser that
  guesses a type guesses the program), no `if`, no loops, no casts, no
  `let`, no atomics, no volatile, no asm. The refusals are the point: the
  pin below could otherwise be satisfied by a parser that accepts
  anything.

  NUMBERING, and where it comes from. C function numbers are assigned in
  the order of the first `static` declaration; C locals are the
  parameters, numbered left to right from `0`; table blocks are numbered
  in the order of the table typedefs. That is the exporter's own map
  (`KorrespondenzAllg.lean`: "Gabbro variable `j` is C local `vm[j]`"),
  and for a chain program the pin CHECKS it: a different numbering makes
  the equality with the certificate's functions false.
-/
import Grammatik.CParser.CLexer
import Grammatik.CFormen

namespace Gabbro.Grammatik.CParser

open Gabbro.Grammatik

/-! ## 1. The names the subset knows -/

/-- The C scalar type of a type name. `bool` is `uint8_t`
    (`CSpeicher.lean` §1: the cell types of lane 128). -/
def cTypName (s : List Char) : Option CTy :=
  if lcEq s "uint8_t".toList then some (.int false .w8)
  else if lcEq s "uint16_t".toList then some (.int false .w16)
  else if lcEq s "uint32_t".toList then some (.int false .w32)
  else if lcEq s "uint64_t".toList then some (.int false .w64)
  else if lcEq s "int8_t".toList then some (.int true .w8)
  else if lcEq s "int16_t".toList then some (.int true .w16)
  else if lcEq s "int32_t".toList then some (.int true .w32)
  else if lcEq s "int64_t".toList then some (.int true .w64)
  else if lcEq s "bool".toList then some (.int false .w8)
  else none

/-- The headers the emitter writes on every unit. -/
def kopfName (s : List Char) : Bool :=
  lcEq s "stdint".toList || lcEq s "stdbool".toList ||
    lcEq s "stdatomic".toList || lcEq s "math".toList

/-! ## 2. What the text declares -/

/-- A table type: its block number, its slot count, and its slot record's
    fields in declaration order. -/
structure TabInfo where
  nr : Nat
  count : Nat
  felder : List (List Char × CTy)

/-- The record layout of a table, as a C compiler lays it out
    (`natLay`: natural alignment, tail padding). NOT transcribed. -/
def TabInfo.lay (T : TabInfo) : RecLay := natLay T.count (T.felder.map Prod.snd)

/-- The index and type of a named field. -/
def feldNr : List (List Char × CTy) → List Char → Nat → Option (Nat × CTy)
  | [], _, _ => none
  | (n, τ) :: rest, s, j => if lcEq n s then some (j, τ) else feldNr rest s (j + 1)

/-- A C local: its number, and -- for a table pointer parameter -- the
    table it points to. -/
structure LokInfo where
  nr : Nat
  tab : Option TabInfo

/-- What the text has declared so far. -/
structure CUmg where
  /-- `#define NAME <integer>`. -/
  makros : List (List Char × Nat) := []
  /-- `typedef struct { … } T_slot;` -- the slot record's fields. -/
  rekords : List (List Char × List (List Char × CTy)) := []
  /-- `typedef struct { T_slot slots[N]; } T;`. -/
  tabs : List (List Char × TabInfo) := []
  /-- `static T T_speicher;` -- a named table object. -/
  objs : List (List Char × TabInfo) := []
  /-- The unit's functions, by name. -/
  fnr : List (List Char × Nat) := []
  /-- The next free function number. -/
  nfn : Nat := 0
  /-- The next free table block number. -/
  ntab : Nat := 0
  /-- Foreign declarations (`void M_nimm(void);`): noted, never called. -/
  fremd : List (List Char) := []
  /-- The bodies, by function number. -/
  defs : List (Nat × CFun) := []
  /-- `_Static_assert((-1 >> 1) == -1, …)` seen. -/
  pinShift : Bool := false
  /-- `_Static_assert((int)0xFFFFFFFFu == -1, …)` seen. -/
  pinConv : Bool := false

/-- Lookup by function number. -/
def defFind : List (Nat × CFun) → Nat → Option CFun
  | [], _ => none
  | (k, F) :: rest, n => if k = n then some F else defFind rest n

/-! ## 3. Token helpers -/

abbrev Toks := List CTok

/-- The next token is this mark. -/
def markeC (p : CPunct) : Toks → Option Toks
  | .pn q :: r => if p = q then some r else none
  | _ => none

/-- The next token is this word. -/
def wortC (w : List Char) : Toks → Option Toks
  | .id s :: r => if lcEq s w then some r else none
  | _ => none

/-! ## 4. Expressions

    NO RECURSION, and that is a cost decision as much as a scope one. A
    mutual recursion through a fuel argument compiles to a mutual
    `Nat.brecOn`, and reducing THAT in the kernel is EXPONENTIAL in the
    fuel: with the fuel taken from the token count, one probe
    (`return x + 1;`, seven tokens) grew to 112 GB before it was killed
    (2026-09-15; the report has the table). The expressions of this
    subset nest at most one level -- a slot read whose index is a literal
    or a local -- so they are parsed by three functions that call each
    other WITHOUT recursion, and a deeper expression is refused. -/

/-- A slot index: a literal or a local. An index that is an expression
    (arithmetic, a nested slot read) is refused, not guessed. -/
def indexC (lok : List (List Char × LokInfo)) : Toks → Option (CX × Toks)
  | .num v :: r => some (.lit (Int.ofNat v), r)
  | .id s :: r =>
    match lcFind lok s with
    | some li => some (.var li.nr, r)
    | none => none
  | _ => none

/-- `slots[i].f` after the base: the emitted address, with the record
    geometry COMPUTED from the table's declarations. -/
def slotC (lok : List (List Char × LokInfo)) (T : TabInfo) (basis : CX) :
    Toks → Option (CX × CTy × Toks)
  | .id sl :: .pn .lbrack :: r =>
    if lcEq sl "slots".toList then
      match indexC lok r with
      | some (i, r1) =>
        match r1 with
        | .pn .rbrack :: .pn .dot :: .id f :: r2 =>
          match feldNr T.felder f 0 with
          | some (j, tau) => some (.slotA basis i T.count T.lay.ssize (T.lay.off j), tau, r2)
          | none => none
        | _ => none
      | none => none
    else none
  | _ => none

/-- A slot place: `p->slots[i].f` through a table pointer parameter, or
    `T_speicher.slots[i].f` at a named table object. Gives the ADDRESS
    node and the cell's type. -/
def platzC (u : CUmg) (lok : List (List Char × LokInfo)) : Toks → Option (CX × CTy × Toks)
  | .id s :: .pn .arrow :: r =>
    match lcFind lok s with
    | some li =>
      match li.tab with
      | some T => slotC lok T (.var li.nr) r
      | none => none
    | none => none
  | .id s :: .pn .dot :: r =>
    match lcFind u.objs s with
    | some T => slotC lok T (.addr (.tab T.nr)) r
    | none => none
  | _ => none

/-- An expression of the subset: an integer literal, a local, or a slot
    read. -/
def ausdruckC (u : CUmg) (lok : List (List Char × LokInfo)) : Toks → Option (CX × Toks)
  | .num v :: r => some (.lit (Int.ofNat v), r)
  | .id s :: r =>
    match platzC u lok (.id s :: r) with
    | some (a, tau, r') => some (.ld a tau, r')
    | none =>
      match lcFind lok s with
      | some li => some (.var li.nr, r)
      | none => none
  | _ => none

/-- A call's arguments, up to and including the closing parenthesis. -/
def argsC (u : CUmg) (lok : List (List Char × LokInfo)) : Nat → Toks → Option (List CX × Toks)
  | 0, _ => none
  | n + 1, ts =>
    match ts with
    | .pn .rpar :: r => some ([], r)
    | _ =>
      match ausdruckC u lok ts with
      | some (e, r) =>
        match r with
        | .pn .comma :: r1 =>
          match argsC u lok n r1 with
          | some (es, r2) => some (e :: es, r2)
          | none => none
        | .pn .rpar :: r1 => some ([e], r1)
        | _ => none
      | none => none

/-! ## 5. Statements -/

/-- ONE statement of the subset. `erg` is the function's return type
    (`none` for `void`), so `return e;` carries the conversion the C
    semantics applies. -/
def anwC (u : CUmg) (lok : List (List Char × LokInfo)) (erg : Option CTy) :
    Nat → Toks → Option (CS × Toks)
  | 0, _ => none
  | n + 1, ts =>
    match ts with
    -- `(void)x;` and `(void)f(args);`
    | .pn .lpar :: .id v :: .pn .rpar :: r =>
      if lcEq v "void".toList then
        match r with
        | .id f :: .pn .lpar :: r1 =>
          match lcFind u.fnr f with
          | some num =>
            match argsC u lok n r1 with
            | some (as, r2) =>
              match markeC .semi r2 with
              | some r3 => some (.call num as none, r3)
              | none => none
            | none => none
          | none => none
        | .id x :: .pn .semi :: r1 =>
          match lcFind lok x with
          | some li => some (.expr (.var li.nr), r1)
          | none => none
        | _ => none
      else none
    | .id s :: r =>
      if lcEq s "return".toList then
        match r with
        | .pn .semi :: r1 =>
          match erg with
          | none => some (.ret none, r1)
          | some _ => none
        | _ =>
          match ausdruckC u lok r with
          | some (e, r1) =>
            match markeC .semi r1 with
            | some r2 =>
              match erg with
              | some τ => some (.ret (some (τ, e)), r2)
              | none => none
            | none => none
          | none => none
      else
        match r with
        -- `f(args);`
        | .pn .lpar :: r1 =>
          match lcFind u.fnr s with
          | some num =>
            match argsC u lok n r1 with
            | some (as, r2) =>
              match markeC .semi r2 with
              | some r3 => some (.call num as none, r3)
              | none => none
            | none => none
          | none => none
        -- `place = e;`
        | _ =>
          match platzC u lok (.id s :: r) with
          | some (a, τ, r1) =>
            match markeC .assign r1 with
            | some r2 =>
              match ausdruckC u lok r2 with
              | some (e, r3) =>
                match markeC .semi r3 with
                | some r4 => some (.store a τ e, r4)
                | none => none
              | none => none
            | none => none
          | none => none
    | _ => none

/-- The statements of a body, up to its closing brace. -/
def anwListeC (u : CUmg) (lok : List (List Char × LokInfo)) (erg : Option CTy) :
    Nat → Toks → Option (List CS × Toks)
  | 0, _ => none
  | n + 1, ts =>
    match ts with
    | .pn .rbrace :: r => some ([], r)
    | _ =>
      match anwC u lok erg n ts with
      | some (s, r) =>
        match anwListeC u lok erg n r with
        | some (ss, r2) => some (s :: ss, r2)
        | none => none
      | none => none

/-- A statement list as ONE statement, in the shape a certificate's rows
    elaborate to (`KorrespondenzAllg.endCS`): a trailing `return` is the
    `return` itself, falling off the end is `skip`. -/
def blockCS : List CS → CS
  | [] => .skip
  | s :: ss =>
    match s, ss with
    | .ret cr, [] => .ret cr
    | s, ss => .seq s (blockCS ss)

/-! ## 6. Declarations -/

/-- A scalar field of a slot record: `uint32_t stand;`. -/
def feldC : Toks → Option ((List Char × CTy) × Toks)
  | .id ty :: .id nm :: .pn .semi :: r =>
    match cTypName ty with
    | some τ => some ((nm, τ), r)
    | none => none
  | _ => none

/-- The fields of a slot record, up to its closing brace. -/
def felderC : Nat → Toks → Option (List (List Char × CTy) × Toks)
  | 0, _ => none
  | n + 1, ts =>
    match ts with
    | .pn .rbrace :: r => some ([], r)
    | _ =>
      match feldC ts with
      | some (f, r) =>
        match felderC n r with
        | some (fs, r2) => some (f :: fs, r2)
        | none => none
      | none => none

/-- A slot count: a literal or a macro. -/
def anzahlC (u : CUmg) : Toks → Option (Nat × Toks)
  | .num v :: r => some (v, r)
  | .id m :: r =>
    match lcFind u.makros m with
    | some v => some (v, r)
    | none => none
  | _ => none

/-- A preprocessor line: one of the four includes, or an integer
    `#define`. -/
def direktiveC (u : CUmg) : Toks → Option CUmg
  | .id d :: .pn .lt :: .id h :: .pn .dot :: .id x :: .pn .gt :: [] =>
    if lcEq d "include".toList && kopfName h && lcEq x ['h'] then some u else none
  | .id d :: .id nm :: rest =>
    if lcEq d "define".toList then
      match rest with
      | [.num v] => some { u with makros := (nm, v) :: u.makros }
      | [.pn .lpar, .num v, .pn .rpar] => some { u with makros := (nm, v) :: u.makros }
      | [.pn .lpar, .id m, .pn .rpar] =>
        match lcFind u.makros m with
        | some v => some { u with makros := (nm, v) :: u.makros }
        | none => none
      | _ => none
    else none
  | _ => none

/-- The two `_Static_assert` pins of the prelude (PLAN-BITS §5b), each
    matched as the exact token sequence the emitter writes. Any other
    `_Static_assert` is refused: a pin nobody checked is no pin. -/
def pinC (u : CUmg) : Toks → Option (CUmg × Toks)
  | .id _ :: .pn .lpar :: .pn .lpar :: .pn .minus :: .num 1 :: .pn .shr :: .num 1 ::
      .pn .rpar :: .pn .eq :: .pn .minus :: .num 1 :: .pn .comma :: .str _ ::
      .pn .rpar :: .pn .semi :: r => some ({ u with pinShift := true }, r)
  | .id _ :: .pn .lpar :: .pn .lpar :: .id i :: .pn .rpar :: .num 4294967295 ::
      .pn .eq :: .pn .minus :: .num 1 :: .pn .comma :: .str _ ::
      .pn .rpar :: .pn .semi :: r =>
    if lcEq i "int".toList then some ({ u with pinConv := true }, r) else none
  | _ => none

/-- A `typedef struct { … } NAME;`: a slot record, or a table. -/
def typedefC (u : CUmg) : Nat → Toks → Option (CUmg × Toks)
  | 0, _ => none
  | n + 1, ts =>
    match ts with
    -- `typedef struct { REC slots[N]; } T;`
    | .id rec :: .id sl :: .pn .lbrack :: rest =>
      if lcEq sl "slots".toList then
        match lcFind u.rekords rec with
        | some fs =>
          match anzahlC u rest with
          | some (cnt, r1) =>
            match r1 with
            | .pn .rbrack :: .pn .semi :: .pn .rbrace :: .id nm :: .pn .semi :: r2 =>
              some ({ u with tabs := (nm, ⟨u.ntab, cnt, fs⟩) :: u.tabs, ntab := u.ntab + 1 }, r2)
            | _ => none
          | none => none
        | none => none
      else none
    -- `typedef struct { <scalar fields> } T_slot;`
    | _ =>
      match felderC n ts with
      | some (fs, r) =>
        match r with
        | .id nm :: .pn .semi :: r1 => some ({ u with rekords := (nm, fs) :: u.rekords }, r1)
        | _ => none
      | none => none

/-- One parameter: `[const] <type> <name>` or
    `[const] <table type> *restrict <name>`. -/
def paramC (u : CUmg) (nr : Nat) : Toks → Option ((Nat × CTy) × (List Char × LokInfo) × Toks)
  | ts =>
    let ts' :=
      match ts with
      | .id c :: r => if lcEq c "const".toList then r else ts
      | _ => ts
    match ts' with
    | .id ty :: r =>
      match cTypName ty with
      | some τ =>
        match r with
        | .id nm :: r1 => some ((nr, τ), (nm, ⟨nr, none⟩), r1)
        | _ => none
      | none =>
        match lcFind u.tabs ty with
        | some T =>
          match r with
          | .pn .star :: .id rs :: .id nm :: r1 =>
            if lcEq rs "restrict".toList then some ((nr, .ptr), (nm, ⟨nr, some T⟩), r1) else none
          | _ => none
        | none => none
    | _ => none

/-- The parameter list, up to and including the closing parenthesis.
    `(void)` is the empty list. -/
def paramsC (u : CUmg) : Nat → Nat → Toks →
    Option (List (Nat × CTy) × List (List Char × LokInfo) × Toks)
  | 0, _, _ => none
  | n + 1, nr, ts =>
    match ts with
    | .id v :: .pn .rpar :: r => if lcEq v "void".toList then some ([], [], r) else none
    | _ =>
      match paramC u nr ts with
      | some (p, l, r) =>
        match r with
        | .pn .comma :: r1 =>
          match paramsC u n (nr + 1) r1 with
          | some (ps, ls, r2) => some (p :: ps, l :: ls, r2)
          | none => none
        | .pn .rpar :: r1 => some ([p], [l], r1)
        | _ => none
      | none => none

/-- Zero or more `__attribute__((word))`. Nested arguments (`section(…)`)
    are refused. -/
def attrsC : Nat → Toks → Option Toks
  | 0, _ => none
  | n + 1, ts =>
    match ts with
    | .id a :: .pn .lpar :: .pn .lpar :: .id _ :: .pn .rpar :: .pn .rpar :: r =>
      if lcEq a "__attribute__".toList then attrsC n r else some ts
    | _ => some ts

/-- A `static` item: a named table object, or a function declaration or
    definition. -/
def statischC (u : CUmg) : Nat → Toks → Option (CUmg × Toks)
  | 0, _ => none
  | n + 1, ts =>
    match ts with
    -- `static T T_speicher;`
    | .id ty :: .id nm :: .pn .semi :: r =>
      match lcFind u.tabs ty with
      | some T => some ({ u with objs := (nm, T) :: u.objs }, r)
      | none => none
    -- `static <ret> f(<params>) <attrs> ;` or `… { body }`
    | .id ty :: .id nm :: .pn .lpar :: r =>
      let erg := if lcEq ty "void".toList then some (none : Option CTy) else (cTypName ty).map some
      match erg with
      | none => none
      | some erg =>
        match paramsC u n 0 r with
        | some (ps, lok, r1) =>
          match attrsC n r1 with
          | some r2 =>
            let num := match lcFind u.fnr nm with | some k => k | none => u.nfn
            let u' := match lcFind u.fnr nm with
              | some _ => u
              | none => { u with fnr := (nm, u.nfn) :: u.fnr, nfn := u.nfn + 1 }
            match r2 with
            | .pn .semi :: r3 => some (u', r3)
            | .pn .lbrace :: r3 =>
              match defFind u.defs num with
              | some _ => none   -- a function defined twice
              | none =>
                match anwListeC u' lok erg n r3 with
                | some (ss, r4) =>
                  some ({ u' with defs := (num, ⟨ps, [], blockCS ss⟩) :: u'.defs }, r4)
                | none => none
            | _ => none
          | none => none
        | none => none
    | _ => none

/-! ## 7. The unit -/

/-- The top-level loop. -/
def topC (u : CUmg) : Nat → Toks → Option CUmg
  | 0, _ => none
  | n + 1, ts =>
    match ts with
    | [] => some u
    | .direkt d :: r =>
      match direktiveC u d with
      | some u' => topC u' n r
      | none => none
    | .id s :: r =>
      if lcEq s "_Static_assert".toList then
        match pinC u (.id s :: r) with
        | some (u', r') => topC u' n r'
        | none => none
      else if lcEq s "typedef".toList then
        match wortC "struct".toList r with
        | some r1 =>
          match markeC .lbrace r1 with
          | some r2 =>
            match typedefC u n r2 with
            | some (u', r3) => topC u' n r3
            | none => none
          | none => none
        | none => none
      else if lcEq s "static".toList then
        match statischC u n r with
        | some (u', r1) => topC u' n r1
        | none => none
      else if lcEq s "void".toList then
        -- `void M_nimm(void);` -- a foreign declaration, never called
        match r with
        | .id nm :: .pn .lpar :: .id v :: .pn .rpar :: .pn .semi :: r1 =>
          if lcEq v "void".toList then topC { u with fremd := nm :: u.fremd } n r1 else none
        | _ => none
      else none
    | _ => none

/-- The functions `0 … k-1`, in order; a hole (a function declared and
    never defined) is a refusal. -/
def alleFns (d : List (Nat × CFun)) : Nat → Nat → Option (List CFun)
  | 0, _ => some []
  | n + 1, i =>
    match defFind d i with
    | some F =>
      match alleFns d n (i + 1) with
      | some rest => some (F :: rest)
      | none => none
    | none => none

/-- A text as the concatenation of its lines. The pinned texts are
    written as a LIST OF LINES and joined here: one long string literal
    would cost the kernel gigabytes (the cost note at `lexC`), and a
    mutation of one line stays visible as a mutation of one line. -/
def zusammen : List (List Char) → List Char
  | [] => []
  | l :: ls => l ++ zusammen ls

/-- **THE C PARSER**: the emitted text -- its characters -- as the
    functions of the C unit, by C function number; or `none`, which is
    every text outside the subset. Both `_Static_assert` pins must be
    present. (Why `List Char` and not `String`: the cost note at `lexC`.) -/
def parseC (cs : List Char) : Option (List CFun) :=
  match lexC cs with
  | some ts =>
    match topC {} (ts.length + 1) ts with
    | some u => if u.pinShift && u.pinConv then alleFns u.defs u.nfn 0 else none
    | none => none
  | none => none

/-- The same on a `String`, for short texts (the probes). -/
def parseS (s : String) : Option (List CFun) := parseC s.toList

/-- The C unit as the semantics wants it (`CProg`), from a text that
    parses. -/
def cProgC (cs : List Char) : CProg := fun n => ((parseC cs).getD [])[n]?

/-- `parseC` is a function: every text has an outcome, and a text outside
    the subset has the outcome `none`. Trivially, by exhibiting it -- the
    content is that `parseC` is TOTAL. -/
theorem parseC_total (cs : List Char) : ∃ r, parseC cs = r := ⟨parseC cs, rfl⟩

/-- The functions of a parsed text ARE the unit `cProgC` reads. -/
theorem cProgC_eq {cs : List Char} {fs : List CFun} (h : parseC cs = some fs) :
    cProgC cs = fun n => fs[n]? := by
  unfold cProgC; rw [h]; rfl

end Gabbro.Grammatik.CParser
