module

public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.Transition.Elaborate

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

/-- The head of an `extern fn`: a foreign body, `D.Ax` -- its parameters and its answer. -/
def uAxKopf (alias : List (String × (Int × Int))) (tabs : List UTab) (whys : List UWhy)
    (name : String) (params : List (String × STyp)) (res : Option STyp) (fehler : Option String) :
    Except String UFnKopf :=
  match uSeq (params.map (uParam alias tabs [] whys)) with
  | .error e => .error e
  | .ok ps =>
    match (match fehler with
        | .none => .ok none
        | .some r =>
          match whys.findIdx? (fun (w : UWhy) => strEq w.name r) with
          | .none => .error ("reason unknown: " ++ r)
          | .some k =>
            match whys[k]? with
            | .some w => if w.cases.isEmpty then .error "reason without cases" else .ok (some (k, w.cases.length))
            | .none => .error ("reason unknown: " ++ r) : Except String (Option (Nat × Nat))) with
    | .error e => .error e
    | .ok kn =>
      let base : UFnKopf :=
        { name, names := ps.map (·.1), kinds := ps.map (·.2.2), types := ps.map (·.2.1), res := .none,
          bits := params.map (fun p => uParamBreite p.2), held := [], ext := true, kanal := kn }
      match res with
      | .none => if kn.isSome then .error "foreign fn with a reason channel and no answer without G form" else .ok base
      | .some (.atom "never") => .ok { base with resNever := true }
      | .some (.atom "bool") => if kn.isSome then .error "fallible foreign fn with a non-number answer without G form" else .ok { base with resBool := true }
      | .some (.index false tn) =>
        match tabs.findIdx? (fun (y : UTab) => strEq y.name tn && y.von.isSome) with
        | .some num => if kn.isSome then .error "fallible provider without G form" else .ok { base with resRef := some num }
        | .none => .error "foreign answer `index into` a table that is not open without G form"
      | .some t =>
        match uErgBereich alias t with
        | .error e => .error e
        | .ok r => .ok { base with res := .some r }

/-- The head of an `extern fn`: a foreign body, `D.Ax` -- its parameters and its answer. -/
def elabAxKopf (alias : List (String × (Int × Int))) (tabs : List UTab) (whys : List UWhy) (globs : List UGlob)
    (asm : Bool) : FnSig → Except String UFnKopf
  | { art, name, params, res, fehler, klauseln } =>
    -- `extern`, `raw`, `prim` and `= asm`: a foreign body (SYNTAX.md); a body-less `divergent fn` is one whose
    -- answer is `never`
    if !(asm || strEq art "extern" || strEq art "raw" || strEq art "prim" || strEq art "divergent") then
      .error "foreign fn without G form"
    else if strEq art "divergent" && res.isSome then .error "divergent fn with a result without G form"
    else
      match uAxKopf alias tabs whys name params (if strEq art "divergent" then some (.atom "never") else res) fehler with
      | .error e => .error e
      | .ok kopf => uAxKlauseln kopf tabs globs klauseln

/-- The head of a `syscall` gate (a foreign body too): the ABI half (`abi`, `number`, the registers) is the stub's,
    a precondition, a postcondition or a write has no form. -/
def elabGateKopf (alias : List (String × (Int × Int))) (tabs : List UTab) (whys : List UWhy) (globs : List UGlob)
    (sc : SSyscall) : Except String UFnKopf :=
  if !(sc.gate.pre.isEmpty && sc.gate.post.isEmpty) then .error "foreign fn clause without G form"
  else match uAxKopf alias tabs whys sc.name sc.params sc.res sc.fail with
    | .error e => .error e
    | .ok kopf => uAxKlauseln kopf tabs globs [.effs sc.gate.uses]

/-- The roots of the `start { .. };` statements of a body, in order (`fuel` bounds the nesting). -/
def uStartNamen : Nat → SAnw → List String
  | 0, _ => []
  | _ + 1, .start ns => ns
  | f + 1, .block ss _ => ss.flatMap (uStartNamen f)
  | f + 1, .cond _ b ei els => uStartNamen f b ++ ei.flatMap (uStartNamen f) ++ (els.map (uStartNamen f)).getD []
  | f + 1, .elsif _ b => uStartNamen f b
  | f + 1, .each _ _ _ _ _ _ _ b => uStartNamen f b
  | f + 1, .retry _ b => uStartNamen f b
  | f + 1, .loop _ b => uStartNamen f b
  | f + 1, .locks _ _ b => uStartNamen f b
  | f + 1, .trim _ _ b => uStartNamen f b
  | f + 1, .cases _ arms => arms.flatMap (uStartNamen f)
  | f + 1, .arm _ _ b => uStartNamen f b
  | _, _ => []

/-- Each root once, in order. -/
def uOhneDoppelte (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.any (fun y => strEq y x) then acc else acc ++ [x]) []

/-- The numeral a token list is. -/
def uZahlTok : List Token → Option Int
  | [.num n] => some (Int.ofNat n)
  | [.zeichen "-", .num n] => some (-(Int.ofNat n))
  | _ => none

/-- A payload type: a type word, or `T in lo .. hi`. -/
def uNutzTyp (alias : List (String × (Int × Int))) : List Token → Except String (Int × Int)
  | [.ident n] => uTypName alias n
  | [.wort n] => uTypName alias n
  | ts =>
    match uTeileBereich [] ts with
    | some (_ :: .wort "in" :: lo, ex, hi) =>
      match uZahlTok lo, uZahlTok hi with
      | some a, some b => .ok (a, if ex then b - 1 else b)
      | _, _ => .error "payload range without G form"
    | _ => .error "payload type without G form"

/-- The tokens up to the closing parenthesis, and the rest behind it. -/
def uBisKlammer : List Token → List Token → Option (List Token × List Token)
  | _, [] => none
  | acc, .zeichen ")" :: rest => some (acc.reverse, rest)
  | acc, t :: rest => uBisKlammer (t :: acc) rest

/-- The cases of a tagged type from its tokens (`Leer , Kurz ( u32 in 0 .. 100 )`), `fuel` bounds the length. -/
def uSumFaelle (alias : List (String × (Int × Int))) :
    Nat → List Token → Except String (List (String × Option (Int × Int)))
  | 0, _ => .error "tagged type too long"
  | _, [] => .ok []
  | f + 1, .ident n :: .zeichen "," :: rest =>
    match uSumFaelle alias f rest with
    | .error e => .error e
    | .ok r => .ok ((n, none) :: r)
  | _ + 1, [.ident n] => .ok [(n, none)]
  | f + 1, .ident n :: .zeichen "(" :: rest =>
    match uBisKlammer [] rest with
    | none => .error "tagged case without G form"
    | some (ty, rest2) =>
      match uNutzTyp alias ty with
      | .error e => .error e
      | .ok r =>
        match rest2 with
        | [] => .ok [(n, some r)]
        | .zeichen "," :: rest3 =>
          match uSumFaelle alias f rest3 with
          | .error e => .error e
          | .ok more => .ok ((n, some r) :: more)
        | _ => .error "tagged case without G form"
  | _ + 1, _ => .error "tagged case without G form"

/-- The `tagged type` items of a unit. -/
def uSums (alias : List (String × (Int × Int))) : List SItemTief → Except String (List USum)
  | [] => .ok []
  | .typeT ["tagged"] n _ _ (.some (.raw txt)) :: rest =>
    match lex txt with
    | .error _ => .error "tagged type without G form"
    | .ok toks0 =>
      let toks := toks0.filter (fun k => match k with | .ende => false | _ => true)
      match toks with
      | .zeichen "{" :: inner =>
        match inner.reverse with
        | .zeichen "}" :: rev =>
          match uSumFaelle alias 10000 rev.reverse with
          | .error e => .error e
          | .ok cs =>
            if cs.isEmpty then .error "tagged type without cases"
            else
              match uSums alias rest with
              | .error e => .error e
              | .ok r => .ok ({ name := n, cases := cs } :: r)
        | _ => .error "tagged type without G form"
      | _ => .error "tagged type without G form"
  | _ :: rest => uSums alias rest

/-- The `reason` items of a unit: the names of their cases in order; a reason that is not `exhaustive` has no
    G form (`Ty.why n` has exactly `n` reasons). -/
def uWhys : List SItemTief → Except String (List UWhy)
  | [] => .ok []
  | .whyT n cs ex :: rest =>
    if !ex then .error "reason that is not exhaustive without G form"
    else
      match uWhys rest with
      | .error e => .error e
      | .ok r => .ok ({ name := n, cases := cs.map (·.1) } :: r)
  | _ :: rest => uWhys rest

/-! ## States -/

/-- The governed fields: each `transition` statement of a body names its table, field and state; a field
    governed by two states is refused. -/
def uRegiert (fns : List UFn) (states : List UZustand := []) : Except String (List (String × String × String)) :=
  let alle := fns.flatMap fun f => f.body.filterMap fun st => match st with
    | .shiftTab tb fld _ s _ _ => some (tb, fld, s)
    | _ => none
  let declared := states.flatMap fun state => state.transitions.flatMap fun tr =>
    if tr.primitive then [] else tr.writes.filterMap fun write => match write.place with
      | .slot table field _ => some (table, field, state.name)
      | _ => none
  let eins := (alle ++ declared).foldl (fun acc x => if acc.any (fun y => strEq y.1 x.1 && strEq y.2.1 x.2.1 && strEq y.2.2 x.2.2)
    then acc else acc ++ [x]) []
  if eins.all (fun x => eins.all (fun y => !(strEq x.1 y.1 && strEq x.2.1 y.2.1) || strEq x.2.2 y.2.2)) then .ok eins
  else .error "a field governed by two states"

/-! ## Invariants -/

/-- The predicate of an invariant over its carriers: no parameter, the guards of the carriers held. -/
def uInv (consts : List (String × Int)) (alias : List (String × (Int × Int))) (tabs : List UTab)
    (locks : List ULock) (globs : List UGlob) (traeger : List String) (g : SGruppenInv) : Except String UInv :=
  if !traeger.all (fun c => tabs.any (fun t => strEq t.name c && !t.arena)) then .error "invariant carrier without G form"
  else
    let held := (locks.filter (fun l => l.guard.any (fun c => traeger.any (strEq · c)))).map (·.name)
    let ctx : UCtx := { names := [], kinds := [], types := [], tabs, locks, held, res := none, fname := g.name,
                        alias, lits := consts, globs }
    match uBool ctx g.pred with
    | .error e => .error e
    | .ok p => .ok { name := g.name, traeger, pred := p }

/-- The `invariant p` of each lock, read with the lock held: the predicate names the protected carriers and
    constants only (`N275`). -/
def uSperrInvs (consts : List (String × Int)) (alias : List (String × (Int × Int))) (globs : List UGlob)
    (tabs : List UTab) (ms : List SItemTief) (locks : List ULock) : Except String (List ULock) :=
  uSeq (locks.map fun l =>
    match ms.findSome? (fun m => match m with | .lockT n _ _ _ _ _ p => if strEq n l.name then some p else none | _ => none) with
    | some (some e) =>
      let ctx : UCtx := { names := [], kinds := [], types := [], tabs, locks, held := [l.name], res := none,
                          fname := l.name, alias, lits := consts, globs }
      match uBool ctx e with
      | .error x => .error x
      | .ok p => .ok { l with inv := some p }
    | _ => .ok l)

/-- The invariants of the unit: those of each table, in table order, then those of each `group`. -/
def uInvs (consts : List (String × Int)) (alias : List (String × (Int × Int))) (tabs : List UTab)
    (locks : List ULock) (globs : List UGlob) (ms : List SItemTief) : Except String (List UInv) :=
  let ausTab := ms.flatMap fun it => match it with
    | .tableT n _ _ _ _ _ parts => parts.filterMap fun p => match p with
      | .tInv g => some (uInv consts alias tabs locks globs [n] g)
      | _ => none
    | _ => []
  let ausGruppe := ms.flatMap fun it => match it with
    | .groupT _ ts gs => gs.map (uInv consts alias tabs locks globs ts)
    | _ => []
  uSeq (ausTab ++ ausGruppe)

/-- `U003`: a function that writes a carrier of an invariant holds (by `requires Held(..)`) every lock that
    guards a carrier of it -- it owes the invariant at its `return` and reads all of them there. -/
def uU003 (locks : List ULock) (fns : List UFn) (invs : List UInv) : Bool :=
  invs.all fun i => fns.all fun f =>
    !(f.puts.any (fun t => i.traeger.any (strEq · t))) ||
    (locks.filter (fun l => l.guard.any (fun c => i.traeger.any (strEq · c)))).all
      (fun l => f.held.any (strEq · l.name))

/-! ## Device registers -/

/-- The register class word (`regklasse`). -/
def uRegKlasse (k : String) : Except String Regklasse :=
  if strEq k "r" then .ok .r else if strEq k "w" then .ok .w else if strEq k "rw" then .ok .rw
  else if strEq k "w1c" then .ok .w1c else if strEq k "rc" then .ok .rc
  else .error ("register class without G form: " ++ k)

/-- A side of a register predicate at the value `v` (the register's own name reads `v`). -/
def uZSeite (v : Int) : USide → Option Int
  | .lit k => some k
  | .param _ => some v
  | .add a b => (uZSeite v a).bind fun x => (uZSeite v b).map (x + ·)
  | .sub a b => (uZSeite v a).bind fun x => (uZSeite v b).map (x - ·)
  | .mul a b => (uZSeite v a).bind fun x => (uZSeite v b).map (x * ·)
  | .neg a => (uZSeite v a).map (- ·)
  | _ => none

/-- A comparison of two numbers by its operator word. -/
def uVergleich (op : String) (x y : Int) : Option Bool :=
  if strEq op "==" then some (decide (x = y)) else if strEq op "!=" then some (!decide (x = y))
  else if strEq op "<" then some (decide (x < y)) else if strEq op "<=" then some (decide (x ≤ y))
  else if strEq op ">" then some (decide (y < x)) else if strEq op ">=" then some (decide (y ≤ x))
  else none

/-- A register predicate at the value `v` (`none`: a form the promise does not evaluate). -/
def uZEns (v : Int) : UEns → Option Bool
  | .cmp op a b => (uZSeite v a).bind fun x => (uZSeite v b).bind fun y => uVergleich op x y
  | .tru => some true
  | .fls => some false
  | .and a b => (uZEns v a).bind fun x => (uZEns v b).map (x && ·)
  | .or a b => (uZEns v a).bind fun x => (uZEns v b).map (x || ·)
  | .not a => (uZEns v a).map (!·)
  | _ => none

/-- The device's promise of a register at a read value: `true` without a promise. -/
def UReg.zusageBei (g : UReg) (v : Int) : Bool :=
  match g.zusage with
  | none => true
  | some p => (uZEns v p).getD true

/-- The context of a register predicate: the register's own name is its one (numeric) variable. -/
def uRegCtx (alias : List (String × (Int × Int))) (lits : List (String × Int)) (n : String) (lo hi : Int) :
    UCtx :=
  { names := [n], kinds := [.int], types := [.int lo hi], tabs := [], locks := [], held := [], res := none,
    fname := n, alias, lits }

/-- One `reg` of a device: an integer type (an EMPTY range `lo > hi` included: the declaration stands, a read
    answers nothing -- the checker's `N314`), a class without stages, no bit fields, a promise (or, with
    `else`, a check at the binding) that evaluates, and `depends` carriers that are tables or statics of the
    unit, named bare. -/
def uReg (alias : List (String × (Int × Int))) (lits : List (String × Int)) (tabs : List UTab)
    (globs : List UGlob) (dev : String) (rg : SReg) : Except String UReg :=
  if !rg.stage.isEmpty then .error "register class per stage without G form"
  else if !rg.felder.isEmpty then .error "register fields without G form"
  else
    match (match rg.rtyp with
        | .atom "bool" => .ok (0, 1, true)
        | t => (uErgBereich alias t).map fun (lo, hi) => (lo, hi, false) : Except String (Int × Int × Bool)) with
    | .error e => .error e
    | .ok (lo, hi, istB) =>
      match uRegKlasse rg.klasse with
      | .error e => .error e
      | .ok k =>
        match uSeq (rg.abhaengt.map fun c => match c with
            | [n] =>
              if tabs.any (fun x => strEq x.name n) || globs.any (fun x => strEq x.name n) then .ok n
              else .error ("depends names no carrier: " ++ n)
            | _ => .error "depends on a field without G form") with
        | .error e => .error e
        | .ok ts =>
          match (match rg.voraus with
              | none => .ok none
              | some p =>
                match uBool (uRegCtx alias lits rg.name lo hi) p with
                | .error e => .error e
                | .ok q => if (uZEns lo q).isSome then .ok (some q) else .error "register promise without G form"
              : Except String (Option UEns)) with
          | .error e => .error e
          | .ok pr =>
            match rg.elseF with
            | some _ => .ok { dev, name := rg.name, lo, hi, klasse := k, traeger := ts, pruefung := pr, bool := istB }
            | none => .ok { dev, name := rg.name, lo, hi, klasse := k, traeger := ts, zusage := pr, bool := istB }

/-- `mirrors W from M` of a device: `M` at `W`. -/
def uSpiegelPaare : List SGerTeil → Except String (List (String × String))
  | [] => .ok []
  | .copy (.variable w) (.variable m) :: rest =>
    match uSpiegelPaare rest with
    | .error e => .error e
    | .ok ps => .ok ((w, m) :: ps)
  | .copy .. :: _ => .error "mirrors without G form"
  | _ :: rest => uSpiegelPaare rest

/-- The registers of one device, in order: banks and transitions have no G form here (a `bank` is sugar for
    indexed registers; a device `transition` has no statement that invokes it in the language). -/
def uGeraet (alias : List (String × (Int × Int))) (lits : List (String × Int)) (tabs : List UTab)
    (globs : List UGlob) (dev : String) (teile : List SGerTeil) : Except String (List UReg) :=
  match uSpiegelPaare teile with
  | .error e => .error e
  | .ok ms =>
    match uSeq (teile.filterMap fun p => match p with
        | .reg rg => some (uReg alias lits tabs globs dev rg)
        | .bank _ => some (.error "register bank without G form")
        | .trans _ => some (.error "device transition without G form")
        | .copy .. => none) with
    | .error e => .error e
    | .ok regs =>
      if ms.all (fun (w, m) => regs.any (fun g => strEq g.name w) && regs.any (fun g => strEq g.name m)) then
        .ok (regs.map fun g =>
          { g with spiegel := (ms.find? (fun p => strEq p.1 g.name)).map (·.2) })
      else .error "mirrors names no register of the device"

/-- The registers of the unit: every `device` item in order. -/
def uRegs (alias : List (String × (Int × Int))) (lits : List (String × Int)) (tabs : List UTab)
    (globs : List UGlob) : List SItemTief → Except String (List UReg)
  | [] => .ok []
  | .devT n _ _ teile :: rest =>
    match uGeraet alias lits tabs globs n teile with
    | .error e => .error e
    | .ok rs =>
      match uRegs alias lits tabs globs rest with
      | .error e => .error e
      | .ok more => .ok (rs ++ more)
  | _ :: rest => uRegs alias lits tabs globs rest

/-! ## Lock floors (`Signatur.boden`)

    The floor of a function is the lowest rank of any lock taken on a path from it (its own `locks L` blocks
    and, through its calls, the callees'); a function that takes none has the floor `hoch`, above every rank
    of the unit. A unit without locks has no floors.
    The floor is DATA of the elaborated function (`UFn.boden`), filled by the post-pass `uMitBoden` after
    elaboration; the declaration reads it (`mkSig`). This is the rule of the exporter (`resolve_floors`):
    an extra lock held across a call ranks below the callee's floor (`RufPasst.hx`), so every lock the callee
    takes ranks above everything held (`H006` across the call boundary). -/

/-- The rank of a lock by name. -/
def lockRank (u : UProg) (n : String) : Option Int :=
  (u.locks.find? (fun l => l.name == n)).map (·.rank)

def optMin : Option Int → Option Int → Option Int
  | none, b => b
  | a, none => a
  | some a, some b => some (min a b)

/-- The lowest rank a function takes directly (its `locks L { .. }` blocks). -/
def directFloor (u : UProg) (f : UFn) : Option Int :=
  f.body.foldl (fun acc st => match st with
    | .lockBeg n => optMin acc (lockRank u n)
    | _ => acc) none

/-- The functions a function calls directly: a call statement, a call bound by `let`, and a call bound by
    `let .. else (e) { .. }` (`bindElse`). -/
def callNames (f : UFn) : List String :=
  f.body.filterMap fun st => match st with
    | .call c _ => some c
    | .bindCall _ c _ => some c
    | .bindElse _ c _ _ => some c
    | .callInd _ c _ => some c
    | .bindCallInd _ _ c _ => some c
    | _ => none

/-- One round of the floor relation: the direct floor and the floors of the callees found so far. -/
def floorStep (u : UProg) (cur : List (String × Option Int)) : List (String × Option Int) :=
  u.fns.map fun f =>
    (f.name, (callNames f).foldl
      (fun acc c => optMin acc (((cur ++ u.ptrs.map (fun p => (p.name, p.boden))).find? (fun p => p.1 == c)).bind
        (·.2))) (directFloor u f))

/-- `n` rounds (a path through the call graph is at most as long as the number of functions). -/
def floorsN (u : UProg) : Nat → List (String × Option Int)
  | 0 => u.fns.map fun f => (f.name, directFloor u f)
  | n + 1 => floorStep u (floorsN u n)

/-- The floor of a function: `none` in a unit without locks, else the lowest rank on any path from it, or
    one above the highest rank of the unit when the paths take no lock. -/
def floorOf (u : UProg) (f : UFn) : Option Int :=
  if u.locks.isEmpty then none
  else some (match ((floorsN u u.fns.length).find? (fun p => p.1 == f.name)).bind (·.2) with
    | some c => c
    | none => (u.locks.map (·.rank)).foldl max 0 + 1)

/-- The post-pass: every function carries its floor (`UFn.boden`). -/
def uMitBoden (u : UProg) : UProg :=
  { u with fns := u.fns.map fun f => { f with boden := floorOf u f } }


end Gabbro.Grammatik.Parser.Uebersetze
