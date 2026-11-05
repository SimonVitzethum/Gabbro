module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil11
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil17
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil5Rest

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-! ## C15 use export: the core query, its wrapper, the update and the reduction

    Per admitted `accumulates n : T merge op per cpu k [assume a]` item the
    elaborator generates four functions besides the guarded storage
    (`uAkkuItem`):

    * the core query `n#kern`: a FOREIGN body (`UFnKopf` with `ext`), no
      parameters, answer `0 .. k - 1`, no reason channel, no writes -- the
      exact shape `Kernzelle.KernAbfrageGestalt` decides;
    * the query wrapper `n#query`: an ordinary body binding the query once
      and returning its answer, so the update calls a unit function and the
      wrapper's foreign bind is the direct syntactic fact
      `Kernzelle.bindetAxE` decides;
    * the update `n#aktualisiere`: one value parameter, no answer; it binds
      the wrapper once (sample-once at entry: migration afterwards does not
      reselect the destination), dispatches over the answer, and runs, under
      the selected cell's exclusive lock, load/merge/store;
    * the reduction `n#falte`: no parameters, answer `T`; it folds the cells
      in index order, each sample taken under its cell's lock.

    The named `assume a` travels from the declaration to the query head
    (`UFnKopf.annahme`) to the elaborated foreign body (`UAx.beleg`, resolved
    against the unit's `assume` items) to the declaration (`D.axHerkunft`,
    `D.axBeleg`): that, together with the named `AxVertragO` ensures on the
    answer, is the ONE hardware premise of the core query
    (`Kernzelle.KernAbfrageHerkunft`). A declaration without `assume` keeps
    `beleg` at `none`: it elaborates, but no query list admits it.

    The merge per operator, with its range/overflow duty:

    * `max`/`min` select one operand (`wenn`), hence stay in range without a
      check -- no silent wrap, no saturation;
    * `add`/`or`/`and` compute into a fresh local and narrow it to `lo .. hi`
      with `trimReq` (`Block/Endblock.narrowRequired`): a violated prefix duty
      stops with `Logik.kapazitaet` in the update and in the reduction alike,
      excluded by the caller's capacity duty exactly as C11/C18 required
      narrowing. No contribution is dropped, no fold restarts from neutral,
      nothing wraps or saturates silently.

    Use sites expand to calls of the generated functions: `n = v;` becomes
    `n#aktualisiere(v)`, `let x [: T] = n;` and `return n;` become the sampled
    fold. Effects expand to the full permitted carrier set: `writes n` names
    every cell, `reads n` reads every cell. Every other mention of `n` --
    a nested read, a compound update, a contract clause, a foreign signature,
    a call of `n` -- is refused by name: reads go through the sampled fold
    under the cell locks, never bare. A unit that binds `n` as a local is
    refused up front, so the scope-unaware rewrite below cannot misread a
    shadowed name (what it misses still fails as an unknown name).

    Generated names carry `#`, which never occurs in a source name, so they
    meet neither user functions nor user locals. -/

/-- The generated names, the core count and the named origin of one accumulator. -/
structure AkkuPlan where
  name : String
  frage : String
  akt : String
  falt : String
  kernZahl : Nat
  /-- The `assume` clause witnessing the query's hardware origin (`none`
      without one: the query elaborates, but no query list admits it). -/
  herkunft : Option String := none
  deriving DecidableEq, Repr

/-- The plan of one accumulator: `n#kern`, `n#aktualisiere`, `n#falte`. -/
def uAkkuPlan (n : String) (k : Nat) (herkunft : Option String := none) : AkkuPlan :=
  { name := n, frage := n ++ "#kern", akt := n ++ "#aktualisiere",
    falt := n ++ "#falte", kernZahl := k, herkunft := herkunft }

/-- The query wrapper name: `n#query`. -/
def uAkkuHuelle (p : AkkuPlan) : String :=
  p.name ++ "#query"

/-- The query head: a foreign body answering the running core in `0 .. k-1`,
    witnessed by the named `assume` (`UFnKopf.annahme`). -/
def uAkkuFrageKopf (p : AkkuPlan) : UFnKopf :=
  { name := p.frage, names := [], kinds := [], types := [],
    res := some (0, (p.kernZahl : Int) - 1), held := [], ext := true,
    annahme := p.herkunft }

/-- The neutral element as a surface literal. -/
def uAkkuNeutralExpr (z : Int) : SExpr :=
  if 0 ≤ z then .lit z.toNat else .un "-" (.lit (-z).toNat)

/-- The narrow range text of the accumulator's value type. -/
def uAkkuBereichText (lo hi : Int) : String :=
  toString lo ++ " .. " ++ toString hi

/-- One dispatch arm of the update: the locked load/merge/store of cell `i`
    for operator `op` (the value rides in `v`, the merge temp is `s<i>`). -/
def uAkkuAktArm (p : AkkuPlan) (lo hi : Int) (op : String) (i : Nat) : SAnw :=
  let zelle := p.name ++ "#zelle" ++ toString i
  let sperre := p.name ++ "#sperre" ++ toString i
  let s := "s" ++ toString i
  let bereich := uAkkuBereichText lo hi
  let gamb := SAnw.block
    (if strEq op "max" then
      [.cond (.bin "<" (.variable zelle) (.variable "v"))
        (.block [.set (.variable zelle) "=" (.variable "v")] none) [] none]
    else if strEq op "min" then
      [.cond (.bin "<" (.variable "v") (.variable zelle))
        (.block [.set (.variable zelle) "=" (.variable "v")] none) [] none]
    else
      let bin := if strEq op "add" then "+" else if strEq op "or" then "|" else "&"
      [.bind false s none (.bin bin (.variable zelle) (.variable "v")),
        .trimReq (.variable s) bereich,
        .set (.variable zelle) "=" (.variable s)])
    none
  .locks false (.variable sperre) gamb

/-- The dispatch over the queried core: arm `i` runs at answer `i`, the last
    else is empty (the query answers in `0 .. k - 1`). Recursive alternatives
    are canonical blocks; the terminal block contains no statement. -/
def uAkkuVersand (p : AkkuPlan) (lo hi : Int) (op : String) : Nat → SAnw
  | 0 => .block [] none
  | k + 1 =>
    .cond (.bin "==" (.variable "k") (.lit k))
      (.block [uAkkuAktArm p lo hi op k] none) []
      (some (.block (match k with
        | 0 => []
        | _ + 1 => [uAkkuVersand p lo hi op k]) none))

/-- The update body: call the query wrapper once, dispatch, locked load/merge/store. -/
def uAkkuAktKoerper (p : AkkuPlan) (lo hi : Int) (op : String) : SAnw :=
  .block [.bind false "k" none (.call (uAkkuHuelle p) []),
      uAkkuVersand p lo hi op p.kernZahl]
    none

/-- The query wrapper body: bind the hardware query once, return its answer. -/
def uAkkuHuelleKoerper (p : AkkuPlan) : SAnw :=
  .block [.bind false "k" none (.call p.frage [])]
    (some (.ret (some (.variable "k"))))

/-- The query wrapper function: no parameters, answer `0 .. k - 1`, costs
    counting the foreign bind and the return. -/
def uAkkuHuelleFn (p : AkkuPlan) : FnSig × SAnw :=
  ({
    art := "impl"
    name := uAkkuHuelle p
    params := []
    res := some (.range (.atom "u32") (.lit 0) (.lit (p.kernZahl - 1)) false)
    fehler := none
    klauseln := [.cost (.lit 2)]
  },
    uAkkuHuelleKoerper p)

/-- The update function: one value parameter, no answer, writes every cell,
    costs counting query, dispatch, `k` locked load/merge/store triples and
    the overflow checks. -/
def uAkkuAktFn (p : AkkuPlan) (t : STyp) (lo hi : Int) (op : String) :
    FnSig × SAnw :=
  ({
    art := "impl"
    name := p.akt
    params := [("v", t)]
    res := none
    fehler := none
    klauseln := [
      .effs ((List.range p.kernZahl).map (fun i => .writes (.variable (p.name ++ "#zelle" ++ toString i)))),
      .cost (.lit (4 * p.kernZahl + 4))]
  },
    uAkkuAktKoerper p lo hi op)

/-- One merge step of the reduction into the accumulator `m` for cell `i`. -/
def uAkkuFaltSchritt (p : AkkuPlan) (lo hi : Int) (op : String)
    (i : Nat) : List SAnw :=
  let zelle := p.name ++ "#zelle" ++ toString i
  let sperre := p.name ++ "#sperre" ++ toString i
  let s := "s" ++ toString i
  let bereich := uAkkuBereichText lo hi
  let inner : List SAnw :=
    if strEq op "max" then
      [.cond (.bin "<" (.variable "m") (.variable zelle))
        (.block [.set (.variable "m") "=" (.variable zelle)] none) [] none]
    else if strEq op "min" then
      [.cond (.bin "<" (.variable zelle) (.variable "m"))
        (.block [.set (.variable "m") "=" (.variable zelle)] none) [] none]
    else
      let bin := if strEq op "add" then "+" else if strEq op "or" then "|" else "&"
      [.bind false s none (.bin bin (.variable "m") (.variable zelle)),
        .trimReq (.variable s) bereich,
        .set (.variable "m") "=" (.variable s)]
  [.locks false (.variable sperre) (.block inner none)]

/-- The reduction body: start from neutral, fold every cell in index order,
    each sample taken under its cell's lock, return the accumulator. -/
def uAkkuFaltKoerper (p : AkkuPlan) (t : STyp) (lo hi neutral : Int)
    (op : String) : SAnw :=
  .block ([.bind true "m" (some t) (uAkkuNeutralExpr neutral)] ++
      (List.range p.kernZahl).flatMap (uAkkuFaltSchritt p lo hi op))
    (some (.ret (some (.variable "m"))))

/-- The reduction function: no parameters, answer `T`, costs counting the
    neutral start, `k` locked samples, merges and overflow checks. -/
def uAkkuFaltFn (p : AkkuPlan) (t : STyp) (lo hi neutral : Int)
    (op : String) : FnSig × SAnw :=
  ({
    art := "impl"
    name := p.falt
    params := []
    res := some t
    fehler := none
    klauseln := [
      .effs ((List.range p.kernZahl).map (fun i => .reads (.variable (p.name ++ "#zelle" ++ toString i)))),
      .cost (.lit (3 * p.kernZahl + 2))]
  },
    uAkkuFaltKoerper p t lo hi neutral op)

/-- The generated functions of one accumulator item: the query head, the
    update, the reduction and the query wrapper. Storage errors keep their
    exact names. -/
def uAkkuGenItem (consts : List (String × Int))
    (alias : List (String × (Int × Int))) : SItemTief → Except String
    (AkkuPlan × UFnKopf × (FnSig × SAnw) × (FnSig × SAnw) × (FnSig × SAnw))
  | .accT n t m cnt q =>
    match uAkkuAnzahl consts cnt with
    | .error e => .error e
    | .ok k =>
      let p := uAkkuPlan n k q
      match uAkkuBereich alias t with
      | .error e => .error e
      | .ok (lo, hi) =>
        match uAkkuNeutral m lo hi with
        | .error e => .error e
        | .ok z =>
          if !(lo ≤ z && z ≤ hi) then
            .error "accumulator neutral outside its range without G form"
          else if !(akkuOperatorOk m) then .error "accumulator operator without G form"
          else .ok (p, uAkkuFrageKopf p, uAkkuAktFn p t lo hi m,
            uAkkuFaltFn p t lo hi z m, uAkkuHuelleFn p)
  | _ => .error "expected accumulator declaration"

/-- One item with its origin checked: a named `assume` must be declared in
    the unit; an unknown name is refused by name. -/
def uAkkuGenEintrag (annahmen : List String) (consts : List (String × Int))
    (alias : List (String × (Int × Int))) : SItemTief → Except String
    (AkkuPlan × UFnKopf × (FnSig × SAnw) × (FnSig × SAnw) × (FnSig × SAnw))
  | .accT n t m cnt (some a) =>
    if annahmen.any (strEq · a) then
      uAkkuGenItem consts alias (.accT n t m cnt (some a))
    else .error ("core query assumption unknown: " ++ a)
  | it => uAkkuGenItem consts alias it

/-- The generated functions of the unit's accumulators; a repeated name is
    refused (it would generate the same cells twice). -/
def uAkkuGenFns (consts : List (String × Int))
    (alias : List (String × (Int × Int))) (ms : List SItemTief) : Except String
    (List (AkkuPlan × UFnKopf × (FnSig × SAnw) × (FnSig × SAnw) × (FnSig × SAnw))) :=
  let annahmen := ms.filterMap fun
    | .assumT n _ _ _ => some n
    | _ => none
  match uSeq ((ms.filterMap fun
    | .accT n t m cnt q => some (.accT n t m cnt q)
    | _ => none).map (uAkkuGenEintrag annahmen consts alias)) with
  | .error e => .error e
  | .ok gen =>
    if (uEindeutig (gen.map fun g => g.1.name)).length != gen.length then
      .error "duplicate accumulator without G form"
    else .ok gen

end Gabbro.Grammatik.Parser.Uebersetze
