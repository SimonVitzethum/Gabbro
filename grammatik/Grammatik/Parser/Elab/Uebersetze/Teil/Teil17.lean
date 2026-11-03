module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil11
public import Grammatik.Bausteine.Kernzelle.Belegung

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-! ## C15 storage expansion: `accumulates` to guarded cells

    An admitted `accumulates n : T merge op per cpu e` becomes `N` private
    globals (`n#zelle<i>`, neutral-initialized, mutable) and `N` exclusive
    locks (`n#sperre<i>`, each guarding its cell, increasing ranks from a base
    above the unit's locks). The descriptor, admission and neutral
    initialization are checked model-side (`Kernzelle.AccumulatorAdmission`,
    `AkkuStart`); the core query, updates and reads stay refused (they need
    the C08 core-query contract, task 4). -/

/-- The `per cpu` count, evaluated: a positive constant (`uAnzahl`). -/
def uAkkuAnzahl (consts : List (String × Int)) : Option SExpr → Except String Nat
  | none => .error "accumulator without per cpu count without G form"
  | some e =>
    match uAnzahl consts e with
    | .error err => .error err
    | .ok n =>
      if 1 ≤ n then .ok n.toNat
      else .error "accumulator with non-positive core count without G form"

/-- The value range of an accumulator: an integer range (`uErgBereich`).
    Floats and other types are refused by name (F004). -/
def uAkkuBereich (alias : List (String × (Int × Int))) (t : STyp) :
    Except String (Int × Int) :=
  match uErgBereich alias t with
  | .ok r => .ok r
  | .error _ => .error "accumulator over a non-integer type without G form (F004)"

/-- Storage width and signedness derived from the declared mathematical range. -/
def uAkkuFormat (lo hi : Int) : Nat × Bool :=
  if lo < 0 then
    (Nat.log2 (max ((-lo - 1).toNat) hi.toNat) + 2, true)
  else (Nat.log2 hi.toNat + 1, false)

/-- Neutral initialization at the derived storage width. Signed bitwise
    ranges remain refused because the model uses nonnegative encodings. -/
def uAkkuNeutral (m : String) (lo hi : Int) : Except String Int :=
  if strEq m "max" then .ok lo
  else if strEq m "min" then .ok hi
  else if strEq m "add" then .ok 0
  else if strEq m "or" then .ok 0
  else if strEq m "and" then
    if lo < 0 then .error "signed accumulator and without G form: nonnegative encoding required"
    else .ok ((2 ^ (uAkkuFormat lo hi).1 - 1 : Nat) : Int)
  else .error "accumulator operator without G form"

theorem uAkkuNeutralAndByte_zeuge : uAkkuNeutral "and" 0 255 = .ok 255 := by decide

/-- The generated cell names (`n#zelle<i>`). -/
def uAkkuZellen (n : String) (k : Nat) : List String :=
  (List.range k).map fun i => n ++ "#zelle" ++ toString i

/-- One admitted item to its storage: cells plus their guarding locks (ranks
    from `boden`, increasing with the index so the reduction's index-order
    acquisition respects the rank order). -/
def uAkkuItem (consts : List (String × Int)) (alias : List (String × (Int × Int)))
    (boden : Int) : SItemTief → Except String (List UGlob × List ULock)
  | .accT n t m p _ =>
    match uAkkuAnzahl consts p with
    | .error e => .error e
    | .ok k =>
      match uAkkuBereich alias t with
      | .error e => .error e
      | .ok (lo, hi) =>
        match uAkkuNeutral m lo hi with
        | .error e => .error e
        | .ok z =>
          if !(lo ≤ z && z ≤ hi) then
            .error "accumulator neutral outside its range without G form"
          else if !(akkuOperatorOk m) then .error "accumulator operator without G form"
          else .ok ((uAkkuZellen n k).map fun c => { name := c, ty := .int lo hi, init := z, var := true, breite := (uAkkuFormat lo hi).1 }, (List.range k).map fun i => { name := n ++ "#sperre" ++ toString i, rank := boden + Int.ofNat i, guard := [n ++ "#zelle" ++ toString i] })
  | _ => .ok ([], [])

/-- Export a source descriptor once its generated carriers and function bindings
    have been resolved. Bindings are explicit: no placeholder core query or
    update/reduction function is invented by the storage expansion. -/
def uAkkuDecl {D : Deklaration}
    (consts : List (String × Int)) (alias : List (String × (Int × Int)))
    (item : SItemTief)
    (cells : (k : Nat) → Fin k → D.Glob)
    (locks : (k : Nat) → Fin k → D.Lock)
    (query update fold : D.Fn) : Except String (Kernzelle.AccumulatorDecl D) := do
  let .accT name ty merge count _ := item
    | .error "expected accumulator declaration"
  let k ← uAkkuAnzahl consts count
  let (lo, hi) ← uAkkuBereich alias ty
  let neutral ← uAkkuNeutral merge lo hi
  if !(lo ≤ neutral && neutral ≤ hi) then
    throw "accumulator neutral outside its range without G form"
  let op ←
    if strEq merge "max" then pure Kernzelle.AccOperator.max
    else if strEq merge "min" then pure Kernzelle.AccOperator.min
    else if strEq merge "add" then pure Kernzelle.AccOperator.add
    else if strEq merge "or" then pure Kernzelle.AccOperator.or
    else if strEq merge "and" then pure Kernzelle.AccOperator.and
    else throw "accumulator operator without G form"
  return { name := name, kernZahl := k, breite := (uAkkuFormat lo hi).1,
    vorzeichen := (uAkkuFormat lo hi).2, lo := lo, hi := hi, op := op,
    zellen := cells k, sperren := locks k, kernAbfrage := query,
    aktualisiere := update, falte := fold }

/-- The storage of every admitted `accumulates` item of the unit. -/
def uAkkuErweiterung (consts : List (String × Int)) (alias : List (String × (Int × Int)))
    (boden : Int) : List SItemTief → Except String (List UGlob × List ULock)
  | [] => .ok ([], [])
  | it :: rest =>
    match uAkkuItem consts alias boden it with
    | .error e => .error e
    | .ok (gs, ls) =>
      match uAkkuErweiterung consts alias boden rest with
      | .error e => .error e
      | .ok (gs', ls') => .ok (gs ++ gs', ls ++ ls')

/-! ## Uses expand to the generated functions

    The generated cells are `n#zelle<i>`; the source name `n` is no global, so
    any update or read of `n` expands before resolution (`Akku.Expand`):
    `n = v` becomes the update call `n#aktualisiere(v)`, `let x = n` and
    `return n` become the sampled fold `n#falte()`, and `reads`/`writes n`
    effects name every cell. The scan below detects the remaining mentions
    for the expansion's narrow refusals (a nested read, a compound update,
    a contract clause, a foreign signature); whatever it misses still fails
    later as an unknown name -- never silently accepted.

    Why the core query stays generated: C08's query contract must return exactly
    a `Fin N`-equivalent bounded value with a boundary record identifying the
    executing core at that query, tied to the same declared core assignment
    the scheduler uses. A Rust thread number, a modulo reduction or a
    constant `0` is not evidence; only the generated `n#kern` foreign body,
    with its exact shape, is. Migration after the query does not reselect
    the destination: the sampled value is bound once per source update. -/

/-- Whether an expression mentions an accumulator name. -/
def uAkkuInExpr : Nat → List String → SExpr → Bool
  | 0, _, _ => false
  | _ + 1, ns, .variable n => ns.any fun m => strEq m n
  | f + 1, ns, .field x _ => uAkkuInExpr f ns x
  | f + 1, ns, .index x i => uAkkuInExpr f ns x || uAkkuInExpr f ns i
  | f + 1, ns, .arrow x _ => uAkkuInExpr f ns x
  | f + 1, ns, .un _ x => uAkkuInExpr f ns x
  | f + 1, ns, .bin _ x y => uAkkuInExpr f ns x || uAkkuInExpr f ns y
  | f + 1, ns, .genericCall g _ args =>
    (ns.any fun m => strEq m g) || (args.any fun a => uAkkuInExpr f ns a)
  | f + 1, ns, .call g args =>
    (ns.any fun m => strEq m g) || (args.any fun a => uAkkuInExpr f ns a)
  | f + 1, ns, .fnref g => ns.any fun m => strEq m g
  | f + 1, ns, .built g args =>
    (ns.any fun m => strEq m g) || (args.any fun a => uAkkuInExpr f ns a)
  | f + 1, ns, .old x => uAkkuInExpr f ns x
  | f + 1, ns, .ext _ _ xs => xs.any fun a => uAkkuInExpr f ns a
  | _, _, _ => false

/-- Whether an effect mentions an accumulator name. -/
def uAkkuInEffekt : Nat → List String → SEffekt → Bool
  | 0, _, _ => false
  | f + 1, ns, .reads e => uAkkuInExpr f ns e
  | f + 1, ns, .writes e => uAkkuInExpr f ns e
  | f + 1, ns, .locks _ e => uAkkuInExpr f ns e
  | f + 1, ns, .takes e => uAkkuInExpr f ns e
  | f + 1, ns, .posts e => uAkkuInExpr f ns e
  | _, _, _ => false

/-- Whether a contract clause mentions an accumulator name. -/
def uAkkuInKlausel : Nat → List String → SKlausel → Bool
  | 0, _, _ => false
  | f + 1, ns, .needs e => uAkkuInExpr f ns e
  | f + 1, ns, .gives e => uAkkuInExpr f ns e
  | f + 1, ns, .cost e => uAkkuInExpr f ns e
  | f + 1, ns, .drops e => uAkkuInExpr f ns e
  | f + 1, ns, .effs es => es.any fun e => uAkkuInEffekt f ns e
  | _, _, _ => false

/-- Whether the clauses mention an accumulator name. -/
def uAkkuInKlauseln : Nat → List String → List SKlausel → Bool
  | _, _, [] => false
  | f, ns, k :: ks => uAkkuInKlausel f ns k || uAkkuInKlauseln f ns ks

/-- Whether an ender mentions an accumulator name. -/
def uAkkuInEnde : Nat → List String → SEnde → Bool
  | 0, _, _ => false
  | f + 1, ns, .ret none => false
  | f + 1, ns, .ret (some e) => uAkkuInExpr f ns e
  | _, _, _ => false

/-- Whether an ender option mentions an accumulator name. -/
def uAkkuInEndeOpt : Nat → List String → Option SEnde → Bool
  | _, _, none => false
  | f, ns, some e => uAkkuInEnde f ns e

/-- Whether a body mentions an accumulator name (best-effort; whatever this
    misses still fails later as an unknown name). -/
def uAkkuInAnw : Nat → List String → SAnw → Bool
  | 0, _, _ => false
  | f + 1, ns, .bind _ x _ e =>
    (ns.any fun m => strEq m x) || uAkkuInExpr f ns e
  | f + 1, ns, .bindElse x _ e _ b =>
    (ns.any fun m => strEq m x) || uAkkuInExpr f ns e || uAkkuInAnw f ns b
  | f + 1, ns, .set x _ y => uAkkuInExpr f ns x || uAkkuInExpr f ns y
  | f + 1, ns, .call g args =>
    (ns.any fun m => strEq m g) || (args.any fun a => uAkkuInExpr f ns a)
  | f + 1, ns, .cond c t ei els =>
    uAkkuInExpr f ns c || uAkkuInAnw f ns t || (ei.any fun b => uAkkuInAnw f ns b) ||
    (match els with | none => false | some b => uAkkuInAnw f ns b)
  | f + 1, ns, .elsif c b => uAkkuInExpr f ns c || uAkkuInAnw f ns b
  | f + 1, ns, .cases e arms => uAkkuInExpr f ns e || (arms.any fun b => uAkkuInAnw f ns b)
  | f + 1, ns, .arm _ _ b => uAkkuInAnw f ns b
  | f + 1, ns, .each _ s _ e _ _ _ b =>
    (match s with | none => false | some x => uAkkuInExpr f ns x) || uAkkuInExpr f ns e ||
    uAkkuInAnw f ns b
  | f + 1, ns, .retry _ b => uAkkuInAnw f ns b
  | f + 1, ns, .loop _ b => uAkkuInAnw f ns b
  | f + 1, ns, .trim e _ b => uAkkuInExpr f ns e || uAkkuInAnw f ns b
  | f + 1, ns, .trimReq e _ => uAkkuInExpr f ns e
  | f + 1, ns, .locks _ e b => uAkkuInExpr f ns e || uAkkuInAnw f ns b
  | f + 1, ns, .grow _ e b => uAkkuInExpr f ns e || uAkkuInAnw f ns b
  | f + 1, ns, .child b => uAkkuInAnw f ns b
  | f + 1, ns, .block ss ende =>
    (ss.any fun b => uAkkuInAnw f ns b) || uAkkuInEndeOpt f ns ende
  | f + 1, ns, .ret e =>
    (match e with | none => false | some x => uAkkuInExpr f ns x)
  | f + 1, ns, .alloc _ x _ _ e _ =>
    (ns.any fun m => strEq m x) || uAkkuInExpr f ns e
  | _, _, _ => false

/-- Whether the signatures mention an accumulator name (for the expansion's
    narrow refusals: foreign signatures never go through the update or fold). -/
def uAkkuInSigs : Nat → List String → List FnSig → Bool
  | _, _, [] => false
  | f, ns, s :: ss => uAkkuInKlauseln f ns s.klauseln || uAkkuInSigs f ns ss

end Gabbro.Grammatik.Parser.Uebersetze
