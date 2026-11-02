module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil11

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

/-- The neutral element of the operator over the range: `max` starts at the
    floor, `min` at the ceiling, `add`/`or` at zero. `and` needs the stored
    width for its all-ones pattern -- still refused, by name. -/
def uAkkuNeutral (m : String) (lo hi : Int) : Except String Int :=
  if strEq m "max" then .ok lo
  else if strEq m "min" then .ok hi
  else if strEq m "add" then .ok 0
  else if strEq m "or" then .ok 0
  else if strEq m "and" then
    .error "accumulator and without G form: the width-indexed neutral needs the stored width (staged)"
  else .error "accumulator operator without G form"

/-- The generated cell names (`n#zelle<i>`). -/
def uAkkuZellen (n : String) (k : Nat) : List String :=
  (List.range k).map fun i => n ++ "#zelle" ++ toString i

/-- One admitted item to its storage: cells plus their guarding locks (ranks
    from `boden`, increasing with the index so the reduction's index-order
    acquisition respects the rank order). -/
def uAkkuItem (consts : List (String × Int)) (alias : List (String × (Int × Int)))
    (boden : Int) : SItemTief → Except String (List UGlob × List ULock)
  | .accT n t m p =>
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
          else .ok ((uAkkuZellen n k).map fun c => { name := c, ty := .int lo hi, init := z, var := true }, (List.range k).map fun i => { name := n ++ "#sperre" ++ toString i, rank := boden + Int.ofNat i, guard := [n ++ "#zelle" ++ toString i] })
  | _ => .ok ([], [])

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

/-! ## Uses stay refused: the core query needs C08 (task 4)

    The generated cells are `n#zelle<i>`; the source name `n` is no global, so
    any update or read of `n` fails resolution. The scan below turns that
    into a NAMED refusal (core query and per-cell lock protocol, task 4);
    whatever it misses still fails later as an unknown name -- never
    silently accepted.

    Why the core query stays refused: C08's query contract must return exactly
    a `Fin N`-equivalent bounded value with a boundary record identifying the
    executing core at that query, tied to the same declared core assignment
    the scheduler uses. A Rust thread number, a modulo reduction or a
    constant `0` is not evidence; migration after the query must not reselect
    the destination (or a proved pinned scope must span query and store).
    None of that exists without C08's software boundary and grant history. -/

/-- The accumulator names of the unit. -/
def uAkkuNamen : List SItemTief → List String
  | [] => []
  | .accT n _ _ _ :: rest => n :: uAkkuNamen rest
  | _ :: rest => uAkkuNamen rest

/-- Whether an expression mentions an accumulator name. -/
def uAkkuInExpr : Nat → List String → SExpr → Bool
  | 0, _, _ => false
  | _ + 1, ns, .variable n => ns.any fun m => strEq m n
  | f + 1, ns, .field x _ => uAkkuInExpr f ns x
  | f + 1, ns, .index x i => uAkkuInExpr f ns x || uAkkuInExpr f ns i
  | f + 1, ns, .arrow x _ => uAkkuInExpr f ns x
  | f + 1, ns, .un _ x => uAkkuInExpr f ns x
  | f + 1, ns, .bin _ x y => uAkkuInExpr f ns x || uAkkuInExpr f ns y
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

/-- Whether the signatures mention an accumulator name. -/
def uAkkuInSigs : Nat → List String → List FnSig → Bool
  | _, _, [] => false
  | f, ns, s :: ss => uAkkuInKlauseln f ns s.klauseln || uAkkuInSigs f ns ss

/-- A unit whose bodies or contracts mention an accumulator is refused by name:
    updates read the core (C08), reductions fold under quiescence -- neither
    is connected. -/
def uAkkuVerwendung (ns : List String) : List (FnSig × SAnw) → Except String Unit
  | [] => .ok ()
  | (sig, b) :: rest =>
    if uAkkuInKlauseln 100000 ns sig.klauseln || uAkkuInAnw 100000 ns b then
      .error "accumulator update/read without G form: the core query (C08) and per-cell lock protocol are not connected"
    else uAkkuVerwendung ns rest

/-- Foreign signatures mentioning an accumulator are refused by the same name. -/
def uAkkuFremdVerwendung (ns : List String) (sigs : List FnSig) : Except String Unit :=
  if uAkkuInSigs 100000 ns sigs then
    .error "accumulator update/read without G form: the core query (C08) and per-cell lock protocol are not connected"
  else .ok ()

end Gabbro.Grammatik.Parser.Uebersetze
