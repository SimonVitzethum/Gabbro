module

public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.Teil15

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

def beqUEns : UEns → UEns → Bool
  | .cmp o a b, .cmp p c d =>
    strEq o p && beqUSide a c && beqUSide b d
  | .tru, .tru => true
  | .fls, .fls => true
  | .and a b, .and c d => beqUEns a c && beqUEns b d
  | .or a b, .or c d => beqUEns a c && beqUEns b d
  | .not a, .not b => beqUEns a b
  | .slotB a f x, .slotB b g y | .tabB a f x, .tabB b g y =>
    strEq a b && strEq f g && beqUIdx x y
  | .globB a, .globB b => strEq a b
  | .alle t x p, .alle s y q | .einige t x p, .einige s y q => strEq t s && strEq x y && beqUEns p q
  | .ergB, .ergB => true
  | .held a, .held b => strEq a b
  | .imp a b, .imp c d => beqUEns a c && beqUEns b d
  | .reach t f a b, .reach u g c d => strEq t u && strEq f g && a == c && b == d
  | .member t a, .member u b => strEq t u && a == b
  | .arrayElements a source x body, .arrayElements b target y other =>
      a == b && beqUSide source target && strEq x y && beqUEns body other
  | .filtered a t x f r s b, .filtered c u y g v z d =>
      a == c && strEq t u && strEq x y && strEq f g && r == v && s == z && beqUEns b d
  | .istSome o m, .istSome p n => o == p && m == n
  | _, _ => false

def beqUEnsList : List UEns → List UEns → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqUEns x y && beqUEnsList xs ys
  | _, _ => false

def beqUArg : UArg → UArg → Bool
  | .var a, .var b => strEq a b
  | .freshPtr a w, .freshPtr b v => strEq a b && w == v
  | .val a, .val b => beqUSide a b
  | .fnref a, .fnref b => strEq a b
  | _, _ => false

def beqUArgList : List UArg → List UArg → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqUArg x y && beqUArgList xs ys
  | _, _ => false

def beqURet : URet → URet → Bool
  | .empty, .empty => true
  | .val a, .val b => beqUSide a b
  | .bool a, .bool b => beqUEns a b
  | _, _ => false

def beqUStmt : UStmt → UStmt → Bool
  | .assign a f x s, .assign b g y t =>
    strEq a b && strEq f g && beqUIdx x y && beqUSide s t
  | .assignTab a f x s, .assignTab b g y t =>
    strEq a b && strEq f g && beqUIdx x y && beqUSide s t
  | .assignB a f x s, .assignB b g y t | .assignTabB a f x s, .assignTabB b g y t =>
    strEq a b && strEq f g && beqUIdx x y && beqUEns s t
  | .assignGlob a s, .assignGlob b t => strEq a b && beqUSide s t
  | .assignGlobB a s, .assignGlobB b t => strEq a b && beqUEns s t
  | .storeAtom a s, .storeAtom b t => strEq a b && beqUSide s t
  | .storeAtomB a s, .storeAtomB b t => strEq a b && beqUEns s t
  | .call a xs, .call b ys => strEq a b && beqUArgList xs ys
  | .lockBeg a, .lockBeg b => strEq a b
  | .blkEnd, .blkEnd => true
  | .bind a d s, .bind b e t => strEq a b && beqOptIntPair d e && beqUSide s t
  | .ifBeg a, .ifBeg b => beqUEns a b
  | .ifElse, .ifElse => true
  | .loopBeg a t i, .loopBeg b u j => strEq a b && strEq t u && beqUEns i j
  | .arrayLoopBeg a source inv, .arrayLoopBeg b target other =>
      strEq a b && beqUSide source target && beqUEns inv other
  | .ret a, .ret b => beqURet a b
  | .leave a, .leave b | .next a, .next b => strEq a b
  | .regRead a d r, .regRead b e s | .regReadElse a d r, .regReadElse b e s =>
    strEq a b && strEq d e && strEq r s
  | .regWrite d r v, .regWrite e s w => strEq d e && strEq r s && beqUSide v w
  | .regWriteB d r v, .regWriteB e s w => strEq d e && strEq r s && beqUEns v w
  | .shiftTab a f x s v w, .shiftTab b g y z v' w' =>
    strEq a b && strEq f g && beqUIdx x y && strEq s z && v == v' && w == w'
  | .awaitBind a g, .awaitBind b h => strEq a b && strEq g h
  | .bindFnref a g n, .bindFnref b h m => strEq a b && strEq g h && n == m
  | .callInd p f xs, .callInd q g ys => strEq p q && strEq f g && beqUArgList xs ys
  | .bindCallInd a p f xs, .bindCallInd b q g ys => strEq a b && strEq p q && strEq f g && beqUArgList xs ys
  | _, _ => false

def beqUStmtList : List UStmt → List UStmt → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqUStmt x y && beqUStmtList xs ys
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
    beqFeldList a.cols b.cols && beqStrList a.bools b.bools

def beqUTabList : List UTab → List UTab → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqUTab x y && beqUTabList xs ys
  | _, _ => false

def beqULock : ULock → ULock → Bool
  | a, b => strEq a.name b.name && a.rank == b.rank &&
    beqStrList a.guard b.guard && a.masks == b.masks

def beqULockList : List ULock → List ULock → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqULock x y && beqULockList xs ys
  | _, _ => false

def beqUGlob : UGlob → UGlob → Bool
  | a, b => strEq a.name b.name && decide (a.ty = b.ty) && a.init == b.init && a.var == b.var && a.atomic == b.atomic

def beqUGlobList : List UGlob → List UGlob → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqUGlob x y && beqUGlobList xs ys
  | _, _ => false

def beqUFn : UFn → UFn → Bool
  | a, b => strEq a.name b.name &&
    beqTyParamList a.params b.params &&
    beqUParamArtList a.kinds b.kinds &&
    beqOptWeite a.res b.res && a.resBool == b.resBool &&
    beqStrList a.held b.held && beqStrList a.puts b.puts && beqStrList a.gputs b.gputs &&
    beqUEnsList a.gives b.gives &&
    beqUStmtList a.body b.body && beqURet a.ret b.ret && a.boden == b.boden &&
    beqUEnsList a.needs b.needs && decide (a.decreases = b.decreases) &&
    decide (a.measureConstants = b.measureConstants) &&
    decide (a.measureTypes = b.measureTypes)

def beqUFnList : List UFn → List UFn → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqUFn x y && beqUFnList xs ys
  | _, _ => false

def beqUProg : UProg → UProg → Bool
  | a, b => beqUTabList a.tabs b.tabs &&
    beqULockList a.locks b.locks && beqUFnList a.fns b.fns &&
    beqStrList a.roots b.roots && beqStrList a.hands b.hands && beqUGlobList a.globs b.globs &&
    decide (a.regs = b.regs)

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
      .ok (G104_referenz.gP, G104_referenz.gFs) := by rfl

/-- Projections of the elaborated program (the left column of
    the data agreement below). -/
def uAnzahl104 (u : UProg) : Int :=
  match u.tabs with
  | [t] => t.count
  | _ => -1

def uWeite104 (u : UProg) : Int × Int :=
  match u.tabs with
  | [{ name := _, count := _, cols := [(_, w)], bools := _, arena := _, opts := _, shared := _, von := _, werte := _, wraps := _, sumNamen := _, sumFelder := _, kanten := _, idxNamen := _, breiten := _ }] => w
  | _ => (-1, -1)

def uRang104 (u : UProg) : Int :=
  match u.locks with
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
  | .some f => f.puts
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
