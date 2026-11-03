module

import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ExportMetadata
import all Init.Data.Repr
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil15

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

def beqUEnsList : List UEns → List UEns → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqUEns x y && beqUEnsList xs ys
  | _, _ => false

def beqUArg : UArg → UArg → Bool
  | .var a, .var b => strEq a b
  | .freshPtr a w, .freshPtr b v => strEq a b && decide (w = v)
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
  | .bindOptBeg x c a, .bindOptBeg y d b => strEq x y && strEq c d && beqUArgList a b
  | .bindOptElseBeg x c a e, .bindOptElseBeg y d b f =>
    strEq x y && strEq c d && beqUArgList a b && strEq e f
  | .axCallElseBeg c a e, .axCallElseBeg d b f => strEq c d && beqUArgList a b && strEq e f
  | .retires a, .retires b => strEq a b
  | .advances a b, .advances c d => strEq a c && strEq b d
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
  | .resetRange a x n, .resetRange b y m =>
    strEq a b && beqUSide x y && beqUSide n m
  | .floatLit a q lo hi, .floatLit b r low high =>
    strEq a b && decide (q = r) && decide (lo = low) && decide (hi = high)
  | .float a op x y lo hi, .float b other z w low high =>
    strEq a b && decide (op = other) && beqUSide x z && beqUSide y w &&
      decide (lo = low) && decide (hi = high)
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
  | .bindCallIndElse a p f xs e, .bindCallIndElse b q g ys h =>
    strEq a b && strEq p q && strEq f g && beqUArgList xs ys && strEq e h
  | .allocReqBeg a t s, .allocReqBeg b u v => strEq a b && strEq t u && beqUSide s v
  | _, _ => false

def beqUStmtList : List UStmt → List UStmt → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqUStmt x y && beqUStmtList xs ys
  | _, _ => false

def beqUParamArt : UParamArt → UParamArt → Bool
  | .ptr a, .ptr b => decide (a = b)
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
    decide (a.regs = b.regs) && decide (a.records = b.records)

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
    uParams104 uExp104 "einzahlen" = [.ptr (.table 0 (true, true)), .index 2, .int 0 10] ∧
    r4D.params r4Ein = [.ptr (.table 0 (true, true)), .index 2, .int 0 10] ∧
    uParams104 uExp104 "lies" = [.ptr (.table 0 (true, false)), .index 2] ∧
    r4D.params r4Lies = [.ptr (.table 0 (true, false)), .index 2] ∧
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
