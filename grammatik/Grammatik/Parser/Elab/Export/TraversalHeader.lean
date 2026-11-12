/-
  The `touches` header of an ordinary traversal, bound to the enclosing function's effects.

  `Stmt.traverse` has no component for the header, so the elaborator drops it. The gate may
  admit it only when the claim follows from something the checker verifies: the function's
  declared effects bound every effect of its body, hence of the loop. If every declared effect
  is listed in the header, the header's claim "the loop touches at most these" is implied.
-/
module
public import Grammatik.Parser.Item.ElementTief
import all Init.Data.String.Basic
import all Init.Data.String.Defs
@[expose] public section

namespace Gabbro.Grammatik.Parser.ExportMetadata

/-- The effects a `touches …` header lists; any other or trailing clause is refused. -/
def touchesHeader (raw : String) : Except String (List SEffekt) := do
  let tokens ← match lex raw with
    | .ok ts => pure ts
    | .error _ => throw "traversal header does not lex"
  let rest ← match tokens with
    | .wort "touches" :: rest => pure rest
    | _ => throw "traversal header is not a touches clause"
  let (effects, rest) ← parseEffektListe 10000 rest
  match rest with
  | [.ende] => pure effects
  | _ => throw "traversal header has an unsupported or duplicate clause"

/-- The declared effects the contract tracks. `pure` declares none, and a read is no right of
    the signature (`Signatur` records writes, held locks and marks only), so a header owes
    nothing for it. -/
def declaredEffects (clauses : List SKlausel) : List SEffekt :=
  (clauses.flatMap fun | .effs effects => effects | _ => []).filter fun
    | .pure | .reads _ => false
    | _ => true

/-- An empty header claims nothing. A written header is covered when it lists every effect
    the function declares. -/
def touchesCovered (clauses : List SKlausel) (raw : String) : Bool :=
  raw == "" || match touchesHeader raw with
    | .ok listed => (declaredEffects clauses).all fun e => listed.any (beqSEffekt e)
    | .error _ => false

/-- An empty header is covered by every function. -/
theorem touchesCovered_empty (clauses : List SKlausel) : touchesCovered clauses "" = true := rfl

/-- A covered written header lists every declared effect. -/
theorem touchesCovered_sound (clauses : List SKlausel) (raw : String) (written : raw ≠ "")
    (covered : touchesCovered clauses raw = true) :
    ∃ listed, touchesHeader raw = .ok listed ∧
      ∀ e ∈ declaredEffects clauses, ∃ l ∈ listed, beqSEffekt e l = true := by
  unfold touchesCovered at covered
  have notEmpty : (raw == "") = false := by simpa using written
  rw [notEmpty, Bool.false_or] at covered
  cases parsed : touchesHeader raw with
  | error e => rw [parsed] at covered; cases covered
  | ok listed =>
    rw [parsed] at covered
    refine ⟨listed, rfl, fun e member => ?_⟩
    exact List.any_eq_true.mp (List.all_eq_true.mp covered e member)

/-- The header of the corpus loops is covered by the same declared effect, an unlisted declared
    effect is not, and a header with a second clause is refused. -/
theorem touchesCovered_zeuge :
    touchesCovered [.effs [.reads (.field (.variable "t") "slots"), .writes (.field (.variable "t") "slots")]]
      "touches writes t.slots" = true ∧
    touchesCovered [.effs [.reads (.field (.variable "t") "slots"), .writes (.variable "g")]]
      "touches reads t.slots" = false ∧
    touchesCovered [] "touches reads t.slots decreases n" = false := by
  decide +kernel

/-- An expression without a call, a function address or a quantifier-like extension: it
    reads only. Builtins are the pure operators of the language. -/
def callFree : Nat → SExpr → Bool
  | 0, _ => false
  | _ + 1, .lit _ | _ + 1, .float _ | _ + 1, .tru | _ + 1, .fls | _ + 1, .variable _ | _ + 1, .res
  | _ + 1, .why _ _ => true
  | n + 1, .field e _ | n + 1, .arrow e _ | n + 1, .un _ e | n + 1, .old e => callFree n e
  | n + 1, .index a b | n + 1, .bin _ a b => callFree n a && callFree n b
  | n + 1, .built _ args => args.all (callFree n)
  -- `Some` and `None` are keywords: the two constructors of an option, no call.
  | n + 1, .call name args => (name == "Some" || name == "None") && args.all (callFree n)
  | _ + 1, .fnref _ | _ + 1, .ext .. => false

/-- The write an assignment target performs: a static, or a slot field of a table or pointer. -/
def writeTarget : SExpr → Option SEffekt
  | .variable g => some (.writes (.variable g))
  | .field (.index (.field base kind) _) _ =>
    if kind == "slots" then some (.writes (.field base "slots")) else none
  | _ => none

/-- The writes and lock takes of a loop body made of bindings, assignments, branches, narrowing, sections, nested
    traversals and exits; any other statement is not analysed (`none`). -/
def bodyWrites : Nat → SAnw → Option (List SEffekt)
  | 0, _ => none
  | n + 1, .block ss _ => (ss.mapM (bodyWrites n)).map List.flatten
  | _ + 1, .set target _ value => if callFree 10000 target && callFree 10000 value then
      (writeTarget target).map fun w => [w] else none
  | _ + 1, .shift target _ _ => if callFree 10000 target then (writeTarget target).map fun w => [w] else none
  | n + 1, .cond c a bs b => if callFree 10000 c then do
      let first ← bodyWrites n a
      let middle ← bs.mapM (bodyWrites n)
      let last ← match b with
        | some e => bodyWrites n e
        | none => some []
      pure (first ++ middle.flatten ++ last) else none
  | n + 1, .elsif c b | n + 1, .trim c _ b => if callFree 10000 c then bodyWrites n b else none
  | n + 1, .arm _ _ b => bodyWrites n b
  | n + 1, .cases e arms => if callFree 10000 e then (arms.mapM (bodyWrites n)).map List.flatten else none
  | n + 1, .each _ origin _ subject _ _ inv body =>
    if origin.all (callFree 10000) && callFree 10000 subject && inv.all (callFree 10000) then
      bodyWrites n body else none
  | _ + 1, .bind _ _ _ e | _ + 1, .trimReq e _ => if callFree 10000 e then some [] else none
  | _ + 1, .ret e => if e.all (callFree 10000) then some [] else none
  | _ + 1, .leave _ | _ + 1, .next _ => some []
  -- An atomic exchange and an atomic store write their static; an await reads.
  | _ + 1, .swap _ _ (.variable a) _ => some [.writes (.variable a)]
  | _ + 1, .await .. => some []
  | _ + 1, .emit (.variable a) value _ => if callFree 10000 value then some [.writes (.variable a)] else none
  -- A section takes its lock: the header must list it, and what the section writes.
  | n + 1, .locks shared lock b => (bodyWrites n b).map fun ws => .locks shared lock :: ws
  | _ + 1, _ => none

/-- A written header is verified against the loop itself when every expression of the body is
    call-free and every write it performs is listed: such an expression writes nothing, and the
    analysed statements write only by assignment. An assignment to a local in scope at the loop
    (`locals`) is no effect. -/
def touchesVerified (raw : String) (body : SAnw) (locals : List String := []) : Bool :=
  match touchesHeader raw, bodyWrites 10000 body with
  | .ok listed, some writes => writes.all fun w =>
    (match w with | .writes (.variable x) => locals.contains x | _ => false) || listed.any (beqSEffekt w)
  | _, _ => false

/-- A header is admitted when the function's declared effects imply it or the loop verifies it. -/
def touchesAdmitted (clauses : List SKlausel) (locals : List String) (raw : String) (body : SAnw) : Bool :=
  touchesCovered clauses raw || touchesVerified raw body locals

/-- A loop that assigns one static verifies a header listing it, although the function also
    writes a table; a header that omits the assigned static, or a body with a call, does not. -/
theorem touchesVerified_zeuge :
    touchesVerified "touches reads t.slots, writes sum"
      (.block [.set (.variable "sum") "=" (.lit 1)] none) = true ∧
    touchesVerified "touches reads t.slots"
      (.block [.set (.variable "sum") "=" (.lit 1)] none) = false ∧
    touchesVerified "touches writes sum"
      (.block [.set (.variable "sum") "=" (.call "f" [])] none) = false := by
  decide +kernel

/-- The word of a header token. -/
def headerWord : Token → Option String
  | .wort w | .ident w => some w
  | _ => none

/-- The words that open a section of a `retry` or `forever` header (`uSchleifenWort`). -/
def sectionWord (t : Token) : Bool :=
  match headerWord t with
  | some w => ["until", "bounded", "per_pass", "progress", "on_exceeded", "effects", "leaves"].contains w
  | none => false

/-- A `retry` header whose every clause the elaborator reads (`uRetryKopf`): an optional label,
    `until` with a brace-free condition, then exactly `bounded N ops progress A on_exceeded F`.
    No other section can stand in such a header, so no clause is dropped. -/
def retryHeaderBound (raw : String) : Bool :=
  match lex raw with
  | .error _ => false
  | .ok tokens =>
    let tokens := tokens.filter fun t => t != .ende
    let label := tokens.takeWhile fun t => !sectionWord t
    match tokens.dropWhile fun t => !sectionWord t with
    | opener :: rest =>
      let condition := rest.takeWhile fun t => !sectionWord t
      label.length ≤ 1 && headerWord opener == some "until" && !condition.isEmpty &&
        (condition.all fun t => t != .zeichen "{" && t != .zeichen "}") &&
        match rest.dropWhile fun t => !sectionWord t with
        | [b, .num _, unit, p, a, o, y] =>
          headerWord b == some "bounded" && headerWord unit == some "ops" &&
            headerWord p == some "progress" && (headerWord a).isSome && !sectionWord a &&
            headerWord o == some "on_exceeded" && (headerWord y).isSome && !sectionWord y
        | _ => false
    | [] => false

/-- The header of the corpus loops is bound; one with a further section or without `progress` is not. -/
theorem retryHeaderBound_zeuge :
    retryHeaderBound "attempt until false bounded 3 ops progress tick on_exceeded sched_yield" = true ∧
    retryHeaderBound "attempt until false bounded 3 ops progress tick on_exceeded sched_yield effects { pure }" = false ∧
    retryHeaderBound "attempt until false bounded 3 ops on_exceeded sched_yield" = false := by
  decide +kernel

/-- A `forever` header the gate binds: an optional label, then exactly
    `per_pass bounded N ops on_exceeded stopped effects { … } progress A`. -/
structure ForeverKopf where
  label : String
  /-- The declared bound of one pass, checked against the lowered body (`ForeverBinding.holds`). -/
  bound : Nat
  /-- The declared effects as a `touches` header, verified against the body. -/
  effects : String
  progress : String

/-- Read a `forever` header of the bound shape. `on_exceeded stopped` is the only handler: the pass
    bound is checked statically, so the handler is never reached. -/
def foreverHeader (raw : String) : Option ForeverKopf :=
  match lex raw with
  | .error _ => none
  | .ok tokens =>
    let tokens := tokens.filter fun t => t != .ende
    let label := tokens.takeWhile fun t => !sectionWord t
    if label.length > 1 then none else
    match tokens.dropWhile fun t => !sectionWord t with
    | p :: b :: .num n :: unit :: o :: s :: e :: .zeichen "{" :: tail =>
      let listed := tail.takeWhile fun t => t != .zeichen "}"
      match tail.dropWhile fun t => t != .zeichen "}" with
      | [.zeichen "}", pw, a] =>
        if headerWord p == some "per_pass" && headerWord b == some "bounded" &&
            headerWord unit == some "ops" && headerWord o == some "on_exceeded" &&
            headerWord s == some "stopped" && headerWord e == some "effects" &&
            headerWord pw == some "progress" && !sectionWord a then
          (headerWord a).map fun name =>
            ⟨String.intercalate " " (label.map zeigeTok), n,
              "touches " ++ String.intercalate " " (listed.map zeigeTok), name⟩
        else none
      | _ => none
    | _ => none

/-- The header the elaborator reads completely: an optional label and `progress A` (`uForeverKopf`). -/
def foreverPlain (raw : String) : Bool :=
  match lex raw with
  | .error _ => false
  | .ok tokens =>
    let tokens := tokens.filter fun t => t != .ende
    (tokens.takeWhile fun t => !sectionWord t).length ≤ 1 &&
      match tokens.dropWhile fun t => !sectionWord t with
      | [pw, a] => headerWord pw == some "progress" && (headerWord a).isSome && !sectionWord a
      | _ => false

/-- The plain header of a bound one. -/
def ForeverKopf.plain (k : ForeverKopf) : String := k.label ++ " progress " ++ k.progress

/-- The header of the corpus loops is bound and its plain form is read completely; a header with
    another handler, or without the pass bound, is not bound. -/
theorem foreverHeader_zeuge :
    ((foreverHeader "service per_pass bounded 16 ops on_exceeded stopped effects { pure } progress tick").map
      fun k => (k.label, k.bound, k.effects, k.progress, foreverPlain k.plain)) =
        some ("service", 16, "touches pure", "tick", true) ∧
    (foreverHeader "service per_pass bounded 16 ops on_exceeded halt effects { pure } progress tick").isNone = true ∧
    (foreverHeader "service per_pass bounded 16 ms on_exceeded stopped effects { pure } progress tick").isNone = true ∧
    (foreverHeader "service effects { pure } progress tick").isNone = true ∧
    foreverPlain "service per_pass bounded 16 ops on_exceeded stopped effects { pure } progress tick" = false := by
  decide +kernel

/-- The names a statement binds for the rest of its block. -/
def binders : SAnw → List String
  | .bind _ x _ _ | .bindQ _ x _ _ | .bindElse x _ _ _ _ | .bindAxiomOpt x _ _
  | .bindAxiomOptElse x _ _ _ _ | .await x _ _ _ | .swap x _ _ _ | .bindLib _ x _ _ => [x]
  | _ => []

/-- Erase every covered `touches` header of an ordinary traversal, in every position the gate
    inspects; a header that is not covered stays and is refused by the gate. `locals` are the
    names in scope: the parameters and the bindings of the enclosing blocks before the statement. -/
def eraseCovered (covered : List String → String → SAnw → Bool) : List String → Nat → SAnw → SAnw
  | _, 0, s => s
  | locals, n + 1, .block ss e =>
    .block (ss.foldl (fun (acc : List SAnw × List String) s =>
      (eraseCovered covered acc.2 n s :: acc.1, binders s ++ acc.2)) ([], locals)).1.reverse e
  | locals, n + 1, .bindElse a ty c d b => .bindElse a ty c d (eraseCovered covered (d :: locals) n b)
  | locals, n + 1, .bindAxiomOptElse a ty c d b =>
    .bindAxiomOptElse a ty c d (eraseCovered covered (d :: locals) n b)
  | locals, n + 1, .callIndElse a b c body => .callIndElse a b c (eraseCovered covered locals n body)
  | locals, n + 1, .callElse a b c body => .callElse a b c (eraseCovered covered locals n body)
  | locals, n + 1, .waive a b => .waive a (eraseCovered covered locals n b)
  | locals, n + 1, .locks a b c => .locks a b (eraseCovered covered locals n c)
  | locals, n + 1, .watch a b => .watch a (eraseCovered covered locals n b)
  | locals, n + 1, .retry header b => .retry header (eraseCovered covered locals n b)
  | locals, n + 1, .trim a b c => .trim a b (eraseCovered covered locals n c)
  | locals, n + 1, .cond c a bs b => .cond c (eraseCovered covered locals n a)
      (bs.map (eraseCovered covered locals n)) (b.map (eraseCovered covered locals n))
  | locals, n + 1, .elsif c b => .elsif c (eraseCovered covered locals n b)
  | locals, n + 1, .arm a b c => .arm a b (eraseCovered covered (b.toList ++ locals) n c)
  | locals, n + 1, .cases a arms => .cases a (arms.map (eraseCovered covered locals n))
  | locals, n + 1, .each a b c d mode raw inv body =>
    .each a b c d mode (if mode == "unvisited" && covered (a :: locals) raw body then "" else raw) inv
      (eraseCovered covered (a :: locals) n body)
  -- A bound `forever` header whose effects the body keeps is replaced by its plain form.
  | locals, n + 1, .loop header body =>
    .loop (match foreverHeader header with
      | some k => if covered locals k.effects body then k.plain else header
      | none => header) (eraseCovered covered locals n body)
  | locals, n + 1, .alloc m x ty an v (some body) =>
    .alloc m x ty an v (some (eraseCovered covered locals n body))
  | _, _ + 1, s => s

/-- A covered header of an ordinary traversal is erased, an uncovered one and a consuming header stay. -/
theorem eraseCovered_zeuge (body : SAnw) :
    eraseCovered (fun _ raw _ => raw == "h") [] 2 (.each "i" none "slots" (.variable "t") "unvisited" "h" none body) =
      .each "i" none "slots" (.variable "t") "unvisited" "" none (eraseCovered (fun _ raw _ => raw == "h") ["i"] 1 body) ∧
    eraseCovered (fun _ raw _ => raw == "h") [] 2 (.each "i" none "slots" (.variable "t") "unvisited" "x" none body) =
      .each "i" none "slots" (.variable "t") "unvisited" "x" none (eraseCovered (fun _ raw _ => raw == "h") ["i"] 1 body) ∧
    eraseCovered (fun _ raw _ => raw == "h") [] 2 (.each "i" none "slots" (.variable "t") "consuming" "h" none body) =
      .each "i" none "slots" (.variable "t") "consuming" "h" none (eraseCovered (fun _ raw _ => raw == "h") ["i"] 1 body) :=
  ⟨rfl, rfl, rfl⟩

/-- A loop that adds into a local of the enclosing block verifies a header that lists no write;
    the same assignment to a name that is no local in scope does not. -/
theorem touchesVerified_local_zeuge :
    touchesVerified "touches reads t.slots" (.block [.set (.variable "total") "=" (.lit 1)] none)
      ["total"] = true ∧
    touchesVerified "touches reads t.slots" (.block [.set (.variable "total") "=" (.lit 1)] none)
      [] = false := by
  decide +kernel

end Gabbro.Grammatik.Parser.ExportMetadata
