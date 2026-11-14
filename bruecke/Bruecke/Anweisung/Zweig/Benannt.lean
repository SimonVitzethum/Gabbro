module
public import Bruecke.Anweisung.Lokal.Benannt
public import Bruecke.Anweisung.Lokal.Kopf
public import Bruecke.Anweisung.Bereich.Basis
public import Bruecke.Anweisung.Schleife.Basis
public import Bruecke.Anweisung.Match.Basis
@[expose] public section

/-!
# Branch reading with a function-wide identifier supply

A block returns its statements, unconsumed source statements and allocation history.
The then arm, else arm and continuation use that history in sequence. Each starts with
the enclosing active identifiers; names of block-local entries never escape their scope.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

/-- The active list is scoped; the returned allocation history is function-wide. -/
def seqZ (u : UProg) : Nat → UFn → BodyNames → List UStmt →
    Option (List Gabbro.Body.Stmt × List UStmt × List String)
  | 0, _, _, _ => none
  | _ + 1, _, ns, [] => some ([], [], ns.used)
  | _ + 1, _, ns, .blkEnd :: rest => some ([], .blkEnd :: rest, ns.used)
  | _ + 1, _, ns, .ifElse :: rest => some ([], .ifElse :: rest, ns.used)
  | k + 1, fn, ns, .ifBeg c :: rest
  | k + 1, fn, ns, .ifEnde c :: rest =>
      match condZ u fn ns c with
      | none => none
      | some ce =>
        match seqZ u k fn ns rest with
        | some (tb, .ifElse :: rest1, used1) =>
          match seqZ u k fn (ns.resume used1) rest1 with
          | some (eb, .blkEnd :: rest2, used2) =>
            (seqZ u k fn (ns.resume used2) rest2).map
              (fun p => (.ite ce tb eb :: p.1, p.2.1, p.2.2))
          | _ => none
        | _ => none
  | k + 1, fn, ns, .loopBeg x tab .tru :: rest => do
      if !loopWritesB rest then none else do
        let t ← (tabIdx u.tabs tab).toOption
        let (body, .blkEnd :: tail, used) ← seqZ u k
          (fn.mitIndex x t.val ((declOf u).count t)) (ns.push x) rest | none
        let p ← seqZ u k fn (ns.resume used) tail
        pure (.forEach (ns.fresh x) (loopIndices u t) body :: p.1, p.2.1, p.2.2)
  | k + 1, fn, ns, .narrowBeg x lo hi :: rest => do
      let e ← narrowName fn ns x
      let (err, .blkEnd :: tail) ← endBodyZ u k fn ns rest | none
      let p ← seqZ u k (fn.mitBindung x (lo, hi)) (ns.push x) tail
      pure (narrowStep ns x lo hi e err :: p.1, p.2.1, p.2.2)
  | k + 1, fn, ns, .ret r :: rest =>
      match retZ u fn ns r with
      | none => none
      | some b => (seqZ u k fn ns rest).map (fun p => (b :: p.1, p.2.1, p.2.2))
  | k + 1, fn, ns, st :: rest =>
      match schrittB u fn ns st with
      | some (b, fn', ns') =>
        (seqZ u k fn' ns' rest).map (fun p => (b :: p.1, p.2.1, p.2.2))
      | none => none

/-- Finite reason arms reuse the ordinary scoped block reader and its allocation history. -/
def reasonArmsZ (u : UProg) (k : Nat) (fn : UFn) : Nat → Nat → BodyNames → List UStmt →
    Option (List (String × List Gabbro.Body.Stmt) × List UStmt × List String)
  | 0, _, ns, ss => some ([], ss, ns.used)
  | n + 1, offset, ns, ss => do
      let (body, remaining, allocated) ← seqZ u k fn ns ss
      match n with
      | 0 => pure ([(caseLabel offset, body)], remaining, allocated)
      | m + 1 =>
        let .ifElse :: tail := remaining | none
        let (arms, rest, used) ← reasonArmsZ u k fn (m + 1) (offset + 1) (ns.resume allocated) tail
        pure ((caseLabel offset, body) :: arms, rest, used)

/-- Read a whole function, retaining allocation history across both arms and the continuation. -/
def stmtsBodyZ (u : UProg) : Nat → UFn → BodyNames → List UStmt → URet →
    Option (List Gabbro.Body.Stmt)
  | 0, _, _, _, _ => none
  | _ + 1, fn, ns, [], r => namedEnd u fn ns r
  | k + 1, fn, ns, .ifBeg c :: rest, r =>
      match condZ u fn ns c with
      | none => none
      | some ce =>
        match seqZ u k fn ns rest with
        | some (tb, .ifElse :: rest1, used1) =>
          match seqZ u k fn (ns.resume used1) rest1 with
          | some (eb, .blkEnd :: rest2, used2) =>
            (stmtsBodyZ u k fn (ns.resume used2) rest2 r).map (.ite ce tb eb :: ·)
          | _ => none
        | _ => none
  | k + 1, fn, ns, .matchTagBeg sidx x _ :: rest, r =>
      if sidx < u.sums.length then do
        let (cs, e) ← tagSubject fn ns x
        let (arms, .blkEnd :: tail, allocated) ← reasonArmsZ u k fn cs.length 0 ns rest | none
        let ys ← stmtsBodyZ u k fn (ns.resume allocated) tail r
        pure (.onTag e (tagArms arms) :: ys)
      else none
  | k + 1, fn, ns, .matchWhyBeg x :: rest, r => do
      let (count, e) ← reasonSubject fn ns x
      let (arms, .blkEnd :: tail, allocated) ← reasonArmsZ u k fn count 0 ns rest | none
      let ys ← stmtsBodyZ u k fn (ns.resume allocated) tail r
      pure (.onReason e arms :: ys)
  | k + 1, fn, ns, .matchBeg num v x :: rest, r =>
      if hn : num < u.tabs.length then do
        let e ← optionZ fn ns v
        let (pb, .ifElse :: r1, used1) ← seqZ u k
          (fn.mitIndex x num ((declOf u).count ⟨num, hn⟩)) (ns.push x) rest | none
        let (ab, .blkEnd :: r2, used2) ← seqZ u k fn (ns.resume used1) r1 | none
        let ys ← stmtsBodyZ u k fn (ns.resume used2) r2 r
        pure (.onOption e (ns.fresh x) pb ab :: ys)
      else none
  | k + 1, fn, ns, .loopBeg x tab .tru :: rest, r => do
      if !loopWritesB rest then none else do
        let t ← (tabIdx u.tabs tab).toOption
        let (body, .blkEnd :: tail, used) ← seqZ u k
          (fn.mitIndex x t.val ((declOf u).count t)) (ns.push x) rest | none
        let bs ← stmtsBodyZ u k fn (ns.resume used) tail r
        pure (.forEach (ns.fresh x) (loopIndices u t) body :: bs)
  | k + 1, fn, ns, .narrowBeg x lo hi :: rest, r => do
      let e ← narrowName fn ns x
      let (err, .blkEnd :: tail) ← endBodyZ u k fn ns rest | none
      let bs ← stmtsBodyZ u k (fn.mitBindung x (lo, hi)) (ns.push x) tail r
      pure (narrowStep ns x lo hi e err :: bs)
  -- An explicitly typed record local shares the positional identifier mechanism.
  -- Inferred aggregates and aggregate binders inside structured blocks remain refused.
  | k + 1, fn, ns, .bindW x (some ty@(.prod ..)) v :: rest, r =>
      match namedSide u fn ns v with
      | none => none
      | some e => (stmtsBodyZ u k (fn.mitWert x ty) (ns.push x) rest r).map
          (.bindName (ns.fresh x) e :: ·)
  | _ + 1, _, _, .bindW .. :: _, _ => none
  | k + 1, fn, ns, st :: rest, r =>
      match schrittB u fn ns st with
      | some (b, fn', ns') => (stmtsBodyZ u k fn' ns' rest r).map (b :: ·)
      | none => none

/-- The canonical whole-function reader starts in the declared entry scope. -/
def zuBodyZ (u : UProg) (f : UFn) : Option (List Gabbro.Body.Stmt) :=
  stmtsBodyZ u (f.body.length + 1) f (BodyNames.start f) f.body f.ret

end Gabbro.Bruecke
