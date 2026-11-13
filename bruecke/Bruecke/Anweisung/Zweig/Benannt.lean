module
public import Bruecke.Anweisung.Lokal.Benannt
public import Bruecke.Anweisung.Zweig.Uebersetzung
@[expose] public section

/-!
# Branch reading with a function-wide identifier supply

A block returns its statements, unconsumed source statements and allocation history.
The then arm, else arm and continuation use that history in sequence. Each starts with
the enclosing active identifiers; names of block-local entries never escape their scope.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik.Parser.Uebersetze

def condZ (u : UProg) (fn : UFn) (ns : BodyNames) (c : UEns) :
    Option Gabbro.Body.Expr :=
  (rawCond u fn c).bind (renameScalar (ns.lookup fn))

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
  | k + 1, fn, ns, .ret r :: rest =>
      match retZ u fn ns r with
      | none => none
      | some b => (seqZ u k fn ns rest).map (fun p => (b :: p.1, p.2.1, p.2.2))
  | k + 1, fn, ns, st :: rest =>
      match schrittB u fn ns st with
      | some (b, fn', ns') =>
        (seqZ u k fn' ns' rest).map (fun p => (b :: p.1, p.2.1, p.2.2))
      | none => none

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
  | k + 1, fn, ns, st :: rest, r =>
      match schrittB u fn ns st with
      | some (b, fn', ns') => (stmtsBodyZ u k fn' ns' rest r).map (b :: ·)
      | none => none

/-- The canonical whole-function reader starts in the declared entry scope. -/
def zuBodyZ (u : UProg) (f : UFn) : Option (List Gabbro.Body.Stmt) :=
  stmtsBodyZ u (f.body.length + 1) f (BodyNames.start f) f.body f.ret

end Gabbro.Bruecke
