module


public import Grammatik.Parser.Namen.Aufloesung.Teil1a
import all Init.Data.Repr
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

@[expose] public section




namespace Gabbro.Grammatik.Parser.Aufloesung

open Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Namensraum (Pfad Quelle Platz aufloeseK)

set_option maxRecDepth 100000

/-- What resolution sees at a position: the unit's source, the module and the locals in scope. -/
structure Kontext where
  q : Quelle
  von : Pfad
  lok : List String

/-- The context with more locals in scope. -/
def Kontext.mit (k : Kontext) (xs : List String) : Kontext := { k with lok := xs ++ k.lok }

/-- The text a written name that names nothing visible becomes: no item carries it, so the elaborator
    refuses it by name. -/
def gift (s : String) : String := "?" ++ s

/-- **A written name, resolved**: a local stays; else the key of the first visible candidate; else, if
    it is the short name of some item, poisoned; else (a built-in, a field, a ground) it stays. -/
def Kontext.ref (k : Kontext) (s : String) : String :=
  if k.lok.any (strEq · s) then s else
  match aufloeseK k.q ⟨none, []⟩ k.von (segmente s) with
  | some c => schluessel k.q.namen c
  | none => if k.q.namen.any (fun q => strEq (letzter q) (letzter (segmente s))) then gift s else s

/-- The key of an item declared here. -/
def Kontext.eigen (k : Kontext) (n : String) : String := schluessel k.q.namen (k.von ++ [n])

/-- A written path (`concurrent`, `dispatch`): one segment, its item's key. -/
def Kontext.pfad (k : Kontext) : Pfad → Pfad
  | [] => []
  | p => [k.ref ("::".intercalate p)]

/-- Whether a name names an item from here (and is no local). -/
def Kontext.nenntItem (k : Kontext) (p : Pfad) : Bool :=
  (aufloeseK k.q ⟨none, []⟩ k.von p).isSome

mutual
/-- **An expression, resolved.** -/
def aus (k : Kontext) : SExpr → SExpr
  | .variable s => .variable (k.ref s)
  | .field x f => .field (aus k x) f
  | .index x i => .index (aus k x) (aus k i)
  | .arrow x f => .arrow (aus k x) f
  | .un o x => .un o (aus k x)
  | .bin o x y => .bin o (aus k x) (aus k y)
  | .call f xs => .call (k.ref f) (ausL k xs)
  | .fnref p => .fnref (k.ref p)
  | .built f xs => .built f (ausL k xs)
  | .old x => .old (aus k x)
  | .why g f =>
    -- `R::F` with `R` an item (a reason) is a ground; `m::x` with `m` a module is a place path.
    if k.lok.any (strEq · g) || k.nenntItem [g] then .why (k.ref g) f
    else match aufloeseK k.q ⟨none, []⟩ k.von [g, f] with
      | some c => .variable (schluessel k.q.namen c)
      | none => .why g f
  | .ext .all (x :: d :: ns) xs => .ext .all (x :: d :: ns.map k.ref) (ausL (k.mit [x]) xs)
  | .ext .any (x :: d :: ns) xs => .ext .any (x :: d :: ns.map k.ref) (ausL (k.mit [x]) xs)
  | .ext .count (x :: d :: ns) xs => .ext .count (x :: d :: ns.map k.ref) (ausL (k.mit [x]) xs)
  | .ext .mem (d :: ns) xs => .ext .mem (d :: ns.map k.ref) (ausL k xs)
  | .ext w ns xs => .ext w ns (ausL k xs)
  | e => e
def ausL (k : Kontext) : List SExpr → List SExpr
  | [] => []
  | x :: xs => aus k x :: ausL k xs
end

/-- An optional expression, resolved. -/
def ausO (k : Kontext) : Option SExpr → Option SExpr
  | some e => some (aus k e)
  | none => none

/-- **A type, resolved.** -/
def typ (k : Kontext) : STyp → STyp
  | .atom s => .atom (k.ref s)
  | .path ps => if k.nenntItem ps then .atom (k.ref ("::".intercalate ps)) else .path ps
  | .ptr r w t => .ptr r w (typ k t)
  | .index o t => .index o (k.ref t)
  | .range b lo hi x => .range (typ k b) (aus k lo) (aus k hi) x
  | .array t n => .array (typ k t) (aus k n)
  | .wrap t => .wrap (typ k t)
  | .embed b s x => .embed (typ k b) s (ausO k x)
  | .str e => .str (aus k e)
  | .entry s (some t) => .entry s (some (typ k t))
  | t => t

/-- An optional type, resolved. -/
def typO (k : Kontext) : Option STyp → Option STyp
  | some t => some (typ k t)
  | none => none

/-- **An effect, resolved**: the places, and the arena of `allocs`. -/
def effekt (k : Kontext) : SEffekt → SEffekt
  | .reads e => .reads (aus k e)
  | .writes e => .writes (aus k e)
  | .locks s e => .locks s (aus k e)
  | .allocs n => .allocs (k.ref n)
  | .takes e => .takes (aus k e)
  | .posts e => .posts (aus k e)
  | e => e

/-- **A contract clause, resolved.** -/
def klausel (k : Kontext) : SKlausel → SKlausel
  | .needs e => .needs (aus k e)
  | .gives e => .gives (aus k e)
  | .refs ns => .refs (ns.map k.ref)
  | .cost e => .cost (aus k e)
  | .drops e => .drops (aus k e)
  | .load p => .load (k.pfad p)
  | .effs es => .effs (es.map (effekt k))
  | c => c

/-- The names a statement binds for the statements after it. -/
def gebunden : SAnw → List String
  | .bind _ x _ _ => [x]
  | .bindElse x _ _ _ _ => [x]
  | .bindQ _ x _ _ => [x]
  | .bindLib _ x _ _ => [x]
  | .alloc _ x _ _ _ _ => [x]
  | .allocVon _ x _ _ => [x]
  | .await x _ _ _ => [x]
  | .swap x _ _ _ => [x]
  | _ => []

/-- An ender, resolved. -/
def ende (k : Kontext) : Option SEnde → Option SEnde
  | some (.ret e) => some (.ret (ausO k e))
  | e => e

/-- Resolve the target and the ordinary arguments; the compile-time input remains byte-for-token exact.
    Paths resolve as paths: the library qualifier and the qualified function name each become their
    item key (`k.pfad` is the singleton key, as for every other resolved path). -/
def libraryCall (k : Kontext) (c : SLibraryCall) : SLibraryCall :=
  { c with library := k.pfad c.library
           function := k.pfad (c.library ++ c.function)
           args := c.args.map (aus k) }

mutual
/-- **A statement, resolved**; the statements of a block see the names the earlier ones bind. -/
def anw (k : Kontext) : SAnw → SAnw
  | .bind m x t e => .bind m x (typO k t) (aus k e)
  | .bindElse x t e g s => .bindElse x (typO k t) (aus k e) g (anw k s)
  | .bindQ m x t e => .bindQ m x (typO k t) (aus k e)
  | .bindLib m x t c => .bindLib m x (typO k t) (libraryCall k c)
  | .lcall c => .lcall (libraryCall k c)
  | .set l o r => .set (aus k l) o (aus k r)
  | .shift p a b => .shift (aus k p) a b
  | .call f xs => .call (k.ref f) (xs.map (aus k))
  | .callQ f xs => .callQ (k.ref f) (xs.map (aus k))
  | .cond c t es none => .cond (aus k c) (anw k t) (anwL k es) none
  | .cond c t es (some e) => .cond (aus k c) (anw k t) (anwL k es) (some (anw k e))
  | .elsif c s => .elsif (aus k c) (anw k s)
  | .cases e arms => .cases (aus k e) (anwL k arms)
  | .arm g b s => .arm g b (anw (k.mit b.toList) s)
  | .each b o d s m r i body =>
    .each b (ausO k o) d (aus k s) m r (ausO (k.mit [b]) i) (anw (k.mit [b]) body)
  | .retry l s => .retry l (anw k s)
  | .loop l s => .loop l (anw k s)
  | .waive gs s => .waive gs (anw k s)
  | .trim e g s => .trim (aus k e) g (anw k s)
  | .locks sh p s => .locks sh (aus k p) (anw k s)
  | .watch d s => .watch (k.ref d) (anw k s)
  | .emit a b p => .emit (aus k a) (aus k b) p
  | .await x t e p => .await x t (aus k e) p
  | .swap x t e w => .swap x t (aus k e) w
  | .ret e => .ret (ausO k e)
  | .alloc m x t a e none => .alloc m x (typO k t) (k.ref a) (aus k e) none
  | .alloc m x t a e (some s) => .alloc m x (typO k t) (k.ref a) (aus k e) (some (anw k s))
  | .reset a none => .reset (k.ref a) none
  | .reset a (some (x, y)) => .reset (k.ref a) (some (aus k x, aus k y))
  | .grow a e s => .grow (k.ref a) (aus k e) (anw k s)
  | .free e => .free (aus k e)
  | .child s => .child (anw k s)
  | .start fs => .start (fs.map k.ref)
  | .block ss e => .block (anwL k ss) (ende (k.mit (ss.flatMap gebunden)) e)
  | .allocVon m x t a => .allocVon m x (typO k t) (k.ref a)
  | s => s
def anwL (k : Kontext) : List SAnw → List SAnw
  | [] => []
  | s :: ss => anw k s :: anwL (k.mit (gebunden s)) ss
end

/-- **A function head, resolved**: its own key; parameters are locals of its clauses. -/
def sig (k : Kontext) (s : FnSig) : FnSig :=
  let k' := k.mit (s.params.map Prod.fst)
  { s with
    name := k.eigen s.name
    params := s.params.map fun (n, t) => (n, typ k t)
    res := typO k s.res
    fehler := s.fehler.map k.ref
    klauseln := s.klauseln.map (klausel k') }

mutual
/-- A constant value, resolved. -/
def konst (k : Kontext) : SKonstWert → SKonstWert
  | .one e => .one (aus k e)
  | .rows vs => .rows (konstL k vs)
def konstL (k : Kontext) : List SKonstWert → List SKonstWert
  | [] => []
  | v :: vs => konst k v :: konstL k vs
end

/-- An invariant, resolved. -/
def inv (k : Kontext) (i : SGruppenInv) : SGruppenInv :=
  { i with kosten := aus k i.kosten, pred := aus k i.pred }

/-- A table member, resolved. -/
def tabTeil (k : Kontext) : STabTeil → STabTeil
  | .tConst n t v => .tConst n (typ k t) (konst k v)
  | .tSlot fs => .tSlot (fs.map fun f => { f with ftyp := typ k f.ftyp, wo := ausO k f.wo })
  | .tInv i => .tInv (inv k i)
  | t => t

end Gabbro.Grammatik.Parser.Aufloesung
