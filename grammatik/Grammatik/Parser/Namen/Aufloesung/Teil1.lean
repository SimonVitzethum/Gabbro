module

public import Grammatik.Parser.Stmt.BoundedRewrite
public import Grammatik.Parser.Namen.Aufloesung.Teil1a
public import Grammatik.Parser.Item.ElementTief.FunctionArguments
public import Grammatik.Parser.Namen.References
public import Grammatik.Parser.Namen.Gebunden
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

structure Kontext where
  q : Quelle
  von : Pfad
  lok : List String
  /-- Checked module instances override keys without changing lexical lookup or local binders. -/
  keys : List (Pfad × String) := []

def Kontext.key (k : Kontext) (path : Pfad) : String :=
  match k.keys.find? (fun entry => entry.1 == path) with
  | some entry => entry.2
  | none => schluessel k.q.namen path

/-- Count short names once per source unit, rather than once per declaration/reference.
    Explicit instance-key overrides retain their first-match order. -/
def Kontext.keySchnell (k : Kontext) (path : Pfad) : String :=
  match k.keys.find? (fun entry => entry.1 == path) with
  | some entry => entry.2
  | none => if k.q.shortCount (letzter path) == 1 then letzter path else "::".intercalate path

@[csimp] theorem Kontext.key_eq_schnell : Kontext.key = Kontext.keySchnell := by
  funext k path
  simp only [Kontext.key, Kontext.keySchnell, schluessel, Quelle.shortCount_eq, letzter]
  rfl

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
  | some c => k.key c
  | none => if k.q.namen.any (fun q => strEq (letzter q) (letzter (segmente s))) then gift s else s

/-- Unknown names (including builtin type names) need a short-name membership test too.
    Without this indexed fallback, each `u32` in a multi-module unit still scans every item. -/
def Kontext.refSchnell (k : Kontext) (s : String) : String :=
  if k.lok.any (strEq · s) then s else
  match aufloeseK k.q ⟨none, []⟩ k.von (segmente s) with
  | some c => k.key c
  | none => if 0 < k.q.shortCount (letzter (segmente s)) then gift s else s

@[csimp] theorem Kontext.ref_eq_schnell : Kontext.ref = Kontext.refSchnell := by
  funext k s
  simp only [Kontext.ref, Kontext.refSchnell, letzter, ← Quelle.shortCount_positive]
  rfl

/-- The key of an item declared here. -/
def Kontext.eigen (k : Kontext) (n : String) : String := k.key (k.von ++ [n])

/-- A written path (`concurrent`, `dispatch`): one segment, its item's key. -/
def Kontext.pfad (k : Kontext) : Pfad → Pfad
  | [] => []
  | p => [k.ref ("::".intercalate p)]

/-- Whether a name names an item from here (and is no local). -/
def Kontext.nenntItem (k : Kontext) (p : Pfad) : Bool :=
  (aufloeseK k.q ⟨none, []⟩ k.von p).isSome


/-- A spec call resolves its group prefix; ordinary qualified function paths resolve as before. -/
def Kontext.ruf (k : Kontext) (s : String) : String :=
  let p := segmente s
  if k.nenntItem p then k.ref s
  else if p.length > 1 && k.nenntItem p.dropLast then
    k.ref ("::".intercalate p.dropLast) ++ "::" ++ letzter p
  else k.ref s

/-- Explicit argument groups are resolved in the caller's scope before generic expansion. Paths
    are kept whole; field names following `.`/`->` remain members rather than global references. -/
def genericArgumentTokens (k : Kontext) : Nat → List Token → List Token
  | 0, tokens => tokens
  | _ + 1, [] => []
  | fuel + 1, .zeichen dot :: field :: rest =>
    if dot == "." || dot == "->" then
      .zeichen dot :: field :: genericArgumentTokens k fuel rest
    else .zeichen dot :: genericArgumentTokens k fuel (field :: rest)
  | fuel + 1, token :: rest => match nameText token with
    | some name =>
      let (path, tail) := sammleSegmente rest [name]
      let text := String.intercalate "::" path
      let resolved := k.ref text
      let head := if path.length == 1 && strEq resolved text then token else .ident resolved
      head :: genericArgumentTokens k fuel tail
    | none => token :: genericArgumentTokens k fuel rest

def genericArgument (k : Kontext) (word : String) : String :=
  match lex word with
  | .error _ => word
  | .ok tokens =>
    let k := match parseFunctionArgument (tokens.length * 4 + 32) tokens with
      | .ok (.literal sig body) =>
        { k with lok := sig.params.map Prod.fst ++ literalLocals body }
      | _ => k
    let tokens := tokens.filter (fun | .ende => false | _ => true)
    String.intercalate " " ((genericArgumentTokens k (tokens.length + 1) tokens).map zeigeTok)

private theorem take_size_le {α : Type} [SizeOf α] (count : Nat) (values : List α) :
    sizeOf (values.take count) ≤ sizeOf values := by
  induction values generalizing count with
  | nil => simpa only [List.take_nil] using Nat.le_refl (sizeOf ([] : List α))
  | cons value values ih =>
    cases count with
    | zero => simp only [List.take_zero, List.nil.sizeOf_spec, List.cons.sizeOf_spec]; omega
    | succ count =>
      have rest := ih count
      simp only [List.take_succ_cons, List.cons.sizeOf_spec]
      omega

private theorem drop_size_le {α : Type} [SizeOf α] (count : Nat) (values : List α) :
    sizeOf (values.drop count) ≤ sizeOf values := by
  induction values generalizing count with
  | nil => simpa only [List.drop_nil] using Nat.le_refl (sizeOf ([] : List α))
  | cons value values ih =>
    cases count with
    | zero => simpa only [List.drop_zero] using Nat.le_refl (sizeOf (value :: values))
    | succ count =>
      have rest := ih count
      simp only [List.drop_succ_cons, List.cons.sizeOf_spec]
      omega

mutual
/-- **An expression, resolved.** -/
def aus (k : Kontext) : SExpr → SExpr
  | .variable s => .variable (k.ref s)
  | .field x f => .field (aus k x) f
  | .index x i => .index (aus k x) (aus k i)
  | .arrow x f => .arrow (aus k x) f
  | .un o x => .un o (aus k x)
  | .bin o x y => .bin o (aus k x) (aus k y)
  | .call f xs => .call (k.ruf f) (ausL k xs)
  | .fnref p => .fnref (k.ref p)
  | .built f xs => .built f (ausL k xs)
  | .old x => .old (aus k x)
  | .why g f =>
    -- `R::F` with `R` an item (a reason) is a ground; `m::x` with `m` a module is a place path.
    if k.lok.any (strEq · g) || k.nenntItem [g] then .why (k.ref g) f
    else match aufloeseK k.q ⟨none, []⟩ k.von [g, f] with
      | some c => .variable (k.key c)
      | none => .why g f
  | .ext .instantiate (name :: words) xs =>
    .ext .instantiate (k.ruf name :: words.map (genericArgument k)) (ausL k xs)
  | .ext .all (x :: d :: ns) xs => .ext .all (x :: d :: ns.map k.ref) (ausL (k.mit [x]) xs)
  | .ext .any (x :: d :: ns) xs => .ext .any (x :: d :: ns.map k.ref) (ausL (k.mit [x]) xs)
  | .ext .count (x :: d :: ns) xs => .ext .count (x :: d :: ns.map k.ref) (ausL (k.mit [x]) xs)
  | .ext .dyn [n] xs => .ext .dyn [k.ref n] (ausL k xs)
  | .ext .mem (d :: ns) xs => .ext .mem (d :: ns.map k.ref) (ausL k xs)
  | .ext kind (binder :: domain :: names) args =>
    if kind == .foldAdd || kind == .foldMin || kind == .foldMax || kind == .foldAnd || kind == .foldOr then
      let count := if domain == "range" then 2 else 1
      have domainSize : sizeOf (args.take count) ≤ sizeOf args := by
        exact take_size_le count args
      have bodySize : sizeOf ((args.drop count).take 2) ≤ sizeOf args := by
        exact Nat.le_trans (take_size_le 2 (args.drop count)) (drop_size_le count args)
      have tailSize : sizeOf (args.drop ((if domain = "range" then 2 else 1) + 2)) ≤ sizeOf args := by
        simpa only [count, List.drop_drop, beq_iff_eq] using
          Nat.le_trans (drop_size_le 2 (args.drop count)) (drop_size_le count args)
      .ext kind (binder :: domain :: names.map k.ref)
        (ausL k (args.take count) ++ ausL (k.mit [binder]) ((args.drop count).take 2) ++
          ausL k ((args.drop count).drop 2))
    else .ext kind (binder :: domain :: names) (ausL k args)
  | .ext w ns xs => .ext w ns (ausL k xs)
  | e => e
termination_by expression => sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals try simp only [List.drop_drop] at *
  all_goals first
    | omega
    | (by_cases hDomain : domain = "range" <;> simp_all [count, hDomain] <;> omega)
def ausL (k : Kontext) : List SExpr → List SExpr
  | [] => []
  | x :: xs => aus k x :: ausL k xs
termination_by expressions => sizeOf expressions
decreasing_by
  all_goals simp_wf
  all_goals omega
end

/-- An optional expression, resolved. -/
def ausO (k : Kontext) : Option SExpr → Option SExpr
  | some e => some (aus k e)
  | none => none

mutual
/-- **A type, resolved.** -/
def typ (k : Kontext) : STyp → STyp
  | .dyn n raw => .dyn (k.ref n) (raw.map (genericArgument k))
  | .atom s => .atom (k.ref s)
  | .tuple types => .tuple (typList k types)
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
termination_by structural ty => ty

/-- Resolve tuple components in source order. -/
def typList (k : Kontext) : List STyp → List STyp
  | [] => []
  | ty :: rest => typ k ty :: typList k rest
termination_by structural ts => ts
end

/-- The structural traversal agrees with the original map traversal. -/
theorem typList_eq_map (k : Kontext) (ts : List STyp) :
    typList k ts = ts.map (typ k) := by
  induction ts with
  | nil => rfl
  | cons head rest ih => simp only [typList, List.map_cons, ih]

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
  | .borrows n => .borrows (k.ref n)
  | .moves n => .moves (k.ref n)
  | .mints n => .mints (k.ref n)
  | .takes e => .takes (aus k e)
  | .posts e => .posts (aus k e)
  | .instanceEffects n ts => .instanceEffects (k.ref n) (ts.map (typ k))
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
  | .bindAxiomOpt x t e => .bindAxiomOpt x (typO k t) (aus k e)
  | .bindAxiomOptElse x t e g s => .bindAxiomOptElse x (typO k t) (aus k e) g (anw k s)
  | .bindLib m x t c => .bindLib m x (typO k t) (libraryCall k c)
  | .lcall c => .lcall (libraryCall k c)
  | .set l o r => .set (aus k l) o (aus k r)
  | .shift p a b => .shift (aus k p) a b
  | .call f xs => .call (k.ruf f) (xs.map (aus k))
  | .callIndElse p xs reason body => .callIndElse (aus k p) (xs.map (aus k)) reason (anw (k.mit [reason]) body)
  | .callElse f xs reason body => .callElse (k.ruf f) (xs.map (aus k)) reason (anw (k.mit [reason]) body)
  | .callQ f xs => .callQ (k.ruf f) (xs.map (aus k))
  | .cond c t es none => .cond (aus k c) (anw k t) (anwL k es) none
  | .cond c t es (some e) => .cond (aus k c) (anw k t) (anwL k es) (some (anw k e))
  | .elsif c s => .elsif (aus k c) (anw k s)
  | .cases e arms => .cases (aus k e) (anwL k arms)
  | .arm g b s => .arm g b (anw (k.mit b.toList) s)
  | .each b o d s m r i body =>
    .each b (ausO k o) d (aus k s) m r (ausO (k.mit [b]) i) (anw (k.mit [b]) body)
  | .boundedLoop raw body =>
    .boundedLoop (mapBoundedHeader (aus k) k.ruf raw)
      (anw (k.mit ((boundedLoopLocals raw).map Prod.fst)) body)
  | .retry l s => .retry l (anw k s)
  | .loop l s => .loop l (anw k s)
  | .waive gs s => .waive gs (anw k s)
  | .trim e g s => .trim (aus k e) g (anw k s)
  | .trimReq e g => .trimReq (aus k e) g
  | .locks sh p s => .locks sh (aus k p) (anw k s)
  | .watch d s => .watch (k.ref d) (anw k s)
  | .retires m => .retires (k.ref m)
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
  | .genericCall name words args => .genericCall (k.ruf name) (words.map (genericArgument k)) (args.map (aus k))
  | .allocVon m x t a => .allocVon m x (typO k t) (k.ref a)
  | s => s
def anwL (k : Kontext) : List SAnw → List SAnw
  | [] => []
  | s :: ss => anw k s :: anwL (k.mit (gebunden s)) ss
end

/-- **A function head, resolved**: its own key; parameters are locals of its clauses. -/
def sig (k : Kontext) (s : FnSig) : FnSig :=
  let k' := k.mit (s.generics.map SGenericParam.name ++ s.params.map Prod.fst)
  { s with
    name := k.eigen s.name
    params := s.params.map fun (n, t) => (n, typ k' t)
    res := typO k' s.res
    fehler := s.fehler.map k.ref
    klauseln := s.klauseln.map (klausel k')
    generics := s.generics.map fun
      | .type n bounds => .type n (bounds.map k.ref)
      | .constant n ty => .constant n (typ k' ty)
      | .function n (.raw raw) => .function n (.raw (genericArgument k' raw))
      | .function n ty => .function n (typ k' ty) }

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
  { i with pred := aus k i.pred }

/-- A table member, resolved. -/
def tabTeil (k : Kontext) : STabTeil → STabTeil
  | .tConst n t v => .tConst n (typ k t) (konst k v)
  | .tSlot fs => .tSlot (fs.map fun f => { f with ftyp := typ k f.ftyp, wo := ausO k f.wo })
  | .tInv i => .tInv (inv k i)
  | t => t

end Gabbro.Grammatik.Parser.Aufloesung
