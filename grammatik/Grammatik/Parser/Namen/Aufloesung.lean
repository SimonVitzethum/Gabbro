import Grammatik.Parser.Elab.Uebersetze
import Grammatik.Parser.Namen.Namensraum

/-!
  File:      Grammatik/Parser/Namen/Aufloesung.lean
  Subject:   **Qualified names of a unit**: every item is named by its full path, and every written
             name is resolved by the name-space rule (`Namensraum.aufloeseK`) before the elaborator
             sees the unit. Two modules may therefore declare items of the same short name -- two
             carriers, two functions, two types -- and stay two items.

  The language rule (SYNTAX.md `usedecl`, `place`), modelled here before the Rust checker follows:

  * **The identity of an item is its path** (module path and name). Short names need not be unique in
    a unit; two items of one path in one module stay a duplicate.
  * **A written name is resolved** where it stands: a local (parameter, `let`, binder) first, else the
    first candidate of `Namensraum.kandidaten` that names a declared item -- the using module and every
    enclosing one, innermost first, then the `use` lines of these modules. A name that resolves to
    nothing but is the short name of some item is refused (it names something not visible from here).
  * **A place head may be a path** (`writes a::C`, `a::C = 1`, `Held(m::L)`): a two-segment path that is
    no reason ground and every longer path names the item it resolves to.
  * After resolution each item carries its **key** (`schluessel`): its short name when no other item of
    the unit has that short name, else its full path joined by `::`. Every resolved reference carries
    the key of its item, so the elaborator, which looks names up by text, sees one text per item and
    the same text at every use. Keys of distinct paths are distinct texts: a short key has no `::`
    (identifiers never contain `:`), a joined key has at least one, and a short key is used only for a
    short name no other item has.
  * `use` items have done their work once the names are resolved and are dropped; module wrappers are
    opened and `pub` marks dropped (as `Uebersetze.uMembers` does; what `pub` demands is checked before,
    `Oeffentlich.lean`).

  A unit without `use` items and with at most one module wrapper (every unit of the corpus models before
  this change) is resolved by `uMembers` alone (`loese_einfach`): there every name is its own key.

  Positions read: every expression, type, effect, contract clause, statement and the item heads of the
  item kinds the elaborator gives a G form. A name at a position the pass does not rewrite keeps its
  text; if it is ambiguous, no item carries that text any more and the elaborator refuses the unit, so a
  missed position can refuse a unit, never bind a name to the wrong item.

  Theorems:
  * `loese_einfach` -- a unit with one name space is resolved as before.
  * `segmente_name` -- a plain name (no `:`) is the one-segment path.
  * `segmente_verbinde` -- a joined path splits back into its segments.
  * **`schluessel_injektiv`** -- distinct items carry distinct keys (segments are identifiers), so the
    elaborator never merges two items.
  * `ref_lokal`, `ref_aufgeloest`, `ref_unsichtbar` -- what a written name becomes: a local stays, a
    resolved name becomes its item's key, a name of an item not visible from here is poisoned.
  * `schluessel_kurz` -- an item whose short name is unique in the unit keeps its short name.
-/

namespace Gabbro.Grammatik.Parser.Aufloesung

open Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Namensraum (Pfad Quelle Platz aufloeseK)

set_option maxRecDepth 100000

/-- The segments of a character list split at `::` (`acc` holds the current segment, reversed). -/
def zerlegeZ : List Char → List Char → List (List Char)
  | [], acc => [acc.reverse]
  | ':' :: ':' :: rest, acc => acc.reverse :: zerlegeZ rest []
  | c :: rest, acc => zerlegeZ rest (c :: acc)

/-- The segments of a written path (`a::b::c`; a plain name is one segment). Structural over the
    characters, so the kernel reduces it (`String.splitOn` does not). -/
def segmente (s : String) : Pfad := (zerlegeZ s.toList []).map String.ofList

/-- One character other than `:` joins the current segment. -/
theorem zerlegeZ_cons {c : Char} (l acc : List Char) (hc : c ≠ ':') :
    zerlegeZ (c :: l) acc = zerlegeZ l (c :: acc) := by
  conv => lhs; rw [zerlegeZ.eq_def]
  split <;> simp_all

/-- Characters without `:` are one segment. -/
theorem zerlegeZ_ohne (l acc : List Char) (h : ':' ∉ l) : zerlegeZ l acc = [acc.reverse ++ l] := by
  induction l generalizing acc with
  | nil => simp [zerlegeZ]
  | cons c rest ih =>
    have hc : c ≠ ':' := fun e => h (e ▸ List.mem_cons_self)
    have hr : ':' ∉ rest := fun m => h (List.mem_cons_of_mem _ m)
    rw [zerlegeZ_cons _ _ hc, ih _ hr]
    simp

/-- **A plain name is one segment**: an identifier (no `:`) resolves as the one-segment path. -/
theorem segmente_name {s : String} (h : ':' ∉ s.toList) : segmente s = [s] := by
  simp [segmente, zerlegeZ_ohne _ _ h, String.ofList_toList]

/-- A segment without `:` followed by `::` closes the segment. -/
theorem zerlegeZ_trenner (l rest acc : List Char) (h : ':' ∉ l) :
    zerlegeZ (l ++ ':' :: ':' :: rest) acc = (acc.reverse ++ l) :: zerlegeZ rest [] := by
  induction l generalizing acc with
  | nil => simp [zerlegeZ]
  | cons c l ih =>
    have hc : c ≠ ':' := fun e => h (e ▸ List.mem_cons_self)
    have hr : ':' ∉ l := fun m => h (List.mem_cons_of_mem _ m)
    rw [List.cons_append, zerlegeZ_cons _ _ hc, ih _ hr]
    simp

/-- Segments without `:`, joined by `::`, split back into themselves. -/
theorem zerlegeZ_verbinde : ∀ (p : List (List Char)), p ≠ [] → (∀ s ∈ p, ':' ∉ s) →
    zerlegeZ ([':', ':'].intercalate p) [] = p
  | [], h, _ => absurd rfl h
  | [x], _, hs => by
    rw [List.intercalate_singleton, zerlegeZ_ohne _ _ (hs x List.mem_cons_self)]
    simp
  | x :: y :: zs, _, hs => by
    rw [List.intercalate_cons_cons, List.append_assoc]
    rw [show [':', ':'] ++ [':', ':'].intercalate (y :: zs) = ':' :: ':' :: [':', ':'].intercalate (y :: zs)
      from rfl]
    rw [zerlegeZ_trenner _ _ _ (hs x List.mem_cons_self),
      zerlegeZ_verbinde (y :: zs) (List.cons_ne_nil _ _) (fun s m => hs s (List.mem_cons_of_mem _ m))]
    simp

/-- **A joined path splits back into its segments** when no segment contains `:` (identifiers never
    do): `segmente` is the inverse of the joined key. -/
theorem segmente_verbinde {p : Pfad} (hp : p ≠ []) (h : ∀ s ∈ p, ':' ∉ s.toList) :
    segmente ("::".intercalate p) = p := by
  have hz : "::".toList = [':', ':'] := by decide
  simp only [segmente, String.toList_intercalate, hz]
  rw [zerlegeZ_verbinde (p.map String.toList) (by simpa using hp)
    (by simpa using h)]
  simp [String.ofList_toList]


/-- The last segment of a path: the short name. -/
def letzter (p : Pfad) : String := p.getLast?.getD ""

/-- The declared name of an item, if it declares one. -/
def itemName : SItemTief → Option String
  | .typeT _ n _ _ _ => some n
  | .constT n _ _ => some n
  | .globT _ n _ _ _ _ _ => some n
  | .fnT s _ => some s.name
  | .protoT s => some s.name
  | .specT s _ => some s.name
  | .asmT s _ => some s.name
  | .formatT n _ _ _ => some n
  | .tableT n _ _ _ _ _ _ => some n
  | .arenaT n _ _ _ _ _ => some n
  | .whyT n _ _ => some n
  | .stateT n _ => some n
  | .devT n _ _ _ => some n
  | .assumT n _ _ _ => some n
  | .axiomT n _ _ _ _ _ => some n
  | .checkT c => some c.cname
  | .atomT n _ _ _ _ => some n
  | .lockT n _ _ _ _ _ _ => some n
  | .rcuT n _ _ => some n
  | .groupT n _ _ => some n
  | .accT n _ _ _ => some n
  | .walkT w => some w.name
  | .entryT e => some e.name
  | .callT c => some c.name
  | .varT n => some n
  | .transT n _ _ => some n
  | .gateT it => itemName it
  | .pubT it => itemName it
  | _ => none

mutual
/-- **What a unit declares and uses**: the full path of every named item, and every `use` line with the
    module it stands in. -/
def sammleI (von : Pfad) : SItemTief → List Pfad × List (Pfad × Pfad)
  | .modT p b => sammleL (von ++ segmente p) b
  | .useT p => ([], [(von, p)])
  | .pubT it => sammleI von it
  | it => match itemName it with
    | some n => ([von ++ [n]], [])
    | none => ([], [])
def sammleL (von : Pfad) : List SItemTief → List Pfad × List (Pfad × Pfad)
  | [] => ([], [])
  | it :: rest =>
    let a := sammleI von it
    let b := sammleL von rest
    (a.1 ++ b.1, a.2 ++ b.2)
end

/-- The source of a unit for the name-space rule. -/
def quelle (items : List SItemTief) : Quelle :=
  let s := sammleL [] items
  ⟨s.1, s.2⟩

/-- **The key of an item**: its short name when no other declared path ends in it, else its path. -/
def schluessel (namen : List Pfad) (c : Pfad) : String :=
  if (namen.filter fun q => strEq (letzter q) (letzter c)).length == 1 then letzter c
  else "::".intercalate c

/-- The short name of a non-empty path is one of its segments. -/
theorem letzter_mem {c : Pfad} (h : c ≠ []) : letzter c ∈ c := by
  unfold letzter
  cases hl : c.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp hl) h
  | some x => exact List.mem_of_getLast? hl

/-- **Distinct items carry distinct keys.** Paths are non-empty and their segments are identifiers
    (no `:`): two items with one key are one item. So the elaborator, which looks names up by text,
    never merges two items of a unit. -/
theorem schluessel_injektiv {namen : List Pfad}
    (hok : ∀ p ∈ namen, p ≠ [] ∧ ∀ s ∈ p, ':' ∉ s.toList) {c d : Pfad} (hc : c ∈ namen)
    (hd : d ∈ namen) (h : schluessel namen c = schluessel namen d) : c = d := by
  obtain ⟨hc0, hcs⟩ := hok c hc
  obtain ⟨hd0, hds⟩ := hok d hd
  have hself : ∀ x : String, strEq x x = true := fun x => by simp [strEq]
  -- One short name, one filter.
  have hfil : letzter c = letzter d →
      (namen.filter fun q => strEq (letzter q) (letzter c)) =
        (namen.filter fun q => strEq (letzter q) (letzter d)) := fun e => by rw [e]
  -- A short key is one of the path's segments, so it splits into itself.
  have kurz : ∀ x : Pfad, x ≠ [] → (∀ s ∈ x, ':' ∉ s.toList) → segmente (letzter x) = [letzter x] :=
    fun x h0 hs => segmente_name (hs _ (letzter_mem h0))
  unfold schluessel at h
  split at h <;> split at h
  · -- both short: one filter of length one holds both
    rename_i h1 h2
    have e := hfil h
    have hl : (namen.filter fun q => strEq (letzter q) (letzter c)).length = 1 := beq_iff_eq.mp h1
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hl
    have mc : c ∈ namen.filter fun q => strEq (letzter q) (letzter c) := by simp [hc, hself]
    have md : d ∈ namen.filter fun q => strEq (letzter q) (letzter c) := by
      rw [e]; simp [hd, hself]
    rw [hx] at mc md
    simp at mc md
    rw [mc, md]
  · -- c short, d joined: d splits into the one segment `letzter c`, so it has c's filter
    rename_i h1 h2
    have sd := segmente_verbinde hd0 hds
    rw [← h, kurz c hc0 hcs] at sd
    have hdl : letzter d = letzter c := by rw [← sd]; rfl
    exact (h2 (by rw [← hfil hdl.symm]; exact h1)).elim
  · -- c joined, d short: symmetric
    rename_i h1 h2
    have sc := segmente_verbinde hc0 hcs
    rw [h, kurz d hd0 hds] at sc
    have hcl : letzter c = letzter d := by rw [← sc]; rfl
    exact (h1 (by rw [hfil hcl]; exact h2)).elim
  · -- both joined: split both
    have := congrArg segmente h
    rwa [segmente_verbinde hc0 hcs, segmente_verbinde hd0 hds] at this

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
  | .bindLib _ x _ _ _ => [x]
  | .alloc _ x _ _ _ _ => [x]
  | .allocVon _ x _ _ => [x]
  | .await x _ _ _ => [x]
  | .swap x _ _ _ => [x]
  | _ => []

/-- An ender, resolved. -/
def ende (k : Kontext) : Option SEnde → Option SEnde
  | some (.ret e) => some (.ret (ausO k e))
  | e => e

mutual
/-- **A statement, resolved**; the statements of a block see the names the earlier ones bind. -/
def anw (k : Kontext) : SAnw → SAnw
  | .bind m x t e => .bind m x (typO k t) (aus k e)
  | .bindElse x t e g s => .bindElse x (typO k t) (aus k e) g (anw k s)
  | .bindLib m x t a b => .bindLib m x (typO k t) a b
  | .set l o r => .set (aus k l) o (aus k r)
  | .shift p a b => .shift (aus k p) a b
  | .call f xs => .call (k.ref f) (xs.map (aus k))
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

/-- A transition, resolved. -/
def trans (k : Kontext) (t : STrans) : STrans :=
  { t with
    schritte := t.schritte.map fun (a, b, c) => (aus k a, aus k b, aus k c)
    voraus := ausO k t.voraus
    wirkung := t.wirkung.map (effekt k) }

/-- A device member, resolved. -/
def gerTeil (k : Kontext) : SGerTeil → SGerTeil
  | .copy a b => .copy (aus k a) (aus k b)
  | .reg r => .reg { r with rtyp := typ k r.rtyp, addr := aus k r.addr, voraus := ausO k r.voraus }
  | .trans t => .trans (trans k t)
  | g => g

/-- A binding of a gate, resolved. -/
def bindung (k : Kontext) (b : SBind) : SBind :=
  { b with id := aus k b.id, codes := b.codes.map fun (e, n, g) => (e, ausO k n, g) }

/-- Where a gate rests, resolved: the assumption it names. -/
def herkunft (k : Kontext) : SHerkunft → SHerkunft
  | .assum n c => .assum (k.ref n) c
  | h => h

/-- **A `syscall` gate, resolved.** -/
def syscall (k : Kontext) (c : SSyscall) : SSyscall :=
  let k' := k.mit (c.params.map Prod.fst)
  { c with
    name := k.eigen c.name
    params := c.params.map fun (n, t) => (n, typ k t)
    res := typO k c.res
    fail := c.fail.map k.ref
    way := match c.way with
      | .lit abi arch b h => .lit abi arch (bindung k' b) (herkunft k h)
      | .via v => .via (k.ref v)
    gate := { pre := c.gate.pre.map (aus k'), post := c.gate.post.map (aus k'),
              uses := c.gate.uses.map (effekt k'), cost := ausO k' c.gate.cost } }

/-- **An item, resolved** in its module: its own key and every name it writes. Item kinds without a G
    form pass unchanged (the elaborator refuses them). -/
def item (k : Kontext) : SItemTief → SItemTief
  | .typeT fl n args ord t => .typeT fl (k.eigen n) (args.map (typ k)) ord (typO k t)
  | .constT n t v => .constT (k.eigen n) (typ k t) (konst k v)
  | .globT m n t v al s sh => .globT m (k.eigen n) (typ k t) (konst k v) (ausO k al) s sh
  | .fnT s b => .fnT (sig k s) (anw (k.mit (s.params.map Prod.fst)) b)
  | .protoT s => .protoT (sig k s)
  | .specT s p => .specT (sig k s) (aus (k.mit (s.params.map Prod.fst)) p)
  | .asmT s h => .asmT (sig k s) h
  | .tableT n v c b o sh ps => .tableT (k.eigen n) (v.map k.ref) (ausO k c) b o sh (ps.map (tabTeil k))
  | .lockT n ps rk h sh m i =>
    .lockT (k.eigen n) (ps.map (aus k)) (aus k rk) (ausO k h) (ausO k sh) m (ausO k i)
  | .atomT n t p o b => .atomT (k.eigen n) (typ k t) (p.map (·.map (aus k))) o b
  | .arenaT n lo hi mx t pb =>
    .arenaT (k.eigen n) (aus k lo) (aus k hi) (ausO k mx) (typ k t) (pb.map fun (ps, e) => (ps, aus k e))
  | .assumT n a s c => .assumT (k.eigen n) a s c
  | .whyT n cs ex => .whyT (k.eigen n) (cs.map fun (a, e, b) => (a, aus k e, b)) ex
  | .callT c => .callT (syscall k c)
  | .varT n => .varT (k.eigen n)
  | .goalT n o => .goalT n (o.map fun (abi, arch, bs) => (abi, arch, bs.map fun (v, b, h) =>
      (k.ref v, bindung k b, herkunft k h)))
  | .entryT e => .entryT { e with name := k.eigen e.name, vektor := ausO k e.vektor, ist := ausO k e.ist,
                                  dispatch := k.pfad e.dispatch }
  | .concT ps => .concT (ps.map fun (p, a) => (k.pfad p, a.map (aus k)))
  | .devT n ps sp ms =>
    .devT (k.eigen n) (ps.map fun (x, t) => (x, typ k t)) sp (ms.map (gerTeil (k.mit (ps.map Prod.fst))))
  | .groupT n ns is => .groupT (k.eigen n) (ns.map k.ref) (is.map (inv k))
  | .stateT n ts => .stateT (k.eigen n) (ts.map (trans k))
  | .pubT it => item k it
  | it => it

mutual
/-- The items of a unit, resolved and flat: module wrappers opened, `use` lines dropped. -/
def loeseI (q : Quelle) (von : Pfad) : SItemTief → List SItemTief
  | .modT p b => loeseL q (von ++ segmente p) b
  | .useT _ => []
  | .pubT it => loeseI q von it
  | it => [item ⟨q, von, []⟩ it]
def loeseL (q : Quelle) (von : Pfad) : List SItemTief → List SItemTief
  | [] => []
  | it :: rest => loeseI q von it ++ loeseL q von rest
end

/-- An item list of one name space: no `use`, no module. -/
def flach : List SItemTief → Bool
  | [] => true
  | .modT _ _ :: _ => false
  | .useT _ :: _ => false
  | .pubT (.modT _ _) :: _ => false
  | .pubT (.useT _) :: _ => false
  | _ :: rest => flach rest

/-- **A unit of one name space**: no `use` line, and at most one module wrapper around flat items. -/
def einfach : List SItemTief → Bool
  | [.modT _ b] => flach b
  | its => flach its

/-- **The resolution of a unit**: one name space as before (`uMembers`); else every name by the
    name-space rule and every item under its key. -/
def loese (items : List SItemTief) : List SItemTief :=
  if einfach items then Uebersetze.uMembers items else loeseL (quelle items) [] items

/-- **A unit of one name space is resolved as before.** -/
theorem loese_einfach {items : List SItemTief} (h : einfach items = true) :
    loese items = Uebersetze.uMembers items := by
  simp [loese, h]

/-- **A local stays what it is.** -/
theorem ref_lokal {k : Kontext} {s : String} (h : k.lok.any (strEq · s) = true) : k.ref s = s := by
  simp [Kontext.ref, h]

/-- **A name that resolves names its item's key.** -/
theorem ref_aufgeloest {k : Kontext} {s : String} {c : Pfad} (hl : k.lok.any (strEq · s) = false)
    (h : aufloeseK k.q ⟨none, []⟩ k.von (segmente s) = some c) :
    k.ref s = schluessel k.q.namen c := by
  simp [Kontext.ref, hl, h]

/-- **A name of an item that is not visible from here is poisoned**: no item carries the text. -/
theorem ref_unsichtbar {k : Kontext} {s : String} (hl : k.lok.any (strEq · s) = false)
    (h : aufloeseK k.q ⟨none, []⟩ k.von (segmente s) = none)
    (hn : k.q.namen.any (fun q => strEq (letzter q) (letzter (segmente s))) = true) :
    k.ref s = gift s := by
  simp [Kontext.ref, hl, h, hn]

/-- **An item whose short name no other item has keeps its short name.** -/
theorem schluessel_kurz {namen : List Pfad} {c : Pfad}
    (h : (namen.filter fun q => strEq (letzter q) (letzter c)).length = 1) :
    schluessel namen c = letzter c := by
  simp [schluessel, h]

end Gabbro.Grammatik.Parser.Aufloesung
