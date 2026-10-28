import Grammatik.Parser.Namen.Aufloesung

/-!
  File:      Grammatik/Parser/Namen/Oeffentlich.lean
  Subject:   **`pub`**: which items cross the boundary of their project, and the rule that an exported
             interface is complete -- what a `pub` item's head names crosses too.

  The language rule, modelled here before the Rust checker follows:

  * `pub` stands before an item and marks it as crossing: its name is one of the public names a
    dependent project sees (`Namensraum.sichtbar`, the `pub` part of `Platz.deps`).
  * **Which items can cross** (`darfPub`): functions (with a body, a prototype, a `spec fn`, an `asm`
    body), `static`, `const`, `type`, `atomic`, `table`, `arena`, `lock`, `format`, `device`, `reason`,
    and `use` and `module` (a re-exported path, a public module). Every other kind has no `pub`; a
    `pub` before it is refused, and so is `pub pub`.
  * **The export hull is closed** (`N038`): every item that a `pub` item's head names -- the types of
    its parameters, result and fields, its `or` reason, its effect places, contract and cost
    (`kopfNamen`; parameters and binders are locals and name nothing) -- is itself `pub`, or the item
    itself. An interface that names something that does not cross would point a dependent at a name it
    cannot see. Names are resolved by the unit's rule (`Aufloesung`), so the check concerns items, not
    texts: two items of one short name are told apart.
  * `huelleZu` decides both. The Lean pipeline refuses a unit where it fails (`pre108`); a unit without
    `pub` is closed trivially (`huelle_ohne_pub`), so units that never used `pub` are unchanged.

  Theorems:
  * `huelle_ohne_pub` -- a unit without `pub` has a closed hull.
  * **`huelle_geschlossen`** -- in a closed unit, every item a `pub` item's head resolves to is `pub` or
    that item itself, and every `pub` stands before a kind that may carry it.
  * `pub_sichtbar` -- what a dependent sees: the names in an exported head resolve to public names.
-/

namespace Gabbro.Grammatik.Parser.Oeffentlich

open Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Aufloesung
open Gabbro.Grammatik.Parser.Namensraum (Pfad Quelle Platz aufloeseK)

set_option maxRecDepth 100000

/-- Whether a name is a local here. -/
def lokal (lok : List String) (s : String) : Bool := lok.any (strEq · s)

mutual
/-- **The names an expression writes**, outside the locals: place heads, called functions, function
    values, reason heads and two-segment paths, quantifier domains. -/
def namenA (lok : List String) : SExpr → List String
  | .variable s => if lokal lok s then [] else [s]
  | .field x _ => namenA lok x
  | .index x i => namenA lok x ++ namenA lok i
  | .arrow x _ => namenA lok x
  | .un _ x => namenA lok x
  | .bin _ x y => namenA lok x ++ namenA lok y
  | .call f xs => (if lokal lok f then [] else [f]) ++ namenL lok xs
  | .fnref p => if lokal lok p then [] else [p]
  | .built _ xs => namenL lok xs
  | .old x => namenA lok x
  | .why g f => if lokal lok g then [] else [g, g ++ "::" ++ f]
  | .ext .all (x :: _ :: ns) xs => ns ++ namenL (x :: lok) xs
  | .ext .any (x :: _ :: ns) xs => ns ++ namenL (x :: lok) xs
  | .ext .count (x :: _ :: ns) xs => ns ++ namenL (x :: lok) xs
  | .ext .mem (_ :: ns) xs => ns ++ namenL lok xs
  | .ext _ _ xs => namenL lok xs
  | _ => []
def namenL (lok : List String) : List SExpr → List String
  | [] => []
  | x :: xs => namenA lok x ++ namenL lok xs
end

/-- The names of an optional expression. -/
def namenO (lok : List String) : Option SExpr → List String
  | some e => namenA lok e
  | none => []

/-- **The names a type writes**: named types, paths, the table of an `index into`, and the names in
    range bounds and array lengths. -/
def namenT : STyp → List String
  | .atom s => [s]
  | .path ps => ["::".intercalate ps]
  | .ptr _ _ t => namenT t
  | .index _ t => [t]
  | .range b lo hi _ => namenT b ++ namenA [] lo ++ namenA [] hi
  | .array t n => namenT t ++ namenA [] n
  | .wrap t => namenT t
  | .embed b _ x => namenT b ++ namenO [] x
  | .str e => namenA [] e
  | .entry _ (some t) => namenT t
  | _ => []

/-- The names of an optional type. -/
def namenTO : Option STyp → List String
  | some t => namenT t
  | none => []

/-- The names an effect writes. -/
def namenE (lok : List String) : SEffekt → List String
  | .reads e | .writes e | .locks _ e | .takes e | .posts e => namenA lok e
  | .masks n | .allocs n => [n]
  | _ => []

/-- The names a contract clause writes. -/
def namenK (lok : List String) : SKlausel → List String
  | .needs e | .gives e | .cost e | .drops e => namenA lok e
  | .refs ns | .keeps ns => ns
  | .load p => ["::".intercalate p]
  | .effs es => es.flatMap (namenE lok)
  | _ => []

/-- The names a function head writes: parameter and result types, the reason, every clause (the
    parameters are locals there). -/
def namenSig (s : FnSig) : List String :=
  let lok := s.params.map Prod.fst
  s.params.flatMap (fun p => namenT p.2) ++ namenTO s.res ++ s.fehler.toList ++
    s.klauseln.flatMap (namenK lok)

/-- The names a table member's head writes: field types, constant types and field conditions. -/
def namenTeil : STabTeil → List String
  | .tConst _ t _ => namenT t
  | .tSlot fs => fs.flatMap fun f => namenT f.ftyp
  | _ => []

/-- **The names an item's head writes** -- what an importer reads of it. -/
def kopfNamen : SItemTief → List String
  | .fnT s _ | .protoT s | .specT s _ | .asmT s _ => namenSig s
  | .globT _ _ t _ _ _ _ | .constT _ t _ | .atomT _ t _ _ _ | .arenaT _ _ _ _ t _ => namenT t
  | .typeT _ _ args _ t => args.flatMap namenT ++ namenTO t
  | .tableT _ v _ _ _ _ ps => v.toList ++ ps.flatMap namenTeil
  | .lockT _ ps _ _ _ _ _ => namenL [] ps
  | .formatT _ _ _ fs => fs.flatMap fun f => namenT f.ftyp
  | .devT _ ps _ _ => ps.flatMap fun p => namenT p.2
  | _ => []

/-- **The kinds that can carry `pub`.** -/
def darfPub : SItemTief → Bool
  | .fnT .. | .protoT .. | .specT .. | .asmT .. | .globT .. | .constT .. | .typeT .. | .atomT ..
  | .tableT .. | .arenaT .. | .lockT .. | .formatT .. | .devT .. | .whyT .. | .useT .. | .modT .. => true
  | _ => false

/-- A `pub` item: where it stands, its path (if it names one) and the item. -/
structure Export where
  von : Pfad
  pfad : Option Pfad
  it : SItemTief

mutual
/-- **The `pub` items of a unit**, with the module they stand in. -/
def exporteI (von : Pfad) : SItemTief → List Export
  | .modT p b => exporteL (von ++ segmente p) b
  | .pubT it =>
    ⟨von, (itemName it).map (fun n => von ++ [n]), it⟩ ::
      (match it with
       | .modT p b => exporteL (von ++ segmente p) b
       | _ => [])
  | _ => []
def exporteL (von : Pfad) : List SItemTief → List Export
  | [] => []
  | it :: rest => exporteI von it ++ exporteL von rest
end

/-- The paths of the `pub` items. -/
def oeffentlich (items : List SItemTief) : List Pfad := (exporteL [] items).filterMap (·.pfad)

/-- **What a name in an exported head may resolve to**: nothing (a built-in, a field), the item itself,
    or a `pub` item. -/
def erlaubt (q : Quelle) (pubs : List Pfad) (e : Export) (n : String) : Bool :=
  match aufloeseK q ⟨none, []⟩ e.von (segmente n) with
  | none => true
  | some c => decide (c ∈ pubs) || decide (some c = e.pfad)

/-- One export is sound: its kind may carry `pub`, and its head names only what crosses. -/
def exportGut (q : Quelle) (pubs : List Pfad) (e : Export) : Bool :=
  darfPub e.it && (kopfNamen e.it).all (erlaubt q pubs e)

/-- **The export hull of a unit is closed** (and every `pub` stands where it may). -/
def huelleZu (items : List SItemTief) : Bool :=
  let es := exporteL [] items
  es.isEmpty || es.all (exportGut (quelle items) (oeffentlich items))

/-- **A unit without `pub` has a closed hull**: it is unchanged by the rule. -/
theorem huelle_ohne_pub {items : List SItemTief} (h : (exporteL [] items).isEmpty = true) :
    huelleZu items = true := by
  simp only [huelleZu, h, Bool.true_or]

/-- **In a closed unit every `pub` item is sound**: it may carry `pub`, and every name of its head
    resolves to nothing, to the item itself, or to a `pub` item. -/
theorem huelle_geschlossen {items : List SItemTief} (h : huelleZu items = true)
    {e : Export} (he : e ∈ exporteL [] items) :
    darfPub e.it = true ∧ ∀ n ∈ kopfNamen e.it, ∀ c,
      aufloeseK (quelle items) ⟨none, []⟩ e.von (segmente n) = some c →
        c ∈ oeffentlich items ∨ some c = e.pfad := by
  unfold huelleZu at h
  have hg : exportGut (quelle items) (oeffentlich items) e = true := by
    cases hn : (exporteL [] items).isEmpty with
    | true => rw [List.isEmpty_iff.mp hn] at he; cases he
    | false => simp only [hn, Bool.false_or, List.all_eq_true] at h; exact h e he
  simp only [exportGut, Bool.and_eq_true, List.all_eq_true] at hg
  refine ⟨hg.1, fun n hn c hc => ?_⟩
  have := hg.2 n hn
  simp only [erlaubt, hc, Bool.or_eq_true, decide_eq_true_eq] at this
  exact this

/-- **What a dependent sees of an exported head**: in a closed unit, every item the head of a `pub`
    item names (other than itself) is one of the unit's public names -- the names the name-space rule
    makes visible to a dependent project (`Namensraum.sichtbar`, the `pub` part of a dependency). -/
theorem pub_sichtbar {items : List SItemTief} (h : huelleZu items = true)
    {e : Export} (he : e ∈ exporteL [] items) {n : String} (hn : n ∈ kopfNamen e.it) {c : Pfad}
    (hc : aufloeseK (quelle items) ⟨none, []⟩ e.von (segmente n) = some c) (hs : some c ≠ e.pfad) :
    c ∈ oeffentlich items :=
  ((huelle_geschlossen h he).2 n hn c hc).resolve_right hs

end Gabbro.Grammatik.Parser.Oeffentlich
