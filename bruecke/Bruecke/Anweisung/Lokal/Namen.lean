module
public import Bruecke.Kodierung
public import Init.Data.String.Length
@[expose] public section

/-!
# Body identifiers for source scopes

`active` is positional: one identifier per source entry, including hidden entries. `used`
belongs to the entire function. Restoring a block's active scope must retain its returned
`used` list, including allocations in the other arm. First bindings retain their source
spelling; repeated spellings receive a suffix longer than every identifier already used.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

/-- A finite bound on the length of every occupied identifier. -/
def nameLengthBound : List String → Nat
  | [] => 0
  | x :: xs => max x.length (nameLengthBound xs)

theorem length_le_nameLengthBound : ∀ (xs : List String) (x : String),
    x ∈ xs → x.length ≤ nameLengthBound xs
  | [], _, h => False.elim (List.not_mem_nil h)
  | y :: ys, x, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_max_left _ _
      · have ht := length_le_nameLengthBound ys x h
        exact Nat.le_trans ht (Nat.le_max_right _ _)

/-- The fallback is longer than every used identifier, even when source names contain `#`. -/
def freshBodyName (used : List String) (x : String) : String :=
  if x ∈ used then
    x ++ String.ofList (List.replicate (nameLengthBound used + 1) '#')
  else x

theorem freshBodyName_not_mem (used : List String) (x : String) :
    freshBodyName used x ∉ used := by
  unfold freshBodyName
  split
  · intro h
    have hb := length_le_nameLengthBound used _ h
    simp only [String.length_append, String.length_ofList, List.length_replicate] at hb
    omega
  · assumption

theorem freshBodyName_first {used : List String} {x : String} (h : x ∉ used) :
    freshBodyName used x = x := by
  unfold freshBodyName
  exact if_neg h

/-- Active positional names and the function-wide allocation history. -/
structure BodyNames where
  active : List String
  used : List String

namespace BodyNames

def start (fn : UFn) : BodyNames :=
  ⟨fn.params.map (·.1), fn.params.map (·.1)⟩

def fresh (ns : BodyNames) (x : String) : String := freshBodyName ns.used x

def push (ns : BodyNames) (x : String) : BodyNames :=
  ⟨ns.fresh x :: ns.active, ns.fresh x :: ns.used⟩

/-- Restore the source scope after a block while keeping every identifier allocated in it. -/
def resume (ns : BodyNames) (used : List String) : BodyNames := ⟨ns.active, used⟩

/-- Identifier lookup uses exactly the position chosen by the source lowering. -/
def lookup (ns : BodyNames) (fn : UFn) (x : String) : Option String :=
  match paramPos fn.params x with
  | .ok j => ns.active[j]?
  | .error _ => none

/-- A source-name view for reusing expression lemmas; the runtime binding is never changed. -/
def visible (ns : BodyNames) (fn : UFn) (β : Gabbro.Body.Binding) : Gabbro.Body.Binding :=
  fun x => match ns.lookup fn x with
    | some id => β id
    | none => β x

/-- Allocation history contains all active identifiers; active identifiers are distinct. -/
def Valid (ns : BodyNames) : Prop :=
  ns.active.Nodup ∧ ∀ x ∈ ns.active, x ∈ ns.used

theorem valid_start {fn : UFn} (h : (fn.params.map (·.1)).Nodup) :
    (start fn).Valid := ⟨h, fun _ hx => hx⟩

theorem fresh_not_active {ns : BodyNames} (h : ns.Valid) (x : String) :
    ns.fresh x ∉ ns.active :=
  fun hm => freshBodyName_not_mem ns.used x (h.2 _ hm)

theorem valid_push {ns : BodyNames} (h : ns.Valid) (x : String) : (ns.push x).Valid := by
  refine ⟨List.nodup_cons.mpr ⟨fresh_not_active h x, h.1⟩, ?_⟩
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (h.2 y hy)

theorem valid_resume {ns : BodyNames} (h : ns.Valid) {used : List String}
    (hu : ∀ x ∈ ns.used, x ∈ used) : (ns.resume used).Valid :=
  ⟨h.1, fun x hx => hu x (h.2 x hx)⟩

theorem used_push (ns : BodyNames) (x y : String) (hy : y ∈ ns.used) :
    y ∈ (ns.push x).used := List.mem_cons_of_mem _ hy

end BodyNames

end Gabbro.Bruecke
