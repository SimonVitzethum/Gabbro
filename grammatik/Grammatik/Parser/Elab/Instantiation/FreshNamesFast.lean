module
public import Grammatik.Parser.Elab.Instantiation.Names
public import Grammatik.Parser.Lex.TafelIndex
@[expose] public section

namespace Gabbro.Grammatik.Parser.Instantiation

/-- Extend the existing faithful index without rebuilding its suffix map. -/
def freshNameIndexCons (name : String) (suffix : Tafel.Index String String id) :
    Tafel.Index String String id :=
  { liste := name :: suffix.liste
    karte := suffix.karte.insert name name
    treu := (by
      intro query
      rw [Std.HashMap.getElem?_insert, List.find?_cons, suffix.treu]
      cases hq : (id name == query) with
      | false => simp only [id_eq] at hq; simp only [hq] <;> rfl
      | true => simp only [id_eq] at hq; simp only [hq] <;> rfl) }

/-- A persistent suffix index keeps duplicate detection indexed and preserves
    the original spelling comparison. No hash structure enters the specification. -/
def freshNameSuffix (source : Tafel.Index String String id) :
    List String → Tafel.Index String String id × Bool
  | [] => (Tafel.Index.von id [], true)
  | name :: rest =>
    let suffix := freshNameSuffix source rest
    -- Read the suffix before insertion so compiled code can reuse its map storage.
    let fresh := !(source.finde name).isSome && !(suffix.1.finde name).isSome && suffix.2
    (freshNameIndexCons name suffix.1, fresh)

theorem freshNameSuffix_eq (source : Tafel.Index String String id) (names : List String) :
    (freshNameSuffix source names).1.liste = names ∧
      (freshNameSuffix source names).2 = freshNames source.liste names := by
  induction names with
  | nil => exact ⟨rfl, rfl⟩
  | cons name rest ih =>
    constructor
    · exact congrArg (name :: ·) ih.1
    · simp only [freshNameSuffix, freshNames, ih.2, Tafel.Index.finde,
        ih.1, id_eq, List.isSome_find?, List.any_beq']

def freshNamesFast (source generated : List String) : Bool :=
  (freshNameSuffix (Tafel.Index.von id source) generated).2

@[csimp] theorem freshNames_eq_fast : @freshNames = @freshNamesFast := by
  funext source generated
  exact (freshNameSuffix_eq (Tafel.Index.von id source) generated).2.symm

end Gabbro.Grammatik.Parser.Instantiation
