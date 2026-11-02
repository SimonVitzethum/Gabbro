module
public import Init.Data.List.Pairwise
public import Init.Data.List.Lemmas
@[expose] public section
namespace Gabbro.Grammatik.Parser.Instantiation

/-- Check each generated name against the original namespace and all later generated names.
    Unlike deduplication, this refuses a collision rather than concealing it. -/
def freshNames (source : List String) : List String → Bool
  | [] => true
  | name :: rest => !source.contains name && !rest.contains name && freshNames source rest

def checkFreshNames (source generated : List String) (message : String) : Except String Unit :=
  if freshNames source generated then .ok () else .error message

/-- The executable collision check proves both parts of hygiene, without assumptions on the
    spelling or injectivity of any of the three instance-name encodings. -/
theorem freshNames_sound (source generated : List String)
    (h : freshNames source generated = true) :
    generated.Nodup ∧ ∀ name ∈ generated, name ∉ source := by
  revert h
  induction generated with
  | nil => intro _; simp
  | cons name rest ih =>
    intro h
    have parts : name ∉ source ∧ name ∉ rest ∧ freshNames source rest = true := by
      simpa [freshNames, Bool.and_eq_true, List.contains_iff_mem, and_assoc] using h
    obtain ⟨unique, disjoint⟩ := ih parts.2.2
    constructor
    · exact List.nodup_cons.mpr ⟨parts.2.1, unique⟩
    · intro other member
      rcases List.mem_cons.mp member with same | tail
      · subst other
        exact parts.1
      · exact disjoint other tail

theorem checkFreshNames_sound (source generated : List String) (message : String)
    (h : checkFreshNames source generated message = .ok ()) :
    generated.Nodup ∧ ∀ name ∈ generated, name ∉ source := by
  apply freshNames_sound
  cases hf : freshNames source generated with
  | false => simp [checkFreshNames, hf] at h
  | true => rfl

end Gabbro.Grammatik.Parser.Instantiation
