module
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil12

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

/-- A table binds a nominal space independently of its optional owner mark.
    The absent binder denotes the existing normal space. -/
def uTableSpaceName : SItemTief → Option String
  | .tableT _ _ _ _ _ _ _ space => some (space.getD "normal")
  | _ => none

/-- Declaration order fixes space ordinals; normal remains zero. Repeated
    names deliberately share one nominal space and introduce no protection. -/
def uSpaces (items : List SItemTief) : List String :=
  uOhneDoppelte ("normal" :: items.filterMap uTableSpaceName)

/-- Bind the table returned by the actual canonical/Stage-0 table callback.
    Existing field, owner and provider checks run first and retain their errors. -/
def uTabelleMitRaum (spaces : List String) (lower : SItemTief → Except String UTab)
    (item : SItemTief) : Except String UTab := do
  let table ← lower item
  match uTableSpaceName item with
  | none => .error "space binding requires a table declaration"
  | some name => do
    let index ← uDataSpace spaces name
    pure { table with space := index }

/-- Every success retains the actual callback result and the actual registered
    name/ordinal equality. No field or owner is reconstructed from the space. -/
theorem uTabelleMitRaum_sound (spaces : List String)
    (lower : SItemTief → Except String UTab) (item : SItemTief) (table : UTab)
    (accepted : uTabelleMitRaum spaces lower item = .ok table) :
    ∃ name index base, uTableSpaceName item = some name ∧ lower item = .ok base ∧
      uDataSpace spaces name = .ok index ∧ table = { base with space := index } := by
  unfold uTabelleMitRaum at accepted
  cases produced : lower item with
  | error error => simp only [produced, bind, Except.bind] at accepted; cases accepted
  | ok base =>
    simp only [produced, bind, Except.bind] at accepted
    cases named : uTableSpaceName item with
    | none => simp only [named] at accepted; cases accepted
    | some name =>
      simp only [named] at accepted
      cases resolved : uDataSpace spaces name with
      | error error => simp only [resolved, bind, Except.bind] at accepted; cases accepted
      | ok index =>
        simp only [resolved, bind, Except.bind, pure, Except.pure] at accepted
        exact ⟨name, index, base, rfl, rfl, resolved, (Except.ok.inj accepted).symm⟩

theorem uTabelleMitRaum_fields (spaces : List String)
    (lower : SItemTief → Except String UTab) (item : SItemTief) (table : UTab)
    (accepted : uTabelleMitRaum spaces lower item = .ok table) :
    ∃ base, lower item = .ok base ∧ table.name = base.name ∧ table.count = base.count ∧
      table.cols = base.cols ∧ table.owner = base.owner := by
  obtain ⟨_, _, base, _, produced, _, same⟩ :=
    uTabelleMitRaum_sound spaces lower item table accepted
  exact ⟨base, produced, by rw [same], by rw [same], by rw [same], by rw [same]⟩

end Gabbro.Grammatik.Parser.Uebersetze
