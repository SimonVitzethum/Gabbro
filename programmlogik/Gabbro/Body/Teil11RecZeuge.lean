module

public import Gabbro.Body.Teil8
public import Gabbro.Body.Teil10RecRegeln

@[expose] public section

namespace Gabbro.Body

/-- A real record-typed place, rather than an inconsistent well-formedness premise. -/
def recTyping : Typing := fun _ => some (.record [.intIn 0 10, .bool])
def recWorld : World := fun _ => .record [.int 7, .bool true]

theorem recWorld_wf : WF recTyping recWorld := by
  intro p sh hp
  change some (.record [.intIn 0 10, .bool]) = some sh at hp
  cases hp
  change (Value.record [.int 7, .bool true]).hasShape (.record [.intIn 0 10, .bool]) = true
  decide

end Gabbro.Body
