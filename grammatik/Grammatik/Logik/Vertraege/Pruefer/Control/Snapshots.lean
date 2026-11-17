module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Arguments
public import Grammatik.Logik.Vertraege.Pruefer.Control.Havoc
public import Grammatik.Logik.Invarianten.Frag.Symbolic.Snapshot.Collect

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Symbolic

open Invarianten Invarianten.Frag Invarianten.Frag.Symbolic Invarianten.Elim Invarianten.Modell

def snapshotFormula (start : Nat) (names : List (Observation D)) (body : LProp (Key D Nat)) :
    LProp (Key D Nat) :=
  universalClosure (argumentKeys start (start + names.length)) (.imp (Snapshot.equations start names) body)

/-- A fresh valuation extension records the actual call-entry memory before
    post-state havoc. Existing immutable observations retain their values. -/
theorem snapshotFormula_sound (start : Nat) (names : List (Observation D))
    (body : LProp (Key D Nat)) (valuation : Assignment Nat) (world : World D)
    (valid : (snapshotFormula start names body).denote (values valuation world)) :
    body.denote (values (Snapshot.extend start names valuation world) world) := by
  have ready := closure_transfer (argumentKeys start (start + names.length))
    (.imp (Snapshot.equations start names) body) (values valuation world)
    (values (Snapshot.extend start names valuation world) world) valid (by
      intro key _ absent
      cases key with
      | inl memory => rfl
      | inr key =>
          exact (Snapshot.extend_preserves names start valuation world key
            (outside_argumentKeys start (start + names.length) key absent)).symm)
  exact ready ((Snapshot.equations_denote names start _ world).mpr
    (Snapshot.extend_realizes names start valuation world))

end Gabbro.Grammatik.Vertraege.Pruefer.Symbolic
