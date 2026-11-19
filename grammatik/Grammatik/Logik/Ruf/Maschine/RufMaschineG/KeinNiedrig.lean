module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T1Basis

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- A discarded continuation contains no active low-level scope. This scan is
    exhaustive so adding a scope marker requires an explicit refusal case.
    Source blocks are pending code, not active scopes. -/
def GRest.keinNiedrig {V : Vertrag D} :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop
  | _, _, _, .ende _ => True
  | _, _, _, .dann _ k => k.keinNiedrig
  | _, _, _, .schrumpf k => k.keinNiedrig
  | _, _, _, .frei _ k => k.keinNiedrig
  | _, _, _, .trav _ _ _ _ k => k.keinNiedrig
  | _, _, _, .travRest _ _ _ _ k => k.keinNiedrig
  | _, _, _, .wieder _ _ _ _ k => k.keinNiedrig
  | _, _, _, .wiederRest _ _ _ _ k => k.keinNiedrig
  | _, _, _, .ewig _ _ _ _ k => k.keinNiedrig
  | _, _, _, .ewigRest _ _ _ _ k => k.keinNiedrig
  | _, _, _, .wartet _ k => k.keinNiedrig
  | _, _, _, .wartetSonst _ _ _ k => k.keinNiedrig
  | _, _, _, .abbruch k => k.keinNiedrig
  | _, _, _, .leer => True
  | _, _, _, .rueckBereit _ k => k.keinNiedrig
  | _, _, _, .verbrauch _ _ _ _ _ _ _ _ k => k.keinNiedrig
  | _, _, _, .verbrauchRest _ _ _ _ _ _ _ _ _ k => k.keinNiedrig
  | _, _, _, .zurueckgekehrt _ => True
  | _, _, _, .aufraeumen _ _ => True

/-- The pre-scope machine has no low-level markers. This preparatory fact
    must be replaced by reachable-state evidence when such markers are added. -/
theorem GRest.keinNiedrig_alt {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (k : GRest D V l Γ Λ) : k.keinNiedrig := by
  induction k <;> first | assumption | trivial

end Gabbro.Grammatik
