module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T3
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T4.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-! ## 6a. No head ever waits: the deadlock of the verbatim pops is gone

    A waiting residue (`wartet`/`wartetSonst`) is created only in a PUSHED
    caller frame, and only a binding pop resumes it; the verbatim pops
    (`rueck`, `rueckCons`, `dannRet`) now demand a caller that does not
    wait (`hnw`). So the invariant "the head residue contains no waiting
    node, and every stacked residue is either clean or waits over a clean
    continuation" holds at the start and is kept by every rule; in
    particular no reachable head is a waiting residue (`rufG_nie_wartend`),
    the state in which only the bare lock steps could fire. -/

/-- A residue with no waiting node anywhere along its continuation. -/
def GRest.sauber {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Bool
  | .ende _ => true
  | .dann _ k => k.sauber
  | .schrumpf k => k.sauber
  | .frei _ k => k.sauber
  | .trav _ _ _ _ k => k.sauber
  | .travRest _ _ _ _ k => k.sauber
  | .wieder _ _ _ _ k => k.sauber
  | .wiederRest _ _ _ _ k => k.sauber
  | .ewig _ _ _ _ k => k.sauber
  | .ewigRest _ _ _ _ k => k.sauber
  | .wartet _ _ => false
  | .wartetSonst _ _ _ _ => false
  | .abbruch k => k.sauber
  | .leer => true

/-- A stacked residue: clean, or waiting over a clean continuation. -/
def GRest.stapelSauber {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Bool
  | .wartet _ k => k.sauber
  | .wartetSonst _ _ _ k => k.sauber
  | r => r.sauber

theorem GRest.sauber_wartend {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {r : GRest D V l Γ Λ} (h : r.sauber = true) : r.wartend = false := by
  cases r <;> simp_all [GRest.sauber, GRest.wartend]

theorem GRest.stapelSauber_sauber {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {r : GRest D V l Γ Λ} (hw : r.wartend = false) (h : r.stapelSauber = true) :
    r.sauber = true := by
  cases r <;> simp_all [GRest.sauber, GRest.stapelSauber, GRest.wartend]

/-- The thread invariant: a clean head, clean-or-waiting stacked frames. -/
def RufFadenSauberG (z : RufFadenG D) : Prop :=
  z.kopf.rest.2.2.2.2.sauber = true ∧ ∀ r ∈ z.stapel, r.rest.2.2.2.2.stapelSauber = true

/-- The invariant implies a head that does not wait. -/
theorem RufFadenSauberG.kopf_wartend {z : RufFadenG D} (h : RufFadenSauberG z) :
    z.kopf.wartend = false :=
  GRest.sauber_wartend h.1


end Gabbro.Grammatik
