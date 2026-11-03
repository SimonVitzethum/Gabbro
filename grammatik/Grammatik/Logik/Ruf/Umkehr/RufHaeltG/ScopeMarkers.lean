module

public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.T1

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The resource balance of a residue. Each non-signature held resource
    has one pending lexical release marker, counting multiplicities.
    This is an internal reachable-state invariant, not a program premise. -/
def GRest.scopeBalance {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r : GRest D V l Γ Λ) : Prop :=
  ∀ L : D.Lock, Λ.count (Res.held L) = V.ende.count (Res.held L) + r.freis.count L

/-- Exact residual resources identify the cleanup list with the pending
    lexical markers. No ordering or duplicate-free assumption is needed
    for this counting argument. -/
theorem GRest.scopes_perm_freis {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (r : GRest D V l Γ Λ) (R : RueckRessourcen D V Λ)
    (h : r.scopeBalance) : R.scopes.Perm r.freis := by
  apply List.perm_iff_count.mpr
  intro L
  have hp := count_of_perm (a := Res.held L) R.genau
  rw [List.count_append, count_held_map] at hp
  have hb := h L
  omega

/-- In particular, the number of release steps equals the number of
    pending lexical markers; each marker already has a unit of source
    potential. -/
theorem GRest.scopes_length {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (r : GRest D V l Γ Λ) (R : RueckRessourcen D V Λ)
    (h : r.scopeBalance) : R.scopes.length = r.freis.length :=
  (r.scopes_perm_freis R h).length_eq

/-- An evaluated cleanup residue has precisely the remaining scope
    resources. Releasing one head marker preserves this balance. -/
theorem GRest.scopeBalance_aufraeumen {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (a : (ErgVal D V.erg ⊕ Fin V.gruende) × World D) (remaining : List D.Lock) :
    (GRest.aufraeumen (l := l) (Γ := Γ) a remaining).scopeBalance := by
  intro L
  simp only [GRest.scopeBalance, GRest.freis, List.count_append, count_held_map]
  omega

/-- Finished scoped roots have no remaining lexical releases. -/
theorem GRest.scopeBalance_zurueckgekehrt {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (a : (ErgVal D V.erg ⊕ Fin V.gruende) × World D) :
    (GRest.zurueckgekehrt (l := l) (Γ := Γ) a).scopeBalance := by
  intro L
  simp only [GRest.freis, List.count_nil, Nat.add_zero]

/-- A source frame enters without any lexical scope markers. -/
theorem GRest.scopeBalance_eintritt {P : Programm D} (g : D.Fn) :
    (GRest.ende (P.rumpf g)).scopeBalance := by
  intro L
  simp only [GRest.freis, List.count_nil, Nat.add_zero]
  simp only [Signatur.anfang, Vertrag.ende, vertragVon, Vertrag.vonSig,
    List.count_append, count_held_marke_map, Nat.add_zero]

end Gabbro.Grammatik
