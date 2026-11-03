module

public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.ScopeMarkers

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Equality of held-resource multiplicities; marks may differ. -/
def HeldCountEq (Λ Λ' : List (Res D)) : Prop :=
  ∀ L : D.Lock, Λ.count (Res.held L) = Λ'.count (Res.held L)

/-- Balance throughout a continuation. Blocks preserve held counts, so only
    terminal nodes and the freely indexed abrupt-exit shim need an equation.
    The retired `rueckBereit` placeholder is never entered by G. -/
def GRest.scopeChain {V : Vertrag D} :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop
  | _, _, Λ, .ende _ => HeldCountEq Λ V.ende
  | _, _, _, .dann _ k => k.scopeChain
  | _, _, _, .schrumpf k => k.scopeChain
  | _, _, _, .frei _ k => k.scopeChain
  | _, _, _, .trav _ _ _ _ k => k.scopeChain
  | _, _, _, .travRest _ _ _ _ k => k.scopeChain
  | _, _, _, .verbrauch _ _ _ _ _ _ _ _ k => k.scopeChain
  | _, _, _, .verbrauchRest _ _ _ _ _ _ _ _ _ k => k.scopeChain
  | _, _, _, .wieder _ _ _ _ k => k.scopeChain
  | _, _, _, .wiederRest _ _ _ _ k => k.scopeChain
  | _, _, _, .ewig _ _ _ _ k => k.scopeChain
  | _, _, _, .ewigRest _ _ _ _ k => k.scopeChain
  | _, _, _, .wartet _ k => k.scopeChain
  | _, _, _, .wartetSonst _ _ _ k => k.scopeChain
  | _, _, Λ, @GRest.abbruch _ _ _ _ _ Λk k => HeldCountEq Λ Λk ∧ k.scopeChain
  | _, _, Λ, .leer => HeldCountEq Λ V.ende
  | _, _, _, .rueckBereit _ _ => False
  | _, _, _, .zurueckgekehrt _ => True
  | _, _, _, .aufraeumen _ _ => True

/-- The continuation invariant supplies the previously missing head balance. -/
theorem GRest.scopeChain_balance {V : Vertrag D} :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ),
      r.scopeChain → r.scopeBalance
  | _, _, _, .ende _, h => by
      intro L
      simpa only [GRest.freis, List.count_nil, Nat.add_zero] using h L
  | _, _, _, .dann b k, h => by
      intro L
      exact (block_heldCount L b).symm.trans (k.scopeChain_balance h L)
  | _, _, _, .schrumpf k, h => k.scopeChain_balance h
  | _, _, _, .frei K k, h => by
      intro L
      have hk := k.scopeChain_balance h L
      by_cases he : K = L
      · subst K
        simp only [GRest.freis, List.count_cons_self]
        omega
      · have hres : Res.held K ≠ Res.held L := by
          intro hh
          cases hh
          exact he rfl
        simp only [GRest.freis, List.count_cons_of_ne he, List.count_cons_of_ne hres]
        exact hk
  | _, _, _, .trav _ _ _ _ k, h => k.scopeChain_balance h
  | _, _, _, .travRest _ _ _ _ k, h => k.scopeChain_balance h
  | _, _, _, .verbrauch _ _ _ _ _ _ _ _ k, h => k.scopeChain_balance h
  | _, _, _, .verbrauchRest _ _ _ _ _ _ _ _ _ k, h => k.scopeChain_balance h
  | _, _, _, .wieder _ _ _ _ k, h => k.scopeChain_balance h
  | _, _, _, .wiederRest _ _ _ _ k, h => k.scopeChain_balance h
  | _, _, _, .ewig _ _ _ _ k, h => k.scopeChain_balance h
  | _, _, _, .ewigRest _ _ _ _ k, h => k.scopeChain_balance h
  | _, _, _, .wartet b k, h => by
      intro L
      exact (block_heldCount L b).symm.trans (k.scopeChain_balance h L)
  | _, _, _, .wartetSonst _ _ b k, h => by
      intro L
      exact (block_heldCount L b).symm.trans (k.scopeChain_balance h L)
  | _, _, _, .abbruch k, h => fun L => (h.1 L).trans (k.scopeChain_balance h.2 L)
  | _, _, _, .leer, h => by
      intro L
      simpa only [GRest.freis, List.count_nil, Nat.add_zero] using h L
  | _, _, _, .rueckBereit _ _, h => h.elim
  | _, _, _, .zurueckgekehrt a, _ => GRest.scopeBalance_zurueckgekehrt a
  | _, _, _, .aufraeumen a remaining, _ => GRest.scopeBalance_aufraeumen a remaining

/-- Fresh source entries balance independently of the source's scope check:
    the entry and exit signatures have exactly the same held counts. -/
theorem GRest.scopeChain_eintritt {P : Programm D} (g : D.Fn) :
    (GRest.ende (P.rumpf g)).scopeChain := by
  intro L
  simpa only [GRest.freis, List.count_nil, Nat.add_zero] using
    (GRest.scopeBalance_eintritt (P := P) g L)

/-- Fold the dependent sigma before rewriting a frame's residue. -/
def RestScopeBalance {V : Vertrag D}
    (x : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ) : Prop :=
  x.2.2.2.2.scopeChain

def FadenScopeBalanceG (z : RufFadenG D) : Prop :=
  RestScopeBalance z.kopf.rest ∧ ∀ c ∈ z.stapel, RestScopeBalance c.rest

/-- Frame-local version used by segment cost proofs: callers below the
    measured frame need no balance premise. -/
theorem scopeBalance_von {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {r : GRest D V l Γ Λ}
    {x : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ}
    (hx : x = ⟨l, Γ, Λ, ρ, r⟩) (h : RestScopeBalance x) : r.scopeBalance := by
  rw [hx] at h
  exact r.scopeChain_balance h

/-- Obtain head balance using a non-dependent frame equation. -/
theorem FadenScopeBalanceG.kopf {z : RufFadenG D} (h : FadenScopeBalanceG z)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ}
    (hx : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩) : r.scopeBalance := by
  have hk := h.1
  rw [hx] at hk
  exact r.scopeChain_balance hk

end Gabbro.Grammatik
