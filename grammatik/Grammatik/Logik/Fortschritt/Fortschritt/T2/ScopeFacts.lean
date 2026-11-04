module

public import Grammatik.Logik.Fortschritt.Fortschritt.T1

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

theorem scopesOk_alsBlock (haelt : List D.Lock) (boden : Option Int) {l : Bool} :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (b : Endblock D V l Γ Λ),
      b.alsBlock.2.scopesOk haelt boden = b.scopesOk haelt boden
  | _, _, .ret _ _ | _, _, .retWhy _ _ | _, _, .retScoped _ _ |
      _, _, .retWhyScoped _ _ | _, _, .leave _ | _, _, .next _ => by
      simp only [Endblock.alsBlock, Block.scopesOk, Stmt.scopesOk,
        Endblock.scopesOk, Bool.and_true]
  | _, _, .cons _ rest | _, _, .bind _ rest |
      _, _, .bindCall _ _ _ _ _ rest | _, _, .bindCallElse _ _ _ _ _ _ rest |
      _, _, .bindAxiom _ _ _ _ _ _ _ rest |
      _, _, .bindAxiomElse _ _ _ _ _ _ _ _ _ rest |
      _, _, .bindAxiomOpt _ _ _ _ _ _ _ rest |
      _, _, .bindAxiomOptElse _ _ _ _ _ _ _ _ _ rest |
      _, _, .regRead _ _ rest | _, _, .regReadElse _ _ _ _ rest |
      _, _, .awaits _ _ _ _ _ rest | _, _, .bindCallInd _ _ _ _ _ rest |
      _, _, .bindCallIndElse _ _ _ _ _ _ rest |
      _, _, .narrow _ _ _ _ rest | _, _, .narrowRequired _ _ _ rest |
      _, _, .exchange _ _ _ _ rest | _, _, .float _ _ _ _ _ rest |
      _, _, .floatLit _ _ _ rest | _, _, .floatOf _ _ _ rest |
      _, _, .floatNarrow _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.scopesOk, Endblock.scopesOk,
        scopesOk_alsBlock haelt boden rest]
  | _, _, .ite _ t _ => by
      simp only [Endblock.alsBlock, Block.scopesOk, Endblock.scopesOk,
        scopesOk_alsBlock haelt boden t, Bool.and_comm]

theorem scopesOk_armWahlG (haelt : List D.Lock) (boden : Option Int)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
      arms.scopesOk haelt boden = true →
        (armWahlG arms v).2.1.scopesOk haelt boden = true
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨⟨0, _⟩, _⟩, h => (Bool.and_eq_true_iff.mp h).1
  | _, .cons b rest, ⟨⟨n + 1, hn⟩, nutz⟩, h =>
      scopesOk_armWahlG haelt boden rest _ (Bool.and_eq_true_iff.mp h).2

theorem scopesOk_grundWahlG (haelt : List D.Lock) (boden : Option Int)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
      arms.scopesOk haelt boden = true →
        (grundWahlG arms r).scopesOk haelt boden = true
  | _, .nil, ⟨k, hk⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨0, _⟩, h => (Bool.and_eq_true_iff.mp h).1
  | _, .cons b rest, ⟨k + 1, hk⟩, h =>
      scopesOk_grundWahlG haelt boden rest _ (Bool.and_eq_true_iff.mp h).2

/-- The existing source scope check, retained on every remaining source
    fragment. This is independent of memory and the replay's read footprint. -/
def GRest.scopesGut : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop
  | _, _, _, .ende b => b.scopesOk V.haelt V.boden = true
  | _, _, _, .dann b k => b.scopesOk V.haelt V.boden = true ∧ k.scopesGut
  | _, _, _, .schrumpf k => k.scopesGut
  | _, _, _, .frei _ k => k.scopesGut
  | _, _, _, .trav _ _ b _ k => b.scopesOk V.haelt V.boden = true ∧ k.scopesGut
  | _, _, _, .travRest _ _ b _ k => b.scopesOk V.haelt V.boden = true ∧ k.scopesGut
  | _, _, _, .verbrauch _ _ _ _ _ _ b _ k => b.scopesOk V.haelt V.boden = true ∧ k.scopesGut
  | _, _, _, .verbrauchRest _ _ _ _ _ _ b _ _ k => b.scopesOk V.haelt V.boden = true ∧ k.scopesGut
  | _, _, _, .wieder _ _ b e k =>
      b.scopesOk V.haelt V.boden = true ∧ e.scopesOk V.haelt V.boden = true ∧ k.scopesGut
  | _, _, _, .wiederRest _ _ b e k =>
      b.scopesOk V.haelt V.boden = true ∧ e.scopesOk V.haelt V.boden = true ∧ k.scopesGut
  | _, _, _, .ewig _ _ _ b k => b.scopesOk V.haelt V.boden = true ∧ k.scopesGut
  | _, _, _, .ewigRest _ _ _ b k => b.scopesOk V.haelt V.boden = true ∧ k.scopesGut
  | _, _, _, .wartet b k => b.scopesOk V.haelt V.boden = true ∧ k.scopesGut
  | _, _, _, .wartetSonst _ e b k =>
      e.scopesOk V.haelt V.boden = true ∧ b.scopesOk V.haelt V.boden = true ∧ k.scopesGut
  | _, _, _, .abbruch k => k.scopesGut
  | _, _, _, .rueckBereit _ k => k.scopesGut
  | _, _, _, .zurueckgekehrt _ => True
  | _, _, _, .aufraeumen _ _ => True
  | _, _, _, .leer => True

theorem scopesGut_weiterOpt {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (e : Option Ty) (k : GRest D V l Γ Λ') :
    (GRest.weiterOpt (Λ := Λ) e k).scopesGut ↔ k.scopesGut := by
  cases e <;> exact Iff.rfl

end Gabbro.Grammatik
