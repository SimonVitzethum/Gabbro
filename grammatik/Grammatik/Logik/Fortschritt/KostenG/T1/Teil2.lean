module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG
public import Grammatik.Logik.Ruf.Umkehr.RufUmkehrRufG
public import Grammatik.Logik.Fortschritt.KostenG.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Positiv
variable (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}

/-- An end block run as a block costs `kostenSonst`. -/
theorem kostenBlock_alsBlock :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ),
      kostenBlock c pa e.alsBlock.2 = kostenSonst c pa e
  | _, _, .ret _ _ => by simp only [Endblock.alsBlock, kostenBlock, kostenStmt, kostenSonst]; omega
  | _, _, .retWhy _ _ => by simp only [Endblock.alsBlock, kostenBlock, kostenStmt, kostenSonst]
  | _, _, .retScoped _ _ => by simp only [Endblock.alsBlock, kostenBlock, kostenStmt, kostenSonst]; omega
  | _, _, .retWhyScoped _ _ => by simp only [Endblock.alsBlock, kostenBlock, kostenStmt, kostenSonst]
  | _, _, .leave _ => by simp only [Endblock.alsBlock, kostenBlock, kostenStmt, kostenSonst]
  | _, _, .next _ => by simp only [Endblock.alsBlock, kostenBlock, kostenStmt, kostenSonst]
  | _, _, .cons s rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .bind e rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .bindCall g args _ _ _ rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .bindAxiom _ args _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .bindCallElse _ args _ _ _ err rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .bindAxiomElse _ args _ _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .bindAxiomOpt _ _ args _ _ _ _ rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .bindAxiomOptElse _ _ args _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .regRead r hk rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .regReadElse r hk z sonst rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .awaits g pl hp hL hat rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .bindCallInd p args he hp hr rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .bindCallIndElse p args he hp hr err rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .narrow _ _ _ _ rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .narrowRequired _ _ _ rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .exchange _ _ _ _ rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .ite _ t _ => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock t]

/-- An end block run as a block names the callees the end block names. -/
theorem rufeB_alsBlock (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ),
      rufeB Z ZS EW e.alsBlock.2 = rufeE Z ZS EW e
  | _, _, .ret _ _ => rfl
  | _, _, .retWhy _ _ => rfl
  | _, _, .retScoped _ _ => rfl
  | _, _, .retWhyScoped _ _ => rfl
  | _, _, .leave _ => rfl
  | _, _, .next _ => rfl
  | _, _, .cons s rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .bind e rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .bindCall _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .bindAxiom _ _ _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .bindCallElse _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .bindAxiomOpt _ _ _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .regRead r hk rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .regReadElse r hk z sonst rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .awaits g pl hp hL hat rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .bindCallInd p args he hp hr rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .bindCallIndElse p args he hp hr err rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .narrow _ _ _ _ rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .narrowRequired _ _ _ rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .exchange _ _ _ _ rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .ite _ t _ => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW t]

end Positiv
/-! ## 4. Arm selection keeps cost and callees -/

theorem kostenBlock_armWahlG (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    kostenBlock c pa (armWahlG arms v).2.1 ≤ kostenArms c pa arms
  | _, .nil, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨⟨0, _⟩, _⟩ => by
      simp only [armWahlG, kostenArms]; omega
  | _, .cons b rest, ⟨⟨n + 1, h⟩, nutz⟩ => by
      have ih := kostenBlock_armWahlG c pa rest ⟨⟨n, Nat.lt_of_succ_lt_succ h⟩, nutz⟩
      simp only [armWahlG, kostenArms]; omega

theorem rufeB_armWahlG (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    rufeArms Z ZS EW arms = true → rufeB Z ZS EW (armWahlG arms v).2.1 = true
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨⟨0, _⟩, _⟩, h => by
      simp only [rufeArms, Bool.and_eq_true] at h
      exact h.1
  | _, .cons b rest, ⟨⟨n + 1, hn⟩, nutz⟩, h => by
      simp only [rufeArms, Bool.and_eq_true] at h
      exact rufeB_armWahlG Z ZS EW rest _ h.2

theorem kostenBlock_grundWahlG (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    kostenBlock c pa (grundWahlG arms r) ≤ kostenGrundArms c pa arms
  | _, .nil, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨0, _⟩ => by
      simp only [grundWahlG, kostenGrundArms]; omega
  | _, .cons b rest, ⟨k + 1, h⟩ => by
      have ih := kostenBlock_grundWahlG c pa rest ⟨k, Nat.lt_of_succ_lt_succ h⟩
      simp only [grundWahlG, kostenGrundArms]; omega

theorem rufeB_grundWahlG (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    rufeGArms Z ZS EW arms = true → rufeB Z ZS EW (grundWahlG arms r) = true
  | _, .nil, ⟨k, hk⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨0, _⟩, h => by
      simp only [rufeGArms, Bool.and_eq_true] at h
      exact h.1
  | _, .cons b rest, ⟨k + 1, hk⟩, h => by
      simp only [rufeGArms, Bool.and_eq_true] at h
      exact rufeB_grundWahlG Z ZS EW rest _ h.2

/-- The index list of a `traverse` has at most `count` entries. -/
theorem alleIndizes_length_toNat (n : Int) : (alleIndizes n).length ≤ n.toNat := by
  unfold alleIndizes
  have h := List.length_filterMap_le
    (fun (k : Nat) => if h : ((k : Nat) : Int) ≤ n - 1 then
      some (⟨((k : Nat) : Int), by omega, h⟩ : Zahl 0 (n - 1)) else none) (List.range n.toNat)
  rw [List.length_range] at h
  exact h

/-! ## 5. One own step of the head

    Every step of thread `f` is one of three kinds (`schrittArt`):
    * (A) the head frame moves and the stack stays -- its potential drops
      by at least one;
    * (B) a push -- the callee enters its body, the caller continues below
      it, and the caller's potential drops by at least one PLUS the cost
      `c g` it counted for the callee (an indirect call admitted by `ZS`:
      by at least one, its callee uncounted);
    * (C) a pop -- the stepping head frame (potential at least one, `potRest_pos`)
      leaves and the caller below resumes with at most its old potential.
    And the callees named in the residue stay admitted (`rufeR`). With
    `ZS = fun _ => false` an indirect-call push falls in (B) only
    vacuously: its residue fails `rufeR`. -/

set_option hygiene false in
/-- Case (A) of `schrittArt`: rewrite the new head and the old head into
    their residues and unfold the costs. -/
macro "kopfA" : tactic => `(tactic| (
  refine Or.inl ⟨by dsimp only; rw [rufUpdateG_self], fun hok => ⟨?_, ?_⟩⟩ <;> dsimp only <;>
  rw [rufUpdateG_self] <;>
  rw [‹(M.faeden f).kopf.rest = _›] at hok <;> (try rw [‹(M.faeden f).kopf.rest = _›]) <;>
  dsimp only at hok ⊢ <;>
  simp only [GRest.weiterOpt, potRest, kostenEnd, kostenBlock, kostenStmt, rufeR, rufeE, rufeB, rufeS,
    kostenBlock_alsBlock, rufeB_alsBlock,
    Bool.and_eq_true, List.length_cons, Nat.add_mul, Nat.one_mul] at hok ⊢))
