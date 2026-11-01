module

public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Logik.Ruf.Ohne.RufOhneHardware.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section HardwareFrei
variable {V : Vertrag D}
variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

mutual

theorem Stmt.hardwareFrei_ok (hR : OhneHardware R) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → s.hardwareFrei = true →
      ∀ (σ : World D) (ρ : Env D Γ) (e : Hardware D), execStmt O passes R s σ ρ ≠ .hardware e
  | .ite c t e, h, σ, ρ, e', he => by
      simp only [Stmt.hardwareFrei, Bool.and_eq_true] at h
      simp only [execStmt] at he
      split at he
      · exact Block.hardwareFrei_ok hR t h.1 _ _ _ he
      · exact Block.hardwareFrei_ok hR e h.2 _ _ _ he
  | .onOption o p a, h, σ, ρ, e', he => by
      simp only [Stmt.hardwareFrei, Bool.and_eq_true] at h
      simp only [execStmt] at he
      split at he
      · exact Block.hardwareFrei_ok hR p h.1 _ _ _ (Ausgang.schrumpf_hardware he)
      · exact Block.hardwareFrei_ok hR a h.2 _ _ _ he
  | .onTag v arms, h, σ, ρ, e', he => by
      simp only [Stmt.hardwareFrei] at h
      simp only [execStmt] at he
      exact Arms.hardwareFrei_ok hR arms h _ _ _ _ he
  | .onWhy r arms, h, σ, ρ, e', he => by
      simp only [Stmt.hardwareFrei] at h
      simp only [execStmt] at he
      exact GrundArms.hardwareFrei_ok hR arms h _ _ _ _ he
  | .locks L hr body, h, σ, ρ, e', he => by
      simp only [Stmt.hardwareFrei] at h
      simp only [execStmt] at he
      exact Block.hardwareFrei_ok hR body h _ _ _ (Ausgang.mapWelt_hardware he)
  | .breaking i body, h, σ, ρ, e', he => by
      simp only [Stmt.hardwareFrei] at h
      simp only [execStmt] at he
      exact Block.hardwareFrei_ok hR body h _ _ _ he
  | .traverse t inv body, h, σ, ρ, e', he => by
      simp only [Stmt.hardwareFrei] at h
      simp only [execStmt] at he
      exact traverseLauf_ohneHardware _ _
        (fun σ ρ e => Block.hardwareFrei_ok hR body h σ ρ e) _ σ ρ e' he
  | .retry n bis body ueber, h, σ, ρ, e', he => by
      simp only [Stmt.hardwareFrei, Bool.and_eq_true] at h
      simp only [execStmt] at he
      exact retryLauf_ohneHardware _ _ _ (fun σ ρ e => Block.hardwareFrei_ok hR body h.1 σ ρ e)
        (fun σ ρ e => Block.hardwareFrei_ok hR ueber h.2 σ ρ e) n σ ρ e' he
  | .call g args hp hr, _, σ, ρ, e', he => by
      simp only [execStmt] at he
      split at he
      · cases he
      · rename_i r _
        exact (Fin.cast hr r).elim0
      · cases he
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
  | .callInd p args hp hr, _, σ, ρ, e', he => by
      simp only [execStmt] at he
      split at he
      rename_i f hf _
      split at he
      · cases he
      · rename_i r _
        exact keinGrundSig hf hr r
      · cases he
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
  | .forever .., h, _, _, _, _ => by simp only [Stmt.hardwareFrei, Bool.false_eq_true] at h
  | .axiomCall .., h, _, _, _, _ => by simp only [Stmt.hardwareFrei, Bool.false_eq_true] at h
  | .shift .., _, _, _, _, he => by
      simp only [execStmt] at he
      split at he <;> cases he
  | .assignSlot .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .assignThru .., _, _, _, _, he | .assignSlotRef .., _, _, _, _, he => by simp only [execStmt, List.append_assoc, reduceCtorEq] at he
  | .assignGlob .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .putBytes .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .assignVar .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .regWrite .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .transition .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .publish .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .advances .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .retires .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .ret .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .retWhy .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .leave .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he
  | .next .., _, _, _, _, he => by simp only [execStmt, reduceCtorEq] at he

theorem Block.hardwareFrei_ok (hR : OhneHardware R) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → b.hardwareFrei = true →
      ∀ (σ : World D) (ρ : Env D Γ) (e : Hardware D), execBlock O passes R b σ ρ ≠ .hardware e
  | .nil, _, σ, ρ, e, he => by simp only [execBlock, reduceCtorEq] at he
  | .cons s rest, h, σ, ρ, e, he => by
      simp only [Block.hardwareFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.hardwareFrei_ok hR rest h.2 _ _ _ he
      · exact Stmt.hardwareFrei_ok hR s h.1 σ ρ e he
  | .bind x rest, h, σ, ρ, e, he => by
      simp only [Block.hardwareFrei] at h
      simp only [execBlock] at he
      exact Block.hardwareFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_hardware he)
  | .bindCall g args he' hp hr rest, h, σ, ρ, e, he => by
      simp only [Block.hardwareFrei] at h
      simp only [execBlock] at he
      split at he
      · exact Block.hardwareFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_hardware he)
      · rename_i r _
        exact (Fin.cast hr r).elim0
      · cases he
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
  | .bindCallInd p args he' hp hr rest, h, σ, ρ, e, he => by
      simp only [Block.hardwareFrei] at h
      simp only [execBlock] at he
      split at he
      rename_i f hf _
      split at he
      · exact Block.hardwareFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_hardware he)
      · rename_i r _
        exact keinGrundSig hf hr r
      · cases he
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
  | .bindCallElse g args he' hp hr err rest, h, σ, ρ, e, he => by
      simp only [Block.hardwareFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.hardwareFrei_ok hR rest h.2 _ _ _ (Ausgang.schrumpf_hardware he)
      · exact Endblock.hardwareFrei_ok hR err h.1 _ _ _
          (EndAusgang.schrumpf_hardware (EndAusgang.zuAusgang_hardware he))
      · cases he
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
  | .bindAxiom .., h, _, _, _, _ => by simp only [Block.hardwareFrei, Bool.false_eq_true] at h
  | .bindAxiomElse .., h, _, _, _, _ => by simp only [Block.hardwareFrei, Bool.false_eq_true] at h
  | .regRead .., h, _, _, _, _ => by simp only [Block.hardwareFrei, Bool.false_eq_true] at h
  | .regReadElse .., h, _, _, _, _ => by simp only [Block.hardwareFrei, Bool.false_eq_true] at h
  | .awaits .., h, _, _, _, _ => by simp only [Block.hardwareFrei, Bool.false_eq_true] at h
  | .exchange g neu hw hL rest, h, σ, ρ, e, he => by
      simp only [Block.hardwareFrei] at h
      simp only [execBlock] at he
      exact Block.hardwareFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_hardware he)
  | .narrow x lo' hi' sonst rest, h, σ, ρ, e, he => by
      simp only [Block.hardwareFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.hardwareFrei_ok hR rest h.2 _ _ _ (Ausgang.schrumpf_hardware he)
      · exact Endblock.hardwareFrei_ok hR sonst h.1 _ _ _ (EndAusgang.zuAusgang_hardware he)
  | .check c sonst rest, h, σ, ρ, e, he => by
      simp only [Block.hardwareFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.hardwareFrei_ok hR rest h.2 _ _ _ he
      · exact Endblock.hardwareFrei_ok hR sonst h.1 _ _ _ (EndAusgang.zuAusgang_hardware he)
  | .float op a b lo hi rest, h, σ, ρ, e, he => by
      simp only [Block.hardwareFrei] at h
      simp only [execBlock] at he
      split at he
      · exact Block.hardwareFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_hardware he)
      · cases he
  | .floatLit q lo hi rest, h, σ, ρ, e, he => by
      simp only [Block.hardwareFrei] at h
      simp only [execBlock] at he
      split at he
      · exact Block.hardwareFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_hardware he)
      · cases he
  | .floatOf x lo hi rest, h, σ, ρ, e, he => by
      simp only [Block.hardwareFrei] at h
      simp only [execBlock] at he
      split at he
      · exact Block.hardwareFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_hardware he)
      · cases he
  | .floatNarrow x lo hi sonst rest, h, σ, ρ, e, he => by
      simp only [Block.hardwareFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.hardwareFrei_ok hR rest h.2 _ _ _ (Ausgang.schrumpf_hardware he)
      · exact Endblock.hardwareFrei_ok hR sonst h.1 _ _ _ (EndAusgang.zuAusgang_hardware he)

theorem Endblock.hardwareFrei_ok (hR : OhneHardware R) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (b : Endblock D V l Γ Λ) → b.hardwareFrei = true →
      ∀ (σ : World D) (ρ : Env D Γ) (e : Hardware D), execEnd O passes R b σ ρ ≠ .hardware e
  | .ret .., _, _, _, _, he => by simp only [execEnd, reduceCtorEq] at he
  | .retWhy .., _, _, _, _, he => by simp only [execEnd, reduceCtorEq] at he
  | .leave .., _, _, _, _, he => by simp only [execEnd, reduceCtorEq] at he
  | .next .., _, _, _, _, he => by simp only [execEnd, reduceCtorEq] at he
  | .cons s rest, h, σ, ρ, e, he => by
      simp only [Endblock.hardwareFrei, Bool.and_eq_true] at h
      simp only [execEnd] at he
      split at he
      · exact Endblock.hardwareFrei_ok hR rest h.2 _ _ _ he
      · cases he
      · cases he
      · cases he
      · cases he
      · cases he
      · rename_i heq
        cases he
        exact Stmt.hardwareFrei_ok hR s h.1 σ ρ e heq
  | .bind x rest, h, σ, ρ, e, he => by
      simp only [Endblock.hardwareFrei] at h
      simp only [execEnd] at he
      exact Endblock.hardwareFrei_ok hR rest h _ _ _ (EndAusgang.schrumpf_hardware he)
  | .bindCall g args he' hp hr rest, h, σ, ρ, e, he => by
      simp only [Endblock.hardwareFrei] at h
      simp only [execEnd] at he
      split at he
      · exact Endblock.hardwareFrei_ok hR rest h _ _ _ (EndAusgang.schrumpf_hardware he)
      · rename_i r _
        exact (Fin.cast hr r).elim0
      · cases he
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
  | .bindCallElse g args he' hp hr err rest, h, σ, ρ, e, he => by
      simp only [Endblock.hardwareFrei, Bool.and_eq_true] at h
      simp only [execEnd] at he
      split at he
      · exact Endblock.hardwareFrei_ok hR rest h.2 _ _ _ (EndAusgang.schrumpf_hardware he)
      · exact Endblock.hardwareFrei_ok hR err h.1 _ _ _
          (EndAusgang.schrumpf_hardware he)
      · cases he
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
  | .bindAxiom .., h, _, _, _, _ => by simp only [Endblock.hardwareFrei, Bool.false_eq_true] at h
  | .bindAxiomElse .., h, _, _, _, _ => by simp only [Endblock.hardwareFrei, Bool.false_eq_true] at h
  | .regRead .., h, _, _, _, _ => by simp only [Endblock.hardwareFrei, Bool.false_eq_true] at h
  | .regReadElse .., h, _, _, _, _ => by simp only [Endblock.hardwareFrei, Bool.false_eq_true] at h
  | .awaits .., h, _, _, _, _ => by simp only [Endblock.hardwareFrei, Bool.false_eq_true] at h
  | .bindCallInd p args he' hp hr rest, h, σ, ρ, e, he => by
      simp only [Endblock.hardwareFrei] at h
      simp only [execEnd] at he
      split at he
      rename_i f hf _
      split at he
      · exact Endblock.hardwareFrei_ok hR rest h _ _ _ (EndAusgang.schrumpf_hardware he)
      · rename_i r _
        exact keinGrundSig hf hr r
      · cases he
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
  | .narrow x lo' hi' sonst rest, h, σ, ρ, e, he => by
      simp only [Endblock.hardwareFrei, Bool.and_eq_true] at h
      simp only [execEnd] at he
      split at he
      · exact Endblock.hardwareFrei_ok hR rest h.2 _ _ _ (EndAusgang.schrumpf_hardware he)
      · exact Endblock.hardwareFrei_ok hR sonst h.1 _ _ _ he
  | .exchange g neu hw hL rest, h, σ, ρ, e, he => by
      simp only [Endblock.hardwareFrei] at h
      simp only [execEnd] at he
      exact Endblock.hardwareFrei_ok hR rest h _ _ _ (EndAusgang.schrumpf_hardware he)
  | .ite c t e', h, σ, ρ, e, he => by
      simp only [Endblock.hardwareFrei, Bool.and_eq_true] at h
      simp only [execEnd] at he
      split at he
      · exact Endblock.hardwareFrei_ok hR t h.1 _ _ _ he
      · exact Endblock.hardwareFrei_ok hR e' h.2 _ _ _ he

theorem Arms.hardwareFrei_ok (hR : OhneHardware R) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    (a : Arms D V l Γ Λ Λ' cs) → a.hardwareFrei = true →
      ∀ (v : Wert D (.sum cs)) (σ : World D) (ρ : Env D Γ) (e : Hardware D),
        execArms O passes R a v σ ρ ≠ .hardware e
  | .nil, _, ⟨⟨k, hk⟩, _⟩, _, _, _, _ => (Nat.not_lt_zero k hk).elim
  | .cons b rest, h, ⟨⟨0, _⟩, nutz⟩, σ, ρ, e, he => by
      simp only [Arms.hardwareFrei, Bool.and_eq_true] at h
      simp only [execArms] at he
      exact Block.hardwareFrei_ok hR b h.1 _ _ _ (Ausgang.schrumpfArm_hardware he)
  | .cons b rest, h, ⟨⟨i + 1, hk⟩, nutz⟩, σ, ρ, e, he => by
      simp only [Arms.hardwareFrei, Bool.and_eq_true] at h
      simp only [execArms] at he
      exact Arms.hardwareFrei_ok hR rest h.2 _ _ _ _ he

theorem GrundArms.hardwareFrei_ok (hR : OhneHardware R) {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} :
    (a : GrundArms D V l Γ Λ Λ' n) → a.hardwareFrei = true →
      ∀ (r : Fin n) (σ : World D) (ρ : Env D Γ) (e : Hardware D),
        execGrund O passes R a r σ ρ ≠ .hardware e
  | .nil, _, r, _, _, _, _ => r.elim0
  | .cons b rest, h, ⟨0, _⟩, σ, ρ, e, he => by
      simp only [GrundArms.hardwareFrei, Bool.and_eq_true] at h
      simp only [execGrund] at he
      exact Block.hardwareFrei_ok hR b h.1 _ _ _ he
  | .cons b rest, h, ⟨i + 1, hk⟩, σ, ρ, e, he => by
      simp only [GrundArms.hardwareFrei, Bool.and_eq_true] at h
      simp only [execGrund] at he
      exact GrundArms.hardwareFrei_ok hR rest h.2 _ _ _ _ he

end

end HardwareFrei

/-! ## 4. The program-level check, and `rufAt` at every depth -/

/-- **The program carries no oracle form**: every body of the member list
    passes the check. A Boolean computation over the program text. -/
def programmHardwareFrei (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun f => (P.rumpf f).hardwareFrei

/-- **A CALL OF SUCH A PROGRAM NEVER ENDS IN A HARDWARE OUTCOME**, at any
    recursion depth, from any world, with any arguments, against any oracle.

    The induction is on the DEPTH, and it needs no premise about the oracle
    or about the user's logic: `rufAt`'s own error branches are all `logik`
    (`abstieg` at depth `0`, `vorbedingung`, `nachbedingung`, `invariante`),
    so the handler premise `OhneHardware` carries itself from one depth to
    the next, and the body contributes none by the check. -/
theorem rufAt_ohneHardware (P : Programm D) (O : Orakel D) (passes : Nat)
    (hP : ∀ f : D.Fn, (P.rumpf f).hardwareFrei = true) :
    ∀ n : Nat, OhneHardware (rufAt P O passes n) := by
  intro n
  induction n with
  | zero => intro g σ ρ e h; simp only [rufAt, reduceCtorEq] at h
  | succ m ih =>
      intro g σ ρ e h
      simp only [rufAt] at h
      split at h
      · cases h
      · split at h
        · split at h
          · cases h
          · split at h
            · cases h
            · cases h
        · cases h
        · rename_i hl _ _ _; exact absurd hl (by decide)
        · rename_i hl _ _ _; exact absurd hl (by decide)
        · cases h
        · rename_i heq
          cases h
          exact Endblock.hardwareFrei_ok O passes _ ih (P.rumpf g) (hP g) _ ρ _ heq

/-- **One `rufAt` unfolding, hardware half**: with the requires gate open and
    the body ending in a hardware outcome, the call does (the twin of
    `rufAt_ok_of_gates`, VertragOrtB.lean, for the other outcome). -/
theorem rufAt_hardware_von_rumpf (P : Programm D) (O : Orakel D) (passes m : Nat)
    (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) (e : Hardware D)
    (hreq : wahr? (eval (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
      (P.requires f) (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ) = true)
    (hb : execEnd (V := vertragVon D f) O passes (rufAt P O passes m) (P.rumpf f)
      (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ = .hardware e) :
    rufAt P O passes (m + 1) f σ ρ = .hardware e := by
  simp only [rufAt]
  rw [if_neg (by rw [hreq]; simp only [Bool.true_eq_false, not_false_eq_true]), hb]

/-- The program-level form, over a member list of the functions. -/
theorem rufAt_ohneHardware_fs (P : Programm D) (O : Orakel D) (passes : Nat)
    {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) (h : programmHardwareFrei P fs = true) :
    ∀ n : Nat, OhneHardware (rufAt P O passes n) :=
  rufAt_ohneHardware P O passes (fun f => (List.all_eq_true.mp h) f (hvoll f))

#print axioms Gabbro.Grammatik.Endblock.hardwareFrei_ok
#print axioms Gabbro.Grammatik.rufAt_hardware_von_rumpf
#print axioms Gabbro.Grammatik.rufAt_ohneHardware

end Gabbro.Grammatik
