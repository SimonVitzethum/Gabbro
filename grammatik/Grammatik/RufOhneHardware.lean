/-
  File:      Grammatik/RufOhneHardware.lean
  Subject:   WHEN A CALL CANNOT END IN A HARDWARE OUTCOME -- the syntactic
             check `hardwareFrei` and its soundness, and the consequence for
             `rufAt` at every depth.

  The model knows exactly two error outcomes (`Semantik.lean`): the writer's
  logic (`Logik`) and an assumption about the machine (`Hardware`). The
  second one has FIVE sources, and every one of them is a syntactic form:

  * `Stmt.axiomCall` / `Block.bindAxiom` -- the axiom's raw answer does not
    fit its declared result type (`Hardware.annahme`);
  * `Block.regLies` -- the register's raw answer does not fit its declared
    type (`Hardware.register`) or breaks its declared promise
    (`Hardware.geraet`); `Block.regLiesElse` -- the type half of the same;
  * `Block.awaits` -- the memory model did not show the publication
    (`Hardware.sichtbarkeit`, A10);
  * `Stmt.forever` -- the environment's budget ran out
    (`Hardware.fortschritt`, H2).

  `Hardware.ieee` is no longer produced at all (verdict F1, 2026-09-15: an
  out-of-range float result is `Logik.bereich`).

  A body that carries none of those five forms therefore cannot end in a
  `hardware` outcome, against any handler that answers none either
  (`Endblock.hardwareFrei_ok`, the twin of `Endblock.logikFrei_ok` in
  `ZielOrtGanz.lean`). Since `rufAt`'s own error branches are all `logik`
  (`vorbedingung`, `nachbedingung`, `invariante`, `abstieg`), the handler
  premise carries itself by induction on the DEPTH: for a program all of
  whose bodies pass the check, `rufAt` never ends in `hardware`, at any
  depth, from any world, with any arguments (`rufAt_ohneHardware`).

  WHY IT MATTERS. The closing theorem (`Schlusssatz.lean`, plan §6.5) carries
  the condition "the Gabbro call ends in no model error" on part 4. Neither
  the checker's Bool nor the user's duty says anything about the `hardware`
  half: `HardwareAnnahmen` (Zielsatz/Spec.lean (c)) is CONDITIONAL -- it
  constrains the oracle only *where* the raw answer fits the declared type --
  and `KoerperGutS` speaks about `logik` outcomes only. So the `hardware`
  half of the condition is not discharged by the goal theorem's premises,
  and it is discharged HERE, syntactically, for every program whose bodies
  carry no oracle form -- which every program with a correspondence
  certificate does (`korrOk_hardwareFrei`, KorrespondenzAllg.lean).
-/
import Grammatik.Semantik

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. A handler that answers no hardware outcome -/

/-- A handler that answers no `hardware` outcome: a callee whose own body
    carries no oracle form and whose callees answer none either. The twin of
    `OhneLogik` (`ZielOrtGanz.lean`). -/
def OhneHardware (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)) (e : Hardware D),
    R g σ ρ ≠ RufAusgang.hardware e

/-! ## 2. The syntactic check: no oracle form -/

section Check

variable {V : Vertrag D}

mutual

/-- The statement carries no source of a `hardware` outcome: no axiom call
    and no `forever` (whose budget is `Hardware.fortschritt`). -/
def Stmt.hardwareFrei {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => t.hardwareFrei && e.hardwareFrei
  | .onOption _ p a => p.hardwareFrei && a.hardwareFrei
  | .onTag _ arms => arms.hardwareFrei
  | .onGrund _ arms => arms.hardwareFrei
  | .locks _ _ body => body.hardwareFrei
  | .breaking _ body => body.hardwareFrei
  | .traverse _ _ body => body.hardwareFrei
  | .retry _ _ body ueber => body.hardwareFrei && ueber.hardwareFrei
  | .forever .. => false
  | .axiomCall .. => false
  | _ => true

/-- The block carries no source of a `hardware` outcome: no axiom bind, no
    register read, no `awaits`. -/
def Block.hardwareFrei {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => s.hardwareFrei && rest.hardwareFrei
  | .bind _ rest => rest.hardwareFrei
  | .bindCall _ _ _ _ _ rest => rest.hardwareFrei
  | .bindCallInd _ _ _ _ _ rest => rest.hardwareFrei
  | .bindCallElse _ _ _ _ _ err rest => err.hardwareFrei && rest.hardwareFrei
  | .bindAxiom .. => false
  | .regLies .. => false
  | .regLiesElse .. => false
  | .awaits .. => false
  | .exchange _ _ _ _ rest => rest.hardwareFrei
  | .narrow _ _ _ sonst rest => sonst.hardwareFrei && rest.hardwareFrei
  | .pruefung _ sonst rest => sonst.hardwareFrei && rest.hardwareFrei
  | .gleit _ _ _ _ _ rest => rest.hardwareFrei
  | .gleitLit _ _ _ rest => rest.hardwareFrei
  | .gleitVon _ _ _ rest => rest.hardwareFrei
  | .gleitNarrow _ _ _ sonst rest => sonst.hardwareFrei && rest.hardwareFrei

def Endblock.hardwareFrei {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retGrund .. => true
  | .leave .. => true
  | .next .. => true
  | .cons s rest => s.hardwareFrei && rest.hardwareFrei
  | .bind _ rest => rest.hardwareFrei

def Arms.hardwareFrei {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => b.hardwareFrei && rest.hardwareFrei

def GrundArms.hardwareFrei {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => b.hardwareFrei && rest.hardwareFrei

end

end Check

/-! ## 3. Soundness of the check -/

section HardwareFrei

variable {V : Vertrag D}

theorem Ausgang.schrumpf_hardware {l : Bool} {Γ : Ctx} {τ : Ty} {o : Ausgang V l (τ :: Γ)}
    {e : Hardware D} (h : o.schrumpf = .hardware e) : o = .hardware e := by
  cases o <;> simp_all [Ausgang.schrumpf]

theorem Ausgang.schrumpfArm_hardware {l : Bool} {Γ : Ctx} {c : Option (Int × Int)}
    {o : Ausgang V l (ArmCtx Γ c)} {e : Hardware D}
    (h : Ausgang.schrumpfArm c o = .hardware e) : o = .hardware e := by
  cases c with
  | none => exact h
  | some p => exact Ausgang.schrumpf_hardware (by simpa [Ausgang.schrumpfArm] using h)

theorem EndAusgang.schrumpf_hardware {l : Bool} {Γ : Ctx} {τ : Ty}
    {o : EndAusgang V l (τ :: Γ)} {e : Hardware D} (h : o.schrumpf = .hardware e) :
    o = .hardware e := by
  cases o <;> simp_all [EndAusgang.schrumpf]

theorem EndAusgang.zuAusgang_hardware {l : Bool} {Γ : Ctx} {o : EndAusgang V l Γ}
    {e : Hardware D} (h : o.zuAusgang = .hardware e) : o = .hardware e := by
  cases o <;> simp_all [EndAusgang.zuAusgang]

theorem Ausgang.mapWelt_hardware {l : Bool} {Γ : Ctx} {o : Ausgang V l Γ}
    {f : World D → World D} {e : Hardware D} (h : o.mapWelt f = .hardware e) :
    o = .hardware e := by
  cases o <;> simp_all [Ausgang.mapWelt]

theorem traverseLauf_ohneHardware {l : Bool} {Γ : Ctx} {τ : Ty}
    (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ e, schritt σ ρ ≠ .hardware e) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ) (e : Hardware D),
      traverseLauf (l := l) schritt inv ks σ ρ ≠ .hardware e
  | [], σ, ρ, e => by
      intro h
      simp only [traverseLauf] at h
      split at h <;> cases h
  | k :: ks, σ, ρ, e => by
      intro h
      simp only [traverseLauf] at h
      split at h
      · cases h
      · split at h
        · exact traverseLauf_ohneHardware schritt inv hs ks _ _ e h
        · exact traverseLauf_ohneHardware schritt inv hs ks _ _ e h
        · split at h <;> cases h
        · cases h
        · cases h
        · cases h
        · rename_i heq
          cases h
          exact hs _ _ _ heq

theorem retryLauf_ohneHardware {l : Bool} {Γ : Ctx}
    (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueber : World D → Env D Γ → Ausgang V l Γ)
    (hs : ∀ σ ρ e, schritt σ ρ ≠ .hardware e) (hu : ∀ σ ρ e, ueber σ ρ ≠ .hardware e) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ) (e : Hardware D),
      retryLauf schritt bis ueber n σ ρ ≠ .hardware e
  | 0, σ, ρ, e => by
      intro h
      simp only [retryLauf] at h
      split at h
      · cases h
      · exact hu _ ρ e h
  | n + 1, σ, ρ, e => by
      intro h
      simp only [retryLauf] at h
      split at h
      · cases h
      · split at h
        · exact retryLauf_ohneHardware schritt bis ueber hs hu n _ _ e h
        · exact retryLauf_ohneHardware schritt bis ueber hs hu n _ _ e h
        · cases h
        · cases h
        · cases h
        · cases h
        · rename_i heq
          cases h
          exact hs _ _ _ heq

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
  | .onGrund r arms, h, σ, ρ, e', he => by
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
  | .forever .., h, _, _, _, _ => by simp [Stmt.hardwareFrei] at h
  | .axiomCall .., h, _, _, _, _ => by simp [Stmt.hardwareFrei] at h
  | .uebergang .., _, _, _, _, he => by
      simp only [execStmt] at he
      split at he <;> cases he
  | .assignSlot .., _, _, _, _, he => by simp [execStmt] at he
  | .assignDurch .., _, _, _, _, he => by simp [execStmt] at he
  | .assignGlob .., _, _, _, _, he => by simp [execStmt] at he
  | .schreibBytes .., _, _, _, _, he => by simp [execStmt] at he
  | .assignVar .., _, _, _, _, he => by simp [execStmt] at he
  | .regSchreib .., _, _, _, _, he => by simp [execStmt] at he
  | .transition .., _, _, _, _, he => by simp [execStmt] at he
  | .publish .., _, _, _, _, he => by simp [execStmt] at he
  | .advances .., _, _, _, _, he => by simp [execStmt] at he
  | .retires .., _, _, _, _, he => by simp [execStmt] at he
  | .ret .., _, _, _, _, he => by simp [execStmt] at he
  | .retGrund .., _, _, _, _, he => by simp [execStmt] at he
  | .leave .., _, _, _, _, he => by simp [execStmt] at he
  | .next .., _, _, _, _, he => by simp [execStmt] at he

theorem Block.hardwareFrei_ok (hR : OhneHardware R) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → b.hardwareFrei = true →
      ∀ (σ : World D) (ρ : Env D Γ) (e : Hardware D), execBlock O passes R b σ ρ ≠ .hardware e
  | .nil, _, σ, ρ, e, he => by simp [execBlock] at he
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
  | .bindAxiom .., h, _, _, _, _ => by simp [Block.hardwareFrei] at h
  | .regLies .., h, _, _, _, _ => by simp [Block.hardwareFrei] at h
  | .regLiesElse .., h, _, _, _, _ => by simp [Block.hardwareFrei] at h
  | .awaits .., h, _, _, _, _ => by simp [Block.hardwareFrei] at h
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
  | .pruefung c sonst rest, h, σ, ρ, e, he => by
      simp only [Block.hardwareFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.hardwareFrei_ok hR rest h.2 _ _ _ he
      · exact Endblock.hardwareFrei_ok hR sonst h.1 _ _ _ (EndAusgang.zuAusgang_hardware he)
  | .gleit op a b lo hi rest, h, σ, ρ, e, he => by
      simp only [Block.hardwareFrei] at h
      simp only [execBlock] at he
      split at he
      · exact Block.hardwareFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_hardware he)
      · cases he
  | .gleitLit q lo hi rest, h, σ, ρ, e, he => by
      simp only [Block.hardwareFrei] at h
      simp only [execBlock] at he
      split at he
      · exact Block.hardwareFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_hardware he)
      · cases he
  | .gleitVon x lo hi rest, h, σ, ρ, e, he => by
      simp only [Block.hardwareFrei] at h
      simp only [execBlock] at he
      split at he
      · exact Block.hardwareFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_hardware he)
      · cases he
  | .gleitNarrow x lo hi sonst rest, h, σ, ρ, e, he => by
      simp only [Block.hardwareFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.hardwareFrei_ok hR rest h.2 _ _ _ (Ausgang.schrumpf_hardware he)
      · exact Endblock.hardwareFrei_ok hR sonst h.1 _ _ _ (EndAusgang.zuAusgang_hardware he)

theorem Endblock.hardwareFrei_ok (hR : OhneHardware R) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (b : Endblock D V l Γ Λ) → b.hardwareFrei = true →
      ∀ (σ : World D) (ρ : Env D Γ) (e : Hardware D), execEnd O passes R b σ ρ ≠ .hardware e
  | .ret .., _, _, _, _, he => by simp [execEnd] at he
  | .retGrund .., _, _, _, _, he => by simp [execEnd] at he
  | .leave .., _, _, _, _, he => by simp [execEnd] at he
  | .next .., _, _, _, _, he => by simp [execEnd] at he
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
  | zero => intro g σ ρ e h; simp [rufAt] at h
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
  rw [if_neg (by rw [hreq]; simp), hb]

/-- The program-level form, over a member list of the functions. -/
theorem rufAt_ohneHardware_fs (P : Programm D) (O : Orakel D) (passes : Nat)
    {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) (h : programmHardwareFrei P fs = true) :
    ∀ n : Nat, OhneHardware (rufAt P O passes n) :=
  rufAt_ohneHardware P O passes (fun f => (List.all_eq_true.mp h) f (hvoll f))

#print axioms Gabbro.Grammatik.Endblock.hardwareFrei_ok
#print axioms Gabbro.Grammatik.rufAt_hardware_von_rumpf
#print axioms Gabbro.Grammatik.rufAt_ohneHardware

end Gabbro.Grammatik
