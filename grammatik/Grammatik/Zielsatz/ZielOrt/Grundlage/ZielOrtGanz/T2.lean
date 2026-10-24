/- Part 2 of 3 of `ZielOrtGanz` (split by instrumente/teile/lean-teilen.py; the umbrella `ZielOrtGanz.lean` imports all parts). -/
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}

section LogikFrei

variable {V : Vertrag D}

theorem Ausgang.schrumpf_logik {l : Bool} {Γ : Ctx} {τ : Ty} {o : Ausgang V l (τ :: Γ)}
    {e : Logik D} (h : o.schrumpf = .logik e) : o = .logik e := by
  cases o <;> simp_all [Ausgang.schrumpf]

theorem EndAusgang.schrumpf_logik {l : Bool} {Γ : Ctx} {τ : Ty} {o : EndAusgang V l (τ :: Γ)}
    {e : Logik D} (h : o.schrumpf = .logik e) : o = .logik e := by
  cases o <;> simp_all [EndAusgang.schrumpf]

theorem EndAusgang.zuAusgang_logik {l : Bool} {Γ : Ctx} {o : EndAusgang V l Γ}
    {e : Logik D} (h : o.zuAusgang = .logik e) : o = .logik e := by
  cases o <;> simp_all [EndAusgang.zuAusgang]

theorem Ausgang.mapWelt_logik {l : Bool} {Γ : Ctx} {o : Ausgang V l Γ}
    {f : World D → World D} {e : Logik D} (h : o.mapWelt f = .logik e) : o = .logik e := by
  cases o <;> simp_all [Ausgang.mapWelt]

theorem retryLauf_ohneLogik {l : Bool} {Γ : Ctx} (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueber : World D → Env D Γ → Ausgang V l Γ)
    (hs : ∀ σ ρ e, schritt σ ρ ≠ .logik e) (hu : ∀ σ ρ e, ueber σ ρ ≠ .logik e) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ) (e : Logik D),
      retryLauf schritt bis ueber n σ ρ ≠ .logik e
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
        · exact retryLauf_ohneLogik schritt bis ueber hs hu n _ _ e h
        · exact retryLauf_ohneLogik schritt bis ueber hs hu n _ _ e h
        · cases h
        · cases h
        · cases h
        · rename_i heq
          cases h
          exact hs _ _ _ heq
        · cases h

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

mutual

theorem Stmt.logikFrei_ok (hR : OhneLogik R) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → s.logikFrei = true →
      ∀ (σ : World D) (ρ : Env D Γ) (e : Logik D), execStmt O passes R s σ ρ ≠ .logik e
  | .ite c t e, h, σ, ρ, e', he => by
      simp only [Stmt.logikFrei, Bool.and_eq_true] at h
      simp only [execStmt] at he
      split at he
      · exact Block.logikFrei_ok hR t h.1 _ _ _ he
      · exact Block.logikFrei_ok hR e h.2 _ _ _ he
  | .onOption o p a, h, σ, ρ, e', he => by
      simp only [Stmt.logikFrei, Bool.and_eq_true] at h
      simp only [execStmt] at he
      split at he
      · exact Block.logikFrei_ok hR p h.1 _ _ _ (Ausgang.schrumpf_logik he)
      · exact Block.logikFrei_ok hR a h.2 _ _ _ he
  | .locks L hr body, h, σ, ρ, e', he => by
      simp only [Stmt.logikFrei] at h
      simp only [execStmt] at he
      exact Block.logikFrei_ok hR body h _ _ _ (Ausgang.mapWelt_logik he)
  | .breaking i body, h, σ, ρ, e', he => by
      simp only [Stmt.logikFrei] at h
      simp only [execStmt] at he
      exact Block.logikFrei_ok hR body h _ _ _ he
  | .retry n bis body ueber, h, σ, ρ, e', he => by
      simp only [Stmt.logikFrei, Bool.and_eq_true] at h
      simp only [execStmt] at he
      exact retryLauf_ohneLogik _ _ _ (fun σ ρ e => Block.logikFrei_ok hR body h.1 σ ρ e)
        (fun σ ρ e => Block.logikFrei_ok hR ueber h.2 σ ρ e) n σ ρ e' he
  | .call g args hp hr, _, σ, ρ, e', he => by
      simp only [execStmt] at he
      split at he
      · cases he
      · rename_i r _
        exact (Fin.cast hr r).elim0
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
      · cases he
  | .callInd p args hp hr, _, σ, ρ, e', he => by
      simp only [execStmt] at he
      split at he
      rename_i f hf _
      split at he
      · cases he
      · rename_i r _
        exact keinGrundSig hf hr r
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
      · cases he
  | .axiomCall a args h' hw hg hd hgd, _, σ, ρ, e', he => by
      simp only [execStmt, axiomAntwort] at he
      split at he <;> cases he
  | .shift .., h, _, _, _, _ => by simp [Stmt.logikFrei] at h
  | .traverse .., h, _, _, _, _ => by simp [Stmt.logikFrei] at h
  | .forever .., h, _, _, _, _ => by simp [Stmt.logikFrei] at h
  | .onTag .., h, _, _, _, _ => by simp [Stmt.logikFrei] at h
  | .onWhy .., h, _, _, _, _ => by simp [Stmt.logikFrei] at h
  | .assignSlot .., _, _, _, _, he => by simp [execStmt] at he
  | .assignThru .., _, _, _, _, he | .assignSlotRef .., _, _, _, _, he => by simp [execStmt] at he
  | .assignGlob .., _, _, _, _, he => by simp [execStmt] at he
  | .putBytes .., _, _, _, _, he => by simp [execStmt] at he
  | .assignVar .., _, _, _, _, he => by simp [execStmt] at he
  | .regWrite .., _, _, _, _, he => by simp [execStmt] at he
  | .transition .., _, _, _, _, he => by simp [execStmt] at he
  | .publish .., _, _, _, _, he => by simp [execStmt] at he
  | .advances .., _, _, _, _, he => by simp [execStmt] at he
  | .retires .., _, _, _, _, he => by simp [execStmt] at he
  | .ret .., _, _, _, _, he => by simp [execStmt] at he
  | .retWhy .., _, _, _, _, he => by simp [execStmt] at he
  | .leave .., _, _, _, _, he => by simp [execStmt] at he
  | .next .., _, _, _, _, he => by simp [execStmt] at he

theorem Block.logikFrei_ok (hR : OhneLogik R) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → b.logikFrei = true →
      ∀ (σ : World D) (ρ : Env D Γ) (e : Logik D), execBlock O passes R b σ ρ ≠ .logik e
  | .nil, _, σ, ρ, e, he => by simp [execBlock] at he
  | .cons s rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h.2 _ _ _ he
      · exact Stmt.logikFrei_ok hR s h.1 σ ρ e he
  | .bind x rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock] at he
      exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
  | .bindCall g args he' hp hr rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
      · rename_i r _
        exact (Fin.cast hr r).elim0
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
      · cases he
  | .bindCallInd p args he' hp hr rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock] at he
      split at he
      rename_i f hf _
      split at he
      · exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
      · rename_i r _
        exact keinGrundSig hf hr r
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
      · cases he
  | .bindCallElse g args he' hp hr err rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h.2 _ _ _ (Ausgang.schrumpf_logik he)
      · exact Endblock.logikFrei_ok hR err h.1 _ _ _
          (EndAusgang.schrumpf_logik (EndAusgang.zuAusgang_logik he))
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
      · cases he
  | .bindAxiom a args he' hw hg hd hgd rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock, axiomAntwort] at he
      split at he
      · exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
      · cases he
  | .bindAxiomElse a args he' hr hw hg hd hgd err rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h.2 _ _ _ (Ausgang.schrumpf_logik he)
      · exact Endblock.logikFrei_ok hR err h.1 _ _ _
          (EndAusgang.schrumpf_logik (EndAusgang.zuAusgang_logik he))
      · cases he
  | .regRead r hk rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock] at he
      split at he
      · split at he
        · exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
        · cases he
      · cases he
  | .regReadElse r hk zusage sonst rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · split at he
        · exact Block.logikFrei_ok hR rest h.2 _ _ _ (Ausgang.schrumpf_logik he)
        · exact Endblock.logikFrei_ok hR sonst h.1 _ _ _ (EndAusgang.zuAusgang_logik he)
      · cases he
  | .awaits g payload hp hL hat rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
      · cases he
  | .exchange g neu hw hL rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock] at he
      exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
  | .narrow x lo' hi' sonst rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h.2 _ _ _ (Ausgang.schrumpf_logik he)
      · exact Endblock.logikFrei_ok hR sonst h.1 _ _ _ (EndAusgang.zuAusgang_logik he)
  | .check c sonst rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h.2 _ _ _ he
      · exact Endblock.logikFrei_ok hR sonst h.1 _ _ _ (EndAusgang.zuAusgang_logik he)
  | .float .., h, _, _, _, _ => by simp [Block.logikFrei] at h
  | .floatLit q lo hi rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h.2 _ _ _ (Ausgang.schrumpf_logik he)
      · rename_i hn
        rw [hn] at h
        simp at h
  | .floatOf .., h, _, _, _, _ => by simp [Block.logikFrei] at h
  | .floatNarrow x lo hi sonst rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h.2 _ _ _ (Ausgang.schrumpf_logik he)
      · exact Endblock.logikFrei_ok hR sonst h.1 _ _ _ (EndAusgang.zuAusgang_logik he)

theorem Endblock.logikFrei_ok (hR : OhneLogik R) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (b : Endblock D V l Γ Λ) → b.logikFrei = true →
      ∀ (σ : World D) (ρ : Env D Γ) (e : Logik D), execEnd O passes R b σ ρ ≠ .logik e
  | .ret .., _, _, _, _, he => by simp [execEnd] at he
  | .retWhy .., _, _, _, _, he => by simp [execEnd] at he
  | .leave .., _, _, _, _, he => by simp [execEnd] at he
  | .next .., _, _, _, _, he => by simp [execEnd] at he
  | .cons s rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei, Bool.and_eq_true] at h
      simp only [execEnd] at he
      split at he
      · exact Endblock.logikFrei_ok hR rest h.2 _ _ _ he
      · cases he
      · cases he
      · cases he
      · cases he
      · rename_i heq
        cases he
        exact Stmt.logikFrei_ok hR s h.1 σ ρ e heq
      · cases he
  | .bind x rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei] at h
      simp only [execEnd] at he
      exact Endblock.logikFrei_ok hR rest h _ _ _ (EndAusgang.schrumpf_logik he)
  | .bindCall g args he' hp hr rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei] at h
      simp only [execEnd] at he
      split at he
      · exact Endblock.logikFrei_ok hR rest h _ _ _ (EndAusgang.schrumpf_logik he)
      · rename_i r _
        exact (Fin.cast hr r).elim0
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
      · cases he
  | .bindCallElse g args he' hp hr err rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei, Bool.and_eq_true] at h
      simp only [execEnd] at he
      split at he
      · exact Endblock.logikFrei_ok hR rest h.2 _ _ _ (EndAusgang.schrumpf_logik he)
      · exact Endblock.logikFrei_ok hR err h.1 _ _ _
          (EndAusgang.schrumpf_logik he)
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
      · cases he
  | .bindAxiom a args he' hw hg hd hgd rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei] at h
      simp only [execEnd, axiomAntwort] at he
      split at he
      · exact Endblock.logikFrei_ok hR rest h _ _ _ (EndAusgang.schrumpf_logik he)
      · cases he
  | .bindAxiomElse a args he' hr hw hg hd hgd err rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei, Bool.and_eq_true] at h
      simp only [execEnd] at he
      split at he
      · exact Endblock.logikFrei_ok hR rest h.2 _ _ _ (EndAusgang.schrumpf_logik he)
      · exact Endblock.logikFrei_ok hR err h.1 _ _ _ (EndAusgang.schrumpf_logik he)
      · cases he
  | .regRead r hk rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei] at h
      simp only [execEnd] at he
      split at he
      · split at he
        · exact Endblock.logikFrei_ok hR rest h _ _ _ (EndAusgang.schrumpf_logik he)
        · cases he
      · cases he
  | .regReadElse r hk zusage sonst rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei, Bool.and_eq_true] at h
      simp only [execEnd] at he
      split at he
      · split at he
        · exact Endblock.logikFrei_ok hR rest h.2 _ _ _ (EndAusgang.schrumpf_logik he)
        · exact Endblock.logikFrei_ok hR sonst h.1 _ _ _ he
      · cases he
  | .awaits g payload hp hL hat rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei] at h
      simp only [execEnd] at he
      split at he
      · exact Endblock.logikFrei_ok hR rest h _ _ _ (EndAusgang.schrumpf_logik he)
      · cases he
  | .bindCallInd p args he' hp hr rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei] at h
      simp only [execEnd] at he
      split at he
      rename_i f hf _
      split at he
      · exact Endblock.logikFrei_ok hR rest h _ _ _ (EndAusgang.schrumpf_logik he)
      · rename_i r _
        exact keinGrundSig hf hr r
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
      · cases he

end

end LogikFrei
/-- **A body without `logik` sources meets `KeineLogik`** -- for every
    declared axiom ensures, without any reasoning about the program. -/
theorem logikFrei_keineLogik {P : Programm D} (passes : Nat) (Q : AxEns D) {f : D.Fn}
    (h : (P.rumpf f).logikFrei = true) : KeineLogik P passes Q f :=
  fun O' _ _ _ R _ hR σ ρ _ e => Endblock.logikFrei_ok O' passes R hR (P.rumpf f) h σ ρ e

/-- The program-level check over a member list. -/
def programmLogikFrei (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun f => (P.rumpf f).logikFrei

theorem programmLogikFrei_ok {P : Programm D} {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (h : programmLogikFrei P fs = true) (passes : Nat) (Q : AxEns D) :
    ∀ f, KeineLogik P passes Q f :=
  fun f => logikFrei_keineLogik passes Q ((List.all_eq_true.mp h) f (hvoll f))

#print axioms Gabbro.Grammatik.logikFrei_keineLogik
#print axioms Gabbro.Grammatik.programmLogikFrei_ok

/-! ## 6. The conclusion: no reachable machine is stuck at a `logik` check -/

/-- **The `logik` checks of G pass for thread `t` of `M`.** At each of the
    five places where a rule of G tests a `logik` condition of the running
    frame, the test passes at the thread's machine world:
    * a `traverse` boundary (`travNext`, `travDone`): the invariant holds;
    * a `forever` boundary with budget left (`ewigWeiter`): the invariant
      holds;
    * a `leave` out of a `traverse` body (`dannLeaveTrav`): the invariant
      holds at the exit;
    * a leaf at the head of an end block or of a block (`blatt`,
      `dannBlatt`; the only leaf with a `logik` outcome is a `state`
      transition): its outcome is no `logik` outcome, so the transition
      finds its pre-state.
    `nachbedingung`, `invariante`, `abstieg` and `vorbedingung` are no
    checks of G at all (G logs entries and returns and has no depth
    bound). -/
def PrueftG (O : Orakel D) (passes : Nat) (M : RufMaschineG D) (t : Faden) : Prop :=
    (∀ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ) (tb : D.Tab)
        (inv : Expr D Γ Λ .bool)
        (body : Block D (vertragVon D (M.faeden t).kopf.f) true (.index (D.count tb) :: Γ) Λ Λ)
        (ks : List (Wert D (.index (D.count tb))))
        (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ),
      (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .trav tb inv body ks k⟩ →
      wahr? (eval ((M.weltVon t).lese Λ inv.orte) inv ((M.weltVon t).lese Λ inv.orte) ρ) = true) ∧
    (∀ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ) (a : D.Annahme) (n : Nat)
        (inv : Expr D Γ Λ .bool) (body : Block D (vertragVon D (M.faeden t).kopf.f) true Γ Λ Λ)
        (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ),
      (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .ewig a (n + 1) inv body k⟩ →
      wahr? (eval ((M.weltVon t).lese Λ inv.orte) inv ((M.weltVon t).lese Λ inv.orte) ρ) = true) ∧
    (∀ (l : Bool) (Γ : Ctx) (Λ Λx : List (Res D)) (ρ : Env D Γ) (tb : D.Tab)
        (inv : Expr D Γ Λ .bool)
        (body : Block D (vertragVon D (M.faeden t).kopf.f) true (.index (D.count tb) :: Γ) Λ Λ)
        (is : List (Wert D (.index (D.count tb))))
        (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ)
        (rest : Block D (vertragVon D (M.faeden t).kopf.f) true (.index (D.count tb) :: Γ) Λx Λ)
        (hl : true = true) (i : Wert D (.index (D.count tb))),
      (M.faeden t).kopf.rest = ⟨true, .index (D.count tb) :: Γ, Λx, .cons i ρ,
        .dann (.cons (.leave hl) rest) (.travRest tb inv body is k)⟩ →
      wahr? (eval ((M.weltVon t).lese Λ inv.orte) inv ((M.weltVon t).lese Λ inv.orte) ρ) = true) ∧
    (∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (ρ : Env D Γ)
        (s : Stmt D (vertragVon D (M.faeden t).kopf.f) l Γ Λ Λ')
        (K : Endblock D (vertragVon D (M.faeden t).kopf.f) l Γ Λ'),
      s.istBlatt = true → (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.cons s K)⟩ →
      ∀ e : Logik D, execStmt O passes keinRuf s (M.weltVon t) ρ ≠ .logik e) ∧
    (∀ (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (ρ : Env D Γ)
        (s : Stmt D (vertragVon D (M.faeden t).kopf.f) l Γ Λ Λ')
        (rst : Block D (vertragVon D (M.faeden t).kopf.f) l Γ Λ' Λ'')
        (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ''),
      s.istBlatt = true → (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons s rst) k⟩ →
      ∀ e : Logik D, execStmt O passes keinRuf s (M.weltVon t) ρ ≠ .logik e)

/-- **No thread of `M` is stopped at a `logik` check of G.** -/
def KeinLogikHaltG (O : Orakel D) (passes : Nat) (M : RufMaschineG D) : Prop :=
  ∀ t : Faden, PrueftG O passes M t

/-- A Boolean that is not `false` is `true`. -/
theorem wahr_of_nicht_falsch {b : Bool} (h : b = false → False) : b = true := by
  cases b
  · exact absurd rfl h
  · rfl

section Halt

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D}

/-- **A replayed thread is stopped at no `logik` check**, when every body
    meets `KeineLogik`. -/
theorem fadenR_prueft (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hL : ∀ f, KeineLogik P passes Q f) {M : RufMaschineG D} (t : Faden)
    (hF : FadenR P O passes Q (M.faeden t) (M.weltVon t)) : PrueftG O passes M t := by
  have hK := hF.1
  refine ⟨fun l Γ Λ ρ tb inv body ks k hr => ?_, fun l Γ Λ ρ a n inv body k hr => ?_,
    fun l Γ Λ Λx ρ tb inv body is k rest hl i hr => ?_,
    fun l Γ Λ Λ' ρ s K hb hr e he => ?_, fun l Γ Λ Λ' Λ'' ρ s rst k hb hr e he => ?_⟩
  · obtain ⟨H, HA, σ, hg, hok, hno⟩ := kopfR_keineLogik' hO hRL hQ hL hK hr
    refine wahr_of_nicht_falsch fun hw => hno .schleife ?_
    apply semV_trav_falsch
    rw [eval_gleichAuf inv (fun _ h => hok.1 h) (hg.lese Λ Λ inv.orte inv.orte) ρ]
    exact hw
  · obtain ⟨H, HA, σ, hg, hok, hno⟩ := kopfR_keineLogik' hO hRL hQ hL hK hr
    refine wahr_of_nicht_falsch fun hw => hno .schleife ?_
    apply semV_ewig_falsch
    rw [eval_gleichAuf inv (fun _ h => hok.1 h) (hg.lese Λ Λ inv.orte inv.orte) ρ]
    exact hw
  · obtain ⟨H, HA, σ, hg, hok, hno⟩ := kopfR_keineLogik' hO hRL hQ hL hK hr
    refine wahr_of_nicht_falsch fun hw => hno .schleife ?_
    apply semV_leaveTrav_falsch
    rw [eval_gleichAuf inv (fun _ h => hok.2.2.1 h) (hg.lese Λ Λ inv.orte inv.orte) ρ]
    exact hw
  · obtain ⟨H, HA, σ, hg, hok, hno⟩ := kopfR_keineLogik' hO hRL hQ hL hK hr
    obtain ⟨_, hss, _⟩ := okG_ende_cons hok
    have h' := blatt_logik P s hb hss hg O (orakelAus O HA) passes keinRuf (rufAusL H) ρ e he
    refine hno e ?_
    show zErg (execEnd (orakelAus O HA) passes (rufAusL H) (.cons s K) σ ρ) = _
    simp only [execEnd, h', zErg]
  · obtain ⟨H, HA, σ, hg, hok, hno⟩ := kopfR_keineLogik' hO hRL hQ hL hK hr
    obtain ⟨_, hss, _⟩ := okG_dann_cons hok
    have h' := blatt_logik P s hb hss hg O (orakelAus O HA) passes keinRuf (rufAusL H) ρ e he
    refine hno e ?_
    rw [semV_dann_cons, h']
    exact weiterZ_logik _ _ _ _ e

end Halt
/-! ## 7. G moves at every `logik` check

  `KeinLogikHaltG` says the checks PASS. Here the step itself: at every
  place where a rule of G tests a `logik` condition, the rule fires -- given
  the one side condition every reading rule of G carries, `HeldGenau` of
  the head's static holdings (a lock-bookkeeping fact, not a `logik` check;
  `rufG_haelt_statisch` proves its `⊆` half on every reachable machine, the
  `⊇` half is not proved -- `THEOREM-MAP.md` §13.5). -/

/-- **Thread `t` of `M` stands at a `logik` check of G**: a `traverse`
    boundary, a `forever` boundary with budget left, a `leave` out of a
    `traverse` body, or a `state` transition at the head of an end block or
    of a block. -/
def AnPruefungG (M : RufMaschineG D) (t : Faden) : Prop :=
  (∃ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ) (tb : D.Tab)
      (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden t).kopf.f) true (.index (D.count tb) :: Γ) Λ Λ)
      (ks : List (Wert D (.index (D.count tb))))
      (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ),
    (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .trav tb inv body ks k⟩) ∨
  (∃ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ) (a : D.Annahme) (n : Nat)
      (inv : Expr D Γ Λ .bool) (body : Block D (vertragVon D (M.faeden t).kopf.f) true Γ Λ Λ)
      (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ),
    (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .ewig a (n + 1) inv body k⟩) ∨
  (∃ (l : Bool) (Γ : Ctx) (Λ Λx : List (Res D)) (ρ : Env D Γ) (tb : D.Tab)
      (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden t).kopf.f) true (.index (D.count tb) :: Γ) Λ Λ)
      (is : List (Wert D (.index (D.count tb))))
      (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ)
      (rest : Block D (vertragVon D (M.faeden t).kopf.f) true (.index (D.count tb) :: Γ) Λx Λ)
      (hl : true = true) (i : Wert D (.index (D.count tb))),
    (M.faeden t).kopf.rest = ⟨true, .index (D.count tb) :: Γ, Λx, .cons i ρ,
      .dann (.cons (.leave hl) rest) (.travRest tb inv body is k)⟩) ∨
  (∃ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ) (lo hi : Int) (tb : D.Tab)
      (fl : D.Feld tb) (hτ : D.typ tb fl = .int lo hi) (i : Expr D Γ Λ (.index (D.count tb)))
      (von nach : Int) (hn : lo ≤ nach ∧ nach ≤ hi) (he : D.erlaubt tb fl von nach = true)
      (hw : (vertragVon D (M.faeden t).kopf.f).schreibt tb = true) (hL : darf D tb Λ)
      (K : Endblock D (vertragVon D (M.faeden t).kopf.f) l Γ Λ),
    (M.faeden t).kopf.rest =
      ⟨l, Γ, Λ, ρ, .ende (.cons (.shift tb fl hτ i von nach hn he hw hL) K)⟩) ∨
  (∃ (l : Bool) (Γ : Ctx) (Λ Λ'' : List (Res D)) (ρ : Env D Γ) (lo hi : Int) (tb : D.Tab)
      (fl : D.Feld tb) (hτ : D.typ tb fl = .int lo hi) (i : Expr D Γ Λ (.index (D.count tb)))
      (von nach : Int) (hn : lo ≤ nach ∧ nach ≤ hi) (he : D.erlaubt tb fl von nach = true)
      (hw : (vertragVon D (M.faeden t).kopf.f).schreibt tb = true) (hL : darf D tb Λ)
      (rst : Block D (vertragVon D (M.faeden t).kopf.f) l Γ Λ Λ'')
      (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ''),
    (M.faeden t).kopf.rest =
      ⟨l, Γ, Λ, ρ, .dann (.cons (.shift tb fl hτ i von nach hn he hw hL) rst) k⟩)

/-- A `state` transition whose outcome is no `logik` outcome is an `ok`
    step that only adds accesses to the trace. -/
theorem uebergang_ok {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {lo hi : Int}
    (O : Orakel D) (passes : Nat) (tb : D.Tab) (fl : D.Feld tb) (hτ : D.typ tb fl = .int lo hi)
    (i : Expr D Γ Λ (.index (D.count tb))) (von nach : Int) (hn : lo ≤ nach ∧ nach ≤ hi)
    (he : D.erlaubt tb fl von nach = true) (hw : V.schreibt tb = true) (hL : darf D tb Λ)
    (W : World D) (ρ : Env D Γ)
    (hno : ∀ e : Logik D, execStmt O passes keinRuf
      (Stmt.shift (l := l) tb fl hτ i von nach hn he hw hL) W ρ ≠ .logik e) :
    ∃ σ' ρ', execStmt O passes keinRuf (Stmt.shift (l := l) tb fl hτ i von nach hn he hw hL)
      W ρ = .ok σ' ρ' ∧ Erw W σ' := by
  cases hx : execStmt O passes keinRuf (Stmt.shift (l := l) tb fl hτ i von nach hn he hw hL)
      W ρ with
  | ok σ' ρ' =>
      refine ⟨σ', ρ', rfl, ?_⟩
      simp only [execStmt] at hx
      split at hx
      · cases hx
        exact (Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)
      · cases hx
  | logik e => exact absurd hx (hno e)
  | _ =>
      simp only [execStmt] at hx
      split at hx <;> cases hx


end Gabbro.Grammatik
