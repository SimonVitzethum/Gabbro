import Grammatik.Berechenbarkeit.Storage.GStack.Grants
import Grammatik.Berechenbarkeit.RunsUntil

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.GStack

open Terminierung ArenaKette

variable {D : Deklaration} {A : FreiForm D} {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)}

/-- The actual logical guard reads the stack head and compares its sentinel. -/
def emptyGuard (G : LinkKopf A) (hLH : gdarf D G.g Λ) : Expr D Γ Λ .bool :=
  .eq (Expr.umTyp G.hg (.glob G.g hLH)) (.lit (D.count A.tab))

theorem emptyGuard_eval (G : LinkKopf A) (hLH : gdarf D G.g Λ) (σ : World D) (ρ : Env D Γ) :
    eval σ (emptyGuard G hLH) σ ρ = decide (G.st σ = D.count A.tab) := by
  simp only [emptyGuard, eval, eval_umTyp]
  rfl

theorem Represents.empty_head {L : LinkFeld A} {G : LinkKopf A} {σ : World D}
    (hr : Represents L G σ []) : G.st σ = D.count A.tab := by
  obtain ⟨indices, hc, _, _, hv⟩ := hr
  generalize hroot : G.st σ = root at hc ⊢
  cases hc with
  | nil => rfl
  | cons i hlo hhi tail ht => simp only [List.map_cons, reduceCtorEq] at hv

namespace Block

/-- One actual pop/release per continuing pass; the guard in `runsUntil`
prevents executing the empty-pop branch on a represented stack. -/
def drainStep (L : LinkFeld A) (G : LinkKopf A)
    (hwH : V.gschreibt G.g = true) (hLH : gdarf D G.g Λ)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwF : V.gschreibt A.kopf = true) (hLF : gdarf D A.kopf Λ)
    (empty : Endblock D V true Γ Λ) : Gabbro.Grammatik.Block D V true Γ Λ Λ :=
  popAndRelease L G hwH hLH hwT hLT hwF hLF empty .nil

end Block

/-- `runs until stack-is-empty`, entirely in existing G syntax. -/
def drain (L : LinkFeld A) (G : LinkKopf A)
    (hwH : V.gschreibt G.g = true) (hLH : gdarf D G.g Λ)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwF : V.gschreibt A.kopf = true) (hLF : gdarf D A.kopf Λ)
    (empty : Endblock D V true Γ Λ) (a : D.Annahme) : Stmt D V false Γ Λ Λ :=
  runsUntil a .tru (emptyGuard G hLH) (Block.drainStep L G hwH hLH hwT hLT hwF hLF empty)

section Execution

variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (L : LinkFeld A) (G : LinkKopf A)
variable (hwH : V.gschreibt G.g = true) (hLH : gdarf D G.g Λ)
variable (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
variable (hwF : V.gschreibt A.kopf = true) (hLF : gdarf D A.kopf Λ)
variable (empty : Endblock D V true Γ Λ)

/-- A trace of the real G loop has exactly as many continuing passes as the
initial value sequence has cells. All representation premises are preserved. -/
theorem drain_trace (values : List (Wert D (D.typ A.tab A.feld))) :
    ∀ (σ : World D) (ρ : Env D Γ), Represents L G σ values → A.FreiOk σ →
    ∃ σ', ExitTrace
      (fun σ ρ => execBlock O passes R
        (untilBody (emptyGuard G hLH) (Block.drainStep L G hwH hLH hwT hLT hwF hLF empty)) σ ρ)
      (fun σ ρ => let σi := σ.lese Λ (Expr.tru : Expr D Γ Λ .bool).orte
        (σi, wahr? (eval σi (.tru : Expr D Γ Λ .bool) σi ρ)))
      values.length σ ρ σ' ρ ∧ Represents L G σ' [] ∧ A.FreiOk σ' := by
  induction values with
  | nil =>
      intro σ ρ hr hf
      let σc := σ.lese Λ (emptyGuard (Γ := Γ) G hLH).orte
      have hguard : wahr? (eval σc (emptyGuard G hLH) σc ρ) = true := by
        rw [emptyGuard_eval]
        exact decide_eq_true (hr.reads _ _).empty_head
      refine ⟨σc, ExitTrace.leave rfl ?_, hr.reads _ _,
        A.freiOk_gleich (σ := σ) (σ' := σc) rfl (fun _ => rfl) rfl hf⟩
      change execBlock O passes R
        (untilBody (emptyGuard G hLH) (Block.drainStep L G hwH hLH hwT hLT hwF hLF empty)) σ ρ =
          .leave rfl σc ρ
      rw [untilBody_exec]
      change (if wahr? (eval σc (emptyGuard G hLH) σc ρ) then _ else _) = _
      rw [hguard]
      rfl
  | cons value values ih =>
      intro σ ρ hr hf
      let σc := σ.lese Λ (emptyGuard (Γ := Γ) G hLH).orte
      have hguard : wahr? (eval σc (emptyGuard G hLH) σc ρ) = false := by
        rw [emptyGuard_eval]
        apply decide_eq_false
        have hh := (hr.reads Λ (emptyGuard (Γ := Γ) G hLH).orte).nonempty
        change G.st σc < D.count A.tab at hh
        intro he
        omega
      obtain ⟨σ1, k, hpop, _, hr1, hf1, _, _⟩ :=
        popAndRelease_values O passes R L G hwH hLH hwT hLT hwF hLF empty .nil σc ρ value values
          (hr.reads _ _) (A.freiOk_gleich (σ := σ) (σ' := σc) rfl (fun _ => rfl) rfl hf)
      obtain ⟨σ', ht, hr', hf'⟩ := ih σ1 ρ hr1 hf1
      refine ⟨σ', ExitTrace.more rfl (Or.inl ?_) ht, hr', hf'⟩
      change execBlock O passes R
        (untilBody (emptyGuard G hLH) (Block.drainStep L G hwH hLH hwT hLT hwF hLF empty)) σ ρ =
          .ok σ1 ρ
      rw [untilBody_exec]
      change (if wahr? (eval σc (emptyGuard G hLH) σc ρ) then _ else _) = _
      simp only [hguard, Bool.false_eq_true, ite_false]
      exact hpop

/-- A sufficient explicit termination budget: n successful pop passes and
one final guard check. No eventual-condition or allocator-success axiom. -/
theorem drain_bound (a : D.Annahme) (σ : World D) (ρ : Env D Γ)
    (values : List (Wert D (D.typ A.tab A.feld))) (hr : Represents L G σ values) (hf : A.FreiOk σ)
    (hbudget : values.length < passes) :
    ∃ σ', execStmt O passes R (drain L G hwH hLH hwT hLT hwF hLF empty a) σ ρ = .ok σ' ρ ∧
      Represents L G σ' [] ∧ A.FreiOk σ' := by
  obtain ⟨σ', ht, hr', hf'⟩ := drain_trace O passes R L G hwH hLH hwT hLT hwF hLF empty values σ ρ hr hf
  exact ⟨σ', ht.run a hbudget, hr', hf'⟩

/-- The bound is exact for this controller: n pops require n+1 loop passes.
Exhaustion before the final guard check is never normal completion. -/
theorem drain_iff_budget (a : D.Annahme) (σ : World D) (ρ : Env D Γ)
    (values : List (Wert D (D.typ A.tab A.feld))) (hr : Represents L G σ values) (hf : A.FreiOk σ) :
    (∃ σ' ρ', execStmt O passes R (drain L G hwH hLH hwT hLT hwF hLF empty a) σ ρ = .ok σ' ρ') ↔
      values.length < passes := by
  constructor
  · rintro ⟨σ', ρ', he⟩
    obtain ⟨n, hn, ht⟩ := (runsUntil_iff O passes R a .tru (emptyGuard G hLH)
      (Block.drainStep L G hwH hLH hwT hLT hwF hLF empty) σ ρ σ' ρ').mp he
    obtain ⟨σfinal, hfull, _, _⟩ := drain_trace O passes R L G hwH hLH hwT hLT hwF hLF empty values σ ρ hr hf
    exact (hfull.length_unique ht) ▸ hn
  · intro hb
    obtain ⟨σ', he, _, _⟩ := drain_bound O passes R L G hwH hLH hwT hLT hwF hLF empty a σ ρ values hr hf hb
    exact ⟨σ', ρ, he⟩

end Execution

end Gabbro.Grammatik.Berechenbarkeit.Storage.GStack
