import Grammatik.Berechenbarkeit.BrainfuckG.Schritt
import Grammatik.Berechenbarkeit.RunsUntil

/-! Brainfuck on G, part 5: the whole program. `programm` is one G statement, uniform in the Brainfuck program:
`runs until pc = n { if pc = 0 { block of instruction 0 } else if pc = 1 { ... } ... }`, the loop of
`Terminierung.runsUntil` over the instruction blocks of `Schritt`. One pass of the loop is one Brainfuck step
(`durchgang`). Two theorems connect the runs:

* `programm_vollstaendig`: a Brainfuck run that halts after `k` steps is completed by every budget above `k` --
  the G statement ends normally in the representation of the final state, or (the arena is finite) it ends in the
  declared failure block. It never ends normally in any other state.
* `programm_korrekt`: a normal completion of the G statement is a halting Brainfuck run, and the final world
  represents its final state, so the output stack holds the program's output.

The failure block `voll` must abort (return, a reason, a stop); it may not `leave` or `next` the loop. -/

namespace Gabbro.Grammatik.Berechenbarkeit.BrainfuckG

open Brainfuck ArenaKette Storage.GStack Terminierung

variable {D : Deklaration} {A : FreiForm D} {V : Vertrag D} {Γ0 : Ctx} {Λ : List (Res D)} {n : Nat}

/-- The counter equals `j`. -/
def pcIst (j : Nat) : Expr D (BCtx n Γ0) Λ .bool := .eq (.var pcV) (.lit j)

theorem pcIst_eval (σ₀ σ : World D) (b : Brainfuck.Byte) (q : Fin (n + 1)) (ρ0 : Env D Γ0) (j : Nat) :
    eval σ₀ (pcIst (Λ := Λ) j) σ (.cons (kodiere b) (.cons (pcWert q) ρ0)) = decide ((q.val : Int) = j) := rfl

/-- The successor counter of position `j`. -/
def nextOf (j : Nat) : Fin (n + 1) := ⟨min (j + 1) n, by omega⟩

/-- The instruction at position `j` (positions past the end are never selected). -/
def befehlAn (p : Program n) (j : Nat) : Instruction n :=
  if h : j < n then p.code.get ⟨j, h⟩ else .increment

/-- The abort a failure block ends a loop with. -/
def abbruch {Γ : Ctx} : Ausgang V true Γ → Ausgang V false Γ
  | .ok σ ρ => .ok σ ρ
  | .next _ σ ρ => .ok σ ρ
  | .leave _ σ ρ => .ok σ ρ
  | .zurueck σ v => .zurueck σ v
  | .why σ r => .why σ r
  | .logik e => .logik e
  | .hardware e => .hardware e

section Code

variable (L : LinkFeld A) (G : Fin 4 → LinkKopf A) (hp : D.typ A.tab A.feld = ByteTy) (r : Rechte A G V Λ)
variable (voll : Endblock D V true (BCtx n Γ0) Λ) (p : Program n)

/-- `if pc = j { block j } else if pc = j + 1 { ... }`, over `k` positions. -/
def wahl : Nat → Nat → Gabbro.Grammatik.Block D V true (BCtx n Γ0) Λ Λ
  | _, 0 => .nil
  | j, k + 1 => .cons (.ite (pcIst j) (befehl L G hp r voll (befehlAn p j) (nextOf j)) (wahl (j + 1) k)) .nil

/-- **The G statement of a Brainfuck program.** -/
def programm (a : D.Annahme) : Stmt D V false (BCtx n Γ0) Λ Λ :=
  runsUntil a .tru (pcIst n) (wahl L G hp r voll p 0 n)

end Code

section Execution

variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

theorem darstellt_lese {L : LinkFeld A} {G : Fin 4 → LinkKopf A} {hp} {ρ0 : Env D Γ0} {s : State n} {σ : World D}
    {ρ : Env D (BCtx n Γ0)} (h : Darstellt L G hp ρ0 s σ ρ) (o : List (D.Tab ⊕ D.Glob)) :
    Darstellt L G hp ρ0 s (σ.lese Λ o) ρ :=
  ⟨h.1, MultiRep.lese h.2.1 _ _, A.freiOk_gleich (σ := σ) rfl (fun _ => rfl) rfl h.2.2⟩

/-- The selection reaches the block of the instruction at the counter, in a world that still represents. -/
theorem wahl_treffer (L : LinkFeld A) (G : Fin 4 → LinkKopf A) (hp : D.typ A.tab A.feld = ByteTy)
    (r : Rechte A G V Λ) (voll : Endblock D V true (BCtx n Γ0) Λ) (p : Program n) (ρ0 : Env D Γ0) (s : State n) :
    ∀ (k j i : Nat), i < k → s.pc.val = j + i → ∀ σ ρ, Darstellt L G hp ρ0 s σ ρ →
      ∃ σ'', execBlock O passes R (wahl L G hp r voll p j k) σ ρ =
        execBlock O passes R (befehl L G hp r voll (befehlAn p (j + i)) (nextOf (j + i))) σ'' ρ ∧
        Darstellt L G hp ρ0 s σ'' ρ ∧ A.kopfSt σ'' = A.kopfSt σ ∧ A.stand σ'' = A.stand σ := by
  intro k
  induction k with
  | zero => intro j i hi; omega
  | succ k ih =>
      intro j i hi hpc σ ρ hd
      have hρ := hd.1
      subst hρ
      simp only [wahl]
      rw [execBlock_single]
      simp only [execStmt]
      rw [pcIst_eval]
      cases i with
      | zero =>
          refine ⟨σ.lese Λ (pcIst (Γ0 := Γ0) (n := n) (Λ := Λ) j).orte, ?_, darstellt_lese hd _, rfl, rfl⟩
          rw [if_pos (by simp only [wahr?, decide_eq_true_eq]; omega)]
          rfl
      | succ i =>
          rw [if_neg (by simp only [wahr?, decide_eq_true_eq]; omega)]
          obtain ⟨σ'', he, hd'', hk'', hs''⟩ := ih (j + 1) i (by omega) (by omega) _ _ (darstellt_lese hd _)
          refine ⟨σ'', ?_, hd'', hk'', hs''⟩
          rw [he]
          simp only [show j + 1 + i = j + (i + 1) by omega]


theorem befehlAn_eq (p : Program n) (j : Nat) (h : j < n) : befehlAn p j = p.code.get ⟨j, h⟩ := by
  simp only [befehlAn, dif_pos h]

theorem nextOf_eq (q : Fin (n + 1)) (h : q.val < n) : nextOf q.val = successor q h := by
  apply Fin.ext
  simp only [nextOf, successor]
  omega

theorem step_eq (p : Program n) (s : State n) (h : s.pc.val < n) :
    step p s = some (execute (p.code.get ⟨s.pc.val, h⟩) (successor s.pc h) s) := by
  simp only [step, dif_pos h]

/-- The pass of the loop body, as the loop runs it. -/
abbrev passF (L : LinkFeld A) (G : Fin 4 → LinkKopf A) (hp : D.typ A.tab A.feld = ByteTy)
    (r : Rechte A G V Λ) (voll : Endblock D V true (BCtx n Γ0) Λ) (p : Program n) :
    World D → Env D (BCtx n Γ0) → Ausgang V true (BCtx n Γ0) :=
  fun σ ρ => execBlock O passes R (untilBody (pcIst n) (wahl L G hp r voll p 0 n)) σ ρ

/-- The loop's check of its invariant `true`. -/
abbrev invF (Λ : List (Res D)) : World D → Env D (BCtx n Γ0) → World D × Bool :=
  fun σ ρ => let σi := σ.lese Λ (Expr.tru : Expr D (BCtx n Γ0) Λ .bool).orte
    (σi, wahr? (eval σi (Expr.tru : Expr D (BCtx n Γ0) Λ .bool) σi ρ))

/-- **One pass is one Brainfuck step**, or the failure block. -/
theorem durchgang (L : LinkFeld A) (G : Fin 4 → LinkKopf A) (hinj : Function.Injective fun k => (G k).g)
    (hp : D.typ A.tab A.feld = ByteTy) (r : Rechte A G V Λ) (voll : Endblock D V true (BCtx n Γ0) Λ)
    (p : Program n) (ρ0 : Env D Γ0) (s : State n) (σ : World D) (ρ : Env D (BCtx n Γ0))
    (hd : Darstellt L G hp ρ0 s σ ρ) (hpc : s.pc.val < n) :
    (∃ σ' ρ', passF O passes R L G hp r voll p σ ρ = .ok σ' ρ' ∧
      Darstellt L G hp ρ0 (execute (p.code.get ⟨s.pc.val, hpc⟩) (successor s.pc hpc) s) σ' ρ') ∨
    ∃ σf ρf, passF O passes R L G hp r voll p σ ρ = (execEnd O passes R voll σf ρf).zuAusgang := by
  have hρ := hd.1
  subst hρ
  simp only [passF]
  rw [untilBody_exec]
  dsimp only
  rw [pcIst_eval, if_neg (by simp only [wahr?, decide_eq_true_eq]; omega)]
  obtain ⟨σ'', he, hd'', hk'', hs''⟩ := wahl_treffer O passes R L G hp r voll p ρ0 s n 0 s.pc.val hpc (by omega) _ _
    (darstellt_lese hd _)
  rw [he, show 0 + s.pc.val = s.pc.val by omega, befehlAn_eq p _ hpc, nextOf_eq s.pc hpc]
  rcases befehl_genau O passes R L G hinj hp r voll ρ0 _ _ s σ'' _ hd'' with h | ⟨σf, h⟩
  · exact .inl h
  · exact .inr ⟨σf, _, h⟩


/-- **A pass with room is one Brainfuck step**, never the failure block. -/
theorem durchgang_platz (L : LinkFeld A) (G : Fin 4 → LinkKopf A) (hinj : Function.Injective fun k => (G k).g)
    (hp : D.typ A.tab A.feld = ByteTy) (r : Rechte A G V Λ) (voll : Endblock D V true (BCtx n Γ0) Λ)
    (p : Program n) (ρ0 : Env D Γ0) (s : State n) (σ : World D) (ρ : Env D (BCtx n Γ0))
    (hd : Darstellt L G hp ρ0 s σ ρ) (hpc : s.pc.val < n)
    (hroom : A.kopfSt σ < D.count A.tab ∨ A.stand σ < D.count A.tab) :
    ∃ σ' ρ', passF O passes R L G hp r voll p σ ρ = .ok σ' ρ' ∧
      Darstellt L G hp ρ0 (execute (p.code.get ⟨s.pc.val, hpc⟩) (successor s.pc hpc) s) σ' ρ' := by
  have hρ := hd.1
  subst hρ
  simp only [passF]
  rw [untilBody_exec]
  dsimp only
  rw [pcIst_eval, if_neg (by simp only [wahr?, decide_eq_true_eq]; omega)]
  obtain ⟨σ'', he, hd'', hk'', hs''⟩ := wahl_treffer O passes R L G hp r voll p ρ0 s n 0 s.pc.val hpc (by omega)
    _ _ (darstellt_lese hd _)
  rw [he, show 0 + s.pc.val = s.pc.val by omega, befehlAn_eq p _ hpc, nextOf_eq s.pc hpc]
  exact befehl_schritt O passes R L G hinj hp r voll ρ0 _ _ s σ'' _ hd''
    (fun _ => by rw [hk'', hs'']; exact hroom)
/-- At the end of the program the pass leaves the loop. -/
theorem durchgang_ende (L : LinkFeld A) (G : Fin 4 → LinkKopf A) (hp : D.typ A.tab A.feld = ByteTy)
    (r : Rechte A G V Λ) (voll : Endblock D V true (BCtx n Γ0) Λ) (p : Program n) (ρ0 : Env D Γ0)
    (s : State n) (σ : World D) (ρ : Env D (BCtx n Γ0)) (hd : Darstellt L G hp ρ0 s σ ρ) (hpc : s.pc.val = n) :
    ∃ σ', passF O passes R L G hp r voll p σ ρ = .leave rfl σ' ρ ∧ Darstellt L G hp ρ0 s σ' ρ := by
  have hρ := hd.1
  subst hρ
  refine ⟨σ.lese Λ (pcIst (Γ0 := Γ0) (n := n) (Λ := Λ) n).orte, ?_, darstellt_lese hd _⟩
  simp only [passF]
  rw [untilBody_exec]
  dsimp only
  rw [pcIst_eval, if_pos (by simp only [wahr?, decide_eq_true_eq]; omega)]

/-- The failure block aborts: it neither leaves nor continues the loop. -/
def Bricht (voll : Endblock D V true (BCtx n Γ0) Λ) : Prop :=
  ∀ σ ρ σ' ρ', (execEnd O passes R voll σ ρ).zuAusgang ≠ .leave rfl σ' ρ' ∧
    (execEnd O passes R voll σ ρ).zuAusgang ≠ .next rfl σ' ρ'

/-- A loop whose pass aborts ends with that abort. -/
theorem lauf_abbruch (a : D.Annahme) (voll : Endblock D V true (BCtx n Γ0) Λ) (hvoll : Bricht O passes R voll)
    (step : World D → Env D (BCtx n Γ0) → Ausgang V true (BCtx n Γ0)) (q : Nat) (σ : World D)
    (ρ : Env D (BCtx n Γ0)) (σf : World D) (ρf : Env D (BCtx n Γ0))
    (hs : step (invF Λ σ ρ).1 ρ = (execEnd O passes R voll σf ρf).zuAusgang) :
    foreverLauf (l := false) a step (invF Λ) (q + 1) σ ρ = abbruch ((execEnd O passes R voll σf ρf).zuAusgang) := by
  rw [foreverLauf]
  simp only [eval, wahr?, Bool.true_eq_false, ↓reduceIte]
  simp only [eval, wahr?] at hs
  rw [hs]
  have h := hvoll σf ρf
  cases he : execEnd O passes R voll σf ρf with
  | leave h' σ' ρ' => exact absurd (by rw [he]; rfl) (h σ' ρ').1
  | next h' σ' ρ' => exact absurd (by rw [he]; rfl) (h σ' ρ').2
  | _ => rfl

/-- **Completeness**: a Brainfuck run that halts after `k` steps is completed by every budget above `k`, in the
representation of its final state -- or it aborts in the failure block. -/
theorem lauf_vollstaendig (L : LinkFeld A) (G : Fin 4 → LinkKopf A) (hinj : Function.Injective fun k => (G k).g)
    (hp : D.typ A.tab A.feld = ByteTy) (r : Rechte A G V Λ) (voll : Endblock D V true (BCtx n Γ0) Λ)
    (hvoll : Bricht O passes R voll) (p : Program n) (ρ0 : Env D Γ0) (a : D.Annahme) :
    ∀ {k s t}, Steps p k s t → step p t = none → ∀ q, k < q → ∀ σ ρ, Darstellt L G hp ρ0 s σ ρ →
      (∃ σ' ρ', foreverLauf (l := false) a (passF O passes R L G hp r voll p) (invF Λ) q σ ρ = .ok σ' ρ' ∧
        Darstellt L G hp ρ0 t σ' ρ') ∨
      ∃ σf ρf, foreverLauf (l := false) a (passF O passes R L G hp r voll p) (invF Λ) q σ ρ =
        abbruch ((execEnd O passes R voll σf ρf).zuAusgang) := by
  intro k s t hst hhalt
  induction hst with
  | zero s =>
      intro q hq σ ρ hd
      obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have hpc : s.pc.val = n := (halt_iff p s).mp hhalt
      have hdi := darstellt_lese (Λ := Λ) hd (Expr.tru : Expr D (BCtx n Γ0) Λ .bool).orte
      obtain ⟨σ', hpass, hd'⟩ := durchgang_ende O passes R L G hp r voll p ρ0 s _ ρ hdi hpc
      refine .inl ⟨σ', ρ, ?_, hd'⟩
      rw [foreverLauf]
      simp only [eval, wahr?, Bool.true_eq_false, ↓reduceIte]
      rw [hpass]
  | @more k s t1 u hs _ ih =>
      intro q hq σ ρ hd
      obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have hpc : s.pc.val < n := by
        by_contra h
        have : step p s = none := (halt_iff p s).mpr (by have := s.pc.isLt; omega)
        rw [this] at hs; cases hs
      rw [step_eq p s hpc] at hs
      cases hs
      have hdi := darstellt_lese (Λ := Λ) hd (Expr.tru : Expr D (BCtx n Γ0) Λ .bool).orte
      rcases durchgang O passes R L G hinj hp r voll p ρ0 s _ ρ hdi hpc with ⟨σ1, ρ1, hpass, hd1⟩ | ⟨σf, ρf, hpass⟩
      · have hrun : foreverLauf (l := false) a (passF O passes R L G hp r voll p) (invF Λ) (q + 1) σ ρ =
            foreverLauf (l := false) a (passF O passes R L G hp r voll p) (invF Λ) q σ1 ρ1 := by
          rw [foreverLauf]
          simp only [eval, wahr?, Bool.true_eq_false, ↓reduceIte]
          rw [hpass]
        rw [hrun]
        exact ih hhalt q (by omega) σ1 ρ1 hd1
      · exact .inr ⟨σf, ρf, lauf_abbruch O passes R a voll hvoll _ q σ ρ σf ρf hpass⟩

/-- **Correctness**: a normal end of the loop is a halting Brainfuck run, in the representation of its final
state. -/
theorem lauf_korrekt (L : LinkFeld A) (G : Fin 4 → LinkKopf A) (hinj : Function.Injective fun k => (G k).g)
    (hp : D.typ A.tab A.feld = ByteTy) (r : Rechte A G V Λ) (voll : Endblock D V true (BCtx n Γ0) Λ)
    (hvoll : Bricht O passes R voll) (p : Program n) (ρ0 : Env D Γ0) :
    ∀ {m σ ρ σ' ρ'}, ExitTrace (passF O passes R L G hp r voll p) (invF Λ) m σ ρ σ' ρ' →
      ∀ s, Darstellt L G hp ρ0 s σ ρ →
        ∃ t, Steps p m s t ∧ step p t = none ∧ Darstellt L G hp ρ0 t σ' ρ' := by
  intro m σ ρ σ' ρ' htr
  induction htr with
  | @leave σ ρ σ' ρ' _ hs =>
      intro s hd
      have hdi := darstellt_lese (Λ := Λ) hd (Expr.tru : Expr D (BCtx n Γ0) Λ .bool).orte
      by_cases hpc : s.pc.val < n
      · exfalso
        rcases durchgang O passes R L G hinj hp r voll p ρ0 s _ ρ hdi hpc with ⟨σ1, ρ1, hpass, _⟩ | ⟨σf, ρf, hpass⟩
        · simp only at hs; rw [hs] at hpass; cases hpass
        · simp only at hs; rw [hs] at hpass; exact (hvoll σf ρf σ' ρ').1 hpass.symm
      · have hn : s.pc.val = n := by have := s.pc.isLt; omega
        obtain ⟨σ2, hpass, hd2⟩ := durchgang_ende O passes R L G hp r voll p ρ0 s _ ρ hdi hn
        simp only at hs
        rw [hs] at hpass
        cases hpass
        exact ⟨s, .zero s, (halt_iff p s).mpr hn, hd2⟩
  | @more m σ ρ σ1 ρ1 σ' ρ' _ hs _ ih =>
      intro s hd
      have hdi := darstellt_lese (Λ := Λ) hd (Expr.tru : Expr D (BCtx n Γ0) Λ .bool).orte
      by_cases hpc : s.pc.val < n
      · rcases durchgang O passes R L G hinj hp r voll p ρ0 s _ ρ hdi hpc with ⟨σ2, ρ2, hpass, hd2⟩ | ⟨σf, ρf, hpass⟩
        · simp only at hs
          rcases hs with hs | hs <;> rw [hs] at hpass <;> cases hpass
          obtain ⟨t, hst, hh, hdt⟩ := ih _ hd2
          exact ⟨t, .more (step_eq p s hpc) hst, hh, hdt⟩
        · exfalso
          simp only at hs
          have h := hvoll σf ρf σ1 ρ1
          rcases hs with hs | hs <;> rw [hs] at hpass
          · cases he : execEnd O passes R voll σf ρf <;> rw [he] at hpass <;> cases hpass
          · exact h.2 hpass.symm
      · exfalso
        have hn : s.pc.val = n := by have := s.pc.isLt; omega
        obtain ⟨σ2, hpass, _⟩ := durchgang_ende O passes R L G hp r voll p ρ0 s _ ρ hdi hn
        simp only at hs
        rcases hs with hs | hs <;> rw [hs] at hpass <;> cases hpass

/-- **The G statement completes every halting Brainfuck run** within a budget above its step count: normally, in
the representation of the final state, or by aborting in the failure block when the arena is full. -/
theorem programm_vollstaendig (L : LinkFeld A) (G : Fin 4 → LinkKopf A)
    (hinj : Function.Injective fun k => (G k).g) (hp : D.typ A.tab A.feld = ByteTy) (r : Rechte A G V Λ)
    (voll : Endblock D V true (BCtx n Γ0) Λ) (hvoll : Bricht O passes R voll) (p : Program n) (ρ0 : Env D Γ0)
    (a : D.Annahme) {k : Nat} {s t : State n} (hst : Steps p k s t) (hhalt : step p t = none) (hk : k < passes)
    (σ : World D) (ρ : Env D (BCtx n Γ0)) (hd : Darstellt L G hp ρ0 s σ ρ) :
    (∃ σ' ρ', execStmt O passes R (programm L G hp r voll p a) σ ρ = .ok σ' ρ' ∧ Darstellt L G hp ρ0 t σ' ρ') ∨
    ∃ σf ρf, execStmt O passes R (programm L G hp r voll p a) σ ρ =
      abbruch ((execEnd O passes R voll σf ρf).zuAusgang) :=
  lauf_vollstaendig O passes R L G hinj hp r voll hvoll p ρ0 a hst hhalt passes hk σ ρ hd

/-- **A normal completion of the G statement is a halting Brainfuck run** of fewer steps than the budget, and the
final world represents its final state. -/
theorem programm_korrekt (L : LinkFeld A) (G : Fin 4 → LinkKopf A)
    (hinj : Function.Injective fun k => (G k).g) (hp : D.typ A.tab A.feld = ByteTy) (r : Rechte A G V Λ)
    (voll : Endblock D V true (BCtx n Γ0) Λ) (hvoll : Bricht O passes R voll) (p : Program n) (ρ0 : Env D Γ0)
    (a : D.Annahme) (s : State n) (σ σ' : World D) (ρ ρ' : Env D (BCtx n Γ0)) (hd : Darstellt L G hp ρ0 s σ ρ)
    (h : execStmt O passes R (programm L G hp r voll p a) σ ρ = .ok σ' ρ') :
    ∃ k t, k < passes ∧ Steps p k s t ∧ step p t = none ∧ Darstellt L G hp ρ0 t σ' ρ' := by
  obtain ⟨k, hk, htr⟩ := (runsUntil_iff O passes R a .tru (pcIst n) _ σ ρ σ' ρ').mp h
  obtain ⟨t, hst, hh, hdt⟩ := lauf_korrekt O passes R L G hinj hp r voll hvoll p ρ0 htr s hd
  exact ⟨k, t, hk, hst, hh, hdt⟩

/-- **Output**: started in the representation of the initial state on `input`, a normal completion of the G
statement means the Brainfuck program halts on `input`, and the output stack holds its output (reversed). -/
theorem programm_haelt (L : LinkFeld A) (G : Fin 4 → LinkKopf A)
    (hinj : Function.Injective fun k => (G k).g) (hp : D.typ A.tab A.feld = ByteTy) (r : Rechte A G V Λ)
    (voll : Endblock D V true (BCtx n Γ0) Λ) (hvoll : Bricht O passes R voll) (p : Program n) (ρ0 : Env D Γ0)
    (a : D.Annahme) (input : List Brainfuck.Byte) (σ σ' : World D) (ρ ρ' : Env D (BCtx n Γ0))
    (hd : Darstellt L G hp ρ0 (initial input) σ ρ)
    (h : execStmt O passes R (programm L G hp r voll p a) σ ρ = .ok σ' ρ') :
    ∃ out, HaltsWith p input out ∧ ∃ vals, MultiRep L G σ' vals ∧ vals 3 = out.reverse.map (ablage hp) := by
  obtain ⟨k, t, _, hst, hh, hdt⟩ := programm_korrekt O passes R L G hinj hp r voll hvoll p ρ0 a _ σ σ' ρ ρ' hd h
  refine ⟨t.output, ⟨k, t, hst, hh, rfl⟩, stapel hp t, hdt.2.1, ?_⟩
  simp only [State.output, List.reverse_reverse]
  rfl
end Execution

end Gabbro.Grammatik.Berechenbarkeit.BrainfuckG
