module

public import Grammatik.Kern.Syntax.Extraktion.T6
public import Grammatik.Kern.Syntax.Extraktion.T7.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Extraktion
variable {D : Deklaration}

/-- A fired oracle leaf step carries its argument reads plus the oracle's
    recorded writes, under the recording oracle bound: the oracle (`O.wirkt`)
    answers with its declared write events (`axiomSpur` over its own domains,
    `GutO`), so every new event names the statement `Λ` (a read) or the
    oracle's `Λe` (a write, mark-free by `GutO`), and every carrier it touches
    sits in the declared writes (over the caller's domains, hence the
    completeness premises) plus the `args.orte` read hull. -/
theorem execEreignis_aus_axiomCall
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (hO : GutO O)
    (tabs : List D.Tab) (globs : List D.Glob)
    (hct : ∀ t, D.aschreibt a t = true → t ∈ tabs)
    (hcg : ∀ g, D.agschreibt a g = true → g ∈ globs)
    (σ : World D) (ρ : Env D Γ) (σ' : World D) (neu : List (Ereignis D))
    (hh : HeldGenau Λ σ.haelt)
    (hstep : (execStmt O passes keinRuf
      (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ) σ ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ σ.spur) :
    ∃ Λe : List (Res D),
      (∀ m st, Res.marke m st ∉ Λe) ∧
      (∀ e ∈ neu, e.lambda = Λ ∨ e.lambda = Λe ∨ e.lambda = []) ∧
      (∀ e ∈ neu, ∀ o, e.traeger = some o →
        o ∈ stmtTraeger tabs globs
          (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ) ++
          stmtOrte
            (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ)) := by
  have hhaelt : (σ.lese Λ args.orte).haelt = σ.haelt := lese_haelt _ _ _
  have hhL : HeldGenau Λ (σ.lese Λ args.orte).haelt := by
    rw [hhaelt]
    exact hh
  have hgt : ∀ t, D.aschreibt a t = true → ∀ L, Sum.inl L ∈ D.braucht t →
      L ∈ (σ.lese Λ args.orte).haelt :=
    fun t hwr L hL => (hhL L).mp (hd t hwr _ hL)
  have hgg : ∀ g, D.agschreibt a g = true → ∀ L, Sum.inl L ∈ D.gbraucht g →
      L ∈ (σ.lese Λ args.orte).haelt :=
    fun g hwr L hL => (hhL L).mp (hgd g hwr _ hL)
  obtain ⟨_, _, hcond⟩ := hO a ((σ.lese Λ args.orte).fragt (.inl a))
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
  obtain ⟨tabs₀, globs₀, Λe, _, _, _, _, hmf₀, _, hspurO⟩ := hcond hgt hgg
  simp only [execStmt] at hstep
  split at hstep
  · rename_i σ1 v ha
    simp only [Ausgang.welt, Option.some.injEq] at hstep
    subst hstep
    have hσ1 : σ1 = (O.wirkt a ((σ.lese Λ args.orte).fragt (.inl a))
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).1 := by
      have hfst := congrArg Prod.fst ha
      simp only [axiomAntwort] at hfst
      exact hfst.symm
    have hlese : ((σ.lese Λ args.orte).fragt (.inl a)).spur =
        (Ereignis.fremd (.inl a) :: args.orte.map fun o => match o with
          | .inl t => Ereignis.zugriff t false Λ σ.haelt
          | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := rfl
    rw [hσ1, hspurO, hlese, ← List.append_assoc] at hneu
    have hneueq : axiomSpur tabs₀ globs₀ a Λe ((σ.lese Λ args.orte).fragt (.inl a)).haelt ++
        (Ereignis.fremd (.inl a) :: args.orte.map fun o => match o with
          | .inl t => Ereignis.zugriff t false Λ σ.haelt
          | .inr g => Ereignis.gzugriff g false Λ σ.haelt) = neu :=
      List.append_cancel_right hneu
    subst hneueq
    refine ⟨Λe, hmf₀, ?_, ?_⟩
    · intro e he
      rw [List.mem_append] at he
      rcases he with hor | hrd
      · rcases axiomSpur_mem hor with ⟨t, _, _, rfl⟩ | ⟨g, _, _, rfl⟩
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inl rfl)
      · rcases List.mem_cons.mp hrd with rfl | hrd
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl (mem_leseEr hrd).1
    · intro e he o ho
      rw [List.mem_append] at he
      rcases he with hor | hrd
      · rcases axiomSpur_mem hor with ⟨t, _, hwr, rfl⟩ | ⟨g, _, hwr, rfl⟩
        · have ho' : o = .inl t := by simpa [Ereignis.traeger] using ho.symm
          rw [ho']
          simp only [stmtTraeger, stmtOrte]
          apply List.mem_append.mpr; apply Or.inl
          apply List.mem_append.mpr; apply Or.inl
          apply List.mem_map.mpr
          exact ⟨t, List.mem_filter.mpr ⟨hct t hwr, hwr⟩, rfl⟩
        · have ho' : o = .inr g := by simpa [Ereignis.traeger] using ho.symm
          rw [ho']
          simp only [stmtTraeger, stmtOrte]
          apply List.mem_append.mpr; apply Or.inl
          apply List.mem_append.mpr; apply Or.inr
          apply List.mem_map.mpr
          exact ⟨g, List.mem_filter.mpr ⟨hcg g hwr, hwr⟩, rfl⟩
      · rcases List.mem_cons.mp hrd with rfl | hrd
        · simp only [Ereignis.traeger, reduceCtorEq] at ho
        have hmem : o ∈ args.orte := (mem_leseEr hrd).2 o ho
        simp only [stmtTraeger, stmtOrte]
        exact List.mem_append.mpr (Or.inr hmem)
  · simp only [Ausgang.welt, reduceCtorEq] at hstep


end Gabbro.Grammatik.Extraktion
