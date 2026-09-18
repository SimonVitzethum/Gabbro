/-
  File:      Grammatik/ArenaReset.lean
  Subject:   Arena-reset reuse safety: a reset wholesales every slot.

  Lane 243 (TODO wave D). PLAN-DYNAMISCH.md section 6 DECIDED arena-reset
  as the free discipline (linear free-list rejected, section 6): freeing is
  `reset A;` only -- counter to zero, generation consumed, commit kept.
  This file is the reuse-safety half of that decision, over the sugar of
  `ArenaZucker.lean` (no new syntax, no new constructor, no new checker
  rule): after a reset the counter stands at zero, strictly under the hard
  bound, so the NEXT `alloc` runs its body with index 0 -- never its `else`.
  No live reference survives a reset because there is nothing to survive:
  indices are scoped binders introduced by `narrow` (see CUTS), and the only
  carried number is back at zero. The staleness refusal is the checker's
  (`N211`); what the RUN does is this store, and that is what is proved.
-/
import Grammatik.ArenaZucker

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Disziplin
variable (O : Orakel D) (passes : Nat)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- **Reset wholesales are safe.** After `reset A;` the counter stands at
    zero -- strictly under the hard bound -- so the next `alloc` runs its
    body (never its `else`) with a freshly issued index whose value is `0`:
    every slot is reusable and no generation check is owed to the run. The
    index is carried existentially (`k.n = 0`) so no dependent rewriting is
    needed. Every premise is used (`hwG`/`hLG` feed both the reset and the
    alloc; the rest feed the alloc); the conclusion is not a premise; worlds
    come from `execStmt` and `execBlock`. -/
theorem reset_alloc_laueft_rumpf (A : ArenaForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) :
    ∃ σ₁ : World D, ∃ k : Wert D (Ty.index (D.count A.tab)), k.n = 0 ∧
      execStmt (V := V) O passes R (Stmt.arenaReset (l := l) A hwG hLG) σ ρ
        = .ok σ₁ ρ ∧
      A.stand σ₁ = 0 ∧
      execBlock (V := V) O passes R
        (Block.arenaAlloc A v hwT hLT hwG hLG voll rest) σ₁ ρ
      = (execBlock O passes R (Block.arenaRumpf A v hwT hLT hwG hLG rest)
          (σ₁.lese Λ [Sum.inr A.zaehl])
          (.cons k ρ)).schrumpf := by
  obtain ⟨σ₁, hrst, h0⟩ := arenaReset_stand O passes R A hwG hLG σ ρ
  have hlt : A.stand σ₁ < D.count A.tab := by
    rw [h0]; have := A.hpos; omega
  refine ⟨σ₁, ⟨A.stand σ₁, A.stand_nonneg σ₁, by omega⟩, h0, hrst, h0, ?_⟩
  exact arenaAlloc_unter_schranke O passes R A v hwT hLT hwG hLG voll rest
    σ₁ ρ hlt

end Disziplin

section Zeuge

/-- The witness oracle over the four-slot fixture: no axioms, no registers;
    visibility answers `false`. -/
def oz : Orakel ArenaZeuge.ZD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun _ _ => false

/-- The `else` continuation for the witness: return with nothing left to hold. -/
def voll0 : Endblock ArenaZeuge.ZD ArenaZeuge.ZV false [] [] :=
  .ret .keine (by rfl)

/-- **Joint witness on the four-slot fixture.** Every premise of
    `reset_alloc_laueft_rumpf` is instantiated JOINTLY: the arena `Log`
    (table of four byte slots beside the `0 .. 4` counter), the stored value
    `sieben`, the concrete continuations `voll0`/`Block.nil`, the FULL world
    (`welt 4` -- the wholesale case: reset from full, then reissue), the
    empty environment, the witness oracle and `keinRuf`. NON-DEGENERATE: the
    fixture's one table is written by the reissued body, and both the reset
    (global store `4 -> 0`) and the body (slot store plus bump) change
    memory. -/
theorem reset_alloc_rumpf_zeuge :
    ∃ (σ₁ : World ArenaZeuge.ZD)
      (k : Wert ArenaZeuge.ZD
        (Ty.index (ArenaZeuge.ZD.count ArenaZeuge.Log.tab))),
      k.n = 0 ∧
      execStmt (V := ArenaZeuge.ZV) (l := false) (Γ := []) (Λ := []) oz 0 keinRuf
        (Stmt.arenaReset ArenaZeuge.Log rfl ArenaZeuge.zeuge_gdarf)
        (ArenaZeuge.welt 4 (by decide) (by decide)) .nil = .ok σ₁ .nil ∧
      ArenaZeuge.Log.stand σ₁ = 0 ∧
      execBlock (V := ArenaZeuge.ZV) (l := false) (Γ := []) (Λ := []) oz 0 keinRuf
        (Block.arenaAlloc ArenaZeuge.Log ArenaZeuge.sieben rfl
          ArenaZeuge.zeuge_darf rfl ArenaZeuge.zeuge_gdarf voll0 Block.nil)
        σ₁ .nil
      = (execBlock (l := false) oz 0 keinRuf
          (Block.arenaRumpf ArenaZeuge.Log ArenaZeuge.sieben rfl
            ArenaZeuge.zeuge_darf rfl ArenaZeuge.zeuge_gdarf Block.nil)
          (σ₁.lese [] [Sum.inr ArenaZeuge.Log.zaehl])
          (.cons k .nil)).schrumpf := by
  obtain ⟨σ₁, k, hkn, h1, h2, h3⟩ :=
    reset_alloc_laueft_rumpf oz 0 keinRuf ArenaZeuge.Log ArenaZeuge.sieben
      rfl ArenaZeuge.zeuge_darf rfl ArenaZeuge.zeuge_gdarf voll0 Block.nil
      _ .nil
  exact ⟨σ₁, k, hkn, h1, h2, h3⟩

/-- **The negative direction.** Without a reset, `alloc` on the FULL arena
    takes its `else` -- the wholesale is what makes the reissue safe, and
    this is the check that the positive theorem above is not vacuous. -/
theorem alloc_voll_ohne_reset_nimmt_else :
    execBlock (V := ArenaZeuge.ZV) (l := false) (Γ := []) (Λ := []) oz 0 keinRuf
      (Block.arenaAlloc ArenaZeuge.Log ArenaZeuge.sieben rfl
        ArenaZeuge.zeuge_darf rfl ArenaZeuge.zeuge_gdarf voll0 Block.nil)
      (ArenaZeuge.welt 4 (by decide) (by decide)) .nil
    = (execEnd (l := false) (Γ := []) oz 0 keinRuf voll0
        ((ArenaZeuge.welt 4 (by decide) (by decide)).lese []
          [Sum.inr ArenaZeuge.Log.zaehl]) .nil).zuAusgang :=
  ArenaZeuge.zeuge_alloc_voll oz 0 keinRuf voll0 Block.nil

#print axioms reset_alloc_laueft_rumpf
#print axioms reset_alloc_rumpf_zeuge
#print axioms alloc_voll_ohne_reset_nimmt_else

end Zeuge

end Gabbro.Grammatik

/-! CUTS -- what this file does NOT claim.

  * **Stale indices are refused by the checker, not here.** The generation
    is checker state (`N211` refuses a use of an index bound before a
    `reset`); `ArenaZucker.lean` section 6 books the same cut. What this
    file adds is the run half: after a reset every slot IS reusable (index
    `0` runs the body), so the wholesale never strands storage.
  * **No stored reference can go stale in the sugar.** An `alloc` index is
    a binder introduced by `Block.narrow`, scoped to the continuation
    block; there is no handle that outlives a `reset` to become dangling.
    This inexpressibility is stated, not formalised: proving it would mean
    quantifying over all terms, which rule 13 forbids without a witness.
  * **Commit is untouched.** `reset` keeps the committed prefix (monotone
    commit, PLAN-DYNAMISCH.md section 3): the counter store moves `stand`
    and nothing else (`stand_schreibGlob` for the counter global only;
    `DynArena.dynGrow_monoton` is lane 241's model half). No cost arm is
    built here: `reset` stays `Kosten::Zahl(1)` (`kosten.rs`, untouched --
    that file is lanes 223/232's); the `grow` cost arm needs the parser
    lane's `StmtArt::Grow` first (see the report).
  * `alloc_voll_ohne_reset_nimmt_else` is the planted-defect-shaped check:
    the full arena without reset takes `else` (by application of
    `zeuge_alloc_voll`); the reset-then-alloc run does not.
-/
