import Grammatik.Bausteine.Arena.Ownership.Source.Expressions

namespace Gabbro.Grammatik.ArenaOwnership.Source

variable {D : Deklaration}

/-- Shared source rule for releasing or passing an owning argument. -/
def consume {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (c : Context)
    (e : Expr D Γ Λ τ) : Option (Context × Nat) := do
  let i ← origin c e
  if c.rights i = some .owned then some (c.kill i, i) else none

theorem consume_facts {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    {c c' : Context} {e : Expr D Γ Λ τ} {i : Nat} (hc : consume c e = some (c', i)) :
    origin c e = some i ∧ c.rights i = some .owned ∧ c' = c.kill i := by
  unfold consume at hc
  cases ho : origin c e with
  | none => simp [ho] at hc
  | some j =>
    rw [ho] at hc
    change (if c.rights j = some .owned then some (c.kill j, j) else none) = some (c', i) at hc
    split at hc
    · rename_i hr
      cases hc
      exact ⟨rfl, hr, rfl⟩
    · cases hc

theorem PassingMode.permits_same_cell {mode : PassingMode} {s s' : State} {frame : Frame} {h : Handle}
    (he : s'.cells h.slot = s.cells h.slot) (hp : mode.permits s frame h) : mode.permits s' frame h := by
  cases mode with
  | owned => exact State.owns_from_same_cell he hp
  | borrowed => exact State.access_from_same_cell he hp

/-- Consuming one origin preserves every other active origin. Aliases of
the consumed origin remain named but have no right, so none is revived. -/
theorem rights_after_consumption {c : Context} {g : Ghost} {s s' : State} {frame : Frame} {i : Nat} {h : Handle}
    (hp : Rights c g s frame) (hi : c.rights i = some .owned) (hg : g i = some h)
    (hframe : ∀ j, j ≠ h.slot → s'.cells j = s.cells j) : Rights (c.kill i) g s' frame := by
  constructor
  · intro j mode hj
    have hne : j ≠ i := by intro he; simp [Context.kill, he] at hj
    have hright : c.rights j = some mode := by simpa [Context.kill, hne] using hj
    obtain ⟨k, hgk, hk⟩ := hp.1 j mode hright
    have hslots : k.slot ≠ h.slot := hp.2 j i mode .owned hright hi hne (Or.inr rfl) k h hgk hg
    exact ⟨k, hgk, PassingMode.permits_same_cell (hframe k.slot hslots) hk⟩
  · exact (Context.kill_rights hp i).2

section Release

variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

/-- The executable source consume check discharges release's ownership
premise. The continuation receives the computed source context, not an
assumed semantic ownership postcondition. -/
theorem checked_release (A : FreiForm D) (c c' : Context) (g : Ghost) (frame : Frame)
    (s : State) (σ : World D) (ρ : Env D Γ) (x : Var Γ (Ty.index (D.count A.tab))) (i : Nat)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwF : V.gschreibt A.kopf = true) (hLF : gdarf D A.kopf Λ) (rest : Block D V l Γ Λ Λ')
    (hc : consume c (.var (Λ := Λ) x) = some (c', i)) (hgood : Realizes c g A frame s σ ρ) :
    ∃ (s' : State) (σ' : World D) (h : Handle),
      execBlock O passes R (Block.freiVar A x hwT hLT hwF hLF rest) σ ρ = execBlock O passes R rest σ' ρ ∧
      Realizes c' g A frame s' σ' ρ ∧ g i = some h ∧ (∀ other, ¬ s'.access other h) := by
  obtain ⟨hsource, howned, hctx⟩ := consume_facts hc
  obtain ⟨ha, hf, hb, hrefs, hrights⟩ := hgood
  obtain ⟨h, hg, hown⟩ := hrights.1 i .owned howned
  obtain ⟨other, hg', hvalue⟩ := origin_sound c g ρ hrefs (.var (Λ := Λ) x) i hsource σ σ
  rw [hg] at hg'
  cases hg'
  have hx : (ρ.get x).n = h.slot := Option.some.inj hvalue
  obtain ⟨s', σ', hrel, he, ha', hf', _, hdead⟩ := release_execution O passes R A s frame h x
    hwT hLT hwF hLF rest σ ρ ha hf hown hx
  refine ⟨s', σ', h, he, ?_, hg, hdead⟩
  rw [hctx]
  exact ⟨ha', hf', Context.kill_bounded hb i, Context.kill_references hrefs i,
    rights_after_consumption hrights howned hg (fun j hj => State.release_other hrel j hj)⟩

end Release

#print axioms checked_release

end Gabbro.Grammatik.ArenaOwnership.Source
