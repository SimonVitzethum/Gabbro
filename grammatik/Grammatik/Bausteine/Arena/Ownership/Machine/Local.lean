import Grammatik.Bausteine.Arena.Ownership.Machine.Inv

/-! **A step inside one activation keeps ownership on the whole machine.**
The stepping thread's running activation moves to its next state over a
next ledger that keeps every cell it does not own and every link it does
not own. No other activation's view moves. Another thread's running
activation inside an allocator form relies on the allocator word it is
about to write (`pendWord`): that word is the one rely this step must keep. -/

namespace Gabbro.Grammatik.ArenaOwnership.Machine

open Source Body

variable {D : Deklaration}

/-- The allocator word a residue is about to write within its next two statements. -/
def pendWord (A : FreiForm D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Option D.Glob
  | .dann (.cons (.assignGlob g _ _ _) _) _ => if g = A.kopf ∨ g = A.zaehl then some g else none
  | .dann (.cons (.assignSlot _ _ _ _ _ _) (.cons (.assignGlob g _ _ _) _)) _ =>
      if g = A.zaehl then some g else none
  | _ => none

section Transfer

variable {A : FreiForm D} {I : Interfaces A} {s s' : State} {depth depth' : Nat → Nat} {fr : Frame}

theorem FrameOk.transfer {c : Context} {g : Ghost} {Γ : Ctx} {ρ : Env D Γ} (hf : FrameOk c g s fr ρ)
    (hd : s.Disciplined depth) (hd' : s'.Disciplined depth') (hrun : View.Running depth fr)
    (hrun' : View.Running depth' fr) (hv : s.viewAt fr = s'.viewAt fr) : FrameOk c g s' fr ρ := by
  refine ⟨hf.1, hf.2.1, ?_, ?_⟩
  · have := (View.rights_running hd hrun).mpr hf.2.2.1
    rw [hv] at this
    exact (View.rights_running hd' hrun').mp this
  · have := (View.complete_running hd hrun).mpr hf.2.2.2
    rw [hv] at this
    exact (View.complete_running hd' hrun').mp this

/-- **Another thread's running activation** keeps its state across a step that moves neither its view, nor
    the allocator word it is about to write, nor a link it owns. -/
theorem Head.other {σ σ' : World D} {f : D.Fn} {x} (h : Head A I fr s σ f x)
    (hd : s.Disciplined depth) (hd' : s'.Disciplined depth') (hrun : View.Running depth fr)
    (hrun' : View.Running depth' fr) (hv : s.viewAt fr = s'.viewAt fr)
    (hglob : ∀ g, pendWord A x.2.2.2.2 = some g → σ'.globs g = σ.globs g)
    (hlink : ∀ j cell, s.cells j = some cell → cell.owner = fr → A.naechst σ' j = A.naechst σ j) :
    Head A I fr s' σ' f x := by
  cases h with
  | run ρ r hk hf hr => exact .run ρ r hk (hf.transfer hd hd' hrun hrun' hv) hr
  | list x ρ e2 hw hL b r he2 hx hlt hk hf hr =>
    have hg := hglob A.kopf (by simp only [pendWord, true_or, ↓reduceIte])
    have hkopf : A.kopfSt σ' = A.kopfSt σ := by simp only [FreiForm.kopfSt, hg]
    exact .list x ρ e2 hw hL b r he2 (hkopf ▸ hx) (hkopf ▸ hlt) hk (hf.transfer hd hd' hrun hrun' hv) hr
  | counter x ρ e2 hw hL b r he2 hx hlt hk hf hr =>
    have hg := hglob A.zaehl (by simp only [pendWord, or_true, ↓reduceIte])
    have hst : A.stand σ' = A.stand σ := by simp only [ArenaForm.stand, hg]
    exact .counter x ρ e2 hw hL b r he2 (hst ▸ hx) (hst ▸ hlt) hk (hf.transfer hd hd' hrun hrun' hv) hr
  | store x ρ t f' i ev hws hLs hn e2 hw hL b r he2 hx hlt hk hf hr =>
    have hg := hglob A.zaehl (by simp only [pendWord, ↓reduceIte])
    have hst : A.stand σ' = A.stand σ := by simp only [ArenaForm.stand, hg]
    exact .store x ρ t f' i ev hws hLs hn e2 hw hL b r he2 (hst ▸ hx) (hst ▸ hlt) hk
      (hf.transfer hd hd' hrun hrun' hv) hr
  | release ρ e2 hw hL b r p o h he2 hp ho hg hlink' hk hf hr =>
    have hgk := hglob A.kopf (by simp only [pendWord, true_or, ↓reduceIte])
    have hkopf : A.kopfSt σ' = A.kopfSt σ := by simp only [FreiForm.kopfSt, hgk]
    obtain ⟨h', hg', howns⟩ := hf.2.2.1.1 o .owned ho
    rw [hg] at hg'; cases hg'
    obtain ⟨cell, hcell⟩ := State.own_cell howns
    have hn := hlink h.slot cell hcell (State.owned_cell howns hcell).2.1
    exact .release ρ e2 hw hL b r p o h he2 hp ho hg (by rw [hn, hkopf]; exact hlink') hk
      (hf.transfer hd hd' hrun hrun' hv) hr

theorem Susp.transfer {callee f : D.Fn} {x} (h : Susp A I fr s callee f x) (hv : s.viewAt fr = s'.viewAt fr) :
    Susp A I fr s' callee f x := by
  cases h with
  | mk ρ r hk hf hres => exact .mk ρ r hk (hv ▸ hf) hres

theorem StackOk.transfer {t : Faden} :
    ∀ {callee : D.Fn} {stack : List (RufRahmenG D)}, StackOk A I s t callee stack →
      (∀ a < stack.length, s.viewAt ⟨t, a⟩ = s'.viewAt ⟨t, a⟩) → StackOk A I s' t callee stack
  | _, [], _, _ => trivial
  | _, r :: rest, ⟨hs, hr⟩, hv =>
    ⟨hs.transfer (hv _ (by simp only [List.length_cons, Nat.lt_add_one])), StackOk.transfer hr (fun a ha => hv a (by simp only [List.length_cons]; omega))⟩

/-- Every cell the running activation owns carries no loan. -/
theorem Head.owned_loans {σ : World D} {f : D.Fn} {x} (h : Head A I fr s σ f x) :
    ∀ j cell, s.cells j = some cell → cell.owner = fr → cell.loans = [] := by
  have key : ∀ {c : Context} {g : Ghost} {Γ : Ctx} {ρ : Env D Γ}, FrameOk c g s fr ρ →
      ∀ j cell, s.cells j = some cell → cell.owner = fr → cell.loans = [] :=
    fun hf j cell hc ho => (hf.2.2.2 j cell hc ho).1
  cases h with
  | run _ _ _ hf _ => exact key hf
  | list _ _ _ _ _ _ _ _ _ _ _ hf _ => exact key hf
  | counter _ _ _ _ _ _ _ _ _ _ _ hf _ => exact key hf
  | store _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf _ => exact key hf
  | release _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf _ => exact key hf

end Transfer

/-! ## The step -/

theorem welt_meta (A : FreiForm D) (σ : World D) : MetaSame A σ (σ.speicher.welt []) :=
  MetaSame.of_cells A rfl rfl (fun _ => rfl)

/-- **A step inside the running activation of thread `u` keeps ownership on the machine**, provided every
    other thread's next allocator word is kept. -/
theorem ownInv_local {A : FreiForm D} {I : Interfaces A} {M M' : RufMaschineG D} {u : Faden} {s : State}
    (hag : s.agrees A (M.speicher.welt [])) (hfo : A.FreiOk (M.speicher.welt []))
    (hd : s.Disciplined (depthOf M)) (hth : ∀ t, ThreadOk A I s (M.speicher.welt []) t (M.faeden t))
    {σ σ' : World D} (hσ : MetaSame A (M.speicher.welt []) σ) (hσ' : MetaSame A σ' (M'.speicher.welt []))
    (hrely : ∀ t, t ≠ u → ∀ g, pendWord A (M.faeden t).kopf.rest.2.2.2.2 = some g →
      M'.speicher.globs g = M.speicher.globs g)
    {rho' : Env D (D.params (M.faeden u).kopf.f)} {s0' : World D}
    {x' : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ}
    {spur' : List (Ereignis D)} {log' : List (RufEreignisF D)}
    (hM' : M'.faeden = rufUpdateG M.faeden u ⟨(M.faeden u).stapel, ⟨(M.faeden u).kopf.f, rho', s0', x'⟩, spur', log'⟩)
    (hnext : Next A I ⟨u, (M.faeden u).stapel.length⟩ s σ σ' (M.faeden u).kopf.f x') :
    OwnInv A I M' := by
  obtain ⟨s', hloc, _, hag', hfo', hlinks, hhead⟩ := hnext
  have hdepth : depthOf M' = depthOf M := by
    funext t
    simp only [depthOf, hM']
    by_cases htu : t = u
    · subst htu; simp only [rufUpdateG_self]
    · simp only [rufUpdateG_noteq _ _ _ htu]
  have hrun : View.Running (depthOf M) ⟨u, (M.faeden u).stapel.length⟩ := rfl
  have hd' : s'.Disciplined (depthOf M) := View.local_disciplined hd hrun hloc hhead.owned_loans
  refine ⟨s', State.agrees_meta hag' hσ', freiOk_meta hfo' hσ', hdepth ▸ hd', fun t => ?_⟩
  by_cases htu : t = u
  · subst htu
    rw [hM', rufUpdateG_self]
    refine ⟨hhead.meta hσ', StackOk.transfer (hth t).2 fun a ha => View.local_view hd hrun hloc (Or.inr ha)⟩
  · rw [hM', rufUpdateG_noteq _ _ _ htu]
    have hrunt : View.Running (depthOf M) ⟨t, (M.faeden t).stapel.length⟩ := rfl
    have hne : (⟨t, (M.faeden t).stapel.length⟩ : Frame).thread ≠ u := htu
    refine ⟨?_, StackOk.transfer (hth t).2 fun a _ => View.local_view hd hrun hloc (Or.inl htu)⟩
    apply (hth t).1.other hd hd' hrunt hrunt (View.local_view hd hrun hloc (Or.inl hne))
    · intro g hg
      exact hrely t htu g hg
    · intro j cell hc ho
      have hne' : cell.owner ≠ ⟨u, (M.faeden u).stapel.length⟩ := by
        rw [ho]; intro he; exact htu (congrArg Frame.thread he)
      have h1 := hlinks j (fun cell' hc' => by rw [hc] at hc'; cases hc'; exact hne')
      rw [hσ'.2.1 j, h1, hσ.2.1 j]

end Gabbro.Grammatik.ArenaOwnership.Machine
