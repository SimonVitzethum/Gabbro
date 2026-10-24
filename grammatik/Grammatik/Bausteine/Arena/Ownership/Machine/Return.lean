import Grammatik.Bausteine.Arena.Ownership.Machine.Call

/-! **A return keeps ownership on the machine.** The running activation
returns a value (or a reason) to its suspended caller. Its checked result
says what it still owns: nothing (a plain result, a reason) or exactly the
allocation it hands back. The caller resumes over the popped ledger from
the context its `Resume` names. -/

namespace Gabbro.Grammatik.ArenaOwnership.Machine

open Source Body

variable {D : Deklaration}

theorem FrameOk.bindNone {c : Context} {g : Ghost} {s : State} {fr : Frame} {Γ : Ctx} {ρ : Env D Γ} {τ : Ty}
    (hf : FrameOk c g s fr ρ) (v : Wert D τ) : FrameOk (c.bind none) g s fr (.cons v ρ) :=
  ⟨Context.bind_bounded hf.1 none (fun _ h => by cases h), References.bind hf.2.1 v none (fun _ h => by cases h),
    hf.2.2.1, Complete.bind hf.2.2.2 none⟩

section Result

variable {A : FreiForm D} {s : State} {cf : Frame}

theorem result_plain {erg : Option Ty} (out : Flow.Output A erg) (v : ErgVal D erg)
    (h : out.result A cf s v) (ho : Flow.Output.isOwner out = false) : s.closed cf := by
  cases out with
  | plain => exact h
  | owner => cases ho

theorem result_owner {erg : Option Ty} (out : Flow.Output A erg) (v : ErgVal D erg) {τ : Ty} (he : erg = some τ)
    (h : out.result A cf s v) (ho : Flow.Output.isOwner out = true) :
    ∃ hh, s.owns cf hh ∧ s.single cf hh ∧ intVon τ (ergWert he v) = some hh.slot := by
  cases out with
  | plain => cases ho
  | owner =>
    cases he
    obtain ⟨hh, hown, hslot, hsingle⟩ := h
    exact ⟨hh, hown, hsingle, by simp [ergWert, intVon, hslot]⟩

theorem result_ownerAny {erg : Option Ty} (out : Flow.Output A erg) (v : ErgVal D erg)
    (h : out.result A cf s v) (ho : Flow.Output.isOwner out = true) :
    ∃ hh, s.owns cf hh ∧ s.single cf hh := by
  cases out with
  | plain => cases ho
  | owner => obtain ⟨hh, hown, _, hsingle⟩ := h; exact ⟨hh, hown, hsingle⟩

end Result

/-! ## The caller, resumed -/

section Resume

variable {A : FreiForm D} {I : Interfaces A} {s : State} {depth : Nat → Nat} {t a : Nat} {σ : World D}

/-- **After a plain call** the caller's residue runs on. -/
theorem resume_plain (hd : s.Disciplined depth) (hdepth : depth t = a + 1) {g f : D.Fn} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {ρ : Env D Γ} {r : GRest D (vertragVon D f) l Γ Λ}
    (hs : Susp A I ⟨t, a⟩ s g f ⟨l, Γ, Λ, ρ, r⟩) (hw : r.wartend = false) (v : ErgVal D (D.erg g))
    (hres : (I g).output.result A ⟨t, a + 1⟩ s v) :
    Head A I ⟨t, a⟩ (s.pop ⟨t, a + 1⟩ ⟨t, a⟩) σ f ⟨l, Γ, Λ, ρ, r⟩ := by
  cases hs with
  | mk _ _ hk hf hresume =>
    cases hresume with
    | plain _ hr =>
      cases ho : Flow.Output.isOwner (I g).output with
      | false =>
        rw [ho] at hr
        exact .run ρ r hk (Pop.frame_plain hd hdepth hf (result_plain _ v hres ho)) hr
      | true =>
        rw [ho] at hr
        obtain ⟨hh, hown, hsingle⟩ := result_ownerAny _ v hres ho
        exact .run ρ r hk (Pop.frame_ownerDrop hd hdepth hf hown hsingle) hr
    | wartet => cases hw
    | wartetSonst => cases hw

/-- **After a binding call** the caller binds the value in front of its rest. -/
theorem resume_bind (hd : s.Disciplined depth) (hdepth : depth t = a + 1) {g f : D.Fn} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {τ : Ty} {ρ : Env D Γ} {restb : Block D (vertragVon D f) l (τ :: Γ) Λ Λ'}
    {r : GRest D (vertragVon D f) l Γ Λ'} {x : GRest D (vertragVon D f) l Γ Λ}
    (hs : Susp A I ⟨t, a⟩ s g f ⟨l, Γ, Λ, ρ, x⟩)
    (hx : x = .wartet restb r ∨ ∃ (n : Nat) (err : Endblock D (vertragVon D f) l (.why n :: Γ) Λ),
      x = .wartetSonst n err restb r)
    (v : ErgVal D (D.erg g)) (he : D.erg g = some τ) (hres : (I g).output.result A ⟨t, a + 1⟩ s v) :
    Head A I ⟨t, a⟩ (s.pop ⟨t, a + 1⟩ ⟨t, a⟩) σ f
      ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρ, .dann restb (.schrumpf r)⟩ := by
  cases hs with
  | @mk _ _ _ k cs gh _ _ hk hf hresume =>
    have hr : OR A I (I f).output k (resultContextB cs (Flow.Output.isOwner (I g).output))
        (.dann restb (.schrumpf r)) := by
      rcases hx with rfl | ⟨n, err, rfl⟩
      · cases hresume with
        | plain _ hr => cases hr
        | wartet _ _ hr => exact hr
      · cases hresume with
        | plain _ hr => cases hr
        | wartetSonst _ _ _ _ hr _ => exact hr
    cases ho : Flow.Output.isOwner (I g).output with
    | false =>
      rw [ho] at hr
      exact .run _ _ (Nat.le_succ_of_le hk)
        ((Pop.frame_plain hd hdepth hf (result_plain _ v hres ho)).bindNone _) hr
    | true =>
      rw [ho] at hr
      obtain ⟨hh, hown, hsingle, hv⟩ := result_owner _ v he hres ho
      exact .run _ _ (Nat.le_succ_of_le hk) (Pop.frame_owner hd hdepth hf hown hsingle _ hv) hr

/-- **After a reason** the caller runs its `else` branch with the reason bound. -/
theorem resume_why (hd : s.Disciplined depth) (hdepth : depth t = a + 1) {g f : D.Fn} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {τ : Ty} {ρ : Env D Γ} {n : Nat} {err : Endblock D (vertragVon D f) l (.why n :: Γ) Λ}
    {restb : Block D (vertragVon D f) l (τ :: Γ) Λ Λ'} {r : GRest D (vertragVon D f) l Γ Λ'}
    (hs : Susp A I ⟨t, a⟩ s g f ⟨l, Γ, Λ, ρ, .wartetSonst n err restb r⟩) (hclosed : s.closed ⟨t, a + 1⟩)
    (w : Fin n) :
    Head A I ⟨t, a⟩ (s.pop ⟨t, a + 1⟩ ⟨t, a⟩) σ f
      ⟨l, .why n :: Γ, Λ, .cons (τ := .why n) w ρ, .dann err.alsBlock.2 (.abbruch (.schrumpf r))⟩ := by
  cases hs with
  | mk _ _ hk hf hresume =>
    cases hresume with
    | plain _ hr => cases hr
    | wartetSonst _ _ _ _ _ he =>
      exact .run _ _ (Nat.le_succ_of_le hk) ((Pop.frame_plain hd hdepth hf hclosed).bindNone _) he

end Resume

/-! ## The return, on the whole machine -/

/-- **The return, on the whole machine**: given the caller's resumed state over the popped ledger. -/
theorem ownInv_pop {A : FreiForm D} {I : Interfaces A} {M M' : RufMaschineG D} {u : Faden} {s : State}
    (hag : s.agrees A (M.speicher.welt [])) (hfo : A.FreiOk (M.speicher.welt []))
    (hd : s.Disciplined (depthOf M)) (hth : ∀ t, ThreadOk A I s (M.speicher.welt []) t (M.faeden t))
    {caller : RufRahmenG D} {rst : List (RufRahmenG D)} (hpop : (M.faeden u).stapel = caller :: rst)
    {nr : RufRahmenG D} (hnf : nr.f = caller.f)
    (hhead : Head A I ⟨u, rst.length⟩ (s.pop ⟨u, rst.length + 1⟩ ⟨u, rst.length⟩) (M.speicher.welt []) nr.f nr.rest)
    {spur' : List (Ereignis D)} {log' : List (RufEreignisF D)}
    (hmem : M'.speicher = M.speicher) (hM' : M'.faeden = rufUpdateG M.faeden u ⟨rst, nr, spur', log'⟩) :
    OwnInv A I M' := by
  have hdu : depthOf M u = rst.length + 1 := by
    show (M.faeden u).stapel.length = _
    rw [hpop]; rfl
  have hdepth : depthOf M' = Pop.lower (depthOf M) u rst.length := by
    funext t
    simp only [depthOf, hM']
    by_cases htu : t = u
    · subst htu; simp [rufUpdateG_self, lower_self]
    · rw [rufUpdateG_noteq _ _ _ htu, lower_other _ _ htu]; rfl
  have hd' := Pop.disciplined hd hdu
  refine ⟨_, by rw [hmem]; exact Pop.agrees hag, by rw [hmem]; exact hfo, hdepth ▸ hd', fun t => ?_⟩
  rw [hmem]
  by_cases htu : t = u
  · subst htu
    rw [hM', rufUpdateG_self]
    refine ⟨hhead, ?_⟩
    have hst := (hth t).2
    rw [hpop] at hst
    rw [hnf]
    exact StackOk.transfer hst.2 fun a ha => (Pop.view_other hd hdu (Or.inr ha)).symm
  · rw [hM', rufUpdateG_noteq _ _ _ htu]
    have hrunt : View.Running (depthOf M) ⟨t, (M.faeden t).stapel.length⟩ := rfl
    have hrunt' : View.Running (Pop.lower (depthOf M) u rst.length) ⟨t, (M.faeden t).stapel.length⟩ := by
      show (M.faeden t).stapel.length = Pop.lower (depthOf M) u rst.length t
      rw [lower_other _ _ htu]; rfl
    refine ⟨(hth t).1.other hd hd' hrunt hrunt' (Pop.view_other hd hdu (Or.inl htu)).symm
      (fun _ _ => rfl) (fun _ _ _ _ => rfl), ?_⟩
    exact StackOk.transfer (hth t).2 fun a _ => (Pop.view_other hd hdu (Or.inl htu)).symm

end Gabbro.Grammatik.ArenaOwnership.Machine
