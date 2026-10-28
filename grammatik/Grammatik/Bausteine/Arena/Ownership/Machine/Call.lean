import Grammatik.Bausteine.Arena.Ownership.Machine.Local

/-! **A call keeps ownership on the machine.** The running activation of
thread `u` at depth `a` hands its arguments to the callee at depth `a + 1`
and becomes suspended: over the ledger it sees it realises its context
after the call, and its residue is judged from where it resumes. The
callee starts its checked body from its interface precondition. -/

namespace Gabbro.Grammatik.ArenaOwnership.Machine

open Source Body

variable {D : Deklaration}

theorem lower_self (depth : Nat → Nat) (t a : Nat) : Pop.lower depth t a t = a := by simp only [Pop.lower, ↓reduceIte]

theorem lower_other (depth : Nat → Nat) {t u : Nat} (a : Nat) (h : u ≠ t) : Pop.lower depth t a u = depth u := by
  simp only [Pop.lower, h, ↓reduceIte]

/-- **The call, on the whole machine.** -/
theorem ownInv_push {P : Programm D} {A : FreiForm D} {I : Interfaces A} (hc : Checked P A I)
    {M M' : RufMaschineG D} {u : Faden} {s : State}
    (hag : s.agrees A (M.speicher.welt [])) (hfo : A.FreiOk (M.speicher.welt []))
    (hd : s.Disciplined (depthOf M)) (hth : ∀ t, ThreadOk A I s (M.speicher.welt []) t (M.faeden t))
    {c : Context} {gh : Ghost} {ms : List (Option PassingMode)} {os : List (Option Nat)}
    {l : Bool} {Γ : Ctx} {Λ' : List (Res D)} {ρ : Env D Γ}
    (hf : FrameOk c gh s ⟨u, (M.faeden u).stapel.length⟩ ρ) (hp : planFits c ms os = true)
    {k : Context} (hk : k.references.length ≤ Γ.length)
    {gf : D.Fn} {rhoC : Env D (D.params gf)}
    (hFc : FrameOk (Flow.parameterContext (I gf).parameters) (calleeGhost gh ms os s.next)
      (s.handoff ⟨u, (M.faeden u).stapel.length + 1⟩ (movedHandles gh ms os) (lentHandles gh ms os))
      ⟨u, (M.faeden u).stapel.length + 1⟩ rhoC)
    {res : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ'}
    (hres : Resume A I (M.faeden u).kopf.f k (c.afterCall ms os) (Flow.Output.isOwner (I gf).output) res)
    {s0' : World D} {spur' : List (Ereignis D)} {log' : List (RufEreignisF D)}
    (hmem : M'.speicher = M.speicher)
    (hM' : M'.faeden = rufUpdateG M.faeden u
      ⟨⟨(M.faeden u).kopf.f, (M.faeden u).kopf.rho, (M.faeden u).kopf.s0, ⟨l, Γ, Λ', ρ, res⟩⟩ :: (M.faeden u).stapel,
       ⟨gf, rhoC, s0', ⟨false, D.params gf, Signatur.anfang D (D.signatur gf), rhoC, .ende (P.rumpf gf)⟩⟩,
       spur', log'⟩) :
    OwnInv A I M' := by
  have hR : Realizes c gh A ⟨u, (M.faeden u).stapel.length⟩ s (M.speicher.welt []) ρ :=
    ⟨hag, hfo, hf.1, hf.2.1, hf.2.2.1⟩
  have hok := handoff_ok_at hR hp ⟨u, (M.faeden u).stapel.length + 1⟩ (Push.fresh hd rfl)
  have hdepth : depthOf M' = Pop.lower (depthOf M) u ((M.faeden u).stapel.length + 1) := by
    funext t
    simp only [depthOf, hM']
    by_cases htu : t = u
    · subst htu; simp only [rufUpdateG_self, List.length_cons, lower_self, Nat.add_left_cancel_iff]
    · rw [rufUpdateG_noteq _ _ _ htu, lower_other _ _ htu]; rfl
  have hd' := Push.disciplined hd rfl hok
  refine ⟨_, by rw [hmem]; exact handoff_agrees hok hag, by rw [hmem]; exact hfo, hdepth ▸ hd', fun t => ?_⟩
  rw [hmem]
  by_cases htu : t = u
  · subst htu
    rw [hM', rufUpdateG_self]
    refine ⟨.run rhoC _ (Nat.zero_le _) hFc (.ende _ (hc gf)), ?_, ?_⟩
    · exact .mk ρ res hk (Push.caller_frame hd rfl hR hf.2.2.2 hp) hres
    · exact StackOk.transfer (hth t).2 fun a ha => (Push.view_other hd rfl hok (Or.inr ha)).symm
  · rw [hM', rufUpdateG_noteq _ _ _ htu]
    have hrunt : View.Running (depthOf M) ⟨t, (M.faeden t).stapel.length⟩ := rfl
    have hrunt' : View.Running (Pop.lower (depthOf M) u ((M.faeden u).stapel.length + 1))
        ⟨t, (M.faeden t).stapel.length⟩ := by
      show (M.faeden t).stapel.length = Pop.lower (depthOf M) u ((M.faeden u).stapel.length + 1) t
      rw [lower_other _ _ htu]; rfl
    refine ⟨(hth t).1.other hd hd' hrunt hrunt' (Push.view_other hd rfl hok (Or.inl htu)).symm
      (fun _ _ => rfl) (fun _ _ _ _ => rfl), ?_⟩
    exact StackOk.transfer (hth t).2 fun a _ => (Push.view_other hd rfl hok (Or.inl htu)).symm

end Gabbro.Grammatik.ArenaOwnership.Machine
