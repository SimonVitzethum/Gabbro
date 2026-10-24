import Grammatik.Bausteine.Arena.Ownership.Machine.Rely
import Grammatik.Speichermodell.Atomar.AtomarLauf

/-! **Ownership on every reachable machine: G, GA and GX.** On machine G the
invariant holds at the start and every step keeps it. Machines GA and GX
present a step memory that may differ from G's at atomic carriers only
and keep every carrier the step does not write; when the allocator words
are plain (not atomic), every carrier the invariant reads is presented and
left as G would, so the invariant holds on every GA and GX run as well. -/

namespace Gabbro.Grammatik.ArenaOwnership.Machine

open Source Body

variable {D : Deklaration}

/-- **The arena's allocator words are plain**: no weak-memory answer reaches them. -/
def ArenaPlain (A : FreiForm D) : Prop := D.atomar A.kopf = false ∧ D.atomar A.zaehl = false

instance (A : FreiForm D) : Decidable (ArenaPlain A) := inferInstanceAs (Decidable (_ ∧ _))

/-- **The declared start memory holds an empty arena**: nothing used, the list empty. -/
def ArenaLeer (A : FreiForm D) (sp0 : Speicher D) : Prop :=
  A.stand (sp0.welt []) = 0 ∧ A.kopfSt (sp0.welt []) = D.count A.tab

instance (A : FreiForm D) (sp0 : Speicher D) : Decidable (ArenaLeer A sp0) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- What the rely and the start need of the program and its threads. -/
structure ThreadFacts (P : Programm D) (A : FreiForm D) (fs : List D.Fn)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) where
  K : Faden → D.Fn → Bool
  abg : ∀ t, AbgK P fs (K t)
  wurzel : ∀ t, K t (init t).1 = true
  exklusiv : StartExklusiv init
  sep : ∀ g, (g = A.kopf ∨ g = A.zaehl) → (∀ L, ¬ Bewacht (.inr g : D.Tab ⊕ D.Glob) L) →
    SchreibGetrenntK P K (.inr g)

section Reach

variable {P : Programm D} {A : FreiForm D} {I : Interfaces A} {O : Orakel D} {passes : Nat}
  {fs : List D.Fn} {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}

/-- **Ownership on every machine G reaches.** -/
theorem ownInv_reach (hO : GutO O) (hc : Checked P A I) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hT : ThreadFacts P A fs init) (hs : StartOwn A I sp init) {M : RufMaschineG D}
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M) : OwnInv A I M := by
  induction hr with
  | start => exact ownInv_start hc hs
  | schritt M M' u hrM hst ih =>
    exact ownInv_step hO hc ih
      (rely_of hO hvoll sp init hT.K hT.abg hT.wurzel hT.exklusiv hT.sep hrM hst) hst

/-- The invariant reads of the memory only the head, the counter and the links. -/
theorem ownInv_congr {M M' : RufMaschineG D} (h : OwnInv A I M) (hfa : M'.faeden = M.faeden)
    (hk : M'.speicher.globs A.kopf = M.speicher.globs A.kopf)
    (hz : M'.speicher.globs A.zaehl = M.speicher.globs A.zaehl)
    (hn : ∀ j, M'.speicher.slots A.tab j A.nxt = M.speicher.slots A.tab j A.nxt) : OwnInv A I M' := by
  obtain ⟨s, hag, hfo, hd, hth⟩ := h
  have hm : MetaSame A (M.speicher.welt []) (M'.speicher.welt []) := MetaSame.of_cells A hk hz hn
  have hdep : depthOf M' = depthOf M := by funext t; simp [depthOf, hfa]
  refine ⟨s, State.agrees_meta hag hm, freiOk_meta hfo hm, hdep ▸ hd, fun t => ?_⟩
  rw [hfa]
  exact ⟨(hth t).1.meta hm, (hth t).2⟩

theorem plain_kopf (hp : ArenaPlain A) : ¬ AtomarAusgenommen (.inr A.kopf : D.Tab ⊕ D.Glob) := by
  rintro ⟨g, hg, ha⟩; cases hg; rw [hp.1] at ha; cases ha

theorem plain_zaehl (hp : ArenaPlain A) : ¬ AtomarAusgenommen (.inr A.zaehl : D.Tab ⊕ D.Glob) := by
  rintro ⟨g, hg, ha⟩; cases hg; rw [hp.2] at ha; cases ha

theorem plain_tab (t : D.Tab) : ¬ AtomarAusgenommen (.inl t : D.Tab ⊕ D.Glob) := by
  rintro ⟨g, hg, _⟩; cases hg

/-- After a GA step, every carrier that is not atomic is as the inner G step left it. -/
theorem ga_plain {M M' M'' : RufMaschineG D} {u : Faden} {σ : Speicher D}
    (hσ : ∀ c, ¬ AtomarAusgenommen c → TraegerGleich σ M.speicher c)
    (hW : ∀ c, SchreibG (mitSpeicher M σ) M'' u c → TraegerGleich M'.speicher M''.speicher c)
    (hU : ∀ c, ¬ SchreibG (mitSpeicher M σ) M'' u c → TraegerGleich M'.speicher M.speicher c)
    {c : D.Tab ⊕ D.Glob} (hc : ¬ AtomarAusgenommen c) : TraegerGleich M'.speicher M''.speicher c := by
  by_cases hw : SchreibG (mitSpeicher M σ) M'' u c
  · exact hW c hw
  · have h1 := hU c hw
    have h2 : TraegerGleich M''.speicher σ c := traegerGleich_of_nicht_schreib hw
    have h3 := hσ c hc
    cases c with
    | inl t => exact h1.trans (h3.symm.trans h2.symm)
    | inr g => exact h1.trans (h3.symm.trans h2.symm)

/-- **Ownership on every machine GA reaches**, for plain allocator words. -/
theorem ownInv_reachGA (hO : GutO O) (hc : Checked P A I) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hT : ThreadFacts P A fs init) (hs : StartOwn A I sp init) (hp : ArenaPlain A) {M : RufMaschineG D}
    (hr : RufErreichbarGA P O passes (RufStartG P sp init) M) : OwnInv A I M := by
  have hHalt : ∀ {M}, RufErreichbarGA P O passes (RufStartG P sp init) M → ∀ t, HaeltInvG (M.faeden t) :=
    fun hr => gaInv (I := fun M => ∀ t, HaeltInvG (M.faeden t)) (fun M M' e h t => by rw [← e]; exact h t)
      (fun t => haeltInvG_start P sp init t)
      (fun M M' u h hs t => by
        by_cases htu : t = u
        · subst htu; exact rufSchrittG_haeltInv hO hs (h t)
        · rw [rufSchrittG_passt_anders P O passes M M' u t htu hs]; exact h t) hr
  have hK : ∀ {M}, RufErreichbarGA P O passes (RufStartG P sp init) M → ∀ v, hT.K v (M.faeden v).kopf.f = true :=
    fun hr v => ((gaInv_merk sp init (fun t g => hT.K t g = true) (fun t _ => rufM fs (hT.K t))
      (fun t => merkAbg_rufM hvoll (hT.abg t)) hT.wurzel hr) v _ List.mem_cons_self).1
  induction hr with
  | start => exact ownInv_start hc hs
  | schritt M M' u hrM hst ih =>
    obtain ⟨σ, M'', hs', hσ, hW, hU, hfa, _, _⟩ := hst
    have hM : OwnInv A I (mitSpeicher M σ) :=
      ownInv_congr ih rfl (hσ _ (plain_kopf hp)) (hσ _ (plain_zaehl hp))
        (fun j => congrFun (congrFun (hσ _ (plain_tab A.tab)) j) A.nxt)
    have hrely := rely_core hO hT.K hT.sep (M := mitSpeicher M σ) (hHalt (M := M) hrM)
      (gaInv_exklusiv (M := M) hO sp init hT.exklusiv hrM) (hK (M := M) hrM) hs'
    have hM'' := ownInv_step hO hc hM hrely hs'
    exact ownInv_congr hM'' hfa (ga_plain hσ hW hU (plain_kopf hp)) (ga_plain hσ hW hU (plain_zaehl hp))
      (fun j => congrFun (congrFun (ga_plain hσ hW hU (plain_tab A.tab)) j) A.nxt)

/-- **Ownership on every machine GX reaches**, when its shared atomics are atomic. -/
theorem ownInv_reachGX (hO : GutO O) (hc : Checked P A I) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hT : ThreadFacts P A fs init) (hs : StartOwn A I sp init) (hp : ArenaPlain A)
    {Tg : D.Tab ⊕ D.Glob → Prop} (hTA : ∀ c, Tg c → AtomarAusgenommen c) {M : RufMaschineG D}
    (hr : RufErreichbarGX P O passes Tg (RufStartG P sp init) M) : OwnInv A I M :=
  ownInv_reachGA hO hc hvoll hT hs hp (gx_ga_lauf hTA hr)

end Reach

#print axioms ownInv_reach
#print axioms ownInv_reachGA
#print axioms ownInv_reachGX

end Gabbro.Grammatik.ArenaOwnership.Machine
