module

public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG
public import Grammatik.Nebenlaeufigkeit.Allgemein.FadenMerkmal.Teil1
public import Grammatik.Nebenlaeufigkeit.Allgemein.FadenMerkmal.Teil1a

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Inv
variable {P : Programm D} {O : Orakel D} {pa : Nat}

theorem merkInvG_schritt {Z : D.Fn → Prop} {A : D.Fn → Merkmal D} (hA : MerkAbg P Z A)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O pa M f M')
    (h : MerkInvG Z A (M.faeden f)) : MerkInvG Z A (M'.faeden f) := by
  have hk := h _ List.mem_cons_self
  rcases schrittMerk hs with ⟨hst, hf, hR⟩ | ⟨g, caller', rho, s0, hst, hcf, hkopf, hR⟩ |
      ⟨caller, rst, hpop, hst, hf, hR⟩
  · intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · refine ⟨hf ▸ hk.1, ?_⟩
      have := hR (A (M.faeden f).kopf.f) hk.2
      rw [← hf] at this
      exact this
    · rw [hst] at hF
      exact h F (List.mem_cons_of_mem _ hF)
  · obtain ⟨hz, hc⟩ := hR (A (M.faeden f).kopf.f) hk.2
    have hg := (hA _ hk.1).2 g hz
    intro F hF
    rw [hst, hkopf] at hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact ⟨hg, (hA g hg).1⟩
    · rcases List.mem_cons.mp hF with rfl | hF
      · refine ⟨hcf ▸ hk.1, ?_⟩
        rw [← hcf] at hc
        exact hc
      · exact h F (List.mem_cons_of_mem _ hF)
  · have hc := h caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · refine ⟨hf ▸ hc.1, ?_⟩
      have := hR (A caller.f) hc.2
      rw [← hf] at this
      exact this
    · rw [hst] at hF
      exact h F (by rw [hpop]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hF))

/-- **The thread invariant on every reachable machine**, per thread `t` with
    its own function set `Z t` and features `A t`, given the closure and a
    start function in `Z t`. -/
theorem merkInvG_erreichbar (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (Z : Faden → D.Fn → Prop) (A : Faden → D.Fn → Merkmal D)
    (hA : ∀ t, MerkAbg P (Z t) (A t)) (hZ : ∀ t, Z t (init t).1) {M : RufMaschineG D}
    (hr : RufErreichbarG P O pa (RufStartG P sp init) M) :
    ∀ t, MerkInvG (Z t) (A t) (M.faeden t) := by
  induction hr with
  | start =>
      intro t F hF
      have e : (RufStartG P sp init).faeden t =
          ⟨[], ⟨(init t).1, (init t).2, sp.welt [], ⟨false, D.params (init t).1,
            Signatur.anfang D (D.signatur (init t).1), (init t).2, .ende (P.rumpf (init t).1)⟩⟩,
            startSpur (init t).1, [RufEreignisF.eintritt (init t).1 (init t).2 (sp.welt [])]⟩ := by
        show (match init t with
          | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
              Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
              [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D)) = _
        cases init t
        rfl
      rw [e] at hF
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      subst hF
      exact ⟨hZ t, (hA t _ (hZ t)).1⟩
  | schritt M M' u _ hs ih =>
      intro t
      by_cases htu : t = u
      · subst htu
        exact merkInvG_schritt (hA t) hs (ih t)
      · rw [rufSchrittG_fremd hs t htu]
        exact ih t

end Inv

#print axioms Gabbro.Grammatik.schrittMerk
#print axioms Gabbro.Grammatik.merkInvG_erreichbar

end Gabbro.Grammatik
