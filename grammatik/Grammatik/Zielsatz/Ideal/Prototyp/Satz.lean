/-
  File:      Grammatik/Zielsatz/Ideal/Prototyp/Satz.lean
  Subject:   PROTOTYPE of S7: the theorem of the prototype in one statement (`s7_prototyp`), and what the relation
             pins down between units (`r_ruhig`: then the ideal state IS the implementation state, up to the
             content of lent buffers, which is outside).
-/
module

public import Grammatik.Zielsatz.Ideal.Prototyp.Run

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.Ideal.Prototyp

/-- Thread 1 never masks under the discipline. -/
theorem progOk_ohneMask {P : Prog} : ∀ (L : Nat → Bool) (us : List Seg), ProgOk P 1 L us → OhneMask us
  | _, [], _ => fun _ h => by cases h
  | L, .lock _ _ :: us, h => fun u hu b he => by
      rcases List.mem_cons.1 hu with rfl | hu
      · cases he
      · exact progOk_ohneMask L us h.2 u hu b he
  | L, .masked _ :: _, h => absurd h.1 (by decide)
  | L, .atom _ _ :: us, h => fun u hu b he => by
      rcases List.mem_cons.1 hu with rfl | hu
      · cases he
      · exact progOk_ohneMask L us h u hu b he
  | L, .lend x :: us, h => fun u hu b he => by
      rcases List.mem_cons.1 hu with rfl | hu
      · cases he
      · exact progOk_ohneMask _ us h.2 u hu b he
  | L, .takeBack x :: us, h => fun u hu b he => by
      rcases List.mem_cons.1 hu with rfl | hu
      · cases he
      · exact progOk_ohneMask _ us h.2 u hu b he
  | L, .set _ _ :: us, h => fun u hu b he => by
      rcases List.mem_cons.1 hu with rfl | hu
      · cases he
      · exact progOk_ohneMask L us h u hu b he

/-- Between units (no context inside a unit) the relation pins the ideal state: the same threads, the same atomic
    memory and lock views, the same plain memory except the lent buffers, nothing pending. -/
theorem r_ruhig {P : Prog} {s : S} {i : IS} {pa : Ctx → List Int} (hR : R P s i pa) (hq : ∀ c, Rest s c = 0) :
    (∀ t, i.th t = ⟨(s.th t).prog, (s.th t).regs, (s.th t).view, (s.th t).lent⟩) ∧
    (∀ l, (∀ t, (s.th t).lent l = false) → i.mem l = s.mem l) ∧ i.am = s.am ∧ i.lview = s.lview ∧
    ∀ c, pa c = [] := by
  have hcur : ∀ t, (s.th t).cur = none := fun t => by
    have := hq (.thr t)
    unfold Rest at this
    cases hc : (s.th t).cur with
    | none => rfl
    | some cu => cases cu <;> simp [hc] at this
  have hhd : s.hd = none := by
    have := hq .irq
    unfold Rest at this
    cases hc : s.hd with
    | none => rfl
    | some x => obtain ⟨r, ρ⟩ := x; simp [hc] at this
  refine ⟨fun t => (thR_none hR (hcur t)).1, fun l hl => hR.mem l (fun t => curK_none (hcur t) l)
    (by simp [HdK, hhd]) hl, hR.am, hR.lview, fun c => pa_ruhig hR (hq c)⟩

/-- **The theorem of the S7 prototype.** For every race-free, lock- and mask-disciplined fragment program with the
    DMA typestate (`Disc P`):
    1. `I` is determined by its named choice points and never blocked (`I.Bestimmt`, `I.Fortschritt`) in every
       reachable ideal state;
    2. every finite implementation run has a run of `I` with the same answers per context, up to the pending
       answers of running units, which are none between units;
    3. every infinite implementation run has ONE ideal run, built along the run: every implementation step is a
       stutter of `I` or ONE step of `I` by the same context; per context the answers are the same up to the
       pending ones; and in every stretch in which a thread or the handler takes no ideal step it takes at most
       `maxLen P + 1` implementation steps (bounded stutter). -/
theorem s7_prototyp (P : Prog) (hD : Disc P) :
    (∀ itr i, IStar P (IS.init P) itr i →
      (∀ c as w i₁ i₂, IStep P i c as w i₁ → IStep P i c as w i₂ → i₁ = i₂) ∧
      (∀ t, (i.th t).prog ≠ [] → ∃ as w i', IStep P i (.thr t) as w i') ∧
      (∃ as w i', IStep P i .irq as w i')) ∧
    (∀ tr s, SStar P (S.init P) tr s →
      ∃ itr i pa, IStar P (IS.init P) itr i ∧ R P s i pa ∧ (∀ c, antS c tr = antI c itr ++ pa c) ∧
        ∀ c, Rest s c = 0 → pa c = []) ∧
    (∀ L : Lauf P,
      (ideal hD L 0) = (IS.init P, fun _ => []) ∧
      (∀ n, R P (L.st n) (ideal hD L n).1 (ideal hD L n).2 ∧
        Folgt P (L.st (n + 1)) (L.ctx n) (L.ans n) (ideal hD L n) (ideal hD L (n + 1)) ∧
        ∀ c, L.antS c n = antIdeal hD L c n ++ (ideal hD L n).2 c) ∧
      ∀ c, c ≠ .dma → ∀ n m, (∀ j, j < m → L.ctx (n + j) = c → Rest (L.st (n + j + 1)) c ≠ 0) →
        ((List.range m).filter fun j => decide (L.ctx (n + j) = c)).length ≤ maxLen P + 1) := by
  refine ⟨fun itr i hI => ?_, fun tr s h => ?_, fun L => ⟨rfl, fun n => ⟨ideal_r hD L n, ideal_folgt hD L n,
    fun c => ideal_ant hD L c n⟩, fun c hd n m hno => ideal_stotter_schranke hD L c hd n m hno⟩⟩
  · have hinv := iInv_star (iInv_init P (progOk_ohneMask _ _ (hD.1 1))) hI
    exact ⟨fun _ _ _ _ _ h₁ h₂ => iStep_bestimmt hinv.1 h₁ h₂, iStep_fortschritt P hinv, iStep_irq P i⟩
  · obtain ⟨itr, i, pa, hI, hR, hA⟩ := sim_star hD h
    exact ⟨itr, i, pa, hI, hR, hA, fun c hc => pa_ruhig hR hc⟩

end Gabbro.Grammatik.Zielsatz.Ideal.Prototyp
