/- Fuel induction for the canonical consuming semantics. Concrete instruction
   simulations must supply every header, selector and post-body premise. -/
module
public import Stage0.Senke.Anweisung.Simulation
@[expose] public section

namespace Gabbro.Stage0.Senke.Consuming
open Gabbro.Grammatik Runner Runner.IR

variable [Kern]

/-- Compose concrete consuming-loop edges into the canonical `verbrauchLauf`.
    Entry carries the represented state at the emitted header. A continuing
    body pass must execute the post-measure checks and the actual backedge,
    and provide the smaller-fuel entry. The leave arm checks the post-body
    measure and invariant before reaching the exit. Returns and failures
    retain their ordinary statement simulation.

    This theorem is a composition lemma, not an admission theorem: the
    instruction-level header/scan/post-body simulations are separate duties. -/
theorem runtime {D : Deklaration} {L : Lay D} {P : Programm D} {f : D.Fn}
    {Γ : Ctx} {l : Bool} {reserved : Nat}
    {σ0 : World D} {ρ0 : Env D (D.params f)}
    {rp cfp fp pc exit outerLeave outerNext : W} {lo K : Nat} {pr : List Nat}
    (t : D.Tab)
    (body : World D → Env D (.index (D.count t) :: Γ) →
      Ausgang (vertragVon D f) true (.index (D.count t) :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (sel : World D → Env D Γ →
      World D × Option (Wert D (.index (D.count t))) × Bool)
    (massW : World D → Env D Γ → World D × Int) (bound : Int)
    (entry : Nat → Mem → World D → Env D Γ → Prop)
    (lower : FB ≤ lo)
    (zero : ∀ m σ ρ, entry 0 m σ ρ →
      Stops ⟨pc, fp⟩ m (logikCode (D := D) .schleife))
    (invalid : ∀ n m σ ρ, entry (n + 1) m σ ρ →
      (inv σ ρ).2 = false → Stops ⟨pc, fp⟩ m (logikCode (D := D) .schleife))
    (empty : ∀ n m σ ρ σr, entry (n + 1) m σ ρ →
      (inv σ ρ).2 ≠ false → sel (inv σ ρ).1 ρ = (σr, none, false) →
      Reach L fp lo K pr ⟨pc, fp⟩ m exit σr ρ reserved)
    (cycle : ∀ n m σ ρ σr, entry (n + 1) m σ ρ →
      (inv σ ρ).2 ≠ false → sel (inv σ ρ).1 ρ = (σr, none, true) →
      Stops ⟨pc, fp⟩ m (logikCode (D := D) .schleife))
    (selected : ∀ n m σ ρ σr k live, entry (n + 1) m σ ρ →
      (inv σ ρ).2 ≠ false → sel (inv σ ρ).1 ρ = (σr, some k, live) →
      let (σm, old) := massW σr ρ
      match body σm (.cons k ρ) with
      | .ok σ' ρ' | .next _ σ' ρ' =>
        let (σm', new) := massW σ' ρ'.tail
        if 0 ≤ new ∧ new ≤ bound ∧ new < old then
          ∃ m', Star ⟨pc, fp⟩ m ⟨pc, fp⟩ m' ∧ AgreeW L fp lo K m m' ∧
            Keeps fp pr m m' ∧ entry n m' σm' ρ'.tail
        else Stops ⟨pc, fp⟩ m (logikCode (D := D) .schleife)
      | .leave _ σ' ρ' =>
        let (σm', new) := massW σ' ρ'.tail
        if 0 ≤ new ∧ new ≤ bound ∧ new < old then
          if (inv σm' ρ'.tail).2 = true then
            Reach L fp lo K pr ⟨pc, fp⟩ m exit (inv σm' ρ'.tail).1 ρ'.tail reserved
          else Stops ⟨pc, fp⟩ m (logikCode (D := D) .schleife)
        else Stops ⟨pc, fp⟩ m (logikCode (D := D) .schleife)
      | .zurueck σ' v => RetZ L P f σ0 ρ0 fp K rp cfp ⟨pc, fp⟩ m σ' v
      | .why σ' r => RetWhy L f fp K rp cfp ⟨pc, fp⟩ m σ' r
      | .logik e => Stops ⟨pc, fp⟩ m (logikCode e)
      | .hardware e => Stops ⟨pc, fp⟩ m (hwCode e)) :
    ∀ n m σ ρ, entry n m σ ρ →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m exit outerLeave outerNext
        (verbrauchLauf (l := l) t body inv sel massW bound n σ ρ) reserved := by
  intro n
  induction n with
  | zero =>
    intro m σ ρ he
    exact zero m σ ρ he
  | succ n ih =>
    intro m σ ρ he
    simp only [verbrauchLauf]
    by_cases hi : (inv σ ρ).2 = false
    · simp only [hi, ↓reduceIte]
      exact invalid n m σ ρ he hi
    · simp only [hi, Bool.true_eq_false, ↓reduceIte]
      generalize hs : sel (inv σ ρ).1 ρ = selection
      rcases selection with ⟨σr, choice, live⟩
      cases choice with
      | none =>
        cases live with
        | false => exact empty n m σ ρ σr he hi hs
        | true => exact cycle n m σ ρ σr he hi hs
      | some k =>
        have pass := selected n m σ ρ σr k live he hi hs
        generalize hm : massW σr ρ = measured at pass ⊢
        rcases measured with ⟨σm, old⟩
        dsimp only at pass ⊢
        have again : ∀ σ' ρ',
            (∃ m', Star ⟨pc, fp⟩ m ⟨pc, fp⟩ m' ∧ AgreeW L fp lo K m m' ∧
              Keeps fp pr m m' ∧ entry n m' σ' ρ') →
            Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m exit outerLeave outerNext
              (verbrauchLauf (l := l) t body inv sel massW bound n σ' ρ') reserved := by
          intro σ' ρ' continuation
          obtain ⟨m', run, frame, kept, next⟩ := continuation
          exact Sim.prefix lower run frame kept (ih m' σ' ρ' next)
        generalize hb : body σm (.cons k ρ) = outcome at pass ⊢
        cases outcome with
        | ok σ' ρ' =>
          generalize hnew : massW σ' ρ'.tail = measured' at pass ⊢
          rcases measured' with ⟨σm', new⟩
          dsimp only at pass ⊢
          by_cases good : 0 ≤ new ∧ new ≤ bound ∧ new < old
          · have next := again σm' ρ'.tail (by simpa only [good, ↓reduceIte] using pass)
            simpa only [hm, hb, hnew, good, ↓reduceIte] using next
          · have stopped : Stops ⟨pc, fp⟩ m (logikCode (D := D) .schleife) := by
              simpa only [good, ↓reduceIte] using pass
            simpa only [hm, hb, hnew, good, ↓reduceIte, Sim] using stopped
        | next h σ' ρ' =>
          generalize hnew : massW σ' ρ'.tail = measured' at pass ⊢
          rcases measured' with ⟨σm', new⟩
          dsimp only at pass ⊢
          by_cases good : 0 ≤ new ∧ new ≤ bound ∧ new < old
          · have next := again σm' ρ'.tail (by simpa only [good, ↓reduceIte] using pass)
            simpa only [hm, hb, hnew, good, ↓reduceIte] using next
          · have stopped : Stops ⟨pc, fp⟩ m (logikCode (D := D) .schleife) := by
              simpa only [good, ↓reduceIte] using pass
            simpa only [hm, hb, hnew, good, ↓reduceIte, Sim] using stopped
        | leave h σ' ρ' =>
          generalize hnew : massW σ' ρ'.tail = measured' at pass ⊢
          rcases measured' with ⟨σm', new⟩
          dsimp only at pass ⊢
          by_cases good : 0 ≤ new ∧ new ≤ bound ∧ new < old
          · by_cases valid : (inv σm' ρ'.tail).2 = true
            · have left : Reach L fp lo K pr ⟨pc, fp⟩ m exit
                  (inv σm' ρ'.tail).1 ρ'.tail reserved := by
                simpa only [good, valid, ↓reduceIte] using pass
              simpa only [hm, hb, hnew, good, valid, ↓reduceIte, Sim] using left
            · have stopped : Stops ⟨pc, fp⟩ m (logikCode (D := D) .schleife) := by
                simpa only [good, valid, ↓reduceIte] using pass
              simpa only [hm, hb, hnew, good, valid, ↓reduceIte, Sim] using stopped
          · have stopped : Stops ⟨pc, fp⟩ m (logikCode (D := D) .schleife) := by
              simpa only [good, ↓reduceIte] using pass
            simpa only [hm, hb, hnew, good, ↓reduceIte, Sim] using stopped
        | zurueck σ' value =>
          simpa only [hm, hb, Bool.true_eq_false, ↓reduceIte, Sim] using pass
        | why σ' reason =>
          simpa only [hm, hb, Bool.true_eq_false, ↓reduceIte, Sim] using pass
        | logik error =>
          simpa only [hm, hb, Bool.true_eq_false, ↓reduceIte, Sim] using pass
        | hardware error =>
          simpa only [hm, hb, Bool.true_eq_false, ↓reduceIte, Sim] using pass

end Gabbro.Stage0.Senke.Consuming
