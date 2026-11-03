/- Full consuming-loop composition on the canonical semantic fuel. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Tail
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Runtime
@[expose] public section

namespace Gabbro.Stage0.Senke.Consuming.Loop
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {P : Programm D} {f : D.Fn}
variable {reserved : Nat} {x : Image L P f reserved} {Γ : Ctx} {Λ : List (Res D)}
variable (q : Loop x Γ Λ)

/-- Compose a completed body with its post-measure check and actual backedge
    or checked leave. The source body supplies both protected control words. -/
theorem resume {m : Mem} {σ : World D} {ρ : Env D (.index (D.count x.table) :: Γ)}
    {n : Nat} {old : Int} (leaving : Bool)
    (ready : x.Ready m σ ρ) (fuelBound : n ≤ x.fuel)
    (oldBound : -2 ^ 63 ≤ old ∧ old < 2 ^ 63)
    (fuelRead : x.read m x.counter (BitVec.ofNat 64 n))
    (savedRead : x.read m x.saved (BitVec.ofInt 64 old))
    (σ' : World D) (ρ' : Env D (.index (D.count x.table) :: Γ))
    (body : Reach L x.fp x.lo x.K (x.s :: x.counter :: x.saved :: x.pr)
      ⟨x.addr 39, x.fp⟩ m (if leaving then x.addr 44 else x.addr 41) σ' ρ' reserved) :
    let measured := q.massW σ' ρ'.tail
    if 0 ≤ measured.2 ∧ measured.2 ≤ x.bound ∧ measured.2 < old then
      if leaving then
        if (q.invW measured.1 ρ'.tail).2 = true then
          Reach L x.fp x.lo x.K x.pr ⟨x.addr 39, x.fp⟩ m (x.addr 50)
            (q.invW measured.1 ρ'.tail).1 ρ'.tail reserved
        else Stops ⟨x.addr 39, x.fp⟩ m (logikCode (D := D) .schleife)
      else ∃ m', Star ⟨x.addr 39, x.fp⟩ m ⟨x.addr 2, x.fp⟩ m' ∧
        AgreeW L x.fp x.lo x.K m m' ∧ Keeps x.fp x.pr m m' ∧ q.Entry n m' measured.1 ρ'.tail
    else Stops ⟨x.addr 39, x.fp⟩ m (logikCode (D := D) .schleife) := by
  have body' : Reach L x.fp x.lo x.K (x.counter :: x.saved :: x.pr)
      ⟨x.addr 39, x.fp⟩ m (if leaving then x.addr 44 else x.addr 41) σ' ρ' reserved := by
    obtain ⟨mem, path, frame, env, world, kept⟩ := body
    exact ⟨mem, path, frame, env, world, fun j hj => kept j (by simp [hj])⟩
  obtain ⟨m1, bodyRun, bodyFrame, bodyEnv, bodyWorld, bodyKept, fuelRead1, savedRead1⟩ :=
    body_control_words body' fuelRead savedRead
  have ready1 := ready.body bodyFrame (envAt_tail bodyEnv) bodyWorld
  let i := if leaving then 44 else 41
  have which : i = 41 ∨ i = 44 := by cases leaving <;> simp [i]
  have checked := q.after_body i which old oldBound ready1 fuelRead1 savedRead1
  dsimp only
  by_cases good : 0 ≤ (q.massW σ' ρ'.tail).2 ∧ (q.massW σ' ρ'.tail).2 ≤ x.bound ∧
      (q.massW σ' ρ'.tail).2 < old
  · simp only [good, ↓reduceIte] at checked ⊢
    obtain ⟨m2, checkRun, checkFrame, checkKept, ready2, fuelRead2⟩ := checked
    have frame := bodyFrame.trans checkFrame
    have kept := bodyKept.trans checkKept
    cases leaving with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have jump := ready2.jump 42 2 .header rfl (by consume_arith x)
        (by consume_arith x) (by consume_arith x)
      exact ⟨m2, bodyRun.trans (checkRun.trans jump), frame, kept, ready2, fuelRead2, fuelBound⟩
    | true =>
      simp only [↓reduceIte]
      have exit := q.leave_invariant ready2
      by_cases valid : (q.invW (q.massW σ' ρ'.tail).1 ρ'.tail).2 = true
      · simp only [valid, ↓reduceIte] at exit ⊢
        exact Reach.prefix (bodyRun.trans checkRun) frame kept exit
      · simp only [valid, ↓reduceIte] at exit ⊢
        exact Stops.prefix (bodyRun.trans checkRun) exit
  · simp only [good, ↓reduceIte] at checked ⊢
    exact Stops.prefix bodyRun checked

/-- Fuel induction is supplied by runtime, with every premise instantiated by
    concrete assembled-image paths. No source interpreter or per-program premise. -/
theorem correct {O : Orakel D} {passes : Nat}
    {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {body : Block D (vertragVon D f) true (.index (D.count x.table) :: Γ) Λ Λ}
    {l : Bool} {outerLeave outerNext : W}
    (bodyRun : ∀ m σ ρ, x.Ready m σ ρ →
      Sim L P f x.σ0 x.ρ0 x.rp x.cfp x.fp x.lo x.K
        (x.s :: x.counter :: x.saved :: x.pr) ⟨x.addr 39, x.fp⟩ m
        (x.addr 41) (x.addr 44) (x.addr 41) (execBlock O passes R body σ ρ) reserved) :
    ∀ n m σ ρ, q.Entry n m σ ρ →
      Sim L P f x.σ0 x.ρ0 x.rp x.cfp x.fp x.lo x.K x.pr ⟨x.addr 2, x.fp⟩ m
        (x.addr 50) outerLeave outerNext
        (verbrauchLauf (l := l) x.table (fun σ ρ => execBlock O passes R body σ ρ)
          q.invW q.sel q.massW x.bound n σ ρ) reserved := by
  apply runtime x.table (fun σ ρ => execBlock O passes R body σ ρ)
    q.invW q.sel q.massW x.bound q.Entry x.low
  · intro mem σ ρ entry
    exact q.zero entry
  · intro n mem σ ρ entry invalid
    have head := q.head entry
    simpa only [invalid, ↓reduceIte] using head
  · intro n mem σ ρ σr entry valid selection
    obtain ⟨m1, scan, frame, kept, result, fuelRead⟩ := q.round entry valid
    rw [selection] at scan result
    simp only [Option.isSome_none, ↓reduceIte] at scan
    have branch := result.ready.branch 34 50 (x.s + 2) .done 0 rfl (by consume_arith x)
      (by consume_arith x) (by consume_arith x)
      (by have := x.scratch; have := x.layout.ks; omega) result.liveRead (by consume_arith x)
    exact ⟨m1, scan.trans (by simpa using branch), frame, result.ready.env,
      result.ready.world, kept⟩
  · intro n mem σ ρ σr entry valid selection
    obtain ⟨m1, scan, frame, kept, result, fuelRead⟩ := q.round entry valid
    rw [selection] at scan result
    simp only [Option.isSome_none, ↓reduceIte] at scan
    have branch := result.ready.branch 34 50 (x.s + 2) .done 1 rfl (by consume_arith x)
      (by consume_arith x) (by consume_arith x)
      (by have := x.scratch; have := x.layout.ks; omega) result.liveRead (by consume_arith x)
    have jump := result.ready.jump 35 49 .stop rfl (by consume_arith x)
      (by consume_arith x) (by consume_arith x)
    exact Stops.prefix (scan.trans ((by simpa using branch).trans jump)) result.ready.stop
  · intro n mem σ ρ σr k live entry valid selection
    obtain ⟨m1, scan, scanFrame, scanKept, selected, fuelRead⟩ := q.round entry valid
    rw [selection] at scan selected
    simp only [Option.isSome_some, ↓reduceIte] at scan
    obtain ⟨m2, measureRun, measureFrame, measureKept, ready2, fuelRead2, savedRead⟩ :=
      q.before_body k selected fuelRead
    have prefix := scan.trans measureRun
    have prefixFrame := scanFrame.trans measureFrame
    have prefixKept := scanKept.trans measureKept
    have oldBounds := q.measure_bounds σr ρ
    have oldBound := inW_spec x.bounds.2.2.2 oldBounds.1 oldBounds.2
    have pass := bodyRun m2 (q.massW σr ρ).1 (.cons k ρ) ready2
    dsimp only
    have again : ∀ σ' ρ',
        Reach L x.fp x.lo x.K (x.s :: x.counter :: x.saved :: x.pr)
          ⟨x.addr 39, x.fp⟩ m2 (x.addr 41) σ' ρ' reserved →
        let measured := q.massW σ' ρ'.tail
        if 0 ≤ measured.2 ∧ measured.2 ≤ x.bound ∧ measured.2 < (q.massW σr ρ).2 then
          ∃ m', Star ⟨x.addr 2, x.fp⟩ mem ⟨x.addr 2, x.fp⟩ m' ∧
            AgreeW L x.fp x.lo x.K mem m' ∧ Keeps x.fp x.pr mem m' ∧
            q.Entry n m' measured.1 ρ'.tail
        else Stops ⟨x.addr 2, x.fp⟩ mem (logikCode (D := D) .schleife) := by
      intro σ' ρ' body
      have resumed := q.resume false ready2 (by have := entry.2.2; omega)
        oldBound fuelRead2 savedRead σ' ρ' body
      dsimp only at resumed ⊢
      split at resumed ⊢
      · obtain ⟨m3, run, frame, kept, next⟩ := resumed
        exact ⟨m3, prefix.trans run, prefixFrame.trans frame, prefixKept.trans kept, next⟩
      · exact Stops.prefix prefix resumed
    generalize bodyOutcome : execBlock O passes R body (q.massW σr ρ).1 (.cons k ρ) = outcome at pass ⊢
    cases outcome with
    | ok σ' ρ' => exact again σ' ρ' pass
    | next _ σ' ρ' => exact again σ' ρ' pass
    | leave _ σ' ρ' =>
      have resumed := q.resume true ready2 (by have := entry.2.2; omega)
        oldBound fuelRead2 savedRead σ' ρ' pass
      dsimp only at resumed ⊢
      split at resumed ⊢
      · split at resumed ⊢
        · exact Reach.prefix prefix prefixFrame prefixKept resumed
        · exact Stops.prefix prefix resumed
      · exact Stops.prefix prefix resumed
    | zurueck σ' value => exact RetZ.prefix prefix (prefixFrame.mono (by have := x.low; simp [FB] at *; omega)) pass
    | why σ' reason => exact RetWhy.prefix prefix (prefixFrame.mono (by have := x.low; simp [FB] at *; omega)) pass
    | logik code => exact Stops.prefix prefix pass
    | hardware code => exact Stops.prefix prefix pass

end Gabbro.Stage0.Senke.Consuming.Loop
