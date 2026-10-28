import Grammatik.Code.Model.Step

/-
  File:      Grammatik/Code/Model/Facts.lean
  Subject:   TRACK L, PHASE L0 -- FACTS ABOUT THE SEMANTICS the lowering proofs build on.

    * `Stretch`, `seqI`, `reach_seq` -- a stretch of straight-line code found in a block runs in
      one `Reach`, and what it does to memory and registers is `seqI`, a plain function;
    * `reach_jmp`, `reach_br_true/false`, `reach_ret` -- the terminators as `Reach` lemmas;
    * `step_sc_det` -- under sequential consistency (`Sees.sc`) and without opaque instructions
      the step relation is a partial FUNCTION (deterministic);
    * the executable side: `Oracle.sc`, `exec`, `exec_reach` -- running the module under the SC
      oracle gives a `Reach`, which is what lets the witness be computed by `decide`.
-/

namespace Gabbro.Code

variable [Conf]

/-! ## 1. Straight-line code -/

/-- Run the straight-line instructions in sequence. -/
def seqI : List Instr → Mem → Regs → Option (Mem × Regs)
  | [], m, rs => some (m, rs)
  | i :: is, m, rs =>
      match stepI i m rs with
      | some (m', rs') => seqI is m' rs'
      | none => none

/-- `code` is the stretch of the body of block `l` of function `fn` that starts at index `pc`. -/
def Stretch (M : Modl) (fn : Nat) (l : Lbl) (pc : Nat) (code : List Instr) : Prop :=
  ∃ blk, M.blk fn l = some blk ∧ ∀ i (h : i < code.length), blk.body[pc + i]? = some code[i]

/-- The two instruction forms `step` handles outside `stepI`. -/
def Instr.special : Instr → Bool
  | .call .. | .aload .. => true
  | _ => false

theorem stepI_plain {i : Instr} {m : Mem} {rs : Regs} {r : Mem × Regs}
    (h : stepI i m rs = some r) : i.special = false := by
  cases i <;> simp_all [stepI, Instr.special]

theorem Instr.oracular_of_plain {i : Instr} (h : i.special = false) : i.oracular = false := by
  cases i <;> simp_all [Instr.special, Instr.oracular]

/-- The oracle is not consulted at a plain instruction or at a terminator. -/
theorem legal_of_not_oracular (S : Sees) (M : Modl) (O : Oracle) (c : Cfg)
    (h : ∀ i, Cfg.nextI M c = some i → i.oracular = false) : O.legal S M c := by
  cases c with
  | fin m v => trivial
  | run m f ks =>
      unfold Oracle.legal
      cases hn : Cfg.nextI M (.run m f ks) with
      | none => simp only [hn]
      | some i =>
          have := h i hn
          cases i <;> simp_all [Instr.oracular]

/-- **One plain instruction is one step.** -/
theorem step_plain {M : Modl} {S : Sees} {f : Frame} {blk : Block} {i : Instr} {m m' : Mem}
    {rs' : Regs} (ks : List Frame) (hb : M.blk f.fn f.lbl = some blk) (hi : blk.body[f.pc]? = some i)
    (hs : stepI i m f.regs = some (m', rs')) :
    Step M S (.run m f ks) (.run m' { f with regs := rs', pc := f.pc + 1 } ks) := by
  have hp := stepI_plain hs
  have hnext : Cfg.nextI M (.run m f ks) = some i := by simp only [Cfg.nextI, hb, Option.bind_some, hi]
  refine ⟨⟨fun _ _ _ _ _ => none⟩,
    legal_of_not_oracular S M _ _ ?_, ?_⟩
  · intro j hj
    rw [hnext] at hj
    cases hj
    exact Instr.oracular_of_plain hp
  · cases i <;> simp_all [step, stepI, Instr.special]

/-- **Straight-line code is one `Reach`.** -/
theorem reach_seq (M : Modl) (S : Sees) :
    ∀ (code : List Instr) (m : Mem) (f : Frame) (ks : List Frame) (m' : Mem) (rs' : Regs),
      Stretch M f.fn f.lbl f.pc code → seqI code m f.regs = some (m', rs') →
      Reach M S (.run m f ks) (.run m' { f with regs := rs', pc := f.pc + code.length } ks) := by
  intro code
  induction code with
  | nil =>
      intro m f ks m' rs' _ h
      simp only [seqI, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.length_nil, Nat.add_zero]
      exact .refl _
  | cons i is ih =>
      intro m f ks m' rs' hc h
      obtain ⟨blk, hb, hcode⟩ := hc
      simp only [seqI] at h
      cases hs : stepI i m f.regs with
      | none => simp only [hs, reduceCtorEq] at h
      | some r =>
          simp only [hs] at h
          have hi : blk.body[f.pc]? = some i := by
            have := hcode 0 (by simp only [List.length_cons, Nat.zero_lt_succ])
            simpa using this
          have h1 := step_plain (S := S) ks hb hi hs
          have h2 := ih r.1 { f with regs := r.2, pc := f.pc + 1 } ks m' rs'
            ⟨blk, hb, fun j hj => by
              have := hcode (j + 1) (by simp only [List.length_cons, Nat.add_lt_add_iff_right]; omega)
              simpa [Nat.add_assoc, Nat.add_comm 1 j] using this⟩ h
          have h3 := Reach.trans (Reach.one h1) h2
          have e : f.pc + 1 + is.length = f.pc + (i :: is).length := by simp only [List.length_cons]; omega
          simpa only [e] using h3

/-! ## 2. Terminators -/

/-- The terminator of the block of `f` (`f` stands at the end of the body). -/
def Frame.atTerm (M : Modl) (f : Frame) (t : Term) (blk : Block) : Prop :=
  M.blk f.fn f.lbl = some blk ∧ blk.body.length ≤ f.pc ∧ blk.term = t

theorem step_term {M : Modl} {S : Sees} {f : Frame} {t : Term} {blk : Block} {m : Mem}
    {ks : List Frame} {c : Cfg} (h : Frame.atTerm M f t blk) (hs : stepTerm M t m f ks = some c) :
    Step M S (.run m f ks) c := by
  obtain ⟨hb, hl, ht⟩ := h
  have hnone : blk.body[f.pc]? = none := by simp only [Nat.not_lt, hl, getElem?_neg]
  refine ⟨⟨fun _ _ _ _ _ => none⟩,
    legal_of_not_oracular S M _ _ ?_, ?_⟩
  · intro j hj
    simp only [Cfg.nextI, hb, Option.bind_some, hnone, reduceCtorEq] at hj
  · simp only [step, hb, hnone]
    rw [← ht] at hs
    exact hs

/-- A block with no phis is entered with its registers unchanged. -/
theorem enter_nophi {M : Modl} {f : Frame} {l : Lbl} {blk : Block} (hb : M.blk f.fn l = some blk)
    (hp : blk.phis = []) : f.enter M l = some { f with lbl := l, pc := 0 } := by
  simp only [Frame.enter, hb, hp, List.mapM_nil, Option.pure_def, List.foldl_nil]

theorem reach_jmp {M : Modl} {S : Sees} {f : Frame} {l : Lbl} {blk blk' : Block} {m : Mem}
    {ks : List Frame} (h : Frame.atTerm M f (.jmp l) blk) (hb : M.blk f.fn l = some blk')
    (hp : blk'.phis = []) :
    Reach M S (.run m f ks) (.run m { f with lbl := l, pc := 0 } ks) :=
  Reach.one (step_term h (by simp only [stepTerm, enter_nophi hb hp, Option.map_some]))

theorem reach_br {M : Modl} {S : Sees} {f : Frame} {c : Opd} {t e : Lbl} {blk blk' : Block}
    {m : Mem} {ks : List Frame} {x : BitVec 1} (h : Frame.atTerm M f (.br c t e) blk)
    (hc : c.ev f.regs = some (.int 1 x)) (hb : M.blk f.fn (if x = 1 then t else e) = some blk')
    (hp : blk'.phis = []) :
    Reach M S (.run m f ks) (.run m { f with lbl := (if x = 1 then t else e), pc := 0 } ks) :=
  Reach.one (step_term h (by
    have he := enter_nophi hb hp
    simp only [stepTerm, hc, he, Option.map_some]))

/-- `ret v` with the register file of `f`: with no caller it finishes the run. -/
theorem reach_ret_top {M : Modl} {S : Sees} {f : Frame} {o : Opd} {blk : Block} {m : Mem}
    {v : Val} (h : Frame.atTerm M f (.ret (some o)) blk) (hv : o.ev f.regs = some v) :
    Reach M S (.run m f []) (.fin m (some v)) :=
  Reach.one (step_term h (by simp only [stepTerm, hv, finish]))

/-! ## 3. Determinism under sequential consistency -/

/-- Under `Sees.sc` an oracle's atomic load answer is the memory's: so a legal oracle can be
    replaced by the one that reads memory. -/
def Oracle.mem : Oracle := ⟨fun m b o t _ => m.load b o t⟩

theorem step_sc_oracle (M : Modl) (O : Oracle) (c c' : Cfg) (hl : O.legal Sees.sc M c)
    (h : step M O c = some c') : step M Oracle.mem c = some c' := by
  cases c with
  | fin m v => simp only [step, reduceCtorEq] at h
  | run m f ks =>
      simp only [step] at h ⊢
      cases hb : M.blk f.fn f.lbl with
      | none => simp only [hb, reduceCtorEq] at h
      | some blk =>
          simp only [hb] at h ⊢
          cases hi : blk.body[f.pc]? with
          | none => simpa [hi] using h
          | some ins =>
              simp only [hi] at h ⊢
              cases ins with
              | aload d t p ord =>
                  simp only at h ⊢
                  cases hp : p.ev f.regs with
                  | none => simp only [hp, reduceCtorEq] at h
                  | some pv =>
                      cases pv with
                      | int w x => simp only [hp, reduceCtorEq] at h
                      | flt g => simp only [hp, reduceCtorEq] at h
                      | dbl g => simp only [hp, reduceCtorEq] at h
                      | ptr b o =>
                          simp only [hp] at h ⊢
                          split at h
                          · rename_i hal
                            cases hld : O.ld m b o t ord with
                            | none => simp only [hld, reduceCtorEq] at h
                            | some v =>
                                have hleg : Sees.sc m b o t ord v := by
                                  have := hl
                                  simp only [Oracle.legal, Cfg.nextI, hb, hi, Option.bind_some] at this
                                  exact this b o v hp hld
                                have : m.load b o t = some v := hleg
                                simp only [hld] at h
                                simp only [Oracle.mem, hal, this]
                                exact h
                          · simp only [reduceCtorEq] at h
              | _ => simpa [step] using h

/-- **Determinism.** Under sequential consistency, with no opaque instruction next, the step
    relation is a partial function. -/
theorem step_sc_det {M : Modl} {c c' c'' : Cfg}
    (h1 : Step M Sees.sc c c') (h2 : Step M Sees.sc c c'') : c' = c'' := by
  obtain ⟨O, hl, hs⟩ := h1
  obtain ⟨O', hl', hs'⟩ := h2
  have a := step_sc_oracle M O c c' hl hs
  have b := step_sc_oracle M O' c c'' hl' hs'
  rw [a] at b
  exact Option.some.inj b

/-! ## 4. Running a module: the executable side -/

/-- Run at most `n` steps under the memory oracle; stop where the run is stuck or finished. -/
def exec (M : Modl) : Nat → Cfg → Cfg
  | 0, c => c
  | n + 1, c =>
      match step M Oracle.mem c with
      | some c' => exec M n c'
      | none => c

theorem exec_reach {M : Modl} : ∀ (n : Nat) (c : Cfg), Reach M Sees.sc c (exec M n c) := by
  intro n
  induction n with
  | zero => intro c; exact .refl c
  | succ n ih =>
      intro c
      simp only [exec]
      cases hs : step M Oracle.mem c with
      | none => exact .refl c
      | some c' =>
          refine .step c c' _ ⟨Oracle.mem, ?_, hs⟩ (ih c')
          cases c with
          | fin m v => trivial
          | run m f ks =>
              unfold Oracle.legal
              cases hn : Cfg.nextI M (.run m f ks) with
              | none => simp only [hn]
              | some i =>
                  cases i with
                  | aload d t p ord =>
                      simp only [hn]
                      intro b o v _ hv
                      exact hv
                  | _ => simp only [hn]

end Gabbro.Code
