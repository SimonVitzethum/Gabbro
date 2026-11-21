module

public import Runner.Mach.Maschine

@[expose] public section

namespace Runner.Mach

/-- Continuing transitions of the process. Each is a recursive case of
    `Tr` with its successor configuration retained. Terminal observations
    are still governed by `Tr`. -/
inductive ProcessStep (M : MemSys) (act : θ → Res θ) :
    Cfg M θ → List Ev → Cfg M θ → Prop where
  | tau {c : Cfg M θ} {ms : M.St} :
      M.tau c.ms ms → ProcessStep M act c [] ⟨ms, c.ths⟩
  | priv {c : Cfg M θ} {i : Nat} {t t' : θ} :
      c.ths[i]? = some (some t) → act t = .next t' →
      ProcessStep M act c [] ⟨c.ms, c.ths.set i (some t')⟩
  | ask {c : Cfg M θ} {i : Nat} {t t' : θ} {o : Op} {k : Ans → Res θ} {a : Ans} {ms : M.St} :
      c.ths[i]? = some (some t) → act t = .ask o k → o.special = false → M.ans c.ms i o a ms →
      k a = .next t' → ProcessStep M act c (lbl i o a) ⟨ms, c.ths.set i (some t')⟩
  | exit {c : Cfg M θ} {i : Nat} {t : θ} {q : Req} {k : Ans → Res θ} :
      c.ths[i]? = some (some t) → act t = .ask (.sys q) k → q.nr.toNat = NR_EXIT →
      ProcessStep M act c [(i, q, none)] ⟨c.ms, c.ths.set i none⟩
  | cloneNo {c : Cfg M θ} {i : Nat} {t t' : θ} {k : Ans → Res θ} {a : Ans} {ms : M.St} :
      c.ths[i]? = some (some t) → act t = .ask (.sys cloneReq) k → M.ans c.ms i (.sys cloneReq) a ms →
      (∀ r w, a = some (r, w) → ¬ 0 < r.toInt) → k a = .next t' →
      ProcessStep M act c [(i, cloneReq, a)] ⟨ms, c.ths.set i (some t')⟩
  | clone {c : Cfg M θ} {i : Nat} {t t' tc : θ} {k : Ans → Res θ} {r w : W} {ms : M.St} :
      c.ths[i]? = some (some t) → act t = .ask (.sys cloneReq) k →
      M.ans c.ms i (.sys cloneReq) (some (r, w)) ms → 0 < r.toInt → k (some (r, w)) = .next t' →
      k (some (0, w)) = .next tc →
      ProcessStep M act c [(i, cloneReq, some (r, w))]
        ⟨ms, c.ths.set i (some t') ++ [some tc]⟩

/-- An observed process prefix with its endpoint and step count. -/
inductive ProcessPrefix (M : MemSys) (act : θ → Res θ) :
    Cfg M θ → List Ev → Nat → Cfg M θ → Prop where
  | nil (c : Cfg M θ) : ProcessPrefix M act c [] 0 c
  | cons : ProcessStep M act c events next →
      ProcessPrefix M act next rest steps final →
      ProcessPrefix M act c (events ++ rest) (steps + 1) final

variable {M : MemSys} {act : θ → Res θ}

theorem ProcessPrefix.ofStep {a b : Cfg M θ} {events : List Ev}
    (step : ProcessStep M act a events b) : ProcessPrefix M act a events 1 b := by
  simpa only [List.append_nil] using ProcessPrefix.cons step (.nil b)

theorem ProcessPrefix.trans {a b c : Cfg M θ} {first last : List Ev} {m n : Nat}
    (left : ProcessPrefix M act a first m b) (right : ProcessPrefix M act b last n c) :
    ProcessPrefix M act a (first ++ last) (n + m) c := by
  induction left with
  | nil => exact right
  | cons step _ ih =>
    simpa only [List.append_assoc, Nat.add_succ] using ProcessPrefix.cons step (ih right)

theorem ProcessStep.prepend {a b : Cfg M θ} {events rest : List Ev} {n : Nat} {endState : Ende}
    (step : ProcessStep M act a events b) (suffix : Tr M act b rest endState n) :
    Tr M act a (events ++ rest) endState (n + 1) := by
  cases step with
  | tau moved => exact .tau moved suffix
  | priv found executed => exact .priv found executed suffix
  | ask found asked ordinary answered resumed => exact .ask found asked ordinary answered resumed suffix
  | exit found asked number => exact .exit found asked number suffix
  | cloneNo found asked answered failed resumed => exact .cloneNo found asked answered failed resumed suffix
  | clone found asked answered created parent child => exact .clone found asked answered created parent child suffix

theorem ProcessPrefix.prepend {a b : Cfg M θ} {events rest : List Ev} {m n : Nat} {endState : Ende}
    (path : ProcessPrefix M act a events m b) (suffix : Tr M act b rest endState n) :
    Tr M act a (events ++ rest) endState (n + m) := by
  induction path with
  | nil => exact suffix
  | cons step _ ih =>
    simpa only [List.append_assoc, Nat.add_succ] using step.prepend (ih suffix)

theorem ende_ne_lauf (r : Res θ) : Res.ende r ≠ some .lauf := by
  cases r <;> simp [Res.ende]

theorem Tr.prefix {a : Cfg M θ} {events : List Ev} {n : Nat} (run : Tr M act a events .lauf n) :
    ∃ b, ProcessPrefix M act a events n b := by
  generalize ending : (Ende.lauf) = e at run
  induction run with
  | nil => exact ⟨_, .nil _⟩
  | tau moved _ ih => obtain ⟨_, path⟩ := ih ending; exact ⟨_, .cons (.tau moved) path⟩
  | priv found executed _ ih =>
    obtain ⟨_, path⟩ := ih ending; exact ⟨_, .cons (.priv found executed) path⟩
  | ask found asked ordinary answered resumed _ ih =>
    obtain ⟨_, path⟩ := ih ending; exact ⟨_, .cons (.ask found asked ordinary answered resumed) path⟩
  | exit found asked number _ ih =>
    obtain ⟨_, path⟩ := ih ending; exact ⟨_, .cons (.exit found asked number) path⟩
  | cloneNo found asked answered failed resumed _ ih =>
    obtain ⟨_, path⟩ := ih ending; exact ⟨_, .cons (.cloneNo found asked answered failed resumed) path⟩
  | clone found asked answered created parent child _ ih =>
    obtain ⟨_, path⟩ := ih ending; exact ⟨_, .cons (.clone found asked answered created parent child) path⟩
  | stop _ stopped | askStop _ _ _ _ stopped | cloneNoStop _ _ _ _ stopped =>
    rw [← ending] at stopped
    exact (ende_ne_lauf _ stopped).elim
  | exitGroup => cases ending

/-- Keeping an endpoint neither admits new continuing observations nor
    excludes any continuing observation of the runner. -/
theorem Tr.lauf_iff_prefix {a : Cfg M θ} {events : List Ev} {n : Nat} :
    Tr M act a events .lauf n ↔ ∃ b, ProcessPrefix M act a events n b := by
  refine ⟨Tr.prefix, ?_⟩
  rintro ⟨b, path⟩
  simpa only [List.append_nil, Nat.zero_add] using path.prepend (.nil b)

/-- A terminal trace has an actual last running configuration and one
    terminal observation there. The prefix carries every earlier event. -/
theorem Tr.split_stop {a : Cfg M θ} {events : List Ev} {ending : Ende} {n : Nat}
    (run : Tr M act a events ending n) (stopped : ending ≠ .lauf) :
    ∃ boundary earlier last steps,
      ProcessPrefix M act a earlier steps boundary ∧ Tr M act boundary last ending 1 ∧
      events = earlier ++ last ∧ n = steps + 1 := by
  have addStep {before after : Cfg M θ} {labels rest : List Ev} {e : Ende} {count : Nat}
      (step : ProcessStep M act before labels after)
      (split : ∃ boundary earlier last steps,
        ProcessPrefix M act after earlier steps boundary ∧ Tr M act boundary last e 1 ∧
        rest = earlier ++ last ∧ count = steps + 1) :
      ∃ boundary earlier last steps,
        ProcessPrefix M act before earlier steps boundary ∧ Tr M act boundary last e 1 ∧
        labels ++ rest = earlier ++ last ∧ count + 1 = steps + 1 := by
    obtain ⟨boundary, earlier, last, steps, run, stop, rfl, rfl⟩ := split
    exact ⟨boundary, labels ++ earlier, last, steps + 1, .cons step run, stop,
      (List.append_assoc _ _ _).symm, rfl⟩
  induction run with
  | nil => exact (stopped rfl).elim
  | tau moved _ ih => exact addStep (.tau moved) (ih stopped)
  | priv found executed _ ih => exact addStep (.priv found executed) (ih stopped)
  | ask found asked ordinary answered resumed _ ih =>
    exact addStep (.ask found asked ordinary answered resumed) (ih stopped)
  | exit found asked number _ ih => exact addStep (.exit found asked number) (ih stopped)
  | cloneNo found asked answered failed resumed _ ih =>
    exact addStep (.cloneNo found asked answered failed resumed) (ih stopped)
  | clone found asked answered created parent child _ ih =>
    exact addStep (.clone found asked answered created parent child) (ih stopped)
  | stop found done => exact ⟨_, [], _, 0, .nil _, .stop found done, rfl, rfl⟩
  | askStop found asked ordinary answered done =>
    exact ⟨_, [], _, 0, .nil _, .askStop found asked ordinary answered done, rfl, rfl⟩
  | cloneNoStop found asked answered failed done =>
    exact ⟨_, [], _, 0, .nil _, .cloneNoStop found asked answered failed done, rfl, rfl⟩
  | exitGroup found asked number =>
    exact ⟨_, [], _, 0, .nil _, .exitGroup found asked number, rfl, rfl⟩

end Runner.Mach
