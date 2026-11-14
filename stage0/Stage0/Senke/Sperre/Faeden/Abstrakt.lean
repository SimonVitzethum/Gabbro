/-
  File:      stage0/Stage0/Senke/Sperre/Faeden/Abstrakt.lean
  Subject:   THE ABSTRACT TICKET LOCK: a holder and the queue of the waiting threads in ticket order. Its three steps
             are those of the model's lock (Code/Conc/Lock.lean; proved in Faeden/Geist.lean against its
             ghost `Tkt`): `Zieht` (take a ticket: join the end of the queue), `Tritt` (the head of the queue takes
             the free lock), `Gibt` (the holder gives it). `Weg u a d` is what ONE step of machine G by thread `u`
             can do to one lock: give,
             then draw, then enter, each at most once and in this order (a G step that takes a lock does nothing
             else to it). `AbsOK` (the queue has no duplicate, the holder is not in it) holds along every such run.
             `Weg.kopf` and `Weg.ordnung` are the two facts the queue of a `FifoLauf` needs.
-/
module
@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

/-- **The abstract ticket lock**: the holder, and the waiting threads in ticket order. -/
structure Abs (τ : Type) where
  holder : Option τ
  queue : List τ
  deriving DecidableEq

variable {τ : Type}

/-- **Draw a ticket**: a thread neither waiting nor holding joins the end of the queue. -/
def Zieht (u : τ) (a b : Abs τ) : Prop :=
  u ∉ a.queue ∧ a.holder ≠ some u ∧ b = ⟨a.holder, a.queue ++ [u]⟩

/-- **Enter**: the lock is free and `u` heads the queue; `u` holds it and leaves the queue. -/
def Tritt (u : τ) (a b : Abs τ) : Prop :=
  a.holder = none ∧ a.queue.head? = some u ∧ b = ⟨some u, a.queue.tail⟩

/-- **Give**: the holder `u` frees the lock. -/
def Gibt (u : τ) (a b : Abs τ) : Prop :=
  a.holder = some u ∧ b = ⟨none, a.queue⟩

/-- One step of the abstract ticket lock by thread `u`. -/
inductive AbsSchritt (u : τ) (a b : Abs τ) : Prop where
  | zieht : Zieht u a b → AbsSchritt u a b
  | tritt : Tritt u a b → AbsSchritt u a b
  | gibt : Gibt u a b → AbsSchritt u a b

/-- At most one step of `r`. -/
def Opt (r : Abs τ → Abs τ → Prop) (a b : Abs τ) : Prop := a = b ∨ r a b

/-- **What one step of machine G by `u` does to one lock**: a give, a draw, an enter, each optional, in this order. -/
def Weg (u : τ) (a d : Abs τ) : Prop :=
  ∃ b c, Opt (Gibt u) a b ∧ Opt (Zieht u) b c ∧ Opt (Tritt u) c d

/-- The well-formed abstract states: no thread twice in the queue, the holder not in it. -/
structure AbsOK (a : Abs τ) : Prop where
  nodup : a.queue.Nodup
  frei : ∀ x, a.holder = some x → x ∉ a.queue

/-! ## 1. Well-formedness is kept -/

theorem Zieht.ok {u : τ} {a b : Abs τ} (h : Zieht u a b) (ha : AbsOK a) : AbsOK b := by
  obtain ⟨hu, hh, rfl⟩ := h
  refine ⟨?_, ?_⟩
  · show (a.queue ++ [u]).Nodup
    refine List.nodup_append.2 ⟨ha.nodup, by simp, ?_⟩
    intro x hx y hy hxy
    rw [List.mem_singleton] at hy
    rw [hxy, hy] at hx
    exact hu hx
  · show ∀ x, a.holder = some x → x ∉ a.queue ++ [u]
    intro x hx hmem
    rcases List.mem_append.1 hmem with h1 | h1
    · exact ha.frei x hx h1
    · rw [List.mem_singleton] at h1
      rw [h1] at hx
      exact hh hx

theorem Tritt.ok {u : τ} {a b : Abs τ} (h : Tritt u a b) (ha : AbsOK a) : AbsOK b := by
  obtain ⟨_, hq, rfl⟩ := h
  obtain ⟨r, hr⟩ := List.head?_eq_some_iff.1 hq
  have hn := ha.nodup
  rw [hr] at hn
  refine ⟨?_, ?_⟩
  · show a.queue.tail.Nodup
    rw [hr]
    exact (List.nodup_cons.1 hn).2
  · show ∀ x, some u = some x → x ∉ a.queue.tail
    intro x hx
    cases hx
    rw [hr]
    exact (List.nodup_cons.1 hn).1

theorem Gibt.ok {u : τ} {a b : Abs τ} (h : Gibt u a b) (ha : AbsOK a) : AbsOK b := by
  obtain ⟨_, rfl⟩ := h
  refine ⟨ha.nodup, ?_⟩
  show ∀ x, (none : Option τ) = some x → x ∉ a.queue
  intro x hx
  cases hx

theorem AbsSchritt.ok {u : τ} {a b : Abs τ} (h : AbsSchritt u a b) (ha : AbsOK a) : AbsOK b := by
  cases h with
  | zieht h => exact h.ok ha
  | tritt h => exact h.ok ha
  | gibt h => exact h.ok ha

theorem Opt.ok {r : Abs τ → Abs τ → Prop} (hr : ∀ a b, r a b → AbsOK a → AbsOK b) {a b : Abs τ}
    (h : Opt r a b) (ha : AbsOK a) : AbsOK b := by
  rcases h with h | h
  · rw [← h]; exact ha
  · exact hr a b h ha

theorem Weg.ok {u : τ} {a d : Abs τ} (h : Weg u a d) (ha : AbsOK a) : AbsOK d := by
  obtain ⟨b, c, h1, h2, h3⟩ := h
  have hb := Opt.ok (fun _ _ h ha => Gibt.ok h ha) h1 ha
  have hc := Opt.ok (fun _ _ h ha => Zieht.ok h ha) h2 hb
  exact Opt.ok (fun _ _ h ha => Tritt.ok h ha) h3 hc

/-! ## 2. Head and order -/

/-- **Only the head enters**: a waiting `u` that holds the lock after its step was the head of the queue. -/
theorem Weg.kopf {u : τ} {a d : Abs τ} (hw : Weg u a d) (ha : AbsOK a) (hu : u ∈ a.queue)
    (hd : d.holder = some u) : a.queue.head? = some u := by
  obtain ⟨b, c, h1, h2, h3⟩ := hw
  have hb : a = b := by
    rcases h1 with h | ⟨hh, _⟩
    · exact h
    · exact absurd hu (ha.frei u hh)
  have hc : b = c := by
    rcases h2 with h | ⟨hn, _, _⟩
    · exact h
    · exact absurd (by rw [← hb]; exact hu) hn
  rcases h3 with h | ⟨_, hq, _⟩
  · rw [← h, ← hc, ← hb] at hd
    exact absurd hu (ha.frei u hd)
  · rw [hb, hc]
    exact hq

/-- **First come, first served**: the threads of the queue that are still in it after a step keep their order,
    ahead of every newcomer. `p` is any Boolean test for membership in the new queue. -/
theorem Weg.ordnung {u : τ} {a d : Abs τ} (hw : Weg u a d) (ha : AbsOK a) (p : τ → Bool)
    (hp : ∀ x, p x = true ↔ x ∈ d.queue) : a.queue.filter p <+: d.queue := by
  obtain ⟨b, c, h1, h2, h3⟩ := hw
  have hbq : b.queue = a.queue := by
    rcases h1 with h | ⟨_, h⟩
    · exact (congrArg Abs.queue h :).symm
    · exact (congrArg Abs.queue h :)
  have hall : ∀ x ∈ a.queue, x ∈ c.queue := by
    intro x hx
    rcases h2 with h | ⟨_, _, h⟩
    · rw [← congrArg Abs.queue h, hbq]
      exact hx
    · rw [congrArg Abs.queue h]
      show x ∈ b.queue ++ [u]
      rw [hbq]
      exact List.mem_append.2 (Or.inl hx)
  rcases h3 with h | ⟨_, hq, h⟩
  · have hf : a.queue.filter p = a.queue :=
      List.filter_eq_self.2 (fun x hx => (hp x).2 (by rw [← h]; exact hall x hx))
    rw [hf]
    rcases h2 with h' | ⟨_, _, h'⟩
    · exact ⟨[], by rw [List.append_nil, ← h, ← h', hbq]⟩
    · refine ⟨[u], ?_⟩
      rw [← h, h']
      show a.queue ++ [u] = b.queue ++ [u]
      rw [hbq]
  · have hdq : d.queue = c.queue.tail := (congrArg Abs.queue h :)
    obtain ⟨r, hr⟩ := List.head?_eq_some_iff.1 hq
    have hcq : c.queue = u :: d.queue := by
      rw [hdq, hr, List.tail_cons]
    rcases h2 with h' | ⟨hu, _, h'⟩
    · have hac : a.queue = u :: d.queue := hbq.symm.trans ((congrArg Abs.queue h' :).trans hcq)
      have hn := ha.nodup
      rw [hac] at hn
      have hpu : ¬ p u = true := fun hpu' => (List.nodup_cons.1 hn).1 ((hp u).1 hpu')
      have e : a.queue.filter p = d.queue := by
        rw [hac, List.filter_cons_of_neg hpu, List.filter_eq_self.2 (fun x hx => (hp x).2 hx)]
      exact ⟨[], by rw [List.append_nil, e]⟩
    · have hcq' : c.queue = b.queue ++ [u] := (congrArg Abs.queue h' :)
      rw [hbq] at hcq' hu
      have hae : a.queue = [] := by
        cases hq' : a.queue with
        | nil => rfl
        | cons x r' =>
          rw [hq'] at hcq' hu
          have he := hcq.symm.trans hcq'
          simp only [List.cons_append, List.cons.injEq] at he
          exact absurd (by rw [he.1]; exact List.mem_cons_self) hu
      rw [hae]
      exact ⟨d.queue, rfl⟩

end Gabbro.Stage0.Senke.Faeden
