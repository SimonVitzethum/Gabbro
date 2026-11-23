/-
  File:      Grammatik/Zielsatz/Ideal/Prototyp/Atomics.lean
  Subject:   PROTOTYPE of S7: the atomic memory of the fragment, RC11 for `relaxed` and `seq_cst` stated directly on
             the fragment (`dokumente/PERFECT-MODEL.md` §3.4), operationally.

  The formulation is the promise-free VIEW model: every write is a message with a timestamp, the modification
  order of a location is the order of its timestamps, every thread (and every lock, and the `seq_cst` fence)
  carries a view, the newest timestamp per location it has seen.
  * `rlx` load: any message of the location not older than the thread's view (coherence); the view moves to it.
  * `rlx` store: a fresh timestamp after the thread's view, anywhere in the modification order (2+2W stays
    possible); `rlx` fetch-add reads a message and writes immediately after it (atomicity of the RMW).
  * `sc`: the access first joins the thread view with the global `sc` view, reads the NEWEST message, writes
    after it, and publishes its view as the new `sc` view: all `sc` accesses form one total order that agrees with
    every view, which is sequential consistency for locations accessed only by `sc` operations.
  * no load buffering: a read reads only messages that already exist, so `po ∪ rf` is acyclic by construction.
  Locks synchronise views (release stores the thread view into the lock, acquire joins it): `Impl.lean`.
  The atomic memory is the SAME in the implementation and in `I` (G's memory W is not refined here; S5 proves the
  correspondence with the axiomatic RC11 and DRF-SC). The timestamp `w` of a step is its named CHOICE POINT.
-/
module

public import Grammatik.Zielsatz.Ideal.Prototyp.Syntax

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.Ideal.Prototyp

/-- A write message: location, value, timestamp. -/
structure Msg where
  loc : Nat
  val : Int
  ts : Nat
  deriving DecidableEq

/-- A view: per atomic location the newest timestamp seen. -/
abbrev View := Nat → Nat

/-- The join of two views. -/
def vjoin (V W : View) : View := fun a => max (V a) (W a)

/-- The atomic memory: the written messages and the `seq_cst` view. -/
structure AMem where
  msgs : List Msg
  scv : View

/-- The empty atomic memory (every location holds the initial message `⟨a, 0, 0⟩`). -/
def AMem.init : AMem := ⟨[], fun _ => 0⟩

/-- `m` is a message of location `a` (the initial message or a written one). -/
def Liest (A : AMem) (a : Nat) (m : Msg) : Prop := m.loc = a ∧ (m = ⟨a, 0, 0⟩ ∨ m ∈ A.msgs)

/-- `ts` is free at location `a`. -/
def Frei (A : AMem) (a ts : Nat) : Prop := 0 < ts ∧ ∀ m ∈ A.msgs, m.loc = a → m.ts ≠ ts

/-- `m` is the newest message of `a`. -/
def Neuest (A : AMem) (a : Nat) (m : Msg) : Prop := Liest A a m ∧ ∀ m', Liest A a m' → m'.ts ≤ m.ts

/-- The atomic step: order, operation, registers, view, memory, the CHOICE `w` (the timestamp read or written)
    and the results. Every case is written out; there is no catch-all. -/
inductive AStep : Ord → AOp → Regs → View → AMem → Nat → Regs → View → AMem → Prop
  | rlxLd {r a ρ V A m w} : Liest A a m → m.ts = w → V a ≤ w →
      AStep .rlx (.ld r a) ρ V A w (upd ρ r m.val) (upd V a w) A
  | rlxSt {a e ρ V A w} : Frei A a w → V a < w →
      AStep .rlx (.st a e) ρ V A w ρ (upd V a w) ⟨⟨a, e.eval ρ, w⟩ :: A.msgs, A.scv⟩
  | rlxFaa {r a e ρ V A m w} : Liest A a m → m.ts = w → V a ≤ w → Frei A a (w + 1) →
      AStep .rlx (.faa r a e) ρ V A w (upd ρ r m.val) (upd V a (w + 1))
        ⟨⟨a, m.val + e.eval ρ, w + 1⟩ :: A.msgs, A.scv⟩
  | scLd {r a ρ V A m w} : Neuest A a m → m.ts = w →
      AStep .sc (.ld r a) ρ V A w (upd ρ r m.val) (upd (vjoin V A.scv) a w)
        ⟨A.msgs, upd (vjoin V A.scv) a w⟩
  | scSt {a e ρ V A m w} : Neuest A a m → m.ts = w →
      AStep .sc (.st a e) ρ V A w ρ (upd (vjoin V A.scv) a (w + 1))
        ⟨⟨a, e.eval ρ, w + 1⟩ :: A.msgs, upd (vjoin V A.scv) a (w + 1)⟩
  | scFaa {r a e ρ V A m w} : Neuest A a m → m.ts = w →
      AStep .sc (.faa r a e) ρ V A w (upd ρ r m.val) (upd (vjoin V A.scv) a (w + 1))
        ⟨⟨a, m.val + e.eval ρ, w + 1⟩ :: A.msgs, upd (vjoin V A.scv) a (w + 1)⟩

/-! ## Invariants of the atomic memory: timestamps are unique per location, views point at messages -/

/-- Timestamps identify the message of a location. -/
def TsEind (A : AMem) : Prop := ∀ a m m', Liest A a m → Liest A a m' → m.ts = m'.ts → m = m'

/-- A view is covered by the messages: each of its entries is at most the timestamp of some message. -/
def Gedeckt (A : AMem) (V : View) : Prop := ∀ a, ∃ m, Liest A a m ∧ V a ≤ m.ts

theorem tsEind_init : TsEind AMem.init := by
  intro a m m' h h' _
  simp only [Liest, AMem.init, List.not_mem_nil, or_false] at h h'
  rw [h.2, h'.2]

theorem gedeckt_init (V : View) (hV : ∀ a, V a = 0) : Gedeckt AMem.init V :=
  fun a => ⟨⟨a, 0, 0⟩, ⟨rfl, Or.inl rfl⟩, by simp [hV a]⟩

theorem liest_cons {A : AMem} {a : Nat} {m n : Msg} {s : View} (h : Liest A a m) :
    Liest ⟨n :: A.msgs, s⟩ a m :=
  ⟨h.1, h.2.imp id (fun h => List.mem_cons_of_mem n h)⟩

theorem liest_cons_inv {A : AMem} {a : Nat} {m n : Msg} {s : View} (h : Liest ⟨n :: A.msgs, s⟩ a m) :
    m = n ∨ Liest A a m := by
  rcases h with ⟨hl, h | h⟩
  · exact Or.inr ⟨hl, Or.inl h⟩
  · rcases List.mem_cons.1 h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hl, Or.inr h⟩

theorem liest_scv {A : AMem} {a : Nat} {m : Msg} {s : View} : Liest ⟨A.msgs, s⟩ a m ↔ Liest A a m := Iff.rfl

theorem neuest_frei {A : AMem} {a : Nat} {m : Msg} (h : Neuest A a m) : Frei A a (m.ts + 1) := by
  refine ⟨Nat.succ_pos _, fun m' hm' hl he => ?_⟩
  have := h.2 m' ⟨hl, Or.inr hm'⟩
  omega

/-- A fresh message keeps timestamps unique. -/
theorem tsEind_cons {A : AMem} {a ts : Nat} {v : Int} {s : View} (hT : TsEind A) (hF : Frei A a ts) :
    TsEind ⟨⟨a, v, ts⟩ :: A.msgs, s⟩ := by
  intro b m m' h h' he
  rcases liest_cons_inv h with rfl | h <;> rcases liest_cons_inv h' with rfl | h'
  · rfl
  · rcases h' with ⟨hl, h' | h'⟩
    · subst h'; exact absurd he (by simp only; exact Nat.ne_of_gt hF.1)
    · exact absurd he.symm (hF.2 m' h' (by rw [hl]; exact h.1.symm))
  · rcases h with ⟨hl, h | h⟩
    · subst h; exact absurd he.symm (by simp only; exact Nat.ne_of_gt hF.1)
    · exact absurd he (hF.2 m h (by rw [hl]; exact h'.1.symm))
  · exact hT b m m' h h' he

theorem gedeckt_cons {A : AMem} {V : View} {n : Msg} {s : View} (h : Gedeckt A V) :
    Gedeckt ⟨n :: A.msgs, s⟩ V := fun a => (h a).imp fun _ hm => ⟨liest_cons hm.1, hm.2⟩

theorem gedeckt_join {A : AMem} {V W : View} (hV : Gedeckt A V) (hW : Gedeckt A W) : Gedeckt A (vjoin V W) := by
  intro a
  rcases Nat.le_total (V a) (W a) with h | h
  · obtain ⟨m, hm, hle⟩ := hW a
    exact ⟨m, hm, by simp only [vjoin]; omega⟩
  · obtain ⟨m, hm, hle⟩ := hV a
    exact ⟨m, hm, by simp only [vjoin]; omega⟩

theorem gedeckt_upd {A : AMem} {V : View} {a : Nat} {m : Msg} (h : Gedeckt A V) (hm : Liest A a m) :
    Gedeckt A (upd V a m.ts) := by
  intro b
  by_cases hb : b = a
  · subst hb; exact ⟨m, hm, by simp⟩
  · rw [upd_ne _ _ hb]; exact h b

theorem gedeckt_upd_new {A : AMem} {V : View} {a ts : Nat} {v : Int} {s : View} (h : Gedeckt A V) :
    Gedeckt ⟨⟨a, v, ts⟩ :: A.msgs, s⟩ (upd V a ts) := by
  intro b
  by_cases hb : b = a
  · subst hb; exact ⟨⟨b, v, ts⟩, ⟨rfl, Or.inr List.mem_cons_self⟩, by simp⟩
  · rw [upd_ne _ _ hb]; exact gedeckt_cons h b

/-- The invariants of the atomic memory together with the views that live beside it. -/
def AInv (A : AMem) (vs : View → Prop) : Prop := TsEind A ∧ Gedeckt A A.scv ∧ ∀ V, vs V → Gedeckt A V

/-- An atomic step keeps unique timestamps, keeps every covered view covered, and produces covered views. -/
theorem aStep_inv {o : Ord} {op : AOp} {ρ ρ' : Regs} {V V' : View} {A A' : AMem} {w : Nat}
    (h : AStep o op ρ V A w ρ' V' A') (hT : TsEind A) (hS : Gedeckt A A.scv) (hV : Gedeckt A V) :
    TsEind A' ∧ Gedeckt A' A'.scv ∧ Gedeckt A' V' ∧ ∀ W, Gedeckt A W → Gedeckt A' W := by
  cases h with
  | rlxLd hm hw _ => subst hw; exact ⟨hT, hS, gedeckt_upd hV hm, fun _ h => h⟩
  | rlxSt hF _ =>
      exact ⟨tsEind_cons hT hF, gedeckt_cons hS, gedeckt_upd_new hV, fun _ h => gedeckt_cons h⟩
  | rlxFaa _ _ _ hF =>
      exact ⟨tsEind_cons hT hF, gedeckt_cons hS, gedeckt_upd_new hV, fun _ h => gedeckt_cons h⟩
  | scLd hm hw =>
      subst hw
      have hJ := gedeckt_upd (gedeckt_join hV hS) hm.1
      exact ⟨hT, hJ, hJ, fun _ h => h⟩
  | @scSt a e _ _ _ m w hm hw =>
      subst hw
      have hJ : Gedeckt ⟨⟨a, e.eval ρ, m.ts + 1⟩ :: A.msgs, upd (vjoin V A.scv) a (m.ts + 1)⟩
          (upd (vjoin V A.scv) a (m.ts + 1)) := gedeckt_upd_new (gedeckt_join hV hS)
      exact ⟨tsEind_cons hT (neuest_frei hm), hJ, hJ, fun _ h => gedeckt_cons h⟩
  | @scFaa r a e _ _ _ m w hm hw =>
      subst hw
      have hJ : Gedeckt ⟨⟨a, m.val + e.eval ρ, m.ts + 1⟩ :: A.msgs, upd (vjoin V A.scv) a (m.ts + 1)⟩
          (upd (vjoin V A.scv) a (m.ts + 1)) := gedeckt_upd_new (gedeckt_join hV hS)
      exact ⟨tsEind_cons hT (neuest_frei hm), hJ, hJ, fun _ h => gedeckt_cons h⟩

/-! ## The atomic step is determined by its choice, and it is always enabled -/

theorem neuest_eind {A : AMem} {a : Nat} {m m' : Msg} (hT : TsEind A) (h : Neuest A a m) (h' : Neuest A a m') :
    m = m' := hT a m m' h.1 h'.1 (Nat.le_antisymm (h'.2 m h.1) (h.2 m' h'.1))

/-- `I.Bestimmt` for atomics: with unique timestamps, the choice `w` determines the step. -/
theorem aStep_bestimmt {o : Ord} {op : AOp} {ρ ρ₁ ρ₂ : Regs} {V V₁ V₂ : View} {A A₁ A₂ : AMem} {w : Nat}
    (hT : TsEind A) (h₁ : AStep o op ρ V A w ρ₁ V₁ A₁) (h₂ : AStep o op ρ V A w ρ₂ V₂ A₂) :
    ρ₁ = ρ₂ ∧ V₁ = V₂ ∧ A₁ = A₂ := by
  cases h₁ with
  | rlxLd hm hw _ =>
      cases h₂ with
      | rlxLd hm' hw' _ =>
          obtain rfl := hT _ _ _ hm hm' (hw.trans hw'.symm)
          exact ⟨rfl, rfl, rfl⟩
  | rlxSt => cases h₂ with | rlxSt => exact ⟨rfl, rfl, rfl⟩
  | rlxFaa hm hw _ _ =>
      cases h₂ with
      | rlxFaa hm' hw' _ _ =>
          obtain rfl := hT _ _ _ hm hm' (hw.trans hw'.symm)
          exact ⟨rfl, rfl, rfl⟩
  | scLd hm _ =>
      cases h₂ with | scLd hm' _ => obtain rfl := neuest_eind hT hm hm'; exact ⟨rfl, rfl, rfl⟩
  | scSt hm _ =>
      cases h₂ with | scSt hm' _ => obtain rfl := neuest_eind hT hm hm'; exact ⟨rfl, rfl, rfl⟩
  | scFaa hm _ =>
      cases h₂ with | scFaa hm' _ => obtain rfl := neuest_eind hT hm hm'; exact ⟨rfl, rfl, rfl⟩

/-- Every location has a newest message. -/
theorem neuest_ex (A : AMem) (a : Nat) : ∃ m, Neuest A a m := by
  induction h : A.msgs generalizing A with
  | nil =>
      refine ⟨⟨a, 0, 0⟩, ⟨rfl, Or.inl rfl⟩, fun m' hm' => ?_⟩
      rcases hm' with ⟨_, rfl | hm⟩
      · exact Nat.le_refl _
      · rw [h] at hm; cases hm
  | cons n ns ih =>
      obtain ⟨m, hm, hmax⟩ := ih ⟨ns, A.scv⟩ rfl
      have hA : A = ⟨n :: ns, A.scv⟩ := by cases A; simp_all
      by_cases hn : n.loc = a ∧ m.ts ≤ n.ts
      · refine ⟨n, ⟨hn.1, Or.inr (by rw [h]; exact List.mem_cons_self)⟩, fun m' hm' => ?_⟩
        rw [hA] at hm'
        rcases liest_cons_inv (A := ⟨ns, A.scv⟩) hm' with rfl | hm'
        · exact Nat.le_refl _
        · exact Nat.le_trans (hmax m' hm') hn.2
      · refine ⟨m, ?_, fun m' hm' => ?_⟩
        · rw [hA]; exact liest_cons (A := ⟨ns, A.scv⟩) hm
        · rw [hA] at hm'
          rcases liest_cons_inv (A := ⟨ns, A.scv⟩) hm' with rfl | hm'
          · rcases Classical.em (m'.loc = a) with hl | hl
            · omega
            · exact absurd hm'.1 (by rw [hA] at hm'; exact hl)
          · exact hmax m' hm'

/-- `I.Fortschritt` for atomics: under covered views, every atomic operation of every order has a step. -/
theorem aStep_ex (o : Ord) (op : AOp) (ρ : Regs) (V : View) (A : AMem) (hV : Gedeckt A V) :
    ∃ w ρ' V' A', AStep o op ρ V A w ρ' V' A' := by
  cases o <;> cases op with
  | ld r a =>
      obtain ⟨m, hm⟩ := neuest_ex A a
      obtain ⟨m₀, hm₀, hle⟩ := hV a
      first
      | exact ⟨_, _, _, _, AStep.rlxLd (r := r) (ρ := ρ) hm.1 rfl (Nat.le_trans hle (hm.2 m₀ hm₀))⟩
      | exact ⟨_, _, _, _, AStep.scLd (r := r) (ρ := ρ) (V := V) hm rfl⟩
  | st a e =>
      obtain ⟨m, hm⟩ := neuest_ex A a
      obtain ⟨m₀, hm₀, hle⟩ := hV a
      first
      | exact ⟨_, _, _, _, AStep.rlxSt (e := e) (ρ := ρ) (neuest_frei hm)
          (Nat.lt_succ_of_le (Nat.le_trans hle (hm.2 m₀ hm₀)))⟩
      | exact ⟨_, _, _, _, AStep.scSt (e := e) (ρ := ρ) (V := V) hm rfl⟩
  | faa r a e =>
      obtain ⟨m, hm⟩ := neuest_ex A a
      obtain ⟨m₀, hm₀, hle⟩ := hV a
      first
      | exact ⟨_, _, _, _, AStep.rlxFaa (r := r) (e := e) (ρ := ρ) hm.1 rfl
          (Nat.le_trans hle (hm.2 m₀ hm₀)) (neuest_frei hm)⟩
      | exact ⟨_, _, _, _, AStep.scFaa (r := r) (e := e) (ρ := ρ) (V := V) hm rfl⟩

end Gabbro.Grammatik.Zielsatz.Ideal.Prototyp
