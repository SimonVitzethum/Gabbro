module

public import Core.Maschine.Schritte

@[expose] public section

namespace Gabbro.Core.Maschine

variable {S Ev : Type}

def KeinSchritt (schritt : Nat → S → Ev → S → Prop) (t : Nat) (s : S) : Prop :=
  ∀ event next, ¬ schritt t s event next

/-- A hardware cut records an enabled transition or an unchanged state where the clock permits a
    pause. Implementations pause only when no transition exists. -/
inductive Takt (schritt : Nat → S → Ev → S → Prop) (pause : Nat → S → Prop)
    (t : Nat) (s : S) (spur : Option Ev) (next : S) : Prop where
  | schritt {event} (label : spur = some event) (h : schritt t s event next) :
      Takt schritt pause t s spur next
  | wartet (label : spur = none) (gleich : next = s) (h : pause t s) : Takt schritt pause t s spur next

structure Zeitlauf (schritt : Nat → S → Ev → S → Prop)
    (pause : Nat → S → Prop := KeinSchritt schritt) where
  zustand : Nat → S
  spur : Nat → Option Ev
  takt : ∀ t, Takt schritt pause t (zustand t) (spur t) (zustand (t + 1))

namespace Zeitlauf

variable {schritt : Nat → S → Ev → S → Prop} {pause : Nat → S → Prop}

/-- The initial cut and the prefix ending after every actual transition. -/
def Schnitt (ρ : Zeitlauf schritt pause) : Type :=
  { t : Nat // t = 0 ∨ ∃ i event, t = i + 1 ∧ ρ.spur i = some event }

/-- The finite cases have a last transition (possibly only the initial state). The hardware input
    remains infinite after it. -/
def Endlich (ρ : Zeitlauf schritt pause) : Prop :=
  ∃ t : ρ.Schnitt, ∀ i, t.val ≤ i → ρ.spur i = none

/-- Every finite tail is stuck or finished at each later opportunity. -/
def Maximal (ρ : Zeitlauf schritt pause) : Prop :=
  ∀ t, (∀ i, t ≤ i → ρ.spur i = none) → ∀ i, t ≤ i → KeinSchritt schritt i (ρ.zustand i)

theorem wartet {ρ : Zeitlauf schritt pause} {t : Nat} (h : ρ.spur t = none) :
    ρ.zustand (t + 1) = ρ.zustand t ∧ pause t (ρ.zustand t) := by
  cases ρ.takt t with
  | schritt label _step => cases label.symm.trans h
  | wartet _label eq hp => exact ⟨eq, hp⟩

/-- Each hardware index has the state of a prefix cut, even when it is a pause. -/
theorem schnitt_deckt (ρ : Zeitlauf schritt pause) (t : Nat) :
    ∃ k : ρ.Schnitt, k.val ≤ t ∧ ρ.zustand k.val = ρ.zustand t := by
  induction t with
  | zero => exact ⟨⟨0, Or.inl rfl⟩, Nat.le_refl _, rfl⟩
  | succ t ih =>
    cases event : ρ.spur t with
    | none =>
      obtain ⟨k, before, eq⟩ := ih
      exact ⟨k, Nat.le_trans before (Nat.le_succ _), eq.trans (ρ.wartet event).1.symm⟩
    | some e => exact ⟨⟨t + 1, Or.inr ⟨t, e, rfl, event⟩⟩, Nat.le_refl _, rfl⟩

/-- Private implementation steps may occupy hardware ticks at which the ideal run pauses. -/
def erlaubePausen {pause' : Nat → S → Prop} (ρ : Zeitlauf schritt pause)
    (erlaubt : ∀ t s, pause t s → pause' t s) : Zeitlauf schritt pause' where
  zustand := ρ.zustand
  spur := ρ.spur
  takt t := by
    cases ρ.takt t with
    | schritt label step => exact .schritt label step
    | wartet label eq hp => exact .wartet label eq (erlaubt _ _ hp)

theorem erlaubePausen_maximal {pause' : Nat → S → Prop} (ρ : Zeitlauf schritt)
    (erlaubt : ∀ t s, KeinSchritt schritt t s → pause' t s) : (ρ.erlaubePausen erlaubt).Maximal :=
  fun _ tail i after => (ρ.wartet (tail i after)).2

theorem takt_existiert (schritt : Nat → S → Ev → S → Prop) (t : Nat) (s : S) :
    ∃ r : S × Option Ev, Takt schritt (KeinSchritt schritt) t s r.2 r.1 := by
  by_cases h : ∃ event next, schritt t s event next
  · obtain ⟨event, next, step⟩ := h
    exact ⟨(next, some event), .schritt rfl step⟩
  · exact ⟨(s, none), .wartet rfl rfl (fun event next step => h ⟨event, next, step⟩)⟩

noncomputable def folge (schritt : Nat → S → Ev → S → Prop) (init : S) : Nat → S × Option Ev
  | 0 => (init, none)
  | t + 1 => Classical.choose (takt_existiert schritt t (folge schritt init t).1)

/-- Every time-dependent step relation has a maximal run from a given state, with a transition
    selected at each cut where the relation admits one. -/
theorem existiert (schritt : Nat → S → Ev → S → Prop) (init : S) :
    ∃ ρ : Zeitlauf schritt, ρ.zustand 0 = init :=
  ⟨⟨fun t => (folge schritt init t).1, fun t => (folge schritt init (t + 1)).2,
    fun t => Classical.choose_spec (takt_existiert schritt t (folge schritt init t).1)⟩, rfl⟩

end Zeitlauf

end Gabbro.Core.Maschine
