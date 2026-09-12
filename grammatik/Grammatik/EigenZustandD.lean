/-
  File:      Grammatik/EigenZustandD.lean
  Subject:   **OWN-STATE PROJECTION** (lane 56, attempt D).

  A step fired by a thread `h` whose program text never names table `t`
  leaves every slot of `t` unchanged. The route is bottom-up: each writing
  leaf records a `zugriff t true ..` event (carried by `hcar` of the leaf
  rule of `PCSchritt`); a leaf whose recorded events carry no `Sum.inl t`
  keeps the slots of `t`; take/release steps keep memory by construction.
-/
import Grammatik.Maschine
import Grammatik.Satz

namespace Gabbro.Grammatik.EZD

open Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Trace suffix helpers: from outcome spur to the recorded list.

  A leaf step records `σ'.spur = neu ++ oldSpur`. Each writing form below
  computes `σ'.spur = pre ++ oldSpur` with a write event in `pre`; cancelling
  the common suffix `oldSpur` puts the event into `neu`. -/

/-- Cancelling a common trace suffix: two prefixes of one spur agree. -/
theorem neu_of_suffix {σ' σ : World D} {pre neu : List (Ereignis D)}
    (h1 : σ'.spur = pre ++ σ.spur) (h2 : σ'.spur = neu ++ σ.spur) :
    neu = pre :=
  List.append_cancel_right (h2.symm.trans h1)

/-- The head write event lands in the recorded list. -/
theorem neu_head {σ' σ : World D} {ev : Ereignis D} {reads neu : List (Ereignis D)}
    (h1 : σ'.spur = ev :: reads ++ σ.spur) (h2 : σ'.spur = neu ++ σ.spur) :
    ev ∈ neu := by
  have h1' : σ'.spur = (ev :: reads) ++ σ.spur := h1
  have heq : neu = ev :: reads := neu_of_suffix h1' h2
  rw [heq]
  exact List.mem_cons_self

/-- `schreibBytes` only prefixes the trace: the outcome spur is a prefix
    plus the entry spur. -/
theorem schreibBytes_spur_suffix (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ : List (Res D)) (k : Int) (bs : List Byte) :
    ∃ pre, (σ.schreibBytes t f hf Λ k bs).spur = pre ++ σ.spur := by
  induction bs generalizing σ k with
  | nil => exact ⟨[], by simp [World.schreibBytes]⟩
  | cons b bs ih =>
      have hcons : σ.schreibBytes t f hf Λ k (b :: bs) =
          (σ.schreibSlot t Λ k f
            (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))).schreibBytes
            t f hf Λ (k + 1) bs := rfl
      obtain ⟨pre₂, hpre₂⟩ := ih _ _
      refine ⟨pre₂ ++ [Ereignis.zugriff t true Λ σ.haelt], ?_⟩
      have hspur : (σ.schreibSlot t Λ k f
          (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))).spur =
          [Ereignis.zugriff t true Λ σ.haelt] ++ σ.spur := rfl
      rw [hcons, hpre₂, hspur, List.append_assoc]

/-- A nonempty `schreibBytes` records a write event for its table. -/
theorem schreibBytes_has_write (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ : List (Res D)) (k : Int) (bs : List Byte)
    (hne : bs ≠ []) :
    ∃ ev ∈ (σ.schreibBytes t f hf Λ k bs).spur,
      ev.traeger = some (Sum.inl t) := by
  cases bs with
  | nil => exact absurd rfl hne
  | cons b bs =>
      refine ⟨Ereignis.zugriff t true Λ σ.haelt, ?_, rfl⟩
      have hmem : Ereignis.zugriff (D := D) t true Λ σ.haelt ∈
          (σ.schreibSlot t Λ k f
            (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))).spur :=
        List.mem_cons_self
      obtain ⟨pre, hpre⟩ := schreibBytes_spur_suffix
        (σ.schreibSlot t Λ k f
          (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))) t f hf Λ (k + 1) bs
      have hmem₂ : Ereignis.zugriff (D := D) t true Λ σ.haelt ∈
          ((σ.schreibSlot t Λ k f
            (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))).schreibBytes
            t f hf Λ (k + 1) bs).spur := by
        rw [hpre]
        exact List.mem_append_right _ hmem
      exact hmem₂

/-- `schreibBytes` on `t` leaves every other table's slots alone. -/
theorem schreibBytes_slots_other (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ : List (Res D)) (t₀ : D.Tab) (hne : t₀ ≠ t)
    (k : Int) (bs : List Byte) (k' : Int) (f' : D.Feld t₀) :
    (σ.schreibBytes t f hf Λ k bs).slots t₀ k' f' = σ.slots t₀ k' f' := by
  induction bs generalizing σ k with
  | nil => rfl
  | cons b bs ih =>
      have hcons : σ.schreibBytes t f hf Λ k (b :: bs) =
          (σ.schreibSlot t Λ k f
            (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))).schreibBytes
            t f hf Λ (k + 1) bs := rfl
      rw [hcons, ih]
      exact storeSlot_andere _ _ _ _ _ _ hne _ _

end Gabbro.Grammatik.EZD
