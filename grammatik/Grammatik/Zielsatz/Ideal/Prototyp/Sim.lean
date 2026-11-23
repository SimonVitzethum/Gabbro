/-
  File:      Grammatik/Zielsatz/Ideal/Prototyp/Sim.lean
  Subject:   PROTOTYPE of S7: the refinement relation `R` between an implementation state and the ONE ideal state
             of its run (`dokumente/PERFECT-MODEL.md` §3.6), with its frame and disjointness lemmas.

  The ideal run commits a unit at its LAST implementation step (release, unmask, end of handler; a one-step unit
  at its step). Until then `I` has not started the unit: the ideal thread stands at the unit's start, and the
  implementation is a REPLAY of a prefix of the unit's body against the ideal memory (`Replay`, the per-thread
  idea of `ZielInvSA`). The answers the unit received so far are PENDING (`pa c`): the ideal run receives them
  when it takes the unit. Outside the carriers of the running units and outside the lent buffers, the two
  memories are equal. That one global ideal run exists rests on ONE fact: the carriers of units that run at the
  same time are DISJOINT (lock ownership, the mask, ownership of buffers) -- `acc_disj_*`.
-/
module

public import Grammatik.Zielsatz.Ideal.Prototyp.Discipline

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.Ideal.Prototyp

/-- The carriers of the unit thread `t` is inside (none between units). -/
def CurK (P : Prog) (t : Fin 2) (th : Th) : Nat → Prop :=
  match th.cur with
  | some (.lk k _) => KLk P t k th.lent
  | some (.mk _) => KMk P t th.lent
  | none => fun _ => False

/-- The carriers of the running handler (none when it does not run). -/
def HdK (P : Prog) (s : S) : Nat → Prop :=
  match s.hd with
  | some _ => KIrq P
  | none => fun _ => False

/-- The replay of thread `t`: equal to `I` between units; inside a unit a replay of its body. -/
def ThR (P : Prog) (s : S) (i : IS) (pa : List Int) (t : Fin 2) : Prop :=
  match (s.th t).cur with
  | none => i.th t = ⟨(s.th t).prog, (s.th t).regs, (s.th t).view, (s.th t).lent⟩ ∧ pa = []
  | some (.lk k rest) => ∃ body, (i.th t).prog = .lock k body :: (s.th t).prog ∧
      BodyOk (KLk P t k (s.th t).lent) body ∧
      Replay (KLk P t k (s.th t).lent) body rest pa (i.th t).regs i.mem (s.th t).regs s.mem ∧
      (s.th t).view = vjoin (i.th t).view (i.lview k) ∧ (i.th t).lent = (s.th t).lent ∧ s.owner k = some t
  | some (.mk rest) => t = 0 ∧ ∃ body, (i.th t).prog = .masked body :: (s.th t).prog ∧
      BodyOk (KMk P t (s.th t).lent) body ∧
      Replay (KMk P t (s.th t).lent) body rest pa (i.th t).regs i.mem (s.th t).regs s.mem ∧
      (s.th t).view = (i.th t).view ∧ (i.th t).lent = (s.th t).lent ∧ s.mask = true ∧ s.hd = none

/-- The replay of the handler. -/
def HdR (P : Prog) (s : S) (i : IS) (pa : List Int) : Prop :=
  match s.hd with
  | none => pa = []
  | some (rest, ρ) => Replay (KIrq P) P.handler rest pa (fun _ => 0) i.mem ρ s.mem ∧ s.mask = true

/-- **The refinement relation** between the implementation state `s`, the ideal state `i` of its run, and the
    pending answers `pa` of the units still running. -/
structure R (P : Prog) (s : S) (i : IS) (pa : Ctx → List Int) : Prop where
  thr : ∀ t, ThR P s i (pa (.thr t)) t
  hd : HdR P s i (pa .irq)
  dma : pa .dma = []
  mem : ∀ l, (∀ t, ¬ CurK P t (s.th t) l) → ¬ HdK P s l → (∀ t, (s.th t).lent l = false) → i.mem l = s.mem l
  lview : i.lview = s.lview
  am : i.am = s.am
  lentOwn : ∀ t x, (s.th t).lent x = true → P.prot x = .own t
  prog : ∀ t, ProgOk P t (s.th t).lent (s.th t).prog
  suf : ∀ t, (i.th t).prog <:+ P.thread t

/-- The relation holds at the start. -/
theorem r_init (P : Prog) (hD : Disc P) : R P (S.init P) (IS.init P) (fun _ => []) where
  thr t := by simp [ThR, S.init, IS.init]
  hd := by simp only [HdR, S.init]
  dma := rfl
  mem _ _ _ _ := rfl
  lview := rfl
  am := rfl
  lentOwn t x h := by simp [S.init] at h
  prog t := hD.1 t
  suf t := List.suffix_refl _

/-! ## Where the carriers of a running unit lie -/

/-- A carrier of a running thread unit is a location of a lock the thread owns, an owned location of the thread,
    or a location of the mask while thread 0 masks and the handler does not run. -/
theorem curK_prot {P : Prog} {s : S} {i : IS} {pa : List Int} {t : Fin 2} {l : Nat} (h : ThR P s i pa t)
    (hl : CurK P t (s.th t) l) :
    (∃ k, P.prot l = .lock k ∧ s.owner k = some t) ∨ P.prot l = .own t ∨
      (P.prot l = .irq ∧ t = 0 ∧ s.hd = none) := by
  unfold ThR at h
  unfold CurK at hl
  cases hc : (s.th t).cur with
  | none => simp only [hc] at hl
  | some cu =>
      cases cu with
      | lk k rest =>
          simp only [hc] at h hl
          obtain ⟨_, _, _, _, _, _, ho⟩ := h
          rcases hl with hl | ⟨hl, _⟩
          · exact Or.inl ⟨k, hl, ho⟩
          · exact Or.inr (Or.inl hl)
      | mk rest =>
          simp only [hc] at h hl
          obtain ⟨ht, _, _, _, _, _, _, _, hhd⟩ := h
          rcases hl with hl | ⟨hl, _⟩
          · exact Or.inr (Or.inr ⟨hl, ht, hhd⟩)
          · exact Or.inr (Or.inl hl)

theorem hdK_prot {P : Prog} {s : S} {l : Nat} (hl : HdK P s l) : P.prot l = .irq ∧ s.hd ≠ none := by
  unfold HdK at hl
  cases hc : s.hd with
  | none => simp only [hc] at hl
  | some _ => simp only [hc] at hl; exact ⟨hl, by simp⟩

/-- Units of two different threads have disjoint carriers. -/
theorem acc_disj_thr {P : Prog} {s : S} {i : IS} {pa pa' : List Int} {t u : Fin 2} {l : Nat} (htu : t ≠ u)
    (ht : ThR P s i pa t) (hu : ThR P s i pa' u) (hlt : CurK P t (s.th t) l) (hlu : CurK P u (s.th u) l) :
    False := by
  rcases curK_prot ht hlt with ⟨k, hk, ho⟩ | ho | ⟨hi, h0, _⟩ <;>
    rcases curK_prot hu hlu with ⟨k', hk', ho'⟩ | ho' | ⟨hi', h0', _⟩
  all_goals first
    | (rw [hk] at hk'; cases hk'; rw [ho] at ho'; cases ho'; exact htu rfl)
    | (rw [ho] at ho'; cases ho'; exact htu rfl)
    | exact htu (h0.trans h0'.symm)
    | (simp_all; done)

/-- A running thread unit and the running handler have disjoint carriers. -/
theorem acc_disj_hd {P : Prog} {s : S} {i : IS} {pa : List Int} {t : Fin 2} {l : Nat}
    (ht : ThR P s i pa t) (hlt : CurK P t (s.th t) l) (hl : HdK P s l) : False := by
  obtain ⟨hi, hn⟩ := hdK_prot hl
  rcases curK_prot ht hlt with ⟨k, hk, _⟩ | ho | ⟨_, _, hhd⟩
  · rw [hk] at hi; cases hi
  · rw [ho] at hi; cases hi
  · exact hn hhd

/-- A lent buffer is no carrier of any running unit. -/
theorem lent_not_curK {P : Prog} {s : S} {i : IS} {pa : List Int} {t u : Fin 2} {x : Nat}
    (hR : ∀ t x, (s.th t).lent x = true → P.prot x = .own t) (ht : ThR P s i pa u)
    (hx : (s.th t).lent x = true) : ¬ CurK P u (s.th u) x := by
  intro hl
  have hp := hR t x hx
  rcases curK_prot ht hl with ⟨k, hk, _⟩ | ho | ⟨hi, _, _⟩
  · rw [hp] at hk; cases hk
  · rw [hp] at ho; cases ho
    unfold CurK at hl
    cases hc : (s.th t).cur with
    | none => simp only [hc] at hl
    | some cu =>
        cases cu with
        | lk k rest =>
            simp only [hc, KLk] at hl
            rcases hl with hl | ⟨_, hl⟩
            · rw [hp] at hl; cases hl
            · rw [hx] at hl; cases hl
        | mk rest =>
            simp only [hc, KMk] at hl
            rcases hl with hl | ⟨_, hl⟩
            · rw [hp] at hl; cases hl
            · rw [hx] at hl; cases hl
  · rw [hp] at hi; cases hi

theorem lent_not_hdK {P : Prog} {s : S} {t : Fin 2} {x : Nat}
    (hR : ∀ t x, (s.th t).lent x = true → P.prot x = .own t) (hx : (s.th t).lent x = true) : ¬ HdK P s x := by
  intro hl
  have := (hdK_prot hl).1
  rw [hR t x hx] at this; cases this

/-! ## Frames: what another context does not touch -/

/-- The replay of thread `u` survives a step of another context that leaves `u`, its carriers, its lock's view
    and owner, and (while it masks) the mask and the handler alone. -/
theorem thR_frame {P : Prog} {s s' : S} {i i' : IS} {pa : List Int} {u : Fin 2} (h : ThR P s i pa u)
    (hth : s'.th u = s.th u) (hi : i'.th u = i.th u)
    (hmS : Agree (CurK P u (s.th u)) s.mem s'.mem) (hmI : Agree (CurK P u (s.th u)) i.mem i'.mem)
    (hlk : ∀ k rest, (s.th u).cur = some (.lk k rest) → i'.lview k = i.lview k ∧ s'.owner k = s.owner k)
    (hmk : ∀ rest, (s.th u).cur = some (.mk rest) → s'.mask = s.mask ∧ s'.hd = s.hd) :
    ThR P s' i' pa u := by
  unfold ThR at h ⊢
  rw [hth, hi]
  unfold CurK at hmS hmI
  cases hc : (s.th u).cur with
  | none => simp only [hc] at h ⊢; exact h
  | some cu =>
      cases cu with
      | lk k rest =>
          simp only [hc] at h hmS hmI ⊢
          obtain ⟨body, hp, hok, hrp, hv, hl, ho⟩ := h
          obtain ⟨h1, h2⟩ := hlk k rest hc
          exact ⟨body, hp, hok, replay_frameS (replay_frameI hrp hok hmI) hmS, by rw [h1]; exact hv, hl,
            by rw [h2]; exact ho⟩
      | mk rest =>
          simp only [hc] at h hmS hmI ⊢
          obtain ⟨h0, body, hp, hok, hrp, hv, hl, hm, hhd⟩ := h
          obtain ⟨h1, h2⟩ := hmk rest hc
          exact ⟨h0, body, hp, hok, replay_frameS (replay_frameI hrp hok hmI) hmS, hv, hl, by rw [h1]; exact hm,
            by rw [h2]; exact hhd⟩

/-- The replay of the handler survives a step of another context that leaves its carriers and the mask alone. -/
theorem hdR_frame {P : Prog} {s s' : S} {i i' : IS} {pa : List Int} (hok : BodyOk (KIrq P) P.handler)
    (h : HdR P s i pa) (hhd : s'.hd = s.hd)
    (hA : s.hd ≠ none → Agree (KIrq P) s.mem s'.mem ∧ Agree (KIrq P) i.mem i'.mem ∧ s'.mask = s.mask) :
    HdR P s' i' pa := by
  unfold HdR at h ⊢
  rw [hhd]
  cases hc : s.hd with
  | none => simp only [hc] at h ⊢; exact h
  | some x =>
      obtain ⟨rest, ρ⟩ := x
      simp only [hc] at h ⊢
      obtain ⟨hS, hI, hm⟩ := hA (by simp [hc])
      exact ⟨replay_frameS (replay_frameI h.1 hok hI) hS, by rw [hm]; exact h.2⟩

end Gabbro.Grammatik.Zielsatz.Ideal.Prototyp
