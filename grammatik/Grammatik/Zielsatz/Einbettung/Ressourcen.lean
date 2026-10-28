import Grammatik.Zielsatz.Einbettung.Einbettung

/-!
  File:      Grammatik/Zielsatz/Einbettung/Ressourcen.lean
  Subject:   Held resources, access rights, signatures and contracts under an embedding (stage E0).

  Everything the syntax of `D` states about holdings and rights holds of the image in `D'`: a
  guard of a carrier is the image of its guard (`darfE`), a call's fit is the image's fit
  (`rufPasstE`), the holdings after a call are the image of the holdings after it (`nachSigE`),
  a body's end and start holdings are the images (`endeE`, `anfangE`).
-/

namespace Gabbro.Grammatik.Einbettung

open Gabbro.Grammatik

variable {D D' : Deklaration} (E : Einbettung D D')

namespace Einbettung

theorem lock_inj : Function.Injective E.lock := fun x y h => by
  have := congrArg E.lockZ h
  rw [E.lockZ_lock, E.lockZ_lock] at this
  exact Option.some.inj this

theorem marke_inj : Function.Injective E.marke := fun x y h => by
  have := congrArg E.markeZ h
  rw [E.markeZ_marke, E.markeZ_marke] at this
  exact Option.some.inj this

theorem tab_inj : Function.Injective E.tab := fun x y h => by
  have := congrArg E.tabZ h
  rw [E.tabZ_tab, E.tabZ_tab] at this
  exact Option.some.inj this

theorem glob_inj : Function.Injective E.glob := fun x y h => by
  have := congrArg E.globZ h
  rw [E.globZ_glob, E.globZ_glob] at this
  exact Option.some.inj this

theorem fn_inj : Function.Injective E.fn := fun x y h => by
  have := congrArg E.fnZ h
  rw [E.fnZ_fn, E.fnZ_fn] at this
  exact Option.some.inj this

theorem von_e (w : D.Lock ⊕ (D.Marke × Nat)) :
    Res.von D' (Sum.map E.lock (Prod.map E.marke _root_.id) w) = E.resE (Res.von D w) := by
  rcases w with L | ⟨m, s⟩ <;> rfl

theorem vonMarke_e (m : D.Marke × Nat) :
    Res.vonMarke D' (Prod.map E.marke _root_.id m) = E.resE (Res.vonMarke D m) := by
  rcases m with ⟨m, s⟩; rfl

theorem darfE {t : D.Tab} {Λ : List (Res D)} (h : darf D t Λ) : darf D' (E.tab t) (Λ.map E.resE) := by
  intro w hw
  rw [E.braucht] at hw
  obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw
  rw [E.von_e]
  exact List.mem_map_of_mem (h w0 hw0)

theorem gdarfE {g : D.Glob} {Λ : List (Res D)} (h : gdarf D g Λ) :
    gdarf D' (E.glob g) (Λ.map E.resE) := by
  intro w hw
  rw [E.gbraucht] at hw
  obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw
  rw [E.von_e]
  exact List.mem_map_of_mem (h w0 hw0)

theorem mem_mapE {r : Res D} {Λ : List (Res D)} : E.resE r ∈ Λ.map E.resE ↔ r ∈ Λ := by
  constructor
  · intro h
    obtain ⟨a, ha, he⟩ := List.mem_map.mp h
    rw [← E.resE_inj he]
    exact ha
  · exact List.mem_map_of_mem

/-- A held lock among the images is the image of a held lock. -/
theorem held_mem_mapE {M : D'.Lock} {Λ : List (Res D)} (h : Res.held M ∈ Λ.map E.resE) :
    ∃ L, M = E.lock L ∧ Res.held L ∈ Λ := by
  obtain ⟨r, hr, he⟩ := List.mem_map.mp h
  cases r with
  | held L => exact ⟨L, (Res.held.inj he).symm, hr⟩
  | marke m s => cases he

theorem erase_mapE (Λ : List (Res D)) (a : Res D) :
    (Λ.erase a).map E.resE = (Λ.map E.resE).erase (E.resE a) := by
  induction Λ with
  | nil => rfl
  | cons b Λ ih =>
      by_cases h : b = a
      · subst h
        simp only [List.erase_cons_head, List.map_cons]
      · have h' : E.resE b ≠ E.resE a := fun e => h (E.resE_inj e)
        simp only [beq_iff_eq, h, not_false_eq_true, List.erase_cons_tail, List.map_cons, ih, h']

theorem map_heldE (l : List D.Lock) :
    (l.map (Res.held (D := D))).map E.resE = (l.map E.lock).map (Res.held (D := D')) := by
  induction l with
  | nil => rfl
  | cons L l ih => simp only [List.map_cons, ih]; rfl

theorem map_vonMarkeE (l : List (D.Marke × Nat)) :
    (l.map (Res.vonMarke D)).map E.resE = (l.map (Prod.map E.marke _root_.id)).map (Res.vonMarke D') := by
  induction l with
  | nil => rfl
  | cons m l ih =>
      simp only [List.map_cons, ih, E.vonMarke_e]

theorem endeE (V : Vertrag D) : V.ende.map E.resE = (E.vertragE V).ende := by
  simp only [Vertrag.ende, List.map_append, E.map_heldE, E.map_vonMarkeE]
  rfl

theorem anfangE (S : Signatur D.Tab D.Glob D.Lock D.Marke) :
    (Signatur.anfang D S).map E.resE = Signatur.anfang D' (E.sigE S) := by
  simp only [Signatur.anfang, List.map_append, E.map_heldE, E.map_vonMarkeE]
  rfl

theorem foldl_erase_mapE (ks : List (D.Marke × Nat)) (Λ : List (Res D)) :
    (ks.foldl (fun acc m => acc.erase (Res.vonMarke D m)) Λ).map E.resE =
      (ks.map (Prod.map E.marke _root_.id)).foldl (fun (acc : List (Res D')) m =>
        acc.erase (Res.vonMarke D' m)) (Λ.map E.resE) := by
  induction ks generalizing Λ with
  | nil => rfl
  | cons k ks ih =>
      rw [List.foldl_cons, List.map_cons, List.foldl_cons, ih, E.erase_mapE, E.vonMarke_e]

theorem nachSigE (S : Signatur D.Tab D.Glob D.Lock D.Marke) (Λ : List (Res D)) :
    (nachSig D S Λ).map E.resE = nachSig D' (E.sigE S) (Λ.map E.resE) := by
  simp only [nachSig, List.map_append, E.map_vonMarkeE, E.foldl_erase_mapE]
  rfl

theorem nachE {E : Einbettung D D'} (hS : E.SigTreu) (f : D.Fn) (Λ : List (Res D)) :
    (nach D f Λ).map E.resE = nach D' (E.fn f) (Λ.map E.resE) := by
  unfold nach
  rw [hS.signatur]
  exact E.nachSigE (D.signatur f) Λ

theorem ergCtxE (Γ : Ctx) (e : Option Ty) :
    (ErgCtx Γ e).map E.tyE = ErgCtx (Γ.map E.tyE) (e.map E.tyE) := by
  cases e <;> rfl

theorem invSichtE (i : D.Inv) : (invSicht D i).map E.resE = invSicht D' (E.inv i) := by
  simp only [invSicht]
  rw [E.traeger]
  induction D.traeger i with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.foldr_cons, List.map_append, List.map_cons, ih]
      congr 1
      rw [E.braucht, List.map_map, List.map_map]
      exact List.map_congr_left fun w _ => (E.von_e w).symm

theorem rufPasstE {V : Vertrag D} {S : Signatur D.Tab D.Glob D.Lock D.Marke} {Λ : List (Res D)}
    (h : RufPasst D V S Λ) : RufPasst D' (E.vertragE V) (E.sigE S) (Λ.map E.resE) where
  hw := fun t' ht => by
    simp only [sigE, vertragE] at ht ⊢
    revert ht
    cases E.tabZ t' with
    | none => intro ht; cases ht
    | some t => exact h.hw t
  hg := fun g' hg => by
    simp only [sigE, vertragE] at hg ⊢
    revert hg
    cases E.globZ g' with
    | none => intro hg; cases hg
    | some g => exact h.hg g
  hk := by
    obtain ⟨l, hp, hs⟩ := h.hk
    refine ⟨l.map E.resE, ?_, hs.map E.resE⟩
    have e := E.map_vonMarkeE S.konsumiert
    show ((S.konsumiert.map (Prod.map E.marke _root_.id)).map (Res.vonMarke D')).Perm (l.map E.resE)
    rw [← e]
    exact hp.map E.resE
  hh := fun L' hL' => by
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hL'
    exact List.mem_map_of_mem (f := E.resE) (h.hh L hL)
  hx := fun L' hL' hn => by
    obtain ⟨L, rfl, hL⟩ := E.held_mem_mapE hL'
    obtain ⟨c, hc, hr⟩ := h.hx L hL (fun hm => hn (List.mem_map_of_mem hm))
    exact ⟨c, hc, by rw [E.rang]; exact hr⟩
  hb := h.hb

end Einbettung

end Gabbro.Grammatik.Einbettung
