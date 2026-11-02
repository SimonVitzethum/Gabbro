/-
  File:      Grammatik/RennfreiOrte.lean
  Subject:   RACE FREEDOM ON UNGUARDED CARRIERS -- what a thread can touch
             is bounded by its call graph, so an unguarded carrier that one
             thread's graph may write and no other thread's graph may read
             or write is never part of a cross-thread pair.

  `rennfrei_g_voll` (RennfreiVoll.lean) orders every cross-thread pair on a
  LOCK-GUARDED carrier. For an unguarded carrier there is no lock to order
  anything, so the claim there is that such a pair does not exist. That
  needs two static bounds per step, both new:

  * **Reads.** Every read event a step records lies on a carrier of the
    footprint `fussOrteG P f` of the function `f` of the acting frame. The
    residue predicate `GRest.oR P C` ("every expression still to run reads
    only carriers in `C`", over the existing `blockOrteP`/`endblockOrteP`)
    is kept by every rule (`schrittOrte`, the twin of `schrittMerk`); the
    frame invariant `OrteInvG` holds on every reachable machine
    (`orteInvG_erreichbar`) with `C` the footprint of each frame's function.
  * **Writes.** Every write event a step records is on a carrier the acting
    frame's function may write by signature (`TraegerSchreibt`): every write
    form carries its permission `hw` in the syntax; axioms write only their
    declared frame, which the call's `hw` bounds. Memory changes are
    `schritt_traeger`.

  `schritt_zugriffe` joins both per step. With the call-graph invariant
  `merkInvG_erreichbar` every acting function lies in its thread's call
  graph, which gives `zugriff_im_graph`, and from it the theorem
  `rennfrei_ungeschuetzt`: a carrier that is SEPARATED over the call graphs
  (`SchreibGetrenntK`: one graph may write it => no other graph may write it
  or have it in a footprint) has no cross-thread access pair with a write.
  `rennfrei_alle` combines both halves into the full race-freedom statement
  for every carrier that is not atomic and not a publish payload.
-/
module
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtMehrfaden
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiOrte.T1.Teil1a
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}
/-! ## 3. The frame invariant -/

/-- The footprint of `f`, as a carrier test. -/
def fussC (P : Programm D) (f : D.Fn) (c : D.Tab ⊕ D.Glob) : Bool :=
  istIn (fussOrteG P f) c

/-- **The read bound of a thread**: every frame's residue reads only
    carriers of its function's footprint. -/
def OrteInvG (P : Programm D) (z : RufFadenG D) : Prop :=
  ∀ F ∈ z.kopf :: z.stapel, F.rest.2.2.2.2.oR P (fussC P F.f)

theorem body_oR (P : Programm D) (g : D.Fn) :
    (endblockOrteP P (P.rumpf g)).all (fussC P g) = true :=
  List.all_eq_true.mpr fun _ hc => istIn_iff.mpr (fuss_rumpfG P g hc)

section Inv

variable {P : Programm D} {O : Orakel D} {pa : Nat}

theorem orteInvG_schritt {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O pa M f M')
    (h : OrteInvG P (M.faeden f)) : OrteInvG P (M'.faeden f) := by
  have hk := h _ List.mem_cons_self
  rcases schrittOrte hs with ⟨hst, hf, hR⟩ | ⟨g, caller', rho, s0, hst, hcf, hkopf, hR⟩ |
      ⟨caller, rst, hpop, hst, hf, hR⟩
  · intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · have := hR (fussC P (M.faeden f).kopf.f) hk
      rw [← hf] at this
      exact this
    · rw [hst] at hF
      exact h F (List.mem_cons_of_mem _ hF)
  · have hc := hR (fussC P (M.faeden f).kopf.f) hk
    intro F hF
    rw [hst, hkopf] at hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact body_oR P g
    · rcases List.mem_cons.mp hF with rfl | hF
      · rw [← hcf] at hc
        exact hc
      · exact h F (List.mem_cons_of_mem _ hF)
  · have hc := h caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · have := hR _ hc
      rw [← hf] at this
      exact this
    · rw [hst] at hF
      exact h F (by rw [hpop]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hF))

/-- **The read bound on every reachable machine** -- no premise: a frame
    enters with its function's body, whose reads are its footprint. -/
theorem orteInvG_erreichbar (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    {M : RufMaschineG D} (hr : RufErreichbarG P O pa (RufStartG P sp init) M) :
    ∀ t, OrteInvG P (M.faeden t) := by
  induction hr with
  | start =>
      intro t F hF
      have e : (RufStartG P sp init).faeden t =
          ⟨[], ⟨(init t).1, (init t).2, sp.welt [], ⟨false, D.params (init t).1,
            Signatur.anfang D (D.signatur (init t).1), (init t).2, .ende (P.rumpf (init t).1)⟩⟩,
            startSpur (init t).1, [RufEreignisF.eintritt (init t).1 (init t).2 (sp.welt [])]⟩ := by
        show (match init t with
          | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
              Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
              [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D)) = _
        cases init t
        rfl
      rw [e] at hF
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      subst hF
      exact body_oR P _
  | schritt M M' u _ hs ih =>
      intro t
      by_cases htu : t = u
      · subst htu
        exact orteInvG_schritt hs (ih t)
      · rw [rufSchrittG_fremd hs t htu]
        exact ih t

end Inv
/-! ## 4. The events of one step -/

/-- The write permission of a contract, per carrier. -/
def schreibV (V : Vertrag D) : D.Tab ⊕ D.Glob → Bool
  | .inl t => V.schreibt t
  | .inr g => V.gschreibt g

theorem schreibV_vertragVon (f : D.Fn) (c : D.Tab ⊕ D.Glob) :
    schreibV (vertragVon D f) c = TraegerSchreibt f c := by
  cases c <;> rfl

/-- **Recorded events within bounds**: every read event is on a carrier in
    `C`, every write event on a carrier in `W`. -/
def EvOk (C W : D.Tab ⊕ D.Glob → Bool) (X : List (Ereignis D)) : Prop :=
  ∀ e ∈ X, ∀ c w, zugriffVon e = some (c, w) → (w = false → C c = true) ∧ (w = true → W c = true)

section Ev

variable {C W : D.Tab ⊕ D.Glob → Bool}

theorem evOk_nil : EvOk (D := D) C W [] := fun _ h => absurd h List.not_mem_nil

theorem evOk_fremd (q : D.Ax ⊕ D.Reg ⊕ D.Glob) : EvOk (D := D) C W [.fremd q] := fun e he c w h => by
  simp only [List.mem_singleton] at he
  subst he
  simp only [zugriffVon, reduceCtorEq] at h

theorem evOk_append {X Y : List (Ereignis D)} (hX : EvOk C W X) (hY : EvOk C W Y) :
    EvOk C W (X ++ Y) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hX e he
  · exact hY e he

theorem evOk_lese (σ : World D) (Λ : List (Res D)) {os : List (D.Tab ⊕ D.Glob)}
    (h : os.all C = true) : EvOk C W (leseEv σ Λ os) := by
  intro e he c w hz
  simp only [leseEv, List.mem_map] at he
  obtain ⟨o, ho, rfl⟩ := he
  have hC := (List.all_eq_true.mp h) o ho
  cases o with
  | inl t =>
      simp only [zugriffVon, Option.some.injEq, Prod.mk.injEq] at hz
      obtain ⟨rfl, rfl⟩ := hz
      exact ⟨fun _ => hC, fun h => by cases h⟩
  | inr g =>
      simp only [zugriffVon, Option.some.injEq, Prod.mk.injEq] at hz
      obtain ⟨rfl, rfl⟩ := hz
      exact ⟨fun _ => hC, fun h => by cases h⟩

theorem evOk_schreibT {t : D.Tab} {Λ : List (Res D)} {h : List D.Lock}
    (hw : W (.inl t) = true) : EvOk C W [Ereignis.zugriff t true Λ h] := by
  intro e he c w hz
  rw [List.mem_singleton] at he
  subst he
  simp only [zugriffVon, Option.some.injEq, Prod.mk.injEq] at hz
  obtain ⟨rfl, rfl⟩ := hz
  exact ⟨fun h => (by cases h), fun _ => hw⟩

theorem evOk_schreibG {g : D.Glob} {Λ : List (Res D)} {h : List D.Lock}
    (hw : W (.inr g) = true) : EvOk C W [Ereignis.gzugriff g true Λ h] := by
  intro e he c w hz
  rw [List.mem_singleton] at he
  subst he
  simp only [zugriffVon, Option.some.injEq, Prod.mk.injEq] at hz
  obtain ⟨rfl, rfl⟩ := hz
  exact ⟨fun h => (by cases h), fun _ => hw⟩

theorem evOk_sperre (e : Ereignis D) (he : zugriffVon e = none) : EvOk C W [e] := by
  intro e' h c w hz
  rw [List.mem_singleton] at h
  subst h
  rw [he] at hz
  cases hz

end Ev
end Gabbro.Grammatik
