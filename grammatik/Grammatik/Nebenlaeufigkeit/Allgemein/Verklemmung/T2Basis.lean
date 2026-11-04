/- Part 2 of 3 of `Verklemmung` (split by instrumente/teile/lean-teilen.py; the umbrella `Verklemmung.lean` imports all parts). -/
module
public import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung.T1
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **A push**: the callee's typing at the call site (`RufPasst`: its
    signature locks are named by the caller, every extra lock ranks below
    its floor, floors rise) gives the chain one frame higher. -/
theorem rangKette_push {o : List D.Lock} {F C G : RufRahmenG D} {S : List (RufRahmenG D)}
    {g : D.Fn} (h : RangKette o (fun _ => False) F S) (hCf : C.f = F.f) (hGf : G.f = g)
    (hGΛ : G.rest.2.2.1 = Signatur.anfang D (D.signatur g))
    (hCΛ : ∀ K, Res.held K ∈ F.rest.2.2.1 → Res.held K ∈ C.rest.2.2.1)
    (hp : RufPasst D (vertragVon D F.f) (D.signatur g) F.rest.2.2.1) :
    RangKette o (fun _ => False) G (C :: S) := by
  have hk0 := rangKette_kopfK h
  have ebG : bodenF G.f = (D.signatur g).boden := by rw [hGf]; rfl
  have ehG : D.haelt G.f = (D.signatur g).haelt := by rw [hGf]; rfl
  have ebC : bodenF C.f = bodenF F.f := congrArg bodenF hCf
  have ehC : D.haelt C.f = D.haelt F.f := congrArg D.haelt hCf
  have hb : BodenLe (bodenF F.f) (bodenF G.f) := by
    rw [ebG]; exact fun c hc => hp.hb c hc
  refine ⟨fun K hK => ?_, ?_, by rw [ebC]; exact hb, ?_⟩
  · rcases hk0 K hK with h1 | h1
    · by_cases hKg : K ∈ (D.signatur g).haelt
      · exact Or.inl (by rw [hGΛ]; exact (held_anfang _ K).mpr hKg)
      · obtain ⟨c, hc, hlt⟩ := hp.hx K h1 hKg
        exact Or.inr (Or.inl ⟨c, by rw [ebG]; exact hc, hlt⟩)
    · obtain ⟨c, hc, hlt⟩ := h1
      obtain ⟨c', hc', hle⟩ := hb c hc
      exact Or.inr (Or.inl ⟨c', hc', by omega⟩)
  · rw [ehG]
    exact fun L hL => hCΛ L (hp.hh L hL)
  · cases S with
    | nil =>
        intro K hK
        rcases h K hK with h1 | h1
        · exact Or.inl (hCΛ K h1)
        · exact h1.elim
    | cons c rest =>
        obtain ⟨h1, h2, h3, h4⟩ := h
        refine ⟨fun K hK => ?_, by rw [ehC]; exact h2, by rw [ebC]; exact h3, by rw [ebC]; exact h4⟩
        rcases h1 K hK with h5 | h5 | h5
        · exact Or.inl (hCΛ K h5)
        · exact Or.inr (Or.inl (by rw [ebC]; exact h5))
        · exact h5.elim

/-- A pop transports every remaining holding through the caller. A released
    occurrence need not survive, and all lower frames restrict to the same subset. -/
theorem rangKette_pop {o o' : List D.Lock} {H caller N : RufRahmenG D} {rst : List (RufRahmenG D)}
    (h : RangKette o (fun _ => False) H (caller :: rst))
    (subset : o' ⊆ o)
    (hnamed : ∀ K ∈ o', Res.held K ∈ H.rest.2.2.1 → Res.held K ∈ caller.rest.2.2.1)
    (hNf : N.f = caller.f) (hNΛ : N.rest.2.2.1 = caller.rest.2.2.1) :
    RangKette o' (fun _ => False) N rst := by
  obtain ⟨h1, _, _, h4⟩ := h
  have tail := rangKette_tail h4 (fun K hK => Or.inl (subset hK))
  have ebN : bodenF N.f = bodenF caller.f := congrArg bodenF hNf
  have ehN : D.haelt N.f = D.haelt caller.f := congrArg D.haelt hNf
  cases rst with
  | nil =>
      intro K hK
      rw [hNΛ]
      rcases h1 K (subset hK) with h5 | h5 | h5
      · exact Or.inl (hnamed K hK h5)
      · rcases tail K hK with h6 | h6
        · exact Or.inl h6
        · exact (unter_ueber h5 h6).elim
      · exact h5.elim
  | cons c rest =>
      obtain ⟨g1, g2, g3, g4⟩ := tail
      refine ⟨fun K hK => ?_, by rw [ehN]; exact g2, by rw [ebN]; exact g3, by rw [ebN]; exact g4⟩
      rw [hNΛ, ebN]
      rcases h1 K (subset hK) with h5 | h5 | h5
      · exact Or.inl (hnamed K hK h5)
      · rcases g1 K hK with h6 | h6 | h6
        · exact Or.inl h6
        · exact Or.inr (Or.inl h6)
        · exact (unter_ueber h5 h6).elim
      · exact h5.elim

/-- The feature set of the floors: every `locks L` still ahead of a frame of
    `f` ranks at least `f`'s floor. -/
def bodenM (f : D.Fn) : Merkmal D :=
  ⟨fun _ => true, fun _ => true, fun L => match bodenF f with
    | none => true
    | some c => decide (c ≤ D.rang L)⟩

theorem bodenM_ueber {f : D.Fn} {L : D.Lock} (h : (bodenM f).sperre L = true) :
    UeberB (bodenF f) L := by
  intro c hc
  simp only [bodenM, hc, decide_eq_true_eq] at h
  exact h

/-- The floors of a program, read on its bodies (the residue form of
    `StufenOk`), decided per function. -/
def StufenM (P : Programm D) : Prop := ∀ f, mE (bodenM f) (P.rumpf f) = true

/-- The bottom frame's function. -/
def unten (z : RufFadenG D) : D.Fn := (z.stapel.getLast?.getD z.kopf).f

/-- **The rank invariant of a thread** whose start function is `w`. -/
def RangInvG (w : D.Fn) (z : RufFadenG D) : Prop :=
  (offen z.spur).Nodup ∧ RangKette (offen z.spur) (fun _ => False) z.kopf z.stapel ∧
  MerkInvG (fun _ => True) bodenM z ∧ unten z = w

section Inv

variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem rangInvG_schritt (hO : GutO O) (hSt : StufenM P) {w : D.Fn} {M M' : RufMaschineG D}
    {u : Faden} (hs : RufSchrittG P O passes M u M') (h : RangInvG w (M.faeden u)) :
    RangInvG w (M'.faeden u) := by
  obtain ⟨hnd, hk, hm, hu⟩ := h
  have hm' := merkInvG_schritt (fun f _ => ⟨hSt f, fun _ _ => trivial⟩) hs hm
  have hR := (hm _ List.mem_cons_self).2
  rcases schrittRang hO hs _ hR with
    ⟨hst, hf, ⟨ho, hΛ⟩ | ⟨L, hL, _, hsp, ho, hΛ⟩ | ⟨L, ho, hΛ⟩⟩ |
    ⟨g, c', hst, hcf, hgf, hgΛ, hcΛ, ho, hp⟩ | ⟨caller, rst, released, hpop, hst, hf, hΛ, ho, hperm⟩
  · refine ⟨by rw [ho]; exact hnd, ?_, hm', ?_⟩
    · rw [hst, ho]
      exact rangKette_kopf hf hk (fun K hK => Or.inr ⟨hK, hΛ K⟩) (fun K hK => Or.inl hK)
    · rw [← hu]; unfold unten; rw [hst]
      cases (M.faeden u).stapel.getLast? with
      | none => exact hf
      | some F => rfl
  · refine ⟨by rw [ho]; exact List.nodup_cons.mpr ⟨hL, hnd⟩, ?_, hm', ?_⟩
    · rw [hst, ho]
      refine rangKette_kopf hf hk (fun K hK => ?_) (fun K hK => ?_)
      · rcases List.mem_cons.mp hK with rfl | hK
        · exact Or.inl (by rw [hΛ]; exact List.mem_cons_self)
        · exact Or.inr ⟨hK, fun h => by rw [hΛ]; exact List.mem_cons_of_mem _ h⟩
      · rcases List.mem_cons.mp hK with rfl | hK
        · refine Or.inr fun G hG => ?_
          rcases List.mem_cons.mp hG with rfl | hG
          · exact bodenM_ueber hsp
          · exact ueberB_of_le (bodenM_ueber hsp) (rangKette_boden hk G hG)
        · exact Or.inl hK
    · rw [← hu]; unfold unten; rw [hst]
      cases (M.faeden u).stapel.getLast? with
      | none => exact hf
      | some F => rfl
  · refine ⟨by rw [ho]; exact hnd.erase L, ?_, hm', ?_⟩
    · rw [hst, ho]
      refine rangKette_kopf hf hk (fun K hK => ?_) (fun K hK => Or.inl (List.mem_of_mem_erase hK))
      obtain ⟨hne, hK'⟩ := (List.Nodup.mem_erase_iff hnd).mp hK
      exact Or.inr ⟨hK', hΛ K hne⟩
    · rw [← hu]; unfold unten; rw [hst]
      cases (M.faeden u).stapel.getLast? with
      | none => exact hf
      | some F => rfl
  · refine ⟨by rw [ho]; exact hnd, ?_, hm', ?_⟩
    · rw [hst, ho]
      exact rangKette_push hk hcf hgf hgΛ hcΛ hp
    · rw [← hu]; unfold unten; rw [hst, List.getLast?_cons]
      cases (M.faeden u).stapel.getLast? with
      | none => exact hcf
      | some F => rfl
  · have hnd' : (offen (M'.faeden u).spur).Nodup := by
      cases released with
      | none => rw [ho]; exact hnd
      | some L => rw [ho]; exact hnd.erase L
    have subset : offen (M'.faeden u).spur ⊆ offen (M.faeden u).spur := by
      intro K hK
      cases released with
      | none => rw [ho] at hK; exact hK
      | some L => rw [ho] at hK; exact List.mem_of_mem_erase hK
    refine ⟨hnd', ?_, hm', ?_⟩
    · rw [hst]
      rw [hpop] at hk
      refine rangKette_pop hk subset (fun K hK hNamed => ?_) hf hΛ
      apply hk.2.1 K
      apply (held_ende (vertragVon D (M.faeden u).kopf.f) K).mp
      apply hperm.mem_iff.mp
      cases released with
      | none => exact hNamed
      | some L =>
        rw [ho] at hK
        have different : K ≠ L := ((List.Nodup.mem_erase_iff hnd).mp hK).1
        exact (List.mem_erase_of_ne (fun he => different (Res.held.inj he))).mpr hNamed
    · rw [← hu]; unfold unten; rw [hst, hpop, List.getLast?_cons]
      cases rst.getLast? with
      | none => exact hf
      | some F => rfl

/-- **The rank invariant on every reachable machine**, given the floors on
    the bodies and duplicate-free start locks. -/
theorem rangInvG_erreichbar (hO : GutO O) (hSt : StufenM P) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hND : ∀ t, (offen (startSpur (D := D) (init t).1)).Nodup) {M : RufMaschineG D}
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M) :
    ∀ t, RangInvG (init t).1 (M.faeden t) := by
  induction hr with
  | start =>
      intro t
      rw [start_faden]
      refine ⟨hND t, fun K hK => Or.inl ((held_anfang _ K).mpr ((offen_startSpur _ K).mp hK)), ?_, rfl⟩
      intro F hF
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      subst hF
      exact ⟨trivial, hSt _⟩
  | schritt M M' u _ hs ih =>
      intro t
      by_cases htu : t = u
      · subst htu
        exact rangInvG_schritt hO hSt hs (ih t)
      · rw [rufSchrittG_fremd hs t htu]
        exact ih t

end Inv

end Gabbro.Grammatik
