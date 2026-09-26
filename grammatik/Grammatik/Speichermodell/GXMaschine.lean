/-
  File:      Grammatik/Speichermodell/GXMaschine.lean
  Subject:   THE THREAD MACHINE AND THE TIME SEGMENTS OVER MACHINE GX (Opus lane O25c, 2026-09-26,
             OFFEN O25). Definitions and machine-level lemmas; no program fact.

  Machine GX (`RufSchrittGX`, AtomarLauf.lean) is machine G whose reads of the shared atomics
  `Tg` are answered by the weak memory: a G step on a PRESENTED memory that agrees with G's
  outside `Tg`. Every W step of an accepted program is a GX step (`schwach_ist_gX`). The goal
  statement speaks, since lane O25c, about runs of GX with threads spawned at run time. This
  file builds that machine the way FadenMaschine.lean builds it over G:

  * `FadenSchrittX`, `FadenErreichbarX` -- the thread machine with GX in place of G in its `lauf`
    rule; `start`, `kind`, `join` are FadenMaschine.lean's word for word;
  * `fadenSchrittX_of`, `fadenErreichbarX_of` -- every thread-machine run over G is one over GX
    (a G step is a GX step presenting G's own memory, `gx_aus_g`): nothing is lost;
  * `fadenErreichbarX_GX`, `fadenErreichbarX_von_GX` -- the bridge to GX and back, as for G;
  * `FadenInvX` and its lemmas -- `FadenInv` with a GX run in its `lauf` field;
  * `gx_leer_g` -- with NO shared atomic (`Tg` empty) a GX step IS a G step, so GX over an empty
    `Tg` is G (used to derive the statement of before);
  * `SegLaufX`, `segZaehleX`, `aktivVorX`, `frame_schritte_beschraenktX` -- the time bound of
    KostenG.lean over GX segments: a thread's step count depends on its own frames only, which a
    GX step moves exactly as its inner G step does.
-/
import Grammatik.FadenMaschine
import Grammatik.KostenG
import Grammatik.Speichermodell.AtomarLauf

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. GX steps: facts about threads -/

section GX

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}

/-- A thread other than the actor keeps its state over a GX step. -/
theorem gxSchritt_fremd {M M' : RufMaschineG D} {u : Faden}
    (h : RufSchrittGX P O passes Tg M u M') (t : Faden) (htu : t ≠ u) :
    M'.faeden t = M.faeden t := by
  obtain ⟨σ, M'', hs, _, _, _, hfa, _, _⟩ := h
  rw [hfa]
  exact rufSchrittG_fremd hs t htu

/-- **With no shared atomic a GX step is a G step**: the presented memory is G's, and the
    successor is the inner step's machine. -/
theorem gx_leer_g (hT : ∀ c, ¬ Tg c) {M M' : RufMaschineG D} {u : Faden}
    (h : RufSchrittGX P O passes Tg M u M') : RufSchrittG P O passes M u M' := by
  obtain ⟨σ, M'', hs, hσ, h1, h2, hfa, hla, hst⟩ := h
  have eσ : σ = M.speicher := speicher_ext fun c => hσ c (hT c)
  subst eσ
  rw [mitSpeicher_selbst] at hs h1 h2
  have esp : M'.speicher = M''.speicher := speicher_ext fun c => by
    by_cases hw : SchreibG M M'' u c
    · exact h1 c hw
    · exact traegerGleich_trans (h2 c hw)
        (traegerGleich_symm (traegerGleich_of_nicht_schreib (M := M) (M' := M'') hw))
  have e : M' = M'' := by
    cases M' with
    | mk sp fa la st =>
      cases M'' with
      | mk sp' fa' la' st' =>
        simp only at esp hfa hla hst
        subst esp hfa hla hst
        rfl
  rw [e]
  exact hs

theorem gx_leer_g_lauf (hT : ∀ c, ¬ Tg c) {M0 M : RufMaschineG D}
    (h : RufErreichbarGX P O passes Tg M0 M) : RufErreichbarG P O passes M0 M := by
  induction h with
  | start => exact .start
  | schritt M M' u _ hs ih => exact .schritt _ _ _ ih (gx_leer_g hT hs)

/-- GX is monotone in the shared atomics: a larger `Tg` admits more presented memories. -/
theorem gx_mono {Tg' : D.Tab ⊕ D.Glob → Prop} (hT : ∀ c, Tg c → Tg' c) {M M' : RufMaschineG D}
    {u : Faden} (h : RufSchrittGX P O passes Tg M u M') : RufSchrittGX P O passes Tg' M u M' := by
  obtain ⟨σ, M'', hs, hσ, h1, h2, h3, h4, h5⟩ := h
  exact ⟨σ, M'', hs, fun c hc => hσ c fun ht => hc (hT c ht), h1, h2, h3, h4, h5⟩

end GX

/-! ## 2. The thread machine over GX -/

/-- **One step of the thread machine over GX**: `FadenSchritt` with a GX step in `lauf`. -/
inductive FadenSchrittX (P : Programm D) (O : Orakel D) (passes : Nat)
    (Tg : D.Tab ⊕ D.Glob → Prop) : FadenMaschine D → FadenMaschine D → Prop where
  | lauf (K : FadenMaschine D) (f : Faden) (M' : RufMaschineG D)
      (hf : K.lebt f = true) (hw : K.wartet f = []) (hs : RufSchrittGX P O passes Tg K.m f M') :
      FadenSchrittX P O passes Tg K ⟨M', K.lebt, K.wartet, K.rang, K.uhr⟩
  | start (K : FadenMaschine D) (p : Faden) (cs : List Faden)
      (hp : K.lebt p = true) (hw : K.wartet p = [])
      (hfrei : offen (K.m.faeden p).spur = [])
      (hcs : ∀ c ∈ cs, K.lebt c = false) :
      FadenSchrittX P O passes Tg K
        ⟨K.m, fun t => if t ∈ cs then true else K.lebt t,
         fun t => if t = p then cs else K.wartet t,
         fun t => if t ∈ cs then K.rang p + 1 else K.rang t, K.uhr + 1⟩
  | kind (K : FadenMaschine D) (p c : Faden)
      (hp : K.lebt p = true) (hw : K.wartet p = []) (hc : K.lebt c = false) :
      FadenSchrittX P O passes Tg K
        ⟨K.m, fun t => if t = c then true else K.lebt t, K.wartet,
         fun t => if t = c then K.rang p + 1 else K.rang t, K.uhr + 1⟩
  | join (K : FadenMaschine D) (p : Faden)
      (hp : K.lebt p = true) (hw : K.wartet p ≠ [])
      (hf : ∀ u ∈ K.wartet p, FertigG K.m u) :
      FadenSchrittX P O passes Tg K
        ⟨K.m, K.lebt, fun t => if t = p then [] else K.wartet t, K.rang, K.uhr⟩

/-- Reachable thread machines over GX. -/
inductive FadenErreichbarX (P : Programm D) (O : Orakel D) (passes : Nat)
    (Tg : D.Tab ⊕ D.Glob → Prop) (K0 : FadenMaschine D) : FadenMaschine D → Prop where
  | start : FadenErreichbarX P O passes Tg K0 K0
  | schritt (K K' : FadenMaschine D) (h : FadenErreichbarX P O passes Tg K0 K)
      (hs : FadenSchrittX P O passes Tg K K') : FadenErreichbarX P O passes Tg K0 K'

section Faden

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}

/-- **Every thread-machine step over G is one over GX.** -/
theorem fadenSchrittX_of {K K' : FadenMaschine D} (h : FadenSchritt P O passes K K') :
    FadenSchrittX P O passes Tg K K' := by
  cases h with
  | lauf f M' hf hw hs => exact .lauf K f M' hf hw (gx_aus_g hs)
  | start p cs hp hw hfrei hcs => exact .start K p cs hp hw hfrei hcs
  | kind p c hp hw hc => exact .kind K p c hp hw hc
  | join p hp hw hf => exact .join K p hp hw hf

/-- **Every thread-machine run over G is one over GX**: the GX statement loses no G run. -/
theorem fadenErreichbarX_of {K0 K : FadenMaschine D} (h : FadenErreichbar P O passes K0 K) :
    FadenErreichbarX P O passes Tg K0 K := by
  induction h with
  | start => exact .start
  | schritt K K' _ hs ih => exact .schritt _ _ ih (fadenSchrittX_of hs)

/-- With no shared atomic, a thread-machine step over GX is one over G. -/
theorem fadenSchritt_of_X (hT : ∀ c, ¬ Tg c) {K K' : FadenMaschine D}
    (h : FadenSchrittX P O passes Tg K K') : FadenSchritt P O passes K K' := by
  cases h with
  | lauf f M' hf hw hs => exact .lauf K f M' hf hw (gx_leer_g hT hs)
  | start p cs hp hw hfrei hcs => exact .start K p cs hp hw hfrei hcs
  | kind p c hp hw hc => exact .kind K p c hp hw hc
  | join p hp hw hf => exact .join K p hp hw hf

/-- **Every thread-machine run over GX is a GX run** from the same start machine. -/
theorem fadenErreichbarX_GX {K0 K : FadenMaschine D} (h : FadenErreichbarX P O passes Tg K0 K) :
    RufErreichbarGX P O passes Tg K0.m K.m := by
  induction h with
  | start => exact .start
  | schritt K K' _ hs ih =>
      cases hs with
      | lauf f M' _ _ hs' => exact .schritt _ _ f ih hs'
      | start => exact ih
      | kind => exact ih
      | join => exact ih

/-- **Every GX run is a thread-machine run over GX** with every thread live, nothing spawned. -/
theorem fadenErreichbarX_von_GX {M0 M : RufMaschineG D} (h : RufErreichbarGX P O passes Tg M0 M) :
    FadenErreichbarX P O passes Tg (FadenMaschine.alleLebend M0) (FadenMaschine.alleLebend M) := by
  induction h with
  | start => exact .start
  | schritt M M' f _ hs ih =>
      exact .schritt _ _ ih (.lauf (FadenMaschine.alleLebend M) f M' rfl rfl hs)

/-- A spawn leaves the G state alone. -/
theorem fadenX_spawn_m {K K' : FadenMaschine D} {t : Faden}
    (hs : FadenSchrittX P O passes Tg K K') (h0 : K.lebt t = false) (h1 : K'.lebt t = true) :
    K'.m = K.m := by
  cases hs with
  | lauf f M' _ _ _ =>
      have h : K.lebt t = true := h1
      rw [h0] at h
      cases h
  | start => rfl
  | kind => rfl
  | join => rfl

/-- **The invariant of the thread machine over GX** (`FadenInv` with a GX run). -/
structure FadenInvX (P : Programm D) (O : Orakel D) (passes : Nat) (Tg : D.Tab ⊕ D.Glob → Prop)
    (M0 : RufMaschineG D) (K : FadenMaschine D) : Prop where
  lauf : RufErreichbarGX P O passes Tg M0 K.m
  schlaeft : ∀ t, K.lebt t = false → K.m.faeden t = M0.faeden t
  joinFrei : ∀ t, K.wartet t ≠ [] → offen (K.m.faeden t).spur = []
  joinLebt : ∀ t, K.wartet t ≠ [] → K.lebt t = true
  kindLebt : ∀ t u, u ∈ K.wartet t → K.lebt u = true
  rangSteigt : ∀ t u, u ∈ K.wartet t → K.rang t < K.rang u
  rangUhr : ∀ t, K.rang t ≤ K.uhr

theorem fadenInvX_start (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (lebt0 : Faden → Bool) :
    FadenInvX P O passes Tg (RufStartG P sp init) (FadenStart P sp init lebt0) where
  lauf := .start
  schlaeft _ _ := rfl
  joinFrei _ h := absurd rfl h
  joinLebt _ h := absurd rfl h
  kindLebt _ _ h := absurd h List.not_mem_nil
  rangSteigt _ _ h := absurd h List.not_mem_nil
  rangUhr _ := Nat.le_refl 0

/-- The G-free part of `FadenInv`: what spawn, kind and join rules preserve. -/
theorem fadenInvX_schritt {M0 : RufMaschineG D} {K K' : FadenMaschine D}
    (hI : FadenInvX P O passes Tg M0 K) (hs : FadenSchrittX P O passes Tg K K') :
    FadenInvX P O passes Tg M0 K' := by
  cases hs with
  | lauf f M' hf hw hs' =>
      refine ⟨.schritt _ _ f hI.lauf hs', fun t ht => ?_, fun t ht => ?_,
        hI.joinLebt, hI.kindLebt, hI.rangSteigt, hI.rangUhr⟩
      · have hne : t ≠ f := by intro e; subst e; simp_all
        rw [gxSchritt_fremd hs' t hne]
        exact hI.schlaeft t ht
      · have hne : t ≠ f := by intro e; subst e; exact ht hw
        rw [gxSchritt_fremd hs' t hne]
        exact hI.joinFrei t ht
  | start p cs hp hw hfrei hcs =>
      -- the rules without a G step are FadenMaschine.lean's; reuse its invariant
      have hI0 : FadenInv P O passes K.m K :=
        ⟨.start, fun t _ => rfl, hI.joinFrei, hI.joinLebt, hI.kindLebt, hI.rangSteigt, hI.rangUhr⟩
      have h := fadenInv_schritt hI0 (FadenSchritt.start K p cs hp hw hfrei hcs)
      refine ⟨hI.lauf, fun t ht => ?_, h.joinFrei, h.joinLebt, h.kindLebt, h.rangSteigt,
        h.rangUhr⟩
      by_cases hc : t ∈ cs
      · simp [hc] at ht
      · simp only [hc, if_false] at ht
        exact hI.schlaeft t ht
  | kind p c hp hw hc =>
      have hI0 : FadenInv P O passes K.m K :=
        ⟨.start, fun t _ => rfl, hI.joinFrei, hI.joinLebt, hI.kindLebt, hI.rangSteigt, hI.rangUhr⟩
      have h := fadenInv_schritt hI0 (FadenSchritt.kind K p c hp hw hc)
      refine ⟨hI.lauf, fun t ht => ?_, h.joinFrei, h.joinLebt, h.kindLebt, h.rangSteigt,
        h.rangUhr⟩
      by_cases htc : t = c
      · simp [htc] at ht
      · simp only [htc, if_false] at ht
        exact hI.schlaeft t ht
  | join p hp hw hf =>
      have hI0 : FadenInv P O passes K.m K :=
        ⟨.start, fun t _ => rfl, hI.joinFrei, hI.joinLebt, hI.kindLebt, hI.rangSteigt, hI.rangUhr⟩
      have h := fadenInv_schritt hI0 (FadenSchritt.join K p hp hw hf)
      exact ⟨hI.lauf, hI.schlaeft, h.joinFrei, h.joinLebt, h.kindLebt, h.rangSteigt, h.rangUhr⟩

/-- **The invariant on every reachable thread machine over GX.** -/
theorem fadenInvX_erreichbar {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    {lebt0 : Faden → Bool} {K : FadenMaschine D}
    (h : FadenErreichbarX P O passes Tg (FadenStart P sp init lebt0) K) :
    FadenInvX P O passes Tg (RufStartG P sp init) K := by
  induction h with
  | start => exact fadenInvX_start sp init lebt0
  | schritt K K' _ hs ih => exact fadenInvX_schritt ih hs

/-- The G-free facts of `FadenInvX` as a `FadenInv` over the machine's own G state (for the
    lemmas of Zielsatz/Faeden.lean that read only them). -/
theorem FadenInvX.ohneLauf {M0 : RufMaschineG D} {K : FadenMaschine D}
    (hI : FadenInvX P O passes Tg M0 K) :
    FadenInv P O passes K.m ⟨K.m, fun _ => true, K.wartet, K.rang, K.uhr⟩ :=
  ⟨.start, (fun _ h => by cases h), hI.joinFrei, fun _ _ => rfl, fun _ _ _ => rfl, hI.rangSteigt,
    hI.rangUhr⟩

/-- **A dormant slot holds nothing** when its root holds nothing by signature. -/
theorem faden_schlafend_freiX {K : FadenMaschine D} {sp : Speicher D}
    {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    (hI : FadenInvX P O passes Tg (RufStartG P sp init) K) (t : Faden)
    (ht : K.lebt t = false) (hsig : D.haelt (init t).1 = []) :
    offen (K.m.faeden t).spur = [] := by
  rw [hI.schlaeft t ht]
  have hsp : ((RufStartG P sp init).faeden t).spur = startSpur (init t).1 := by
    simp only [RufStartG]
  rw [hsp]
  refine List.eq_nil_iff_forall_not_mem.mpr fun L hL => ?_
  rw [offen_startSpur, hsig] at hL
  exact List.not_mem_nil hL

end Faden

/-! ## 3. Time over GX segments -/

/-- An explicit run of GX (the twin of `SegLauf`). -/
inductive SegLaufX (P : Programm D) (O : Orakel D) (passes : Nat) (Tg : D.Tab ⊕ D.Glob → Prop)
    (M0 : RufMaschineG D) : RufMaschineG D → Type where
  | start : SegLaufX P O passes Tg M0 M0
  | schritt (M M' : RufMaschineG D) (f : Faden)
      (h : SegLaufX P O passes Tg M0 M) (hs : RufSchrittGX P O passes Tg M f M') :
      SegLaufX P O passes Tg M0 M'

/-- Number of steps of thread `f` in an explicit GX run. -/
def segZaehleX {P : Programm D} {O : Orakel D} {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    {M0 M : RufMaschineG D} : SegLaufX P O passes Tg M0 M → Faden → Nat
  | .start, _ => 0
  | .schritt _ _ g h' _, f => segZaehleX h' f + (if g = f then 1 else 0)

/-- Thread `f`'s frame at depth `k` is active before every step of the run. -/
def aktivVorX {P : Programm D} {O : Orakel D} {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    {M0 : RufMaschineG D} (f : Faden) (k : Nat) : {M : RufMaschineG D} →
    SegLaufX P O passes Tg M0 M → Prop
  | _, .start => True
  | _, .schritt (M := M) _ _ h' _ => aktivVorX f k h' ∧ k ≤ (M.faeden f).stapel.length

section Zeit

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}

/-- `KInv` reads thread `f`'s frames only. -/
theorem kinv_faeden {ι : Type} {T : ι → D.Fn → Nat} {S : ι → D.Fn → Bool} {pa B : Nat}
    {f : Faden} {k : Nat} {M M' : RufMaschineG D} {n : Nat} (e : M'.faeden = M.faeden)
    (h : KInv T S pa B f k M n) : KInv T S pa B f k M' n := by
  unfold KInv at h ⊢
  rw [e]
  exact h

/-- **The engine over GX**: the cost invariant along a GX run (each GX step is a G step on the
    presented memory, and the invariant reads the acting thread's frames only). -/
theorem kinv_laufX {ι : Type} (T : ι → D.Fn → Nat) (S : ι → D.Fn → Bool) (nx : ι → D.Fn → ι)
    (hS1 : ∀ i g, S i g = true → kostenEnd (T (nx i g)) passes (P.rumpf g) ≤ T i g)
    (hS2 : ∀ i g, S i g = true → rufeE (S (nx i g)) (P.rumpf g) = true)
    {B : Nat} {f : Faden} {k : Nat} {M1 : RufMaschineG D}
    (h0 : KInv T S passes B f k M1 0) :
    ∀ {M2 : RufMaschineG D} (run : SegLaufX P O passes Tg M1 M2), aktivVorX f k run →
      segZaehleX run f ≤ B ∧
      (k ≤ (M2.faeden f).stapel.length → KInv T S passes B f k M2 (segZaehleX run f)) := by
  intro M2 run
  induction run with
  | start =>
    intro _
    refine ⟨?_, fun _ => h0⟩
    obtain ⟨_, _, _, _, _, _, hB⟩ := h0
    simp only [segZaehleX]
    omega
  | schritt M M' g run' hs ih =>
    intro hA
    obtain ⟨hA', hk⟩ := hA
    have hI := (ih hA').2 hk
    obtain ⟨σ, M'', hs', _, _, _, hfa, _, _⟩ := hs
    have hI' : KInv T S passes B f k (mitSpeicher M σ) (segZaehleX run' f) := kinv_faeden rfl hI
    have h := kinv_schritt T S nx P O passes hS1 hS2 hI' hs'
    refine ⟨h.1, fun hk' => kinv_faeden hfa (h.2 ?_)⟩
    rw [← hfa]
    exact hk'

/-- **TIME OVER GX (`frame_schritte_beschraenkt` for GX runs).** A frame of `g` entered at `M1`
    with calls nested at most `n` deep takes at most `kostenTief P passes (n + 1) g` own steps
    on every GX run while it is active -- whatever the weak memory answers at the shared
    atomics. -/
theorem frame_schritte_beschraenktX (f : Faden) (g : D.Fn) (n : Nat)
    (hadm : rufTief P (n + 1) g = true)
    {rho : Env D (D.params g)} {s0 : World D} {k : Nat} {M1 M2 : RufMaschineG D}
    (hE : Eintritt P f g rho s0 k M1)
    (run : SegLaufX P O passes Tg M1 M2) (hA : aktivVorX f k run) :
    segZaehleX run f ≤ kostenTief P passes (n + 1) g :=
  (kinv_laufX (kostenTief P passes) (rufTief P) (fun i _ => i - 1)
    (fun i h hS => by
      cases i with
      | zero => simp [rufTief] at hS
      | succ m => exact Nat.le_refl _)
    (fun i h hS => by
      cases i with
      | zero => simp [rufTief] at hS
      | succ m => exact hS)
    (kinv_eintritt (kostenTief P passes) (rufTief P) P passes hE n hadm) run hA).1

/-- A G segment is a GX segment with the same counts. -/
def SegLauf.alsX {M0 : RufMaschineG D} :
    {M : RufMaschineG D} → SegLauf P O passes M0 M → SegLaufX P O passes Tg M0 M
  | _, .start => .start
  | _, .schritt M M' f h hs => .schritt M M' f (SegLauf.alsX h) (gx_aus_g hs)

theorem segZaehle_alsX {M0 : RufMaschineG D} :
    ∀ {M : RufMaschineG D} (run : SegLauf P O passes M0 M) (f : Faden),
      segZaehleX (SegLauf.alsX (Tg := Tg) run) f = segZaehle run f
  | _, .start, _ => rfl
  | _, .schritt _ _ g h _, f => by
      simp only [SegLauf.alsX, segZaehleX, segZaehle]
      rw [segZaehle_alsX h f]

theorem aktivVor_alsX {M0 : RufMaschineG D} (f : Faden) (k : Nat) :
    ∀ {M : RufMaschineG D} (run : SegLauf P O passes M0 M),
      aktivVor f k run → aktivVorX f k (SegLauf.alsX (Tg := Tg) run)
  | _, .start, _ => trivial
  | _, .schritt _ _ _ h _, hA => ⟨aktivVor_alsX f k h hA.1, hA.2⟩

end Zeit

#print axioms Gabbro.Grammatik.gx_leer_g
#print axioms Gabbro.Grammatik.fadenErreichbarX_of
#print axioms Gabbro.Grammatik.fadenErreichbarX_GX
#print axioms Gabbro.Grammatik.fadenInvX_erreichbar
#print axioms Gabbro.Grammatik.frame_schritte_beschraenktX

end Gabbro.Grammatik
