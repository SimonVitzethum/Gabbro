/-
  File:      Grammatik/Zielsatz/FaedenVor.lean -- THE SPEC DIFF OF 2026-09-26 WEAKENS NOTHING
             (Opus agent A, OFFEN O21/O22).

  The diff (Spec.lean, "WHAT CHANGED ON 2026-09-26") gave `Einheit` a field `gestartet` (default
  `[]`), put each run-time root TWICE into `Einheit.ws`, let (b) `StartPflicht.req` and (d)
  `Laufzeit.start` range over `E.starts ++ E.gestartet`, and moved the conclusion from G runs
  (`Ziel` on every `RufErreichbarG` machine) to thread-machine runs (`ZielF` on every
  `FadenErreichbar` machine). This file proves, as theorems and not as prose:

  * `ws_ohne_gestartet`, `startPflicht_vor_iff`, `laufzeit_vor_iff` -- on a unit with no
    run-time root (`gestartet = []`, every unit of before) the checker's `ws`, the start
    obligation and the runtime premise are WORD FOR WORD the old ones;
  * `pruefer_aus_vor`, `pruefer_aus_vor_gleich` -- every checker of the OLD interface (sound
    against `AkzeptiertSpec … (E.starts.map (·.1))`) is a checker of the new one that gives the
    SAME verdict on every unit of before (it refuses a unit with run-time roots, which it never
    judged);
  * `gabbro_ziel_vor : GabbroZielVor` -- THE OLD STATEMENT, VERBATIM over the units of before
    (old checker interface, old (b), old (d), `Ziel` on every G run), is a corollary of the new
    `gabbro_ziel`. So the new statement claims everything the old one claimed.
  * `akzeptiertSpec_gestartet` -- what the checker's Bool guarantees about a run-time root:
    no signature lock, no reasons (`N458`'s model half) and pool safety (`N462`/`N457`'s model
    half), because the root stands twice in `ws`.
-/
import Grammatik.Zielsatz.Beweis

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. On a unit of before, every premise is the old one -/

/-- Without run-time roots, `ws` is the list of the declared starts, as before 2026-09-26. -/
theorem ws_ohne_gestartet (E : Einheit D) (h : E.gestartet = []) :
    E.ws = E.starts.map (·.1) := by
  unfold Einheit.ws
  rw [h, List.append_nil, List.append_nil]

/-- The start obligation of before (`req` over `E.starts`). -/
structure StartPflichtVor (E : Einheit D) : Prop where
  sperren : ∀ L, E.S.inv L E.sp0 = true
  req : ∀ a ∈ E.starts, ReqAmEintritt E.P a.1 (E.sp0.welt []) a.2

/-- The user's obligation of before. -/
structure NutzerPflichtVor (E : Einheit D) : Prop where
  logik : LogikPflicht E.P E.S E.Q
  start : StartPflichtVor E

/-- The runtime premise of before (`start` over `E.starts`, `einmal` over their functions). -/
structure LaufzeitVor (E : Einheit D) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)) : Prop where
  lader : sp = speicherR E.sp0
  start : ∀ t, init t = ⟨none, .nil⟩ ∨ ∃ a ∈ E.starts, init t = ⟨some a.1, envR a.2⟩
  einmal : ∀ t u, t ≠ u → (init t).1 = (init u).1 →
    (init t).1 = none ∨ ∃ w, (init t).1 = some w ∧ Mehrfach (E.starts.map (·.1)) w

/-- (b) of before and (b) now coincide on a unit of before. -/
theorem startPflicht_vor_iff (E : Einheit D) (h : E.gestartet = []) :
    StartPflicht E ↔ StartPflichtVor E := by
  constructor
  · intro hS
    exact ⟨hS.sperren, fun a ha => hS.req a (List.mem_append_left _ ha)⟩
  · intro hS
    refine ⟨hS.sperren, fun a ha => ?_⟩
    rw [h, List.append_nil] at ha
    exact hS.req a ha

/-- (d) of before and (d) now coincide on a unit of before. -/
theorem laufzeit_vor_iff (E : Einheit D) (h : E.gestartet = []) {sp : Speicher D.mitRuhe}
    {init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)} :
    Laufzeit E sp init ↔ LaufzeitVor E sp init := by
  have hws := ws_ohne_gestartet E h
  have hl : E.starts ++ E.gestartet = E.starts := by rw [h, List.append_nil]
  constructor
  · intro hL
    refine ⟨hL.lader, fun t => ?_, fun t u htu he => ?_⟩
    · rw [← hl]; exact hL.start t
    · rw [← hws]; exact hL.einmal t u htu he
  · intro hL
    refine ⟨hL.lader, fun t => ?_, fun t u htu he => ?_⟩
    · rw [hl]; exact hL.start t
    · rw [hws]; exact hL.einmal t u htu he

/-! ## 2. Every checker of before is a checker now, with the same verdict -/

/-- **The checker interface of before**: sound against `AkzeptiertSpec` over the declared
    starts' functions. -/
structure PrueferVor where
  akzeptiert : ∀ {D : Deklaration} [DecidableEq D.Fn],
    Einheit D → List D.Fn → List D.Lock → List (D.Tab ⊕ D.Glob) → Bool
  korrekt : ∀ {D : Deklaration} [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    akzeptiert E fs.1 ls.1 cs.1 = true → AkzeptiertSpec E.P E.S fs.1 (E.starts.map (·.1))

/-- An old checker as a new one: it refuses what it never judged (a unit with run-time
    roots) and says what it said on every other unit. -/
def pruefer_aus_vor (C : PrueferVor) : Pruefer where
  akzeptiert := fun E fs ls cs => C.akzeptiert E fs ls cs && E.gestartet.isEmpty
  korrekt := fun E fs ls cs h => by
    rw [Bool.and_eq_true] at h
    have hg : E.gestartet = [] := List.isEmpty_iff.mp h.2
    rw [ws_ohne_gestartet E hg]
    exact C.korrekt E fs ls cs h.1

/-- **The same verdict on every unit of before.** -/
theorem pruefer_aus_vor_gleich (C : PrueferVor) {D : Deklaration} [DecidableEq D.Fn]
    (E : Einheit D) (h : E.gestartet = []) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) :
    (pruefer_aus_vor C).akzeptiert E fs ls cs = C.akzeptiert E fs ls cs := by
  show (C.akzeptiert E fs ls cs && E.gestartet.isEmpty) = C.akzeptiert E fs ls cs
  rw [h]
  simp

/-! ## 3. The old statement, verbatim, is a corollary -/

/-- **`GabbroZiel` AS IT READ BEFORE 2026-09-26**, over the units of before (no run-time root):
    the old checker interface, the old (b) and (d), and `Ziel` on every machine-G run. -/
def GabbroZielVor : Prop :=
  ∀ (C : PrueferVor) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D),
    E.gestartet = [] →
    ∀ (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    C.akzeptiert E fs.1 ls.1 cs.1 = true →
    NutzerPflichtVor E →
    ∀ O : Orakel D, HardwareAnnahmen O E.Q →
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      LaufzeitVor E sp init →
      ∀ M : RufMaschineG D.mitRuhe,
        RufErreichbarG E.P.mitRuhe O.mitRuhe passes (RufStartG E.P.mitRuhe sp init) M →
          Ziel E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes (RufStartG E.P.mitRuhe sp init) M

/-- **NOTHING IS WEAKENED: the old statement follows from the new one.** -/
theorem gabbro_ziel_vor : GabbroZielVor := by
  intro C D _ E hg fs ls cs hC hN O hH passes sp init hL M hr
  have hC' : (pruefer_aus_vor C).akzeptiert E fs.1 ls.1 cs.1 = true := by
    rw [pruefer_aus_vor_gleich C E hg]; exact hC
  exact gabbro_ziel_g (pruefer_aus_vor C) D E fs ls cs hC'
    ⟨hN.logik, (startPflicht_vor_iff E hg).mpr hN.start⟩ O hH passes sp init
    ((laufzeit_vor_iff E hg).mpr hL) M hr

/-! ## 4. What the checker guarantees about a run-time root -/

/-- A run-time root stands twice in `ws`. -/
theorem mehrfach_gestartet (E : Einheit D) (a : Σ w : D.Fn, Env D (D.params w))
    (ha : a ∈ E.gestartet) : Mehrfach E.ws a.1 := by
  unfold Einheit.ws Mehrfach
  rw [List.map_append]
  have h1 : List.Sublist [a.1] ((E.starts ++ E.gestartet).map (·.1)) :=
    List.singleton_sublist.mpr (List.mem_map_of_mem (List.mem_append_right _ ha))
  have h2 : List.Sublist [a.1] (E.gestartet.map (·.1)) :=
    List.singleton_sublist.mpr (List.mem_map_of_mem ha)
  exact List.Sublist.append h1 h2

/-- **The checker's guarantee about a run-time root** (the model half of `N458`, `N462` and, for
    a lifted `child` region, `N456`/`N457`): no signature lock, no reasons, and pool-safe --
    every carrier its graph may write is guarded or atomic. -/
theorem akzeptiertSpec_gestartet [DecidableEq D.Fn] (E : Einheit D) (fs : List D.Fn)
    (hA : AkzeptiertSpec E.P E.S fs E.ws) (a : Σ w : D.Fn, Env D (D.params w))
    (ha : a ∈ E.gestartet) :
    D.haelt a.1 = [] ∧ D.gruende a.1 = 0 ∧ PoolSicherW E.P fs a.1 := by
  have hm := mehrfach_gestartet E a ha
  have hw : a.1 ∈ E.ws := hm.subset (List.mem_cons_self)
  exact ⟨(hA.wurzeln a.1 hw).1, (hA.wurzeln a.1 hw).2, hA.einzeln a.1 hm⟩

#print axioms Gabbro.Grammatik.Zielsatz.ws_ohne_gestartet
#print axioms Gabbro.Grammatik.Zielsatz.startPflicht_vor_iff
#print axioms Gabbro.Grammatik.Zielsatz.laufzeit_vor_iff
#print axioms Gabbro.Grammatik.Zielsatz.pruefer_aus_vor_gleich
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_vor
#print axioms Gabbro.Grammatik.Zielsatz.mehrfach_gestartet
#print axioms Gabbro.Grammatik.Zielsatz.akzeptiertSpec_gestartet

end Gabbro.Grammatik.Zielsatz
