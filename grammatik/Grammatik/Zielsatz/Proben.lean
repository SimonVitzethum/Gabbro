/-
  File:    Grammatik/Zielsatz/Proben.lean -- PLAN-ZIELSATZ.md step 5: the anti-vacuity
           obligations stated in `Zielsatz/SpecProben.lean`, PROVED.

  Refutations (each fails a premise group of `GabbroZiel`):
  * `probeA_widerlegt_gilt`      -- probe A (`paP`) fails (b) `NutzerPflicht`
                                    (`paP_nicht_sperre`: `logik schleife` at budget 0);
  * `probeD_widerlegt_gilt`      -- probe D (`fvP false`) fails (b) at budget 1 (`probeD_nicht`);
  * `probeD_wahr_widerlegt_gilt` -- the `forever` variant with invariant `true` fails (b) at
                                    budget 1 (`fwP_nicht`: returns under `ensures false`);
  * `tabelle_widerlegt_gilt`     -- the table-invariant breaker `ivPschlecht` fails (b): its
                                    `setze` returns with `konto[0] = 5`, `konto[1] = 0`;
  * `ungeschuetzt_abgelehnt_gilt`-- an unguarded carrier one declared start reads (footprint)
                                    and another writes fails (a) `AkzeptiertSpec`, for every
                                    program.
  The refutations of (b) hold for EVERY family of lock invariants with guarded carriers
  that some memory satisfies (the form `NutzerWiderlegt` of SpecProben): `NutzerPflicht`
  itself carries `SperrInvLokal`, so the family is well-formed (`SperrInvOk`).

  Positives (all premise groups jointly, with an admissible start of `P.mitRuhe`):
  * `zweiFaeden_erfuellbar_gilt` -- the two-thread program `mP` with its declared starts
                                    `hauptA`, `hauptB`;
  * `zweiFaeden_bewegt_gilt`     -- on that admissible start a machine of `mP.mitRuhe`
                                    reached in ONE step of thread 0 (`privA[0] = 7`) has
                                    changed memory;
  * `probeB_erfuellbar_gilt`, `probeC_erfuellbar_gilt` -- probes B/C with `haupt` as the
    DECLARED start (the statements fix `ws = [haupt]`, and `Erfuellbar` asks that every
    declared start runs on some thread): `haupt` runs on thread 0 (`initRuhe [haupt]`), the
    runtime's root on every other thread.

  Applied (`gabbro_ziel_zeuge`): the proved `gabbro_ziel` (Zielsatz/Beweis.lean)
  on `mP`, with the concrete checker `akzeptiert_pruefer`: every leg of `Ziel` at a machine
  of `mP.mitRuhe` with changed memory.
-/
import Grammatik.Zielsatz.SpecProben
import Grammatik.Zielsatz.RuheZeuge
import Grammatik.ZielOrtInvGrund
import Grammatik.Zielsatz.Beweis

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

/-! ## 1. Refutations of (b) -- no side condition on the lock invariants -/

theorem probeA_widerlegt_gilt : probeA_widerlegt := by
  rintro ⟨P, S, Q, st, s⟩ hP h
  obtain rfl : P = paP := hP
  exact paP_nicht_sperre Q S h.logik.2.1 s h.start.sperren zHaupt (h.logik.1 0 zHaupt).1

/-- **Verdict P1, closed: probe A with `invariant false` fails (b)** -- by the start
    obligation: the declared initial memory would have to satisfy `false`. -/
theorem probeA_falsch_inv_nicht : probeA_falsch_inv :=
  fun _ _ _ h => Bool.false_ne_true (h.start.sperren ())

/-- The P1 program passes the checker (with `haupt` declared): the refutation above is by
    (b), not by (a). -/
theorem p1_akzeptiert : Akzeptiert paP sFalsch zFs [()] [.inl ()] [zHaupt] = true := by decide

/-- **P1, the whole class at once**: no program whatever has an unsatisfiable lock-invariant
    family and meets (b). -/
theorem unerfuellbar_widerlegt {D : Deklaration} (E : Einheit D)
    (hS : ¬ ∃ s : Speicher D, ∀ L, E.S.inv L s = true) : ¬ NutzerPflicht E :=
  fun h => hS ⟨E.sp0, h.start.sperren⟩

theorem probeD_widerlegt_gilt : probeD_widerlegt := by
  rintro ⟨P, S, Q, st, s⟩ hP h
  obtain rfl : P = fvP false := hP
  exact probeD_nicht Q S h.logik.2.1 s h.start.sperren (fun passes f => (h.logik.1 passes f).1)

theorem probeD_wahr_widerlegt_gilt : probeD_wahr_widerlegt := by
  rintro ⟨P, S, Q, st, s⟩ hP h
  obtain rfl : P = fvP true := hP
  exact fwP_nicht Q S h.logik.2.1 s h.start.sperren (fun passes f => (h.logik.1 passes f).1)

theorem tabelle_widerlegt_gilt : tabelle_widerlegt := by
  rintro ⟨P, S, Q, st, s⟩ hP h
  obtain rfl : P = ivPschlecht := hP
  have hI : InvGutS ivPschlecht 0 Q S ivSetze := (h.logik.1 0 ivSetze).2.1
  have hrun := Endblock.execH_ohne S ivO (fun L σ => mischU S L σ s) 0 (rufAusV [])
    (ivPschlecht.rumpf ivSetze) rfl (ivSp.welt []) .nil
  have h3 := hI ivO (gutO_rahmenO ivO_gut) ivO_lokal (fun a => nomatch a)
    (fun L σ => mischU S L σ s) (havocOk_misch_lokal h.logik.2.1 (fun _ _ => s)
      (fun L _ => h.start.sperren L))
    (rufAusV []) (rufAusV_rahmen (vertraegeOkR_nil ivPschlecht))
    (rufAusV_ohneVorbedingung (vertraegeOkR_nil ivPschlecht).1) (ivSp.welt []) .nil rfl _ _
    (hrun.trans rfl) () (List.mem_singleton.mpr rfl) rfl
  revert h3
  simp [InvHaelt, ivPschlecht, ivP, ivInv, ivIdx, ivWert, eval, World.storeSlot, World.merke,
    World.lese, World.schreibSlot, Zahl.weiter, ivSp, Speicher.welt]
  decide

/-! ## 2. Refutations of (a) -/

theorem ungeschuetzt_abgelehnt_gilt : ungeschuetzt_abgelehnt := by
  intro D _ P S fs ws w₁ w₂ c h₁ h₂ hne hc hw hB hA
  rcases (hA.fuss w₁).1 c hc with h | ⟨L, hL, _⟩
  · rcases Bool.or_eq_true_iff.mp h with h | h
    · obtain ⟨L, hL, _⟩ := sigB_ok h
      exact hB L hL
    · unfold lokW at h
      have hg := @of_decide_eq_true _ (Classical.propDecidable _) h
      have := hg w₁ h₁ w₂ h₂ hne w₁ w₂ (reachB_wurzel P fs w₁) (fuss_teilG P w₁ hc)
        (reachB_wurzel P fs w₂)
      rw [hw] at this
      cases this
  · exact hB L hL

/-! ## 3. Verdict P2: the starts are the program's -/

/-- **The two writers of `akD` never both run** (verdict P2, closed): in ANY program over
    `akD` (for instance `akP3`, where nothing reads the table) that the checker accepts, no
    runtime start (A4) runs `a` on one thread and `b` on another -- both would have to be
    declared (`laufzeit_nur_erklaert`), and two declared writers of the unguarded table are
    refused (`zwei_schreiber_abgelehnt_gilt`). Before 2026-09-15 `ws = []` was a free knob:
    the statement then accepted `akP3` and simply did not say which starts were its own. -/
theorem akD_kein_zweiter_schreiber (E : Einheit akD) (fs : List akD.Fn)
    (hA : AkzeptiertSpec E.P E.S fs E.ws) {sp : Speicher akD.mitRuhe}
    {init : Faden → Σ f : akD.mitRuhe.Fn, Env akD.mitRuhe (akD.mitRuhe.params f)}
    (hL : Laufzeit E sp init) : ¬ ∃ t u, (init t).1 = some akA ∧ (init u).1 = some akB := by
  rintro ⟨t, u, ht, hu⟩
  exact zwei_schreiber_abgelehnt_gilt akD E.P E.S fs E.ws akA akB (.inl ())
    (laufzeit_nur_erklaert hL t akA ht) (laufzeit_nur_erklaert hL u akB hu) (by decide) rfl rfl
    (fun _ h => absurd h List.not_mem_nil) (fun ⟨_, h, _⟩ => by cases h) hA

/-- The same code DECLARING no start is a different program: the checker accepts it, and the
    statement then speaks about the runtime's root on every thread and nothing else. -/
theorem akP3_ohne_starts :
    Akzeptiert akP3 akS akFs [()] akCs [] = true ∧
    ∀ (sp : Speicher akD.mitRuhe)
      (init : Faden → Σ f : akD.mitRuhe.Fn, Env akD.mitRuhe (akD.mitRuhe.params f)),
      Laufzeit ⟨akP3, akS, axWahr akD, [], akSp⟩ sp init → ∀ t, (init t).1 = none :=
  ⟨by decide, fun _ _ hL t => laufzeit_ohne_starts rfl hL t⟩

/-! ## 4. The two-thread program -/

/-- Every declared start runs on some thread of the runtime's exact start. -/
theorem initRuhe_laeuft {D : Deklaration} (E : Einheit D) :
    ∀ w ∈ E.ws, ∃ t : Faden, (initRuhe E.starts t).1 = some w := by
  intro w hw
  obtain ⟨⟨w', ρ⟩, ha, rfl⟩ := List.mem_map.mp hw
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
  refine ⟨i, ?_⟩
  unfold initRuhe
  rw [hi]

theorem mE_nutzerPflicht : NutzerPflicht mE :=
  ⟨⟨fun passes f => ⟨mP_koerper_alle passes f, mP_inv_alle passes f,
      invGutGrund_ohneGrund (by cases f <;> rfl)⟩, mSI_ok.2, axEnsLokal_wahr⟩,
    ⟨fun L => by cases L; decide, fun a ha => by
      simp only [mE, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> rfl⟩⟩

theorem zweiFaeden_erfuellbar_gilt : zweiFaeden_erfuellbar :=
  ⟨⟨mFs, mFs_voll⟩, akzeptiertSpec_of mFs_voll mLocks_voll mCs_voll mP_akzeptiert,
    mE_nutzerPflicht, ⟨mO, mO_gut, mO_lokal, axVertragO_wahr mO⟩,
    speicherR mSp, _, laufzeit_initRuhe mE (by decide), initRuhe_laeuft mE⟩

/-- **The runtime's start of `mE` moves memory**: one step of thread 0 (`hauptA`'s first
    statement `privA[0] = 7`) changes the shared memory. -/
theorem zweiFaeden_bewegt_gilt : zweiFaeden_bewegt := by
  obtain ⟨M1, s1, hZ1⟩ := w_blatt (P := mP.mitRuhe) (O := mO.mitRuhe) (passes := 0)
    (M := RufStartG mP.mitRuhe (speicherR mSp) (initRuhe [⟨mHauptA, .nil⟩, ⟨mHauptB, .nil⟩]))
    (f := 0) rfl _ _ _ rfl rfl (fun _ h => nomatch h) _ _
    (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _) ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  refine ⟨speicherR mSp, _, 0, M1, laufzeit_initRuhe mE (by decide), .schritt _ _ _ .start s1, ?_⟩
  intro h
  have e := congrArg (fun s : Speicher mD.mitRuhe => (s.slots MTab.privA 0 () : Zahl 0 100).n) h
  rw [hZ1.2] at e
  revert e
  decide

/-! ## 5. Probes B and C -/

theorem zLs_voll : ∀ L : zD.Lock, L ∈ [()] := fun L => by cases L; exact List.mem_singleton_self _

theorem zCs_voll : ∀ c : zD.Tab ⊕ zD.Glob, c ∈ ([.inl ()] : List (zD.Tab ⊕ zD.Glob)) := by
  intro c
  rcases c with ⟨⟩ | e
  · exact List.mem_singleton_self _
  · exact nomatch e

theorem zInvGutS {P : Programm zD} {passes : Nat} {Q : AxEns zD} {S : SperrInv zD} (f : zD.Fn) :
    InvGutS P passes Q S f := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i hi
  exact absurd hi List.not_mem_nil

theorem zInvGutGrund {P : Programm zD} {passes : Nat} {Q : AxEns zD} {S : SperrInv zD}
    (f : zD.Fn) : InvGutGrund P passes Q S f :=
  invGutGrund_ohne (fun _ hi => absurd hi List.not_mem_nil)

theorem zS_lokal : SperrInvLokal zS := fun _ _ _ _ => rfl

theorem zPB_akzeptiert : Akzeptiert zPB zS zFs [()] [.inl ()] [zHaupt] = true := by decide

theorem zPC_akzeptiert : Akzeptiert zPC zS zFs [()] [.inl ()] [zHaupt] = true := by decide

/-- The start obligation of a `zD` program declaring `haupt` from `zSp` under `zS`. -/
theorem zStartPflicht (E : Einheit zD) (hS : E.S = zS) (hst : E.starts = [⟨zHaupt, .nil⟩])
    (hreq : ReqAmEintritt E.P zHaupt (E.sp0.welt []) .nil) : StartPflicht E :=
  ⟨fun L => by rw [hS]; rfl, fun a ha => by
    rw [hst] at ha
    obtain rfl := List.mem_singleton.mp ha
    exact hreq⟩

/-- **Probe B satisfies every premise group with `haupt` as a DECLARED start** (it runs on
    thread 0; the root on every other thread). -/
theorem probeB_erfuellbar_haupt : Erfuellbar zEB ⟨zFs, zFs_voll⟩ :=
  ⟨akzeptiertSpec_of zFs_voll zLs_voll zCs_voll zPB_akzeptiert,
    ⟨⟨fun passes f => ⟨koerperGutS_alle zFs_voll (by decide) zPB_koerper passes f, zInvGutS f,
      zInvGutGrund f⟩, zS_lokal, axEnsLokal_wahr⟩, zStartPflicht zEB rfl rfl rfl⟩,
    ⟨zO, zO_gut, zO_lokal, axVertragO_wahr zO⟩, _, _, laufzeit_initRuhe zEB (by decide),
    initRuhe_laeuft zEB⟩

theorem probeC_erfuellbar_haupt : Erfuellbar zEC ⟨zFs, zFs_voll⟩ :=
  ⟨akzeptiertSpec_of zFs_voll zLs_voll zCs_voll zPC_akzeptiert,
    ⟨⟨fun passes f => ⟨koerperGutS_alle zFs_voll (by decide) zPC_koerper passes f, zInvGutS f,
      zInvGutGrund f⟩, zS_lokal, axEnsLokal_wahr⟩, zStartPflicht zEC rfl rfl rfl⟩,
    ⟨zO, zO_gut, zO_lokal, axVertragO_wahr zO⟩, _, _, laufzeit_initRuhe zEC (by decide),
    initRuhe_laeuft zEC⟩

theorem probeB_erfuellbar_gilt : probeB_erfuellbar := ⟨_, probeB_erfuellbar_haupt⟩

theorem probeC_erfuellbar_gilt : probeC_erfuellbar := ⟨_, probeC_erfuellbar_haupt⟩

/-! ## 6. The assembled goal, applied -/

/-- **`gabbro_ziel` applied to the two-thread program**: on the runtime's start with both
    declared starts, at a machine reached in one step with CHANGED memory, every leg of
    `Ziel` holds -- by the theorem, not by hand. -/
theorem gabbro_ziel_zeuge : ∃ (sp : Speicher mD.mitRuhe)
    (init : Faden → Σ f : mD.mitRuhe.Fn, Env mD.mitRuhe (mD.mitRuhe.params f))
    (M : RufMaschineG mD.mitRuhe),
    Laufzeit mE sp init ∧
    RufErreichbarG mE.P.mitRuhe mO.mitRuhe 0 (RufStartG mE.P.mitRuhe sp init) M ∧
    M.speicher ≠ sp ∧
    Ziel mE.P.mitRuhe mE.S.mitRuhe mO.mitRuhe 0 (RufStartG mE.P.mitRuhe sp init) M := by
  obtain ⟨M1, s1, hZ1⟩ := w_blatt (P := mP.mitRuhe) (O := mO.mitRuhe) (passes := 0)
    (M := RufStartG mP.mitRuhe (speicherR mSp) (initRuhe [⟨mHauptA, .nil⟩, ⟨mHauptB, .nil⟩]))
    (f := 0) rfl _ _ _ rfl rfl (fun _ h => nomatch h) _ _
    (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _) ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hL : Laufzeit mE (speicherR mSp) (initRuhe [⟨mHauptA, .nil⟩, ⟨mHauptB, .nil⟩]) :=
    laufzeit_initRuhe mE (by decide)
  refine ⟨speicherR mSp, _, M1, hL, .schritt _ _ _ .start s1, ?_, ?_⟩
  · intro h
    have e := congrArg (fun s : Speicher mD.mitRuhe => (s.slots MTab.privA 0 () : Zahl 0 100).n) h
    rw [hZ1.2] at e
    revert e
    decide
  · exact gabbro_ziel akzeptiert_pruefer mD mE ⟨mFs, mFs_voll⟩ ⟨[()], mLocks_voll⟩
      ⟨mCs, mCs_voll⟩
      (by show Akzeptiert mP mSI mFs [()] mCs [mHauptA, mHauptB] = true; exact mP_akzeptiert)
      mE_nutzerPflicht mO ⟨mO_gut, mO_lokal, axVertragO_wahr mO⟩ 0 _ _ hL M1
      (.schritt _ _ _ .start s1)

#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_zeuge
#print axioms Gabbro.Grammatik.Zielsatz.probeA_widerlegt_gilt
#print axioms Gabbro.Grammatik.Zielsatz.probeA_falsch_inv_nicht
#print axioms Gabbro.Grammatik.Zielsatz.p1_akzeptiert
#print axioms Gabbro.Grammatik.Zielsatz.unerfuellbar_widerlegt
#print axioms Gabbro.Grammatik.Zielsatz.probeD_widerlegt_gilt
#print axioms Gabbro.Grammatik.Zielsatz.probeD_wahr_widerlegt_gilt
#print axioms Gabbro.Grammatik.Zielsatz.tabelle_widerlegt_gilt
#print axioms Gabbro.Grammatik.Zielsatz.ungeschuetzt_abgelehnt_gilt
#print axioms Gabbro.Grammatik.Zielsatz.zwei_schreiber_abgelehnt_gilt
#print axioms Gabbro.Grammatik.Zielsatz.akD_kein_zweiter_schreiber
#print axioms Gabbro.Grammatik.Zielsatz.akP3_ohne_starts
#print axioms Gabbro.Grammatik.Zielsatz.zweiFaeden_erfuellbar_gilt
#print axioms Gabbro.Grammatik.Zielsatz.zweiFaeden_bewegt_gilt
#print axioms Gabbro.Grammatik.Zielsatz.probeB_erfuellbar_gilt
#print axioms Gabbro.Grammatik.Zielsatz.probeC_erfuellbar_gilt
#print axioms Gabbro.Grammatik.Zielsatz.probeB_erfuellbar_haupt
#print axioms Gabbro.Grammatik.Zielsatz.probeC_erfuellbar_haupt

end Gabbro.Grammatik.Zielsatz
