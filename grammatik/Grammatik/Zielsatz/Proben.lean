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
  * `probeB_erfuellbar_gilt`, `probeC_erfuellbar_gilt` -- probes B/C, through the stronger
    `probeB_erfuellbar_haupt`/`probeC_erfuellbar_haupt`: `haupt` is a DECLARED start and
    runs on thread 0 (`initRuhe [haupt]`), the runtime's root on every other thread. (The
    propositions ask only `∃ ws`; `ws = []` would satisfy them with the root on every
    thread, where the bodies never run -- the witness here avoids that.)
-/
import Grammatik.Zielsatz.SpecProben
import Grammatik.Zielsatz.RuheZeuge
import Grammatik.ZielOrtInvGrund

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

/-! ## 1. Refutations of (b) -/

/-- The user obligation makes the family well-formed. -/
theorem sperrInvOk_of_nutzer {D : Deklaration} {P : Programm D} {S : SperrInv D} {Q : AxEns D}
    (hB : ∀ L c, c ∈ S.orte L → Bewacht c L) (h : NutzerPflicht P S Q) : SperrInvOk S :=
  ⟨hB, h.2.1⟩

theorem probeA_widerlegt_gilt : probeA_widerlegt := by
  intro S Q hB ⟨s, hs⟩ h
  exact paP_nicht_sperre Q S (sperrInvOk_of_nutzer hB h) s hs zHaupt (h.1 0 zHaupt).1

theorem probeD_widerlegt_gilt : probeD_widerlegt := by
  intro S Q hB ⟨s, hs⟩ h
  exact probeD_nicht Q S (sperrInvOk_of_nutzer hB h) s hs (fun passes f => (h.1 passes f).1)

theorem probeD_wahr_widerlegt_gilt : probeD_wahr_widerlegt := by
  intro S Q hB ⟨s, hs⟩ h
  exact fwP_nicht Q S (sperrInvOk_of_nutzer hB h) s hs (fun passes f => (h.1 passes f).1)

theorem tabelle_widerlegt_gilt : tabelle_widerlegt := by
  intro S Q hB ⟨s, hs⟩ h
  have hS := sperrInvOk_of_nutzer hB h
  have hI : InvGutS ivPschlecht 0 Q S ivSetze := (h.1 0 ivSetze).2.1
  have hrun := Endblock.execH_ohne S ivO (fun L σ => mischU S L σ s) 0 (rufAusV [])
    (ivPschlecht.rumpf ivSetze) rfl (ivSp.welt []) .nil
  have h3 := hI ivO (gutO_rahmenO ivO_gut) ivO_lokal (fun a => nomatch a)
    (fun L σ => mischU S L σ s) (havocOk_misch hS (fun _ _ => s) (fun L _ => hs L))
    (rufAusV []) (rufAusV_rahmen (vertraegeOkR_nil ivPschlecht))
    (rufAusV_ohneVorbedingung (vertraegeOkR_nil ivPschlecht).1) (ivSp.welt []) .nil rfl _ _
    (hrun.trans rfl) () (List.mem_singleton.mpr rfl) rfl
  revert h3
  simp [InvHaelt, ivPschlecht, ivP, ivInv, ivIdx, ivWert, eval, World.storeSlot, World.merke,
    World.lese, World.schreibSlot, Zahl.weiter, ivSp, Speicher.welt]
  decide

/-! ## 2. Refutation of (a) -/

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

/-! ## 3. The two-thread program -/

theorem mP_nutzerPflicht : NutzerPflicht mP mSI (axWahr mD) :=
  ⟨fun passes f => ⟨mP_koerper_alle passes f, mP_inv_alle passes f,
    invGutGrund_ohneGrund (by cases f <;> rfl)⟩, mSI_ok.2, axEnsLokal_wahr⟩

theorem zweiFaeden_erfuellbar_gilt : zweiFaeden_erfuellbar :=
  ⟨⟨mFs, mFs_voll⟩, akzeptiertSpec_of mFs_voll mLocks_voll mCs_voll mP_akzeptiert,
    mP_nutzerPflicht, ⟨mO, mO_gut, mO_lokal, axVertragO_wahr mO⟩,
    speicherR mSp, _, mP_mitRuhe_start⟩

/-- **The admissible start of `mP.mitRuhe` moves memory**: one step of thread 0 (`hauptA`'s
    first statement `privA[0] = 7`) changes the shared memory. -/
theorem zweiFaeden_bewegt_gilt : zweiFaeden_bewegt := by
  obtain ⟨M1, s1, hZ1⟩ := w_blatt (P := mP.mitRuhe) (O := mO.mitRuhe) (passes := 0)
    (M := RufStartG mP.mitRuhe (speicherR mSp) (initRuhe [⟨mHauptA, .nil⟩, ⟨mHauptB, .nil⟩]))
    (f := 0) rfl _ _ _ rfl rfl (fun _ h => nomatch h) _ _
    (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _) ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  refine ⟨speicherR mSp, _, ⟨mFs, mFs_voll⟩, 0, M1, mP_mitRuhe_start, .schritt _ _ _ .start s1, ?_⟩
  intro h
  have e := congrArg (fun s : Speicher mD.mitRuhe => (s.slots MTab.privA 0 () : Zahl 0 100).n) h
  rw [hZ1.2] at e
  revert e
  decide

/-! ## 4. Probes B and C -/

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

/-- `haupt` declared as the start of thread 0, the runtime's root everywhere else. -/
theorem zHauptStartZ (P : Programm zD) (hreq : ReqAmEintritt P zHaupt (zSp.welt []) .nil) :
    StartZulaessig P.mitRuhe zS.mitRuhe (fsRuhe zFs) (wsRuhe [zHaupt]) (speicherR zSp)
      (initRuhe [⟨zHaupt, .nil⟩]) :=
  startZulaessig_mitRuhe_P P [⟨zHaupt, .nil⟩] zSp
    (fun a ha => by rw [List.mem_singleton.mp ha]; exact List.mem_singleton_self _)
    (by decide) (fun a ha => by rw [List.mem_singleton.mp ha]; exact hreq)
    (fun _ => rfl)

/-- **Probe B satisfies every premise group with `haupt` as a DECLARED start** (it runs on
    thread 0; the root on every other thread). -/
theorem probeB_erfuellbar_haupt :
    Erfuellbar zPB zS (axWahr zD) ⟨zFs, zFs_voll⟩ [zHaupt] :=
  ⟨akzeptiertSpec_of zFs_voll zLs_voll zCs_voll zPB_akzeptiert,
    ⟨fun passes f => ⟨koerperGutS_alle zFs_voll (by decide) zPB_koerper passes f, zInvGutS f,
      zInvGutGrund f⟩, zS_lokal, axEnsLokal_wahr⟩,
    ⟨zO, zO_gut, zO_lokal, axVertragO_wahr zO⟩, _, _, zHauptStartZ zPB rfl⟩

theorem probeC_erfuellbar_haupt :
    Erfuellbar zPC zS (axWahr zD) ⟨zFs, zFs_voll⟩ [zHaupt] :=
  ⟨akzeptiertSpec_of zFs_voll zLs_voll zCs_voll zPC_akzeptiert,
    ⟨fun passes f => ⟨koerperGutS_alle zFs_voll (by decide) zPC_koerper passes f, zInvGutS f,
      zInvGutGrund f⟩, zS_lokal, axEnsLokal_wahr⟩,
    ⟨zO, zO_gut, zO_lokal, axVertragO_wahr zO⟩, _, _, zHauptStartZ zPC rfl⟩

theorem probeB_erfuellbar_gilt : probeB_erfuellbar := ⟨_, _, probeB_erfuellbar_haupt⟩

theorem probeC_erfuellbar_gilt : probeC_erfuellbar := ⟨_, _, probeC_erfuellbar_haupt⟩

#print axioms Gabbro.Grammatik.Zielsatz.probeA_widerlegt_gilt
#print axioms Gabbro.Grammatik.Zielsatz.probeD_widerlegt_gilt
#print axioms Gabbro.Grammatik.Zielsatz.probeD_wahr_widerlegt_gilt
#print axioms Gabbro.Grammatik.Zielsatz.tabelle_widerlegt_gilt
#print axioms Gabbro.Grammatik.Zielsatz.ungeschuetzt_abgelehnt_gilt
#print axioms Gabbro.Grammatik.Zielsatz.zweiFaeden_erfuellbar_gilt
#print axioms Gabbro.Grammatik.Zielsatz.zweiFaeden_bewegt_gilt
#print axioms Gabbro.Grammatik.Zielsatz.probeB_erfuellbar_gilt
#print axioms Gabbro.Grammatik.Zielsatz.probeC_erfuellbar_gilt
#print axioms Gabbro.Grammatik.Zielsatz.probeB_erfuellbar_haupt
#print axioms Gabbro.Grammatik.Zielsatz.probeC_erfuellbar_haupt

end Gabbro.Grammatik.Zielsatz
