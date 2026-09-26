/-
  File:      Grammatik/Zielsatz/VerbundZeuge.lean
  Subject:   The witnesses of linking (Opus agent E, 2026-09-26): `GabbroZielVerbund` is not
             vacuous in either direction.

  * POSITIVE (`vz_ziel`, `vz_lauf_zeuge`). A LIBRARY `vzE2` owns `wrap`, `lies`, `einzahlen`:
    `wrap` holds the lock by signature, calls `lies` and `einzahlen`, and `einzahlen` WRITES the
    lock-guarded table `konto`; `wrap`'s exported contract is `ensures konto[0] == 100` (probe
    B, ZielOrtSperreZeuge.lean). An APP `vzE1` owns `haupt() = locks { wrap() }` and declares it
    TWICE (`concurrent { haupt, haupt }`); its view of the library is three leaf placeholders
    with the library's heads. Each unit is accepted ALONE by the concrete checker
    (`vz_app_akzeptiert`, `vz_bib_akzeptiert`), the link check accepts (`vz_schnittstelle`), each
    user proves only the bodies the unit owns (`vz_nutzer1`, `vz_nutzer2`), the hardware
    assumptions are the same (`rfl`). `vz_ziel`: every leg of `ZielF` on every reachable
    thread machine of the linked program, from `gabbro_ziel_verbund`. Non-degenerate: the app's
    own graph does NOT reach the writer (`reachB vzApp … zEin = false`: the placeholder is a
    leaf), the COMPOSED hull does (`vz_huelle_schreibt`), so the race leg really speaks about
    the library's write, reached from two app threads; the linked unit is fix lane F10's pool
    (`vz_verbinde_gleich`), and on its run in which both app threads step and thread 0 takes
    the lock, `Ziel` holds (`vz_lauf_zeuge`).
  * REFUSAL, FOOTPRINTS (`vm_abgelehnt`). The library's `pruefeA` READS the unguarded table
    `privB` in its body; its contract does not name it. The app (the two-thread fixture `mE`)
    calls `pruefeA` from `hauptA`, and `hauptB` writes `privB`. Each unit alone is accepted;
    the link check refuses -- `privB` is relied on as thread-local (`lokBedarfB`) and is not,
    over the composed hulls (`getrenntVB`) -- and the whole-program checker refuses the linked
    program for the same reason. `vm_abgelehnt_spec`: no `SchnittstelleSpec`.
  * REFUSAL, CONTRACT (`vz_vertrag_zu_schwach`). The library compiled against `zP` exports
    `wrap … ensures true`; the app relies on `ensures konto[0] == 100`. The library alone is
    accepted; there is no link declaration for the pair (`¬ Verbindbar`, at `ensures`) -- the
    Rust `N502`.
-/
import Grammatik.Zielsatz.Verbund
import Grammatik.Zielsatz.PoolZeuge
import Grammatik.Zielsatz.AkzeptiertZeuge

namespace Gabbro.Grammatik.Zielsatz
open Gabbro.Grammatik

/-! ## 1. POSITIVE: a library exports a lock-guarded table writer, an app calls it from two
    threads -/

/-- Ownership: the app (unit 1) owns `haupt`; the library (unit 2) owns `einzahlen`, `lies`
    and `wrap`. -/
def vzE : zD.Fn → Bool
  | .haupt => true
  | _ => false

/-- The app's placeholder for `einzahlen`: a leaf. -/
def vzStubEin : Endblock zD (vertragVon zD zEin) false [] zL := .ret .keine (by rfl)
/-- The app's placeholder for `lies`: a leaf. -/
def vzStubLies : Endblock zD (vertragVon zD zLies) false [] zL := .ret (.wert zHundert) (by rfl)
/-- The app's placeholder for `wrap`: a leaf. -/
def vzStubWrap : Endblock zD (vertragVon zD zWrap) false [] zL := .ret .keine (by rfl)
/-- The library's placeholder for `haupt`: a leaf. -/
def vzStubHaupt : Endblock zD (vertragVon zD zHaupt) false [] [] := .ret .keine List.Perm.nil

/-- The app's program: `haupt() = locks { wrap() }` (its own body), probe B's contracts
    (the IMPORTED `wrap` ensures `konto[0] == 100`), placeholders for the library. -/
def vzApp : Programm zD := mitRumpf zPB fun
  | .haupt => zRumpfHaupt
  | .ein => vzStubEin
  | .lies => vzStubLies
  | .wrap => vzStubWrap

/-- The library's program: `wrap`, `lies`, `einzahlen` (its own bodies; `einzahlen` WRITES the
    lock-guarded table `konto`), a placeholder for `haupt`. -/
def vzBib : Programm zD := mitRumpf zPB fun
  | .haupt => vzStubHaupt
  | .ein => zRumpfEin
  | .lies => zRumpfLies
  | .wrap => zRumpfWrap

/-- The app: `concurrent { haupt, haupt }`. -/
def vzE1 : Einheit zD := ⟨vzApp, zS, axWahr zD, [⟨zHaupt, .nil⟩, ⟨zHaupt, .nil⟩], zSp, []⟩

/-- The library: no thread of its own. -/
def vzE2 : Einheit zD := ⟨vzBib, zS, axWahr zD, [], zSp, []⟩

/-- Each unit is accepted ALONE by the concrete checker. -/
theorem vz_app_akzeptiert :
    Akzeptiert vzApp zS zFs [()] [.inl ()] [zHaupt, zHaupt] = true := by decide

theorem vz_bib_akzeptiert : Akzeptiert vzBib zS zFs [()] [.inl ()] [] = true := by decide

theorem vz_verbindbar : Verbindbar vzE1 vzE2 := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **The link check accepts.** -/
theorem vz_schnittstelle : schnittstelleB zFs [.inl ()] vzE vzE1 vzE2 = true := by decide

/-- Non-degenerate: the composed hull of the app's thread root `haupt` reaches into the
    library down to `einzahlen`, which WRITES `konto`; the imported `wrap` promises
    `konto[0] == 100`. -/
theorem vz_huelle_schreibt :
    HuelleV zFs vzE vzE1 vzE2 zHaupt zEin ∧
      TraegerSchreibt zEin (.inl () : zD.Tab ⊕ zD.Glob) = true ∧
      reachB vzApp zFs zHaupt zEin = false :=
  ⟨(huelleB_iff zFs_voll).mp (by decide), rfl, by decide⟩

theorem vz_nutzer1 : NutzerTeil vzE vzE1 := by
  refine ⟨⟨fun passes f hf => ?_, zS_lokal, axEnsLokal_wahr⟩, ⟨fun _ => rfl, fun a ha => ?_⟩⟩
  · cases f <;> simp [vzE] at hf
    obtain ⟨k, i, g⟩ := zPool_nutzerPflicht.logik.1 passes zHaupt
    exact ⟨(koerper_mitRumpf2 zPB _ zPB.rumpf passes _ _ zHaupt rfl).mpr k,
      (invGutS_mitRumpf2 zPB _ zPB.rumpf passes _ _ zHaupt rfl).mpr i,
      (invGutGrund_mitRumpf2 zPB _ zPB.rumpf passes _ _ zHaupt rfl).mpr g⟩
  · simp only [vzE1, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> rfl

theorem vz_nutzer2 : NutzerTeil (fun f => !vzE f) vzE2 := by
  refine ⟨⟨fun passes f _ => ?_, zS_lokal, axEnsLokal_wahr⟩, ⟨fun _ => rfl, fun a ha => ?_⟩⟩
  · obtain ⟨k, i, g⟩ := zPool_nutzerPflicht.logik.1 passes f
    cases f
    · exact ⟨(koerper_mitRumpf2 zPB _ zPB.rumpf passes _ _ zEin rfl).mpr k,
        (invGutS_mitRumpf2 zPB _ zPB.rumpf passes _ _ zEin rfl).mpr i,
        (invGutGrund_mitRumpf2 zPB _ zPB.rumpf passes _ _ zEin rfl).mpr g⟩
    · exact ⟨(koerper_mitRumpf2 zPB _ zPB.rumpf passes _ _ zLies rfl).mpr k,
        (invGutS_mitRumpf2 zPB _ zPB.rumpf passes _ _ zLies rfl).mpr i,
        (invGutGrund_mitRumpf2 zPB _ zPB.rumpf passes _ _ zLies rfl).mpr g⟩
    · exact ⟨(koerper_mitRumpf2 zPB _ zPB.rumpf passes _ _ zWrap rfl).mpr k,
        (invGutS_mitRumpf2 zPB _ zPB.rumpf passes _ _ zWrap rfl).mpr i,
        (invGutGrund_mitRumpf2 zPB _ zPB.rumpf passes _ _ zWrap rfl).mpr g⟩
    · simp [vzE] at *
  · simp [vzE2] at ha

/-- **THE LINKED GOAL**: every leg of `ZielF` on every reachable thread machine of the linked
    program, from `gabbro_ziel_verbund` -- the two units' verdicts, the link check, the two
    units' user duties, the SAME hardware assumptions. -/
theorem vz_ziel (passes : Nat) (lebt0 : Faden → Bool) (K : FadenMaschine zD.mitRuhe)
    (hK : FadenErreichbar (verbinde vzE vzE1 vzE2).P.mitRuhe zO.mitRuhe passes
      (FadenStart (verbinde vzE vzE1 vzE2).P.mitRuhe (speicherR zSp)
        (initRuhe (verbinde vzE vzE1 vzE2).starts) lebt0) K) :
    ZielF (verbinde vzE vzE1 vzE2).P.mitRuhe (verbinde vzE vzE1 vzE2).S.mitRuhe zO.mitRuhe passes
      (RufStartG (verbinde vzE vzE1 vzE2).P.mitRuhe (speicherR zSp)
        (initRuhe (verbinde vzE vzE1 vzE2).starts)) K :=
  gabbro_ziel_verbund akzeptiert_pruefer zD vzE1 vzE2 vzE ⟨zFs, zFs_voll⟩ ⟨[()], zLs_voll⟩
    ⟨[.inl ()], zCs_voll⟩
    (by show Akzeptiert vzApp zS zFs [()] [.inl ()] [zHaupt, zHaupt] = true
        exact vz_app_akzeptiert)
    (by show Akzeptiert vzBib zS zFs [()] [.inl ()] [] = true
        exact vz_bib_akzeptiert) vz_verbindbar
    ((schnittstelleB_iff zFs_voll zCs_voll).mp vz_schnittstelle) vz_nutzer1 vz_nutzer2 rfl zO
    ⟨zO_gut, zO_lokal, axVertragO_wahr zO⟩ passes _ _ (laufzeit_initRuhe _) lebt0 K hK

/-- The linked unit IS the pool of fix lane F10 (`zPool`): the link reassembles the program. -/
theorem vz_verbinde_gleich : verbinde vzE vzE1 vzE2 = zPool := by
  have hr : (verbindeP vzE vzE1 vzE2) = zPB := by
    show mitRumpf vzApp _ = zPB
    unfold mitRumpf
    have : (fun f => if vzE f = true then vzE1.P.rumpf f else vzE2.P.rumpf f) = zPB.rumpf := by
      funext f
      cases f <;> rfl
    rw [this]
    rfl
  unfold verbinde
  rw [hr]
  rfl

/-- **THE RUN**: on the linked program both app threads run `haupt`; thread 0 unfolds its body,
    thread 1 unfolds its body, thread 0 takes the lock -- and at that machine `gabbro_ziel_verbund`
    gives every leg of `Ziel` (race freedom over the library's table writer included). -/
theorem vz_lauf_zeuge : ∃ M3 : RufMaschineG zD.mitRuhe,
    RufErreichbarG (verbinde vzE vzE1 vzE2).P.mitRuhe zO.mitRuhe 0
      (RufStartG (verbinde vzE vzE1 vzE2).P.mitRuhe (speicherR zSp)
        (initRuhe (verbinde vzE vzE1 vzE2).starts)) M3 ∧
    (initRuhe (verbinde vzE vzE1 vzE2).starts 0).1 = some zHaupt ∧
    (initRuhe (verbinde vzE vzE1 vzE2).starts 1).1 = some zHaupt ∧
    (() : zD.mitRuhe.Lock) ∈ offen (M3.faeden 0).spur ∧
    Ziel (verbinde vzE vzE1 vzE2).P.mitRuhe (verbinde vzE vzE1 vzE2).S.mitRuhe zO.mitRuhe 0
      (RufStartG (verbinde vzE vzE1 vzE2).P.mitRuhe (speicherR zSp)
        (initRuhe (verbinde vzE vzE1 vzE2).starts)) M3 := by
  obtain ⟨M1, M2, M3, _, h0, h1, s1, s2, s3, hheld, _⟩ := pool_ziel_zeuge
  have hr : RufErreichbarG zPool.P.mitRuhe zO.mitRuhe 0 zPoolM0 M3 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3
  have hz := vz_ziel 0 (fun _ => true) (FadenMaschine.alleLebend M3)
  rw [vz_verbinde_gleich] at hz ⊢
  exact ⟨M3, hr, h0, h1, hheld, (hz (fadenErreichbar_von_G hr)).g⟩

/-! ## 2. REFUSAL: footprints that do not compose -/

/-- Ownership: the library owns `pruefeA`, the app everything else. -/
def vmE : mD.Fn → Bool
  | .pruefeA => false
  | _ => true

/-- The library's `pruefeA` READS `privB` (unguarded) in its body: `let _ = privB[0]; return`.
    Its contract (`requires privA[0] == 7`) does not mention `privB`, so the app cannot see the
    read. -/
def vmLeser : Endblock mD (vertragVon mD mPruefeA) false [] [] :=
  .bind (.slot MTab.privB () mI0 (mDarfB _)) (.ret .keine List.Perm.nil)

/-- The library's program: `pruefeA` reads `privB`; leaves for the app's functions. -/
def vmBib : Programm mD := mitRumpf mP fun
  | .setze => .ret .keine (by rfl)
  | .hauptA => .ret .keine List.Perm.nil
  | .hauptB => .ret .keine List.Perm.nil
  | .pruefeA => vmLeser
  | .ruhe => .ret .keine List.Perm.nil

/-- The library as a unit: no thread of its own. -/
def vmE2 : Einheit mD := ⟨vmBib, mSI, axWahr mD, [], mSp, []⟩

/-- **Refused at the link, although each unit alone is accepted.** The app is the two-thread
    fixture `mE` (`hauptA` calls the imported `pruefeA`, `hauptB` writes `privB`); its
    placeholder for `pruefeA` reads nothing, so ALONE it is accepted. The library alone is
    accepted (no thread of its own reads against a writer). Linked, thread `hauptA` reaches the
    library's `pruefeA`, which reads `privB` while thread `hauptB` writes it: `privB` is relied
    on as thread-local (`LokBedarf`), and over the composed hulls it is not (`GetrenntV`
    fails). The whole-program checker refuses the linked program for the same reason. -/
theorem vm_abgelehnt :
    Akzeptiert mE.P mE.S mFs [()] mCs mE.ws = true ∧
    Akzeptiert vmBib mSI mFs [()] mCs [] = true ∧
    Verbindbar mE vmE2 ∧
    schnittstelleB mFs mCs vmE mE vmE2 = false ∧
    lokBedarfB mFs vmE mE vmE2 (.inl MTab.privB) = true ∧
    getrenntVB mFs vmE mE vmE2 (verbinde vmE mE vmE2).ws (.inl MTab.privB) = false ∧
    Akzeptiert (verbinde vmE mE vmE2).P mSI mFs [()] mCs (verbinde vmE mE vmE2).ws = false :=
  ⟨mP_akzeptiert, by decide, ⟨rfl, rfl, rfl, rfl, rfl⟩, by decide, by decide, by decide,
    by decide⟩

/-- The refusal at the specification: no `SchnittstelleSpec` for this pair. -/
theorem vm_abgelehnt_spec : ¬ SchnittstelleSpec mFs vmE mE vmE2 := fun h => by
  have := (schnittstelleB_iff mFs_voll mCs_voll).mpr h
  rw [vm_abgelehnt.2.2.2.1] at this
  cases this

/-! ## 3. REFUSAL: an exported contract too weak for the importer -/

/-- The library as compiled against `zP`: `wrap` ensures only `true`. -/
def vzBibSchwach : Programm zD := mitRumpf zP fun
  | .haupt => vzStubHaupt
  | .ein => zRumpfEin
  | .lies => zRumpfLies
  | .wrap => zRumpfWrap

def vzE2Schwach : Einheit zD := ⟨vzBibSchwach, zS, axWahr zD, [], zSp, []⟩

/-- **The contract is too weak: the link is refused.** The app relies on the imported
    `wrap`'s `ensures konto[0] == 100`; the library promises `ensures true`. The library alone
    is accepted; there is no link declaration for the pair (`Verbindbar` fails at `ensures`). -/
theorem vz_vertrag_zu_schwach :
    Akzeptiert vzBibSchwach zS zFs [()] [.inl ()] [] = true ∧ ¬ Verbindbar vzE1 vzE2Schwach := by
  refine ⟨by decide, fun h => ?_⟩
  have e : zEnsWrapB = (Expr.wahr : Expr zD (ErgCtx (zD.params zWrap) (zD.erg zWrap))
      (vertragVon zD zWrap).ende .bool) := congrFun h.ensures zWrap
  cases e

#print axioms vz_ziel
#print axioms vz_lauf_zeuge
#print axioms vm_abgelehnt
#print axioms vm_abgelehnt_spec
#print axioms vz_vertrag_zu_schwach

end Gabbro.Grammatik.Zielsatz
