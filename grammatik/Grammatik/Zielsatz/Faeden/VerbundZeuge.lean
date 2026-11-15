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
  * REFUSAL, CONTRACT (`vz_vertrag_zu_schwach`). The library's in-fragment replacement exports
    `wrap … ensures true`; the app relies on `ensures konto[0] == 100`. The library alone is
    accepted; there is no link declaration for the pair (`¬ Verbindbar`, at `ensures`) -- the
    Rust `N502`.
-/
module
public import Grammatik.Zielsatz.Faeden.Verbund
public import Grammatik.Zielsatz.Faeden.PoolZeuge
public import Grammatik.Zielsatz.Kern.AkzeptiertZeuge
import all Batteries.Data.Except
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section


namespace Gabbro.Grammatik.Zielsatz
open Gabbro.Grammatik
local instance verbundZeugeAxGleich : DecidableEq zD.Ax := inferInstanceAs (DecidableEq Empty)

/-! ## 1. POSITIVE: a library exports a lock-guarded table writer, an app calls it from two
    threads -/

/-- Ownership: the app (unit 1) owns `haupt`; the library (unit 2) owns `einzahlen`, `lies`
    and `wrap`. -/
def vzE : zD.Fn → Bool
  | .haupt => true
  | _ => false

/-- Capability gap: outside the decidable fragment: ownership-aware imported stubs.
    The replacement leaves satisfy their contracts independently, without calling
    the imported writer; the composed call hull remains non-degenerate. -/
def vzStubEin : Endblock zD (vertragVon zD zEin) false [] zL := zRumpfEin

def vzStubLies : Endblock zD (vertragVon zD zLies) false [] zL :=
  zRumpfLies

def vzStubWrap : Endblock zD (vertragVon zD zWrap) false [] zL :=
  .cons (.assignSlot () () zIdx zHundert rfl zDarf) (.ret .empty (List.Perm.refl _))

/-- The library's placeholder for `haupt`: a leaf. -/
def vzStubHaupt : Endblock zD (vertragVon zD zHaupt) false [] [] := .ret .empty List.Perm.nil

/-- The app's program: `haupt() = locks { wrap() }` (its own body), probe B's contracts
    (the IMPORTED `wrap` ensures `konto[0] == 100`), placeholders for the library. -/
def vzApp : Programm zD := mitRumpf zPB fun
  | .haupt => zRumpfHaupt
  | .ein => vzStubEin
  | .lies => vzStubLies
  | .wrap => vzStubWrap

/-- The library keeps its real bodies and a contract-correct leaf for the app. -/
def vzBib : Programm zD := mitRumpf zPB fun
  | .haupt => vzStubHaupt
  | .ein => zRumpfEin
  | .lies => zRumpfLies
  | .wrap => zRumpfWrap

/-- The app: `concurrent { haupt, haupt }`. -/
def vzE1 : Einheit zD where
  P := vzApp
  S := zS
  lockFormulas := zPoolSources
  Q := axWahr zD
  starts := [⟨zHaupt, .nil⟩, ⟨zHaupt, .nil⟩]
  sp0 := zSp
  gestartet := []
  arenen := []
  akku := []
  pruefungen := []
  grants0 := []

/-- The library: no thread of its own. -/
def vzE2 : Einheit zD where
  P := vzBib
  S := zS
  lockFormulas := zPoolSources
  Q := axWahr zD
  starts := []
  sp0 := zSp
  gestartet := []
  arenen := []
  akku := []
  pruefungen := []
  grants0 := []

/-- Both libraries keep the original reader; its strict gate uses the symbolic certificate. -/
theorem vz_app_contracts : Vertraege.Pruefer.KontrakteGeprueftB vzApp zS zFs zPoolSources = true := by
  apply Vertraege.Pruefer.SelectionWitness.contracts_success vzApp zS zPoolSources {} zFs
  intro f
  cases f with
  | ein => decide +kernel
  | lies => exact PoolCertificate.reader_checked_for vzApp.rumpf rfl zPoolSources (by decide +kernel)
  | wrap => decide +kernel
  | haupt => decide +kernel

theorem vz_bib_contracts : Vertraege.Pruefer.KontrakteGeprueftB vzBib zS zFs zPoolSources = true := by
  apply Vertraege.Pruefer.SelectionWitness.contracts_success vzBib zS zPoolSources {} zFs
  intro f
  cases f with
  | ein => decide +kernel
  | lies => exact PoolCertificate.reader_checked_for vzBib.rumpf rfl zPoolSources (by decide +kernel)
  | wrap => decide +kernel
  | haupt => decide +kernel

/-- Each unit is accepted ALONE by the concrete checker. -/
theorem vz_app_akzeptiert :
    Akzeptiert vzApp zS zFs [()] [.inl ()] [zHaupt, zHaupt] (sources := zPoolSources) = true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel,
    Bool.and_eq_true_iff.mpr ⟨by decide +kernel, vz_app_contracts⟩⟩

theorem vz_bib_akzeptiert : Akzeptiert vzBib zS zFs [()] [.inl ()] [] (sources := zPoolSources) = true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel,
    Bool.and_eq_true_iff.mpr ⟨by decide +kernel, vz_bib_contracts⟩⟩

theorem vz_verbindbar : Verbindbar vzE1 vzE2 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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
  refine ⟨⟨fun passes f hf => ?_, zS_lokal, axEnsLokal_wahr,
    fun f _ => zPool_nutzerPflicht.logik.2.2.2 f⟩, ⟨fun _ => rfl, fun a ha => ?_⟩⟩
  · cases f <;> simp only [vzE, Bool.false_eq_true] at hf
    obtain ⟨k, i, g⟩ := zPool_nutzerPflicht.logik.1 passes zHaupt
    exact ⟨(koerper_mitRumpf2 zPB _ zPB.rumpf passes _ _ zHaupt rfl).mpr k,
      (invGutS_mitRumpf2 zPB _ zPB.rumpf passes _ _ zHaupt rfl).mpr i,
      (invGutGrund_mitRumpf2 zPB _ zPB.rumpf passes _ _ zHaupt rfl).mpr g⟩
  · simp only [vzE1, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> rfl

theorem vz_nutzer2 : NutzerTeil (fun f => !vzE f) vzE2 := by
  refine ⟨⟨fun passes f _ => ?_, zS_lokal, axEnsLokal_wahr,
    fun f _ => zPool_nutzerPflicht.logik.2.2.2 f⟩, ⟨fun _ => rfl, fun a ha => ?_⟩⟩
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
    · simp only [vzE, Bool.not_true, Bool.false_eq_true] at *
  · simp only [vzE2, List.append_nil, List.not_mem_nil] at ha

/-- **THE LINKED GOAL**: every leg of `ZielF` on every reachable thread machine of the linked
    program, from `gabbro_ziel_verbund` -- the two units' verdicts, the link check, the two
    units' user duties, the SAME hardware assumptions. -/
theorem vz_ziel [RootNativeFloat.Hardware]
    (passes : Nat) (lebt0 : Faden → Bool) (K : FadenMaschine zD.mitRuhe)
    (hK : FadenErreichbar (verbinde vzE vzE1 vzE2).P.mitRuhe zO.mitRuhe passes
      (FadenStart (verbinde vzE vzE1 vzE2).P.mitRuhe (speicherR zSp)
        (initRuhe (verbinde vzE vzE1 vzE2).starts) lebt0) K) :
    ZielF (verbinde vzE vzE1 vzE2).P.mitRuhe (verbinde vzE vzE1 vzE2).S.mitRuhe zO.mitRuhe passes
      (RufStartG (verbinde vzE vzE1 vzE2).P.mitRuhe (speicherR zSp)
        (initRuhe (verbinde vzE vzE1 vzE2).starts)) K :=
  gabbro_ziel_verbund_sc akzeptiert_pruefer zD vzE1 vzE2 vzE ⟨zFs, zFs_voll⟩ ⟨[()], zLs_voll⟩
    ⟨[.inl ()], zCs_voll⟩
    (by rw [akzeptiert_pruefer_eq]; exact vz_app_akzeptiert)
    (by rw [akzeptiert_pruefer_eq]; exact vz_bib_akzeptiert) vz_verbindbar
    (((schnittstelleB_iff zFs_voll zCs_voll []).mp vz_schnittstelle).1) vz_nutzer1 vz_nutzer2 rfl zO
    ⟨zO_gut, zO_lokal, axVertragO_wahr zO, inferInstance⟩ passes _ _ (laufzeit_initRuhe _) lebt0 K hK

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
  simp only [vzE1, vzE2, zPool, ite_self, List.append_nil]

/-- **THE RUN**: on the linked program both app threads run `haupt`; thread 0 unfolds its body,
    thread 1 unfolds its body, thread 0 takes the lock -- and at that machine `gabbro_ziel_verbund`
    gives every leg of `Ziel` (race freedom over the library's table writer included). -/
theorem vz_lauf_zeuge [RootNativeFloat.Hardware] : ∃ M3 : RufMaschineG zD.mitRuhe,
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
  .bind (.slot MTab.privB () mI0 (mDarfB _)) (.ret .empty List.Perm.nil)

/-- The library's unowned writer is a contract-correct leaf. -/
def vmStubA : Endblock mD (vertragVon mD mHauptA) false [] [] :=
  .cons (.assignSlot MTab.privA () mI0 m7 rfl (mDarfA _))
    (.cons (.assignSlot MTab.privA () mI1 m7 rfl (mDarfA _)) (.ret .empty List.Perm.nil))

/-- The library reads `privB`; all imported functions have correct leaf bodies. -/
def vmBib : Programm mD := mitRumpf mFragment fun
  | .pruefeA => vmLeser
  | .hauptA => vmStubA
  | .setze => .ret .empty (List.Perm.refl _)
  | .hauptB => .ret .empty List.Perm.nil
  | .ruhe => .ret .empty List.Perm.nil

/-- The library as a unit: no thread of its own. -/
def vmE2 : Einheit mD where
  P := vmBib
  S := mFragmentS
  lockFormulas := CheckedMehrfaden.sources
  Q := axWahr mD
  starts := []
  sp0 := mSp
  gestartet := []
  arenen := []
  akku := []
  pruefungen := []
  grants0 := []

/-- **Refused at the link, although each unit alone is accepted.** The app is the two-thread
    fixture `mE` (`hauptA` calls the imported `pruefeA`, `hauptB` writes `privB`); its
    placeholder for `pruefeA` reads nothing, so ALONE it is accepted. The library alone is
    accepted (no thread of its own reads against a writer). Linked, thread `hauptA` reaches the
    library's `pruefeA`, which reads `privB` while thread `hauptB` writes it: `privB` is relied
    on as thread-local (`LokBedarf`), and over the composed hulls it is not (`GetrenntV`
    fails). The whole-program checker refuses the linked program for the same reason. -/
theorem vm_abgelehnt :
    Akzeptiert mE.P mE.S mFs [()] mCs mE.ws (sources := CheckedMehrfaden.sources) = true ∧
    Akzeptiert vmBib mFragmentS mFs [()] mCs [] (sources := CheckedMehrfaden.sources) = true ∧
    Verbindbar mE vmE2 ∧
    schnittstelleB mFs mCs vmE mE vmE2 = false ∧
    lokBedarfB mFs vmE mE vmE2 (.inl MTab.privB) = true ∧
    getrenntVB mFs vmE mE vmE2 (verbinde vmE mE vmE2).ws (.inl MTab.privB) = false ∧
    Akzeptiert (verbinde vmE mE vmE2).P mFragmentS mFs [()] mCs (verbinde vmE mE vmE2).ws
      (sources := CheckedMehrfaden.sources) = false :=
  ⟨mFragment_akzeptiert, by decide +kernel, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by decide, by decide, by decide,
    by decide⟩

/-- The refusal at the specification: no `SchnittstelleSpec` for this pair. -/
theorem vm_abgelehnt_spec : ¬ SchnittstelleSpec mFs vmE mE vmE2 := fun h => by
  have hak : (verbinde vmE mE vmE2).akku = [] := rfl
  have := (schnittstelleB_iff mFs_voll mCs_voll []).mpr
    ⟨h, fun a ha => by rw [hak] at ha; exact absurd ha List.not_mem_nil⟩
  rw [vm_abgelehnt.2.2.2.1] at this
  cases this

/-! ## 3. REFUSAL: an exported contract too weak for the importer -/

/-- Capability gap: outside the decidable fragment: old-memory ensures.
    The replacement keeps the weak exported contract and the resulting mismatch. -/
def vzSchwach : Programm zD :=
  { zPB with ensures := fun _ => .tru }

def vzBibSchwach : Programm zD := mitRumpf vzSchwach fun
  | .haupt => vzStubHaupt
  | .ein => zRumpfEin
  | .lies => zRumpfLies
  | .wrap => zRumpfWrap

def vzE2Schwach : Einheit zD where
  P := vzBibSchwach
  S := zS
  lockFormulas := zPoolSources
  Q := axWahr zD
  starts := []
  sp0 := zSp
  gestartet := []
  arenen := []
  akku := []
  pruefungen := []
  grants0 := []

/-- **The contract is too weak: the link is refused.** The app relies on the imported
    `wrap`'s `ensures konto[0] == 100`; the library promises `ensures true`. The library alone
    is accepted; there is no link declaration for the pair (`Verbindbar` fails at `ensures`). -/
theorem vz_vertrag_zu_schwach :
    Akzeptiert vzBibSchwach zS zFs [()] [.inl ()] [] (sources := zPoolSources) = true ∧ ¬ Verbindbar vzE1 vzE2Schwach := by
  refine ⟨by decide +kernel, fun h => ?_⟩
  have e : zEnsWrapB = (Expr.tru : Expr zD (ErgCtx (zD.params zWrap) (zD.erg zWrap))
      (vertragVon zD zWrap).ende .bool) := congrFun h.ensures zWrap
  cases e

#print axioms vz_ziel
#print axioms vz_lauf_zeuge
#print axioms vm_abgelehnt
#print axioms vm_abgelehnt_spec
#print axioms vz_vertrag_zu_schwach

end Gabbro.Grammatik.Zielsatz
