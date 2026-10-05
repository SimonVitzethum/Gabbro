/-
  File:      Grammatik/X86/HwKapsteinSteps.lean
  Subject:   Capstone steps: reached union steps for the six
             equation-only tags, and the two plug-less families.

  Lane 1289: capstone follow-up of lane 1149 (`HwKapstein.lean`).
  Every accepted definition is reused unchanged (lifted, never
  redefined); no new machine, no new evaluator, no new adapter.
-/
import Grammatik.X86.Hw.Kapstein.HwKapstein
import Grammatik.X86.Hw.Familien.HwDevices
import Grammatik.X86.Hw.Ausnahmen.HwNestedInterrupts
import Grammatik.X86.Hw.Ausnahmen.HwInterrupts
import Grammatik.X86.Hw.Familien.HwSystemForms
import Grammatik.X86.Hw.Bild.HwLoadedImage
import Grammatik.X86.Hw.Bild.HwBildInstanzen
import Grammatik.X86.Hw.Bild.HwBildFamilien
import Grammatik.X86.Hw.Ausnahmen.HwFeatureStep

namespace Gabbro.Grammatik.X86

/-! ## 1. Port witness machine: a fetched OUT on core 0.

   Two cores, empty buffers, full silicon. Core 0 fetches
   `OUT 0x60, AL` (`E6 60`) at `0x1000`; core 1 idles. -/

/-- Port witness bytes: `OUT imm8` at the fetch head, zero past it. -/
def kapPortBytes : Adresse → Byte
  | a => if a == BitVec.ofNat 64 0x1000 then natByte 230
    else if a == BitVec.ofNat 64 0x1001 then natByte 96
    else natByte 0

/-- Port witness memory: everything readable and executable. -/
def kapPortMem : Speicher :=
  { bytes := kapPortBytes
    lesbar := fun _ => true
    schreibbar := fun _ => true
    ausfuehrbar := fun _ => true }

/-- Port witness cores: core 0 fetches at `0x1000`, core 1 idles. -/
def kapPortKern : Nat → HwKern
  | 0 => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 0x1000, fun _ => BitVec.ofNat 128 0,
      kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 0x2000, fun _ => BitVec.ofNat 128 0,
      kontextReset⟩

/-- Port witness start: two cores, empty buffers, full silicon. -/
def kapPortStart : HwMaschine :=
  ⟨kapPortMem, kapPortKern, fun _ => [], basisHw,
    fun _ => basisBereit⟩

/-- The port witness machine is well-formed. -/
theorem kapPortStart_wf : HwWf kapPortStart := by
  apply hwWf_aus_zugelassen
  intro c f
  cases f with
  | skalar64 => rfl
  | skalar32 => rfl
  | sseDoppel =>
    show merkmalZugelassen basisHw basisBereit .sseDoppel = true
    decide
  | paketInt128 =>
    show merkmalZugelassen basisHw basisBereit .paketInt128 = true
    decide

/-- The fetched port decode: `OUT 0x60, AL`, length 2. -/
def kapPortDec : IoDec := ⟨⟨.aus, .p8, .imm 96⟩, 2⟩

/-- FETCH: core 0 fetches the OUT row whole, 13 zero bytes past it. -/
theorem kapPort_fetch :
    fetchIo (projZustand kapPortStart 0) =
      some (kapPortDec, List.replicate 13 (natByte 0)) := by
  decide

/-- The exhibited port event: OUT under direct CPL<=IOPL admission,
    full-map card, empty log. -/
def kapPortEv : HwDev1133.PortZugriff1133 :=
  .aus kapPortDec ⟨0, 0⟩ [] ⟨0, 0⟩ Bus704.volleKarte

/-- SELECTION: the fetched OUT computes the core successor through
    the accepted plug gates (length, direct privilege, empty buffer). -/
theorem kapPort_kern :
    HwDev1133.portAdapterKern kapPortStart 0 kapPortEv =
      some (HwDev1133.portAusKern kapPortStart 0 kapPortDec) := by
  have hsel := HwDev1133.portAdapter_aus_fetch kapPortStart 0
    kapPortDec ⟨0, 0⟩ [] ⟨0, 0⟩ Bus704.volleKarte
    kapPortDec (List.replicate 13 (natByte 0)) .p8 (.imm 96)
    kapPort_fetch rfl rfl (by decide) (by decide) (by decide)
  exact hsel.1

/-- PLUG: the fetched OUT is an admitted coherent port step. -/
theorem kapPlug_port :
    HwDev1133.adapterPort1133.schritt kapPortStart 0 kapPortEv =
      some (setKernDaten kapPortStart 0
        (HwDev1133.portAusKern kapPortStart 0 kapPortDec)) := by
  have hker := kapPort_kern
  show HwDev1133.portAdapterSchritt kapPortStart 0 kapPortEv = _
  unfold HwDev1133.portAdapterSchritt
  simp [hker]

/-- Exhibited port union step: core 0 OUTs to port `0x60`. -/
theorem kapStep_port :
    ∃ m1, HwVollSchritt kapPortStart m1
      (KapEreignis.port 0 kapPortEv) :=
  ⟨_, (kap_port_embedded _ _ _ _).mp kapPlug_port⟩

/-! ## 2. Nested delivery: the family's own two-gate run.

   `nestVerschachtelt` (trap 32, then interrupt 33, on core 0) is
   `some` -- the family's `nestV_rip` decides the handler `0x2200`.
   The adapter reads the first event's snapshot, which is `nestSteuer`
   by construction. -/

/-- PLUG: the nested run is an admitted coherent nest step. -/
theorem kapPlug_nested :
    ∃ m2 ifNeu2 gew1 gew2,
      adapterVerschachtelt.schritt nestStart 0
        (evMask32, evMask33) = some m2 ∧
      verschachteltSchritt nestStart 0 evMask32 evMask33
        nestSteuer = some (m2, ifNeu2, gew1, gew2) := by
  cases hV : nestVerschachtelt with
  | none =>
    have hc := nestV_rip
    simp [nestRipOut, hV] at hc
  | some r =>
    obtain ⟨m2, ifNeu2, gew1, gew2⟩ := r
    have h3 : verschachteltSchritt nestStart 0 evMask32 evMask33
        evMask32.steuer = some (m2, ifNeu2, gew1, gew2) := hV
    refine ⟨m2, ifNeu2, gew1, gew2, ?_, hV⟩
    show adapterVerschachtelt.schritt nestStart 0 (evMask32, evMask33) =
      some m2
    unfold adapterVerschachtelt
    simp [h3]

/-- Exhibited nested union step: trap 32, then interrupt 33. -/
theorem kapStep_nested :
    ∃ m2, HwVollSchritt nestStart m2
      (KapEreignis.nested 0 evMask32 evMask33) := by
  obtain ⟨m2, _, _, _, hplug, _⟩ := kapPlug_nested
  exact ⟨m2, (kap_nested_embedded _ _ _ _ _).mp hplug⟩

/-! ## 3. Single delivery: the family's own NMI run.

   `witSchritt` (NMI vector 2 on core 0 under cleared IF) is `some` --
   the family's `witNmi_erfolg_ex`. The adapter reads the event's own
   snapshot, which is `witSteuerNmi` by construction. -/

/-- PLUG: the NMI run is an admitted coherent delivery step. -/
theorem kapPlug_int :
    ∃ m' ifNeu gew,
      adapterInterrupt1125.schritt intWitStart 0 witNmi = some m' ∧
      asyncSchritt intWitStart 0 witNmi witSteuerNmi =
        some (m', ifNeu, gew) := by
  obtain ⟨⟨m', ifNeu, gew⟩, h⟩ := witNmi_erfolg_ex
  have h2 : asyncSchritt intWitStart 0 witNmi witNmi.steuer =
      some (m', ifNeu, gew) := h
  refine ⟨m', ifNeu, gew, ?_, h⟩
  show adapterInterrupt1125.schritt intWitStart 0 witNmi = some m'
  unfold adapterInterrupt1125
  simp [h2]

/-- Exhibited single-delivery union step: NMI on core 0. -/
theorem kapStep_int :
    ∃ m', HwVollSchritt intWitStart m'
      (KapEreignis.int 0 witNmi) := by
  obtain ⟨m', _, _, hplug, _⟩ := kapPlug_int
  exact ⟨m', (kap_int_embedded _ _ _ _).mp hplug⟩

/-! ## 4. System forms: the family's own CLI run.

   `sysWitO_cli` (CLI on core 0) is `.ok` -- the family's
   `sysWit_cli_if` decides IF cleared. The snapshot leg behind it
   succeeds, and the plug installs exactly it (`adapterSystem_ok`). -/

/-- The exhibited system event: CLI with the witness inputs. -/
def kapSysEv : SysSteuer × SysEreignis :=
  (sysWitSteuer, ⟨.cli, sysWitEingaben⟩)

/-- The hosted profile admits the CLI form (no `#UD` gate). -/
theorem kapSys_frei :
    formFrei sysWitEingaben.profil .cli = true := by
  decide

/-- PLUG: the CLI leg is an admitted coherent system step. -/
theorem kapPlug_system :
    ∃ m1, adapterSystem.schritt sysWitStart.hw 0 kapSysEv = some m1 := by
  cases hS : sysSnapSchritt sysWitStart.hw 0 sysWitSteuer
      ⟨.cli, sysWitEingaben⟩ with
  | ok k' st' mem' =>
    exact ⟨_, adapterSystem_ok sysWitStart.hw 0 kapSysEv k' st' mem' hS⟩
  | fehler f =>
    have hAus : sysWitO_cli = .fehler f := by
      show sysAusfuehren sysWitStart 0 ⟨.cli, sysWitEingaben⟩ =
        .fehler f
      unfold sysAusfuehren
      have hfrei : formFrei sysWitEingaben.profil .cli = false →
          False := by
        rw [kapSys_frei]
        decide
      by_cases hf : formFrei (⟨.cli, sysWitEingaben⟩ :
          SysEreignis).eingaben.profil
          (⟨.cli, sysWitEingaben⟩ : SysEreignis).form = false
      · exact absurd hf hfrei
      · simp only [hf]
        have hsys : sysWitStart.sys 0 = sysWitSteuer := rfl
        simp [hsys, hS]
    have hc := sysWit_cli_if
    simp [sysIfOut, hAus] at hc
  | verweigert =>
    have hAus : sysWitO_cli = .verweigert := by
      show sysAusfuehren sysWitStart 0 ⟨.cli, sysWitEingaben⟩ =
        .verweigert
      unfold sysAusfuehren
      have hfrei : formFrei sysWitEingaben.profil .cli = false →
          False := by
        rw [kapSys_frei]
        decide
      by_cases hf : formFrei (⟨.cli, sysWitEingaben⟩ :
          SysEreignis).eingaben.profil
          (⟨.cli, sysWitEingaben⟩ : SysEreignis).form = false
      · exact absurd hf hfrei
      · simp only [hf]
        have hsys : sysWitStart.sys 0 = sysWitSteuer := rfl
        simp [hsys, hS]
    have hc := sysWit_cli_if
    simp [sysIfOut, hAus] at hc

/-- Exhibited system union step: CLI on core 0. -/
theorem kapStep_system :
    ∃ m1, HwVollSchritt sysWitStart.hw m1
      (KapEreignis.system 0 sysWitSteuer ⟨.cli, sysWitEingaben⟩) := by
  obtain ⟨m1, hplug⟩ := kapPlug_system
  have hplug' : adapterSystem.schritt sysWitStart.hw 0
      (sysWitSteuer, ⟨.cli, sysWitEingaben⟩) = some m1 := hplug
  exact ⟨m1, (kap_system_embedded _ _ _ _ _).mp hplug'⟩

/-! ## 5. Loaded image and loader instances: two register rows.

   Both plugs ARE the accepted register-path plug (`adapterBild`
   and `adapterInstanzen` are `adapterInteger666` by definition), so
   the families' own `stepExt` successes step through them unchanged:
   MUL `6 * 7` on the muldiv instance machine (bild tag), PXOR on the
   vec instance machine (instanzen tag). -/

/-- PLUG: the MUL row steps through the loaded-image plug. -/
theorem kapPlug_bild :
    adapterBild.schritt instStart_muldiv 0
      (.muldiv ⟨.mulRax .rcx, 3⟩) =
      some (setKernVonFp instStart_muldiv 0 instT_muldiv) :=
  adapterBild_vereinbarung _ _ _ _ inst_schritt_muldiv

/-- Exhibited loaded-image union step: MUL on core 0. -/
theorem kapStep_bild :
    ∃ m1, HwVollSchritt instStart_muldiv m1
      (KapEreignis.bild 0 (.muldiv ⟨.mulRax .rcx, 3⟩)) :=
  ⟨_, (kap_bild_embedded _ _ _ _).mp kapPlug_bild⟩

/-- PLUG: the PXOR row steps through the instances plug. -/
theorem kapPlug_instanzen :
    adapterInstanzen.schritt instStart_vec 0
      (.vec ⟨.pxorRR .xmm0 .xmm1, 5⟩) =
      some (setKernVonFp instStart_vec 0 instT_vec) :=
  adapterInstanzen_vereinbarung _ _ _ _ inst_schritt_vec

/-- Exhibited instances union step: PXOR on core 0. -/
theorem kapStep_instanzen :
    ∃ m1, HwVollSchritt instStart_vec m1
      (KapEreignis.instanzen 0
        (.vec ⟨.pxorRR .xmm0 .xmm1, 5⟩)) :=
  ⟨_, (kap_instanzen_embedded _ _ _ _).mp kapPlug_instanzen⟩

/-! ## 6. The extended union keeps `kap_wf` and the exact embeddings.

   Well-formedness: every exhibited step preserves `HwWf` through the
   capstone's `kap_wf` (no new preservation argument anywhere).
   Embeddings: every exhibited union step returns its plug equation
   through the capstone's exact iffs (no new behaviour behind any of
   the six tags). -/

/-- Every exhibited step preserves well-formedness. -/
theorem kapSteps_wf :
    (∀ m1, HwVollSchritt kapPortStart m1 (KapEreignis.port 0 kapPortEv) →
      HwWf kapPortStart → HwWf m1) ∧
    (∀ m2, HwVollSchritt nestStart m2
      (KapEreignis.nested 0 evMask32 evMask33) →
      HwWf nestStart → HwWf m2) ∧
    (∀ m', HwVollSchritt intWitStart m' (KapEreignis.int 0 witNmi) →
      HwWf intWitStart → HwWf m') ∧
    (∀ m1, HwVollSchritt sysWitStart.hw m1
      (KapEreignis.system 0 sysWitSteuer ⟨.cli, sysWitEingaben⟩) →
      HwWf sysWitStart.hw → HwWf m1) ∧
    (∀ m1, HwVollSchritt instStart_muldiv m1
      (KapEreignis.bild 0 (.muldiv ⟨.mulRax .rcx, 3⟩)) →
      HwWf instStart_muldiv → HwWf m1) ∧
    (∀ m1, HwVollSchritt instStart_vec m1
      (KapEreignis.instanzen 0
        (.vec ⟨.pxorRR .xmm0 .xmm1, 5⟩)) →
      HwWf instStart_vec → HwWf m1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intro m h hwf <;> exact kap_wf _ _ _ h hwf

/-- Every exhibited union step returns its plug equation: the six tags
    embed exactly, both directions, on the exhibited steps. -/
theorem kapSteps_embedded :
    (∀ m1, HwVollSchritt kapPortStart m1 (KapEreignis.port 0 kapPortEv) →
      HwDev1133.adapterPort1133.schritt kapPortStart 0 kapPortEv =
        some m1) ∧
    (∀ m2, HwVollSchritt nestStart m2
      (KapEreignis.nested 0 evMask32 evMask33) →
      adapterVerschachtelt.schritt nestStart 0 (evMask32, evMask33) =
        some m2) ∧
    (∀ m', HwVollSchritt intWitStart m' (KapEreignis.int 0 witNmi) →
      adapterInterrupt1125.schritt intWitStart 0 witNmi = some m') ∧
    (∀ m1, HwVollSchritt sysWitStart.hw m1
      (KapEreignis.system 0 sysWitSteuer ⟨.cli, sysWitEingaben⟩) →
      adapterSystem.schritt sysWitStart.hw 0 kapSysEv = some m1) ∧
    (∀ m1, HwVollSchritt instStart_muldiv m1
      (KapEreignis.bild 0 (.muldiv ⟨.mulRax .rcx, 3⟩)) →
      adapterBild.schritt instStart_muldiv 0
        (.muldiv ⟨.mulRax .rcx, 3⟩) = some m1) ∧
    (∀ m1, HwVollSchritt instStart_vec m1
      (KapEreignis.instanzen 0
        (.vec ⟨.pxorRR .xmm0 .xmm1, 5⟩)) →
      adapterInstanzen.schritt instStart_vec 0
        (.vec ⟨.pxorRR .xmm0 .xmm1, 5⟩) = some m1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m1 h
    exact (kap_port_embedded _ _ _ _).mpr h
  · intro m2 h
    exact (kap_nested_embedded _ _ _ _ _).mpr h
  · intro m' h
    exact (kap_int_embedded _ _ _ _).mpr h
  · intro m1 h
    have h' : adapterSystem.schritt sysWitStart.hw 0
        (sysWitSteuer, ⟨.cli, sysWitEingaben⟩) = some m1 :=
      (kap_system_embedded _ _ _ _ _).mpr h
    simpa [kapSysEv] using h'
  · intro m1 h
    exact (kap_bild_embedded _ _ _ _).mpr h
  · intro m1 h
    exact (kap_instanzen_embedded _ _ _ _).mpr h

/-! ## 7. The six tags are pairwise distinct.

   The capstone's `kap_tags_disjoint` keeps the base apart from every
   family tag; what is new here is that the six equation-only tags are
   pairwise distinct among themselves (and `bild` apart from
   `instanzen`, although both ride the same register-path plug). Each
   pair falls by constructor discrimination through `kapTag`. -/

/-- The six exhibited tags are pairwise distinct. -/
theorem kapSteps_tags_disjoint :
    (KapEreignis.port 0 kapPortEv ≠
      KapEreignis.nested 0 evMask32 evMask33) ∧
    (KapEreignis.port 0 kapPortEv ≠ KapEreignis.int 0 witNmi) ∧
    (KapEreignis.port 0 kapPortEv ≠
      KapEreignis.system 0 sysWitSteuer ⟨.cli, sysWitEingaben⟩) ∧
    (KapEreignis.port 0 kapPortEv ≠
      KapEreignis.bild 0 (.muldiv ⟨.mulRax .rcx, 3⟩)) ∧
    (KapEreignis.port 0 kapPortEv ≠ KapEreignis.instanzen 0
      (.vec ⟨.pxorRR .xmm0 .xmm1, 5⟩)) ∧
    (KapEreignis.nested 0 evMask32 evMask33 ≠
      KapEreignis.int 0 witNmi) ∧
    (KapEreignis.nested 0 evMask32 evMask33 ≠
      KapEreignis.system 0 sysWitSteuer ⟨.cli, sysWitEingaben⟩) ∧
    (KapEreignis.nested 0 evMask32 evMask33 ≠
      KapEreignis.bild 0 (.muldiv ⟨.mulRax .rcx, 3⟩)) ∧
    (KapEreignis.nested 0 evMask32 evMask33 ≠
      KapEreignis.instanzen 0
        (.vec ⟨.pxorRR .xmm0 .xmm1, 5⟩)) ∧
    (KapEreignis.int 0 witNmi ≠
      KapEreignis.system 0 sysWitSteuer ⟨.cli, sysWitEingaben⟩) ∧
    (KapEreignis.int 0 witNmi ≠
      KapEreignis.bild 0 (.muldiv ⟨.mulRax .rcx, 3⟩)) ∧
    (KapEreignis.int 0 witNmi ≠ KapEreignis.instanzen 0
      (.vec ⟨.pxorRR .xmm0 .xmm1, 5⟩)) ∧
    (KapEreignis.system 0 sysWitSteuer ⟨.cli, sysWitEingaben⟩ ≠
      KapEreignis.bild 0 (.muldiv ⟨.mulRax .rcx, 3⟩)) ∧
    (KapEreignis.system 0 sysWitSteuer ⟨.cli, sysWitEingaben⟩ ≠
      KapEreignis.instanzen 0
        (.vec ⟨.pxorRR .xmm0 .xmm1, 5⟩)) ∧
    (KapEreignis.bild 0 (.muldiv ⟨.mulRax .rcx, 3⟩) ≠
      KapEreignis.instanzen 0
        (.vec ⟨.pxorRR .xmm0 .xmm1, 5⟩)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;>
    intro h <;> have h2 := congrArg kapTag h <;>
      simp [kapTag] at h2

/-! ## 8. The two plug-less families ride existing tags.

   `HwBildFamilien` contributes fetch/decoder equations, not steps:
   both loaded-image plugs ARE the one accepted register-path plug
   (`adapterBild` and `adapterInstanzen` are `adapterInteger666` by
   definition), so there is no third plug to tag -- every one of its
   six rows steps through the already-tagged instanzen plug, shown
   below on the families' own `stepExt` successes. `HwFeatureStep`
   refines the gate (`stepExtTor`): its admitted vector step executes
   exactly as the already-tagged tor arm (`hwStepTor_verbindung`). -/

/-- One plug, two tags: no third plug exists to tag. -/
theorem familien_plug_gleich :
    adapterBild = adapterInstanzen := rfl

/-- MUL rides the instanzen tag (the same row rides bild above). -/
theorem kapFamilie_muldiv :
    ∃ m1, HwVollSchritt instStart_muldiv m1
      (KapEreignis.instanzen 0
        (.muldiv ⟨.mulRax .rcx, 3⟩)) :=
  ⟨_, (kap_instanzen_embedded _ _ _ _).mp
    (adapterInstanzen_vereinbarung _ _ _ _ inst_schritt_muldiv)⟩

/-- SHL rides the instanzen tag. -/
theorem kapFamilie_shift :
    ∃ m1, HwVollSchritt instStart_shift m1
      (KapEreignis.instanzen 0
        (.shift ⟨.imm .shl .rax 1, 4⟩)) :=
  ⟨_, (kap_instanzen_embedded _ _ _ _).mp
    (adapterInstanzen_vereinbarung _ _ _ _ inst_schritt_shift)⟩

/-- SETcc rides the instanzen tag. -/
theorem kapFamilie_setcc :
    ∃ m1, HwVollSchritt instStart_setcc m1
      (KapEreignis.instanzen 0 (.setcc .e .rax 4)) :=
  ⟨_, (kap_instanzen_embedded _ _ _ _).mp
    (adapterInstanzen_vereinbarung _ _ _ _ inst_schritt_setcc)⟩

/-- CMOV rides the instanzen tag. -/
theorem kapFamilie_cmov :
    ∃ m1, HwVollSchritt instStart_cmov m1
      (KapEreignis.instanzen 0 (.cmov .e .rax .rcx 4)) :=
  ⟨_, (kap_instanzen_embedded _ _ _ _).mp
    (adapterInstanzen_vereinbarung _ _ _ _ inst_schritt_cmov)⟩

/-- MOVSD rides the instanzen tag. -/
theorem kapFamilie_fp :
    ∃ m1, HwVollSchritt instStart_fp m1
      (KapEreignis.instanzen 0
        (.fp ⟨.movsdRR .xmm0 .xmm1, 4⟩)) :=
  ⟨_, (kap_instanzen_embedded _ _ _ _).mp
    (adapterInstanzen_vereinbarung _ _ _ _ inst_schritt_fp)⟩

/-- The gate refinement rides the tor tag: the admitted step-level
    vector step executes exactly as the tor arm. -/
theorem kapFamilie_feature_tor :
    ∃ m1, HwVollSchritt hwWitStart m1
      (KapEreignis.tor zeugeOut1 (BitVec.ofNat 32 0x6)
        (.ausf 0 (.vec hwTorWitV))) := by
  obtain ⟨_, htor, _⟩ := hwStepTor_verbindung_zeuge
  exact ⟨_, (kap_tor_embedded _ _ _ _ _).mp htor⟩

/-! ## 9. Planted refusals beside the run. -/

/-- REFUSED: a forged IN decode the fetch did not produce. -/
theorem kapPort_falschDecodiert_verweigert :
    HwDev1133.portAdapterSchritt kapPortStart 0
      (.aus ⟨⟨.ein, .p8, .imm 96⟩, 2⟩ ⟨0, 0⟩ [] ⟨0, 0⟩
        Bus704.volleKarte) = none :=
  HwDev1133.portAdapter_falschDecodiert_verweigert kapPortStart 0
    ⟨⟨.ein, .p8, .imm 96⟩, 2⟩ ⟨0, 0⟩ [] ⟨0, 0⟩ Bus704.volleKarte
    kapPortDec (List.replicate 13 (natByte 0))
    kapPort_fetch (by decide)

/-! ## 10. Joint witness: every exhibited premise together.

   Six reached union steps (one per equation-only tag), five further
   rows riding the instanzen tag, the gate refinement riding the tor
   tag, the one-plug-two-tags identity, well-formedness of every start
   machine, planted refusals, tag disjointness, and the shared
   non-degeneracy: deliveries push real frames and change memory,
   buffered stores forward to the owner only and drain into shared
   memory 0 to 42 observed from both cores. -/

/-- Joint capstone-steps witness over the coherent machine. -/
theorem kapSteps_zeuge :
    (∃ m1, HwVollSchritt kapPortStart m1
      (KapEreignis.port 0 kapPortEv)) ∧
    (∃ m2, HwVollSchritt nestStart m2
      (KapEreignis.nested 0 evMask32 evMask33)) ∧
    (∃ m', HwVollSchritt intWitStart m'
      (KapEreignis.int 0 witNmi)) ∧
    (∃ m1, HwVollSchritt sysWitStart.hw m1
      (KapEreignis.system 0 sysWitSteuer ⟨.cli, sysWitEingaben⟩)) ∧
    (∃ m1, HwVollSchritt instStart_muldiv m1
      (KapEreignis.bild 0 (.muldiv ⟨.mulRax .rcx, 3⟩))) ∧
    (∃ m1, HwVollSchritt instStart_vec m1
      (KapEreignis.instanzen 0
        (.vec ⟨.pxorRR .xmm0 .xmm1, 5⟩))) ∧
    (∃ m1, HwVollSchritt hwWitStart m1
      (KapEreignis.tor zeugeOut1 (BitVec.ofNat 32 0x6)
        (.ausf 0 (.vec hwTorWitV)))) ∧
    HwWf kapPortStart ∧ HwWf nestStart ∧ HwWf intWitStart ∧
    HwWf sysWitStart.hw ∧ HwWf instStart_muldiv ∧
    HwWf instStart_vec ∧
    nestTsoLoadEigen = some (some (BitVec.ofNat 8 42)) ∧
    nestTsoLoadFremd = some (some (BitVec.ofNat 8 0)) ∧
    nestTsoNachFlush = some (some (BitVec.ofNat 8 42)) ∧
    nestTsoFremdNachFlush = some (some (BitVec.ofNat 8 42)) ∧
    sysWitLoadEigen = some (some (BitVec.ofNat 8 42)) ∧
    sysWitLoadFremd = some (some (BitVec.ofNat 8 0)) ∧
    sysWitNachFlush = some (some (BitVec.ofNat 8 42)) ∧
    instLoadEigen_muldiv = some (some (BitVec.ofNat 8 42)) ∧
    instLoadFremd_muldiv = some (some (BitVec.ofNat 8 0)) ∧
    instNachFlush_muldiv = some (some (BitVec.ofNat 8 42)) ∧
    instFremdNachFlush_muldiv = some (some (BitVec.ofNat 8 42)) ∧
    witMem.bytes (BitVec.ofNat 64 16376) ≠
      (asyncMemOut witSchritt).bytes (BitVec.ofNat 64 16376) ∧
    HwDev1133.portAdapterSchritt kapPortStart 0
      (.aus ⟨⟨.ein, .p8, .imm 96⟩, 2⟩ ⟨0, 0⟩ [] ⟨0, 0⟩
        Bus704.volleKarte) = none ∧
    asyncSchritt intWitStart 1 witMaskiert witSteuerNmi = none ∧
    nestDritt = none := by
  refine ⟨kapStep_port, kapStep_nested, kapStep_int, kapStep_system,
    kapStep_bild, kapStep_instanzen, kapFamilie_feature_tor,
    kapPortStart_wf, nestStart_wf, intWitStart_wf, sysWitStart_wf,
    instStart_wf_muldiv, instStart_wf_vec,
    nestTso_weiterleitung, nestTso_fremd_alt,
    nestTso_spuelung_aendert, nestTso_fremd_neu,
    sysWit_weiterleitung, sysWit_fremd_alt,
    sysWit_spuelung_aendert_speicher,
    inst_weiterleitung_muldiv, inst_fremd_alt_muldiv,
    inst_spuelung_aendert_speicher_muldiv, inst_fremd_neu_muldiv,
    witNmi_aendert_ss, kapPort_falschDecodiert_verweigert,
    witNmi_maskiert_verweigert, nestDritt_verweigert⟩

/- CUTS:
    Proved here, over the reused accepted vocabulary only (every
    definition lifted, never redefined; no new machine, evaluator
    or adapter):
    - six reached closed union steps, one per equation-only tag:
      port (`kapStep_port`: fetched OUT `E6 60` on a new two-core
      machine, via `portAdapter_aus_fetch`), nested
      (`kapStep_nested`: trap 32 then interrupt 33, via the family's
      `nestVerschachtelt`/`nestV_rip`), int (`kapStep_int`: NMI
      vector 2 under cleared IF, via `witNmi_erfolg_ex`), system
      (`kapStep_system`: CLI on core 0, via `sysWit_cli_if` and
      `adapterSystem_ok`), bild (`kapStep_bild`: MUL 6*7, via
      `inst_schritt_muldiv` and `adapterBild_vereinbarung`),
      instanzen (`kapStep_instanzen`: PXOR, via
      `inst_schritt_vec` and `adapterInstanzen_vereinbarung`);
    - the extended union keeps `kap_wf` (`kapSteps_wf`, through the
      capstone's `kap_wf`) and the exact embeddings
      (`kapSteps_embedded`, both directions of the six capstone
      iffs on the exhibited steps);
    - the six tags are pairwise distinct (`kapSteps_tags_disjoint`,
      through `kapTag`); base-vs-family disjointness stays in the
      capstone's `kap_tags_disjoint`;
    - the two plug-less families ride existing tags, and precisely
      why no new tag is possible: `adapterBild` and
      `adapterInstanzen` ARE the one accepted register-path plug
      (`familien_plug_gleich`), so `HwBildFamilien` -- fetch/decoder
      equations, no step plug -- has no third plug to tag; all six
      of its rows step through the instanzen tag (`kapFamilie_*`);
      `HwFeatureStep` refines the gate (`stepExtTor`): its admitted
      vector step executes exactly as the tor arm
      (`kapFamilie_feature_tor`, via `hwStepTor_verbindung_zeuge`);
    - planted refusals beside the run (forged port decode, masked
      delivery, post-nest masked delivery);
    - joint witness `kapSteps_zeuge`: all six steps, the tor-arm
      refinement step, well-formedness of every start machine, and
      shared non-degeneracy (owner-only forwarding and drains
      changing actual shared memory 0 to 42 observed from both
      cores; the NMI frame observably changes memory).
    NOT proved here, and not claimed:
    - no hardware correspondence beyond self-consistency (silicon
      and timing assumptions live in the family files, not
      re-checked here); the OUT opcode bytes are the accepted
      canonical subset, not silicon truth;
    - no W/GX bridge; no source, checker, contract, entry, ABI,
      loader, budget or liveness claim;
    - the UC-load leg still refuses on the bare machine (its answer
      lives in the device); device continuity rides the extended
      relation, not the stateless plug;
    - async/nested delivery control snapshots ride in the events;
      no independent control-state model is built here.
-/

#print axioms kapPortStart_wf
#print axioms kapPort_fetch
#print axioms kapPort_kern
#print axioms kapPlug_port
#print axioms kapStep_port
#print axioms kapPlug_nested
#print axioms kapStep_nested
#print axioms kapPlug_int
#print axioms kapStep_int
#print axioms kapSys_frei
#print axioms kapPlug_system
#print axioms kapStep_system
#print axioms kapPlug_bild
#print axioms kapStep_bild
#print axioms kapPlug_instanzen
#print axioms kapStep_instanzen
#print axioms kapSteps_wf
#print axioms kapSteps_embedded
#print axioms kapSteps_tags_disjoint
#print axioms familien_plug_gleich
#print axioms kapFamilie_muldiv
#print axioms kapFamilie_shift
#print axioms kapFamilie_setcc
#print axioms kapFamilie_cmov
#print axioms kapFamilie_fp
#print axioms kapFamilie_feature_tor
#print axioms kapPort_falschDecodiert_verweigert
#print axioms kapSteps_zeuge

end Gabbro.Grammatik.X86
