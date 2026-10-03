/-
  File:      Grammatik/X86/ComposeVaCheck.lean
  Subject:   Composition closing: virtual-address closing.

  Lane 856: ONE checked closing step over already-accepted producers.
  Producers (reused by name, never re-proved): `AddressEncoding.adrEff`
  (with the pilot bridge `adrEff_basisForm`), `kanonisch48` and
  `fussZugelassen`; `AddressedHardwareExecution.adrPruefe` (with
  `adrPruefe_gleich_fuss` and the order lemmas), `adrLade`/`adrSpeichere`
  (with `adrLade_erfolg`, `adrSpeichere_erfolg`,
  `adrLade_basisForm_pilot`); `HardwareFaults.istKanonisch` and `adrKlasse`
  (with `adrKlasse_kanonisch_kein_fehler`); `ExceptionPriorityHardware`
  `SeitenInfo`/`seitenKlasse` (with both resolution lemmas).
  Consumer: the actual execution/footprint sites (`schritt`,
  `byteschritt`, `zugriff`), which discharge one data-access site by
  `ComposeVaCheck_verbindung` and refuse the planted cases. No second
  address model, decoder, executor or paging structure is invented here:
  mapped status is the caller-stated `SeitenInfo` present bit, never
  inferred from refusal.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.AddressEncoding
import Grammatik.X86.HardwareFaults
import Grammatik.X86.AddressedHardwareExecution
import Grammatik.X86.ExceptionPriorityHardware

namespace Gabbro.Grammatik.X86

/-- Canonical-form agreement: the accepted `kanonisch48` check and the
    accepted `istKanonisch` fault gate decide the same predicate. -/
theorem kanonisch48_istKanonisch (a : Adresse) :
    kanonisch48 a = istKanonisch a := rfl

/-- The one ordered closing classifier over a computed address: the
    accepted `adrPruefe` order (canonical, no-wrap, permission) mapped to
    architectural classes. Noncanonical addresses fault as #SS/#GP by the
    accepted `adrKlasse`; permission failures resolve to #GP/#PF from the
    caller-stated page state by `seitenKlasse`; the wrap edge and success
    carry no fault (validator refusal, never hardware). -/
def vaKlasse (pg : SeitenInfo) (m : Speicher) (a : Adresse)
    (schreiben stapel : Bool) : Option ArchFehler :=
  match adrPruefe m a schreiben with
  | some .unkanonisch => adrKlasse a stapel
  | some .keinLesen => some (seitenKlasse pg a)
  | some .keinSchreiben => some (seitenKlasse pg a)
  | some .umbruch => none
  | none => none

/-- SUCCESS: an admitted address carries no fault on either path. -/
theorem vaKlasse_kein_fehler (pg : SeitenInfo) (m : Speicher) (a : Adresse)
    (schreiben stapel : Bool)
    (h : adrPruefe m a schreiben = none) :
    vaKlasse pg m a schreiben stapel = none := by
  unfold vaKlasse
  rw [h]

/-- ORDER, DATA: a noncanonical data address faults as #GP before any
    access runs, even with full rights. -/
theorem vaKlasse_unkanonisch_daten (pg : SeitenInfo) (m : Speicher)
    (a : Adresse) (schreiben : Bool)
    (h : kanonisch48 a = false) :
    vaKlasse pg m a schreiben false = some .gp := by
  have hpr := adrPruefe_ordnung_kanonisch m a schreiben h
  have hk : istKanonisch a = false := by
    rw [← kanonisch48_istKanonisch]
    exact h
  unfold vaKlasse
  rw [hpr]
  simp [adrKlasse, hk]

/-- ORDER, STACK: the same noncanonical address through a stack register
    faults as #SS before any access runs. -/
theorem vaKlasse_unkanonisch_stapel (pg : SeitenInfo) (m : Speicher)
    (a : Adresse) (schreiben : Bool)
    (h : kanonisch48 a = false) :
    vaKlasse pg m a schreiben true = some .ss := by
  have hpr := adrPruefe_ordnung_kanonisch m a schreiben h
  have hk : istKanonisch a = false := by
    rw [← kanonisch48_istKanonisch]
    exact h
  unfold vaKlasse
  rw [hpr]
  simp [adrKlasse, hk]

/-- WRAP EDGE: a canonical address whose eight-byte footprint leaves the
    space is refused by the validator before permissions are consulted,
    and carries no architectural fault (validator refusal, never
    hardware, by the lane-670 precedent for decode-length refusal). -/
theorem vaKlasse_umbruch_kein_fehler (pg : SeitenInfo) (m : Speicher)
    (a : Adresse) (schreiben stapel : Bool)
    (hkan : kanonisch48 a = true)
    (hwrap : ¬ a.toNat + 8 ≤ 2 ^ 64) :
    vaKlasse pg m a schreiben stapel = none := by
  have hpr := adrPruefe_ordnung_umbruch m a schreiben hkan hwrap
  unfold vaKlasse
  rw [hpr]

/-- PERMISSION, WRITE: a canonical wrap-free address without write rights
    faults with the caller-stated page class (#GP vs #PF from the present
    bit, never inferred from the refusal). -/
theorem vaKlasse_schreib_verweigert_seite (pg : SeitenInfo) (m : Speicher)
    (a : Adresse) (stapel : Bool)
    (hkan : kanonisch48 a = true)
    (hwrap : a.toNat + 8 ≤ 2 ^ 64)
    (hperm : schreibbar8 m a = false) :
    vaKlasse pg m a true stapel = some (seitenKlasse pg a) := by
  have hpr := adrPruefe_schreib_verweigert m a hkan hwrap hperm
  unfold vaKlasse
  rw [hpr]

/-- PERMISSION, READ: a canonical wrap-free address without read rights
    faults with the caller-stated page class. -/
theorem vaKlasse_lese_verweigert_seite (pg : SeitenInfo) (m : Speicher)
    (a : Adresse) (stapel : Bool)
    (hkan : kanonisch48 a = true)
    (hwrap : a.toNat + 8 ≤ 2 ^ 64)
    (hperm : lesbar8 m a = false) :
    vaKlasse pg m a false stapel = some (seitenKlasse pg a) := by
  have hdec : decide (a.toNat + 8 ≤ 2 ^ 64) = true :=
    decide_eq_true hwrap
  have hpr : adrPruefe m a false = some .keinLesen := by
    unfold adrPruefe
    simp only [hkan, hdec, hperm, reduceCtorEq, if_false]
  unfold vaKlasse
  rw [hpr]

/-- MAPPED STATUS, ABSENT: a refused write on a non-present page faults
    as #PF. The page state is caller-stated, never inferred. -/
theorem vaKlasse_seite_fehlt_pf (pg : SeitenInfo) (m : Speicher)
    (a : Adresse) (stapel : Bool)
    (hkan : kanonisch48 a = true)
    (hwrap : a.toNat + 8 ≤ 2 ^ 64)
    (hperm : schreibbar8 m a = false)
    (hseite : pg.vorhanden a = false) :
    vaKlasse pg m a true stapel = some .pf := by
  have hcls := vaKlasse_schreib_verweigert_seite pg m a stapel hkan hwrap hperm
  rw [hcls]
  exact congrArg some (seitenKlasse_nicht_vorhanden pg a hseite)

/-- MAPPED STATUS, PRESENT: the same refused write on a present-but-denied
    page faults as #GP. -/
theorem vaKlasse_seite_da_gp (pg : SeitenInfo) (m : Speicher)
    (a : Adresse) (stapel : Bool)
    (hkan : kanonisch48 a = true)
    (hwrap : a.toNat + 8 ≤ 2 ^ 64)
    (hperm : schreibbar8 m a = false)
    (hseite : pg.vorhanden a = true) :
    vaKlasse pg m a true stapel = some .gp := by
  have hcls := vaKlasse_schreib_verweigert_seite pg m a stapel hkan hwrap hperm
  rw [hcls]
  exact congrArg some (seitenKlasse_vorhanden pg a hseite)

/-- VIRTUAL-ADDRESS CLOSING, STORE (generic, arbitrary admitted inputs):
    from the computed `adrEff` address, canonical form, wrap-free
    footprint, write rights and the real `write64` effect derive the
    checked `adrSpeichere` execution, the accepted `fussZugelassen`
    admission, absence of any fault class, and preserved permissions.
    Proved by applying the accepted producer lemmas by name; no producer
    fact is re-proved here. -/
theorem ComposeVaCheck_verbindung (m : Speicher) (s : Zustand)
    (ripNext : Adresse) (f : AdrForm) (pg : SeitenInfo) (v : Wort)
    (m' : Speicher)
    (hkan : kanonisch48 (adrEff s ripNext f) = true)
    (hwrap : (adrEff s ripNext f).toNat + 8 ≤ 2 ^ 64)
    (hperm : schreibbar8 m (adrEff s ripNext f) = true)
    (hwr : write64 m (adrEff s ripNext f) v = some m') :
    adrSpeichere m s ripNext f v = .inl m' ∧
      fussZugelassen m (adrEff s ripNext f) true = true ∧
      (∀ stapel : Bool,
        vaKlasse pg m (adrEff s ripNext f) true stapel = none) ∧
      m'.lesbar = m.lesbar ∧ m'.schreibbar = m.schreibbar ∧
        m'.ausfuehrbar = m.ausfuehrbar := by
  have hpr : adrPruefe m (adrEff s ripNext f) true = none :=
    adrPruefe_schreib_frei m (adrEff s ripNext f) hkan hwrap hperm
  have hfuss : fussZugelassen m (adrEff s ripNext f) true = true :=
    (adrPruefe_gleich_fuss m (adrEff s ripNext f) true).mp hpr
  have hklasse : ∀ stapel : Bool,
      vaKlasse pg m (adrEff s ripNext f) true stapel = none := by
    intro stapel
    exact vaKlasse_kein_fehler pg m (adrEff s ripNext f) true stapel hpr
  have heff : adrSpeichere m s ripNext f v = .inl m' := by
    simp only [adrSpeichere, hpr, hwr]
  have hperm2 :=
    write64_erhaelt_berechtigungen m (adrEff s ripNext f) v m' hwr
  exact ⟨heff, hfuss, hklasse, hperm2.1, hperm2.2.1, hperm2.2.2⟩

/-- VIRTUAL-ADDRESS CLOSING, LOAD (generic, arbitrary admitted inputs):
    from the computed `adrEff` address, canonical form, wrap-free
    footprint, read rights and the real `read64` effect derive the checked
    `adrLade` execution, the accepted `fussZugelassen` admission and
    absence of any fault class. -/
theorem ComposeVaCheck_verbindung_lese (m : Speicher) (s : Zustand)
    (ripNext : Adresse) (f : AdrForm) (pg : SeitenInfo) (v : Wort)
    (hkan : kanonisch48 (adrEff s ripNext f) = true)
    (hwrap : (adrEff s ripNext f).toNat + 8 ≤ 2 ^ 64)
    (hperm : lesbar8 m (adrEff s ripNext f) = true)
    (hrd : read64 m (adrEff s ripNext f) = some v) :
    adrLade m s ripNext f = .inl v ∧
      fussZugelassen m (adrEff s ripNext f) false = true ∧
      (∀ stapel : Bool,
        vaKlasse pg m (adrEff s ripNext f) false stapel = none) := by
  have hdec : decide ((adrEff s ripNext f).toNat + 8 ≤ 2 ^ 64) = true :=
    decide_eq_true hwrap
  have hpr : adrPruefe m (adrEff s ripNext f) false = none := by
    unfold adrPruefe
    simp only [hkan, hdec, hperm, reduceCtorEq, if_false]
  have hfuss : fussZugelassen m (adrEff s ripNext f) false = true :=
    (adrPruefe_gleich_fuss m (adrEff s ripNext f) false).mp hpr
  have hklasse : ∀ stapel : Bool,
      vaKlasse pg m (adrEff s ripNext f) false stapel = none := by
    intro stapel
    exact vaKlasse_kein_fehler pg m (adrEff s ripNext f) false stapel hpr
  have heff : adrLade m s ripNext f = .inl v := by
    simp only [adrLade, hpr, hrd]
  exact ⟨heff, hfuss, hklasse⟩

/-- PILOT BRIDGE: on the pilot-owned base-plus-displacement shape the
    composed load reads the PILOT `effAddr` (by reuse of
    `adrEff_basisForm` and `adrLade_basisForm_pilot`, never a second
    address model), with the accepted admission and no fault class. -/
theorem ComposeVaCheck_pilot (m : Speicher) (s : Zustand)
    (b : Register) (d : BitVec 32) (n : Adresse) (pg : SeitenInfo)
    (v : Wort)
    (h : adrLade m s n (basisForm b d) = .inl v) :
    read64 m (effAddr s b d) = some v ∧
      fussZugelassen m (effAddr s b d) false = true ∧
      (∀ stapel : Bool,
        vaKlasse pg m (effAddr s b d) false stapel = none) := by
  have hrd := adrLade_basisForm_pilot m s b d n v h
  have hpr : adrPruefe m (adrEff s n (basisForm b d)) false = none := by
    cases hc : adrPruefe m (adrEff s n (basisForm b d)) false with
    | some e =>
      unfold adrLade at h
      simp [hc] at h
    | none => rfl
  rw [adrEff_basisForm] at hpr
  have hfuss : fussZugelassen m (effAddr s b d) false = true :=
    (adrPruefe_gleich_fuss m (effAddr s b d) false).mp hpr
  have hklasse : ∀ stapel : Bool,
      vaKlasse pg m (effAddr s b d) false stapel = none := by
    intro stapel
    exact vaKlasse_kein_fehler pg m (effAddr s b d) false stapel hpr
  exact ⟨hrd, hfuss, hklasse⟩

/-- PLANTED REFUSAL, HOLE DATA: the noncanonical hole address faults as
    #GP on the data path for every memory and page state. -/
theorem vaCheck_loch_daten_gp (pg : SeitenInfo) (m : Speicher)
    (schreiben : Bool) :
    vaKlasse pg m (BitVec.ofNat 64 (2 ^ 47)) schreiben false =
      some .gp :=
  vaKlasse_unkanonisch_daten pg m _ schreiben kanonisch48_loch

/-- PLANTED REFUSAL, HOLE STACK: the same hole faults as #SS on the
    stack path. -/
theorem vaCheck_loch_stapel_ss (pg : SeitenInfo) (m : Speicher)
    (schreiben : Bool) :
    vaKlasse pg m (BitVec.ofNat 64 (2 ^ 47)) schreiben true =
      some .ss :=
  vaKlasse_unkanonisch_stapel pg m _ schreiben kanonisch48_loch

/-- PLANTED EDGE, WRAP: the top-of-space address is canonical (high
    half) but admits no eight-byte footprint: ordered refusal before
    permissions, and no architectural fault. -/
theorem vaCheck_rand_kein_fehler (pg : SeitenInfo) (m : Speicher)
    (schreiben stapel : Bool) :
    vaKlasse pg m (BitVec.ofNat 64 (2 ^ 64 - 4)) schreiben stapel =
      none :=
  vaKlasse_umbruch_kein_fehler pg m _ schreiben stapel
    (by decide) (by decide)

/-- Dark memory: zeroed bytes, no rights anywhere (fault witness). -/
def dunkelVaSpeicher : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0
    lesbar := fun _ => false
    schreibbar := fun _ => false
    ausfuehrbar := fun _ => false }

/-- Absent page state: no page present (fault witness for #PF). -/
def dunkelVaSeite : SeitenInfo :=
  ⟨fun _ => false⟩

/-- PLANTED REFUSAL, DARK STORE: a canonical wrap-free address with dark
    memory admits no checked store step. -/
theorem vaCheck_dunkel_verweigert (s : Zustand) (ripNext : Adresse)
    (f : AdrForm) (v : Wort)
    (hkan : kanonisch48 (adrEff s ripNext f) = true)
    (hwrap : (adrEff s ripNext f).toNat + 8 ≤ 2 ^ 64) :
    adrSpeichere dunkelVaSpeicher s ripNext f v = .inr .keinSchreiben := by
  have hperm : schreibbar8 dunkelVaSpeicher (adrEff s ripNext f) = false :=
    by rfl
  have hpr := adrPruefe_schreib_verweigert dunkelVaSpeicher
    (adrEff s ripNext f) hkan hwrap hperm
  simp only [adrSpeichere, hpr]

/-- PLANTED CLASS, DARK PAGE: the same refused store on the absent page
    faults as #PF. -/
theorem vaCheck_dunkel_pf (s : Zustand) (ripNext : Adresse)
    (f : AdrForm) (stapel : Bool)
    (hkan : kanonisch48 (adrEff s ripNext f) = true)
    (hwrap : (adrEff s ripNext f).toNat + 8 ≤ 2 ^ 64) :
    vaKlasse dunkelVaSeite dunkelVaSpeicher (adrEff s ripNext f) true
      stapel = some .pf := by
  have hperm : schreibbar8 dunkelVaSpeicher (adrEff s ripNext f) = false :=
    by rfl
  have hseite : dunkelVaSeite.vorhanden (adrEff s ripNext f) = false := rfl
  exact vaKlasse_seite_fehlt_pf dunkelVaSeite dunkelVaSpeicher
    (adrEff s ripNext f) stapel hkan hwrap hperm hseite

/-- Witness successor memory: `42` stored at 8192 over zeroed bytes. -/
def witVaNach : Speicher :=
  { zeugeSpeicher with bytes := writeBytes zeugeSpeicher (BitVec.ofNat 64 8192) 42 }

/-- JOINT WITNESS for `ComposeVaCheck_verbindung`: all four premises are
    instantiated jointly on concrete values (`rsp + 0 = 8192` through the
    pilot-owned shape, witness memory), together with the composed
    checked-store execution itself, the observably changed byte, and the
    non-degenerate memory-changing reached run (the accepted mov/store/load
    witness reaches byte 42 at 8192 from zero). -/
theorem ComposeVaCheck_verbindung_zeuge :
    ∃ (m : Speicher) (s : Zustand) (ripNext : Adresse) (f : AdrForm)
      (pg : SeitenInfo) (v : Wort) (m' : Speicher),
      kanonisch48 (adrEff s ripNext f) = true ∧
      (adrEff s ripNext f).toNat + 8 ≤ 2 ^ 64 ∧
      schreibbar8 m (adrEff s ripNext f) = true ∧
      write64 m (adrEff s ripNext f) v = some m' ∧
      adrSpeichere m s ripNext f v = .inl m' ∧
      vaKlasse pg m (adrEff s ripNext f) true false = none ∧
      m'.bytes (adrEff s ripNext f) ≠ m.bytes (adrEff s ripNext f) ∧
      ((lauf zeugeProg zeugeZustand).map
        (fun s' => s'.speicher.bytes (BitVec.ofNat 64 8192)) =
        some (BitVec.ofNat 8 42)) ∧
      m.bytes (adrEff s ripNext f) = BitVec.ofNat 8 0 := by
  have haddr : adrEff zeugeZustand 0 (basisForm .rsp (BitVec.ofNat 32 0)) = BitVec.ofNat 64 8192 := by
    decide
  have hperm8192 : schreibbar8 zeugeSpeicher (BitVec.ofNat 64 8192) = true :=
    rfl
  have hwr8192 : write64 zeugeSpeicher (BitVec.ofNat 64 8192) 42 = some witVaNach := by
    unfold write64 witVaNach
    rw [if_pos hperm8192]
  have hkan : kanonisch48 (adrEff zeugeZustand 0 (basisForm .rsp (BitVec.ofNat 32 0))) = true := by
    rw [haddr]
    exact kanonisch48_8192
  have hwrap : (adrEff zeugeZustand 0 (basisForm .rsp (BitVec.ofNat 32 0))).toNat + 8 ≤ 2 ^ 64 := by
    rw [haddr]
    decide
  have hperm : schreibbar8 zeugeSpeicher (adrEff zeugeZustand 0 (basisForm .rsp (BitVec.ofNat 32 0))) = true := by
    rw [haddr]
    exact hperm8192
  have hwr : write64 zeugeSpeicher (adrEff zeugeZustand 0 (basisForm .rsp (BitVec.ofNat 32 0))) 42 = some witVaNach := by
    rw [haddr]
    exact hwr8192
  have hconn := ComposeVaCheck_verbindung zeugeSpeicher zeugeZustand 0 (basisForm .rsp (BitVec.ofNat 32 0)) ⟨fun _ => true⟩ 42 witVaNach hkan hwrap hperm hwr
  have hhit := writeBytesN_hit zeugeSpeicher (BitVec.ofNat 64 8192) 42 8 0 (by decide) (by decide)
  rw [addrOff_null] at hhit
  have hchg : witVaNach.bytes (BitVec.ofNat 64 8192) ≠ zeugeSpeicher.bytes (BitVec.ofNat 64 8192) := by
    show writeBytes zeugeSpeicher (BitVec.ofNat 64 8192) 42 (BitVec.ofNat 64 8192) ≠ zeugeSpeicher.bytes (BitVec.ofNat 64 8192)
    unfold writeBytes
    rw [hhit]
    decide
  have hlauf := zeuge_speicher_aendert_sich
  refine ⟨zeugeSpeicher, zeugeZustand, 0, basisForm .rsp (BitVec.ofNat 32 0), ⟨fun _ => true⟩, 42, witVaNach, hkan, hwrap, hperm, hwr, hconn.1, hconn.2.2.1 false, ?_, hlauf.2.1, ?_⟩
  · rw [haddr]
    exact hchg
  · rw [haddr]
    exact hlauf.2.2

/-- JOINT WITNESS for `ComposeVaCheck_verbindung_lese`: the same concrete
    address after the witnessed store reads `42` back through the composed
    checked load, with the applied closing beside it. -/
theorem ComposeVaCheck_verbindung_lese_zeige :
    ∃ (m : Speicher) (s : Zustand) (ripNext : Adresse) (f : AdrForm)
      (pg : SeitenInfo) (v : Wort),
      kanonisch48 (adrEff s ripNext f) = true ∧
      (adrEff s ripNext f).toNat + 8 ≤ 2 ^ 64 ∧
      lesbar8 m (adrEff s ripNext f) = true ∧
      read64 m (adrEff s ripNext f) = some v ∧
      adrLade m s ripNext f = .inl v ∧
      vaKlasse pg m (adrEff s ripNext f) false false = none := by
  have haddr : adrEff zeugeZustand 0 (basisForm .rsp (BitVec.ofNat 32 0)) = BitVec.ofNat 64 8192 := by
    decide
  have hrd_perm : lesbar8 zeugeSpeicher (BitVec.ofNat 64 8192) = true :=
    rfl
  have hwr8192 : write64 zeugeSpeicher (BitVec.ofNat 64 8192) 42 = some witVaNach := by
    have hperm8192b : schreibbar8 zeugeSpeicher (BitVec.ofNat 64 8192) = true :=
      rfl
    unfold write64 witVaNach
    rw [if_pos hperm8192b]
  have hkan : kanonisch48 (adrEff zeugeZustand 0 (basisForm .rsp (BitVec.ofNat 32 0))) = true := by
    rw [haddr]
    exact kanonisch48_8192
  have hwrap : (adrEff zeugeZustand 0 (basisForm .rsp (BitVec.ofNat 32 0))).toNat + 8 ≤ 2 ^ 64 := by
    rw [haddr]
    decide
  have hperm : lesbar8 witVaNach (adrEff zeugeZustand 0 (basisForm .rsp (BitVec.ofNat 32 0))) = true := by
    rw [haddr]
    rfl
  have hrd : read64 witVaNach (adrEff zeugeZustand 0 (basisForm .rsp (BitVec.ofNat 32 0))) = some 42 := by
    rw [haddr]
    exact read64_nach_write64 zeugeSpeicher witVaNach (BitVec.ofNat 64 8192) 42 hwr8192 hrd_perm
  have hconn := ComposeVaCheck_verbindung_lese witVaNach zeugeZustand 0 (basisForm .rsp (BitVec.ofNat 32 0)) ⟨fun _ => true⟩ 42 hkan hwrap hperm hrd
  exact ⟨witVaNach, zeugeZustand, 0, basisForm .rsp (BitVec.ofNat 32 0), ⟨fun _ => true⟩, 42, hkan, hwrap, hperm, hrd, hconn.1, hconn.2.2 false⟩

/- CUTS:
    Proved here: canonical-form agreement (`kanonisch48_istKanonisch`);
    the one ordered closing classifier (`vaKlasse`) with its success
    case, data/stack order pins (#GP/#SS before any access), the
    wrap-edge no-fault case, read/write permission resolution to the
    caller-stated page class, and both #PF/#GP page resolutions; the
    store and load closings (`ComposeVaCheck_verbindung`,
    `ComposeVaCheck_verbindung_lese`) from the computed `adrEff`
    address through admission, real effects and preserved permissions;
    the pilot bridge (`ComposeVaCheck_pilot`); planted hole, wrap-edge,
    dark-memory and dark-page refusals; joint `_zeuge` companions with
    the composed checked steps executing, an observably changed byte,
    and the accepted memory-changing reached run.
    NOT proved here, and not claimed:
    - No hardware correspondence: address math reuses the accepted
      `adrEff`/`effAddr`, faults are the accepted permission-checked
      `read64`/`write64` outcomes plus caller-stated classes, not silicon.
    - No paging-structure truth: `SeitenInfo.vorhanden` is an explicit
      caller-stated input (lane 738 interface), never inferred from
      refusal; page-table walks stay OPEN.
    - No wrap-edge fault class: `umbruch` maps to `none` (validator
      refusal, never hardware, by the lane-670 precedent); whether
      silicon faults a wrapping footprint is not decided here.
    - No native scaled-index step: `adrEff` beyond the pilot shape runs
      through the accepted adapter (`adrLade`/`adrSpeichere`,
      `lockXaddAdr`); a new SIB `schritt` row stays with its producer.
    - No TSO/GX bridge: effects are sequential `read64`/`write64`
      outcomes, not atomic multi-byte events and not an interleaving
      trace; tearing, visibility and grouping stay OPEN (TSO-bridge lane).
    - No source correspondence, no ABI/loader/entry/budget/cost claim;
      no whole-image and no full source-to-byte validation claim.
    - Missing producer legs (explicit, owning lanes named, never
      assumed): arbitrary-input decoder length soundness (lane 279, open
      per `Byteschritt` CUTS); full selected-form execution beyond the
      accepted adapter rows (integer666/locked662/FP668 consumers).
-/

#print axioms kanonisch48_istKanonisch
#print axioms vaKlasse_kein_fehler
#print axioms vaKlasse_unkanonisch_daten
#print axioms vaKlasse_unkanonisch_stapel
#print axioms vaKlasse_umbruch_kein_fehler
#print axioms vaKlasse_schreib_verweigert_seite
#print axioms vaKlasse_lese_verweigert_seite
#print axioms vaKlasse_seite_fehlt_pf
#print axioms vaKlasse_seite_da_gp
#print axioms ComposeVaCheck_verbindung
#print axioms ComposeVaCheck_verbindung_lese
#print axioms ComposeVaCheck_pilot
#print axioms vaCheck_loch_daten_gp
#print axioms vaCheck_loch_stapel_ss
#print axioms vaCheck_rand_kein_fehler
#print axioms vaCheck_dunkel_verweigert
#print axioms vaCheck_dunkel_pf
#print axioms ComposeVaCheck_verbindung_zeuge
#print axioms ComposeVaCheck_verbindung_lese_zeige

end Gabbro.Grammatik.X86
