/-
  File:      Grammatik/X86/HwAddressed.lean
  Subject:   Addressed loads/stores of all widths through TSO.

  Lane 1121: base+index*scale+disp (SIB) addresses at every width
  (1/2/4/8 bytes) over the coherent machine. Addresses come from the
  accepted selected `adrEff` (AddressEncoding, never a second model);
  bytes move through the accepted width-selected `concIssue`/`concLoad`
  (ConcurrentIntegerExecution) on the shared TSO view, i.e. ordered
  `issueByte` folds with youngest-own `loadByte` forwarding. No SC word
  effect is substituted for a buffered access; partial overlap and
  tearing are refused through the accepted `WortGruppe` guards
  (HardwareExecution). Provenance: clone-local Intel SDM extracts are
  provenance only; no silicon correspondence is claimed (see CUTS).
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.AddressEncoding
import Grammatik.X86.ConcurrentIntegerExecution
import Grammatik.X86.NarrowOps
import Grammatik.X86.EffectiveAddress

namespace Gabbro.Grammatik.X86

/-! ## 1. Addressed access: selected address, width-selected bytes. -/

/-- Address of one access from the acting core's pre-state registers
    plus the next-RIP base for RIP-relative forms. -/
def hwAddrOf (m : HwMaschine) (c : Nat) (ripNext : Adresse)
    (f : AdrForm) : Adresse :=
  adrEff (projZustand m c) ripNext f

/-- Addressed store on the coherent machine: the pre-state source
    register's low bytes issue width-selected into the acting core's
    buffer (never the SC word effect); RIP advances past `len`. -/
def hwAddrStore (m : HwMaschine) (c : Nat) (b : Breite) (f : AdrForm)
    (ripNext : Adresse) (src : Register) (len : Nat) :
    Option HwMaschine :=
  match laengeOk len with
  | false => none
  | true =>
    let a := hwAddrOf m c ripNext f
    match concIssue (tsoAnsicht m) c b a ((m.kerne c).register src) with
    | none => none
    | some s' => some ({ setTso m s' with kerne := fun d => if d = c then { m.kerne c with rip := ripNach (m.kerne c).rip len } else m.kerne d })

/-- Addressed load on the coherent machine: the forwarded value merges
    into the destination with the accepted partial-register discipline
    (`mergeRegNarrow`); RIP advances past `len`. -/
def hwAddrLoad (m : HwMaschine) (c : Nat) (b : Breite) (f : AdrForm)
    (ripNext : Adresse) (dst : Register) (len : Nat) :
    Option HwMaschine :=
  match laengeOk len with
  | false => none
  | true =>
    match concLoad (tsoAnsicht m) c b (hwAddrOf m c ripNext f) with
    | none => none
    | some w => some ({ m with kerne := fun d => if d = c then { m.kerne c with register := regSet (m.kerne c).register dst (mergeRegNarrow b ((m.kerne c).register dst) w), rip := ripNach (m.kerne c).rip len } else m.kerne d })

/-- The addressed address reads the acting core's pre-state registers
    (and the RIP base for RIP-relative forms) only. -/
theorem hwAddrOf_basisForm (m : HwMaschine) (c : Nat) (base : Register)
    (disp : BitVec 32) (ripNext : Adresse) :
    hwAddrOf m c ripNext (basisForm base disp) =
      effAddr (projZustand m c) base disp := by
  unfold hwAddrOf
  rw [adrEff_basisForm]

/-- A store keeps the flags. -/
theorem hwAddrStore_flags (m m' : HwMaschine) (c : Nat)
    (b : Breite) (f : AdrForm) (ripNext : Adresse) (src : Register)
    (len : Nat)
    (h : hwAddrStore m c b f ripNext src len = some m') :
    (m'.kerne c).flags = (m.kerne c).flags := by
  unfold hwAddrStore at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hi : concIssue (tsoAnsicht m) c b (hwAddrOf m c ripNext f)
        ((m.kerne c).register src) with
    | none => simp [hi] at h
    | some s' =>
      simp [hi] at h
      cases h
      simp

/-- A store advances RIP past its length. -/
theorem hwAddrStore_rip (m m' : HwMaschine) (c : Nat)
    (b : Breite) (f : AdrForm) (ripNext : Adresse) (src : Register)
    (len : Nat)
    (h : hwAddrStore m c b f ripNext src len = some m') :
    (m'.kerne c).rip = ripNach (m.kerne c).rip len := by
  unfold hwAddrStore at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hi : concIssue (tsoAnsicht m) c b (hwAddrOf m c ripNext f)
        ((m.kerne c).register src) with
    | none => simp [hi] at h
    | some s' =>
      simp [hi] at h
      cases h
      simp

/-- A store appends exactly its width-selected bytes to the acting buffer. -/
theorem hwAddrStore_puffer (m m' : HwMaschine) (c : Nat)
    (b : Breite) (f : AdrForm) (ripNext : Adresse) (src : Register)
    (len : Nat)
    (h : hwAddrStore m c b f ripNext src len = some m') :
    m'.puffer c = m.puffer c ++
      entriesOf b (hwAddrOf m c ripNext f) ((m.kerne c).register src) := by
  unfold hwAddrStore at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hi : concIssue (tsoAnsicht m) c b (hwAddrOf m c ripNext f)
        ((m.kerne c).register src) with
    | none => simp [hi] at h
    | some s' =>
      simp [hi] at h
      cases h
      have he := concIssue_haengt_an (tsoAnsicht m) s' c b
        (hwAddrOf m c ripNext f) ((m.kerne c).register src) hi
      simpa [tsoAnsicht, setTso] using he

/-- A store changes no canonical byte (buffer only). -/
theorem hwAddrStore_kein_speicher (m m' : HwMaschine) (c : Nat)
    (b : Breite) (f : AdrForm) (ripNext : Adresse) (src : Register)
    (len : Nat) (x : Adresse)
    (h : hwAddrStore m c b f ripNext src len = some m') :
    m'.mem.bytes x = m.mem.bytes x := by
  unfold hwAddrStore at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hi : concIssue (tsoAnsicht m) c b (hwAddrOf m c ripNext f)
        ((m.kerne c).register src) with
    | none => simp [hi] at h
    | some s' =>
      simp [hi] at h
      cases h
      have he := concIssue_kein_speicher (tsoAnsicht m) s' c b
        (hwAddrOf m c ripNext f) ((m.kerne c).register src) hi x
      simpa [tsoAnsicht, setTso] using he

/-- A store preserves well-formedness (profiles untouched). -/
theorem hwAddrStore_wf (m m' : HwMaschine) (c : Nat)
    (b : Breite) (f : AdrForm) (ripNext : Adresse) (src : Register)
    (len : Nat)
    (h : hwAddrStore m c b f ripNext src len = some m')
    (hwf : HwWf m) : HwWf m' := by
  unfold hwAddrStore at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hi : concIssue (tsoAnsicht m) c b (hwAddrOf m c ripNext f)
        ((m.kerne c).register src) with
    | none => simp [hi] at h
    | some s' =>
      simp [hi] at h
      cases h
      exact hwf

/-- A load writes the destination through the accepted merge. -/
theorem hwAddrLoad_dst (m m' : HwMaschine) (c : Nat)
    (b : Breite) (f : AdrForm) (ripNext : Adresse) (dst : Register)
    (len : Nat)
    (h : hwAddrLoad m c b f ripNext dst len = some m') :
    ∃ w : Wort, concLoad (tsoAnsicht m) c b (hwAddrOf m c ripNext f) =
        some w ∧
      (m'.kerne c).register dst =
        mergeRegNarrow b ((m.kerne c).register dst) w := by
  unfold hwAddrLoad at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hl : concLoad (tsoAnsicht m) c b (hwAddrOf m c ripNext f) with
    | none => simp [hl] at h
    | some w =>
      simp [hl] at h
      cases h
      exact ⟨w, rfl, by simp [regSet_gleich]⟩

/-- A load preserves well-formedness (profiles untouched). -/
theorem hwAddrLoad_wf (m m' : HwMaschine) (c : Nat)
    (b : Breite) (f : AdrForm) (ripNext : Adresse) (dst : Register)
    (len : Nat)
    (h : hwAddrLoad m c b f ripNext dst len = some m')
    (hwf : HwWf m) : HwWf m' := by
  unfold hwAddrLoad at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hl : concLoad (tsoAnsicht m) c b (hwAddrOf m c ripNext f) with
    | none => simp [hl] at h
    | some w =>
      simp [hl] at h
      cases h
      exact hwf

/-! ## 2. Agreement: the old evaluators are lifted, never redefined. -/

/-- BRIDGE (store): on a base-plus-disp32 form the addressed store IS
    the accepted width-selected machine store. -/
theorem hwAddrStore_basisForm (m : HwMaschine) (c : Nat) (b : Breite)
    (base src : Register) (disp : BitVec 32) (ripNext : Adresse)
    (len : Nat) :
    hwAddrStore m c b (basisForm base disp) ripNext src len =
      concStoreMaschine m c b base src disp len := by
  unfold hwAddrStore concStoreMaschine hwAddrOf
  cases hlen : laengeOk len with
  | false => rfl
  | true =>
    rw [adrEff_basisForm]
    rfl

/-- BRIDGE (load): on a base-plus-disp32 form the addressed load IS
    the accepted width-selected machine load. -/
theorem hwAddrLoad_basisForm (m : HwMaschine) (c : Nat) (b : Breite)
    (dst base : Register) (disp : BitVec 32) (ripNext : Adresse)
    (len : Nat) :
    hwAddrLoad m c b (basisForm base disp) ripNext dst len =
      concLoadMaschine m c b dst base disp len := by
  unfold hwAddrLoad concLoadMaschine hwAddrOf
  cases hlen : laengeOk len with
  | false => rfl
  | true =>
    rw [adrEff_basisForm]
    rfl

/-- FORWARDING (whole access): after an addressed store from an empty
    own buffer, the addressed load on the issuing core reads the
    issued value back (accepted `concLoad_nach_concIssue`, lifted to
    selected addresses at every width). -/
theorem hwAddrWeiterleitung (m m' : HwMaschine) (c : Nat)
    (b : Breite) (f : AdrForm) (ripNext : Adresse) (src : Register)
    (len : Nat)
    (hleer : m.puffer c = [])
    (hstore : hwAddrStore m c b f ripNext src len = some m')
    (hgateL : concAdmitted m.mem (hwAddrOf m c ripNext f) b false = true) :
    concLoad (tsoAnsicht m') c b (hwAddrOf m c ripNext f) =
      match b with
      | .b8 => some (BitVec.ofNat 64 (((m.kerne c).register src).toNat % 256))
      | .b16 => some (BitVec.ofNat 64 (((m.kerne c).register src).toNat % 65536))
      | .b32 => some (BitVec.ofNat 64 (((m.kerne c).register src).toNat % 4294967296))
      | .b64 => some ((m.kerne c).register src) := by
  unfold hwAddrStore at hstore
  cases hlen : laengeOk len with
  | false => simp [hlen] at hstore
  | true =>
    simp only [hlen] at hstore
    cases hi : concIssue (tsoAnsicht m) c b (hwAddrOf m c ripNext f)
        ((m.kerne c).register src) with
    | none => simp [hi] at hstore
    | some s' =>
      simp [hi] at hstore
      cases hstore
      have hm : (tsoAnsicht { setTso m s' with kerne := fun d => if d = c then { m.kerne c with rip := ripNach (m.kerne c).rip len } else m.kerne d }) = s' := by
        cases s' with
        | mk mem puffer => rfl
      have hleer' : (tsoAnsicht m).puffer c = [] := by
        simpa [tsoAnsicht] using hleer
      cases b with
      | b8 =>
        have h := concLoad_nach_concIssue (tsoAnsicht m) s' c .b8
          (hwAddrOf m c ripNext f) ((m.kerne c).register src) hleer' hi hgateL
        rw [hm]
        simpa using h
      | b16 =>
        have h := concLoad_nach_concIssue (tsoAnsicht m) s' c .b16
          (hwAddrOf m c ripNext f) ((m.kerne c).register src) hleer' hi hgateL
        rw [hm]
        simpa using h
      | b32 =>
        have h := concLoad_nach_concIssue (tsoAnsicht m) s' c .b32
          (hwAddrOf m c ripNext f) ((m.kerne c).register src) hleer' hi hgateL
        rw [hm]
        simpa using h
      | b64 =>
        have h := concLoad_nach_concIssue (tsoAnsicht m) s' c .b64
          (hwAddrOf m c ripNext f) ((m.kerne c).register src) hleer' hi hgateL
        rw [hm]
        simpa using h

/-! ## 3. The adapter plug and planted refusals. -/

/-- Addressed family events: width-selected SIB-addressed loads and
    stores with their actual length and next-RIP base. -/
inductive HwAddrEreignis where
  | store (b : Breite) (f : AdrForm) (ripNext : Adresse) (src : Register)
    (len : Nat)
  | load (b : Breite) (f : AdrForm) (ripNext : Adresse) (dst : Register)
    (len : Nat)
  | verweigert
  deriving DecidableEq, Repr

/-- The addressed adapter: one checked event step on the coherent
    machine, reusing the accepted width-selected evaluators. -/
def adapterAddr : HwAdapter HwAddrEreignis :=
  ⟨fun m c e =>
    match e with
    | .store b f ripNext src len => hwAddrStore m c b f ripNext src len
    | .load b f ripNext dst len => hwAddrLoad m c b f ripNext dst len
    | .verweigert => none⟩

/-- The refused event admits nothing. -/
theorem adapterAddr_verweigert (m : HwMaschine) (c : Nat) :
    adapterAddr.schritt m c .verweigert = none := rfl

/-- An adapter store step is an addressed store step. -/
theorem adapterAddr_store (m m' : HwMaschine) (c : Nat)
    (b : Breite) (f : AdrForm) (ripNext : Adresse) (src : Register)
    (len : Nat)
    (h : adapterAddr.schritt m c (.store b f ripNext src len) = some m') :
    hwAddrStore m c b f ripNext src len = some m' := h

/-- A bad length refuses the addressed store on any machine. -/
theorem hwAddrStore_laenge_verweigert (m : HwMaschine) (c : Nat)
    (b : Breite) (f : AdrForm) (ripNext : Adresse) (src : Register)
    (len : Nat) (h : laengeOk len = false) :
    hwAddrStore m c b f ripNext src len = none := by
  unfold hwAddrStore
  simp [h]

/-- A bad length refuses the addressed load on any machine. -/
theorem hwAddrLoad_laenge_verweigert (m : HwMaschine) (c : Nat)
    (b : Breite) (f : AdrForm) (ripNext : Adresse) (dst : Register)
    (len : Nat) (h : laengeOk len = false) :
    hwAddrLoad m c b f ripNext dst len = none := by
  unfold hwAddrLoad
  simp [h]

/-- A refused gate refuses the addressed store: no successor. -/
theorem hwAddrStore_gate_verweigert (m : HwMaschine) (c : Nat)
    (b : Breite) (f : AdrForm) (ripNext : Adresse) (src : Register)
    (len : Nat) (hok : laengeOk len = true)
    (hgate : concIssue (tsoAnsicht m) c b (hwAddrOf m c ripNext f)
      ((m.kerne c).register src) = none) :
    hwAddrStore m c b f ripNext src len = none := by
  unfold hwAddrStore
  simp [hok, hgate]

/-- A refused gate refuses the addressed load: no successor. -/
theorem hwAddrLoad_gate_verweigert (m : HwMaschine) (c : Nat)
    (b : Breite) (f : AdrForm) (ripNext : Adresse) (dst : Register)
    (len : Nat) (hok : laengeOk len = true)
    (hgate : concLoad (tsoAnsicht m) c b (hwAddrOf m c ripNext f) = none) :
    hwAddrLoad m c b f ripNext dst len = none := by
  unfold hwAddrLoad
  simp [hok, hgate]

/-- TEARING: a partial buffer is no word group (accepted guard, lifted
    to the addressed view). -/
theorem hwAddrTeil_keine_gruppe (s : TSOZustand) (c : Nat)
    (a : Adresse) (v : Wort)
    (hne : s.puffer c ≠ wortEintraege a v) :
    ¬ WortGruppe s c a v :=
  hwTeilwort_keine_gruppe s c a v hne

/-- OVERLAP: a foreign footprint entry refuses the word group
    (accepted guard, lifted to the addressed view). -/
theorem hwAddrOverlap_keine_gruppe (s : TSOZustand) (c : Nat)
    (a : Adresse) (v : Wort) (d : Nat) (hne : d ≠ c)
    (e : TSOEintrag) (hmem : e ∈ s.puffer d)
    (hfuss : e.addr ∈ Fuss a) :
    ¬ WortGruppe s c a v :=
  hwGruppe_verweigert_bei_fremdeintrag s c a v d hne e hmem hfuss

/-! ## 4. Reached witness: two cores, SIB address, buffered store.

  Core 0 stores 4 bytes through `rbx + rcx * 8 + 0 = 8200` (scaled SIB
  form with disp8 zero), forwards the value to its own load while core
  1 still reads the old value, then drains it into shared memory where
  both cores observe it. Tearing and overlap refusals stand beside it.
  Every claim below is a closed decidable observation. -/

/-- Witness value: `0x01020304` (low byte `0x04`). -/
def hwAddrWitV : Wort := BitVec.ofNat 64 0x01020304

/-- Witness SIB form: base `rbx`, index `rcx`, scale 8, disp8 zero. -/
def hwAddrWitForm : AdrForm :=
  skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 0) .d8

/-- Witness next-RIP base (unused by non-RIP forms, fixed). -/
def hwAddrWitNext : Adresse := BitVec.ofNat 64 4103

/-- Witness data address: `8192 + 1 * 8 + 0`. -/
def hwAddrWitA : Adresse := BitVec.ofNat 64 8200

/-- Witness code bytes: zeroes (fetch never taken here;
    decode coverage is owned by the accepted producers). -/
def hwAddrWitBytes (_ : Adresse) : Byte := BitVec.ofNat 8 0

/-- Witness code permission: seven bytes at 4096. -/
def hwAddrWitCode (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4103)

/-- Witness data permission: sixteen bytes at 8192. -/
def hwAddrWitDaten (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8208)

/-- Witness shared memory. -/
def hwAddrWitMem : Speicher :=
  { bytes := hwAddrWitBytes, lesbar := hwAddrWitDaten,
    schreibbar := hwAddrWitDaten, ausfuehrbar := hwAddrWitCode }

/-- Witness core-0 registers: base, index and value. -/
def hwAddrWitReg0 : Register → Wort := fun q =>
  if q = Register.rbx then BitVec.ofNat 64 8192
  else if q = Register.rcx then BitVec.ofNat 64 1
  else if q = Register.rax then hwAddrWitV
  else if q = Register.rsp then BitVec.ofNat 64 8704
  else BitVec.ofNat 64 0

/-- Witness cores: core 0 runs at 4096, core 1 idles on the
    (non-executable) data page. -/
def hwAddrWitKern : Nat → HwKern
  | 0 => ⟨hwAddrWitReg0, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 8192, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness start machine: shared memory, two cores, empty buffers,
    full silicon with OS vector state. -/
def hwAddrWitM0 : HwMaschine :=
  ⟨hwAddrWitMem, hwAddrWitKern, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- The witness machine is well-formed: full silicon admits all. -/
theorem hwAddrWitM0_wf : HwWf hwAddrWitM0 := by
  intro c f _
  cases f <;> rfl

/-- The SIB form names the data cell from pre-state registers. -/
theorem hwAddrWit_addr :
    hwAddrOf hwAddrWitM0 0 hwAddrWitNext hwAddrWitForm = hwAddrWitA := by
  decide

/-- The SIB form is admitted as data. -/
theorem hwAddrWit_form_ok :
    adrOk hwAddrWitForm = true := by
  decide

/-- The data cell starts zeroed: the run really changes memory. -/
theorem hwAddrWit_anfang_null :
    hwAddrWitMem.bytes hwAddrWitA = BitVec.ofNat 8 0 := by
  decide

/-- The machine after the addressed 32-bit store. -/
def hwAddrWitM1 : Option HwMaschine :=
  hwAddrStore hwAddrWitM0 0 .b32 hwAddrWitForm hwAddrWitNext .rax 7

/-- The shared TSO state after the store issue. -/
def hwAddrWitT1 : Option TSOZustand := hwAddrWitM1.map tsoAnsicht

/-- Core 0 observes its own issued value (forwarding). -/
def hwAddrWitLoadEigen : Option (Option Wort) :=
  hwAddrWitT1.map (fun s => concLoad s 0 .b32 hwAddrWitA)

/-- Core 1 observes the old value (no foreign forwarding). -/
def hwAddrWitLoadFremd : Option (Option Wort) :=
  hwAddrWitT1.map (fun s => concLoad s 1 .b32 hwAddrWitA)

/-- Core 0 drains its four entries, one flush per state. -/
def hwAddrWitT2 : Option TSOZustand :=
  hwAddrWitT1.bind (fun s => flushKern s 0)

def hwAddrWitT3 : Option TSOZustand :=
  hwAddrWitT2.bind (fun s => flushKern s 0)

def hwAddrWitT4 : Option TSOZustand :=
  hwAddrWitT3.bind (fun s => flushKern s 0)

def hwAddrWitT5 : Option TSOZustand :=
  hwAddrWitT4.bind (fun s => flushKern s 0)

/-- The shared byte after the drain. -/
def hwAddrWitNachFlush : Option (Option Byte) :=
  hwAddrWitT5.map (fun s => some (s.mem.bytes hwAddrWitA))

/-- Core 1 reads the drained value from shared memory. -/
def hwAddrWitFremdNachFlush : Option (Option Wort) :=
  hwAddrWitT5.map (fun s => concLoad s 1 .b32 hwAddrWitA)

/-- The addressed store issues four buffer entries. -/
theorem hwAddrWit_store_buf :
    hwAddrWitM1.map (fun m => (m.puffer 0).length) = some 4 := by
  decide

/-- The addressed store advances RIP past its length. -/
theorem hwAddrWit_store_rip :
    hwAddrWitM1.map (fun m => (m.kerne 0).rip) =
      some (BitVec.ofNat 64 4103) := by
  decide

/-- Forwarding: core 0 reads its own unflushed store. -/
theorem hwAddrWit_weiterleitung :
    hwAddrWitLoadEigen = some (some hwAddrWitV) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem hwAddrWit_fremd_alt :
    hwAddrWitLoadFremd = some (some (BitVec.ofNat 64 0)) := by
  decide

/-- The drain changes shared memory: the cell reads `0x04`. -/
theorem hwAddrWit_spuelung :
    hwAddrWitNachFlush = some (some (BitVec.ofNat 8 4)) := by
  decide

/-- After the drain core 1 observes the new value. -/
theorem hwAddrWit_fremd_neu :
    hwAddrWitFremdNachFlush = some (some hwAddrWitV) := by
  decide

/-- Tearing state: four of eight bytes buffered on core 0. -/
def hwAddrWitTeil : TSOZustand :=
  ⟨hwAddrWitMem, fun d =>
    if d = 0 then (wortEintraege hwAddrWitA hwAddrWitV).take 4 else []⟩

/-- TEARING REFUSAL: four buffered bytes are no word group. -/
theorem hwAddrWitTeil_keine_gruppe :
    ¬ WortGruppe hwAddrWitTeil 0 hwAddrWitA hwAddrWitV := by
  apply hwAddrTeil_keine_gruppe
  decide

/-- Overlap state: a full group on core 0, a foreign entry inside its
    footprint on core 1. -/
def hwAddrWitOverlap : TSOZustand :=
  ⟨hwAddrWitMem, fun d =>
    if d = 0 then wortEintraege hwAddrWitA hwAddrWitV
    else if d = 1 then [⟨addrOff hwAddrWitA 1, BitVec.ofNat 8 9⟩] else []⟩

/-- OVERLAP REFUSAL: the foreign footprint entry breaks the group. -/
theorem hwAddrWitOverlap_keine_gruppe :
    ¬ WortGruppe hwAddrWitOverlap 0 hwAddrWitA hwAddrWitV :=
  hwAddrOverlap_keine_gruppe hwAddrWitOverlap 0 hwAddrWitA hwAddrWitV
    1 (by decide) ⟨addrOff hwAddrWitA 1, BitVec.ofNat 8 9⟩ (by decide)
    (fuss_mem_offset hwAddrWitA 1 (by decide))

/-- THE JOINT WITNESS: a reached two-core addressed run through a SIB
    form at width 4 -- selected address, buffered issue with
    register/flag/memory discipline, owner-only forwarding, observable
    drain into shared memory (0 becomes `0x04`, both cores observe) --
    beside the tearing/overlap refusals. Non-degenerate: the drain
    observably changes shared memory, and the buffered store is visible
    via forwarding to the owner only. -/
theorem hwAddrWit_zeuge :
    hwAddrOf hwAddrWitM0 0 hwAddrWitNext hwAddrWitForm = hwAddrWitA ∧
      hwAddrWitM1.map (fun m => (m.puffer 0).length) = some 4 ∧
      hwAddrWitM1.map (fun m => (m.kerne 0).rip) =
        some (BitVec.ofNat 64 4103) ∧
      hwAddrWitMem.bytes hwAddrWitA = BitVec.ofNat 8 0 ∧
      hwAddrWitLoadEigen = some (some hwAddrWitV) ∧
      hwAddrWitLoadFremd = some (some (BitVec.ofNat 64 0)) ∧
      hwAddrWitNachFlush = some (some (BitVec.ofNat 8 4)) ∧
      hwAddrWitFremdNachFlush = some (some hwAddrWitV) ∧
      ¬ WortGruppe hwAddrWitTeil 0 hwAddrWitA hwAddrWitV ∧
      ¬ WortGruppe hwAddrWitOverlap 0 hwAddrWitA hwAddrWitV ∧
      HwWf hwAddrWitM0 := by
  refine ⟨hwAddrWit_addr, hwAddrWit_store_buf, hwAddrWit_store_rip,
    hwAddrWit_anfang_null, hwAddrWit_weiterleitung, hwAddrWit_fremd_alt,
    hwAddrWit_spuelung, hwAddrWit_fremd_neu, hwAddrWitTeil_keine_gruppe,
    hwAddrWitOverlap_keine_gruppe, hwAddrWitM0_wf⟩

/- CUTS:
  Proved here, layering over (never editing) the accepted producers:
  - Selected SIB addresses (`adrEff`) at every width through the
    accepted width-selected `concIssue`/`concLoad` on the shared TSO
    view: buffer append, no canonical change, accepted
    partial-register merge, RIP/flag discipline, well-formedness
    preservation.
  - Exact agreement with the accepted evaluators: the old
    base-plus-disp32 machine steps are lifted
    (`hwAddrStore_basisForm`, `hwAddrLoad_basisForm`); whole-access
    forwarding is the accepted read-after-write value at every width
    (`hwAddrWeiterleitung`).
  - Planted refusals: bad length, refused gate (both directions),
    the refused adapter event, tearing (partial buffer is no group)
    and overlap (foreign footprint entry breaks the group).
  - Reached two-core SIB witness (`hwAddrWit_zeuge`): width-4 store
    through `rbx + rcx * 8`, owner-only forwarding, observable drain
    (0 becomes `0x04`, both cores observe), beside the refusals.
    Non-degenerate: the drain observably changes shared memory.
  NOT proved here, and not claimed:
  - No silicon correspondence: addresses and byte shapes follow the
    accepted canonical subsets with self-consistency only; Intel SDM
    extracts are provenance, not proofs.
  - No byte-codec round trip for addressed forms here: fetch/decode
    coverage stays with the accepted producers (`decodeLockAdr`,
    `decodeLea`, `decodeStoreIdx`, `concDecode`); this module takes
    decoded `AdrForm` values.
  - No LOCK/RMW path, no fault beyond the carried gate refusals, no
    per-access target-to-W/GX simulation, no whole-word atomicity
    beyond `WortGruppe`-guarded byte drains, no source/ABI/loader/
    entry/budget claim.
-/

#print axioms hwAddrOf_basisForm
#print axioms hwAddrStore_flags
#print axioms hwAddrStore_rip
#print axioms hwAddrStore_puffer
#print axioms hwAddrStore_kein_speicher
#print axioms hwAddrStore_wf
#print axioms hwAddrLoad_dst
#print axioms hwAddrLoad_wf
#print axioms hwAddrStore_basisForm
#print axioms hwAddrLoad_basisForm
#print axioms hwAddrWeiterleitung
#print axioms adapterAddr_verweigert
#print axioms adapterAddr_store
#print axioms hwAddrStore_laenge_verweigert
#print axioms hwAddrLoad_laenge_verweigert
#print axioms hwAddrStore_gate_verweigert
#print axioms hwAddrLoad_gate_verweigert
#print axioms hwAddrTeil_keine_gruppe
#print axioms hwAddrOverlap_keine_gruppe
#print axioms hwAddrWitM0_wf
#print axioms hwAddrWit_addr
#print axioms hwAddrWit_form_ok
#print axioms hwAddrWit_weiterleitung
#print axioms hwAddrWit_fremd_alt
#print axioms hwAddrWit_spuelung
#print axioms hwAddrWit_fremd_neu
#print axioms hwAddrWitTeil_keine_gruppe
#print axioms hwAddrWitOverlap_keine_gruppe
#print axioms hwAddrWit_zeuge

end Gabbro.Grammatik.X86
