/-
  File:      Grammatik/X86/SfenceStoreNarrow.lean
  Subject:   SFENCE store narrowness: the narrower store-ordering fence,
             distinct from MFENCE, over the canonical TSO/machine state.

  Lane 781 (Lean-first). Manual provenance (local snapshot
  `.tmp/HARDWARE-REFERENCES/`, Intel SDM 325462-093US Sep 2026):
  SFENCE entry Vol. 2B 4-628 (txt lines 94415-94451): opcode
  `NP 0F AE F8`, Op/En ZO, "Serializes store operations"; Description:
  "every store prior to SFENCE is globally visible before any store
  after SFENCE becomes globally visible", "ordered with respect to
  memory stores, other SFENCE instructions, MFENCE instructions, and
  any serializing instructions", "not ordered with respect to memory
  loads or the LFENCE instruction"; ModR/M byte F8 with the r/m field
  ignored ("any opcode of the form 0F AE Fx, where x is in 8-F");
  Operation `Wait_On_Following_Stores_Until(...)`; Exceptions: #UD if
  CPUID.01H:EDX.SSE[25] = 0, #UD if the LOCK prefix is used. Vol. 1
  §10.4.6.4 (txt lines 15087-15092) states the same store-only fence.
  Reuses `Zustand`/`TSOZustand`/`LockMaschine`, `drainVoll`,
  `zaunBereit`, the accepted `decodeExt` dispatcher (tried first, never
  shadowed) and the accepted MFENCE side for the proved gate
  distinction. No source/checker/goal change.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.TSO
import Grammatik.X86.FenceDrain
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.LockedOps
import Grammatik.X86.LockedInstructionExecution
import Grammatik.X86.FeatureProfile
import Grammatik.X86.Byteschritt

namespace Gabbro.Grammatik.X86

/-- The single admitted SFENCE store-fence form. The manual's F8..FF
    range denotes one instruction; there are no operand variants. -/
inductive SfenceForm where
  | sfence
  deriving DecidableEq, Repr

/-- Canonical SFENCE bytes: 0F AE F8 (manual opcode table). -/
def pinSfence : List Byte := [natByte 15, natByte 174, natByte 248]

/-- Architectural #UD grounds the byte layer parses or gates but never
    executes: no silicon SSE (manual Exceptions: CPUID.01H:EDX.SSE[25]
    = 0), and LOCK before the fence (manual Exceptions: LOCK prefix).
    Distinct from `LockUdGrund.sse2Fehlt`: SFENCE needs SSE, MFENCE
    needs SSE2. -/
inductive SfenceUdGrund where
  | sseFehlt
  | lockAufZaun
  deriving DecidableEq, Repr

/-- One parsed SFENCE instruction: the admitted store fence, or a
    parsed architectural #UD, each with its consumed length. -/
inductive SfenceAnweisung where
  | ok (f : SfenceForm) (len : Nat)
  | ud (g : SfenceUdGrund) (len : Nat)
  deriving DecidableEq, Repr

/-- Consumed length of one parsed SFENCE instruction. -/
def sfenceLaenge : SfenceAnweisung → Nat
  | .ok _ len => len
  | .ud _ len => len

/-! ## 1. Byte codec: the F8 row plus the LOCK-prefix #UD.

    The manual ignores the r/m field, so every ModR/M byte F8..FF
    (mod=3, reg=7) after 0F AE denotes SFENCE; the neighbouring 0F AE
    rows (MFENCE F0..F7 with reg=6, LFENCE E8..EF, memory CLFLUSH
    shapes) refuse with `none` here -- they belong to their own
    decoders, never to this one. LOCK before an SFENCE shape parses to
    the fence #UD with length 4 (mirroring the accepted LOCK-fence
    marker, on the disjoint reg=7 field, so no accepted row is
    shadowed). -/

/-- SFENCE byte decode: the bare F8..FF row, or LOCK before that row
    as the parsed fence #UD. Everything else refuses. -/
def decodeSfence : List Byte → Option (SfenceAnweisung × List Byte)
  | [] => none
  | b0 :: rest0 =>
    if byteNat b0 == 240 then
      match rest0 with
      | b1 :: b2 :: m :: rest =>
        if byteNat b1 == 15 && byteNat b2 == 174 && 248 ≤ byteNat m then
          some (.ud .lockAufZaun 4, rest)
        else none
      | _ => none
    else if byteNat b0 == 15 then
      match rest0 with
      | b1 :: m :: rest =>
        if byteNat b1 == 174 && 248 ≤ byteNat m then
          some (.ok .sfence 3, rest)
        else none
      | _ => none
    else none

/-- Round trip: the canonical bytes decode to the fence with no rest. -/
theorem roundtrip_sfence (suffix : List Byte) :
    decodeSfence (pinSfence ++ suffix) =
      some (SfenceAnweisung.ok .sfence 3, suffix) := by
  rfl

/-- The manual ignores the r/m field: every ModR/M byte F8..FF
    denotes the same fence. F8 is `roundtrip_sfence`; the rest pins. -/
theorem decodeSfence_ignoriert_rm :
    decodeSfence [natByte 15, natByte 174, natByte 249] =
      some (SfenceAnweisung.ok .sfence 3, []) ∧
    decodeSfence [natByte 15, natByte 174, natByte 250] =
      some (SfenceAnweisung.ok .sfence 3, []) ∧
    decodeSfence [natByte 15, natByte 174, natByte 251] =
      some (SfenceAnweisung.ok .sfence 3, []) ∧
    decodeSfence [natByte 15, natByte 174, natByte 252] =
      some (SfenceAnweisung.ok .sfence 3, []) ∧
    decodeSfence [natByte 15, natByte 174, natByte 253] =
      some (SfenceAnweisung.ok .sfence 3, []) ∧
    decodeSfence [natByte 15, natByte 174, natByte 254] =
      some (SfenceAnweisung.ok .sfence 3, []) ∧
    decodeSfence [natByte 15, natByte 174, natByte 255] =
      some (SfenceAnweisung.ok .sfence 3, []) := by
  decide

/-- LOCK before the SFENCE shape parses to the fence #UD, never to a
    fence step. -/
theorem pin_sfence_lock_ud :
    decodeSfence [natByte 240, natByte 15, natByte 174, natByte 248] =
      some (SfenceAnweisung.ud .lockAufZaun 4, []) := by
  decide

/-- Explicit neighbour refusals: the MFENCE row (lane 662 owns it),
    the LFENCE row, a CLFLUSH memory shape (mod=0, reg=7), truncations
    and a wrong escape opcode are all `none` here. -/
theorem pin_sfence_verweigert_nachbarn :
    decodeSfence [natByte 15, natByte 174, natByte 240] = none ∧
    decodeSfence [natByte 15, natByte 174, natByte 232] = none ∧
    decodeSfence [natByte 15, natByte 174, natByte 56] = none ∧
    decodeSfence [natByte 240, natByte 15, natByte 174, natByte 240] =
      none ∧
    decodeSfence [natByte 15, natByte 174] = none ∧
    decodeSfence [natByte 15] = none ∧
    decodeSfence ([] : List Byte) = none ∧
    decodeSfence [natByte 15, natByte 175, natByte 248] = none := by
  decide

/-- The accepted unified dispatcher refuses the SFENCE bytes: no older
    row is shadowed by §1. -/
theorem pin_sfence_ext_verweigert :
    decodeExt pinSfence = none := by
  decide

/-! ## 2. Store-only ordering: the manual's Description as data.

    "Ordered with respect to memory stores, other SFENCE instructions,
    MFENCE instructions, and any serializing instructions. It is not
    ordered with respect to memory loads or the LFENCE instruction."
    (SFENCE entry, Description). The execution side (§3-§4) discharges
    the store half through the canonical drain and the load half by
    leaving every load observation untouched. -/

/-- Memory operation kinds the fence may or may not order. -/
inductive SpeicherZugriff where
  | lese
  | schreibe
  deriving DecidableEq, Repr

/-- SFENCE orders exactly store-before-store pairs across it. -/
def sfenceOrdnet : SpeicherZugriff → SpeicherZugriff → Bool
  | .schreibe, .schreibe => true
  | _, _ => false

/-- The store half: preceding stores are ordered past the fence. -/
theorem sfence_ordnet_schreibe :
    sfenceOrdnet .schreibe .schreibe = true := by
  decide

/-- The narrow half: no load pair is ordered by SFENCE -- the clause
    the MFENCE full fence does not share. -/
theorem sfence_ordnet_last_nicht :
    sfenceOrdnet .lese .lese = false ∧
    sfenceOrdnet .schreibe .lese = false ∧
    sfenceOrdnet .lese .schreibe = false := by
  decide

/-! ## 3. Execution: the SSE gate plus the empty-buffer admission.

    `sse` is the named silicon premise (CPUID.01H:EDX.SSE[25]): without
    it the manual raises #UD. With silicon SSE, the fence gates on the
    empty own buffer -- the exact admitted elimination premise: an
    SFENCE over an empty buffer is fence-only and changes no observable
    memory state; over a pending buffer it refuses instead of silently
    passing. Only RIP advances; registers, flags, memory and every
    buffer are kept, and the event is the fence-only record shared with
    the accepted MFENCE shape (`istZaun`, no RMW). -/

/-- SFENCE execution outcome: success with its fence event; the
    manual's architectural #UD exactly where stated; profile refusal
    (non-empty own buffer, bad length). Admission refusals are never
    #UD claims. -/
inductive SfenceAusgang where
  | ok (m : LockMaschine) (ev : LockEreignis)
  | udFehler (g : SfenceUdGrund)
  | verweigert

/-- One SFENCE step on core `c`. -/
def sfenceSchritt (a : SfenceAnweisung) (c : Nat) (m : LockMaschine)
    (sse : Bool) : SfenceAusgang :=
  match a with
  | .ud g _ => .udFehler g
  | .ok .sfence len =>
    match laengeOk len with
    | false => .verweigert
    | true =>
      if sse then
        match m.puffer c with
        | _ :: _ => .verweigert
        | [] =>
          .ok ⟨{ m.zu with rip := ripNach m.zu.rip len }, m.puffer⟩
            ⟨c, [], [], none, none, false, true⟩
      else .udFehler .sseFehlt

/-- Length 3 is instruction-length valid. -/
theorem sfence_len_ok : laengeOk 3 = true := by
  decide

/-- SFENCE success: only RIP advances past the 3 bytes; memory and
    every buffer are untouched and the event is fence-only. -/
theorem sfence_erfolg (m : LockMaschine) (c : Nat) (sse : Bool)
    (hsse : sse = true)
    (hbuf : m.puffer c = [])
    (hok : laengeOk 3 = true) :
    sfenceSchritt (.ok .sfence 3) c m sse =
      .ok ⟨{ m.zu with rip := ripNach m.zu.rip 3 }, m.puffer⟩
        ⟨c, [], [], none, none, false, true⟩ := by
  unfold sfenceSchritt
  simp [hsse, hbuf, hok]

/-- No silicon SSE is the manual's #UD, whatever the buffer holds. -/
theorem sfence_ohne_sse (m : LockMaschine) (c : Nat) (sse : Bool)
    (hsse : sse = false)
    (hok : laengeOk 3 = true) :
    sfenceSchritt (.ok .sfence 3) c m sse = .udFehler .sseFehlt := by
  unfold sfenceSchritt
  simp [hsse, hok]

/-- A pending own store refuses the fence: the elimination premise is
    exact -- no silent skip over buffered stores. -/
theorem sfence_puffer_verweigert (m : LockMaschine) (c : Nat)
    (sse : Bool)
    (hsse : sse = true)
    (e : TSOEintrag) (rest : List TSOEintrag)
    (hbuf : m.puffer c = e :: rest)
    (hok : laengeOk 3 = true) :
    sfenceSchritt (.ok .sfence 3) c m sse = .verweigert := by
  unfold sfenceSchritt
  simp [hsse, hbuf, hok]

/-- A parsed #UD never executes: it answers the #UD outcome. -/
theorem sfence_ud (g : SfenceUdGrund) (len : Nat) (c : Nat)
    (m : LockMaschine) (sse : Bool) :
    sfenceSchritt (.ud g len) c m sse = .udFehler g := by
  rfl

/-- Success shape: silicon SSE plus an empty own buffer force exactly
    the fence-only successor and the fence-only event. -/
theorem sfence_erfolg_form (m m' : LockMaschine) (c : Nat)
    (sse : Bool) (ev : LockEreignis)
    (h : sfenceSchritt (.ok .sfence 3) c m sse = .ok m' ev) :
    sse = true ∧ m.puffer c = [] ∧
    m' = ⟨{ m.zu with rip := ripNach m.zu.rip 3 }, m.puffer⟩ ∧
    ev = ⟨c, [], [], none, none, false, true⟩ := by
  unfold sfenceSchritt at h
  by_cases hsse : sse = true
  · simp only [hsse, if_true] at h
    by_cases hbuf : m.puffer c = []
    · simp only [hbuf, sfence_len_ok] at h
      cases h
      exact ⟨hsse, hbuf, rfl, rfl⟩
    · cases hne : m.puffer c with
      | nil => exact absurd hne hbuf
      | cons e rest =>
        simp only [hne, sfence_len_ok] at h
        cases h
  · have hsse' : sse = false := by
      cases sse with
      | false => rfl
      | true => exact absurd rfl hsse
    simp only [hsse', sfence_len_ok] at h
    cases h

/-- Success keeps the whole TSO projection: memory and every buffer.
    This is the admitted elimination content -- over an empty buffer
    the fence is TSO-observably the identity. -/
theorem sfence_behaelt_tso (m m' : LockMaschine) (c : Nat)
    (sse : Bool) (ev : LockEreignis)
    (h : sfenceSchritt (.ok .sfence 3) c m sse = .ok m' ev) :
    toTSO m' = toTSO m := by
  have hf := sfence_erfolg_form m m' c sse ev h
  rw [hf.2.2.1]
  simp [toTSO]

/-- Registers and flags are untouched (the entry states no register or
    flag effect: ZO encoding with no Flags section). -/
theorem sfence_behaelt_register_flags (m m' : LockMaschine) (c : Nat)
    (sse : Bool) (ev : LockEreignis)
    (h : sfenceSchritt (.ok .sfence 3) c m sse = .ok m' ev) :
    m'.zu.register = m.zu.register ∧ m'.zu.flags = m.zu.flags := by
  have hf := sfence_erfolg_form m m' c sse ev h
  rw [hf.2.2.1]
  exact ⟨rfl, rfl⟩

/-- Loads are unaffected by the admitted fence: a subsequent load
    reads exactly what it read before -- the load half of §2,
    executed on the canonical state. -/
theorem sfence_last_unveraendert (m m' : LockMaschine) (c : Nat)
    (sse : Bool) (ev : LockEreignis)
    (h : sfenceSchritt (.ok .sfence 3) c m sse = .ok m' ev)
    (a : Adresse) :
    loadByte (toTSO m') c a = loadByte (toTSO m) c a := by
  have hf := sfence_erfolg_form m m' c sse ev h
  rw [hf.2.2.1]
  simp [toTSO]

/-- The SFENCE gate is the accepted fence gate: on the same projected
    state the accepted `lockSchritt` fence is the fence-only identity
    exactly when this gate passes. -/
theorem sfence_mfence_gleiches_tor (m : LockMaschine) (c : Nat)
    (hbuf : m.puffer c = []) :
    lockSchritt .mfence c (toTSO m) =
      some (toTSO m, ⟨c, [], [], none, none, false, true⟩) := by
  exact lockVoll_mfence_adapter m c hbuf

/-! ## 4. Fetched layer: reuse the unified dispatcher, then SFENCE.

    `decodeSfenceExt` tries the accepted `decodeExt` first and consults
    the SFENCE rows only where every older decoder refuses: no older
    form is shadowed, and no SFENCE row steals older bytes, by
    construction. Fetch reuses the canonical executable window
    (`geholt`), the 3-byte length and the execute-permission prefix
    (`ausfuehrbarN`); the fetched step runs `sfenceSchritt` on the
    fetched instruction only. -/

/-- Combined decode: the accepted unified dispatcher first, the SFENCE
    rows only where it refuses. -/
def decodeSfenceExt : List Byte → Option (SfenceAnweisung × List Byte) :=
  fun bs =>
    match decodeExt bs with
    | some _ => none
    | none => decodeSfence bs

/-- Where the unified dispatcher accepts, the combined decode refuses:
    older rows keep their bytes. -/
theorem decodeSfenceExt_aelter (bs : List Byte) (e : ExtInstr)
    (rest : List Byte) (h : decodeExt bs = some (e, rest)) :
    decodeSfenceExt bs = none := by
  unfold decodeSfenceExt
  rw [h]

/-- Where every older decoder refuses, an SFENCE row is taken whole. -/
theorem decodeSfenceExt_sfence (bs : List Byte) (a : SfenceAnweisung)
    (rest : List Byte) (h1 : decodeExt bs = none)
    (h2 : decodeSfence bs = some (a, rest)) :
    decodeSfenceExt bs = some (a, rest) := by
  unfold decodeSfenceExt
  rw [h1, h2]

/-- Fetch and decode for the SFENCE rows: the actual fetched bytes at
    `rip` through the combined decoder, with consumed-length,
    3-byte-length and execute-permission checks. Anything else is an
    explicit `none`. -/
def sfenceFetch (m : LockMaschine) : Option (SfenceAnweisung × List Byte) :=
  match decodeSfenceExt (geholt m.zu) with
  | none => none
  | some (a, rest) =>
    if sfenceLaenge a + rest.length == (geholt m.zu).length &&
        sfenceLaenge a == 3 &&
        ausfuehrbarN m.zu.speicher m.zu.rip (sfenceLaenge a)
    then some (a, rest)
    else none

/-- Outcome kind: the decidable projection used by refusal witnesses. -/
inductive SfenceArt where
  | ok
  | udFehler
  | verweigert
  deriving DecidableEq, Repr

/-- Project one fetched outcome to its kind. -/
def sfenceArt : SfenceAusgang → SfenceArt
  | .ok _ _ => .ok
  | .udFehler _ => .udFehler
  | .verweigert => .verweigert

/-- Observe the RIP of a fetched outcome (`none` on non-success). -/
def sfenceRip : SfenceAusgang → Option Adresse
  | .ok m _ => some m.zu.rip
  | _ => none

/-- One fetched SFENCE step: fetch, decode, then `sfenceSchritt`.
    Takes the machine plus the named silicon SSE premise: no
    caller-supplied decoded value ever becomes a trusted fetch. -/
def sfenceByteschritt (m : LockMaschine) (c : Nat)
    (sse : Bool) : SfenceAusgang :=
  match sfenceFetch m with
  | none => .verweigert
  | some (a, _) => sfenceSchritt a c m sse

/-- FETCH-TO-STEP (success): the fetched step runs `sfenceSchritt`
    on the fetched instruction. -/
theorem sfenceByteschritt_weiter (m : LockMaschine) (c : Nat)
    (sse : Bool) (a : SfenceAnweisung)
    (rest : List Byte) (hf : sfenceFetch m = some (a, rest))
    (hs : sfenceSchritt a c m sse = o) :
    sfenceByteschritt m c sse = o := by
  unfold sfenceByteschritt
  simp only [hf, hs]

/-- FETCH-TO-STEP (fetch refusal): no fetch means the profile refusal,
    never a termination claim. -/
theorem sfenceByteschritt_verweigert_ohne_fetch (m : LockMaschine)
    (c : Nat) (sse : Bool) (hf : sfenceFetch m = none) :
    sfenceByteschritt m c sse = .verweigert := by
  unfold sfenceByteschritt
  simp only [hf]

/-- PROVED NARROWNESS (gate): with silicon SSE present but silicon SSE2
    absent, the SFENCE fence succeeds on an empty own buffer while the
    accepted MFENCE step raises the manual's #UD on the same machine --
    the exact gate clause that makes SFENCE narrower than MFENCE
    (SFENCE entry Exceptions: SSE[25]; MFENCE entry: SSE2[26]). -/
theorem sfence_schmaler_als_mfence_gate (m : LockMaschine) (c : Nat)
    (hw : HwProfil) (bp : BereitProfil)
    (hbuf : m.puffer c = [])
    (hfehlt : merkmalZugelassen hw bp .sseDoppel = false) :
    (∃ m' ev, sfenceSchritt (.ok .sfence 3) c m true = .ok m' ev) ∧
    lockSchrittVoll (.ok .mfence 3) c m hw bp =
      .udFehler .sse2Fehlt := by
  refine ⟨⟨_, _, sfence_erfolg m c true rfl hbuf sfence_len_ok⟩, ?_⟩
  exact lockSchrittVoll_mfence_ohne_sse2 m c 3 hw bp sfence_len_ok hfehlt

/-! ## 5. Witness infrastructure: reachability of drains, machines.

    Drains iterate the canonical flush, so every drained state is
    reached; the fetched pins run the complete fallback chain on closed
    bytes through the accepted witness helpers. -/

/-- Reachability composes: the TSO course is transitive. -/
theorem tsoErreichbar_trans {s0 s1 s2 : TSOZustand}
    (h1 : TSOErreichbar s0 s1) (h2 : TSOErreichbar s1 s2) :
    TSOErreichbar s0 s2 := by
  induction h2 with
  | start => exact h1
  | schritt _ step ih => exact .schritt ih step

/-- Every successful local drain is a reached run: each drain step is a
    canonical flush step. -/
theorem drainKernN_erreichbar (s s' : TSOZustand) (c n : Nat)
    (h : drainKernN s c n = some s') :
    TSOErreichbar s s' := by
  induction n generalizing s s' with
  | zero =>
    simp only [drainKernN] at h
    cases h
    exact .start
  | succ n ih =>
    simp only [drainKernN] at h
    cases hf : flushKern s c with
    | none =>
      rw [hf] at h
      cases h
    | some s1 =>
      rw [hf] at h
      simp only at h
      have h1 : TSOErreichbar s s1 :=
        .schritt .start (.flush s s1 c hf)
      exact tsoErreichbar_trans h1 (ih s1 s' h)

/-- Silicon without SSE2 refuses the SSE2 admission while keeping
    everything else baseline-admitted. -/
theorem hmfence_kein_sse2 :
    merkmalZugelassen hwOhneSse2 basisBereit .sseDoppel = false := by
  decide

/-- Witness machine over the drained TSO state: zeroed registers, the
    drained memory and buffers. -/
def sfZeugM : LockMaschine :=
  ⟨{ register := fun _ => BitVec.ofNat 64 0
     flags := witnessFlags
     rip := BitVec.ofNat 64 4096
     speicher := fdS3.mem },
   fdS3.puffer⟩

/-- Witness machine: SFENCE bytes at 4096, empty own buffer. -/
def sfZeug : LockMaschine :=
  lockZeug pinSfence 0 lockCodeExec lockDataRW lockDataRW 0 8192 0 []

/-- FETCHED SFENCE: from actual bytes with silicon SSE, the fence
    succeeds and RIP advances past the 3 bytes. -/
theorem sfZeug_ok :
    sfenceArt (sfenceByteschritt sfZeug 0 true) = .ok ∧
    sfenceRip (sfenceByteschritt sfZeug 0 true) =
      some (BitVec.ofNat 64 4099) := by
  decide

/-- Without silicon SSE the fetched fence is #UD, never executed. -/
theorem sfZeug_ohne_sse_ud :
    sfenceArt (sfenceByteschritt sfZeug 0 false) = .udFehler := by
  decide

/-- A pending own store refuses the fetched fence. -/
theorem sfZeug_puffer_verweigert :
    sfenceArt (sfenceByteschritt
      (lockZeug pinSfence 0 lockCodeExec lockDataRW lockDataRW 0 8192 0
        einEintrag) 0 true) = .verweigert := by
  decide

/-- The MFENCE witness on SSE-without-SSE2 silicon fetches as #UD: the
    concrete counterpart of the gate-narrowness bridge. -/
theorem sfZeug_mfence_ohne_sse2_ud :
    lockArt (lockByteschritt zeugZaun 0 hwOhneSse2 basisBereit) =
      .udFehler := by
  decide

/-! ## 6. Connection: store narrowness end to end. -/

/-- **Connection (store narrowness, end to end).** On any reached TSO
    run whose full local drain observably changes memory, the drained
    state admits the SFENCE fence: the drained state is reached, memory
    observably moved, the fence gate passes, the step is the fence-only
    identity on the TSO projection with loads, registers and flags
    untouched, stores are ordered and loads are not, the canonical
    bytes decode through the common dispatcher, and the MFENCE full
    fence on the same machine raises #UD without SSE2. -/
theorem SfenceStoreNarrow_verbindung (s2 s3 : TSOZustand) (c : Nat)
    (m : LockMaschine) (sse : Bool)
    (hreach : TSOErreichbar fdStart s2)
    (hdrain : drainVoll s2 c = some s3)
    (hmem : s2.mem.bytes fdX ≠ s3.mem.bytes fdX)
    (hto : toTSO m = s3)
    (hsse : sse = true) :
    TSOErreichbar fdStart (toTSO m) ∧
    s2.mem.bytes fdX ≠ (toTSO m).mem.bytes fdX ∧
    zaunBereit (toTSO m) c = true ∧
    (∃ m' ev, sfenceSchritt (.ok .sfence 3) c m sse = .ok m' ev ∧
      toTSO m' = toTSO m ∧
      (∀ a, loadByte (toTSO m') c a = loadByte (toTSO m) c a) ∧
      m'.zu.register = m.zu.register ∧ m'.zu.flags = m.zu.flags) ∧
    sfenceOrdnet .schreibe .schreibe = true ∧
    sfenceOrdnet .lese .lese = false ∧
    decodeSfence pinSfence = some (SfenceAnweisung.ok .sfence 3, []) ∧
    decodeExt pinSfence = none ∧
    lockSchrittVoll (.ok .mfence 3) c m hwOhneSse2 basisBereit =
      .udFehler .sse2Fehlt := by
  have hdrain' : drainKernN s2 c (s2.puffer c).length = some s3 := hdrain
  have hreach3 : TSOErreichbar fdStart s3 :=
    tsoErreichbar_trans hreach (drainKernN_erreichbar s2 s3 c _ hdrain')
  have hbuf : m.puffer c = [] := by
    have h3 := drain_voll_leer s2 s3 c hdrain
    show (toTSO m).puffer c = []
    rw [hto]
    exact h3
  have hbereit : zaunBereit (toTSO m) c = true := by
    rw [zaunBereit_iff_leer]
    exact hbuf
  have hsuc := sfence_erfolg m c sse hsse hbuf sfence_len_ok
  have hmfence := lockSchrittVoll_mfence_ohne_sse2 m c 3 hwOhneSse2
    basisBereit sfence_len_ok hmfence_kein_sse2
  refine ⟨?_, ?_, hbereit, ?_, sfence_ordnet_schreibe,
    sfence_ordnet_last_nicht.1, ?_, pin_sfence_ext_verweigert, hmfence⟩
  · rw [hto]
    exact hreach3
  · rw [hto]
    exact hmem
  · refine ⟨_, _, hsuc, ?_, ?_, ?_⟩
    · simp [toTSO]
    · intro a
      simp [toTSO]
    · exact ⟨rfl, rfl⟩
  · simpa using roundtrip_sfence []

/-- Joint witness for `SfenceStoreNarrow_verbindung`: all premises
    together on a non-degenerate reached run -- two issues on two
    cores, a memory-changing local drain, the fence machine over the
    drained state with silicon SSE present. -/
theorem SfenceStoreNarrow_verbindung_zeuge :
    ∃ (s2 s3 : TSOZustand) (c : Nat) (m : LockMaschine) (sse : Bool),
      TSOErreichbar fdStart s2 ∧
      drainVoll s2 c = some s3 ∧
      s2.mem.bytes fdX ≠ s3.mem.bytes fdX ∧
      toTSO m = s3 ∧
      sse = true ∧
      s2.puffer 1 ≠ [] := by
  refine ⟨fdS2, fdS3, 0, sfZeugM, true, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact .schritt (.schritt .start (.issue _ _ _ _ _ fd_schritt1))
      (.issue _ _ _ _ _ fd_schritt2)
  · exact fd_voll_schritt
  · exact fd_speicher_aendert
  · rfl
  · rfl
  · exact fd_fremd_wartend.1

/- CUTS:
    - The canonical TSO model has no weakly-ordered (WC/NT
      non-temporal) store path, so SFENCE's store-ordering over such
      memory is NOT modeled here: the store half is discharged through
      the canonical drain only. WC/NT forms stay refused/OPEN.
    - Loads and LFENCE are explicitly NOT ordered (proved
      `sfence_ordnet_last_nicht`, executed `sfence_last_unveraendert`);
      serializing instructions (CPUID) and `MFENCE`-as-ordered-after
      are not modeled as steps here.
    - The SSE premise (`sse : Bool`, CPUID.01H:EDX.SSE[25]) is named
      silicon behaviour and is assumed, never probed; readiness beyond
      it is not claimed.
    - The r/m-ignored range F8..FF is proved; every other 0F AE row
      (MFENCE F0..F7, LFENCE E8..EF, CLFLUSH memory shapes) refuses
      here and belongs to its own decoder.
    - The MFENCE side of the narrowness bridge
      (`lockSchrittVoll_mfence_ohne_sse2`, `lockVoll_mfence_adapter`,
      `zeugZaun`, `hwOhneSse2`, witness helpers) is reused from the
      accepted locked-execution module, not re-proved.
    - No source-to-target simulation: no `W`/`GX` run induction, no
      lowering map, no per-access linearisation of G steps.
    - No interrupt, device, MMIO, DMA, timing, fairness, progress or
      cycle-cost claim; a local fence discharging a foreign or device
      read is refused (`sfence_puffer_verweigert` gates the own buffer
      only, `mfence_loest_fremd_nicht` is reused by reference).
-/

#print axioms roundtrip_sfence
#print axioms decodeSfence_ignoriert_rm
#print axioms pin_sfence_lock_ud
#print axioms pin_sfence_verweigert_nachbarn
#print axioms pin_sfence_ext_verweigert
#print axioms sfence_ordnet_schreibe
#print axioms sfence_ordnet_last_nicht
#print axioms sfence_len_ok
#print axioms sfence_erfolg
#print axioms sfence_ohne_sse
#print axioms sfence_puffer_verweigert
#print axioms sfence_ud
#print axioms sfence_erfolg_form
#print axioms sfence_behaelt_tso
#print axioms sfence_behaelt_register_flags
#print axioms sfence_last_unveraendert
#print axioms sfence_mfence_gleiches_tor
#print axioms decodeSfenceExt_aelter
#print axioms decodeSfenceExt_sfence
#print axioms sfenceByteschritt_weiter
#print axioms sfenceByteschritt_verweigert_ohne_fetch
#print axioms sfence_schmaler_als_mfence_gate
#print axioms tsoErreichbar_trans
#print axioms drainKernN_erreichbar
#print axioms hmfence_kein_sse2
#print axioms sfZeug_ok
#print axioms sfZeug_ohne_sse_ud
#print axioms sfZeug_puffer_verweigert
#print axioms sfZeug_mfence_ohne_sse2_ud
#print axioms SfenceStoreNarrow_verbindung
#print axioms SfenceStoreNarrow_verbindung_zeuge

end Gabbro.Grammatik.X86
