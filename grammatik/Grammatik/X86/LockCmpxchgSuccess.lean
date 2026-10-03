/-
  File:      Grammatik/X86/LockCmpxchgSuccess.lean
  Subject:   LOCK CMPXCHG success as the single RMW access: full barrier
             plus one atomicity unit, through fetched bytes.

  Lane 776: builds only on accepted vocabulary (`lockSchrittVoll` success
  equation, `casSchritt` adapter, `RmwForm`, `mfence_ordnung` barrier
  shape, the `lockByteschritt` fetched dispatcher). No new evaluator,
  no source/checker/goal change.
  Manual provenance (local snapshot `.tmp/HARDWARE-REFERENCES/`,
  Intel SDM 325462-093US Sep 2026): LOCK prefix Vol. 2A 3-565/3-566,
  CMPXCHG Vol. 2A 3-193/3-194.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.TSO
import Grammatik.X86.LockedOps
import Grammatik.X86.LockedInstructionExecution
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.FeatureProfile
import Grammatik.X86.Byteschritt

namespace Gabbro.Grammatik.X86

/-- The single-RMW shape of a CMPXCHG success event: one indivisible
    read-modify-write over the full word footprint, carrying the
    observed old word and the installed new word. -/
def CmpxchgErfolgForm (ev : LockEreignis) (tgt : Adresse)
    (dest sval : Wort) : Prop :=
  ev.istRmw = true ∧ ev.istZaun = false ∧
    ev.lesen = Fuss tgt ∧ ev.schreiben = Fuss tgt ∧
    ev.gelesen = some dest ∧ ev.geschrieben = some sval

/-! ## 1. Common-architecture routing: no shadowing. -/

/-- A fetched instruction runs through the common dispatcher: where
    `lockFetch` admits, the shared `decodeExt` refused, so no older row
    is shadowed and the lock row is taken whole. -/
theorem cmpxchg_erfolg_ohne_schatten (m : LockMaschine)
    (a : LockAnweisung) (rest : List Byte)
    (hf : lockFetch m = some (a, rest)) :
    decodeExt (geholt m.zu) = none := by
  unfold lockFetch at hf
  cases hde : decodeLockExt (geholt m.zu) with
  | none =>
    simp [hde] at hf
  | some _ =>
    unfold decodeLockExt at hde
    cases hdx : decodeExt (geholt m.zu) with
    | some _ =>
      simp [hdx] at hde
    | none =>
      rfl

/-! ## 2. No split pair reproduces the success observation. -/

/-- The success RMW observation is never a split pair: two non-RMW
    events carry no RMW shape while the success event does, so no
    load-then-store pair observes what the single locked access does. -/
theorem cmpxchg_erfolg_kein_split (ev e1 e2 : LockEreignis)
    (hrmw : ev.istRmw = true)
    (h1 : e1.istRmw = false) (h2 : e2.istRmw = false) :
    RmwForm [e1, e2] = false ∧ RmwForm [e1, e2] ≠ RmwForm [ev] := by
  have hsplit := rmw_nur_mit_lock e1 e2 h1 h2
  have hev : RmwForm [ev] = true := by simp [RmwForm, hrmw]
  exact ⟨hsplit, by simp [hsplit, hev]⟩

/-! ## 3. The connection: success IS the single RMW access. -/

/-- LOCK CMPXCHG success IS the single RMW access: from fetched bytes,
    under the success guards, the outcome is one RMW event over the full
    word footprint (the observed word replaced by the source word), with
    a full local barrier (no pending store before or after on the acting
    core, so later loads observe canonical memory), preserved
    permissions, an untouched frame outside the footprint, exact
    read-back, an untouched RAX, the comparison flags and an advanced
    RIP -- and it projects onto exactly one accepted CAS step, the
    single atomicity unit the W `rmw` field consumes
    (`neu = wahl.ts + 1` at an exchange head; the lowering itself stays
    with the bridge). -/
theorem LockCmpxchgSuccess_verbindung (m : LockMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (hw : HwProfil) (bp : BereitProfil)
    (dest sval : Wort) (mem' : Speicher) (rest : List Byte)
    (hf : lockFetch m = some ((.ok (.cmpxchg64 src base d) len), rest))
    (hbuf : m.puffer c = [])
    (hali : ausgerichtet8 (effAddr m.zu base d) = true)
    (hrd : read64 m.zu.speicher (effAddr m.zu base d) = some dest)
    (hgleich : (dest == m.zu.register .rax) = true)
    (hsrc : m.zu.register src = sval)
    (hok : laengeOk len = true)
    (hwr : write64 m.zu.speicher (effAddr m.zu base d) sval = some mem')
    (hles : lesbar8 m.zu.speicher (effAddr m.zu base d) = true) :
    ∃ (m' : LockMaschine) (ev : LockEreignis),
      lockByteschritt m c hw bp = LockAusgang.ok m' ev ∧
      m'.puffer = m.puffer ∧ m'.puffer c = [] ∧
      (∀ a, neuestens (m'.puffer c) a = none) ∧
      CmpxchgErfolgForm ev (effAddr m.zu base d) dest sval ∧
      RmwForm [ev] = true ∧
      m'.zu.speicher.lesbar = m.zu.speicher.lesbar ∧
      m'.zu.speicher.schreibbar = m.zu.speicher.schreibbar ∧
      m'.zu.speicher.ausfuehrbar = m.zu.speicher.ausfuehrbar ∧
      (∀ x, (∀ k : Nat, k < 8 → x ≠ addrOff (effAddr m.zu base d) k) →
        m'.zu.speicher.bytes x = m.zu.speicher.bytes x) ∧
      read64 m'.zu.speicher (effAddr m.zu base d) = some sval ∧
      m'.zu.register .rax = m.zu.register .rax ∧
      m'.zu.flags = (sub64 dest (m.zu.register .rax)).2 ∧
      m'.zu.rip = ripNach m.zu.rip len ∧
      casSchritt (effAddr m.zu base d) (m.zu.register .rax)
        (m.zu.register src) c (toTSO m) =
        some (⟨mem', m.puffer⟩, true) := by
  have hvoll := lockSchrittVoll_cmpxchg_erfolg m c src base d len hw bp
    dest sval mem' hbuf hali hrd hgleich hsrc hok hwr
  have hb : lockByteschritt m c hw bp =
      LockAusgang.ok
        ⟨{ { { m.zu with rip := ripNach m.zu.rip len } with
          speicher := mem' } with
          flags := (sub64 dest (m.zu.register .rax)).2 }, m.puffer⟩
        ⟨c, Fuss (effAddr m.zu base d), Fuss (effAddr m.zu base d),
          some dest, some sval, true, false⟩ :=
    lockByteschritt_weiter m c hw bp _ rest hf hvoll
  have hperm := write64_erhaelt_berechtigungen m.zu.speicher
    (effAddr m.zu base d) sval mem' hwr
  have hles' := read64_nach_write64 m.zu.speicher mem'
    (effAddr m.zu base d) sval hwr hles
  have hwr2 : write64 m.zu.speicher (effAddr m.zu base d)
      (m.zu.register src) = some mem' := by
    rw [hsrc]
    exact hwr
  have hadapter := lockVoll_cmpxchg_erfolg_adapter m c src base d dest
    mem' hbuf hrd hali hgleich hwr2
  refine ⟨_, _, hb, rfl, hbuf, ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hadapter⟩
  · intro a
    have h2 : (⟨{ { { m.zu with rip := ripNach m.zu.rip len } with
        speicher := mem' } with
        flags := (sub64 dest (m.zu.register .rax)).2 },
        m.puffer⟩ : LockMaschine).puffer c = [] := hbuf
    rw [h2]
    rfl
  · exact hperm.1
  · exact hperm.2.1
  · exact hperm.2.2
  · intro x haussen
    exact write64_rahmen m.zu.speicher mem' _ x sval hwr haussen
  · exact hles'
  · rfl
  · rfl
  · rfl

/-! ## 4. Joint witness: fetched success, memory-changing. -/

/-- The fetched instruction on the success witness machine: LOCK CMPXCHG
    with length 9, over six trailing zero bytes of the 15-byte window. -/
theorem lockFetch_zeugCmpxchgOk :
    lockFetch zeugCmpxchgOk =
      some ((.ok (.cmpxchg64 .rcx .rbp 0) 9),
        List.replicate 6 (natByte 0)) := by
  decide

/-- The witness effective address: base `rbp` plus zero displacement. -/
theorem effAddr_zeugCmpxchgOk :
    effAddr zeugCmpxchgOk.zu .rbp 0 = BitVec.ofNat 64 8192 := by
  decide

/-- **Joint witness for `LockCmpxchgSuccess_verbindung`.** All premises
    hold together on the reached fetched machine `zeugCmpxchgOk` (word
    10 at 8192, `rax` 10, new value 7 in `rcx`, empty own buffer): the
    fetched step succeeds as one RMW event and observably moves the word
    from 10 to 7. Non-degenerate: real bytes, a written word, a
    memory-changing reached run. -/
theorem LockCmpxchgSuccess_verbindung_zeuge :
    ∃ (rest : List Byte) (mem' : Speicher),
      lockFetch zeugCmpxchgOk =
        some ((.ok (.cmpxchg64 .rcx .rbp 0) 9), rest) ∧
      zeugCmpxchgOk.puffer 0 = [] ∧
      ausgerichtet8 (effAddr zeugCmpxchgOk.zu .rbp 0) = true ∧
      read64 zeugCmpxchgOk.zu.speicher
        (effAddr zeugCmpxchgOk.zu .rbp 0) = some 10 ∧
      ((10 : Wort) == zeugCmpxchgOk.zu.register .rax) = true ∧
      zeugCmpxchgOk.zu.register .rcx = 7 ∧
      laengeOk 9 = true ∧
      write64 zeugCmpxchgOk.zu.speicher
        (effAddr zeugCmpxchgOk.zu .rbp 0) 7 = some mem' ∧
      lesbar8 zeugCmpxchgOk.zu.speicher
        (effAddr zeugCmpxchgOk.zu .rbp 0) = true ∧
      ∃ (m' : LockMaschine) (ev : LockEreignis),
        lockByteschritt zeugCmpxchgOk 0 basisHw basisBereit =
          LockAusgang.ok m' ev ∧
        read64 zeugCmpxchgOk.zu.speicher (BitVec.ofNat 64 8192) =
          some 10 ∧
        read64 m'.zu.speicher (BitVec.ofNat 64 8192) = some 7 ∧
        ev.istRmw = true := by
  have hwr0 : ∃ mem',
      write64 zeugCmpxchgOk.zu.speicher
        (effAddr zeugCmpxchgOk.zu .rbp 0) 7 = some mem' := ⟨_, rfl⟩
  obtain ⟨mem0, hwr0⟩ := hwr0
  have hf := lockFetch_zeugCmpxchgOk
  have hbuf : zeugCmpxchgOk.puffer 0 = [] := by decide
  have hali : ausgerichtet8 (effAddr zeugCmpxchgOk.zu .rbp 0) = true := by
    decide
  have hrd : read64 zeugCmpxchgOk.zu.speicher
      (effAddr zeugCmpxchgOk.zu .rbp 0) = some 10 := by
    decide
  have hgleich : ((10 : Wort) == zeugCmpxchgOk.zu.register .rax) = true := by
    decide
  have hsrc : zeugCmpxchgOk.zu.register .rcx = 7 := by decide
  have hok : laengeOk 9 = true := by decide
  have hles : lesbar8 zeugCmpxchgOk.zu.speicher
      (effAddr zeugCmpxchgOk.zu .rbp 0) = true := by
    decide
  have hmain := LockCmpxchgSuccess_verbindung zeugCmpxchgOk 0 .rcx .rbp 0 9
    basisHw basisBereit 10 7 mem0 _ hf hbuf hali hrd hgleich hsrc hok
    hwr0 hles
  obtain ⟨m', ev, hout, _, _, _, hform, _, _, _, _, _, hpost, _, _, _,
    _⟩ := hmain
  have hpre : read64 zeugCmpxchgOk.zu.speicher (BitVec.ofNat 64 8192) =
      some 10 := by
    rw [← effAddr_zeugCmpxchgOk]
    exact hrd
  have hpost7 : read64 m'.zu.speicher (BitVec.ofNat 64 8192) = some 7 := by
    rw [← effAddr_zeugCmpxchgOk]
    exact hpost
  exact ⟨_, _, hf, hbuf, hali, hrd, hgleich, hsrc, hok, hwr0, hles,
    m', ev, hout, hpre, hpost7, hform.1⟩

/-! ## 5. Refusals: unsupported neighbours of the success row. -/

/-- BUFFER REFUSAL: a pending own store refuses the CMPXCHG step. -/
theorem cmpxchg_erfolg_puffer_verweigert :
    lockArt (lockByteschritt
      (lockZeug pinCmpxchg 10 lockCodeExec lockDataRW lockDataRW 11 8192 7
        einEintrag)
      0 basisHw basisBereit) = .verweigert := by
  decide

/-- MISALIGNED REFUSAL: base 8193 is refused as an unsupported profile,
    never as a hardware fault. -/
theorem cmpxchg_erfolg_unaligned_verweigert :
    lockArt (lockByteschritt
      (lockZeug pinCmpxchg 10 lockCodeExec lockDataRW lockDataRW 11 8193 7
        [])
      0 basisHw basisBereit) = .verweigert := by
  decide

/-- TRUNCATED-PREFIX REFUSAL: the opcode tail cut by the execute
    boundary has no transition. -/
theorem cmpxchg_erfolg_stumpf_verweigert :
    lockArt (lockByteschritt
      (lockZeug [natByte 240, natByte 72, natByte 15] 0 lockCodeExecKurz
        lockDataRW lockDataRW 11 8192 7 [])
      0 basisHw basisBereit) = .verweigert := by
  decide

#print axioms CmpxchgErfolgForm
#print axioms cmpxchg_erfolg_ohne_schatten
#print axioms cmpxchg_erfolg_kein_split
#print axioms LockCmpxchgSuccess_verbindung
#print axioms lockFetch_zeugCmpxchgOk
#print axioms effAddr_zeugCmpxchgOk
#print axioms LockCmpxchgSuccess_verbindung_zeuge
#print axioms cmpxchg_erfolg_puffer_verweigert
#print axioms cmpxchg_erfolg_unaligned_verweigert
#print axioms cmpxchg_erfolg_stumpf_verweigert

/- CUTS:
    Proved here: the LOCK CMPXCHG success case as the single RMW
    access (`LockCmpxchgSuccess_verbindung`, with joint non-degenerate
    witness `LockCmpxchgSuccess_verbindung_zeuge`): from fetched bytes,
    the success outcome is one RMW event over the full word footprint
    with the observed word replaced by the source word; a full local
    barrier (empty own buffer before and after, no forwarding
    afterwards, direct canonical-memory operation); preserved
    permissions, frame outside the footprint, exact read-back,
    untouched RAX, comparison flags, advanced RIP; projection onto
    exactly one accepted `casSchritt` success step (the single
    atomicity unit whose shape the W `rmw` field consumes). The
    success observation is never a split pair
    (`cmpxchg_erfolg_kein_split`); admitted bytes route through the
    common dispatcher (`cmpxchg_erfolg_ohne_schatten`); buffer,
    misalignment and truncation neighbours refuse explicitly.
    Manual provenance: Intel SDM 325462-093US Sep 2026, LOCK Vol. 2A
    3-565/3-566, CMPXCHG Vol. 2A 3-193/3-194 (local snapshot,
    verified 2026-10-02).
    NOT proved here, and not claimed:
    - No W/GX refinement: the projection stops at the accepted
      `casSchritt` success; the exchange/CAS lowering into `SchrittW`
      and the `rmw`-field (`neu = wahl.ts + 1`) correspondence stay
      with the bridge (OPEN wave-B work, cf. TSO.lean CUTS).
    - Failure path untouched: only the success case (`dest == rax`)
      is connected here; failure write-back lives in
      `lockVoll_cmpxchg_fehlschlag_adapter`.
    - Widths: only the 64-bit word row (REX.W + 0F B1); 8/16/32-bit
      rows and CMPXCHG8B/16B stay open.
    - Addressing: only mod=2 base-plus-disp32 as admitted by the
      accepted decoder; other modes stay refused there, not modelled
      here.
    - Alignment is the accepted selected-profile contract
      (`ausgerichtet8`); silicon behaviour on misaligned locked words
      is not claimed.
    - No cycle, latency, progress, fairness or retry-bound claim; no
      fence pacing beyond the empty-buffer gate.
    - No source, checker, contract, budget, duty or goal change:
      nothing here speaks about `Vertrag`, `Stmt`, duties or
      `gabbro_ziel`.
-/

end Gabbro.Grammatik.X86
