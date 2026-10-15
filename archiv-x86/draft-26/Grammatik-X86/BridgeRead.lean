/-
  File:      Grammatik/X86/BridgeRead.lean
  Subject:   Projected TSO group loads to source W reads (lane 574).

  Consumes ACCEPTED TSOHistory567 (`histVon`/`sichtVon`, youngest
  forwarding, freshness/FIFO facts) and SourceMemory570 (`RepSlot`,
  `zahlWort`/`wortZahl`, `read64`), plus real `Sicht` read/view rules
  (`Lesbar`, `Frisch`) and real W vocabulary (`RufMaschineW`,
  `NachrichtW`, `TraegerGleich`, `LiestG`, `HavocA`).

  Produces: an 8-byte group load (`ladeWort8`) over real `loadByte`,
  its committed case (no tearing-free group value without forwarding),
  its forwarded assembly, the represented value link (`wortZahl`
  roundtrip to the exact source slot value), and two W-read simulations
  deriving the `SchrittW.lies` consequent
  (`Lesbar W.hist (W.sicht u) c (wahl c)` with `TraegerGleich`) from
  projection facts plus explicit history/view-link premises -- never by
  assuming `Lesbar` for the desired read. `schwach_ist_gX` is NOT
  applied here (no full `SchrittW` is derived); it is the recorded next
  integration once a real G step reads the carrier.
-/
import Grammatik.X86.TSO
import Grammatik.X86.TSOHistory
import Grammatik.X86.SourceMemory
import Grammatik.Speichermodell.Sicht
import Grammatik.Speichermodell.MaschineW
import Grammatik.Speichermodell.AtomarSem

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The eight group bytes as a `Fin 8` function (plain match, no
    Mathlib notation). Each projection computes by `rfl`. -/
def achtBytes (b0 b1 b2 b3 b4 b5 b6 b7 : Byte) (i : Fin 8) : Byte :=
  match i.val with
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | 3 => b3
  | 4 => b4
  | 5 => b5
  | 6 => b6
  | _ => b7

/-- An 8-byte group load on core `c` at `a`: eight real `loadByte`s
    assembled little-endian. `none` if any byte is unreadable. One
    group stands for one represented source slot (`RepSlot`); a group
    is NOT atomic (tearing is a proved refusal, not a silent case). -/
def ladeWort8 (s : TSOZustand) (c : Nat) (a : Adresse) : Option Wort :=
  match loadByte s c (addrOff a 0), loadByte s c (addrOff a 1),
    loadByte s c (addrOff a 2), loadByte s c (addrOff a 3),
    loadByte s c (addrOff a 4), loadByte s c (addrOff a 5),
    loadByte s c (addrOff a 6), loadByte s c (addrOff a 7) with
  | some b0, some b1, some b2, some b3,
    some b4, some b5, some b6, some b7 =>
    some (bytesWort (achtBytes b0 b1 b2 b3 b4 b5 b6 b7))
  | _, _, _, _, _, _, _, _ => none

/-! ## 1. Committed group loads: no forwarding, canonical word -/

/-- One byte of the `lesbar8` permission: every footprint byte is
    readable. Core tactics only: eight positions read off the flattened
    left-nested conjunction, with the impossible tail by `omega`. -/
theorem lesbar8_hit (m : Speicher) (a : Adresse) (i : Nat)
    (h : lesbar8 m a = true) (hi : i < 8) :
    m.lesbar (addrOff a i) = true := by
  unfold lesbar8 at h
  simp only [Bool.and_eq_true] at h
  match i with
  | 0 => exact h.1.1.1.1.1.1.1
  | 1 => exact h.1.1.1.1.1.1.2
  | 2 => exact h.1.1.1.1.1.2
  | 3 => exact h.1.1.1.1.2
  | 4 => exact h.1.1.1.2
  | 5 => exact h.1.1.2
  | 6 => exact h.1.2
  | 7 => exact h.2
  | n + 8 => exact absurd hi (by omega)

/-- COMMITTED GROUP: with no pending own-buffer entry on any of the
    eight footprint bytes and full read permission, the group load is
    exactly the canonical `read64` word. Every premise is used: `hMiss`
    through `load_ohne_eintrag` per byte, `hRd` through `lesbar8_hit`
    and the `read64` permission check. -/
theorem ladeWort8_ohne_weiterleitung (s : TSOZustand) (c : Nat)
    (a : Adresse)
    (hMiss : ∀ i : Nat, i < 8 → neuestens (s.puffer c) (addrOff a i) = none)
    (hRd : lesbar8 s.mem a = true) :
    ladeWort8 s c a = read64 s.mem a := by
  have hL0 := load_ohne_eintrag s c (addrOff a 0) (hMiss 0 (by decide))
    (lesbar8_hit s.mem a 0 hRd (by decide))
  have hL1 := load_ohne_eintrag s c (addrOff a 1) (hMiss 1 (by decide))
    (lesbar8_hit s.mem a 1 hRd (by decide))
  have hL2 := load_ohne_eintrag s c (addrOff a 2) (hMiss 2 (by decide))
    (lesbar8_hit s.mem a 2 hRd (by decide))
  have hL3 := load_ohne_eintrag s c (addrOff a 3) (hMiss 3 (by decide))
    (lesbar8_hit s.mem a 3 hRd (by decide))
  have hL4 := load_ohne_eintrag s c (addrOff a 4) (hMiss 4 (by decide))
    (lesbar8_hit s.mem a 4 hRd (by decide))
  have hL5 := load_ohne_eintrag s c (addrOff a 5) (hMiss 5 (by decide))
    (lesbar8_hit s.mem a 5 hRd (by decide))
  have hL6 := load_ohne_eintrag s c (addrOff a 6) (hMiss 6 (by decide))
    (lesbar8_hit s.mem a 6 hRd (by decide))
  have hL7 := load_ohne_eintrag s c (addrOff a 7) (hMiss 7 (by decide))
    (lesbar8_hit s.mem a 7 hRd (by decide))
  unfold ladeWort8 read64
  simp only [hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7, if_pos hRd]
  congr 1

/-! ## 2. Forwarded group assembly: youngest bytes per position -/

/-- FORWARDED ASSEMBLY: when every footprint byte loads (whatever each
    one's source -- own-buffer forward or canonical), the group load is
    the assembly of the eight loaded bytes. This is the shape the
    youngest-forwarding facts (`weiterleitung_ist_jüngste` per byte)
    feed; the VALUE link for forwarded bytes is separate (§4). -/
theorem ladeWort8_aus_lesungen (s : TSOZustand) (c : Nat) (a : Adresse)
    (f : Fin 8 → Byte)
    (h : ∀ i : Fin 8, loadByte s c (addrOff a i.val) = some (f i)) :
    ladeWort8 s c a = some (bytesWort f) := by
  have hL0 := h ⟨0, by decide⟩
  have hL1 := h ⟨1, by decide⟩
  have hL2 := h ⟨2, by decide⟩
  have hL3 := h ⟨3, by decide⟩
  have hL4 := h ⟨4, by decide⟩
  have hL5 := h ⟨5, by decide⟩
  have hL6 := h ⟨6, by decide⟩
  have hL7 := h ⟨7, by decide⟩
  unfold ladeWort8
  simp only [hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7]
  congr 1

/-- One forwarded byte is the youngest own-buffer value at its address,
    with the buffer split exhibiting it: thin per-position application
    of the accepted `weiterleitung_ist_jüngste`, kept so group proofs
    name the youngest split instead of re-deriving it. -/
theorem ladeByte_ist_jüngste (s : TSOZustand) (c : Nat) (x : Adresse)
    (v w : Byte)
    (hload : loadByte s c x = some v)
    (hpend : neuestens (s.puffer c) x = some w) :
    v = w ∧ ∃ pre post : List TSOEintrag,
      s.puffer c = pre ++ [⟨x, w⟩] ++ post ∧
        ∀ e' ∈ post, e'.addr ≠ x :=
  weiterleitung_ist_jüngste s c x v w hload hpend

/-! ## 3. Value link: the group parses to the source slot value -/

/-- REPRESENTED VALUE: a committed group load at a represented slot
    parses back to exactly the source slot value. The target side comes
    from §1 (`ladeWort8_ohne_weiterleitung`), the source side from the
    accepted representation (`RepSlot` + `zahlWort_wortZahl`); `hLo`/`hHi`
    are the roundtrip bounds, `hWort` names the loaded word. -/
theorem gruppenwert_rep {D : Deklaration} {t : D.Tab} {k : Int}
    {f : D.Feld t} {lo hi : Int} {hT : D.typ t f = .int lo hi}
    {a : Adresse} {s : TSOZustand} {c : Nat}
    {σw : World D}
    (v : Zahl lo hi)
    (hRep : RepSlot t k f lo hi hT a s.mem σw)
    (hMiss : ∀ i : Nat, i < 8 → neuestens (s.puffer c) (addrOff a i) = none)
    (hRd : lesbar8 s.mem a = true)
    (hLo : 0 ≤ lo) (hHi : hi < 2 ^ 64)
    (w : Wort) (hWort : ladeWort8 s c a = some w)
    (hv : (cast (congrArg (Wert D) hT) (σw.slots t k f)) = v) :
    wortZahl lo hi w = some v := by
  have hGrp := ladeWort8_ohne_weiterleitung s c a hMiss hRd
  unfold RepSlot at hRep
  rw [hWort] at hGrp
  rw [hRep] at hGrp
  simp only [Option.some.injEq] at hGrp
  rw [hGrp, hv]
  exact zahlWort_wortZahl v hLo hHi

/-! ## 4. W-read simulation: the committed case -/

/-- **COMMITTED W-READ SIMULATION.** A committed group load at a
    represented slot simulates a source W read: the loaded word parses
    to exactly the source slot value, and -- for a real G step that
    records a read of the carrier -- the `SchrittW.lies` consequent
    (`Lesbar` at the actual message plus `TraegerGleich`) is DERIVED,
    never assumed. The projection carries the view: `hProj` covers the
    source view by the target core's projected view, `hTs` puts the
    message timestamp above it. The message membership (`hMem`) and the
    presented-memory agreement (`hTraeger`) are facts about the source
    run; the VALUE identity across sides comes from the accepted
    representation (`RepSlot`, §3). `schwach_ist_gX` is not applied:
    no full `SchrittW` is derived here. -/
theorem wLesbar_aus_gruppe {D : Deklaration} {t : D.Tab} {k : Int}
    {f : D.Feld t} {lo hi : Int} {hT : D.typ t f = .int lo hi}
    {a : Adresse} {s : TSOZustand} {c0 : Nat}
    {σw : World D} {σ : Gabbro.Grammatik.Speicher D}
    {W : RufMaschineW D} {u : Faden} {M'' : RufMaschineG D} {ts : Nat}
    (v : Zahl lo hi)
    (hRep : RepSlot t k f lo hi hT a s.mem σw)
    (hMiss : ∀ i : Nat, i < 8 → neuestens (s.puffer c0) (addrOff a i) = none)
    (hRd : lesbar8 s.mem a = true)
    (hLo : 0 ≤ lo) (hHi : hi < 2 ^ 64)
    (w : Wort) (hWort : ladeWort8 s c0 a = some w)
    (hv : (cast (congrArg (Wert D) hT) (σw.slots t k f)) = v)
    (hMem : (⟨ts, σw.speicher, Speichermodell.Sicht.null⟩ : NachrichtW D) ∈
      W.hist (.inl t))
    (hProj : W.sicht u (.inl t) ≤ sichtVon s c0 a)
    (hTs : sichtVon s c0 a ≤ ts)
    (hTraeger : TraegerGleich σ σw.speicher (.inl t)) :
    wortZahl lo hi w = some v ∧
      (LiestG (mitSpeicher W.g σ) M'' u (.inl t) →
        Speichermodell.Lesbar W.hist (W.sicht u) (.inl t)
          (⟨ts, σw.speicher, Speichermodell.Sicht.null⟩ : NachrichtW D) ∧
        TraegerGleich σ
          (⟨ts, σw.speicher, Speichermodell.Sicht.null⟩ : NachrichtW D).wert
          (.inl t)) := by
  refine ⟨gruppenwert_rep v hRep hMiss hRd hLo hHi w hWort hv, fun _ => ⟨⟨hMem, ?_⟩, hTraeger⟩⟩
  exact Nat.le_trans hProj hTs

/-! ## 5. W-read simulation: the forwarded case -/

/-- **FORWARDED W-READ SIMULATION.** When every footprint byte loads
    while pending own-buffer entries exist, the group assembles from
    the loaded bytes, each byte is exhibited as the youngest buffer
    entry (no silent forward), and -- for a real recording G step --
    the `SchrittW.lies` consequent is derived as in §4. The VALUE
    identity across sides (`hWert`: the assembled word parses to the
    source slot value) is an explicit premise: it is the lowering
    certificate's job (write side, lane 573), never derived from the
    buffer here. A mixed committed/forwarded footprint has no value
    simulation (tearing refusal, §7). -/
theorem wLesbar_aus_weiterleitung {D : Deklaration} {t : D.Tab} {k : Int}
    {f : D.Feld t} {lo hi : Int} {hT : D.typ t f = .int lo hi}
    {a : Adresse} {s : TSOZustand} {c0 : Nat}
    {σw : World D} {σ : Gabbro.Grammatik.Speicher D}
    {W : RufMaschineW D} {u : Faden} {M'' : RufMaschineG D} {ts : Nat}
    (v : Zahl lo hi)
    (f8 : Fin 8 → Byte)
    (hL : ∀ i : Fin 8, loadByte s c0 (addrOff a i.val) = some (f8 i))
    (hPend : ∀ i : Fin 8, ∃ w : Byte,
      neuestens (s.puffer c0) (addrOff a i.val) = some w)
    (hWert : wortZahl lo hi (bytesWort f8) =
      some (cast (congrArg (Wert D) hT) (σw.speicher.slots t k f)))
    (hv : (cast (congrArg (Wert D) hT) (σw.speicher.slots t k f)) = v)
    (hMem : (⟨ts, σw.speicher, Speichermodell.Sicht.null⟩ : NachrichtW D) ∈
      W.hist (.inl t))
    (hProj : W.sicht u (.inl t) ≤ sichtVon s c0 a)
    (hTs : sichtVon s c0 a ≤ ts)
    (hTraeger : TraegerGleich σ σw.speicher (.inl t)) :
    ladeWort8 s c0 a = some (bytesWort f8) ∧
      (∀ i : Fin 8, ∃ w : Byte, f8 i = w ∧ ∃ pre post : List TSOEintrag,
        s.puffer c0 = pre ++ [⟨addrOff a i.val, w⟩] ++ post ∧
          ∀ e' ∈ post, e'.addr ≠ addrOff a i.val) ∧
      wortZahl lo hi (bytesWort f8) = some v ∧
      (LiestG (mitSpeicher W.g σ) M'' u (.inl t) →
        Speichermodell.Lesbar W.hist (W.sicht u) (.inl t)
          (⟨ts, σw.speicher, Speichermodell.Sicht.null⟩ : NachrichtW D) ∧
        TraegerGleich σ
          (⟨ts, σw.speicher, Speichermodell.Sicht.null⟩ : NachrichtW D).wert
          (.inl t)) := by
  refine ⟨ladeWort8_aus_lesungen s c0 a f8 hL, ?_, ?_, fun _ => ⟨⟨hMem, ?_⟩, hTraeger⟩⟩
  · intro i
    obtain ⟨w, hw⟩ := hPend i
    exact ⟨w, ladeByte_ist_jüngste s c0 _ (f8 i) w (hL i) hw⟩
  · exact hWert.trans (congrArg Option.some hv)
  · exact Nat.le_trans hProj hTs

/-! ## 6. Atomic-rely leg: the read value survives any atomic havoc -/

/-- **RELY STABILITY.** A group-read value at a carrier outside the
    shared-atomic set `T` survives every atomic environment of the
    rely (`HavocA`, the exact class `NutzerPflichtA` quantifies over):
    havoc may only touch carriers that are read AND in `T`, so
    `TraegerGleich` keeps the slot and the parsed value is unchanged.
    Used with `hTnot` for plain carriers; shared atomics take the
    §5 path with their value link instead. -/
theorem havoc_erhaelt_gruppenwert {D : Deklaration}
    {T : D.Tab ⊕ D.Glob → Prop} {A : AUmwelt D} (hA : HavocA T A)
    {t : D.Tab} {k : Int} {f : D.Feld t} {lo hi : Int}
    {hT : D.typ t f = .int lo hi} {v : Zahl lo hi}
    (hTnot : ¬ T (.inl t))
    {X : List (D.Tab ⊕ D.Glob)} {σw : World D}
    (hV : (cast (congrArg (Wert D) hT) (σw.speicher.slots t k f)) = v) :
    (cast (congrArg (Wert D) hT) (((A X σw).speicher.slots) t k f)) = v := by
  have hTG := (hA X σw).2 (.inl t) (fun h => hTnot h.2)
  unfold TraegerGleich at hTG
  rw [hTG]
  exact hV

/-! ## 7. Stale reads are allowed; tearing and foreign drain are refused -/

/-- STALE IS ALLOWED (positive): in `sbNach2` core 0 loads `0` for
    `sbY` although core 1 has issued `1` there -- its own buffer misses,
    so the committed byte is what the load returns, and that byte is
    `Lesbar` in the shared projection at its actual value. Stale
    histories are `Lesbar` options, never a simulation gap. -/
theorem stale_lesbar_sb :
    Speichermodell.Lesbar (histVon sbNach2) (sichtVon sbNach2 0) sbY
      ⟨1, 0, Speichermodell.Sicht.null⟩ := by
  have hmiss : neuestens (sbNach2.puffer 0) sbY = none := by decide
  have hrd : sbNach2.mem.lesbar sbY = true := by decide
  have hload : loadByte sbNach2 0 sbY = some 0 := sb_beide_laden_null.1
  exact (load_lesbar_ohne_weiterleitung sbNach2 0 sbY 0 hmiss hrd hload).2

/-- **TEARING, OBSERVED BY TWO CORES (refusal).** After core 0 issues
    two bytes and flushes only the first (`hS2`/`hS3` from the accepted
    projection), the forwarding core assembles the intended pair
    `(1, 1)` while the foreign core assembles the torn word `(1, 0)` --
    which equals neither the pre-issue word nor any single
    flush-atomic update. A group value simulation needs the no-tear
    guard (§§4-5 take all-miss or uniformly-linked footprints); a torn
    footprint has no single source message. Reachability and the
    memory change are joint facts of the same witnesses. -/
theorem gruppe_reisst_fremd :
    ladeWort8 hS3 1 sbX = some (bytesWort (achtBytes sbEins 0 0 0 0 0 0 0)) ∧
      ladeWort8 hS3 0 sbX =
        some (bytesWort (achtBytes sbEins sbEins 0 0 0 0 0 0)) ∧
      bytesWort (achtBytes sbEins 0 0 0 0 0 0 0) ≠
        bytesWort (readBytes hS2.mem sbX) ∧
      TSOErreichbar sbStart hS3 ∧ hS2.mem.bytes sbX ≠ hS3.mem.bytes sbX := by
  refine ⟨by decide, by decide, by decide, ?_, by decide⟩
  exact .schritt
    (.schritt (.schritt .start
      (TSOSchritt.issue sbStart sbNach1 0 sbX sbEins sb_schritt1))
      (TSOSchritt.issue sbNach1 hS2 0 sbY sbEins h_schritt2))
    (TSOSchritt.flush hS2 hS3 0 h_flush)

/-- **FOREIGN FORWARD IS NO COMMITTED READ (refusal).** A fence-ready
    core (`zaunBereit`, own buffer empty) coexists with a foreign
    pending store: the fencing core assembles committed zeros while the
    forwarding core assembles the pending `1` in the same footprint.
    A local drain is no foreign drain (accepted `zaun_kein_fremd_drain`
    and `fremd_weiterleitung_unsichtbar`): the forwarded value has no
    committed message, so only the §5 path (explicit value link) may
    simulate it -- never the committed path of §4. This is the proved
    OBS-5-shaped limitation at group level. -/
theorem gruppe_fremd_weiterleitung_uneinig :
    ∃ s : TSOZustand, zaunBereit s 0 = true ∧
      ladeWort8 s 0 0 = some (bytesWort (achtBytes 0 0 0 0 0 0 0 0)) ∧
      ladeWort8 s 1 0 =
        some (bytesWort (achtBytes (BitVec.ofNat 8 1) 0 0 0 0 0 0 0)) := by
  refine ⟨⟨zeugenSpeicher,
    fun d => if d = 1 then [⟨(0 : Adresse), BitVec.ofNat 8 1⟩] else []⟩,
    by decide, by decide, by decide⟩

/-! ## 8. Joint witness: reached two-core run, simulated read -/

/-- A minimal witness frame over the one-table declaration: the unit
    function with an empty environment, ended (`leave`) at `l = true`.
    No premise, no proof duty -- the shape a reached run would resume. -/
def brueckenRahmen : RufRahmenG witD :=
  ⟨(), Env.nil, witSigma,
    ⟨true, [], [], Env.nil,
      GRest.ende (Endblock.leave (show (true : Bool) = true from rfl))⟩⟩

/-- A minimal witness thread: the frame alone, no trace, no log. -/
def brueckenFaden : RufFadenG witD :=
  ⟨[], brueckenRahmen, [], []⟩

/-- A minimal witness G machine: the witness world's memory on every
    thread, no steps taken. -/
def brueckenG : RufMaschineG witD :=
  ⟨witSigma.speicher, fun _ => brueckenFaden, [], witSigma⟩

/-- The witness W machine: the start state over `brueckenG`, hence one
    message per carrier (timestamp 0) and empty views. -/
def brueckenW : RufMaschineW witD := RufStartW brueckenG

/-- **JOINT WITNESS for `wLesbar_aus_gruppe`.** All premises hold
    jointly on concrete values: the reached two-core TSO state
    `sbGespült` (two issues on different cores, one memory-changing
    flush) carries the group at address 8 with empty buffers; the
    witness world holds slot value 0, represented there; the witness W
    machine holds the timestamp-0 message with an empty view, covered
    by the projection. The conclusion simulates the read at its actual
    value and derives the `lies` consequent for every recording G step.
    Non-degenerate: a table the witness function writes
    (`witD.schreibt`), a reached two-core run with a memory-changing
    flush, and a changed canonical byte beside the read footprint. -/
theorem wLesbar_aus_gruppe_zeuge :
    (∃ w : Wort,
      wortZahl 0 100 w = some (⟨0, by decide, by decide⟩ : Zahl 0 100) ∧
        ∀ M'' : RufMaschineG witD,
          LiestG (mitSpeicher brueckenW.g witSigma.speicher) M'' 0 (.inl ()) →
            Speichermodell.Lesbar brueckenW.hist (brueckenW.sicht 0)
              (.inl ())
              (⟨0, witSigma.speicher,
                Speichermodell.Sicht.null⟩ : NachrichtW witD) ∧
            TraegerGleich witSigma.speicher
              (⟨0, witSigma.speicher, Speichermodell.Sicht.null⟩ :
                NachrichtW witD).wert
              (.inl ())) ∧
      TSOErreichbar sbStart sbGespült ∧
        sbNach2.mem.bytes sbX ≠ sbGespült.mem.bytes sbX ∧
        witD.schreibt () () = true := by
  have hMiss : ∀ i : Nat, i < 8 →
      neuestens (sbGespült.puffer 0) (addrOff 8 i) = none :=
    fun i _ => rfl
  have hRd : lesbar8 sbGespült.mem 8 = true := by decide
  have hRep : RepSlot () (0 : Int) () 0 100 witHT 8 sbGespült.mem witSigma := by
    unfold RepSlot
    decide
  have hR : read64 sbGespült.mem 8 =
      some (bytesWort (readBytes sbGespült.mem 8)) := by
    unfold read64
    rw [if_pos hRd]
  have hWort : ladeWort8 sbGespült 0 8 =
      some (bytesWort (readBytes sbGespült.mem 8)) :=
    (ladeWort8_ohne_weiterleitung sbGespült 0 8 hMiss hRd).trans hR
  have hv : (cast (congrArg (Wert witD) witHT)
      (witSigma.slots () (0 : Int) ())) =
      (⟨0, by decide, by decide⟩ : Zahl 0 100) := rfl
  have hMem : ((⟨0, witSigma.speicher,
      Speichermodell.Sicht.null⟩ : NachrichtW witD) ∈
      brueckenW.hist (.inl ())) :=
    List.mem_singleton_self _
  have hProj : brueckenW.sicht 0 (.inl ()) ≤ sichtVon sbGespült 0 8 :=
    Nat.zero_le _
  have hTs : sichtVon sbGespült 0 8 ≤ 0 := by decide
  have hTraeger : TraegerGleich witSigma.speicher witSigma.speicher
      (.inl ()) :=
    traegerGleich_refl _ _
  have hval := gruppenwert_rep (⟨0, by decide, by decide⟩ : Zahl 0 100)
    hRep hMiss hRd (by decide : (0 : Int) ≤ 0) (by decide)
    _ hWort hv
  refine ⟨⟨_, hval, fun M'' hLi =>
    (wLesbar_aus_gruppe (M'' := M'')
      (⟨0, by decide, by decide⟩ : Zahl 0 100)
      hRep hMiss hRd (by decide : (0 : Int) ≤ 0) (by decide) _ hWort hv hMem
      hProj hTs hTraeger).2 hLi⟩, ?_,
    sb_flush_aendert_speicher, rfl⟩
  exact .schritt
    (.schritt (.schritt .start
      (TSOSchritt.issue sbStart sbNach1 0 sbX sbEins sb_schritt1))
      (TSOSchritt.issue sbNach1 sbNach2 1 sbY sbEins sb_schritt2))
    (TSOSchritt.flush sbNach2 sbGespült 0 sb_flush_schritt)

/- CUTS: what is not proved here
     - No full `SchrittW`/`RufSchrittW` is derived: the simulations
       conclude the `lies` consequent for a real recording G step, but
       the G step itself (hence `wahl`/`neu` witnesses and the run
       induction to W runs) stays with the lowering consumer that owns
       the executed program. `schwach_ist_gX` is therefore cited, not
       applied; applying it here would assume the desired execution.
     - No typed-carrier W/GX mapping beyond one `.int` slot stored as
       one little-endian word (`RepSlot`): sums, floats, bools, globals
       and function pointers have no representation (cut of 570).
     - Forwarded GROUP values need the lowering certificate's value
       link (`hWert` of §5); mixed committed/forwarded footprints have
       no value simulation (tearing refusal of §7).
     - `schwach_ist_gX` reuse, per-access run induction, validator
       soundness (`valX86_sound`) and the source-to-final-bytes closing
       theorem are the recorded next integration, not claimed here.
     - No fairness, progress, timing or cycle-cost claim; no interrupt,
       device, MMIO or DMA model; fences only gate (cut of 567).
     - No new TSO executor and no second IR: `TSOZustand`, `issueByte`,
       `loadByte`, `flushKern`, `TSOErreichbar`, `sb*`/`hS*` witnesses
       and `RepSlot`/`witD` are reused unchanged.
-/

#print axioms ladeWort8
#print axioms lesbar8_hit
#print axioms ladeWort8_ohne_weiterleitung
#print axioms ladeWort8_aus_lesungen
#print axioms ladeByte_ist_jüngste
#print axioms gruppenwert_rep
#print axioms wLesbar_aus_gruppe
#print axioms wLesbar_aus_weiterleitung
#print axioms havoc_erhaelt_gruppenwert
#print axioms stale_lesbar_sb
#print axioms gruppe_reisst_fremd
#print axioms gruppe_fremd_weiterleitung_uneinig
#print axioms wLesbar_aus_gruppe_zeuge

end Gabbro.Grammatik.X86
