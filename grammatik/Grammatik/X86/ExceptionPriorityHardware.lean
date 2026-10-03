/-
  File:      Grammatik/X86/ExceptionPriorityHardware.lean
  Subject:   Precise fault ordering across fetched instruction accesses.

  Lane 738: closes the set-of-possible-faults gap left by lane 670 (which
  proves fault CLASSES but no PRIORITY between pending classes). A generic
  ordered-access/fault relation over the actual fetched-byte decoder
  (`decodeExt` / `fetchExt` / `extByteschritt`) and the actual evaluator
  accesses (`read64` / `write64` / `mulDivSchritt`), with architectural
  priority fetch < decode < address < access < divide < control and
  precise pre-fault observable state. Paging disambiguation (#GP vs #PF)
  and #UD membership are explicit input interfaces, never inferred from
  refusal. Exports the fault/ordered-access producer for common execution
  and IRQ delivery (Table 7-2 boundary order).

  Manual provenance (local snapshot `.tmp/HARDWARE-REFERENCES/`):
  - Table 7-2 "Priority Among Concurrent Events", Intel SDM Vol. 3A Ch. 7
    (txt line 164271): traps on previous instruction > NMI > maskable
    interrupts > fault-class #DB > fetch faults (#GP code-segment limit,
    #PF code page) > decode faults (#GP length > 15, #UD, #NM); pending
    lower-priority exceptions are discarded and may be re-generated.
  - canonical addressing, Vol. 1 §3.3.7.1 (txt line 4220): bits 63..48
    must match bit 47; other linear references raise #GP, stack #SS.
  - DIV entry (txt line 31795), IDIV entry (txt line 31887): zero divisor
    or unrepresentable quotient traps as #DE.
  - #AC entries (txt lines 42479, 62386): alignment checking needs
    CR0.AM = 1, RFLAGS.AC = 1 and CPL = 3; otherwise no #AC.
  - exception vectors Table 6-1, Vol. 1 Ch. 6 (txt lines 9641-9671):
    #DE vec 0, #UD vec 6, #NM vec 7, #SS vec 12, #GP vec 13, #PF vec 14,
    #AC vec 17, #XM vec 19.
-/
import Grammatik.X86.HardwareFaults
import Grammatik.X86.ExtendedExecution

namespace Gabbro.Grammatik.X86

/-- Priority stage of one fault candidate, in architectural order:
    fetch, decode, operand address, data access, divide, control. -/
inductive FehlerStufe where
  | abruf
  | dekodiere
  | adresse
  | zugriff
  | teilung
  | steuerung
  deriving DecidableEq, Repr

/-- Numeric rank: strictly increasing across the stages. -/
def stufenRang : FehlerStufe → Nat
  | .abruf => 0
  | .dekodiere => 1
  | .adresse => 2
  | .zugriff => 3
  | .teilung => 4
  | .steuerung => 5

/-- The rank chain: fetch < decode < address < access < divide < control.
    Cross-class order follows Table 7-2 (fetch before decode) extended in
    execution order for the during-execution faults the table leaves
    implementation-dependent; within-class pins are stated in CUTS. -/
theorem rang_kette :
    stufenRang .abruf < stufenRang .dekodiere ∧
      stufenRang .dekodiere < stufenRang .adresse ∧
      stufenRang .adresse < stufenRang .zugriff ∧
      stufenRang .zugriff < stufenRang .teilung ∧
      stufenRang .teilung < stufenRang .steuerung := by
  decide

/-- Explicit paging input interface: the present bit decides #GP vs #PF.
    Lane 670 pinned `.pf` for every refused access; here the caller states
    the page state and the CLASS FOLLOWS from it -- never chosen by the
    relation itself. A non-present page faults as #PF; a present-but-denied
    page (non-paging protection) faults as #GP. -/
structure SeitenInfo where
  vorhanden : Adresse → Bool

/-- #GP vs #PF from the explicit page state: no arbitrary choice. -/
def seitenKlasse (pg : SeitenInfo) (a : Adresse) : ArchFehler :=
  if pg.vorhanden a then .gp else .pf

/-- A non-present page resolves to #PF, for every page state. -/
theorem seitenKlasse_nicht_vorhanden (pg : SeitenInfo) (a : Adresse)
    (h : pg.vorhanden a = false) : seitenKlasse pg a = .pf := by
  simp [seitenKlasse, h]

/-- A present-but-denied page resolves to #GP, for every page state. -/
theorem seitenKlasse_vorhanden (pg : SeitenInfo) (a : Adresse)
    (h : pg.vorhanden a = true) : seitenKlasse pg a = .gp := by
  simp [seitenKlasse, h]

/-- Explicit illegality input interface: #UD membership is STATED by the
    consumer (validator/hardware profile), never inferred from decoder
    refusal. `decodeExt = none` alone yields admission refusal, not #UD. -/
structure IllegalInfo where
  istIllegal : List Byte → Bool

/-- Explicit control-state input interface: alignment checking fires only
    when armed (CR0.AM, RFLAGS.AC, CPL = 3 per txt line 62386). The
    admitted profile runs disarmed; unmasked #NM/#XM traps have no
    producer here (see CUTS). -/
structure SteuerInfo where
  acScharf : Bool

/-- One ordered fault candidate: its stage plus its class. -/
structure PrioritaetsFehler where
  stufe : FehlerStufe
  klasse : ArchFehler
  deriving DecidableEq, Repr

/-- Caller-supplied access description of one fetched instruction: the
    data-read and data-write addresses (if any), whether the reference is
    through a stack register (rsp/rbp: #SS instead of #GP), the alignment
    the access requires, and whether the instruction divides. The producer
    never decodes operands itself; the consumer binds the descriptor to
    the actual decoded arm (witnesses below pin two arms). -/
structure ZugriffsBeschreibung where
  lese : Option Adresse
  schreibe : Option Adresse
  stapel : Bool
  ausrichtung : Nat
  teilt : Bool

/-! ## Fetch and decode candidates from the actual fetched window.

  All predicates run on `geholt t.kern` (actual executable bytes at RIP)
  through the actual unified decoder and admission check. A noncanonical
  RIP is #GP (fetch never reads stack semantics); an empty window is the
  code page fault #PF; a refused decode is #UD only under the explicit
  illegality oracle, overlong (#GP, full 15-byte window still refusing)
  or truncated (#PF at the execute boundary) otherwise; a refused
  admission with successful decode is fetch-side #PF. -/

/-- Fetch-stage candidate: noncanonical RIP, empty window, or refused
    admission with a successful decode (execute-denied prefix or length
    inconsistency -- both fetch-side, both #PF in 64-bit mode). -/
def abrufKandidat (t : FpZustand) : Option PrioritaetsFehler :=
  if istKanonisch t.kern.rip then
    match geholt t.kern with
    | [] => some ⟨.abruf, .pf⟩
    | _ :: _ =>
      match decodeExt (geholt t.kern) with
      | none => none
      | some (i, rest) =>
        if extZugelassen t (geholt t.kern) i rest then none
        else some ⟨.abruf, .pf⟩
  else some ⟨.abruf, .gp⟩

/-- A noncanonical RIP is the fetch #GP candidate, in every memory. -/
theorem abruf_nichtkanonisch_rip (t : FpZustand)
    (h : istKanonisch t.kern.rip = false) :
    abrufKandidat t = some ⟨.abruf, .gp⟩ := by
  simp [abrufKandidat, h]

/-- An empty fetched window is the fetch #PF candidate. -/
theorem abruf_leeres_fenster (t : FpZustand)
    (hkan : istKanonisch t.kern.rip = true)
    (hleer : geholt t.kern = []) :
    abrufKandidat t = some ⟨.abruf, .pf⟩ := by
  simp [abrufKandidat, hkan, hleer]

/-- An admitted fetch carries no fetch candidate. -/
theorem abruf_zugelassen_keiner (t : FpZustand) (i : ExtInstr)
    (rest : List Byte)
    (hkan : istKanonisch t.kern.rip = true)
    (hne : geholt t.kern ≠ [])
    (hdec : decodeExt (geholt t.kern) = some (i, rest))
    (hz : extZugelassen t (geholt t.kern) i rest = true) :
    abrufKandidat t = none := by
  have e : abrufKandidat t =
      match decodeExt (geholt t.kern) with
      | none => (none : Option PrioritaetsFehler)
      | some (j, rs) =>
        if extZugelassen t (geholt t.kern) j rs then none
        else some ⟨.abruf, .pf⟩ := by
    simp [abrufKandidat, hkan]
    cases hg : geholt t.kern with
    | nil => exact absurd hg hne
    | cons _ _ => rfl
  rw [e, hdec]
  simp [hz]

/-- Decode-stage candidate on a refused decode: #UD only under the
    explicit oracle; a full 15-byte window that still refuses is overlong
    (#GP per Table 7-2); a short window is truncated at the execute
    boundary (fetch-side #PF). Without oracle evidence there is NO #UD. -/
def dekodiereKandidat (t : FpZustand) (ill : IllegalInfo) :
    Option PrioritaetsFehler :=
  match decodeExt (geholt t.kern) with
  | some _ => none
  | none =>
    if ill.istIllegal (geholt t.kern) then some ⟨.dekodiere, .ud⟩
    else if (geholt t.kern).length = fetchCap then some ⟨.dekodiere, .gp⟩
    else some ⟨.abruf, .pf⟩

/-- A successful decode carries no decode candidate. -/
theorem dekodiere_erfolg_keiner (t : FpZustand) (ill : IllegalInfo)
    (i : ExtInstr) (rest : List Byte)
    (h : decodeExt (geholt t.kern) = some (i, rest)) :
    dekodiereKandidat t ill = none := by
  simp [dekodiereKandidat, h]

/-- Refusal without oracle evidence is never #UD: truncated short window
    reads as fetch #PF. -/
theorem dekodiere_ohne_orakel_kein_ud (t : FpZustand) (ill : IllegalInfo)
    (href : decodeExt (geholt t.kern) = none)
    (hill : ill.istIllegal (geholt t.kern) = false)
    (hkurz : (geholt t.kern).length ≠ fetchCap) :
    dekodiereKandidat t ill = some ⟨.abruf, .pf⟩ := by
  simp [dekodiereKandidat, href, hill, hkurz]

/-- Oracle-stated illegality is the #UD candidate. -/
theorem dekodiere_orakel_ud (t : FpZustand) (ill : IllegalInfo)
    (href : decodeExt (geholt t.kern) = none)
    (hill : ill.istIllegal (geholt t.kern) = true) :
    dekodiereKandidat t ill = some ⟨.dekodiere, .ud⟩ := by
  simp [dekodiereKandidat, href, hill]

/-- A full window that still refuses, without oracle evidence, is the
    overlong #GP candidate. -/
theorem dekodiere_voll_ohne_orakel_gp (t : FpZustand) (ill : IllegalInfo)
    (href : decodeExt (geholt t.kern) = none)
    (hill : ill.istIllegal (geholt t.kern) = false)
    (hvoll : (geholt t.kern).length = fetchCap) :
    dekodiereKandidat t ill = some ⟨.dekodiere, .gp⟩ := by
  simp [dekodiereKandidat, href, hill, hvoll]

/-! ## Address, access, divide and control candidates.

  The address stage reuses lane 670's `adrKlasse` (#SS for stack
  references, #GP else) over the descriptor's addresses, read before
  write in program order. The access stage runs the actual
  permission-checked `read64`/`write64` and resolves #GP vs #PF through
  the explicit page state. The divide stage fires only on the actual
  evaluator trap (same selection pattern as `stepExt_muldiv_halt`); the
  control stage fires #AC only when armed. -/

/-- Address-stage candidate: noncanonical operand addresses, read before
    write. The class reuses the proved `adrKlasse` rule. -/
def adressKandidat (z : ZugriffsBeschreibung) : Option PrioritaetsFehler :=
  match z.lese with
  | some a =>
    match adrKlasse a z.stapel with
    | some k => some ⟨.adresse, k⟩
    | none =>
      match z.schreibe with
      | some b =>
        match adrKlasse b z.stapel with
        | some k => some ⟨.adresse, k⟩
        | none => none
      | none => none
  | none =>
    match z.schreibe with
    | some b =>
      match adrKlasse b z.stapel with
      | some k => some ⟨.adresse, k⟩
      | none => none
    | none => none

/-- A noncanonical read address is the address-stage candidate, whatever
    the write side says: the read is checked first. Stack references give
    #SS, all others #GP. -/
theorem adress_lese_nichtkanonisch (z : ZugriffsBeschreibung) (a : Adresse)
    (hlese : z.lese = some a) (hkan : istKanonisch a = false) :
    adressKandidat z =
      if z.stapel then some ⟨.adresse, .ss⟩
      else some ⟨.adresse, .gp⟩ := by
  unfold adressKandidat
  rw [hlese]
  cases hst : z.stapel <;> simp_all [adrKlasse]

/-- Canonical addresses on both sides carry no address candidate. -/
theorem adress_kanonisch_keiner (z : ZugriffsBeschreibung)
    (hlese : ∀ a, z.lese = some a → istKanonisch a = true)
    (hschreibe : ∀ b, z.schreibe = some b → istKanonisch b = true) :
    adressKandidat z = none := by
  cases hlese' : z.lese with
  | none =>
    cases hschreibe' : z.schreibe with
    | none => simp [adressKandidat, hlese', hschreibe']
    | some b =>
      have hkan := hschreibe b hschreibe'
      have hklasse := adrKlasse_kanonisch_kein_fehler b hkan z.stapel
      simp [adressKandidat, hlese', hschreibe', hklasse]
  | some a =>
    have hkan := hlese a hlese'
    have hklasse := adrKlasse_kanonisch_kein_fehler a hkan z.stapel
    cases hschreibe' : z.schreibe with
    | none => simp [adressKandidat, hlese', hklasse, hschreibe']
    | some b =>
      have hkan2 := hschreibe b hschreibe'
      have hklasse2 := adrKlasse_kanonisch_kein_fehler b hkan2 z.stapel
      simp [adressKandidat, hlese', hklasse, hschreibe', hklasse2]

/-- Access-stage candidate: the actual permission-checked access through
    `read64`/`write64`, read before write, class from the page state. -/
def schreibKandidat (t : FpZustand) (z : ZugriffsBeschreibung)
    (pg : SeitenInfo) : Option PrioritaetsFehler :=
  match z.schreibe with
  | some b =>
    match write64 t.kern.speicher b 0 with
    | some _ => none
    | none => some ⟨.zugriff, seitenKlasse pg b⟩
  | none => none

/-- Access-stage candidate: the actual permission-checked access through
    `read64`/`write64`, read before write, class from the page state. -/
def zugriffKandidat (t : FpZustand) (z : ZugriffsBeschreibung)
    (pg : SeitenInfo) : Option PrioritaetsFehler :=
  match z.lese with
  | some a =>
    match read64 t.kern.speicher a with
    | some _ => schreibKandidat t z pg
    | none => some ⟨.zugriff, seitenKlasse pg a⟩
  | none => schreibKandidat t z pg

/-- A refused read is the access-stage candidate with the page-state
    class, whatever the write side says. -/
theorem zugriff_lese_verweigert (t : FpZustand) (z : ZugriffsBeschreibung)
    (pg : SeitenInfo) (a : Adresse)
    (hlese : z.lese = some a)
    (hread : read64 t.kern.speicher a = none) :
    zugriffKandidat t z pg = some ⟨.zugriff, seitenKlasse pg a⟩ := by
  simp [zugriffKandidat, hlese, hread]

/-- A refused write with no read side is the access-stage candidate. -/
theorem zugriff_schreibe_verweigert (t : FpZustand)
    (z : ZugriffsBeschreibung) (pg : SeitenInfo) (b : Adresse)
    (hlese : z.lese = none) (hschreibe : z.schreibe = some b)
    (hwrite : write64 t.kern.speicher b 0 = none) :
    zugriffKandidat t z pg = some ⟨.zugriff, seitenKlasse pg b⟩ := by
  unfold zugriffKandidat schreibKandidat
  rw [hlese, hschreibe]
  dsimp only
  rw [hwrite]

/-- Successful accesses on both sides carry no access candidate. -/
theorem zugriff_erfolg_keiner (t : FpZustand) (z : ZugriffsBeschreibung)
    (pg : SeitenInfo) (v : Wort)
    (hlese : ∀ a, z.lese = some a → read64 t.kern.speicher a = some v)
    (hschreibe : ∀ b, z.schreibe = some b →
      ∃ m' : Speicher, write64 t.kern.speicher b 0 = some m') :
    zugriffKandidat t z pg = none := by
  cases hlese' : z.lese with
  | none =>
    cases hschreibe' : z.schreibe with
    | none =>
      unfold zugriffKandidat schreibKandidat
      rw [hlese', hschreibe']
    | some b =>
      obtain ⟨m', hm'⟩ := hschreibe b hschreibe'
      unfold zugriffKandidat schreibKandidat
      rw [hlese', hschreibe']
      dsimp only
      rw [hm']
  | some a =>
    have hread := hlese a hlese'
    cases hschreibe' : z.schreibe with
    | none =>
      unfold zugriffKandidat schreibKandidat
      rw [hlese']
      dsimp only
      rw [hread]
      dsimp only
      rw [hschreibe']
    | some b =>
      obtain ⟨m', hm'⟩ := hschreibe b hschreibe'
      unfold zugriffKandidat schreibKandidat
      rw [hlese']
      dsimp only
      rw [hread]
      dsimp only
      rw [hschreibe']
      dsimp only
      rw [hm']

end Gabbro.Grammatik.X86
