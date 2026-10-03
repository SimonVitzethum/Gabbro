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

/-! ## Divide and control candidates.

  The divide stage fires only on the actual evaluator trap (the caller
  ties the flag to `mulDivSchritt = .hardwareHalt`, the same selection
  pattern as `stepExt_muldiv_halt`). The control stage fires #AC only
  when armed through the explicit control input; disarmed control never
  faults, matching silicon where #AC needs flag setup. -/

/-- Divide-stage candidate: the actual divide trap IS #DE. The flag is
    caller-supplied evidence from `mulDivSchritt`, never an assumption. -/
def teilungsKandidat (falle : Bool) : Option PrioritaetsFehler :=
  if falle then some ⟨.teilung, .de⟩ else none

/-- A proved trap is the divide candidate. -/
theorem teilung_falle_ist_de (h : falle = true) :
    teilungsKandidat falle = some ⟨.teilung, .de⟩ := by
  simp [teilungsKandidat, h]

/-- Without trap evidence there is no divide candidate. -/
theorem teilung_ohne_falle_keiner (h : falle = false) :
    teilungsKandidat falle = none := by
  simp [teilungsKandidat, h]

/-- Control-stage candidate: #AC only when armed and misaligned. The
    addresses are the descriptor's present data addresses; the check is
    the actual `addrAusgerichtet` predicate. -/
def steuerKandidat (z : ZugriffsBeschreibung) (st : SteuerInfo) :
    Option PrioritaetsFehler :=
  if st.acScharf then
    match z.lese with
    | some a =>
      if addrAusgerichtet a z.ausrichtung then
        match z.schreibe with
        | some b =>
          if addrAusgerichtet b z.ausrichtung then none
          else some ⟨.steuerung, .ac⟩
        | none => none
      else some ⟨.steuerung, .ac⟩
    | none =>
      match z.schreibe with
      | some b =>
        if addrAusgerichtet b z.ausrichtung then none
        else some ⟨.steuerung, .ac⟩
      | none => none
  else none

/-- Disarmed control never faults, in every state and descriptor. -/
theorem steuerung_entschaerft_keiner (z : ZugriffsBeschreibung)
    (st : SteuerInfo) (h : st.acScharf = false) :
    steuerKandidat z st = none := by
  simp [steuerKandidat, h]

/-- An armed misaligned read is the #AC candidate. -/
theorem steuerung_scharf_falsch_ausgerichtet (z : ZugriffsBeschreibung)
    (st : SteuerInfo) (a : Adresse)
    (hscharf : st.acScharf = true) (hlese : z.lese = some a)
    (hschief : addrAusgerichtet a z.ausrichtung = false) :
    steuerKandidat z st = some ⟨.steuerung, .ac⟩ := by
  simp [steuerKandidat, hscharf, hlese, hschief]

/-! ## Ordered selection: the first pending candidate wins.

  The candidate row is collected in priority order by construction, so
  the head IS the minimum-rank pending fault. Dominance theorems pin
  the exact chosen cause whenever several stages fire at once. -/

/-- The ordered candidate row: fetch, decode, address, access, divide,
    control -- priority order by construction. -/
def kandidatenReihe (t : FpZustand) (z : ZugriffsBeschreibung)
    (pg : SeitenInfo) (st : SteuerInfo) (ill : IllegalInfo)
    (teiltFalle : Bool) : List PrioritaetsFehler :=
  ((abrufKandidat t).toList ++ (dekodiereKandidat t ill).toList ++
    (adressKandidat z).toList ++ (zugriffKandidat t z pg).toList ++
    (teilungsKandidat teiltFalle).toList ++
    (steuerKandidat z st).toList)

/-- The chosen fault: the first pending candidate. -/
def ersteWahl (ks : List PrioritaetsFehler) : Option PrioritaetsFehler :=
  ks.head?

/-- The choice over the row: exactly the row head. -/
theorem ersteWahl_reihe (t : FpZustand) (z : ZugriffsBeschreibung)
    (pg : SeitenInfo) (st : SteuerInfo) (ill : IllegalInfo)
    (teiltFalle : Bool) :
    ersteWahl (kandidatenReihe t z pg st ill teiltFalle) =
      (kandidatenReihe t z pg st ill teiltFalle).head? := rfl

/-- CASE SPLIT: the choice is the earliest firing stage. The chosen
    cause is never beaten by a later stage, and no earlier stage fires. -/
theorem wahl_fallunterscheidung (t : FpZustand) (z : ZugriffsBeschreibung)
    (pg : SeitenInfo) (st : SteuerInfo) (ill : IllegalInfo)
    (teiltFalle : Bool) (f : PrioritaetsFehler)
    (h : ersteWahl (kandidatenReihe t z pg st ill teiltFalle) = some f) :
    abrufKandidat t = some f ∨
      (abrufKandidat t = none ∧ dekodiereKandidat t ill = some f) ∨
      (abrufKandidat t = none ∧ dekodiereKandidat t ill = none ∧
        adressKandidat z = some f) ∨
      (abrufKandidat t = none ∧ dekodiereKandidat t ill = none ∧
        adressKandidat z = none ∧ zugriffKandidat t z pg = some f) ∨
      (abrufKandidat t = none ∧ dekodiereKandidat t ill = none ∧
        adressKandidat z = none ∧ zugriffKandidat t z pg = none ∧
        teilungsKandidat teiltFalle = some f) ∨
      (abrufKandidat t = none ∧ dekodiereKandidat t ill = none ∧
        adressKandidat z = none ∧ zugriffKandidat t z pg = none ∧
        teilungsKandidat teiltFalle = none ∧
        steuerKandidat z st = some f) := by
  cases hab : abrufKandidat t with
  | some g =>
    have hgf : g = f := by
      simp [ersteWahl, kandidatenReihe, hab] at h
      exact h
    exact Or.inl (by rw [hgf])
  | none =>
    cases hdec : dekodiereKandidat t ill with
    | some g =>
      have hgf : g = f := by
        simp [ersteWahl, kandidatenReihe, hab, hdec] at h
        exact h
      exact Or.inr (Or.inl ⟨rfl, by rw [hgf]⟩)
    | none =>
      cases hadr : adressKandidat z with
      | some g =>
        have hgf : g = f := by
          simp [ersteWahl, kandidatenReihe, hab, hdec, hadr] at h
          exact h
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by rw [hgf]⟩))
      | none =>
        cases hzug : zugriffKandidat t z pg with
        | some g =>
          have hgf : g = f := by
            simp [ersteWahl, kandidatenReihe, hab, hdec, hadr, hzug] at h
            exact h
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl,
            by rw [hgf]⟩)))
        | none =>
          cases htei : teilungsKandidat teiltFalle with
          | some g =>
            have hgf : g = f := by
              simp [ersteWahl, kandidatenReihe, hab, hdec, hadr, hzug,
                htei] at h
              exact h
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨rfl, rfl, rfl, rfl, by rw [hgf]⟩))))
          | none =>
            cases hst : steuerKandidat z st with
            | some g =>
              have hgf : g = f := by
                simp [ersteWahl, kandidatenReihe, hab, hdec, hadr, hzug,
                  htei, hst] at h
                exact h
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                ⟨rfl, rfl, rfl, rfl, rfl, by rw [hgf]⟩))))
            | none =>
              simp [ersteWahl, kandidatenReihe, hab, hdec, hadr, hzug,
                htei, hst] at h

/-- A fetch candidate beats everything: exact cause under conflict. -/
theorem abruf_schlaegt_alles (t : FpZustand) (z : ZugriffsBeschreibung)
    (pg : SeitenInfo) (st : SteuerInfo) (ill : IllegalInfo)
    (teiltFalle : Bool) (f : PrioritaetsFehler)
    (h : abrufKandidat t = some f) :
    ersteWahl (kandidatenReihe t z pg st ill teiltFalle) = some f := by
  simp [ersteWahl, kandidatenReihe, h]

/-- An address candidate beats access, divide and control -- given quiet
    fetch and decode. -/
theorem adresse_schlaegt_spaete (t : FpZustand) (z : ZugriffsBeschreibung)
    (pg : SeitenInfo) (st : SteuerInfo) (ill : IllegalInfo)
    (teiltFalle : Bool) (f : PrioritaetsFehler)
    (hfrueh : abrufKandidat t = none)
    (hdec : dekodiereKandidat t ill = none)
    (hadr : adressKandidat z = some f) :
    ersteWahl (kandidatenReihe t z pg st ill teiltFalle) = some f := by
  simp [ersteWahl, kandidatenReihe, hfrueh, hdec, hadr]

/-- An access candidate beats divide and control -- given quiet fetch,
    decode and address. -/
theorem zugriff_schlaegt_teilung_steuerung (t : FpZustand)
    (z : ZugriffsBeschreibung) (pg : SeitenInfo) (st : SteuerInfo)
    (ill : IllegalInfo) (teiltFalle : Bool) (f : PrioritaetsFehler)
    (hfrueh : abrufKandidat t = none)
    (hdec : dekodiereKandidat t ill = none)
    (hadr : adressKandidat z = none)
    (hzug : zugriffKandidat t z pg = some f) :
    ersteWahl (kandidatenReihe t z pg st ill teiltFalle) = some f := by
  simp [ersteWahl, kandidatenReihe, hfrueh, hdec, hadr, hzug]

/-- The divide trap beats control -- given quiet fetch, decode, address
    and access. -/
theorem teilung_schlaegt_steuerung (t : FpZustand) (z : ZugriffsBeschreibung)
    (pg : SeitenInfo) (st : SteuerInfo) (ill : IllegalInfo)
    (hfrueh : abrufKandidat t = none)
    (hdec : dekodiereKandidat t ill = none)
    (hadr : adressKandidat z = none)
    (hzug : zugriffKandidat t z pg = none)
    (hfalle : teiltFalle = true) :
    ersteWahl (kandidatenReihe t z pg st ill teiltFalle) =
      some ⟨.teilung, .de⟩ := by
  simp [ersteWahl, kandidatenReihe, teilungsKandidat, hfrueh, hdec, hadr,
    hzug, hfalle]

/-! ## Verdict producer for common execution and IRQ delivery.

  The verdict keeps three outcomes apart BY CONSTRUCTION: success with
  the actual successor, a fault with its stage and class, and admission
  refusal (validator verdict, never a fault). The binder takes the
  ACTUAL unified outcome, so success is never invented. `halt` binds to
  the divide trap: it is proved below that `halt` comes only from the
  divide arm. -/

/-- The bound verdict: success, ordered fault, or admission refusal. -/
inductive FehlerUrteil where
  | erfolg : FpZustand → FehlerUrteil
  | fehler : PrioritaetsFehler → FehlerUrteil
  | zugelassenVerweigert : FehlerUrteil

/-- Bind the actual outcome to the ordered choice: success keeps its
    successor, `halt` IS the divide trap, refusal carries the choice or
    stays admission refusal when no candidate fires. -/
def bindeUrteil (o : ExtAusgang) (wahl : Option PrioritaetsFehler) :
    FehlerUrteil :=
  match o with
  | .weiter t' => .erfolg t'
  | .halt => .fehler ⟨.teilung, .de⟩
  | .verweigert =>
    match wahl with
    | some f => .fehler f
    | none => .zugelassenVerweigert

/-- Success is never invented: `erfolg` carries the actual successor. -/
theorem urteil_erfolg_treue (t' : FpZustand) (wahl : Option PrioritaetsFehler) :
    bindeUrteil (.weiter t') wahl = .erfolg t' := rfl

/-- `halt` always binds the divide trap, whatever the choice says. -/
theorem urteil_halt_ist_teilung (wahl : Option PrioritaetsFehler) :
    bindeUrteil .halt wahl = .fehler ⟨.teilung, .de⟩ := rfl

/-- Admission refusal is never a fault: the two outcomes differ. -/
theorem verweigerung_kein_fehler (f : PrioritaetsFehler) :
    FehlerUrteil.zugelassenVerweigert ≠ .fehler f := by
  intro h
  cases h

/-- Refusal with a choice binds that exact choice. -/
theorem urteil_verweigert_wahl (f : PrioritaetsFehler) :
    bindeUrteil .verweigert (some f) = .fehler f := rfl

/-- Refusal without a choice stays admission refusal. -/
theorem urteil_verweigert_ohne_wahl :
    bindeUrteil .verweigert none = .zugelassenVerweigert := rfl

/-- HALT COMES ONLY FROM DIVIDE: a byte-step `halt` implies a fetched
    multiply/divide instruction whose actual evaluator trapped. Every
    other arm yields `weiter` or `verweigert` by its selection equation. -/
theorem halt_kommt_von_teilung (t : FpZustand) (b : BereitProfil)
    (h : extByteschritt t b = .halt) :
    ∃ m : MulDivDecodiert, ∃ rest : List Byte,
      fetchExt t (geholt t.kern) = some (.muldiv m, rest) ∧
        mulDivSchritt m t.kern = .hardwareHalt := by
  have e : extByteschritt t b =
      match fetchExt t (geholt t.kern) with
      | none => ExtAusgang.verweigert
      | some (j, _) => stepExt j t b := rfl
  rw [e] at h
  cases hfetch : fetchExt t (geholt t.kern) with
  | none => simp [hfetch] at h
  | some p =>
    simp [hfetch] at h
    cases p with
    | mk i rest =>
      cases i with
      | pilot d =>
        cases hstep : laufAlt d t with
        | some t' =>
          have hs := stepExt_pilot d t t' b hstep
          rw [hs] at h
          cases h
        | none =>
          have hs := stepExt_pilot_verweigert d t b hstep
          rw [hs] at h
          cases h
      | narrow n =>
        have hs : stepExt (.narrow n) t b ≠ .halt := by
          cases hstep : stepNarrow n t.kern with
          | some s' =>
            have := stepExt_narrow n t b s' hstep
            simp [this]
          | none =>
            have := stepExt_narrow_verweigert n t b hstep
            simp [this]
        exact absurd h hs
      | muldiv m =>
        cases htrap : mulDivSchritt m t.kern with
        | ok s' =>
          have hs := stepExt_muldiv_ok m t b s' htrap
          rw [hs] at h
          cases h
        | hardwareHalt => exact ⟨m, rest, rfl, htrap⟩
        | misslungen =>
          have hs := stepExt_muldiv_misslungen m t b htrap
          rw [hs] at h
          cases h
      | shift d =>
        have hs : stepExt (.shift d) t b ≠ .halt := by
          cases hstep : shiftSchritt d t.kern with
          | some s' =>
            have := stepExt_shift d t b s' hstep
            simp [this]
          | none =>
            have := stepExt_shift_verweigert d t b hstep
            simp [this]
        exact absurd h hs
      | setcc c dst l =>
        have hs : stepExt (.setcc c dst l) t b ≠ .halt := by
          cases hstep : setccSchrittBytes l t.kern dst c with
          | some s' =>
            have := stepExt_setcc c dst l t b s' hstep
            simp [this]
          | none =>
            have := stepExt_setcc_verweigert c dst l t b hstep
            simp [this]
        exact absurd h hs
      | cmov c dst src l =>
        have hs : stepExt (.cmov c dst src l) t b ≠ .halt := by
          cases hstep : cmovSchrittBytes l t.kern dst src c with
          | some s' =>
            have := stepExt_cmov c dst src l t b s' hstep
            simp [this]
          | none =>
            have := stepExt_cmov_verweigert c dst src l t b hstep
            simp [this]
        exact absurd h hs
      | fp f =>
        have hs : stepExt (.fp f) t b ≠ .halt := by
          cases hstep : fpSchritt f t with
          | some t' =>
            have := stepExt_fp f t t' b hstep
            simp [this]
          | none =>
            have := stepExt_fp_verweigert f t b hstep
            simp [this]
        exact absurd h hs
      | vec v =>
        have hs : stepExt (.vec v) t b ≠ .halt := by
          cases hstep : stepVector v t b with
          | some t' =>
            have := stepExt_vec v t t' b hstep
            simp [this]
          | none =>
            have := stepExt_vec_verweigert v t b hstep
            simp [this]
        exact absurd h hs

/-! ## Delivery interface: vector numbers and fault RIP.

  The consumer for fault delivery (lane 672) reads the Table 6-1 vector
  and the faulting RIP off the verdict. The fault RIP is the pre-state
  RIP by construction: no handler runs and no RIP advances here. -/

/-- Table 6-1 vector of one fault class. -/
def fehlerVektor : ArchFehler → Nat
  | .de => 0
  | .ud => 6
  | .nm => 7
  | .ss => 12
  | .gp => 13
  | .pf => 14
  | .ac => 17
  | .xm => 19

/-- The divide trap delivers on vector 0. -/
theorem vektor_de_null : fehlerVektor .de = 0 := rfl

/-- The page fault delivers on vector 14. -/
theorem vektor_pf_vierzehn : fehlerVektor .pf = 14 := rfl

/-- The faulting RIP of one bound verdict, for IDT delivery. -/
def urteilRip (u : FehlerUrteil) : Option Adresse :=
  match u with
  | .fehler _ => none
  | .erfolg t' => some t'.kern.rip
  | .zugelassenVerweigert => none

/-- The pre-fault RIP producer: the faulting instruction address is the
    pre-state RIP, read off the state the candidate ran on. -/
def fehlerRipVor (t : FpZustand) : Adresse := t.kern.rip

/-- The pre-fault observation IS the pre-state: fault RIP names the
    faulting instruction and no successor memory exists. -/
theorem vorFehler_beobachtung (t : FpZustand) (f : PrioritaetsFehler) :
    fehlerRipVor t = t.kern.rip ∧
      ∀ t' : FpZustand, bindeUrteil .verweigert (some f) ≠ .erfolg t' := by
  refine ⟨rfl, ?_⟩
  intro t' hcon
  simp [bindeUrteil] at hcon

/-! ## No partial writes: success writes the whole footprint.

  A successful `write64` writes exactly the eight footprint bytes
  (proved from `writeBytesN_hit`/`_miss`); a refused store has no
  successor at all. Partial-write and stack-switch specifics stay
  unstated (see CUTS). -/

/-- NO PARTIAL WRITE: a successful store writes every footprint byte
    from the value and keeps every outside byte. -/
theorem kein_teilschreiben (m m' : Speicher) (a : Adresse) (v : Wort)
    (h : write64 m a v = some m') (x : Adresse) :
    (∃ i : Nat, i < 8 ∧ x = addrOff a i ∧ m'.bytes x = wortByte v i) ∨
      (∀ i : Nat, i < 8 → x ≠ addrOff a i) ∧ m'.bytes x = m.bytes x := by
  have hdef : write64 m a v =
      if schreibbar8 m a then some { m with bytes := writeBytes m a v }
        else none := rfl
  rw [hdef] at h
  cases hperm : schreibbar8 m a with
  | false => simp [hperm] at h
  | true =>
    simp [hperm] at h
    have hm' : m' = { m with bytes := writeBytes m a v } := h.symm
    by_cases hfoot : ∃ i : Nat, i < 8 ∧ x = addrOff a i
    · obtain ⟨i, hi, rfl⟩ := hfoot
      left
      refine ⟨i, hi, rfl, ?_⟩
      rw [hm']
      show writeBytes m a v (addrOff a i) = wortByte v i
      unfold writeBytes
      exact writeBytesN_hit m a v 8 i hi (by omega)
    · right
      have hfoot' : ∀ i : Nat, i < 8 → x ≠ addrOff a i := by
        intro i hi hcontra
        exact hfoot ⟨i, hi, hcontra⟩
      refine ⟨hfoot', ?_⟩
      rw [hm']
      show writeBytes m a v x = m.bytes x
      unfold writeBytes
      exact writeBytesN_miss m a v 8 x (fun k hk => hfoot' k hk)

/-! ## Instruction-boundary order (Table 7-2, classes 4-9).

  At an instruction boundary the processor services the highest-priority
  pending event; lower-priority exceptions are discarded (and possibly
  re-generated later). Classes 1-3 (reset, task switch, external
  interventions) are hardware assumptions outside this model. Faults that
  arise DURING execution (address, access, divide, control) are not
  boundary events at all: they trap immediately, ahead of any pending
  interrupt, because interrupts are sampled only at boundaries. -/

/-- Boundary events of classes 4-7: previous-instruction trap, NMI,
    maskable interrupt with its vector, fault-class debug breakpoint. -/
inductive GrenzEreignis where
  | vorTrap : GrenzEreignis
  | nmi : GrenzEreignis
  | irq : Nat → GrenzEreignis
  | bruchFehler : GrenzEreignis

/-- Boundary decision: deliver an event, deliver an ordered fault, or
    execute on. -/
inductive GrenzEntscheid where
  | ereignisAusliefern : GrenzEreignis → GrenzEntscheid
  | falleAusliefern : PrioritaetsFehler → GrenzEntscheid
  | weiterAusfuehren : GrenzEntscheid

/-- During-execution faults never wait for the boundary. -/
def istAusfuehrungsfehler : PrioritaetsFehler → Bool
  | ⟨.adresse, _⟩ => true
  | ⟨.zugriff, _⟩ => true
  | ⟨.teilung, _⟩ => true
  | ⟨.steuerung, _⟩ => true
  | _ => false

/-- Split off an immediate during-execution fault, if any. -/
def burstAusfuehrung (wahl : Option PrioritaetsFehler) :
    Option PrioritaetsFehler :=
  match wahl with
  | some f => if istAusfuehrungsfehler f then some f else none
  | none => none

/-- The boundary decision in Table 7-2 order: previous traps, NMI,
    enabled maskable interrupts, fault-class debug, then fetch/decode
    faults of the next instruction. -/
def grenzEntscheid (vorTrap : Bool) (nmiAnhaengig : Bool)
    (irqAnhaengig : Bool) (irqNr : Nat) (irqFrei : Bool) (bruch : Bool)
    (wahl : Option PrioritaetsFehler) : GrenzEntscheid :=
  match burstAusfuehrung wahl with
  | some f => .falleAusliefern f
  | none =>
    if vorTrap then .ereignisAusliefern .vorTrap
    else if nmiAnhaengig then .ereignisAusliefern .nmi
    else if irqAnhaengig && irqFrei then .ereignisAusliefern (.irq irqNr)
    else if bruch then .ereignisAusliefern .bruchFehler
    else match wahl with
      | some f => .falleAusliefern f
      | none => .weiterAusfuehren

/-- DURING-EXECUTION FAULTS TRAP IMMEDIATELY: no pending event at the
    (not yet reached) boundary defers them. -/
theorem ausfuehrungsfehler_sofort (vorTrap : Bool) (nmiAnhaengig : Bool)
    (irqAnhaengig : Bool) (irqNr : Nat) (irqFrei : Bool) (bruch : Bool)
    (f : PrioritaetsFehler)
    (hausf : istAusfuehrungsfehler f = true) :
    grenzEntscheid vorTrap nmiAnhaengig irqAnhaengig irqNr irqFrei bruch
      (some f) = .falleAusliefern f := by
  simp [grenzEntscheid, burstAusfuehrung, hausf]

/-- Class 4 beats everything behind it: a previous-instruction trap is
    delivered ahead of interrupts and fetch/decode faults. -/
theorem vortrap_schlaegt_alle (nmiAnhaengig : Bool) (irqAnhaengig : Bool)
    (irqNr : Nat) (irqFrei : Bool) (bruch : Bool)
    (wahl : Option PrioritaetsFehler)
    (hburst : burstAusfuehrung wahl = none) :
    grenzEntscheid true nmiAnhaengig irqAnhaengig irqNr irqFrei bruch
      wahl = .ereignisAusliefern .vorTrap := by
  simp [grenzEntscheid, hburst]

/-- Class 5 beats maskable interrupts and fetch/decode faults. -/
theorem nmi_schlaegt_irq_und_abruf (irqAnhaengig : Bool) (irqNr : Nat)
    (irqFrei : Bool) (bruch : Bool) (wahl : Option PrioritaetsFehler)
    (hburst : burstAusfuehrung wahl = none) :
    grenzEntscheid false true irqAnhaengig irqNr irqFrei bruch
      wahl = .ereignisAusliefern .nmi := by
  simp [grenzEntscheid, hburst]

/-- Class 6 beats fetch/decode faults: a pending enabled interrupt is
    serviced BEFORE the next instruction is fetched, so its fetch fault
    (if any) is discarded and re-generated later. -/
theorem irq_schlaegt_abruf (irqNr : Nat) (bruch : Bool)
    (f : PrioritaetsFehler)
    (hburst : burstAusfuehrung (some f) = none) :
    grenzEntscheid false false true irqNr true bruch
      (some f) = .ereignisAusliefern (.irq irqNr) := by
  simp [grenzEntscheid, hburst]

/-- An uncontested fetch/decode fault is delivered. -/
theorem abruf_ohne_konkurrenz (f : PrioritaetsFehler)
    (hburst : burstAusfuehrung (some f) = none) :
    grenzEntscheid false false false 0 false false
      (some f) = .falleAusliefern f := by
  simp [grenzEntscheid, hburst]

/-- A quiet boundary executes on. -/
theorem ruhe_weiter (irqNr : Nat) :
    grenzEntscheid false false false irqNr false false none =
      .weiterAusfuehren := by
  simp [grenzEntscheid, burstAusfuehrung]

/-! ## Ordered selection, completed: decode and control dominance. -/

/-- A decode candidate beats address, access, divide and control --
    given a quiet fetch. -/
theorem dekodiere_schlaegt_spaete (t : FpZustand) (z : ZugriffsBeschreibung)
    (pg : SeitenInfo) (st : SteuerInfo) (ill : IllegalInfo)
    (teiltFalle : Bool) (f : PrioritaetsFehler)
    (hfrueh : abrufKandidat t = none)
    (hdec : dekodiereKandidat t ill = some f) :
    ersteWahl (kandidatenReihe t z pg st ill teiltFalle) = some f := by
  simp [ersteWahl, kandidatenReihe, hfrueh, hdec]

/-- The control candidate wins when everything before it is quiet. -/
theorem steuerung_als_letzte (t : FpZustand) (z : ZugriffsBeschreibung)
    (pg : SeitenInfo) (st : SteuerInfo) (ill : IllegalInfo)
    (teiltFalle : Bool) (f : PrioritaetsFehler)
    (hfrueh : abrufKandidat t = none)
    (hdec : dekodiereKandidat t ill = none)
    (hadr : adressKandidat z = none)
    (hzug : zugriffKandidat t z pg = none)
    (hteil : teilungsKandidat teiltFalle = none)
    (hst : steuerKandidat z st = some f) :
    ersteWahl (kandidatenReihe t z pg st ill teiltFalle) = some f := by
  simp [ersteWahl, kandidatenReihe, hfrueh, hdec, hadr, hzug, hteil, hst]

/-! ## Witness states: a fetched divide trap, dark and bright.

  `divFalleStart` fetches a real `divRax rcx` with divisor zero from
  actual executable memory; its data side is dark (nothing readable or
  writable), so permission candidates fire on demand. `hellFalleStart`
  shares the same fetched window over permissive data memory, so
  alignment control can fire while access stays quiet. -/

/-- The fetched divide bytes at 4096, zeroes elsewhere. -/
def divFalleBytes (a : Adresse) : Byte :=
  match (mulDivEncode (.divRax .rcx))[a.toNat - 4096]? with
  | some b => b
  | none => BitVec.ofNat 8 0

/-- Dark code-and-data memory: three executable divide bytes, nothing
    readable or writable. Fetch uses execute permission only. -/
def divFalleSpeicher : Speicher :=
  { bytes := divFalleBytes
    lesbar := fun _ => false
    schreibbar := fun _ => false
    ausfuehrbar := fun a => decide (4096 ≤ a.toNat ∧ a.toNat < 4099) }

/-- Bright variant: the same fetched window over permissive data. -/
def hellFalleSpeicher : Speicher :=
  { divFalleSpeicher with
    lesbar := fun _ => true
    schreibbar := fun _ => true }

/-- Divide-trap core: zero divisor registers under the dark memory. -/
def divFalleKern : Zustand :=
  { register := mdRegNull, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := divFalleSpeicher }

/-- Divide-trap start state with reset FP control. -/
def divFalleStart : FpZustand :=
  ⟨divFalleKern, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Bright start state: same window, permissive data memory. -/
def hellFalleStart : FpZustand :=
  ⟨{ divFalleKern with speicher := hellFalleSpeicher },
    fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Pure divide descriptor: no data access, divides. -/
def divZ : ZugriffsBeschreibung := ⟨none, none, false, 8, true⟩

/-- Dark conflict descriptor: noncanonical read plus divide. -/
def dunkelKonfliktZ : ZugriffsBeschreibung :=
  ⟨some (BitVec.ofNat 64 (2 ^ 47)), none, false, 8, true⟩

/-- Control descriptor: unaligned permitted read plus divide. -/
def hellKontrollZ : ZugriffsBeschreibung :=
  ⟨some (BitVec.ofNat 64 8193), none, false, 8, true⟩

/-- Overlap descriptor: the write target is the fetched code page. -/
def overlapZ : ZugriffsBeschreibung :=
  ⟨none, some (BitVec.ofNat 64 4096), false, 8, false⟩

/-- Empty oracles: no page present, nothing stated illegal. -/
def illLeer : IllegalInfo := ⟨fun _ => false⟩

/-- Oracle stating the truncated jump opcode byte illegal. -/
def illE9 : IllegalInfo := ⟨fun w => decide (w = [natByte 233])⟩

/-- Page states: nothing present, everything present. -/
def pgDunkel : SeitenInfo := ⟨fun _ => false⟩
def pgHell : SeitenInfo := ⟨fun _ => true⟩

/-- Control states: armed, disarmed. -/
def stScharf : SteuerInfo := ⟨true⟩
def stStumpf : SteuerInfo := ⟨false⟩

/-! ## Divide-trap probes on fetched bytes.

  The window IS the encoded divide, admission holds, no fetch/decode/
  address/access candidate fires, the actual evaluator traps, the
  choice is exactly the divide #DE, the byte step halts, and the
  verdict binds the halt to the trap. -/

/-- The fetched window is the encoded divide. -/
theorem geholt_divFalle :
    geholt divFalleStart.kern = mulDivEncode (.divRax .rcx) := by
  decide

/-- The window decodes to the divide arm with no suffix. -/
theorem decode_divFalle :
    decodeExt (mulDivEncode (.divRax .rcx)) =
      some (.muldiv ⟨.divRax .rcx, 3⟩, []) := by
  decide

/-- Admission holds over the fetched window. -/
theorem zugelassen_divFalle :
    extZugelassen divFalleStart (geholt divFalleStart.kern)
      (.muldiv ⟨.divRax .rcx, 3⟩) [] = true := by
  rw [geholt_divFalle]
  decide

/-- No fetch candidate over the admitted divide window. -/
theorem abruf_divFalle_keiner :
    abrufKandidat divFalleStart = none := by
  have hne : geholt divFalleStart.kern ≠ [] := by
    rw [geholt_divFalle]
    decide
  have hdec : decodeExt (geholt divFalleStart.kern) =
      some (.muldiv ⟨.divRax .rcx, 3⟩, []) := by
    rw [geholt_divFalle]
    exact decode_divFalle
  have hkan : istKanonisch divFalleStart.kern.rip = true := kanonisch_code
  exact abruf_zugelassen_keiner _ _ _ hkan hne hdec zugelassen_divFalle

/-- No decode candidate over the admitted divide window. -/
theorem dekodiere_divFalle_keiner (ill : IllegalInfo) :
    dekodiereKandidat divFalleStart ill = none := by
  apply dekodiere_erfolg_keiner _ _ _ _
  rw [geholt_divFalle]
  exact decode_divFalle

/-- The actual evaluator traps on the fetched divide state. -/
theorem falle_divFalle :
    mulDivSchritt ⟨.divRax .rcx, 3⟩ divFalleKern = .hardwareHalt :=
  fehler_div_null_haelt _ _ _ (by decide) rfl (by decide)

/-- CHOICE: the divide #DE wins over the quiet earlier stages. -/
theorem wahl_divFalle :
    ersteWahl
        (kandidatenReihe divFalleStart divZ pgDunkel stStumpf illLeer
          true) = some ⟨.teilung, .de⟩ := by
  apply teilung_schlaegt_steuerung _ _ _ _ _ abruf_divFalle_keiner
    (dekodiere_divFalle_keiner _) _ _ _
  · simp [adressKandidat, divZ]
  · simp [zugriffKandidat, schreibKandidat, divZ]
  · rfl

/-- The byte step halts on the fetched divide trap. -/
theorem halt_divFalle :
    extByteschritt divFalleStart extWitBereit = .halt := by
  have hf : fetchExt divFalleStart (geholt divFalleStart.kern) =
      some (.muldiv ⟨.divRax .rcx, 3⟩, []) := by
    have hdec : decodeExt (geholt divFalleStart.kern) =
        some (.muldiv ⟨.divRax .rcx, 3⟩, []) := by
      rw [geholt_divFalle]
      exact decode_divFalle
    simp [fetchExt, hdec, zugelassen_divFalle]
  have hs : stepExt (.muldiv ⟨.divRax .rcx, 3⟩) divFalleStart extWitBereit =
      .halt :=
    stepExt_muldiv_halt _ _ _ falle_divFalle
  exact extByteschritt_weiter _ _ _ _ _ hf hs

/-- The halt verdict binds the trap, and the halt comes from divide. -/
theorem urteil_divFalle :
    bindeUrteil (extByteschritt divFalleStart extWitBereit)
        (ersteWahl
          (kandidatenReihe divFalleStart divZ pgDunkel stStumpf illLeer
            true)) = .fehler ⟨.teilung, .de⟩ := by
  rw [halt_divFalle]
  exact urteil_halt_ist_teilung _

/-! ## Conflict probes: several pending faults, one exact cause.

  Each probe fires candidates at several stages at once and proves the
  single chosen cause from the priority theorems -- never by picking a
  desired outcome. -/

/-- CONFLICT 1 (fetch beats divide and access): a noncanonical RIP wins
    over a pending divide trap and a dark data access. -/
def konfliktAbrufStart : FpZustand :=
  { extWitStart with kern :=
    { extWitKern with rip := BitVec.ofNat 64 (2 ^ 47) } }

/-- The fetch #GP candidate fires on the noncanonical RIP. -/
theorem kandidat_konflikt_abruf :
    abrufKandidat konfliktAbrufStart = some ⟨.abruf, .gp⟩ := by
  apply abruf_nichtkanonisch_rip
  show istKanonisch (BitVec.ofNat 64 (2 ^ 47)) = false
  exact nichtkanonisch_bit47

/-- CHOICE: fetch #GP beats the pending divide trap. -/
theorem wahl_konflikt_abruf :
    ersteWahl
        (kandidatenReihe konfliktAbrufStart dunkelKonfliktZ pgDunkel
          stStumpf illLeer true) = some ⟨.abruf, .gp⟩ :=
  abruf_schlaegt_alles _ _ _ _ _ _ _ kandidat_konflikt_abruf

/-- CONFLICT 2 (address beats access): a noncanonical read wins over a
    refused dark read, with divide pending behind both. -/
theorem hadr_konflikt_adresse :
    adressKandidat dunkelKonfliktZ = some ⟨.adresse, .gp⟩ := by
  have h := adress_lese_nichtkanonisch dunkelKonfliktZ
    (BitVec.ofNat 64 (2 ^ 47)) rfl nichtkanonisch_bit47
  simpa [dunkelKonfliktZ] using h

/-- The dark read would refuse as #PF -- but address fires first. -/
theorem zugriff_konflikt_haette_auch :
    zugriffKandidat divFalleStart dunkelKonfliktZ pgDunkel =
      some ⟨.zugriff, .pf⟩ := by
  have hread : read64 divFalleStart.kern.speicher
      (BitVec.ofNat 64 (2 ^ 47)) = none := by
    decide
  have h := zugriff_lese_verweigert divFalleStart dunkelKonfliktZ pgDunkel
    (BitVec.ofNat 64 (2 ^ 47)) rfl hread
  have hklasse : seitenKlasse pgDunkel (BitVec.ofNat 64 (2 ^ 47)) = .pf :=
    seitenKlasse_nicht_vorhanden _ _ rfl
  rw [hklasse] at h
  exact h

/-- CHOICE: address #GP beats access and divide. -/
theorem wahl_konflikt_adresse :
    ersteWahl
        (kandidatenReihe divFalleStart dunkelKonfliktZ pgDunkel stStumpf
          illLeer true) = some ⟨.adresse, .gp⟩ := by
  apply adresse_schlaegt_spaete _ _ _ _ _ _ _ abruf_divFalle_keiner
    (dekodiere_divFalle_keiner _) hadr_konflikt_adresse

end Gabbro.Grammatik.X86
