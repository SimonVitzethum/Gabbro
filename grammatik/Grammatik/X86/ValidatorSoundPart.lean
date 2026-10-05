/-
  Validator soundness for the decidable part (lane 1223).

  Packages exactly what `valX86` decides (`ValidatorSkeleton.valX86`:
  checked mapping AND whole-section decode coverage from each section
  base): mapping and coverage projections, per-section full decode,
  loaded-byte agreement through the accepted `geladen` construction,
  and the coherent-machine fetch identity (`HwLoadedImage`). This is
  NOT source refinement; the full closing theorem stays OPEN (CUTS).
-/
import Grammatik.X86.ValidatorExecution
import Grammatik.X86.ValidationBudget
import Grammatik.X86.HwLoadedImage

namespace Gabbro.Grammatik.X86

/-- SOUNDNESS, mapping leg: admission implies the checked mapping.
    Reuses `valX86_wohlgeformt`; no claim beyond the decided Bool. -/
theorem valSound_mapping (p : Profil) (bild : Bild)
    (h : valX86 p bild = true) :
    wohlgeformt p bild = true :=
  valX86_wohlgeformt p bild h

/-- SOUNDNESS, coverage leg: admission implies whole-image decode
    coverage. Reuses `valX86_deckung`; coverage starts at each
    section base (interior entries are a pinned gap, see CUTS). -/
theorem valSound_deckung (p : Profil) (bild : Bild)
    (h : valX86 p bild = true) :
    bildDeckung bild = true :=
  valX86_deckung p bild h

/-- SOUNDNESS, per-section leg: admission covers EVERY member section
    (executable sections decode fully, data sections carry `true`).
    Derived from the coverage projection through the same `all` the
    definition uses; no second register. -/
theorem valSound_abschnitt (p : Profil) (bild : Bild) (s : Abschnitt)
    (hmem : s ∈ bild.abschnitte) (h : valX86 p bild = true) :
    abschnittDeckung bild s = true := by
  have hd := valSound_deckung p bild h
  unfold bildDeckung at hd
  exact (List.all_eq_true.mp hd) s hmem

/-- SOUNDNESS, no-stray-bytes leg: every executable member section
    fully decodes from its base under fuel `dateiLen + 1` (one byte
    per instruction plus the empty program). This is whole-section
    decode from the base only; interior offsets are a pinned gap. -/
theorem valSound_exec_vollex (p : Profil) (bild : Bild) (s : Abschnitt)
    (hmem : s ∈ bild.abschnitte) (hexe : s.ausfuehrbar = true)
    (h : valX86 p bild = true) :
    validAllFuel (s.dateiLen + 1) (abschnittBytes bild s) = true := by
  have ha := valSound_abschnitt p bild s hmem h
  unfold abschnittDeckung at ha
  simp only [hexe, if_true] at ha
  exact ha

/-- SOUNDNESS, traversal leg (generic): full validation means the
    fuel traversal succeeds with no remainder. Timeout (`none`) and
    leftover bytes never validate; the proof inverts the `validAllFuel`
    match, so every premise shapes the conclusion. -/
theorem validAllFuel_gibt_traversierung (fuel : Nat) (bs : List Byte)
    (h : validAllFuel fuel bs = true) :
    ∃ ins, decodeFuel fuel bs = some (ins, []) := by
  unfold validAllFuel at h
  generalize hg : decodeFuel fuel bs = g at h ⊢
  cases g with
  | none =>
    simp at h
  | some pr =>
    obtain ⟨ins, rest⟩ := pr
    cases rest with
    | nil =>
      exact ⟨ins, rfl⟩
    | cons _ _ =>
      simp at h

/-- SOUNDNESS, traversal leg (applied): every executable member
    section of an admitted image traverses with no remainder. -/
theorem valSound_exec_traversierung (p : Profil) (bild : Bild)
    (s : Abschnitt) (hmem : s ∈ bild.abschnitte)
    (hexe : s.ausfuehrbar = true) (h : valX86 p bild = true) :
    ∃ ins, decodeFuel (s.dateiLen + 1) (abschnittBytes bild s) =
      some (ins, []) :=
  validAllFuel_gibt_traversierung _ _
    (valSound_exec_vollex p bild s hmem hexe h)

/-- SOUNDNESS, W^X leg: no member section of an admitted image is
    writable and executable at once. Inversion of the checked mapping
    through the member hypothesis; the mapping premise is discharged
    from the validator premise, never assumed. -/
theorem valSound_wx (p : Profil) (bild : Bild) (s : Abschnitt)
    (hmem : s ∈ bild.abschnitte) (h : valX86 p bild = true) :
    wxOk s = true :=
  wohlgeformt_wx p bild s hmem (valSound_mapping p bild h)

/-- SOUNDNESS, size leg: every member section of an admitted image
    carries a non-negative BSS tail (`dateiLen <= memLen`). -/
theorem valSound_groesse (p : Profil) (bild : Bild) (s : Abschnitt)
    (hmem : s ∈ bild.abschnitte) (h : valX86 p bild = true) :
    groesseOk s = true :=
  wohlgeformt_groesse p bild s hmem (valSound_mapping p bild h)

/-- SOUNDNESS, file-containment leg: every member section of an
    admitted image lies inside the file bytes. -/
theorem valSound_datei (p : Profil) (bild : Bild) (s : Abschnitt)
    (hmem : s ∈ bild.abschnitte) (h : valX86 p bild = true) :
    s.dateiOff + s.dateiLen ≤ bild.datei.length :=
  wohlgeformt_datei p bild s hmem (valSound_mapping p bild h)

/-- SOUNDNESS, loaded-byte agreement: inside the file-backed part of
    a member section of an admitted image, the loaded byte IS the
    mapped file byte, and the mapped index lies inside the file. The
    equality reuses the accepted `geladenByte_datei`; the index bound
    discharges the file containment from the validator premise, so
    every premise is used. -/
theorem valSound_lade_datei (p : Profil) (bild : Bild) (s : Abschnitt)
    (hmem : s ∈ bild.abschnitte) (h : valX86 p bild = true)
    (bias a : Nat)
    (hfind : abteilFinden bild.abschnitte bias a = some s)
    (hlo : bias + s.vaddr ≤ a)
    (hhi : a < bias + s.vaddr + s.dateiLen) :
    ladenByte bild bias a =
      dateiByte bild.datei (s.dateiOff + (a - (bias + s.vaddr))) ∧
      s.dateiOff + (a - (bias + s.vaddr)) < bild.datei.length := by
  refine ⟨geladenByte_datei bild bias a s hfind hhi, ?_⟩
  have hfile := valSound_datei p bild s hmem h
  omega

/-- SOUNDNESS, BSS-zero leg: past the file-backed part but inside the
    found section, the loaded byte is defined zero. Reuses the
    accepted construction; both premises shape the conclusion. -/
theorem valSound_lade_bss (bild : Bild) (bias a : Nat) (s : Abschnitt)
    (hfind : abteilFinden bild.abschnitte bias a = some s)
    (hlo : bias + s.vaddr + s.dateiLen ≤ a) :
    ladenByte bild bias a = BitVec.ofNat 8 0 :=
  geladenByte_bss bild bias a s hfind hlo

/-- SOUNDNESS, outside-domain leg: outside every section the loaded
    byte is zero and nothing is readable, writable or executable.
    Reuses the accepted outside frame; the single premise is the
    conclusion's condition. -/
theorem valSound_ausserhalb (bild : Bild) (bias a : Nat)
    (hfind : abteilFinden bild.abschnitte bias a = none) :
    ladenByte bild bias a = BitVec.ofNat 8 0 ∧
    ladenLesbar bild bias a = false ∧
    ladenSchreibbar bild bias a = false ∧
    ladenAusfuehrbar bild bias a = false :=
  ausserhalb_rahmen bild bias a hfind

/-- SOUNDNESS, permission-agreement leg: the loaded execute
    permission at an address is exactly its section's flag. The
    mapping is permission-correct by construction; this reuses the
    accepted agreement, with the lookup as the single premise. -/
theorem valSound_perm_exec (bild : Bild) (bias a : Nat) (s : Abschnitt)
    (hfind : abteilFinden bild.abschnitte bias a = some s) :
    ladenAusfuehrbar bild bias a = s.ausfuehrbar :=
  geladenAusfuehrbar_fund bild bias a s hfind

/-- SOUNDNESS, W^X consequence: an executable member section of an
    admitted image is not writable. Membership and validator premises
    flow through the W^X leg; the executability premise selects the
    refused shape in the case split. -/
theorem valSound_wx_kein_schreiben (p : Profil) (bild : Bild)
    (s : Abschnitt) (hmem : s ∈ bild.abschnitte)
    (hexe : s.ausfuehrbar = true) (h : valX86 p bild = true) :
    s.schreibbar = false := by
  have hwx := valSound_wx p bild s hmem h
  unfold wxOk at hwx
  cases hsb : s.schreibbar with
  | true =>
    simp [hsb, hexe] at hwx
  | false =>
    rfl

/-- SOUNDNESS, coherent-fetch leg: under memory coincidence (the
    machine runs on the canonically loaded image) and core/fetch-input
    agreement, the core projection fetches exactly what the loaded
    image state fetches. Reuses the accepted `HwLoadedImage` identity
    unchanged; coincidence stays an explicit premise, never derived
    from `valX86` alone. -/
theorem valSound_hw_fetch_gleich (m : HwMaschine) (c : Nat) (bild : Bild)
    (bias : Nat) (rip : Adresse) (reg : Register → Wort) (fl : Flags)
    (hmem : m.mem = geladen bild bias)
    (hrip : (m.kerne c).rip = rip)
    (hreg : (m.kerne c).register = reg)
    (hfl : (m.kerne c).flags = fl) :
    fetchDekodiert (projZustand m c) =
      fetchDekodiert (bildZustand bild bias rip reg fl) :=
  hwBild_fetchDekodiert_gleich m c bild bias rip reg fl hmem hrip hreg hfl

/-- SOUNDNESS, coherent-step leg: under the same coincidence and
    core agreement, the core projection takes exactly the loaded
    image's byte step. Reuses the accepted `HwLoadedImage` identity;
    coincidence stays a premise, never a validator conclusion. -/
theorem valSound_hw_schritt_gleich (m : HwMaschine) (c : Nat) (bild : Bild)
    (bias : Nat) (rip : Adresse) (reg : Register → Wort) (fl : Flags)
    (hmem : m.mem = geladen bild bias)
    (hrip : (m.kerne c).rip = rip)
    (hreg : (m.kerne c).register = reg)
    (hfl : (m.kerne c).flags = fl) :
    byteschritt (projZustand m c) =
      byteschritt (bildZustand bild bias rip reg fl) :=
  hwBild_byteschritt_gleich m c bild bias rip reg fl hmem hrip hreg hfl

/-- SOUNDNESS, entry-at-decoded-start leg: the strengthened entry
    check (mapping AND containment AND execute byte AND successful
    fetch from actual loaded bytes) yields the fetched covered pilot
    form at its exact length with executable prefix. This packages
    the accepted `valStark_gibt_deckung` as the soundness half the
    plain `valX86` Bool does NOT supply (interior entries stay a
    pinned gap below). The single premise is threaded through. -/
theorem valSound_stark_gibt_deckung (p : Profil) (bild : Bild)
    (bias e : Nat) (reg : Register → Wort) (fl : Flags)
    (h : valEintrittStark p bild bias e reg fl = true) :
    eintragEnthalten bias bild.abschnitte e = true ∧
    ladenAusfuehrbar bild bias e = true ∧
    ∃ (d : Decodiert) (rest : List Byte),
      fetchDekodiert (bildZustand bild bias (BitVec.ofNat 64 e) reg fl) =
        some (d, rest) ∧
      decktAb d ∧
      d.laenge + rest.length =
        (geholt (bildZustand bild bias (BitVec.ofNat 64 e) reg fl)).length ∧
      laengeOk d.laenge = true ∧
      ausfuehrbarN (bildZustand bild bias (BitVec.ofNat 64 e) reg fl).speicher
        (bildZustand bild bias (BitVec.ofNat 64 e) reg fl).rip d.laenge =
        true :=
  valStark_gibt_deckung p bild bias e reg fl h

/-- SOUNDNESS, entry-at-decoded-start leg: the strengthened entry
    check (mapping AND containment AND execute byte AND successful
    fetch from actual loaded bytes) yields the fetched covered pilot
    form at its exact length with executable prefix. This packages
    the accepted `valStark_gibt_deckung` as the soundness half that
    the plain `valX86` Bool does NOT supply (interior entries stay a
    pinned gap below). The single premise is threaded through. -/
theorem valSound_stark_gibt_deckung (p : Profil) (bild : Bild)
    (bias e : Nat) (reg : Register → Wort) (fl : Flags)
    (h : valEintrittStark p bild bias e reg fl = true) :
    eintragEnthalten bias bild.abschnitte e = true ∧
    ladenAusfuehrbar bild bias e = true ∧
    ∃ (d : Decodiert) (rest : List Byte),
      fetchDekodiert (bildZustand bild bias (BitVec.ofNat 64 e) reg fl) =
        some (d, rest) ∧
      decktAb d ∧
      d.laenge + rest.length =
        (geholt (bildZustand bild bias (BitVec.ofNat 64 e) reg fl)).length ∧
      laengeOk d.laenge = true ∧
      ausfuehrbarN (bildZustand bild bias (BitVec.ofNat 64 e) reg fl).speicher
        (bildZustand bild bias (BitVec.ofNat 64 e) reg fl).rip d.laenge =
        true :=
  valStark_gibt_deckung p bild bias e reg fl h

/- CUTS (partial; extended with each added leg):
    Proved here: mapping and coverage projections of `valX86`,
    per-section coverage, whole-section full decode from the base,
    and its no-remainder traversal inversion.
    OPEN (never a premise here): `valX86_sound_full`: no claim that
    an admitted image is the emitted form of any source program, or
    refines any contract, duty, cost, lock or budget; no hardware
    claim (silicon, caches, TLBs, store buffers, interrupts, faults,
    timing); no multi-step control-flow or TSO/GX bridge claim.
-/

#print axioms valSound_mapping
#print axioms valSound_deckung
#print axioms valSound_abschnitt
#print axioms valSound_exec_vollex
#print axioms valSound_wx
#print axioms valSound_groesse
#print axioms valSound_datei
#print axioms valSound_lade_datei
#print axioms valSound_lade_bss
#print axioms valSound_ausserhalb
#print axioms valSound_perm_exec
#print axioms valSound_wx_kein_schreiben
#print axioms valSound_hw_fetch_gleich
#print axioms valSound_hw_schritt_gleich
#print axioms validAllFuel_gibt_traversierung
#print axioms valSound_exec_traversierung

end Gabbro.Grammatik.X86
