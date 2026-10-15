/-
  Composition closing: nolibc entry hooks to proved entry admission
  (lane 853).

  Producer/consumer interface closed here: the producers are the accepted
  entry admission (`EntryExecution.eintrittZulassung`: checked `Bild`
  mapping AND `EntryState.eintrittOk` AND admitted caller gates) with its
  executed consequences (`zulassung_rip_ausfuehrbar`, `zulassung_stapel_rw`,
  `zulassung_erster_schritt` through `Byteschritt.byteschritt`), and the
  consumer is the nolibc entry-hook handshake (`NolibcHaken`: the
  `os_anfang` handoff done AND the `os_ende` hook present, with the
  returned main status handed to `os_ende` unchanged). This file only
  composes already-accepted theorems; it re-proves no mapping, entry,
  gate, fetch or step fact and defines no second loader, decoder,
  executor or ISA model.
-/
import Grammatik.X86.EntryExecution

namespace Gabbro.Grammatik.X86

/-- Nolibc entry hooks as validator findings: the `os_anfang` handoff was
    done before `main` runs, and the `os_ende` hook is present to take the
    returned status. Both are `Bool` findings, never behaviour claims. -/
structure NolibcHaken where
  anfang : Bool
  ende : Bool
  deriving DecidableEq, Repr

/-- Both hooks present: `anfang` handoff done AND `ende` present. A
    missing hook refuses, whatever the image and entry state are. -/
def hakenOk (h : NolibcHaken) : Bool :=
  h.anfang && h.ende

/-- Status handoff: the value handed to `os_ende` equals the returned main
    status. A changed status refuses. -/
def statusHalt (code rueck : Nat) : Bool :=
  decide (rueck = code)

/-- The one checked closing step: joint entry admission AND both hooks
    AND the unchanged status handoff. `code` is the returned main status,
    `rueck` the value handed to `os_ende`. -/
def eintrittHakenZulassung (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (h : NolibcHaken) (code rueck : Nat) : Bool :=
  eintrittZulassung p bild bias art z tore && hakenOk h &&
    statusHalt code rueck

/- CUTS:
   Proved here: the closing vocabulary (`NolibcHaken`, `hakenOk`,
   `statusHalt`, `eintrittHakenZulassung`), its projections onto the
   accepted joint admission, the hooks and the status handoff, the
   checked-mapping consequences (executable RIP through the loaded
   mapping, entry stack window), the fetched-first-instruction step
   (execution, not a conjunction of checks), and planted refusals for
   every missing leg (no `anfang`, no `ende`, changed status, unlisted
   RIP, refused gate).
   NOT proved here, and not claimed:
   - No hook-behaviour claim: `anfang`/`ende` are validator findings as
     `Bool`, not proved call sequences; OS/binding behaviour stays user
     logic, never an assumption.
   - No source correspondence, no hardware correspondence, no TSO/GX
     bridge, no cost/budget transfer, no multi-step control-flow claim.
   - Missing producer legs are explicit CUTS with the owning lane named,
     never assumed: source-to-entry lowering and the shared IR (lane 287),
     asynchronous interrupt behaviour after handoff (interrupt-leg owner).
-/

/-- Admission implies the accepted joint entry admission. -/
theorem hakenZulassung_eintrittZulassung (p : Profil) (bild : Bild)
    (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl) (h : NolibcHaken) (code rueck : Nat)
    (hadm : eintrittHakenZulassung p bild bias art z tore h code rueck
      = true) :
    eintrittZulassung p bild bias art z tore = true := by
  unfold eintrittHakenZulassung at hadm
  simp only [Bool.and_eq_true_iff] at hadm
  exact hadm.1.1

/-- Admission implies both hooks are present. -/
theorem hakenZulassung_haken (p : Profil) (bild : Bild)
    (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl) (h : NolibcHaken) (code rueck : Nat)
    (hadm : eintrittHakenZulassung p bild bias art z tore h code rueck
      = true) :
    hakenOk h = true := by
  unfold eintrittHakenZulassung at hadm
  simp only [Bool.and_eq_true_iff] at hadm
  exact hadm.1.2

/-- Admission implies the handed status equals the returned one. -/
theorem hakenZulassung_status (p : Profil) (bild : Bild)
    (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl) (h : NolibcHaken) (code rueck : Nat)
    (hadm : eintrittHakenZulassung p bild bias art z tore h code rueck
      = true) :
    rueck = code := by
  unfold eintrittHakenZulassung at hadm
  simp only [Bool.and_eq_true_iff] at hadm
  unfold statusHalt at hadm
  exact of_decide_eq_true hadm.2

/-- Admission implies the proved entry predicate. -/
theorem hakenZulassung_eintritt (p : Profil) (bild : Bild)
    (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl) (h : NolibcHaken) (code rueck : Nat)
    (hadm : eintrittHakenZulassung p bild bias art z tore h code rueck
      = true) :
    eintrittOk p bild bias art z = true :=
  zulassung_eintritt p bild bias art z tore
    (hakenZulassung_eintrittZulassung p bild bias art z tore h code rueck
      hadm)

/-- Admission makes the RIP executable through the CHECKED loaded mapping. -/
theorem hakenZulassung_rip_ausfuehrbar (p : Profil) (bild : Bild)
    (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl) (h : NolibcHaken) (code rueck : Nat)
    (hadm : eintrittHakenZulassung p bild bias art z tore h code rueck
      = true) :
    (geladen bild bias).ausfuehrbar z.zustand.rip = true :=
  zulassung_rip_ausfuehrbar p bild bias art z tore
    (hakenZulassung_eintrittZulassung p bild bias art z tore h code rueck
      hadm)

/-- Admission makes the entry stack window readable and writable. -/
theorem hakenZulassung_stapel_rw (p : Profil) (bild : Bild)
    (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl) (h : NolibcHaken) (code rueck : Nat)
    (hadm : eintrittHakenZulassung p bild bias art z tore h code rueck
      = true) :
    lesbar8 z.zustand.speicher
        (eintrittRsp z - BitVec.ofNat 64 8) = true ∧
      schreibbar8 z.zustand.speicher
        (eintrittRsp z - BitVec.ofNat 64 8) = true :=
  zulassung_stapel_rw p bild bias art z tore
    (hakenZulassung_eintrittZulassung p bild bias art z tore h code rueck
      hadm)

/-- FIRST INSTRUCTION: from admission, the fetched instruction runs as a
    real byte step, and the RIP is executable through the checked loaded
    mapping. Reuses `zulassung_erster_schritt`; no second fetch. -/
theorem hakenZulassung_erster_schritt (p : Profil) (bild : Bild)
    (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl) (h : NolibcHaken) (code rueck : Nat)
    (d : Decodiert) (rest : List Byte) (s' : Zustand)
    (hadm : eintrittHakenZulassung p bild bias art z tore h code rueck
      = true)
    (hf : fetchDekodiert z.zustand = some (d, rest))
    (hs : schritt d z.zustand = some s') :
    (geladen bild bias).ausfuehrbar z.zustand.rip = true ∧
      byteschritt z.zustand = .weiter s' :=
  zulassung_erster_schritt p bild bias art z tore d rest s'
    (hakenZulassung_eintrittZulassung p bild bias art z tore h code rueck
      hadm) hf hs

/-- REFUSAL: without the `anfang` handoff nothing is admitted. -/
theorem hakenZulassung_verweigert_ohne_anfang (p : Profil) (bild : Bild)
    (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl) (h : NolibcHaken) (code rueck : Nat)
    (hanf : h.anfang = false) :
    eintrittHakenZulassung p bild bias art z tore h code rueck
      = false := by
  have hh : hakenOk h = false := by
    unfold hakenOk
    rw [hanf]
    simp
  unfold eintrittHakenZulassung
  rw [hh]
  simp

/-- REFUSAL: without the `ende` hook nothing is admitted. -/
theorem hakenZulassung_verweigert_ohne_ende (p : Profil) (bild : Bild)
    (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl) (h : NolibcHaken) (code rueck : Nat)
    (hende : h.ende = false) :
    eintrittHakenZulassung p bild bias art z tore h code rueck
      = false := by
  have hh : hakenOk h = false := by
    unfold hakenOk
    rw [hende]
    simp
  unfold eintrittHakenZulassung
  rw [hh]
  simp

/-- REFUSAL: a handed status that differs from the returned one admits
    nothing. Uses the mismatch. -/
theorem hakenZulassung_verweigert_status (p : Profil) (bild : Bild)
    (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl) (h : NolibcHaken) (code rueck : Nat)
    (hmis : rueck ≠ code) :
    eintrittHakenZulassung p bild bias art z tore h code rueck
      = false := by
  have hs : statusHalt code rueck = false := by
    unfold statusHalt
    rw [decide_eq_false hmis]
  unfold eintrittHakenZulassung
  rw [hs]
  simp

/-- REFUSAL: an unlisted RIP admits no hooked entry. -/
theorem hakenZulassung_verweigert_unlisted (p : Profil) (bild : Bild)
    (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl) (h : NolibcHaken) (code rueck : Nat)
    (hrip : eintragGelisted bild z.zustand.rip.toNat = false) :
    eintrittHakenZulassung p bild bias art z tore h code rueck
      = false := by
  unfold eintrittHakenZulassung
  rw [zulassung_verweigert_unlisted p bild bias art z tore hrip]
  simp

/-- REFUSAL: a gate list with a refused member admits no hooked entry. -/
theorem hakenZulassung_verweigert_tor (p : Profil) (bild : Bild)
    (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl) (h : NolibcHaken) (code rueck : Nat)
    (t : TorDekl) (hmem : t ∈ tore) (href : torOkB t = false) :
    eintrittHakenZulassung p bild bias art z tore h code rueck
      = false := by
  unfold eintrittHakenZulassung
  rw [zulassung_verweigert_tor p bild bias art z tore t hmem href]
  simp

/-- ENTRY-HOOK CLOSING, generic over arbitrary admitted inputs: a hooked
    admission carries the accepted joint entry admission, both hooks, the
    unchanged status handoff, the executable RIP through the CHECKED
    loaded mapping, and the readable/writable entry stack window.
    Composes the accepted producer lemmas by name; no producer fact is
    re-proved here. -/
theorem ComposeEntryHooks_verbindung (p : Profil) (bild : Bild)
    (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl) (h : NolibcHaken) (code rueck : Nat)
    (hadm : eintrittHakenZulassung p bild bias art z tore h code rueck
      = true) :
    eintrittZulassung p bild bias art z tore = true ∧
      hakenOk h = true ∧ rueck = code ∧
      (geladen bild bias).ausfuehrbar z.zustand.rip = true ∧
      lesbar8 z.zustand.speicher
        (eintrittRsp z - BitVec.ofNat 64 8) = true ∧
      schreibbar8 z.zustand.speicher
        (eintrittRsp z - BitVec.ofNat 64 8) = true := by
  have hzul := hakenZulassung_eintrittZulassung p bild bias art z tore h
    code rueck hadm
  have hh := hakenZulassung_haken p bild bias art z tore h code rueck hadm
  have hs := hakenZulassung_status p bild bias art z tore h code rueck hadm
  have hrip := hakenZulassung_rip_ausfuehrbar p bild bias art z tore h
    code rueck hadm
  have hrw := hakenZulassung_stapel_rw p bild bias art z tore h code rueck
    hadm
  exact ⟨hzul, hh, hs, hrip, hrw.1, hrw.2⟩

/-- Witness hooks: `anfang` handoff done, `ende` present. -/
def zeugenHaken : NolibcHaken :=
  { anfang := true, ende := true }

/-- ACCEPTANCE: the nolibc entry with both hooks and the unchanged zero
    status is admitted on the minimal image. -/
theorem haken_zeuge_nolibc_ok :
    eintrittHakenZulassung .p48 valZeuge 0 .nolibcMain zeugenEintrittAusf
      [schreibTor] zeugenHaken 0 0 = true := by
  decide

/-- PLANTED REFUSAL: the same entry without the `anfang` handoff admits
    nothing, although image, entry state, gate and status are unchanged. -/
theorem haken_zeuge_ohne_anfang :
    eintrittHakenZulassung .p48 valZeuge 0 .nolibcMain zeugenEintrittAusf
      [schreibTor] { anfang := false, ende := true } 0 0 = false := by
  decide

/-- PLANTED REFUSAL: the same entry without the `ende` hook admits
    nothing, although image, entry state, gate and status are unchanged. -/
theorem haken_zeuge_ohne_ende :
    eintrittHakenZulassung .p48 valZeuge 0 .nolibcMain zeugenEintrittAusf
      [schreibTor] { anfang := true, ende := false } 0 0 = false := by
  decide

/-- PLANTED REFUSAL: a handed status that differs from the returned one
    admits nothing, although hooks, image, entry state and gate hold. -/
theorem haken_zeuge_status_weicht :
    eintrittHakenZulassung .p48 valZeuge 0 .nolibcMain zeugenEintrittAusf
      [schreibTor] zeugenHaken 0 1 = false := by
  decide

/-- PLANTED REFUSAL: the hooked entry moved to an unlisted RIP admits
    nothing, although hooks, image, stack, gate and status hold. -/
theorem haken_zeuge_fremd_verweigert :
    eintrittHakenZulassung .p48 valZeuge 0 .nolibcMain
      { zeugenEintrittAusf with zustand :=
        { zeugenEintrittAusf.zustand with
          rip := BitVec.ofNat 64 0x5000 } } [schreibTor] zeugenHaken 0 0
      = false := by
  decide

/-- PLANTED REFUSAL: the hooked entry with a clobbered-out gate admits
    nothing, although hooks, image, entry state and status hold. -/
theorem haken_zeuge_abi_verweigert :
    eintrittHakenZulassung .p48 valZeuge 0 .nolibcMain zeugenEintrittAusf
      [torAusClobber] zeugenHaken 0 0 = false := by
  decide

/-- JOINT WITNESS for `ComposeEntryHooks_verbindung`: all premises
    jointly instantiated on the admitted nolibc entry (minimal image,
    both hooks, unchanged zero status), with the fetched `ret` and its
    executed step through the composed admission (a reached run from
    checked bytes), a real memory-changing write/read, and planted
    refusals for every missing leg. -/
theorem ComposeEntryHooks_verbindung_zeuge :
    eintrittHakenZulassung .p48 valZeuge 0 .nolibcMain zeugenEintrittAusf
      [schreibTor] zeugenHaken 0 0 = true ∧
    fetchDekodiert zeugenEintrittAusf.zustand = some (⟨.ret, 1⟩, []) ∧
    ausgangRip (byteschritt zeugenEintrittAusf.zustand) =
      some (BitVec.ofNat 64 0) ∧
    (∃ (m m' : Speicher) (a : Adresse) (v : Wort),
      v ≠ 0 ∧ write64 m a v = some m' ∧ read64 m' a = some v ∧
        m.bytes a ≠ m'.bytes a) ∧
    eintrittHakenZulassung .p48 valZeuge 0 .nolibcMain zeugenEintrittAusf
      [schreibTor] { anfang := false, ende := true } 0 0 = false ∧
    eintrittHakenZulassung .p48 valZeuge 0 .nolibcMain zeugenEintrittAusf
      [schreibTor] { anfang := true, ende := false } 0 0 = false ∧
    eintrittHakenZulassung .p48 valZeuge 0 .nolibcMain zeugenEintrittAusf
      [schreibTor] zeugenHaken 0 1 = false ∧
    eintrittHakenZulassung .p48 valZeuge 0 .nolibcMain
      { zeugenEintrittAusf with zustand :=
        { zeugenEintrittAusf.zustand with
          rip := BitVec.ofNat 64 0x5000 } } [schreibTor] zeugenHaken 0 0
      = false ∧
    eintrittHakenZulassung .p48 valZeuge 0 .nolibcMain zeugenEintrittAusf
      [torAusClobber] zeugenHaken 0 0 = false := by
  exact ⟨haken_zeuge_nolibc_ok, zulassung_fetch_ret, zulassung_schritt_ret,
    schreibLese_zeuge, haken_zeuge_ohne_anfang, haken_zeuge_ohne_ende,
    haken_zeuge_status_weicht, haken_zeuge_fremd_verweigert,
    haken_zeuge_abi_verweigert⟩
#print axioms hakenOk
#print axioms statusHalt
#print axioms eintrittHakenZulassung
#print axioms hakenZulassung_eintrittZulassung
#print axioms hakenZulassung_haken
#print axioms hakenZulassung_status
#print axioms hakenZulassung_eintritt
#print axioms hakenZulassung_rip_ausfuehrbar
#print axioms hakenZulassung_stapel_rw
#print axioms hakenZulassung_erster_schritt
#print axioms hakenZulassung_verweigert_ohne_anfang
#print axioms hakenZulassung_verweigert_ohne_ende
#print axioms hakenZulassung_verweigert_status
#print axioms hakenZulassung_verweigert_unlisted
#print axioms hakenZulassung_verweigert_tor
#print axioms ComposeEntryHooks_verbindung
#print axioms haken_zeuge_nolibc_ok
#print axioms haken_zeuge_ohne_anfang
#print axioms haken_zeuge_ohne_ende
#print axioms haken_zeuge_status_weicht
#print axioms haken_zeuge_fremd_verweigert
#print axioms haken_zeuge_abi_verweigert
#print axioms ComposeEntryHooks_verbindung_zeuge

end Gabbro.Grammatik.X86
