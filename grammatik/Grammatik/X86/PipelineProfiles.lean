/-
  File:      Grammatik/X86/PipelineProfiles.lean
  Subject:   Checked hosted/freestanding profiles for the direct pipeline:
              ABI, image layout, entry sequence, support-code bytes and
              bindings for a hosted profile and a freestanding profile.

  Reused, not duplicated:
    - entry hooks: `ComposeEntryHooks.eintrittHakenZulassung`,
      `hakenZulassung_*`, `zeugenHaken`, `haken_zeuge_*`;
    - support bytes: `ComposeSupportBytes.stuetzOk`/`stuetzSchritt`,
      `stuetzOk_teile`, `stuetzSchritt_weiter`/`_verweigert_*`,
      `stuetz_verweigert_*`, `schreibLese_zeuge`;
    - profile selection: `ComposeProfileSelect.composeInstr`,
      `compose_zero`, `compose_bytes_revalidated`;
    - entry sequence: `PipelineEntry.prolog`/`prologPaare`/`prologOk`/
      `prologOk_teile`/`zuege_lauf`/`sysvParameter`;
    - image/loader: `ValidatorSkeleton.valX86`/`valZeuge`/`valWx`,
      `GateStub.schreibTor`/`torAusClobber`/`zeugenMoves`,
      `TableLayout.layoutFuer`/`zeugenU`/`zeugenLayout_ok`,
      `EntryExecution.eintrittZulassung`/`zeugenEintrittAusf`,
      `EntryState.profilEintritt` is new here (OS profile, not CPU `Profil`).
  No second loader, decoder, executor, IR or source interpreter. No
  implicit Linux/POSIX/libc/ELF: environment services stay user logic;
  only hardware behaviour is assumed.
-/
import Grammatik.X86.PipelineEntry
import Grammatik.X86.ComposeEntryHooks
import Grammatik.X86.ComposeSupportBytes
import Grammatik.X86.ComposeProfileSelect
import Grammatik.X86.TableLayout

namespace Gabbro.Grammatik.X86.PipelineProfiles

open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.PipelineEntry

/-- The two checked OS profiles: hosted (`main` under a C runtime) and
    freestanding (`nolibc` entry with the `os_anfang`/`os_ende` hooks). -/
inductive ZielProfil where
  | gehostet
  | frei
  deriving DecidableEq, Repr

/-- The entry kind each OS profile runs through (IMAGE-ABI section 5). -/
def profilEintritt : ZielProfil → EintrittArt
  | .gehostet => .hostedMain
  | .frei => .nolibcMain

/-- The integer parameter ABI of each OS profile: the System V AMD64
    order, stated per profile so a future target varies it as data. -/
def profilAbi : ZielProfil → List Register
  | .gehostet => sysvParameter
  | .frei => sysvParameter

/- CUTS (skeleton): profile vocabulary only; admission, refusals,
   entry-sequence execution and witnesses follow. -/

/-! ## 1. The checked profile admission

    One `Bool`: the hooked entry admission (checked image mapping AND
    entry state AND caller gate AND both `nolibc` hooks AND the unchanged
    status handoff) AND the support admission (validated image bytes with
    decode coverage AND gate AND arena layout AND stub bindings AND trap
    suffix AND entry state AND float control word). Every reachable
    support byte is covered or refused: `stuetzSchritt` forces
    canonically loaded image memory, so no caller-supplied byte ever
    becomes a trusted support byte. -/

/-- The checked admission of one OS profile: hooked entry AND support. -/
def profilOk (w : ZielProfil) (bild : Bild) (bias : Nat)
    (z : EintrittZustand) (tor : TorDekl) (moves : List Befehl)
    (es : List TabLayout) (h : NolibcHaken) (code rueck : Nat) : Bool :=
  eintrittHakenZulassung .p48 bild bias (profilEintritt w) z [tor] h
    code rueck &&
  stuetzOk .p48 bild tor moves es (profilEintritt w) z

/-- ADMISSION SPLIT: an admitted profile meets the hooked entry half
    and the support half. Pure `Bool` inversion; no producer fact is
    re-proved here. -/
theorem profilOk_teile (w : ZielProfil) (bild : Bild) (bias : Nat)
    (z : EintrittZustand) (tor : TorDekl) (moves : List Befehl)
    (es : List TabLayout) (h : NolibcHaken) (code rueck : Nat)
    (hadm : profilOk w bild bias z tor moves es h code rueck = true) :
    eintrittHakenZulassung .p48 bild bias (profilEintritt w) z [tor] h
      code rueck = true ∧
    stuetzOk .p48 bild tor moves es (profilEintritt w) z = true := by
  unfold profilOk at hadm
  simp only [Bool.and_eq_true] at hadm
  exact hadm

/-- Admission implies the accepted joint entry admission. -/
theorem profilOk_eintrittZulassung (w : ZielProfil) (bild : Bild)
    (bias : Nat) (z : EintrittZustand) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout) (h : NolibcHaken)
    (code rueck : Nat)
    (hadm : profilOk w bild bias z tor moves es h code rueck = true) :
    eintrittZulassung .p48 bild bias (profilEintritt w) z [tor] = true :=
  hakenZulassung_eintrittZulassung _ _ _ _ _ _ _ _ _
    (profilOk_teile w bild bias z tor moves es h code rueck hadm).1

/-- Admission implies the proved entry predicate. -/
theorem profilOk_eintritt (w : ZielProfil) (bild : Bild) (bias : Nat)
    (z : EintrittZustand) (tor : TorDekl) (moves : List Befehl)
    (es : List TabLayout) (h : NolibcHaken) (code rueck : Nat)
    (hadm : profilOk w bild bias z tor moves es h code rueck = true) :
    eintrittOk .p48 bild bias (profilEintritt w) z = true :=
  hakenZulassung_eintritt _ _ _ _ _ _ _ _ _
    (profilOk_teile w bild bias z tor moves es h code rueck hadm).1

/-- Admission implies both hooks are present. -/
theorem profilOk_haken (w : ZielProfil) (bild : Bild) (bias : Nat)
    (z : EintrittZustand) (tor : TorDekl) (moves : List Befehl)
    (es : List TabLayout) (h : NolibcHaken) (code rueck : Nat)
    (hadm : profilOk w bild bias z tor moves es h code rueck = true) :
    hakenOk h = true :=
  hakenZulassung_haken _ _ _ _ _ _ _ _ _
    (profilOk_teile w bild bias z tor moves es h code rueck hadm).1

/-- Admission implies the handed status equals the returned one. -/
theorem profilOk_status (w : ZielProfil) (bild : Bild) (bias : Nat)
    (z : EintrittZustand) (tor : TorDekl) (moves : List Befehl)
    (es : List TabLayout) (h : NolibcHaken) (code rueck : Nat)
    (hadm : profilOk w bild bias z tor moves es h code rueck = true) :
    rueck = code :=
  hakenZulassung_status _ _ _ _ _ _ _ _ _
    (profilOk_teile w bild bias z tor moves es h code rueck hadm).1

/-- Admission makes the RIP executable through the CHECKED loaded
    mapping, the entry stack window readable/writable, and meets every
    support half (image bytes with decode coverage, gate, arena layout,
    stub bindings, trap suffix, entry state, float control word). -/
theorem profilOk_folgen (w : ZielProfil) (bild : Bild) (bias : Nat)
    (z : EintrittZustand) (tor : TorDekl) (moves : List Befehl)
    (es : List TabLayout) (h : NolibcHaken) (code rueck : Nat)
    (hadm : profilOk w bild bias z tor moves es h code rueck = true) :
    (geladen bild bias).ausfuehrbar z.zustand.rip = true ∧
      lesbar8 z.zustand.speicher
        (eintrittRsp z - BitVec.ofNat 64 8) = true ∧
      schreibbar8 z.zustand.speicher
        (eintrittRsp z - BitVec.ofNat 64 8) = true ∧
      valX86 .p48 bild = true ∧ torOkB tor = true ∧
      valLayout es = true ∧
      bindungErstelltB tor moves = true ∧
      stubEndsTrapB (moves.flatMap encode ++ trapBytes) = true ∧
      mxcsrGueltig z.mxcsr = true := by
  obtain ⟨hh, hs⟩ :=
    profilOk_teile w bild bias z tor moves es h code rueck hadm
  obtain ⟨_, _, _, hrip, hrw1, hrw2⟩ :=
    ComposeEntryHooks_verbindung _ _ _ _ _ _ _ _ _ hh
  obtain ⟨hA, hB, hC, hD, hE, _, hG⟩ :=
    stuetzOk_teile _ _ _ _ _ _ _ hs
  exact ⟨hrip, hrw1, hrw2, hA, hB, hC, hD, hE, hG⟩

/-- FIRST INSTRUCTION: from admission, the fetched instruction runs as a
    real byte step, and the RIP is executable through the checked loaded
    mapping. Reuses the accepted hook-entry step; no second fetch. -/
theorem profilOk_erster_schritt (w : ZielProfil) (bild : Bild)
    (bias : Nat) (z : EintrittZustand) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout) (h : NolibcHaken)
    (code rueck : Nat) (d : Decodiert) (rest : List Byte) (s' : Zustand)
    (hadm : profilOk w bild bias z tor moves es h code rueck = true)
    (hf : fetchDekodiert z.zustand = some (d, rest))
    (hs : schritt d z.zustand = some s') :
    (geladen bild bias).ausfuehrbar z.zustand.rip = true ∧
      byteschritt z.zustand = .weiter s' :=
  hakenZulassung_erster_schritt _ _ _ _ _ _ _ _ _ d rest s'
    (profilOk_teile w bild bias z tor moves es h code rueck hadm).1
    hf hs

/-- SUPPORT COVERAGE: through the closing step over loaded image memory,
    a successful fetch runs the existing `schritt`, and no fetch means no
    transition. Unvalidated reachable bytes refuse: nothing outside the
    validated image is ever fetched. -/
theorem profilOk_stuetz_schritt (bild : Bild) (bias : Nat) (s : Zustand)
    (d : Decodiert) (rest : List Byte) (s' : Zustand)
    (hf : fetchDekodiert { s with speicher := geladen bild bias } =
      some (d, rest))
    (hs : schritt d { s with speicher := geladen bild bias } = some s') :
    stuetzSchritt bild bias s = .weiter s' :=
  stuetzSchritt_weiter bild bias s s' d rest hf hs

theorem profilOk_stuetz_verweigert (bild : Bild) (bias : Nat)
    (s : Zustand)
    (hf : fetchDekodiert { s with speicher := geladen bild bias } = none) :
    stuetzSchritt bild bias s = .verweigert :=
  stuetzSchritt_verweigert_ohne_fetch bild bias s hf

#print axioms profilEintritt
#print axioms profilAbi

end Gabbro.Grammatik.X86.PipelineProfiles
