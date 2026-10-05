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
import Grammatik.X86.Pipeline.Kern.PipelineEntry
import Grammatik.X86.Compose.Vertraege.ComposeEntryHooks
import Grammatik.X86.Compose.Bild.ComposeSupportBytes
import Grammatik.X86.Compose.Vertraege.ComposeProfileSelect
import Grammatik.X86.Speicher.TableLayout

namespace Gabbro.Grammatik.X86.PipelineProfiles

open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
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

/-! ## 2. Refusals: every missing leg refuses the profile

    Unsupported shapes are REFUSED, never guessed. Each refusal reuses
    the accepted leg refusal; every premise is used. -/

/-- REFUSAL: without the `anfang` handoff no profile is admitted. -/
theorem profil_verweigert_ohne_anfang (w : ZielProfil) (bild : Bild)
    (bias : Nat) (z : EintrittZustand) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout) (h : NolibcHaken)
    (code rueck : Nat) (hanf : h.anfang = false) :
    profilOk w bild bias z tor moves es h code rueck = false := by
  unfold profilOk
  rw [hakenZulassung_verweigert_ohne_anfang _ _ _ _ _ _ _ _ _ hanf]
  simp

/-- REFUSAL: without the `ende` hook no profile is admitted. -/
theorem profil_verweigert_ohne_ende (w : ZielProfil) (bild : Bild)
    (bias : Nat) (z : EintrittZustand) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout) (h : NolibcHaken)
    (code rueck : Nat) (hende : h.ende = false) :
    profilOk w bild bias z tor moves es h code rueck = false := by
  unfold profilOk
  rw [hakenZulassung_verweigert_ohne_ende _ _ _ _ _ _ _ _ _ hende]
  simp

/-- REFUSAL: a handed status that differs from the returned one admits
    no profile. -/
theorem profil_verweigert_status (w : ZielProfil) (bild : Bild)
    (bias : Nat) (z : EintrittZustand) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout) (h : NolibcHaken)
    (code rueck : Nat) (hmis : rueck ≠ code) :
    profilOk w bild bias z tor moves es h code rueck = false := by
  unfold profilOk
  rw [hakenZulassung_verweigert_status _ _ _ _ _ _ _ _ _ hmis]
  simp

/-- REFUSAL: an unlisted RIP admits no profile. -/
theorem profil_verweigert_unlisted (w : ZielProfil) (bild : Bild)
    (bias : Nat) (z : EintrittZustand) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout) (h : NolibcHaken)
    (code rueck : Nat)
    (hrip : eintragGelisted bild z.zustand.rip.toNat = false) :
    profilOk w bild bias z tor moves es h code rueck = false := by
  unfold profilOk
  rw [hakenZulassung_verweigert_unlisted _ _ _ _ _ _ _ _ _ hrip]
  simp

/-- REFUSAL: a refused gate admits no profile. -/
theorem profil_verweigert_tor (w : ZielProfil) (bild : Bild)
    (bias : Nat) (z : EintrittZustand) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout) (h : NolibcHaken)
    (code rueck : Nat) (href : torOkB tor = false) :
    profilOk w bild bias z tor moves es h code rueck = false := by
  unfold profilOk
  rw [hakenZulassung_verweigert_tor _ _ _ _ _ _ _ _ _ tor
    List.mem_cons_self href]
  simp

/-- IMAGE REFUSAL: support bytes outside a validated image admit no
    profile, whatever the entry side says. -/
theorem profil_verweigert_ohne_bild (w : ZielProfil) (bild : Bild)
    (bias : Nat) (z : EintrittZustand) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout) (h : NolibcHaken)
    (code rueck : Nat) (hbild : valX86 .p48 bild = false) :
    profilOk w bild bias z tor moves es h code rueck = false := by
  unfold profilOk
  rw [stuetz_verweigert_ohne_bild _ _ _ _ _ _ _ hbild]
  simp

/-- FLOAT REFUSAL: an invalid float control word admits no profile. -/
theorem profil_verweigert_ohne_mxcsr (w : ZielProfil) (bild : Bild)
    (bias : Nat) (z : EintrittZustand) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout) (h : NolibcHaken)
    (code rueck : Nat) (hmx : mxcsrGueltig z.mxcsr = false) :
    profilOk w bild bias z tor moves es h code rueck = false := by
  unfold profilOk
  rw [stuetz_verweigert_ohne_mxcsr _ _ _ _ _ _ _ hmx]
  simp

/-! ## 3. The checked entry sequence

    The pipeline's variable registers are ESTABLISHED, never assumed:
    the entry sequence copies the profile ABI registers into them. This
    is the accepted `PipelineEntry.prolog` at the profile ABI, with its
    decided check and its run. -/

/-- The entry sequence of one OS profile for `n` parameters. -/
def profilProlog (c : PipeCfg) (w : ZielProfil) (n : Nat) : List Befehl :=
  prolog c (profilAbi w) n

/-- The entry sequence is straight-line code. -/
theorem profilProlog_gerade (c : PipeCfg) (w : ZielProfil) (n : Nat) :
    (profilProlog c w n).all gerade = true :=
  prolog_gerade c (profilAbi w) n

/-- THE ENTRY SEQUENCE RUNS: the copies execute one after the other,
    keep memory, set every destination to its source's ENTRY value, and
    keep every register that is no destination. -/
theorem profilProlog_lauf (c : PipeCfg) (w : ZielProfil) (n : Nat)
    (s : Zustand)
    (h : (prologPaare c (profilAbi w) n).Pairwise ZugOk) :
    ∃ s', lauf (((prologPaare c (profilAbi w) n).map fun q =>
      Befehl.movReg64 q.1 q.2).map kanon) s = some s' ∧
      s'.speicher = s.speicher ∧
      (∀ q ∈ prologPaare c (profilAbi w) n,
        s'.register q.1 = s.register q.2) ∧
      (∀ r, (∀ q ∈ prologPaare c (profilAbi w) n, r ≠ q.1) →
        s'.register r = s.register r) :=
  zuege_lauf _ s h

/-! ## 4. The profile closing

    Generic over arbitrary admitted inputs: a profile admission carries
    the accepted joint entry admission, both hooks, the unchanged status
    handoff, the executable RIP through the CHECKED loaded mapping, the
    readable/writable entry stack window, and every support half (image
    bytes with decode coverage, gate, arena layout, stub bindings, trap
    suffix, float control word). Composes the accepted producer lemmas
    by name; no producer fact is re-proved here. -/

/-- PROFILE CLOSING over arbitrary admitted inputs. -/
theorem pipeline_profil_verbindung (w : ZielProfil) (bild : Bild)
    (bias : Nat) (z : EintrittZustand) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout) (h : NolibcHaken)
    (code rueck : Nat)
    (hadm : profilOk w bild bias z tor moves es h code rueck = true) :
    eintrittZulassung .p48 bild bias (profilEintritt w) z [tor] = true ∧
      hakenOk h = true ∧ rueck = code ∧
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
  obtain ⟨hh, _⟩ :=
    profilOk_teile w bild bias z tor moves es h code rueck hadm
  obtain ⟨hzul, hhok, hst, hrip, hrw1, hrw2⟩ :=
    ComposeEntryHooks_verbindung _ _ _ _ _ _ _ _ _ hh
  obtain ⟨_, _, _, hA, hB, hC, hD, hE, hG⟩ :=
    profilOk_folgen w bild bias z tor moves es h code rueck hadm
  exact ⟨hzul, hhok, hst, hrip, hrw1, hrw2, hA, hB, hC, hD, hE, hG⟩

/-! ## 5. Joint witnesses and poison probes

    Both profiles are admitted on the minimal image with both hooks and
    the unchanged zero status, next to a fetched `ret` and its executed
    step, a real memory-changing write/read, a table some function
    writes, and a planted refusal for every missing leg. -/

/-- ACCEPTANCE (hosted): the hosted profile is admitted on the minimal
    image with both hooks and the unchanged zero status. -/
theorem profil_gehostet_ok :
    profilOk .gehostet valZeuge 0 zeugenEintrittAusf schreibTor zeugenMoves
      (layoutFuer zeugenU 4096 8) zeugenHaken 0 0 = true := by
  decide

/-- ACCEPTANCE (freestanding): the freestanding profile is admitted
    on the minimal image with both hooks and the unchanged zero
    status. -/
theorem profil_frei_ok :
    profilOk .frei valZeuge 0 zeugenEintrittAusf schreibTor zeugenMoves
      (layoutFuer zeugenU 4096 8) zeugenHaken 0 0 = true := by
  decide

/-- JOINT WITNESS for `pipeline_profil_verbindung`: both profiles
    admitted jointly on the minimal image (both hooks, unchanged zero
    status), with the fetched `ret` and its executed step (a reached run
    from checked bytes), a real memory-changing write/read, a table some
    function writes, and planted refusals for every missing leg. -/
theorem pipeline_profil_verbindung_zeuge :
    profilOk .gehostet valZeuge 0 zeugenEintrittAusf schreibTor
      zeugenMoves (layoutFuer zeugenU 4096 8) zeugenHaken 0 0 = true ∧
    profilOk .frei valZeuge 0 zeugenEintrittAusf schreibTor zeugenMoves
      (layoutFuer zeugenU 4096 8) zeugenHaken 0 0 = true ∧
    fetchDekodiert zeugenEintrittAusf.zustand = some (⟨.ret, 1⟩, []) ∧
    ausgangRip (byteschritt zeugenEintrittAusf.zustand) =
      some (BitVec.ofNat 64 0) ∧
    (∃ (m m' : Speicher) (a : Adresse) (v : Wort),
      v ≠ 0 ∧ write64 m a v = some m' ∧ read64 m' a = some v ∧
        m.bytes a ≠ m'.bytes a) ∧
    (zeugenU.fns.get ⟨0, by decide⟩).schreibt = ["konto"] ∧
    profilOk .gehostet valZeuge 0 zeugenEintrittAusf schreibTor
      zeugenMoves (layoutFuer zeugenU 4096 8)
      { anfang := false, ende := true } 0 0 = false ∧
    profilOk .frei valZeuge 0 zeugenEintrittAusf schreibTor zeugenMoves
      (layoutFuer zeugenU 4096 8) zeugenHaken 0 1 = false ∧
    profilOk .gehostet valWx 0 zeugenEintrittAusf schreibTor zeugenMoves
      (layoutFuer zeugenU 4096 8) zeugenHaken 0 0 = false ∧
    profilOk .frei valZeuge 0 zeugenEintrittAusf torAusClobber
      zeugenMoves (layoutFuer zeugenU 4096 8) zeugenHaken 0 0
      = false := by
  refine ⟨profil_gehostet_ok, profil_frei_ok, zulassung_fetch_ret,
    zulassung_schritt_ret, schreibLese_zeuge, zeugenU_schreibt, ?_, ?_,
    ?_, ?_⟩
  · exact profil_verweigert_ohne_anfang _ _ _ _ _ _ _ _ _ _ rfl
  · exact profil_verweigert_status _ _ _ _ _ _ _ _ _ _ (by decide)
  · exact profil_verweigert_ohne_bild _ _ _ _ _ _ _ _ _ _ valWx_verweigert
  · have href : torOkB torAusClobber = false := by decide
    exact profil_verweigert_tor _ _ _ _ _ _ _ _ _ _ href

/- CUTS: what is not proved here.
   Proved here, by composing the accepted producer modules (no producer
   fact re-proved, no second loader/decoder/executor/ISA/IR): the two
   checked OS profiles (`ZielProfil`: hosted `main` vs freestanding
   `nolibc` entry), each with its entry kind (`profilEintritt`), its
   stated integer parameter ABI (`profilAbi`, System V order as data),
   its checked entry sequence (`profilProlog`, with its run), and the
   one checked admission `profilOk` (hooked entry AND support); its
   split and projections, the executable RIP through the CHECKED loaded
   mapping, the entry stack window, the fetched-first-instruction step,
   the support coverage step (loaded-memory execution, no fetch means
   no transition), one refusal per missing leg (hooks, status, RIP,
   gate, image, float word), the generic closing
   (`pipeline_profil_verbindung` over arbitrary admitted inputs), and
   one joint witness with a reached memory-changing run plus planted
   refusals.
   NOT proved here, and not claimed:
   - No source correspondence: nothing here claims the admitted bytes
     are the emitted form of any source program. The lowering closure
     waits on the shared IR (lane 287, pending); no substitute is
     invented here.
   - No hardware correspondence: fetch runs over the model `Speicher`
     function, not silicon; caches, TLBs, store buffers, interrupts,
     faults beyond the decoded refusal, and timing are OPEN.
   - No TSO/W/GX bridge: per-access refinement of profile bytes stays
     with the bridge lanes; the source `schwach_ist_gX` leg is reused,
     never assumed for the target.
   - No budget/cost transfer, no multi-step control-flow validation, no
     relocation patched-site re-decoding, no kernel behaviour beyond
     the named assumption. Environment services (gates, bindings, the
     loader, the kernel) stay user logic; only hardware behaviour is
     assumed. No implicit Linux/POSIX/libc/ELF anywhere.
   - `verweigert` is the absence of a transition, never a termination
     claim.
-/

#print axioms profilEintritt
#print axioms profilAbi
#print axioms profilOk
#print axioms profilOk_teile
#print axioms profilOk_eintrittZulassung
#print axioms profilOk_eintritt
#print axioms profilOk_haken
#print axioms profilOk_status
#print axioms profilOk_folgen
#print axioms profilOk_erster_schritt
#print axioms profilOk_stuetz_schritt
#print axioms profilOk_stuetz_verweigert
#print axioms profil_verweigert_ohne_anfang
#print axioms profil_verweigert_ohne_ende
#print axioms profil_verweigert_status
#print axioms profil_verweigert_unlisted
#print axioms profil_verweigert_tor
#print axioms profil_verweigert_ohne_bild
#print axioms profil_verweigert_ohne_mxcsr
#print axioms profilProlog
#print axioms profilProlog_gerade
#print axioms profilProlog_lauf
#print axioms pipeline_profil_verbindung
#print axioms profil_gehostet_ok
#print axioms profil_frei_ok
#print axioms pipeline_profil_verbindung_zeuge

end Gabbro.Grammatik.X86.PipelineProfiles
