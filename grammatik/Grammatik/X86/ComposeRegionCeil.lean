/-
  Composition closing: region-ceiling closing (lane 859).

  Producer/consumer interface closed here: the accepted ceiling-carrying
  bump allocator (`Regionen.reserviere` with refuse-on-full) produces,
  the accepted separation verdict (`RegionSeparation.trennungOk`) and the
  accepted fresh-region frames (`RegionFresh.frisch_*` over actual
  `Speicher` transitions) consume. A ceilingless region stays refused by
  default; the ceiling-free model (`Regionen.freiReserviere`) runs only
  behind the explicitly named opt-in gate below. This file only composes
  already-accepted definitions and theorems; it re-proves no allocator,
  separation, layout, decoder, executor or cost internals and defines no
  second allocator, interpreter or executor.
-/
import Grammatik.X86.Regionen
import Grammatik.X86.RegionSeparation
import Grammatik.X86.RegionFresh
import Grammatik.X86.TableLayout
import Grammatik.X86.Ausfuehrung

namespace Gabbro.Grammatik.X86

/-- Opt-in gate for the ceiling-free model: without the explicitly named
    `optIn` flag every request is refused by default; with it the request
    runs as the accepted `freiReserviere` (whose external `scheitert`
    answer and lost static bound are carried, not removed). -/
def deckellosSchluss (s : FreiStand) (len : Nat) (optIn scheitert : Bool)
    (l w x : Bool) : Option (Region × FreiStand) :=
  if optIn then freiReserviere s len scheitert l w x else none

/-- DEFAULT REFUSAL: a ceilingless region stays refused without the
    explicitly named opt-in. -/
theorem deckellos_default_verweigert (s : FreiStand) (len : Nat)
    (scheitert : Bool) (l w x : Bool) :
    deckellosSchluss s len false scheitert l w x = none := by
  simp [deckellosSchluss]

/-- NAMED OPT-IN: with the flag the gate is exactly the accepted
    ceiling-free allocation (including its explicit failure answer). -/
theorem deckellos_benannt_offen (s : FreiStand) (len : Nat)
    (scheitert : Bool) (l w x : Bool) :
    deckellosSchluss s len true scheitert l w x =
      freiReserviere s len scheitert l w x := by
  simp [deckellosSchluss]

/-- CEILING CLOSING (verdict): two successive checked reservations under
    declared ceilings hand regions accepted together by `trennungOk`.
    Composes the accepted `frisch_zwei_verdikt`; generic over arbitrary
    admitted inputs. -/
theorem deckel_zwei_trennung (s s1 s2 : Reservierer)
    (len1 ausr1 len2 ausr2 : Nat) (l1 w1 x1 l2 w2 x2 : Bool)
    (r1 r2 : Region)
    (h1 : reserviere s len1 ausr1 l1 w1 x1 = some (r1, s1))
    (h2 : reserviere s1 len2 ausr2 l2 w2 x2 = some (r2, s2))
    (hinv : alleUnten s) :
    trennungOk [r1, r2] = true :=
  frisch_zwei_verdikt s s1 s2 len1 ausr1 len2 ausr2
    l1 w1 x1 l2 w2 x2 r1 r2 h1 h2 hinv

/-- REFUSE-ON-FULL: a request past the declared ceiling is refused
    outright. Composes the accepted `reserviere_voll_verweigert`; generic
    over arbitrary admitted inputs. -/
theorem deckel_voll_verweigert (s : Reservierer) (len ausr : Nat)
    (l w x : Bool) (start : Nat) (hau : ausricht s.naechst ausr = some start)
    (hvoll : s.vorrat.lo + s.vorrat.umfang < start + len) :
    reserviere s len ausr l w x = none :=
  reserviere_voll_verweigert s len ausr l w x start hau hvoll

/-- STORE FRAME through the closing: a successful 8-byte store inside the
    first handed ceiling region preserves reads inside the second. Runs
    through the accepted `frisch_schreibt_rahmen` over the actual
    `write64` transition; generic over arbitrary admitted inputs. -/
theorem deckel_schreibt_rahmen (s s1 s2 : Reservierer)
    (len1 ausr1 len2 ausr2 : Nat) (l1 w1 x1 l2 w2 x2 : Bool)
    (r1 r2 : Region)
    (h1 : reserviere s len1 ausr1 l1 w1 x1 = some (r1, s1))
    (h2 : reserviere s1 len2 ausr2 l2 w2 x2 = some (r2, s2))
    (hinv : alleUnten s)
    (m m' : Speicher) (x y : Adresse) (v : Wort)
    (hx : r1.basis ≤ x.toNat ∧ x.toNat + 8 ≤ r1.basis + r1.len)
    (hy : r2.basis ≤ y.toNat ∧ y.toNat + 8 ≤ r2.basis + r2.len)
    (hAx : OhneUmbruch x) (hAy : OhneUmbruch y)
    (hwr : write64 m x v = some m') :
    read64 m' y = read64 m y :=
  frisch_schreibt_rahmen s s1 s2 len1 ausr1 len2 ausr2
    l1 w1 x1 l2 w2 x2 r1 r2 h1 h2 hinv m m' x y v hx hy hAx hAy hwr

/-- OPT-IN STILL FAILS LOUDLY: even behind the named flag the external
    `scheitert` answer refuses. The opt-in names the ceiling-free model,
    never success. -/
theorem deckellos_optIn_kann_scheitern (s : FreiStand) (len : Nat)
    (l w x : Bool) :
    deckellosSchluss s len true true l w x = none := by
  rw [deckellos_benannt_offen]
  exact freiReserviere_kann_scheitern s len l w x

/-- REGION-CEILING CLOSING, generic over arbitrary admitted inputs: two
    successive checked reservations under declared ceilings hand regions
    accepted together (`trennungOk`) with the store frame through the
    actual `write64` transition; a ceilingless region stays refused by
    default AND under an externally failed answer; and the named opt-in
    still loses the static bound (some request past any bound `B`
    succeeds). Composes only accepted theorems by name; no allocator,
    separation, layout, decoder, executor or cost fact is re-proved here.
    Every premise is used: the reservation premises feed the verdict and
    the frame, the gate premises feed both refusals, `B`/`hB` feed the
    bound-loss witness. -/
theorem ComposeRegionCeil_verbindung
    (s s1 s2 : Reservierer)
    (len1 ausr1 len2 ausr2 : Nat) (l1 w1 x1 l2 w2 x2 : Bool)
    (r1 r2 : Region)
    (h1 : reserviere s len1 ausr1 l1 w1 x1 = some (r1, s1))
    (h2 : reserviere s1 len2 ausr2 l2 w2 x2 = some (r2, s2))
    (hinv : alleUnten s)
    (m m' : Speicher) (x y : Adresse) (v : Wort)
    (hx : r1.basis ≤ x.toNat ∧ x.toNat + 8 ≤ r1.basis + r1.len)
    (hy : r2.basis ≤ y.toNat ∧ y.toNat + 8 ≤ r2.basis + r2.len)
    (hAx : OhneUmbruch x) (hAy : OhneUmbruch y)
    (hwr : write64 m x v = some m')
    (f : FreiStand) (flen : Nat) (fl fw fx : Bool)
    (B : Nat) (hB : B < 2 ^ 64) :
    trennungOk [r1, r2] = true ∧
    read64 m' y = read64 m y ∧
    deckellosSchluss f flen false true fl fw fx = none ∧
    deckellosSchluss f flen true true fl fw fx = none ∧
    (∃ (g : FreiStand) (glen : Nat) (gr : Region) (g' : FreiStand),
      deckellosSchluss g glen true false true true false = some (gr, g') ∧
        B < gr.len) := by
  refine ⟨deckel_zwei_trennung s s1 s2 len1 ausr1 len2 ausr2
    l1 w1 x1 l2 w2 x2 r1 r2 h1 h2 hinv,
    deckel_schreibt_rahmen s s1 s2 len1 ausr1 len2 ausr2
      l1 w1 x1 l2 w2 x2 r1 r2 h1 h2 hinv m m' x y v hx hy hAx hAy hwr,
    deckellos_default_verweigert f flen true fl fw fx,
    deckellos_optIn_kann_scheitern f flen fl fw fx, ?_⟩
  obtain ⟨g, glen, gr, g', hfr, hlt⟩ :=
    freiReserviere_ohne_statik_gebunden B hB
  exact ⟨g, glen, gr, g', by rw [deckellos_benannt_offen]; exact hfr, hlt⟩

/-- JOINT WITNESS for `ComposeRegionCeil_verbindung`: all premises are
    instantiated jointly on the accepted witness chain (two real
    successive 8-byte reservations at 65536/65544, accepted together;
    a nonzero `write64` in the first region that goes through, reads
    back, observably changes its byte from zero and preserves the second
    region's read; the ceilingless default refused; the named opt-in
    reaching past 4096; some source function writing a table
    (non-degenerate: table `konto` with writer `setze`); the reached
    instruction run observably changing memory (byte 42 at 8192); the
    planted refuse-on-full past the 4 KiB ceiling; the planted overlap
    refusal). -/
theorem ComposeRegionCeil_verbindung_zeuge :
    trennungOk [zeugenRegion, frischRegionZwei] = true ∧
    (∃ (m' : Speicher),
      write64 frischSpeicher (natAdresse 65536) 42 = some m' ∧
      read64 m' (natAdresse 65544) =
        read64 frischSpeicher (natAdresse 65544) ∧
      frischSpeicher.bytes (natAdresse 65536) ≠
        m'.bytes (natAdresse 65536)) ∧
    frischSpeicher.bytes (natAdresse 65536) = BitVec.ofNat 8 0 ∧
    deckellosSchluss ⟨0⟩ 8 false true true true false = none ∧
    (∃ (g : FreiStand) (glen : Nat) (gr : Region) (g' : FreiStand),
      deckellosSchluss g glen true false true true false = some (gr, g') ∧
        4096 < gr.len) ∧
    (zeugenU.fns.get ⟨0, by decide⟩).schreibt = ["konto"] ∧
    ((lauf zeugeProg zeugeZustand).map
      (fun s => s.speicher.bytes (BitVec.ofNat 64 8192)) =
      some (BitVec.ofNat 8 42)) ∧
    reserviere zeugenStart 8192 8 true true false = none ∧
    allePaareDisjunkt [zeugenRegion, frischRegionUeberlapp] = false := by
  refine ⟨frisch_zwei_verdikt_zeuge, ?_, rfl,
    deckellos_default_verweigert _ _ _ _ _ _, ?_,
    zeugenU_schreibt, zeuge_speicher_aendert_sich.2.1,
    zeugenReserviere_voll, frischUeberlapp_verweigert⟩
  · obtain ⟨m', hwr, hframe, _, _, _, hchg⟩ :=
      frisch_schreibt_rahmen_zeuge
    exact ⟨m', hwr, hframe, hchg⟩
  · obtain ⟨g, glen, gr, g', hfr, hlt⟩ :=
      freiReserviere_ohne_statik_gebunden 4096 (by decide)
    exact ⟨g, glen, gr, g', by rw [deckellos_benannt_offen]; exact hfr, hlt⟩

/- CUTS:
    Proved here, by composing the accepted producer modules (no producer
    fact re-proved, no second allocator/interpreter/executor): the
    ceilingless opt-in gate (`deckellosSchluss`, default refusal, named
    opening, loud external failure), the ceiling verdict over two
    successive checked reservations (`deckel_zwei_trennung`), the
    refuse-on-full leg (`deckel_voll_verweigert`), the store frame over
    the actual `write64` transition (`deckel_schreibt_rahmen`), the one
    closing step (`ComposeRegionCeil_verbindung`, generic over arbitrary
    admitted inputs), and one joint non-degenerate witness with a
    reached memory-changing run and planted refusals
    (`ComposeRegionCeil_verbindung_zeuge`).
    NOT proved here, and not claimed:
    - No source-to-allocator correspondence: nothing here claims which
      Gabbro arena, gate or allocator construct lowers to which
      `reserviere` call, nor any duty, cost or template fact about it.
      The witness only reuses the existing writer fact
      (`zeugenU_schreibt`) and the reached run
      (`zeuge_speicher_aendert_sich`) as non-degeneracy evidence.
    - No integer-to-pointer conversion anywhere: handed regions are
      capabilities from checked `reserviere`, never casts; `natAdresse`
      names probe addresses only (accepted vocabulary).
    - Sequential footprints only: disjointness is footprint disjointness
      over one canonical `Speicher`. Per-access TSO refinement, atomicity
      and any concurrent reading stay with the TSO bridge (owning lane:
      the accepted 567/TSOHistory bridge work).
    - The ceiling-free opt-in keeps its accepted cost: every request may
      fail (`scheitert`) and no static `Nat` bound below `2 ^ 64` holds
      (`freiReserviere_ohne_statik_gebunden`); every extent still
      satisfies `basis + len ≤ 2 ^ 64`, so no physical
      unbounded-x86-address claim is made.
    - No loader/image integration beyond the accepted `RegionSeparation`
      vocabulary; mapping, entries, relocations and the loader contract
      stay with `Bild.lean` (owning lanes: image/relocation owners).
    - No decoder, encoder, instruction semantics, ABI, cost transfer,
      budget, progress, timing, entry or whole-image acceptance is proved
      here; source-memory representation beyond the reused witness stays
      with lane 570 (`SourceMemory`).
    - No `Zielsatz/Spec` statement is touched; full
      source-to-final-bytes validation remains OPEN.
-/

#print axioms deckellosSchluss
#print axioms deckellos_default_verweigert
#print axioms deckellos_benannt_offen
#print axioms deckel_zwei_trennung
#print axioms deckel_voll_verweigert
#print axioms deckel_schreibt_rahmen
#print axioms deckellos_optIn_kann_scheitern
#print axioms ComposeRegionCeil_verbindung
#print axioms ComposeRegionCeil_verbindung_zeuge

end Gabbro.Grammatik.X86
