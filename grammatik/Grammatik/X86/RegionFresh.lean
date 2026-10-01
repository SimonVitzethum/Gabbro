/-
  File:      Grammatik/X86/RegionFresh.lean
  Subject:   Fresh/disjoint external-region proofs over checked allocation.

  Lane 544 (N18): generic fresh/disjoint external-region preservation over
  the accepted `Regionen.reserviere`/`initialisiere` and `RegionSeparation`
  interfaces, proved over actual `Speicher` memory transitions and multiple
  reservations. Region extent/ownership originate in the existing
  source/binding model (`TableLayout.alsRegion` over the computed layout),
  never from an integer-to-pointer conversion. Source-to-allocator
  correspondence stays OPEN (see CUTS).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Regionen
import Grammatik.X86.RegionSeparation
import Grammatik.X86.TableLayout
import Grammatik.X86.Ausfuehrung

namespace Gabbro.Grammatik.X86

/-- A bare number names no region extent: admission requires membership. -/
def ausZahlVerweigert (n : Nat) (rs : List Region) : Bool :=
  rs.all (fun r => !inRegion r n)

/-- SOUNDNESS of the number refusal: a refused bare number lies in no
    listed region extent. Every premise is used. -/
theorem ausZahlVerweigert_klingt (n : Nat) (rs : List Region)
    (h : ausZahlVerweigert n rs = true) (r : Region) (hm : r ∈ rs) :
    inRegion r n = false := by
  unfold ausZahlVerweigert at h
  rw [List.all_eq_true] at h
  have h2 := h r hm
  simpa using h2

/-- Interval fact: an address inside one of two disjoint regions lies
    outside the other. Real interval arithmetic, never assumed. -/
theorem disjunkt_nicht_in_region (a b : Region)
    (hd : regionDisjunkt a b = true)
    (x : Nat) (hx : inRegion a x = true) :
    inRegion b x = false := by
  unfold regionDisjunkt at hd
  unfold inRegion at hx ⊢
  rw [decide_eq_true_eq] at hd hx
  rw [decide_eq_false_iff_not]
  omega

/-- FRESHNESS over two reservations: the second handed region is
    disjoint from the first. Discharged through the cursor invariant,
    never assumed. Every premise is used. -/
theorem frisch_zwei_disjunkt (s s1 s2 : Reservierer)
    (len1 ausr1 len2 ausr2 : Nat) (l1 w1 x1 l2 w2 x2 : Bool)
    (r1 r2 : Region)
    (h1 : reserviere s len1 ausr1 l1 w1 x1 = some (r1, s1))
    (h2 : reserviere s1 len2 ausr2 l2 w2 x2 = some (r2, s2))
    (hinv : alleUnten s) :
    regionDisjunkt r1 r2 = true := by
  have hinv1 : alleUnten s1 :=
    reserviere_haelt_alleUnten s len1 ausr1 l1 w1 x1 r1 s1 h1 hinv
  have hfr1 := reserviere_frisch s len1 ausr1 l1 w1 x1 r1 s1 h1
  obtain ⟨-, -, hmem1⟩ := hfr1
  have hd := reserviere_disjunkt_unten s1 len2 ausr2 l2 w2 x2 r2 s2
    h2 hinv1 r1 hmem1
  rw [regionDisjunkt_symm]
  exact hd

/-- A contained region meets the no-wrap bound: the third conjunct of
    `innerhalb` is exactly `keinUmbruchR`. -/
theorem innerhalb_keinUmbruch (v : Vorrat) (r : Region)
    (h : innerhalb v r = true) : keinUmbruchR r = true := by
  unfold innerhalb at h
  unfold keinUmbruchR
  rw [decide_eq_true_eq] at h ⊢
  obtain ⟨-, -, hwrap⟩ := h
  exact hwrap

/-- VERDICT over two reservations: both handed regions are accepted by
    `trennungOk` together. No-wrap comes from containment, disjointness
    from freshness. Every premise is used. -/
theorem frisch_zwei_verdikt (s s1 s2 : Reservierer)
    (len1 ausr1 len2 ausr2 : Nat) (l1 w1 x1 l2 w2 x2 : Bool)
    (r1 r2 : Region)
    (h1 : reserviere s len1 ausr1 l1 w1 x1 = some (r1, s1))
    (h2 : reserviere s1 len2 ausr2 l2 w2 x2 = some (r2, s2))
    (hinv : alleUnten s) :
    trennungOk [r1, r2] = true := by
  have hd := frisch_zwei_disjunkt s s1 s2 len1 ausr1 len2 ausr2
    l1 w1 x1 l2 w2 x2 r1 r2 h1 h2 hinv
  have hw1 := innerhalb_keinUmbruch s.vorrat r1
    (reserviere_innerhalb s len1 ausr1 l1 w1 x1 r1 s1 h1)
  have hw2 := innerhalb_keinUmbruch s1.vorrat r2
    (reserviere_innerhalb s1 len2 ausr2 l2 w2 x2 r2 s2 h2)
  simp [trennungOk, alleOhneUmbruch, allePaareDisjunkt, hw1, hw2, hd]

/-- STORE FRAME over fresh regions: a successful 8-byte store inside
    the first handed region preserves reads inside the second. The frame
    runs through the separation lemma on the proved disjointness, over
    the actual `write64` transition. Every premise is used. -/
theorem frisch_schreibt_rahmen (s s1 s2 : Reservierer)
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
    read64 m' y = read64 m y := by
  have hd := frisch_zwei_disjunkt s s1 s2 len1 ausr1 len2 ausr2
    l1 w1 x1 l2 w2 x2 r1 r2 h1 h2 hinv
  exact trennung_schreibt_rahmen m m' r1 r2 x y v hd hx hy hAx hAy hwr

/-- INIT FRAME over fresh regions: initialising the second handed
    region changes no byte inside the first. The interval fact turns
    proved disjointness into the actual `initialisiere` frame condition.
    Every premise is used. -/
theorem frisch_init_rahmen (s s1 s2 : Reservierer)
    (len1 ausr1 len2 ausr2 : Nat) (l1 w1 x1 l2 w2 x2 : Bool)
    (r1 r2 : Region)
    (h1 : reserviere s len1 ausr1 l1 w1 x1 = some (r1, s1))
    (h2 : reserviere s1 len2 ausr2 l2 w2 x2 = some (r2, s2))
    (hinv : alleUnten s)
    (m : Speicher) (z : Adresse)
    (hz : inRegion r1 z.toNat = true) :
    (initialisiere m r2).bytes z = m.bytes z := by
  have hd := frisch_zwei_disjunkt s s1 s2 len1 ausr1 len2 ausr2
    l1 w1 x1 l2 w2 x2 r1 r2 h1 h2 hinv
  have hframe := disjunkt_nicht_in_region r1 r2 hd z.toNat hz
  exact initialisiere_rahmen_bytes m r2 z hframe

/-- SOURCE BRIDGE: an accepted computed layout separates as regions.
    Extent and ownership originate in the existing source/binding model
    (`layoutFuer` over the source unit, read through `alsRegion`), never
    from a number. Every premise is used. -/
theorem layoutOk_trennung (es : List TabLayout)
    (h : layoutOk es = true) :
    allePaareDisjunkt (es.map alsRegion) = true := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
    have hpaar : paarOk (e :: rest) = true := by
      unfold layoutOk at h
      rw [Bool.and_eq_true] at h
      exact h.2
    unfold paarOk at hpaar
    rw [Bool.and_eq_true] at hpaar
    obtain ⟨hhead, htail⟩ := hpaar
    have hall : ((e :: rest).all eintragOk) = true := by
      unfold layoutOk at h
      rw [Bool.and_eq_true] at h
      exact h.1
    have hlay : layoutOk rest = true := by
      unfold layoutOk
      rw [Bool.and_eq_true]
      refine ⟨?_, htail⟩
      rw [List.all_eq_true]
      intro y hy
      rw [List.all_eq_true] at hall
      exact hall y (List.mem_cons_of_mem _ hy)
    rw [List.all_eq_true] at hhead
    simp only [List.map_cons]
    unfold allePaareDisjunkt
    rw [Bool.and_eq_true]
    refine ⟨?_, ih hlay⟩
    rw [List.all_eq_true]
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    exact hhead t ht

/-! ## Witnesses: two real reservations, stores to both, refusals. -/

/-- Second witness region: eight bytes right past `zeugenRegion`. -/
def frischRegionZwei : Region :=
  { basis := 65544, len := 8, lesbar := true,
    schreibbar := true, ausfuehrbar := false }

/-- Allocator after the first witness reservation (matches
    `zeugenReserviere_erfolg`). -/
def frischZustandEins : Reservierer :=
  { vorrat := zeugenVorrat, naechst := 65544, belegt := [zeugenRegion] }

/-- Allocator after both witness reservations. -/
def frischZustandZwei : Reservierer :=
  { vorrat := zeugenVorrat, naechst := 65552,
    belegt := [frischRegionZwei, zeugenRegion] }

/-- SUCCESS PROBE: the second eight-byte request is handed at 65544 and
    the cursor advances past it (real allocator probe). -/
theorem frisch_zeugen_zweit :
    reserviere frischZustandEins 8 8 true true false =
      some (frischRegionZwei, frischZustandZwei) := by
  decide

/-- The empty witness allocator satisfies the cursor invariant. -/
theorem frisch_zeugen_start_unten : alleUnten zeugenStart :=
  alleUnten_leer zeugenVorrat 65536

/-- JOINT WITNESS for `frisch_zwei_disjunkt`: two real successive
    reservations hand disjoint regions, through the generic theorem. -/
theorem frisch_zwei_disjunkt_zeuge :
    regionDisjunkt zeugenRegion frischRegionZwei = true :=
  frisch_zwei_disjunkt zeugenStart frischZustandEins frischZustandZwei
    8 8 8 8 true true false true true false
    zeugenRegion frischRegionZwei
    zeugenReserviere_erfolg frisch_zeugen_zweit
    frisch_zeugen_start_unten

/-- JOINT WITNESS for `frisch_zwei_verdikt`: both handed regions are
    accepted together, through the generic theorem. -/
theorem frisch_zwei_verdikt_zeuge :
    trennungOk [zeugenRegion, frischRegionZwei] = true :=
  frisch_zwei_verdikt zeugenStart frischZustandEins frischZustandZwei
    8 8 8 8 true true false true true false
    zeugenRegion frischRegionZwei
    zeugenReserviere_erfolg frisch_zeugen_zweit
    frisch_zeugen_start_unten

/-- Witness memory: zero bytes, fully readable/writable, never executable. -/
def frischSpeicher : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0
    lesbar := fun _ => true
    schreibbar := fun _ => true
    ausfuehrbar := fun _ => false }

/-- The 8-byte access at 65536 lies in the first witness region. -/
theorem frischEnthaltenEins :
    zeugenRegion.basis ≤ (natAdresse 65536).toNat ∧
    (natAdresse 65536).toNat + 8 ≤
      zeugenRegion.basis + zeugenRegion.len := by
  decide

/-- The 8-byte access at 65544 lies in the second witness region. -/
theorem frischEnthaltenZwei :
    frischRegionZwei.basis ≤ (natAdresse 65544).toNat ∧
    (natAdresse 65544).toNat + 8 ≤
      frischRegionZwei.basis + frischRegionZwei.len := by
  decide

/-- No-wrap facts for both witness access addresses. -/
theorem frischOhne65536 : OhneUmbruch (natAdresse 65536) := by
  unfold OhneUmbruch
  decide

theorem frischOhne65544 : OhneUmbruch (natAdresse 65544) := by
  unfold OhneUmbruch
  decide

/-- Both witness addresses are writable in the witness memory. -/
theorem frischSchreibbar65536 :
    schreibbar8 frischSpeicher (natAdresse 65536) = true := by
  decide

theorem frischSchreibbar65544 :
    schreibbar8 frischSpeicher (natAdresse 65544) = true := by
  decide

/-- Both witness addresses are readable in the witness memory. -/
theorem frischLesbar65536 :
    lesbar8 frischSpeicher (natAdresse 65536) = true := by
  decide

theorem frischLesbar65544 :
    lesbar8 frischSpeicher (natAdresse 65544) = true := by
  decide

/-- The witness read at 65544 succeeds with value zero (so the preserved
    read below is a real successful read, never a vacuous `none`). -/
theorem frischLiest65544 :
    read64 frischSpeicher (natAdresse 65544) = some 0 := by
  unfold read64
  rw [if_pos frischLesbar65544]
  decide

/-- JOINT WITNESS for `frisch_schreibt_rahmen`: a nonzero `write64` in
    the first handed region goes through, reads back, observably changes
    its byte, and preserves the second region's read and byte through
    the generic fresh-region frame. -/
theorem frisch_schreibt_rahmen_zeuge :
    ∃ (m' : Speicher),
      write64 frischSpeicher (natAdresse 65536) 42 = some m' ∧
      read64 m' (natAdresse 65544) =
        read64 frischSpeicher (natAdresse 65544) ∧
      read64 frischSpeicher (natAdresse 65544) = some 0 ∧
      read64 m' (natAdresse 65536) = some 42 ∧
      m'.bytes (natAdresse 65544) =
        frischSpeicher.bytes (natAdresse 65544) ∧
      frischSpeicher.bytes (natAdresse 65536) ≠
        m'.bytes (natAdresse 65536) := by
  have hwr : write64 frischSpeicher (natAdresse 65536) 42 =
      some { frischSpeicher with
        bytes := writeBytes frischSpeicher (natAdresse 65536) 42 } := by
    unfold write64
    rw [if_pos frischSchreibbar65536]
  refine ⟨_, hwr, ?_, frischLiest65544, ?_, ?_, ?_⟩
  · exact frisch_schreibt_rahmen zeugenStart frischZustandEins
      frischZustandZwei 8 8 8 8 true true false true true false
      zeugenRegion frischRegionZwei
      zeugenReserviere_erfolg frisch_zeugen_zweit
      frisch_zeugen_start_unten _ _ _ _ _
      frischEnthaltenEins frischEnthaltenZwei
      frischOhne65536 frischOhne65544 hwr
  · exact read64_nach_write64 _ _ _ _ hwr frischLesbar65536
  · exact trennung_schreibt_bytes frischSpeicher _ zeugenRegion
      frischRegionZwei _ 42 frisch_zwei_disjunkt_zeuge
      frischEnthaltenEins frischOhne65536 _ ⟨by decide, by decide⟩ hwr
  · have hhit := writeBytesN_hit frischSpeicher (natAdresse 65536) 42 8 0
      (by decide) (by decide)
    rw [addrOff_null] at hhit
    show BitVec.ofNat 8 0 ≠
      writeBytes frischSpeicher (natAdresse 65536) 42 (natAdresse 65536)
    unfold writeBytes
    rw [hhit]
    decide

/-- JOINT WITNESS for `frisch_init_rahmen`: initialising the second
    handed region preserves the first region's byte, through the generic
    theorem over the real interval fact. -/
theorem frisch_init_rahmen_zeuge :
    (initialisiere frischSpeicher frischRegionZwei).bytes
      (natAdresse 65536) = frischSpeicher.bytes (natAdresse 65536) :=
  frisch_init_rahmen zeugenStart frischZustandEins frischZustandZwei
    8 8 8 8 true true false true true false
    zeugenRegion frischRegionZwei
    zeugenReserviere_erfolg frisch_zeugen_zweit
    frisch_zeugen_start_unten frischSpeicher (natAdresse 65536) (by decide)

/-- Overlapping probe region: `[65540, 65548)` shares bytes with both
    witness regions. -/
def frischRegionUeberlapp : Region :=
  { basis := 65540, len := 8, lesbar := true,
    schreibbar := true, ausfuehrbar := false }

/-- OVERLAP REFUSAL: `[65536, 65544)` and `[65540, 65548)` share bytes,
    so no checked reservation may hand both. -/
theorem frischUeberlapp_verweigert :
    allePaareDisjunkt [zeugenRegion, frischRegionUeberlapp] = false := by
  decide

/-- NUMBER REFUSAL: the bare number 0 lies in no handed region extent,
    so it names no address. -/
theorem frischZahl_verweigert :
    ausZahlVerweigert 0 [zeugenRegion, frischRegionZwei] = true := by
  decide

/-- NON-VACUITY: the refusal is not trivially true -- the handed base
    65536 IS admitted as a member of the first region. -/
theorem frischZahl_angenommen :
    ausZahlVerweigert 65536 [zeugenRegion, frischRegionZwei] = false := by
  decide

/-- JOINT WITNESS for `layoutOk_trennung`: the computed witness layout
    separates as regions, through the generic bridge on the accepted
    computed layout. -/
theorem layoutOk_trennung_zeuge :
    allePaareDisjunkt ((layoutFuer zeugenU 4096 8).map alsRegion) = true :=
  layoutOk_trennung _ layout_zeuge.1

/-- JOINT WITNESS: some source function writes a table (non-degenerate:
    table `konto` with writer `setze`), the reached instruction run
    observably changed memory, two real reservations hand disjoint
    regions accepted together, the overlapping interval is refused, the
    bare number names no extent, and a real store in the first region
    preserves the second region's read while changing its own byte. -/
theorem regionFrisch_zeuge :
    (zeugenU.fns.get ⟨0, by decide⟩).schreibt = ["konto"] ∧
    ((lauf zeugeProg zeugeZustand).map
      (fun s => s.speicher.bytes (BitVec.ofNat 64 8192)) =
      some (BitVec.ofNat 8 42)) ∧
    trennungOk [zeugenRegion, frischRegionZwei] = true ∧
    regionDisjunkt zeugenRegion frischRegionZwei = true ∧
    allePaareDisjunkt [zeugenRegion, frischRegionUeberlapp] = false ∧
    ausZahlVerweigert 0 [zeugenRegion, frischRegionZwei] = true ∧
    (∃ (m' : Speicher),
      write64 frischSpeicher (natAdresse 65536) 42 = some m' ∧
      read64 m' (natAdresse 65544) =
        read64 frischSpeicher (natAdresse 65544) ∧
      frischSpeicher.bytes (natAdresse 65536) ≠
        m'.bytes (natAdresse 65536)) := by
  refine ⟨zeugenU_schreibt, zeuge_speicher_aendert_sich.2.1,
    frisch_zwei_verdikt_zeuge, frisch_zwei_disjunkt_zeuge,
    frischUeberlapp_verweigert, frischZahl_verweigert, ?_⟩
  obtain ⟨m', hwr, hframe, _, _, _, hchg⟩ :=
    frisch_schreibt_rahmen_zeuge
  exact ⟨m', hwr, hframe, hchg⟩

/- CUTS:
    - No source-to-allocator correspondence: nothing here claims which
      Gabbro arena, gate or allocator construct lowers to which
      `reserviere` call, nor any duty, cost or template fact about it.
      `layoutOk_trennung` only re-reads the accepted computed layout in
      region vocabulary; the lowering itself stays OPEN.
    - No integer-to-pointer conversion anywhere: fresh regions are
      capabilities handed by checked `reserviere`, never casts.
      `ausZahlVerweigert` decides that a bare number lies in no listed
      extent (proved sound); `natAdresse` names probe addresses only.
    - Sequential footprints only: disjointness is footprint disjointness
      over one canonical `Speicher`. Per-access TSO refinement, atomicity
      and any concurrent reading stay with the TSO bridge.
    - Finite supply only: only the ceiling-carrying `reserviere` chain is
      covered. The opt-in ceiling-free `freiReserviere` model and its
      external `scheitert` answer (runtime/OS behaviour, user logic) are
      untouched here.
    - No loader/image integration beyond the accepted `RegionSeparation`
      vocabulary (`regionDisjunkt`, `trennungOk`, `trennung_schreibt_*`
      frames); mapping, entries, relocations and the loader contract stay
      with `Bild.lean`.
    - No decoder, encoder, instruction semantics, ABI, cost transfer,
      budget, progress, timing, or whole-image acceptance is proved here.
    - No `Zielsatz/Spec` statement is touched; the joint witness only
      reuses the existing writer fact (`zeugenU_schreibt`) and the reached
      run (`zeuge_speicher_aendert_sich`) as non-degeneracy evidence.
    - Full source-to-final-bytes validation remains OPEN.
-/

#print axioms ausZahlVerweigert
#print axioms ausZahlVerweigert_klingt
#print axioms disjunkt_nicht_in_region
#print axioms innerhalb_keinUmbruch
#print axioms frisch_zwei_disjunkt
#print axioms frisch_zwei_verdikt
#print axioms frisch_schreibt_rahmen
#print axioms frisch_init_rahmen
#print axioms layoutOk_trennung
#print axioms frischRegionZwei
#print axioms frischZustandEins
#print axioms frischZustandZwei
#print axioms frisch_zeugen_zweit
#print axioms frisch_zeugen_start_unten
#print axioms frisch_zwei_disjunkt_zeuge
#print axioms frisch_zwei_verdikt_zeuge
#print axioms frischSpeicher
#print axioms frischEnthaltenEins
#print axioms frischEnthaltenZwei
#print axioms frischOhne65536
#print axioms frischOhne65544
#print axioms frischSchreibbar65536
#print axioms frischSchreibbar65544
#print axioms frischLesbar65536
#print axioms frischLesbar65544
#print axioms frischLiest65544
#print axioms frisch_schreibt_rahmen_zeuge
#print axioms frisch_init_rahmen_zeuge
#print axioms frischRegionUeberlapp
#print axioms frischUeberlapp_verweigert
#print axioms frischZahl_verweigert
#print axioms frischZahl_angenommen
#print axioms layoutOk_trennung_zeuge
#print axioms regionFrisch_zeuge

end Gabbro.Grammatik.X86
