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

/- CUTS:
    - Skeleton only: no fresh/disjoint preservation is proved yet.
    - No source correspondence is claimed here.
-/

#print axioms ausZahlVerweigert

end Gabbro.Grammatik.X86
