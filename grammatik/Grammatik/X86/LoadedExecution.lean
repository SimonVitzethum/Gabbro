/-
  Loaded image to actual instruction fetch (lane 560).

  Connects the checked `Bild` file/virtual mapping and its actual memory
  construction (`geladen`, `abteilFinden`, `ladenByte`) to the byte fetch
  (`Byteschritt.geholt`, `fetchDekodiert`, `byteschritt`). The checked map
  is a premise; fetched-byte equality and the loaded execution step are
  derived conclusions. No source refinement or hardware correspondence is
  claimed here; both stay explicitly open (see CUTS).
-/
import Grammatik.X86.Bild
import Grammatik.X86.Byteschritt

namespace Gabbro.Grammatik.X86

/-- Execution state over a canonically loaded image: registers, flags and
    `rip` are caller-chosen; memory is the checked `geladen` construction,
    never a second loader. -/
def bildZustand (bild : Bild) (bias : Nat) (rip : Adresse)
    (reg : Register → Wort) (fl : Flags) : Zustand :=
  { register := reg
    flags := fl
    rip := rip
    speicher := geladen bild bias }

/-- The loaded state carries the canonically loaded memory. -/
theorem bildZustand_speicher (bild : Bild) (bias : Nat) (rip : Adresse)
    (reg : Register → Wort) (fl : Flags) :
    (bildZustand bild bias rip reg fl).speicher = geladen bild bias := by
  rfl

/-! ## 1. Checked-map inversion: the acceptance Bool as premise.

    Each fact below takes `wohlgeformt p bild = true` as a premise and
    derives one per-section obligation for a member section. -/

/-- INVERSION (sizes): an accepted image checks every section's size. -/
theorem wohlgeformt_groesse (p : Profil) (bild : Bild) (s : Abschnitt)
    (hmem : s ∈ bild.abschnitte) (h : wohlgeformt p bild = true) :
    groesseOk s = true := by
  have h2 := h
  simp only [wohlgeformt, Bool.and_eq_true] at h2
  have hall : bild.abschnitte.all groesseOk = true :=
    h2.1.1.1.1.1.1.1.1.1.1
  exact (List.all_eq_true.mp hall) s hmem

/-- INVERSION (file containment): every section of an accepted image lies
    inside the file. -/
theorem wohlgeformt_datei (p : Profil) (bild : Bild) (s : Abschnitt)
    (hmem : s ∈ bild.abschnitte) (h : wohlgeformt p bild = true) :
    s.dateiOff + s.dateiLen ≤ bild.datei.length := by
  have h2 := h
  simp only [wohlgeformt, Bool.and_eq_true] at h2
  have hall : bild.abschnitte.all (dateiOk bild.datei) = true :=
    h2.1.1.1.1.1.1.1.1.1.2
  have hs : dateiOk bild.datei s = true :=
    (List.all_eq_true.mp hall) s hmem
  exact of_decide_eq_true hs

/-- INVERSION (W^X): no section of an accepted image is writable and
    executable at once. -/
theorem wohlgeformt_wx (p : Profil) (bild : Bild) (s : Abschnitt)
    (hmem : s ∈ bild.abschnitte) (h : wohlgeformt p bild = true) :
    wxOk s = true := by
  have h2 := h
  simp only [wohlgeformt, Bool.and_eq_true] at h2
  have hall : bild.abschnitte.all wxOk = true :=
    h2.1.1.1.1.1.2
  exact (List.all_eq_true.mp hall) s hmem

/-- INVERSION (alignment): the biased base of every section of an accepted
    image meets its declared alignment. -/
theorem wohlgeformt_ausr (p : Profil) (bild : Bild) (s : Abschnitt)
    (bias : Nat) (hbias : bias = effBias bild.modus)
    (hmem : s ∈ bild.abschnitte) (h : wohlgeformt p bild = true) :
    0 < s.ausr ∧ (bias + s.vaddr) % s.ausr = 0 := by
  have h2 := h
  simp only [wohlgeformt, Bool.and_eq_true] at h2
  have hall : bild.abschnitte.all (ausrOk (effBias bild.modus)) = true :=
    h2.1.1.1.1.1.1.2
  have hs : ausrOk (effBias bild.modus) s = true :=
    (List.all_eq_true.mp hall) s hmem
  rw [← hbias] at hs
  exact of_decide_eq_true hs

/-! ## 2. Fetch from loaded memory: file bytes as fetched prefix.

    The checked map (`abteilFinden` stability, file-backed bounds, execute
    permission, wrap-free window) is the premise; the fetched-byte equality
    over actual `geladen` memory is the derived conclusion. -/

/-- One fetch step: an executable head byte is taken, then fetching
    continues behind it. -/
theorem holeFetchAux_kopf (m : Speicher) (a : Adresse) (off n : Nat)
    (h : m.ausfuehrbar (addrOff a off) = true) :
    holeFetchAux m a off (n + 1) =
      m.bytes (addrOff a off) :: holeFetchAux m a (off + 1) n := by
  simp only [holeFetchAux, h, if_true]

/-- FETCH-INTERIOR (generic): fetching `n` bytes from loaded image memory at
    an interior position yields exactly the mapped file bytes, including
    nonzero file offset (`dateiOff`), base (`vaddr`), bias and interior
    start (`k`). Premises are the checked map: section-relative start,
    a wrap-free window, file-backed extent, stable section lookup and
    execute permission. Data-read permission is never consulted. -/
theorem holeFetchAux_geladen (bild : Bild) (bias : Nat) (rip : Adresse)
    (s : Abschnitt) (off k n : Nat)
    (hrip : rip.toNat = bias + s.vaddr + k)
    (hfree : ∀ i : Nat, i < off + n → (addrOff rip i).toNat = rip.toNat + i)
    (hdatei : k + (off + n) ≤ s.dateiLen)
    (hstab : ∀ i : Nat, i < off + n →
      abteilFinden bild.abschnitte bias (rip.toNat + i) = some s)
    (hexe : ∀ i : Nat, i < off + n →
      (geladen bild bias).ausfuehrbar (addrOff rip i) = true) :
    holeFetchAux (geladen bild bias) rip off n =
      ((List.range' off n).map fun j =>
        dateiByte bild.datei (s.dateiOff + (k + j))) := by
  induction n generalizing off with
  | zero => rfl
  | succ n ih =>
    have hexe0 : (geladen bild bias).ausfuehrbar (addrOff rip off) = true :=
      hexe off (by omega)
    have hr : List.range' off (n + 1) = off :: List.range' (off + 1) n := rfl
    have hhead : (geladen bild bias).bytes (addrOff rip off) =
        dateiByte bild.datei (s.dateiOff + (k + off)) := by
      show ladenByte bild bias (addrOff rip off).toNat = _
      have e1 : (addrOff rip off).toNat = rip.toNat + off :=
        hfree off (by omega)
      have e2 : rip.toNat + off = bias + s.vaddr + (k + off) := by
        rw [hrip]
        omega
      have hfind : abteilFinden bild.abschnitte bias (addrOff rip off).toNat =
          some s := by
        rw [e1]
        exact hstab off (by omega)
      have hhi : (addrOff rip off).toNat < bias + s.vaddr + s.dateiLen := by
        rw [e1, e2]
        omega
      have hbyte := geladenByte_datei bild bias (addrOff rip off).toNat s
        hfind hhi
      have hidx : (addrOff rip off).toNat - (bias + s.vaddr) = k + off := by
        rw [e1, e2]
        omega
      rw [hidx] at hbyte
      exact hbyte
    have htail := ih (off + 1)
      (fun i hi => hfree i (by omega))
      (by omega)
      (fun i hi => hstab i (by omega))
      (fun i hi => hexe i (by omega))
    rw [holeFetchAux_kopf _ _ _ _ hexe0, hr, List.map_cons, hhead, htail]

/-- FETCH-INTERIOR at the state window: the actual 15-byte fetch from a
    loaded image state is the mapped file-byte prefix. -/
theorem geholt_geladen_innen (bild : Bild) (bias : Nat) (rip : Adresse)
    (reg : Register → Wort) (fl : Flags) (s : Abschnitt) (k : Nat)
    (hrip : rip.toNat = bias + s.vaddr + k)
    (hfree : ∀ i : Nat, i < fetchCap → (addrOff rip i).toNat = rip.toNat + i)
    (hdatei : k + fetchCap ≤ s.dateiLen)
    (hstab : ∀ i : Nat, i < fetchCap →
      abteilFinden bild.abschnitte bias (rip.toNat + i) = some s)
    (hexe : ∀ i : Nat, i < fetchCap →
      (geladen bild bias).ausfuehrbar (addrOff rip i) = true) :
    geholt (bildZustand bild bias rip reg fl) =
      ((List.range' 0 fetchCap).map fun j =>
        dateiByte bild.datei (s.dateiOff + (k + j))) := by
  have hwin := holeFetchAux_geladen bild bias rip s 0 k fetchCap hrip
    (fun i hi => hfree i (by omega))
    (by omega)
    (fun i hi => hstab i (by omega))
    (fun i hi => hexe i (by omega))
  unfold geholt
  show holeFetchAux (geladen bild bias) rip 0 fetchCap = _
  exact hwin

/-- FETCH-BSS (generic): fetching inside the zero-defined tail of a loaded
    section yields zero bytes. The window lies past the file-backed part
    (`hlo`) but inside the section (`hstab`); execute permission still
    gates every byte. -/
theorem holeFetchAux_geladen_bss (bild : Bild) (bias : Nat) (rip : Adresse)
    (s : Abschnitt) (off n : Nat)
    (hfree : ∀ i : Nat, i < off + n → (addrOff rip i).toNat = rip.toNat + i)
    (hlo : ∀ i : Nat, i < off + n →
      bias + s.vaddr + s.dateiLen ≤ rip.toNat + i)
    (hstab : ∀ i : Nat, i < off + n →
      abteilFinden bild.abschnitte bias (rip.toNat + i) = some s)
    (hexe : ∀ i : Nat, i < off + n →
      (geladen bild bias).ausfuehrbar (addrOff rip i) = true) :
    holeFetchAux (geladen bild bias) rip off n =
      List.replicate n (BitVec.ofNat 8 0) := by
  induction n generalizing off with
  | zero => rfl
  | succ n ih =>
    have hexe0 : (geladen bild bias).ausfuehrbar (addrOff rip off) = true :=
      hexe off (by omega)
    have hhead : (geladen bild bias).bytes (addrOff rip off) =
        BitVec.ofNat 8 0 := by
      show ladenByte bild bias (addrOff rip off).toNat = _
      have e1 : (addrOff rip off).toNat = rip.toNat + off :=
        hfree off (by omega)
      have hfind : abteilFinden bild.abschnitte bias (addrOff rip off).toNat =
          some s := by
        rw [e1]
        exact hstab off (by omega)
      have hlo0 : bias + s.vaddr + s.dateiLen ≤ (addrOff rip off).toNat := by
        rw [e1]
        exact hlo off (by omega)
      exact geladenByte_bss bild bias (addrOff rip off).toNat s hfind hlo0
    have htail := ih (off + 1)
      (fun i hi => hfree i (by omega))
      (fun i hi => hlo i (by omega))
      (fun i hi => hstab i (by omega))
      (fun i hi => hexe i (by omega))
    rw [holeFetchAux_kopf _ _ _ _ hexe0, List.replicate_succ, hhead, htail]

/-! ## 3. Execute/data permission distinction.

    Fetch consults execute permission only, never data-read permission:
    flipping `lesbar` everywhere changes neither the fetched window nor
    the fetch-and-decode outcome. -/

/-- Fetch is independent of data-read permission. -/
theorem holeFetchAux_lesbar_unabhaengig (m : Speicher) (l : Adresse → Bool)
    (a : Adresse) (off cap : Nat) :
    holeFetchAux { m with lesbar := l } a off cap =
      holeFetchAux m a off cap := by
  induction cap generalizing off with
  | zero => rfl
  | succ n ih =>
    simp only [holeFetchAux, ih]

/-- The state fetch window is independent of data-read permission. -/
theorem geholt_lesbar_unabhaengig (s : Zustand) (l : Adresse → Bool) :
    geholt { s with speicher := { s.speicher with lesbar := l } } =
      geholt s := by
  unfold geholt
  show holeFetchAux { s.speicher with lesbar := l } s.rip 0 fetchCap = _
  exact holeFetchAux_lesbar_unabhaengig s.speicher l s.rip 0 fetchCap

/-- The consumed-prefix execute check is independent of data-read
    permission. -/
theorem ausfuehrbarN_lesbar_unabhaengig (m : Speicher) (l : Adresse → Bool)
    (a : Adresse) (n : Nat) :
    ausfuehrbarN { m with lesbar := l } a n = ausfuehrbarN m a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ausfuehrbarN, ih]

/-- Fetch-and-decode is independent of data-read permission: the whole
    `fetchDekodiert` outcome consults execute permission only. -/
theorem fetchDekodiert_lesbar_unabhaengig (s : Zustand)
    (l : Adresse → Bool) :
    fetchDekodiert { s with speicher := { s.speicher with lesbar := l } } =
      fetchDekodiert s := by
  have hg := geholt_lesbar_unabhaengig s l
  have ha : ∀ d : Decodiert, ausfuehrbarN
      ({ s with speicher := { s.speicher with lesbar := l } } : Zustand).speicher
      ({ s with speicher := { s.speicher with lesbar := l } } : Zustand).rip
        d.laenge =
      ausfuehrbarN s.speicher s.rip d.laenge := by
    intro d
    show ausfuehrbarN { s.speicher with lesbar := l } s.rip d.laenge = _
    exact ausfuehrbarN_lesbar_unabhaengig s.speicher l s.rip d.laenge
  unfold fetchDekodiert
  simp only [hg, ha]

/- CUTS:
   - Skeleton only: the fetch-interior equality, BSS, permission
     distinction, store execution and negative probes are not yet proved.
   - No source refinement claim and no hardware correspondence claim.
-/

#print axioms bildZustand_speicher

end Gabbro.Grammatik.X86
