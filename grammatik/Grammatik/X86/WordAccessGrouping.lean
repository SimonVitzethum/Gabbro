/-
  File:      Grammatik/X86/WordAccessGrouping.lean
  Subject:   Whole-word grouping over actual per-byte TSO drain traces.

  Lane 603: connects actual TSO issue/flush traces (`TSO`), canonical
  word access (`read64`/`write64` over `Speicher`), the LOCK-profile
  guard vocabulary (`WordAtomicity`) and realised footprints
  (`AccessExecution`) for one useful whole-word observation grouping.
  An eight-byte store/flush sequence drains to one unsplit word value
  exactly under a structural exclusion check over the REAL trace
  accesses (exact own eight-entry list plus foreign-footprint freedom
  at every intermediate state). Alignment alone is insufficient: the
  byte drain is alignment-agnostic and an aligned footprint still
  tears under an overlapping foreign entry. No fairness, no LOCK
  source refinement, no multi-byte hardware atomicity claim.
-/
import Grammatik.X86.WordAtomicity
import Grammatik.X86.AccessExecution
import Grammatik.X86.TSOHistory

namespace Gabbro.Grammatik.X86

/-- The eight canonical byte-store entries of word `v` at `a`, oldest
    first: byte `k` sits at `addrOff a k`. A drain trace must carry
    exactly this list on the acting core, in this order. -/
def wortEintraege (a : Adresse) (v : Wort) : List TSOEintrag :=
  [⟨addrOff a 0, wortByte v 0⟩, ⟨addrOff a 1, wortByte v 1⟩,
   ⟨addrOff a 2, wortByte v 2⟩, ⟨addrOff a 3, wortByte v 3⟩,
   ⟨addrOff a 4, wortByte v 4⟩, ⟨addrOff a 5, wortByte v 5⟩,
   ⟨addrOff a 6, wortByte v 6⟩, ⟨addrOff a 7, wortByte v 7⟩]

/-- Foreign-footprint freedom at one state: no other core holds a
    pending entry inside `Fuss a`. Inspects real buffer accesses. -/
def FremdFrei (s : TSOZustand) (c : Nat) (a : Adresse) : Prop :=
  ∀ d : Nat, d ≠ c → ∀ e : TSOEintrag, e ∈ s.puffer d → e.addr ∉ Fuss a

/-- Start-state grouping check: the acting core carries exactly the
    eight canonical entries and no foreign entry touches the
    footprint. Deliberately alignment-free: the byte drain below
    never consults `ausgerichtet8` (see `ausrichtung_reicht_nicht`). -/
def WortGruppe (s : TSOZustand) (c : Nat) (a : Adresse) (v : Wort) : Prop :=
  s.puffer c = wortEintraege a v ∧ FremdFrei s c a

/-- One drain step on the way to a grouped word: an own flush
    (progress), a foreign flush (must avoid the footprint, enforced
    by `FremdFrei`), or a foreign issue (memory-silent). -/
inductive DrainSchritt (c : Nat) : TSOZustand → TSOZustand → Prop where
  | eigen {s s' : TSOZustand} : flushKern s c = some s' → DrainSchritt c s s'
  | fremdSpülen {s s' : TSOZustand} (d : Nat) : d ≠ c →
      flushKern s d = some s' → DrainSchritt c s s'
  | fremdAusgabe {s s' : TSOZustand} (d : Nat) (e : TSOEintrag) : d ≠ c →
      issueByte s d e.addr e.wert = some s' → DrainSchritt c s s'

/-- A drain trace from `s2` to `sN` with its visited states: every
    adjacent pair is one `DrainSchritt`. The exclusion check is stated
    over `t`, the REAL intermediate states, never over a desired
    end state alone. -/
inductive DrainSpur (c : Nat) : TSOZustand → TSOZustand → List TSOZustand → Prop where
  | leer (s) : DrainSpur c s s [s]
  | schritt (s s' sN : TSOZustand) (t : List TSOZustand) :
      DrainSchritt c s s' → DrainSpur c s' sN t → DrainSpur c s sN (s :: t)

/-- The trace head is its start state. -/
theorem drain_kopf (c : Nat) (s sN : TSOZustand) (t : List TSOZustand)
    (h : DrainSpur c s sN t) : t.head? = some s := by
  cases h with
  | leer s => rfl
  | schritt s s' sN t _ _ => rfl

/-- The trace end is visited. -/
theorem drain_end_mem (c : Nat) (s sN : TSOZustand) (t : List TSOZustand)
    (h : DrainSpur c s sN t) : sN ∈ t := by
  induction h with
  | leer s => simp
  | schritt s s' sN t _ _ iht =>
    simp only [List.mem_cons]
    exact Or.inr iht

/-! ## 1. List and footprint facts about the eight canonical entries. -/

/-- Eight entries, no more: the group shape is exact. -/
theorem wortEintraege_laenge (a : Adresse) (v : Wort) :
    (wortEintraege a v).length = 8 := by
  rfl

/-- Footprint membership is an offset below eight. -/
theorem fuss_mem_iff (a x : Adresse) :
    x ∈ Fuss a ↔ ∃ k, k < 8 ∧ addrOff a k = x := by
  rw [← schreibEreignisse_acht a]
  exact schreibEreignisse_mem a x 8

/-- Every footprint address lies in the footprint list. -/
theorem fuss_mem_offset (a : Adresse) (k : Nat) (hk : k < 8) :
    addrOff a k ∈ Fuss a :=
  fuss_mem_iff a _ |>.mpr ⟨k, hk, rfl⟩

/-- Dropping `k < 8` entries exposes byte `k` at the head: the drain
    order is fixed oldest-first. -/
theorem wortEintraege_kopf (a : Adresse) (v : Wort) (k : Nat) (hk : k < 8) :
    (wortEintraege a v).drop k =
      ⟨addrOff a k, wortByte v k⟩ :: (wortEintraege a v).drop (k + 1) := by
  have h8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 := by
    omega
  rcases h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## 2. Drain invariant: the installed prefix only grows. -/

/-- Permission maps survive one drain step: issues and flushes alike
    preserve all three maps. -/
theorem drain_schritt_berechtigungen (c : Nat) (s s' : TSOZustand)
    (h : DrainSchritt c s s') :
    s'.mem.lesbar = s.mem.lesbar ∧ s'.mem.schreibbar = s.mem.schreibbar ∧
      s'.mem.ausfuehrbar = s.mem.ausfuehrbar := by
  cases h with
  | eigen hfl => exact flush_erhaelt_berechtigungen _ _ _ hfl
  | fremdSpülen d hne hfl => exact flush_erhaelt_berechtigungen _ _ _ hfl
  | fremdAusgabe d e hne hfl =>
    exact issue_erhaelt_berechtigungen _ _ _ _ _ hfl

/-- Footprint readability survives the whole drain: every step
    preserves the permission maps. -/
theorem drain_lesbar8_aux (c : Nat) (a : Adresse) (s sN : TSOZustand)
    (t : List TSOZustand) (hspur : DrainSpur c s sN t) :
    ∀ (_hles : lesbar8 s.mem a = true) (x : TSOZustand),
      x ∈ t → lesbar8 x.mem a = true := by
  induction hspur with
  | leer s =>
    intro hles x hx
    simp at hx
    subst hx
    exact hles
  | schritt s s' sN t hstep _ iht =>
    intro hles x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hles
    · have hperm := drain_schritt_berechtigungen c s s' hstep
      have hles' : lesbar8 s'.mem a = true := by
        have e : lesbar8 s'.mem a = lesbar8 s.mem a := by
          unfold lesbar8
          rw [hperm.1]
        rw [e]
        exact hles
      exact iht hles' x hx

/-- Drain invariant, per visited state: from `k` installed bytes the
    trace only advances the installed prefix (`k ≤ k'`), the acting
    buffer holds exactly the rest, and every new byte comes from an
    actual flush. Foreign flushes use `FremdFrei` from the real trace;
    foreign issues are memory-silent; own shape is pinned by the step
    equations themselves. -/
theorem drain_installiert_aux (c : Nat) (a : Adresse) (v : Wort)
    (s sN : TSOZustand) (t : List TSOZustand)
    (hspur : DrainSpur c s sN t) :
    ∀ (hstoer : ∀ x ∈ t, FremdFrei x c a) (k : Nat), k ≤ 8 →
      ∀ (hbuf : s.puffer c = (wortEintraege a v).drop k)
        (hmem : ∀ j : Nat, j < k → s.mem.bytes (addrOff a j) = wortByte v j)
        (x : TSOZustand), x ∈ t →
        ∃ k' : Nat, k ≤ k' ∧ k' ≤ 8 ∧
          x.puffer c = (wortEintraege a v).drop k' ∧
          (∀ j : Nat, j < k' → x.mem.bytes (addrOff a j) = wortByte v j) := by
  induction hspur with
  | leer s =>
    intro hstoer k hk hbuf hmem x hx
    simp at hx
    subst hx
    exact ⟨k, Nat.le_refl k, hk, hbuf, hmem⟩
  | schritt s s' sN t hstep hrest iht =>
    intro hstoer k hk hbuf hmem x hx
    have hstoer' : ∀ y ∈ t, FremdFrei y c a := by
      intro y hy
      exact hstoer y (by simp only [List.mem_cons]; exact Or.inr hy)
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hxt
    · exact ⟨k, Nat.le_refl k, hk, hbuf, hmem⟩
    · match hstep with
      | .eigen hfl =>
        have hk8 : k < 8 := by
          have h8 : k = 8 ∨ k < 8 := by omega
          rcases h8 with rfl | hk8
          · have hempty : s.puffer c = [] := by
              rw [hbuf]
              rfl
            rw [flush_leer s c hempty] at hfl
            cases hfl
          · exact hk8
        have hhead : s.puffer c =
            ⟨addrOff a k, wortByte v k⟩ :: (wortEintraege a v).drop (k + 1) := by
          rw [hbuf]
          exact wortEintraege_kopf a v k hk8
        have hbuf' : s'.puffer c = (wortEintraege a v).drop (k + 1) :=
          flush_entfernt_kopf s s' c hfl _ _ hhead
        have hneu : s'.mem.bytes (addrOff a k) = wortByte v k :=
          flush_schreibt_kopf s s' c hfl _ _ hhead
        have hmem' : ∀ j : Nat, j < k + 1 →
            s'.mem.bytes (addrOff a j) = wortByte v j := by
          intro j hj
          by_cases hjk : j = k
          · subst hjk
            exact hneu
          · have hjk8 : j < 8 := by omega
            have hne : addrOff a j ≠
                (⟨addrOff a k, wortByte v k⟩ : TSOEintrag).addr :=
              addrOff_ne8 hjk8 hk8 hjk
            have hframe : s'.mem.bytes (addrOff a j) =
                s.mem.bytes (addrOff a j) :=
              flush_rahmen s s' c hfl _ _ hhead _ hne
            rw [hframe]
            exact hmem j (by omega)
        obtain ⟨k', hkk', hk'8, hbufN, hmemN⟩ :=
          iht hstoer' (k + 1) (by omega) hbuf' hmem' x hxt
        exact ⟨k', by omega, hk'8, hbufN, hmemN⟩
      | .fremdSpülen d hne hfl =>
        have hown : s'.puffer c = s.puffer c :=
          flush_anderer_kern s s' d hfl (Ne.symm hne)
        have hbuf' : s'.puffer c = (wortEintraege a v).drop k := by
          rw [hown, hbuf]
        match hpd : s.puffer d with
        | [] =>
          have hnone : flushKern s d = none := flush_leer s d hpd
          rw [hnone] at hfl
          cases hfl
        | e :: rest =>
          have hmem_e : e ∈ s.puffer d := hpd ▸ by simp
          have hff : FremdFrei s c a := hstoer s (by simp)
          have hout : e.addr ∉ Fuss a := hff d hne e hmem_e
          have hmem' : ∀ j : Nat, j < k →
              s'.mem.bytes (addrOff a j) = wortByte v j := by
            intro j hj
            have hj8 : j < 8 := by omega
            have hmem_foot : addrOff a j ∈ Fuss a :=
              fuss_mem_offset a j hj8
            have hne_j : addrOff a j ≠ e.addr := by
              intro heq
              exact hout (heq ▸ hmem_foot)
            have hframe : s'.mem.bytes (addrOff a j) =
                s.mem.bytes (addrOff a j) :=
              flush_rahmen s s' d hfl e rest hpd _ hne_j
            rw [hframe]
            exact hmem j hj
          obtain ⟨k', hkk', hk'8, hbufN, hmemN⟩ :=
            iht hstoer' k hk hbuf' hmem' x hxt
          exact ⟨k', hkk', hk'8, hbufN, hmemN⟩
      | .fremdAusgabe d e hne hissue =>
        have hown : s'.puffer c = s.puffer c :=
          issue_anderer_kern s s' d e.addr e.wert hissue (Ne.symm hne)
        have hbuf' : s'.puffer c = (wortEintraege a v).drop k := by
          rw [hown, hbuf]
        have hmem' : ∀ j : Nat, j < k →
            s'.mem.bytes (addrOff a j) = wortByte v j := by
          intro j hj
          have hframe : s'.mem.bytes (addrOff a j) =
              s.mem.bytes (addrOff a j) :=
            issue_kein_speicher s s' d e.addr e.wert hissue _
          rw [hframe]
          exact hmem j hj
        obtain ⟨k', hkk', hk'8, hbufN, hmemN⟩ :=
          iht hstoer' k hk hbuf' hmem' x hxt
        exact ⟨k', hkk', hk'8, hbufN, hmemN⟩

/-! ## 3. Grouped read-back: the drain installs one unsplit word. -/

/-- GROUPED READ-BACK: an exclusion-checked drain from the exact
    eight-entry group installs the whole word unsplit in canonical
    memory. Every premise is used: the group pins the start buffer,
    readability the final load, the trace the installed prefix, end
    membership the witness state, emptiness the full eight, and the
    exclusion check every foreign step along the way. -/
theorem wort_gruppe_liest_zurueck (s2 sN : TSOZustand)
    (t : List TSOZustand) (c : Nat) (a : Adresse) (v : Wort)
    (hgrp : WortGruppe s2 c a v) (hles : lesbar8 s2.mem a = true)
    (hspur : DrainSpur c s2 sN t) (hend : sN ∈ t)
    (hleer : sN.puffer c = []) (hstoer : ∀ x ∈ t, FremdFrei x c a) :
    read64 sN.mem a = some v := by
  obtain ⟨hbufl, _hff⟩ := hgrp
  have hbase : s2.puffer c = (wortEintraege a v).drop 0 := by
    rw [hbufl]
    rfl
  obtain ⟨k, _hk0, _hk8, hbufN, hinst⟩ :=
    drain_installiert_aux c a v s2 sN t hspur hstoer 0 (Nat.zero_le 8)
      hbase (fun j hj => absurd hj (by omega)) sN hend
  have hlen0 : (sN.puffer c).length = 0 := by
    rw [hleer]
    rfl
  rw [hbufN, List.length_drop, wortEintraege_laenge] at hlen0
  have hk_eq : k = 8 := by omega
  subst hk_eq
  have hlesN : lesbar8 sN.mem a = true :=
    drain_lesbar8_aux c a s2 sN t hspur hles sN hend
  have hbytes : readBytes sN.mem a = fun i => wortByte v i.val := by
    funext i
    show sN.mem.bytes (addrOff a i.val) = wortByte v i.val
    exact hinst i.val i.isLt
  unfold read64
  rw [hlesN, hbytes, bytesWort_wortByte, if_pos rfl]

/-! ## 4. Grouped frame: disjoint words survive the drain. -/

/-- Framed footprint bytes survive one drain step: own flushes install
    footprint-`a` members only (disjoint from `b`), foreign flushes
    avoid footprint `b` by the exclusion check, foreign issues are
    memory-silent. The check must cover the framed footprint: a
    foreign flush outside `a` is a real step and may hit `b`. -/
theorem drain_fuss_bleibt_aux (c : Nat) (a b : Adresse)
    (s sN : TSOZustand) (t : List TSOZustand)
    (hspur : DrainSpur c s sN t) :
    ∀ (hstoerB : ∀ x ∈ t, FremdFrei x c b)
      (hdis : Disjunkt a b)
      (hown : ∀ e : TSOEintrag, e ∈ s.puffer c → e.addr ∈ Fuss a)
      (x : TSOZustand), x ∈ t →
      ∀ k : Nat, k < 8 → x.mem.bytes (addrOff b k) = s.mem.bytes (addrOff b k) := by
  induction hspur with
  | leer s =>
    intro hstoerB hdis hown x hx k hk
    simp at hx
    subst hx
    rfl
  | schritt s s' sN t hstep hrest iht =>
    intro hstoerB hdis hown x hx k hk
    have hstoerB' : ∀ z ∈ t, FremdFrei z c b := by
      intro z hz
      exact hstoerB z (by simp only [List.mem_cons]; exact Or.inr hz)
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hxt
    · rfl
    · match hstep with
      | .eigen hfl =>
        match hpd : s.puffer c with
        | [] =>
          have hnone : flushKern s c = none := flush_leer s c hpd
          rw [hnone] at hfl
          cases hfl
        | e :: rest =>
          have he_foot : e.addr ∈ Fuss a := hown e (hpd ▸ by simp)
          obtain ⟨j, hj8, hj⟩ := (fuss_mem_iff a _).mp he_foot
          have hne : addrOff b k ≠ e.addr := by
            rw [← hj]
            exact Ne.symm (hdis j k hj8 hk)
          have hframe : s'.mem.bytes (addrOff b k) =
              s.mem.bytes (addrOff b k) :=
            flush_rahmen s s' c hfl e rest hpd _ hne
          have htail : s'.puffer c = rest :=
            flush_entfernt_kopf s s' c hfl e rest hpd
          have hown' : ∀ e' : TSOEintrag, e' ∈ s'.puffer c → e'.addr ∈ Fuss a := by
            intro e' he'
            rw [htail] at he'
            exact hown e' (hpd ▸ by simp only [List.mem_cons]; exact Or.inr he')
          have hweiter := iht hstoerB' hdis hown' x hxt k hk
          rw [hweiter]
          exact hframe
      | .fremdSpülen d hne hfl =>
        have hown_buf : s'.puffer c = s.puffer c :=
          flush_anderer_kern s s' d hfl (Ne.symm hne)
        have hown' : ∀ e' : TSOEintrag, e' ∈ s'.puffer c → e'.addr ∈ Fuss a := by
          intro e' he'
          rw [hown_buf] at he'
          exact hown e' he'
        match hpd : s.puffer d with
        | [] =>
          have hnone : flushKern s d = none := flush_leer s d hpd
          rw [hnone] at hfl
          cases hfl
        | e :: rest =>
          have hmem_e : e ∈ s.puffer d := hpd ▸ by simp
          have hff : FremdFrei s c b := hstoerB s (by simp)
          have hout : e.addr ∉ Fuss b := hff d hne e hmem_e
          have hmem_foot : addrOff b k ∈ Fuss b := fuss_mem_offset b k hk
          have hne_y : addrOff b k ≠ e.addr := by
            intro heq
            exact hout (heq ▸ hmem_foot)
          have hframe : s'.mem.bytes (addrOff b k) =
              s.mem.bytes (addrOff b k) :=
            flush_rahmen s s' d hfl e rest hpd _ hne_y
          have hweiter := iht hstoerB' hdis hown' x hxt k hk
          rw [hweiter]
          exact hframe
      | .fremdAusgabe d e hne hissue =>
        have hown_buf : s'.puffer c = s.puffer c :=
          issue_anderer_kern s s' d e.addr e.wert hissue (Ne.symm hne)
        have hown' : ∀ e' : TSOEintrag, e' ∈ s'.puffer c → e'.addr ∈ Fuss a := by
          intro e' he'
          rw [hown_buf] at he'
          exact hown e' he'
        have hframe : s'.mem.bytes (addrOff b k) =
            s.mem.bytes (addrOff b k) :=
          issue_kein_speicher s s' d e.addr e.wert hissue _
        have hweiter := iht hstoerB' hdis hown' x hxt k hk
        rw [hweiter]
        exact hframe

/-- GROUPED FRAME: a disjoint word observation survives the whole
    drain. The group shape makes every own entry a footprint-`a`
    member; disjointness separates the words; the exclusion check
    must also cover the framed footprint, since foreign flushes
    elsewhere in the trace are real steps. Readability follows
    the drain. -/
theorem wort_gruppe_rahmen (s2 sN : TSOZustand) (t : List TSOZustand)
    (c : Nat) (a b : Adresse) (v old : Wort)
    (hgrp : WortGruppe s2 c a v) (hdis : Disjunkt a b)
    (hread : read64 s2.mem b = some old)
    (hspur : DrainSpur c s2 sN t) (hend : sN ∈ t)
    (hstoerB : ∀ x ∈ t, FremdFrei x c b) :
    read64 sN.mem b = some old := by
  obtain ⟨hbufl, _hff⟩ := hgrp
  have hown : ∀ e : TSOEintrag, e ∈ s2.puffer c → e.addr ∈ Fuss a := by
    intro e he
    rw [hbufl] at he
    simp only [wortEintraege, List.mem_cons, List.not_mem_nil,
      or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fuss_mem_offset a 0 (by decide)
    · exact fuss_mem_offset a 1 (by decide)
    · exact fuss_mem_offset a 2 (by decide)
    · exact fuss_mem_offset a 3 (by decide)
    · exact fuss_mem_offset a 4 (by decide)
    · exact fuss_mem_offset a 5 (by decide)
    · exact fuss_mem_offset a 6 (by decide)
    · exact fuss_mem_offset a 7 (by decide)
  have hbytes : ∀ k : Nat, k < 8 →
      sN.mem.bytes (addrOff b k) = s2.mem.bytes (addrOff b k) :=
    fun k hk =>
      drain_fuss_bleibt_aux c a b s2 sN t hspur hstoerB hdis hown sN hend k hk
  have hlesB : lesbar8 s2.mem b = true :=
    read64_braucht_lesbar s2.mem b old hread
  have hlesBN : lesbar8 sN.mem b = true :=
    drain_lesbar8_aux c b s2 sN t hspur hlesB sN hend
  have hbytesF : readBytes sN.mem b = readBytes s2.mem b := by
    funext i
    show sN.mem.bytes (addrOff b i.val) = s2.mem.bytes (addrOff b i.val)
    exact hbytes i.val i.isLt
  have hlesEq : lesbar8 sN.mem b = lesbar8 s2.mem b := by
    rw [hlesB, hlesBN]
  have hreadN : read64 sN.mem b = read64 s2.mem b := by
    unfold read64
    rw [hlesEq, hbytesF]
  rw [hreadN]
  exact hread

/-! ## 5. AccessExecution link: realised stores write group bytes. -/

/-- REALISED-STORE GROUP FIDELITY: a realised `store64` step installs
    exactly the canonical group bytes in post-state memory — every
    footprint byte holds the little-endian byte of the stored word.
    The realised step pins word and footprint (AccessExecution); the
    byte values are this module's group entries. -/
theorem realisiert_store_gruppe_treu (dd : Decodiert) (s s' : Zustand)
    (base src : Register) (disp : BitVec 32)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .store64 base src disp)
    (hstep : istRealisiert dd s s') (k : Nat) (hk : k < 8) :
    s'.speicher.bytes (addrOff (effAddr s base disp) k) =
      wortByte (s.register src) k := by
  have hex := realisiert_store64_gefunden dd s s' base src disp hok h hstep
  obtain ⟨m, hwr, _hperm1, _hperm2, _hperm3⟩ := hex
  have hstep' : s' = { s with speicher := m, rip := ripNach s.rip dd.laenge } := by
    have heq := schritt_store64_erfolg dd s base src disp m hok h hwr
    unfold istRealisiert at hstep
    rw [heq] at hstep
    exact (Option.some.inj hstep).symm
  have hhit : m.bytes (addrOff (effAddr s base disp) k) =
      wortByte (s.register src) k := by
    have hwrU : write64 s.speicher (effAddr s base disp) (s.register src) =
        some m := hwr
    unfold write64 at hwrU
    by_cases hc : schreibbar8 s.speicher (effAddr s base disp) = true
    · rw [if_pos hc] at hwrU
      cases hwrU
      show writeBytes s.speicher (effAddr s base disp) (s.register src)
        (addrOff (effAddr s base disp) k) = wortByte (s.register src) k
      unfold writeBytes
      exact writeBytesN_hit _ _ _ _ k (by omega) (by omega)
    · rw [if_neg hc] at hwrU
      cases hwrU
  rw [hstep']
  exact hhit

/-- The group entries sit exactly on the realised footprint: entry
    addresses are the `Fuss` list every realised store carries. -/
theorem gruppe_fuss_form (a : Adresse) (v : Wort) :
    (wortEintraege a v).map TSOEintrag.addr = Fuss a := by
  rfl

/-! ## 6. Tearing refusal: alignment alone is insufficient. -/

/-- ALIGNMENT IS NOT ENOUGH (refused): address zero is aligned, yet
    core 0's two-entry buffer is no eight-entry group — the
    structural check refuses what alignment admits. The witness
    buffer is the real `hS2` state both TSO lanes share. -/
theorem ausrichtung_reicht_nicht :
    ausgerichtet8 (0 : Adresse) = true ∧
      ¬ WortGruppe hS2 0 (0 : Adresse) zeugenWort := by
  refine ⟨by decide, ?_⟩
  intro hgrp
  obtain ⟨hbufl, _hff⟩ := hgrp
  have hlen := congrArg List.length hbufl
  rw [wortEintraege_laenge] at hlen
  have h2 : (hS2.puffer 0).length = 2 := by rfl
  omega

/-- TEARING UNDER THE REFUSED CHECK: the same aligned two-entry
    buffer flushes one byte at a time — after the first flush the
    first byte is new while the second still reads the pre-flush
    byte, and memory observably changed. No unsplit word emerges. -/
theorem riss_unter_verweigerter_gruppe :
    ∃ s3 : TSOZustand, flushKern hS2 0 = some s3 ∧
      s3.mem.bytes sbX = sbEins ∧ s3.mem.bytes sbY = hS2.mem.bytes sbY ∧
      hS2.mem.bytes sbX ≠ s3.mem.bytes sbX := by
  exact ⟨hS3, h_flush, hist_zerreissen.1, hist_zerreissen.2, by decide⟩

/-! ## 7. Reachability, separation, and the joint witness. -/

/-- Every drain step is a real TSO step: own and foreign flushes are
    flushes, foreign issues are issues. -/
theorem drain_schritt_ist_tso (c : Nat) (s s' : TSOZustand)
    (h : DrainSchritt c s s') : TSOSchritt s s' := by
  cases h with
  | eigen hfl => exact .flush s s' c hfl
  | fremdSpülen d hne hfl => exact .flush s s' d hfl
  | fremdAusgabe d e hne hissue =>
    exact .issue s s' d e.addr e.wert hissue

/-- Reached runs compose: transitivity of `TSOErreichbar`. -/
theorem tsoErreichbar_trans {s0 s1 s2 : TSOZustand}
    (h1 : TSOErreichbar s0 s1) (h2 : TSOErreichbar s1 s2) :
    TSOErreichbar s0 s2 := by
  induction h2 with
  | start => exact h1
  | schritt _ hstep iht => exact .schritt iht hstep

/-- A drain trace is a reached TSO run from its start state. -/
theorem drain_spur_erreichbar (c : Nat) (s sN : TSOZustand)
    (t : List TSOZustand) (hspur : DrainSpur c s sN t) :
    TSOErreichbar s sN := by
  induction hspur with
  | leer s => exact .start
  | schritt s s' sN t hstep _ iht =>
    exact tsoErreichbar_trans
      (.schritt .start (drain_schritt_ist_tso c s s' hstep)) iht

/-- A grouped state admits no LOCK step on the acting core: the LOCK
    form needs the empty buffer the group fills. Byte drains and LOCK
    updates never coincide — the WordAtomicity guard stays the only
    whole-word atomic path. -/
theorem gruppe_verweigert_lock (s : TSOZustand) (c : Nat) (a : Adresse)
    (v : Wort) (delta : Wort) (hgrp : WortGruppe s c a v) :
    lockSchritt (.xadd64 a delta) c s = none := by
  obtain ⟨hbufl, _hff⟩ := hgrp
  have hne : s.puffer c ≠ [] := by
    rw [hbufl]
    intro hcon
    have hlen := congrArg List.length hcon
    rw [wortEintraege_laenge] at hlen
    simp at hlen
  exact lock_verweigert_bei_vollem_puffer s c a delta hne

/-- No per-access refinement of the byte drain into a source model is
    proved here: the type of such a claim is empty. The typed-carrier
    W bridge owns it. -/
inductive GruppeNachW : TSOZustand → Prop

/-- Every source-bridge claim is void inside this module. -/
theorem keine_gruppe_nach_w (s : TSOZustand) : ¬ GruppeNachW s := by
  intro h
  cases h

/-- One own-flush preserves every foreign buffer. -/
theorem eigen_fremd_gleich (s s' : TSOZustand)
    (hfl : flushKern s 0 = some s') (d : Nat) (hne : d ≠ 0) :
    s'.puffer d = s.puffer d :=
  flush_anderer_kern s s' 0 hfl hne

/-- Foreign-buffer emptiness transfers across one own-flush. -/
theorem fremd_leer_eigen_erhalten (s s' : TSOZustand)
    (hfl : flushKern s 0 = some s')
    (hleer : ∀ d : Nat, d ≠ 0 → s.puffer d = []) :
    ∀ d : Nat, d ≠ 0 → s'.puffer d = [] := by
  intro d hne
  rw [eigen_fremd_gleich s s' hfl d hne]
  exact hleer d hne

/-- Empty foreign buffers satisfy the exclusion check at any address. -/
theorem fremdFrei_aus_leer (s : TSOZustand) (c : Nat) (b : Adresse)
    (hleer : ∀ d : Nat, d ≠ c → s.puffer d = []) :
    FremdFrei s c b := by
  intro d hne e he
  rw [hleer d hne] at he
  simp at he

/-! ## 8. Joint witness: a reached memory-changing eight-drain. -/

/-- Witness word address: zero (aligned). -/
def grpA : Adresse := 0

/-- Witness start: zeroed fully-permissive memory, core 0 carries the
    exact eight-entry group for `zeugenWort` at address zero, all
    other buffers empty. -/
def grpS2 : TSOZustand :=
  ⟨zeugenSpeicher,
    fun d => if d = 0 then wortEintraege (0 : Adresse) zeugenWort else []⟩

/-- After own flush 1: byte 0 installed. -/
def grpS3 : TSOZustand :=
  ⟨{ zeugenSpeicher with bytes := fun x =>
      if (x = addrOff grpA 0) then wortByte zeugenWort 0
      else zeugenSpeicher.bytes x },
    pufferSetze grpS2.puffer 0 ((wortEintraege (0 : Adresse) zeugenWort).drop 1)⟩

/-- After own flush 2: bytes 0–1 installed. -/
def grpS4 : TSOZustand :=
  ⟨{ grpS3.mem with bytes := fun x =>
      if (x = addrOff grpA 1) then wortByte zeugenWort 1
      else grpS3.mem.bytes x },
    pufferSetze grpS3.puffer 0 ((wortEintraege (0 : Adresse) zeugenWort).drop 2)⟩

/-- After own flush 3: bytes 0–2 installed. -/
def grpS5 : TSOZustand :=
  ⟨{ grpS4.mem with bytes := fun x =>
      if (x = addrOff grpA 2) then wortByte zeugenWort 2
      else grpS4.mem.bytes x },
    pufferSetze grpS4.puffer 0 ((wortEintraege (0 : Adresse) zeugenWort).drop 3)⟩

/-- After own flush 4: bytes 0–3 installed. -/
def grpS6 : TSOZustand :=
  ⟨{ grpS5.mem with bytes := fun x =>
      if (x = addrOff grpA 3) then wortByte zeugenWort 3
      else grpS5.mem.bytes x },
    pufferSetze grpS5.puffer 0 ((wortEintraege (0 : Adresse) zeugenWort).drop 4)⟩

/-- After own flush 5: bytes 0–4 installed. -/
def grpS7 : TSOZustand :=
  ⟨{ grpS6.mem with bytes := fun x =>
      if (x = addrOff grpA 4) then wortByte zeugenWort 4
      else grpS6.mem.bytes x },
    pufferSetze grpS6.puffer 0 ((wortEintraege (0 : Adresse) zeugenWort).drop 5)⟩

/-- After own flush 6: bytes 0–5 installed. -/
def grpS8 : TSOZustand :=
  ⟨{ grpS7.mem with bytes := fun x =>
      if (x = addrOff grpA 5) then wortByte zeugenWort 5
      else grpS7.mem.bytes x },
    pufferSetze grpS7.puffer 0 ((wortEintraege (0 : Adresse) zeugenWort).drop 6)⟩

/-- After own flush 7: bytes 0–6 installed. -/
def grpS9 : TSOZustand :=
  ⟨{ grpS8.mem with bytes := fun x =>
      if (x = addrOff grpA 6) then wortByte zeugenWort 6
      else grpS8.mem.bytes x },
    pufferSetze grpS8.puffer 0 ((wortEintraege (0 : Adresse) zeugenWort).drop 7)⟩

/-- After own flush 8: all bytes installed, own buffer empty. -/
def grpS10 : TSOZustand :=
  ⟨{ grpS9.mem with bytes := fun x =>
      if (x = addrOff grpA 7) then wortByte zeugenWort 7
      else grpS9.mem.bytes x },
    pufferSetze grpS9.puffer 0 ((wortEintraege (0 : Adresse) zeugenWort).drop 8)⟩

/-- Each recorded flush computes as claimed. -/
theorem grp_step1 : flushKern grpS2 0 = some grpS3 := by rfl

theorem grp_step2 : flushKern grpS3 0 = some grpS4 := by rfl

theorem grp_step3 : flushKern grpS4 0 = some grpS5 := by rfl

theorem grp_step4 : flushKern grpS5 0 = some grpS6 := by rfl

theorem grp_step5 : flushKern grpS6 0 = some grpS7 := by rfl

theorem grp_step6 : flushKern grpS7 0 = some grpS8 := by rfl

theorem grp_step7 : flushKern grpS8 0 = some grpS9 := by rfl

theorem grp_step8 : flushKern grpS9 0 = some grpS10 := by rfl

/-- Foreign buffers start empty off core 0. -/
theorem grpS2_fremd_leer : ∀ d : Nat, d ≠ 0 → grpS2.puffer d = [] := by
  intro d hne
  show (if d = 0 then wortEintraege (0 : Adresse) zeugenWort else []) = []
  rw [if_neg hne]

/-- Foreign-buffer emptiness down the whole drain. -/
theorem grpS3_fremd_leer : ∀ d : Nat, d ≠ 0 → grpS3.puffer d = [] :=
  fremd_leer_eigen_erhalten grpS2 grpS3 grp_step1 grpS2_fremd_leer

theorem grpS4_fremd_leer : ∀ d : Nat, d ≠ 0 → grpS4.puffer d = [] :=
  fremd_leer_eigen_erhalten grpS3 grpS4 grp_step2 grpS3_fremd_leer

theorem grpS5_fremd_leer : ∀ d : Nat, d ≠ 0 → grpS5.puffer d = [] :=
  fremd_leer_eigen_erhalten grpS4 grpS5 grp_step3 grpS4_fremd_leer

theorem grpS6_fremd_leer : ∀ d : Nat, d ≠ 0 → grpS6.puffer d = [] :=
  fremd_leer_eigen_erhalten grpS5 grpS6 grp_step4 grpS5_fremd_leer

theorem grpS7_fremd_leer : ∀ d : Nat, d ≠ 0 → grpS7.puffer d = [] :=
  fremd_leer_eigen_erhalten grpS6 grpS7 grp_step5 grpS6_fremd_leer

theorem grpS8_fremd_leer : ∀ d : Nat, d ≠ 0 → grpS8.puffer d = [] :=
  fremd_leer_eigen_erhalten grpS7 grpS8 grp_step6 grpS7_fremd_leer

theorem grpS9_fremd_leer : ∀ d : Nat, d ≠ 0 → grpS9.puffer d = [] :=
  fremd_leer_eigen_erhalten grpS8 grpS9 grp_step7 grpS8_fremd_leer

theorem grpS10_fremd_leer : ∀ d : Nat, d ≠ 0 → grpS10.puffer d = [] :=
  fremd_leer_eigen_erhalten grpS9 grpS10 grp_step8 grpS9_fremd_leer

/-- Every visited state is foreign-free at the grouped footprint. -/
theorem grp_ff2 : FremdFrei grpS2 0 0 :=
  fremdFrei_aus_leer grpS2 0 0 grpS2_fremd_leer

theorem grp_ff3 : FremdFrei grpS3 0 0 :=
  fremdFrei_aus_leer grpS3 0 0 grpS3_fremd_leer

theorem grp_ff4 : FremdFrei grpS4 0 0 :=
  fremdFrei_aus_leer grpS4 0 0 grpS4_fremd_leer

theorem grp_ff5 : FremdFrei grpS5 0 0 :=
  fremdFrei_aus_leer grpS5 0 0 grpS5_fremd_leer

theorem grp_ff6 : FremdFrei grpS6 0 0 :=
  fremdFrei_aus_leer grpS6 0 0 grpS6_fremd_leer

theorem grp_ff7 : FremdFrei grpS7 0 0 :=
  fremdFrei_aus_leer grpS7 0 0 grpS7_fremd_leer

theorem grp_ff8 : FremdFrei grpS8 0 0 :=
  fremdFrei_aus_leer grpS8 0 0 grpS8_fremd_leer

theorem grp_ff9 : FremdFrei grpS9 0 0 :=
  fremdFrei_aus_leer grpS9 0 0 grpS9_fremd_leer

theorem grp_ff10 : FremdFrei grpS10 0 0 :=
  fremdFrei_aus_leer grpS10 0 0 grpS10_fremd_leer

/-- Every visited state is foreign-free at the framed footprint. -/
theorem grp_ffB2 : FremdFrei grpS2 0 (BitVec.ofNat 64 8192) :=
  fremdFrei_aus_leer grpS2 0 _ grpS2_fremd_leer

theorem grp_ffB3 : FremdFrei grpS3 0 (BitVec.ofNat 64 8192) :=
  fremdFrei_aus_leer grpS3 0 _ grpS3_fremd_leer

theorem grp_ffB4 : FremdFrei grpS4 0 (BitVec.ofNat 64 8192) :=
  fremdFrei_aus_leer grpS4 0 _ grpS4_fremd_leer

theorem grp_ffB5 : FremdFrei grpS5 0 (BitVec.ofNat 64 8192) :=
  fremdFrei_aus_leer grpS5 0 _ grpS5_fremd_leer

theorem grp_ffB6 : FremdFrei grpS6 0 (BitVec.ofNat 64 8192) :=
  fremdFrei_aus_leer grpS6 0 _ grpS6_fremd_leer

theorem grp_ffB7 : FremdFrei grpS7 0 (BitVec.ofNat 64 8192) :=
  fremdFrei_aus_leer grpS7 0 _ grpS7_fremd_leer

theorem grp_ffB8 : FremdFrei grpS8 0 (BitVec.ofNat 64 8192) :=
  fremdFrei_aus_leer grpS8 0 _ grpS8_fremd_leer

theorem grp_ffB9 : FremdFrei grpS9 0 (BitVec.ofNat 64 8192) :=
  fremdFrei_aus_leer grpS9 0 _ grpS9_fremd_leer

theorem grp_ffB10 : FremdFrei grpS10 0 (BitVec.ofNat 64 8192) :=
  fremdFrei_aus_leer grpS10 0 _ grpS10_fremd_leer

/-- The witness start satisfies the grouping check. -/
theorem grp_hgrp : WortGruppe grpS2 0 (0 : Adresse) zeugenWort :=
  ⟨rfl, grp_ff2⟩

/-- Each recorded step is an own-flush drain step. -/
theorem grp_e1 : DrainSchritt 0 grpS2 grpS3 := .eigen grp_step1

theorem grp_e2 : DrainSchritt 0 grpS3 grpS4 := .eigen grp_step2

theorem grp_e3 : DrainSchritt 0 grpS4 grpS5 := .eigen grp_step3

theorem grp_e4 : DrainSchritt 0 grpS5 grpS6 := .eigen grp_step4

theorem grp_e5 : DrainSchritt 0 grpS6 grpS7 := .eigen grp_step5

theorem grp_e6 : DrainSchritt 0 grpS7 grpS8 := .eigen grp_step6

theorem grp_e7 : DrainSchritt 0 grpS8 grpS9 := .eigen grp_step7

theorem grp_e8 : DrainSchritt 0 grpS9 grpS10 := .eigen grp_step8

/-- The full eight-drain trace. -/
theorem grp_spur : DrainSpur 0 grpS2 grpS10
    [grpS2, grpS3, grpS4, grpS5, grpS6, grpS7, grpS8, grpS9, grpS10] :=
  .schritt _ _ _ _ grp_e1 (.schritt _ _ _ _ grp_e2 (.schritt _ _ _ _ grp_e3
    (.schritt _ _ _ _ grp_e4 (.schritt _ _ _ _ grp_e5 (.schritt _ _ _ _ grp_e6
      (.schritt _ _ _ _ grp_e7 (.schritt _ _ _ _ grp_e8
        (.leer grpS10))))))))

/-- The drain end is visited. -/
theorem grp_hend :
    grpS10 ∈ [grpS2, grpS3, grpS4, grpS5, grpS6, grpS7, grpS8, grpS9, grpS10] := by
  simp

/-- The drain ends with an empty own buffer. -/
theorem grp_hempty : grpS10.puffer 0 = [] := by rfl

/-- The witness start reads the grouped footprint. -/
theorem grp_hles : lesbar8 grpS2.mem (0 : Adresse) = true := by rfl

/-- The whole trace is foreign-free at the grouped footprint. -/
theorem grp_hstoer :
    ∀ x ∈ [grpS2, grpS3, grpS4, grpS5, grpS6, grpS7, grpS8, grpS9, grpS10],
      FremdFrei x 0 0 := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact grp_ff2
  · exact grp_ff3
  · exact grp_ff4
  · exact grp_ff5
  · exact grp_ff6
  · exact grp_ff7
  · exact grp_ff8
  · exact grp_ff9
  · exact grp_ff10

/-- The whole trace is foreign-free at the framed footprint. -/
theorem grp_hstoerB :
    ∀ x ∈ [grpS2, grpS3, grpS4, grpS5, grpS6, grpS7, grpS8, grpS9, grpS10],
      FremdFrei x 0 (BitVec.ofNat 64 8192) := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact grp_ffB2
  · exact grp_ffB3
  · exact grp_ffB4
  · exact grp_ffB5
  · exact grp_ffB6
  · exact grp_ffB7
  · exact grp_ffB8
  · exact grp_ffB9
  · exact grp_ffB10

/-- JOINT WITNESS for the grouped read-back: eight real flushes from
    the exact group reach an empty buffer; every visited state is
    foreign-free; the word reads back whole; the run is reached and
    memory observably changed (byte 0 went from 0 to 0x08). -/
theorem wort_gruppe_liest_zurueck_zeuge :
    ∃ (t : List TSOZustand) (sN : TSOZustand),
      DrainSpur 0 grpS2 sN t ∧ TSOErreichbar grpS2 sN ∧
      sN.puffer 0 = [] ∧ (∀ x ∈ t, FremdFrei x 0 0) ∧
      lesbar8 grpS2.mem 0 = true ∧
      read64 sN.mem 0 = some zeugenWort ∧
      grpS2.mem.bytes 0 ≠ sN.mem.bytes 0 := by
  have hread := wort_gruppe_liest_zurueck grpS2 grpS10 _ 0 0 zeugenWort
    grp_hgrp grp_hles grp_spur grp_hend grp_hempty grp_hstoer
  exact ⟨_, _, grp_spur, drain_spur_erreichbar 0 grpS2 grpS10 _ grp_spur,
    grp_hempty, grp_hstoer, grp_hles, hread, by decide⟩

/-- JOINT WITNESS for the grouped frame: the same reached drain
    preserves the distant word (still 0) while changing the grouped
    word's bytes. -/
theorem wort_gruppe_rahmen_zeuge :
    Disjunkt (0 : Adresse) (BitVec.ofNat 64 8192) ∧
    read64 grpS2.mem (BitVec.ofNat 64 8192) = some 0 ∧
    read64 grpS10.mem (BitVec.ofNat 64 8192) = some 0 ∧
    grpS2.mem.bytes 0 ≠ grpS10.mem.bytes 0 := by
  have hA : OhneUmbruch (0 : Adresse) := by
    unfold OhneUmbruch
    decide
  have hB : OhneUmbruch (BitVec.ofNat 64 8192) := by
    unfold OhneUmbruch
    decide
  have hle : (0 : Adresse).toNat + 8 ≤ (BitVec.ofNat 64 8192).toNat := by decide
  have hdis : Disjunkt (0 : Adresse) (BitVec.ofNat 64 8192) :=
    disjunkt_von_intervallen _ _ hA hB (Or.inl hle)
  have hread0 : read64 grpS2.mem (BitVec.ofNat 64 8192) = some 0 := by decide
  have hframe := wort_gruppe_rahmen grpS2 grpS10 _ 0 _ _ zeugenWort 0
    grp_hgrp hdis hread0 grp_spur grp_hend grp_hstoerB
  exact ⟨hdis, hread0, hframe, by decide⟩

/- CUTS:
     - Proved here: whole-word grouping over actual per-byte TSO
       drain traces. `WortGruppe` (exact own eight-entry list) plus
       `FremdFrei` at every visited trace state is the structural
       exclusion check over real trace accesses — no source-simulation
       premise anywhere. §3 read-back installs one unsplit word;
       §4 frame preserves disjoint words (the check must also cover
       the framed footprint, since foreign flushes are real steps);
       §5 ties realised `store64` steps to group bytes and the
       footprint shape; §6 refuses an aligned non-group and shows it
       tearing; §7 reaches a memory-changing eight-drain jointly for
       read-back and frame; LOCK steps are refused on grouped states
       and no source bridge is claimed (`GruppeNachW` empty).
     - NOT proved here, and not claimed:
       - No multi-byte hardware atomicity: the drain passes through
         eight visible intermediate states; aligned grouping is a
         software observation discipline, not a silicon guarantee.
       - No source correspondence: nothing links Gabbro source, IR,
         checker verdicts or contracts to these traces; no entry,
         ABI, loader, relocation, image-layout or cost claim.
       - No per-access W/GX simulation, no typed-carrier bridge:
         `keine_gruppe_nach_w` states the gap; consumers BridgeWrite
         and BridgeRead own it.
       - No fairness, progress, timing or liveness claim; fences only
         gate (`zaunBereit` reused through `TSO`); no interrupt,
         device, MMIO or DMA model.
       - No LOCK source refinement: `gruppe_verweigert_lock` keeps
         the LOCK path disjoint; WordAtomicity owns it.
       - Axioms stay within the standard goal set
         (propext, Classical.choice, Quot.sound).
       - Consumer interface: downstream lanes cite
         `wort_gruppe_liest_zurueck` (read-back),
         `wort_gruppe_rahmen` (frame),
         `realisiert_store_gruppe_treu` (store-to-group fidelity),
         `gruppe_fuss_form` (entry/footprint shape),
         `ausrichtung_reicht_nicht` plus
         `riss_unter_verweigerter_gruppe` (alignment insufficiency),
         and the two `_zeuge` witnesses (joint inhabitation).
-/

#print axioms wortEintraege
#print axioms FremdFrei
#print axioms WortGruppe
#print axioms drain_kopf
#print axioms drain_end_mem
#print axioms wortEintraege_laenge
#print axioms fuss_mem_iff
#print axioms fuss_mem_offset
#print axioms wortEintraege_kopf
#print axioms drain_schritt_berechtigungen
#print axioms drain_lesbar8_aux
#print axioms drain_installiert_aux
#print axioms wort_gruppe_liest_zurueck
#print axioms drain_fuss_bleibt_aux
#print axioms wort_gruppe_rahmen
#print axioms realisiert_store_gruppe_treu
#print axioms gruppe_fuss_form
#print axioms ausrichtung_reicht_nicht
#print axioms riss_unter_verweigerter_gruppe
#print axioms drain_schritt_ist_tso
#print axioms tsoErreichbar_trans
#print axioms drain_spur_erreichbar
#print axioms gruppe_verweigert_lock
#print axioms keine_gruppe_nach_w
#print axioms eigen_fremd_gleich
#print axioms fremd_leer_eigen_erhalten
#print axioms fremdFrei_aus_leer
#print axioms grp_step1
#print axioms grp_step8
#print axioms grpS2_fremd_leer
#print axioms grpS10_fremd_leer
#print axioms grp_ff2
#print axioms grp_ff10
#print axioms grp_ffB2
#print axioms grp_ffB10
#print axioms grp_hgrp
#print axioms grp_e1
#print axioms grp_spur
#print axioms grp_hend
#print axioms grp_hempty
#print axioms grp_hles
#print axioms grp_hstoer
#print axioms grp_hstoerB
#print axioms wort_gruppe_liest_zurueck_zeuge
#print axioms wort_gruppe_rahmen_zeuge

end Gabbro.Grammatik.X86
