/-
  File:      Grammatik/X86/ComposeMapPerms.lean
  Subject:   Composition closing: final loaded mapping to per-address R/W/X bits.

  Lane 847: closes the final loaded mapping (`Bild.geladen` from a
  `valX86`-accepted image) to per-address R/W/X permission bits for every
  executed byte, permission-checked access composed end to end.

  Producer/consumer interface: producers are `valX86` (mapping AND decode
  coverage admission), `geladen` with `ladenLesbar`/`ladenSchreibbar`/
  `ladenAusfuehrbar` (loaded bytes and permissions), `fetchDekodiert`
  (X-gated fetch from actual memory), `zugriff` (potential footprint) and
  `schritt` (realised step); the consumer is the single checked closing
  step `ComposeMapPerms_verbindung` below. Accepted modules are reused by
  name; their internals are never re-proved and no interpreter or executor
  is duplicated.
-/
import Grammatik.X86.Bild
import Grammatik.X86.Byteschritt
import Grammatik.X86.Zugriffe
import Grammatik.X86.ValidatorSkeleton

namespace Gabbro.Grammatik.X86

/-- Read-permission check of one extracted access: every read address readable. -/
def zugriffLesbar (m : Speicher) (z : Zugriff) : Bool :=
  z.lesen.all m.lesbar

/-- Write-permission check of one extracted access: every written address writable. -/
def zugriffSchreibbar (m : Speicher) (z : Zugriff) : Bool :=
  z.schreiben.all m.schreibbar

/-! ## 1. Read/write success carries the eight-byte permission check. -/

/-- A successful 64-bit read carries read permission for all eight bytes. -/
theorem read64_lesbar8 (m : Speicher) (a : Adresse) (v : Wort)
    (h : read64 m a = some v) : lesbar8 m a = true := by
  unfold read64 at h
  by_cases hc : lesbar8 m a = true
  · exact hc
  · rw [if_neg hc] at h
    cases h

/-- A successful 64-bit write carries write permission for all eight bytes. -/
theorem write64_schreibbar8 (m : Speicher) (a : Adresse) (v : Wort)
    (m' : Speicher) (h : write64 m a v = some m') :
    schreibbar8 m a = true := by
  unfold write64 at h
  by_cases hc : schreibbar8 m a = true
  · exact hc
  · rw [if_neg hc] at h
    cases h

/-- Every footprint address is readable when the eight-byte check holds. -/
theorem fuss_all_lesbar (m : Speicher) (a : Adresse)
    (h : lesbar8 m a = true) : (Fuss a).all m.lesbar = true := by
  have h2 := h
  simp only [lesbar8, Bool.and_eq_true] at h2
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h2
  have hr : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide
  simp only [Fuss, hr, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, h0, h1, h2, h3, h4, h5, h6, h7, Bool.true_and]

/-- Every footprint address is writable when the eight-byte check holds. -/
theorem fuss_all_schreibbar (m : Speicher) (a : Adresse)
    (h : schreibbar8 m a = true) : (Fuss a).all m.schreibbar = true := by
  have h2 := h
  simp only [schreibbar8, Bool.and_eq_true] at h2
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h2
  have hr : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide
  simp only [Fuss, hr, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, h0, h1, h2, h3, h4, h5, h6, h7, Bool.true_and]

/-! ## 2. The closing step: mapping to per-address R/W/X, end to end.

    From a `valX86`-accepted image, a state over its canonically loaded
    memory, a successful X-gated fetch and a successful realised step: the
    mapping admission, the executed prefix executable in the loaded mapping,
    the extracted read/write footprints permission-checked, all three
    permission maps preserved, and every changed byte inside the extracted
    write footprint. -/

/-- MAPPING-PERMISSION CLOSING: accepted mapping, X-gated fetch and a
    realised step give per-address R/W/X for every executed byte, checked
    permissions on the extracted access, preserved permission maps and the
    changed bytes inside the write footprint. -/
theorem ComposeMapPerms_verbindung (p : Profil) (bild : Bild) (bias : Nat)
    (s s' : Zustand) (d : Decodiert) (rest : List Byte)
    (hval : valX86 p bild = true)
    (hmem : s.speicher = geladen bild bias)
    (hf : fetchDekodiert s = some (d, rest))
    (hs : schritt d s = some s') :
    wohlgeformt p bild = true ∧
    ausfuehrbarN (geladen bild bias) s.rip d.laenge = true ∧
    zugriffLesbar s.speicher (zugriff d s) = true ∧
    zugriffSchreibbar s.speicher (zugriff d s) = true ∧
    s'.speicher.lesbar = s.speicher.lesbar ∧
    s'.speicher.schreibbar = s.speicher.schreibbar ∧
    s'.speicher.ausfuehrbar = s.speicher.ausfuehrbar ∧
    (∀ x, s'.speicher.bytes x ≠ s.speicher.bytes x →
      x ∈ (zugriff d s).schreiben) := by
  have hmap : wohlgeformt p bild = true := valX86_wohlgeformt p bild hval
  obtain ⟨_, _, hok, hexe⟩ := fetchDekodiert_entspricht s d rest hf
  have hexe' : ausfuehrbarN (geladen bild bias) s.rip d.laenge = true := by
    rw [← hmem]
    exact hexe
  generalize h : d.befehl = b
  cases b with
  | movImm64 dst v =>
    have heq := (erfolg_movImm64_ohne_speicher s s' dst v d hok h hs).1
    exact ⟨hmap, hexe', by simp [zugriffLesbar, zugriff_movImm64 d s dst v h],
      by simp [zugriffSchreibbar, zugriff_movImm64 d s dst v h], by rw [heq],
      by rw [heq], by rw [heq],
      by intro x hx; rw [heq] at hx; exact False.elim (hx rfl)⟩
  | movReg64 dst src =>
    have heq := (erfolg_movReg64_ohne_speicher s s' dst src d hok h hs).1
    exact ⟨hmap, hexe', by simp [zugriffLesbar, zugriff_movReg64 d s dst src h],
      by simp [zugriffSchreibbar, zugriff_movReg64 d s dst src h], by rw [heq],
      by rw [heq], by rw [heq],
      by intro x hx; rw [heq] at hx; exact False.elim (hx rfl)⟩
  | addReg64 dst src =>
    have heq := (erfolg_addReg64_ohne_speicher s s' dst src d hok h hs).1
    exact ⟨hmap, hexe', by simp [zugriffLesbar, zugriff_addReg64 d s dst src h],
      by simp [zugriffSchreibbar, zugriff_addReg64 d s dst src h], by rw [heq],
      by rw [heq], by rw [heq],
      by intro x hx; rw [heq] at hx; exact False.elim (hx rfl)⟩
  | subReg64 dst src =>
    have heq := (erfolg_subReg64_ohne_speicher s s' dst src d hok h hs).1
    exact ⟨hmap, hexe', by simp [zugriffLesbar, zugriff_subReg64 d s dst src h],
      by simp [zugriffSchreibbar, zugriff_subReg64 d s dst src h], by rw [heq],
      by rw [heq], by rw [heq],
      by intro x hx; rw [heq] at hx; exact False.elim (hx rfl)⟩
  | xorReg64 dst src =>
    have heq := (erfolg_xorReg64_ohne_speicher s s' dst src d hok h hs).1
    exact ⟨hmap, hexe', by simp [zugriffLesbar, zugriff_xorReg64 d s dst src h],
      by simp [zugriffSchreibbar, zugriff_xorReg64 d s dst src h], by rw [heq],
      by rw [heq], by rw [heq],
      by intro x hx; rw [heq] at hx; exact False.elim (hx rfl)⟩
  | cmpReg64 lhs rhs =>
    have heq := (erfolg_cmpReg64_ohne_speicher s s' lhs rhs d hok h hs).1
    exact ⟨hmap, hexe', by simp [zugriffLesbar, zugriff_cmpReg64 d s lhs rhs h],
      by simp [zugriffSchreibbar, zugriff_cmpReg64 d s lhs rhs h], by rw [heq],
      by rw [heq], by rw [heq],
      by intro x hx; rw [heq] at hx; exact False.elim (hx rfl)⟩
  | load64 dst base disp =>
    cases hrd : read64 s.speicher (effAddr s base disp) with
    | none =>
      exact False.elim
        (zugriff_load64_versagt_kein_erfolg s s' dst base disp d hok h hrd hs)
    | some v =>
      have heq := (erfolg_load64_ohne_speicher s s' dst base disp v d
        hok h hrd hs).1
      have hR : zugriffLesbar s.speicher (zugriff d s) = true := by
        rw [zugriff_load64 d s dst base disp h]
        exact fuss_all_lesbar s.speicher (effAddr s base disp)
          (read64_lesbar8 s.speicher (effAddr s base disp) v hrd)
      exact ⟨hmap, hexe', hR,
        by simp [zugriffSchreibbar, zugriff_load64 d s dst base disp h],
        by rw [heq], by rw [heq], by rw [heq],
        by intro x hx; rw [heq] at hx; exact False.elim (hx rfl)⟩
  | store64 base src disp =>
    cases hwr : write64 s.speicher (effAddr s base disp) (s.register src) with
    | none =>
      exact False.elim
        (zugriff_store64_versagt_kein_erfolg s s' base src disp d hok h hwr hs)
    | some m =>
      obtain ⟨hframe, hpl, hpw, hpx, _⟩ :=
        erfolg_store64_im_fuss s s' base src disp m d hok h hwr hs
      have hW : zugriffSchreibbar s.speicher (zugriff d s) = true := by
        rw [zugriff_store64 d s base src disp h]
        exact fuss_all_schreibbar s.speicher (effAddr s base disp)
          (write64_schreibbar8 s.speicher (effAddr s base disp)
            (s.register src) m hwr)
      exact ⟨hmap, hexe',
        by simp [zugriffLesbar, zugriff_store64 d s base src disp h],
        hW, hpl, hpw, hpx, hframe⟩
  | jump32 disp =>
    have heq := (erfolg_jump32_ohne_speicher s s' disp d hok h hs).1
    exact ⟨hmap, hexe', by simp [zugriffLesbar, zugriff_jump32 d s disp h],
      by simp [zugriffSchreibbar, zugriff_jump32 d s disp h], by rw [heq],
      by rw [heq], by rw [heq],
      by intro x hx; rw [heq] at hx; exact False.elim (hx rfl)⟩
  | jumpIf32 cond disp =>
    cases hb : bedingung cond s.flags with
    | true =>
      have heq := (erfolg_jumpIfGenommen_ohne_speicher s s' cond disp d
        hok h hb hs).1
      exact ⟨hmap, hexe', by simp [zugriffLesbar, zugriff_jumpIf32 d s cond disp h],
        by simp [zugriffSchreibbar, zugriff_jumpIf32 d s cond disp h],
        by rw [heq], by rw [heq], by rw [heq],
        by intro x hx; rw [heq] at hx; exact False.elim (hx rfl)⟩
    | false =>
      have heq := (erfolg_jumpIfNicht_ohne_speicher s s' cond disp d
        hok h hb hs).1
      exact ⟨hmap, hexe', by simp [zugriffLesbar, zugriff_jumpIf32 d s cond disp h],
        by simp [zugriffSchreibbar, zugriff_jumpIf32 d s cond disp h],
        by rw [heq], by rw [heq], by rw [heq],
        by intro x hx; rw [heq] at hx; exact False.elim (hx rfl)⟩
  | push64 src =>
    cases hwr : write64 s.speicher
        (s.register Register.rsp - BitVec.ofNat 64 8) (s.register src) with
    | none =>
      exact False.elim
        (zugriff_push64_versagt_kein_erfolg s s' src d hok h hwr hs)
    | some m =>
      obtain ⟨hframe, hpl, hpw, hpx, _⟩ :=
        erfolg_push64_im_fuss s s' src m d hok h hwr hs
      have hW : zugriffSchreibbar s.speicher (zugriff d s) = true := by
        rw [zugriff_push64 d s src h]
        exact fuss_all_schreibbar s.speicher (stapelOben s)
          (write64_schreibbar8 s.speicher
            (s.register Register.rsp - BitVec.ofNat 64 8)
            (s.register src) m hwr)
      exact ⟨hmap, hexe',
        by simp [zugriffLesbar, zugriff_push64 d s src h],
        hW, hpl, hpw, hpx, hframe⟩
  | pop64 dst =>
    cases hrd : read64 s.speicher (s.register Register.rsp) with
    | none =>
      exact False.elim
        (zugriff_pop64_versagt_kein_erfolg s s' dst d hok h hrd hs)
    | some v =>
      have heq := schritt_pop64_speicher d s s' dst v hok h hrd hs
      have hR : zugriffLesbar s.speicher (zugriff d s) = true := by
        rw [zugriff_pop64 d s dst h]
        exact fuss_all_lesbar s.speicher (s.register Register.rsp)
          (read64_lesbar8 s.speicher (s.register Register.rsp) v hrd)
      exact ⟨hmap, hexe', hR,
        by simp [zugriffSchreibbar, zugriff_pop64 d s dst h],
        by rw [heq], by rw [heq], by rw [heq],
        by intro x hx; rw [heq] at hx; exact False.elim (hx rfl)⟩
  | call32 disp =>
    cases hwr : write64 s.speicher
        (s.register Register.rsp - BitVec.ofNat 64 8)
        (ripNach s.rip d.laenge) with
    | none =>
      exact False.elim
        (zugriff_call32_versagt_kein_erfolg s s' disp d hok h hwr hs)
    | some m =>
      obtain ⟨hframe, hpl, hpw, hpx, _⟩ :=
        erfolg_call32_im_fuss s s' disp m d hok h hwr hs
      have hW : zugriffSchreibbar s.speicher (zugriff d s) = true := by
        rw [zugriff_call32 d s disp h]
        exact fuss_all_schreibbar s.speicher (stapelOben s)
          (write64_schreibbar8 s.speicher
            (s.register Register.rsp - BitVec.ofNat 64 8)
            (ripNach s.rip d.laenge) m hwr)
      exact ⟨hmap, hexe',
        by simp [zugriffLesbar, zugriff_call32 d s disp h],
        hW, hpl, hpw, hpx, hframe⟩
  | ret =>
    cases hrd : read64 s.speicher (s.register Register.rsp) with
    | none =>
      exact False.elim
        (zugriff_ret_versagt_kein_erfolg s s' d hok h hrd hs)
    | some ziel =>
      have heq := (erfolg_ret_ohne_speicher s s' ziel d hok h hrd hs).1
      have hR : zugriffLesbar s.speicher (zugriff d s) = true := by
        rw [zugriff_ret d s h]
        exact fuss_all_lesbar s.speicher (s.register Register.rsp)
          (read64_lesbar8 s.speicher (s.register Register.rsp) ziel hrd)
      exact ⟨hmap, hexe', hR,
        by simp [zugriffSchreibbar, zugriff_ret d s h],
        by rw [heq], by rw [heq], by rw [heq],
        by intro x hx; rw [heq] at hx; exact False.elim (hx rfl)⟩

/-! ## 3. Joint witness: accepted image with a reached memory-changing run.

    The witness image holds the canonical encoding of
    `store [rsp], rax` in a readable-executable code section beside a
    readable-writable data section carrying a nonzero byte. The witness
    state runs that store from the loaded mapping: fetch sees the store,
    the step succeeds, and the data byte observably changes. -/

/-- Witness code bytes: canonical encoding of `store [rsp], rax`. -/
def zeugenCode847 : List Byte :=
  encode (.store64 .rsp .rax (BitVec.ofNat 32 0))

/-- Witness file: eight code bytes then eight data bytes, nonzero at 8. -/
def zeugenDatei847 : List Byte :=
  zeugenCode847 ++ [natByte 9, natByte 1, natByte 2, natByte 3,
    natByte 4, natByte 5, natByte 6, natByte 7]

/-- Witness code section: readable and executable, never writable. -/
def zeugenCodeAbs847 : Abschnitt :=
  { dateiOff := 0, dateiLen := 8, vaddr := 0x1000, memLen := 8,
    lesbar := true, schreibbar := false, ausfuehrbar := true, ausr := 4096 }

/-- Witness data section: readable and writable, never executable. -/
def zeugenDatenAbs847 : Abschnitt :=
  { dateiOff := 8, dateiLen := 8, vaddr := 0x2000, memLen := 8,
    lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := 4096 }

/-- The witness image: fixed bias, entry inside the code section. -/
def zeugenBild847 : Bild :=
  { datei := zeugenDatei847
    abschnitte := [zeugenCodeAbs847, zeugenDatenAbs847]
    reloks := []
    eintraege := [0x1000]
    modus := .fest }

/-- Witness register file: `rax` holds 42, `rsp` names the data section. -/
def zeugenReg847 : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 42
  else if q = Register.rsp then BitVec.ofNat 64 0x2000
  else BitVec.ofNat 64 0

/-- Witness flags: nothing set. -/
def zeugenFlags847 : Flags :=
  { cf := false, pf := true, af := some false, zf := false, sf := false,
    of := false }

/-- Witness start state: entry `rip`, loaded witness image memory. -/
def zeugenZustand847 : Zustand :=
  { register := zeugenReg847
    flags := zeugenFlags847
    rip := BitVec.ofNat 64 0x1000
    speicher := geladen zeugenBild847 0 }

/-- ACCEPTANCE: the witness image validates (mapping AND decode coverage). -/
theorem zeugenBild847_akzeptiert : valX86 .p48 zeugenBild847 = true := by
  decide

/-- FETCH: the loaded witness state fetches exactly the stored store form. -/
theorem zeugenFetch847 :
    fetchDekodiert zeugenZustand847 =
      some (⟨.store64 .rsp .rax (BitVec.ofNat 32 0), 8⟩, []) := by
  decide

/-- STEP: the fetched store runs, moves `rip` past the 8-byte form and
    observably writes 42 to the data base. -/
theorem zeugenSchritt847 :
    (schritt ⟨.store64 .rsp .rax (BitVec.ofNat 32 0), 8⟩
      zeugenZustand847).map
      (fun s' => (s'.rip, s'.speicher.bytes (BitVec.ofNat 64 0x2000))) =
      some (BitVec.ofNat 64 0x1008, natByte 42) := by
  decide

/-- The data base holds a nonzero byte before the store runs. -/
theorem zeugenAlt847 :
    zeugenZustand847.speicher.bytes (BitVec.ofNat 64 0x2000) =
      natByte 9 := by
  decide

/-! ## 4. Joint companion and planted refusals. -/

/-- JOINT COMPANION: the closing theorem's premises hold jointly on the
    non-degenerate witness (two-section accepted image, nonzero data byte,
    reached memory-changing store step), and the changed byte lies in the
    extracted write footprint through the composed step. -/
theorem ComposeMapPerms_verbindung_zeuge :
    ∃ (s s' : Zustand) (d : Decodiert) (rest : List Byte),
      valX86 .p48 zeugenBild847 = true ∧
      s.speicher = geladen zeugenBild847 0 ∧
      fetchDekodiert s = some (d, rest) ∧
      schritt d s = some s' ∧
      s.speicher.bytes (BitVec.ofNat 64 0x2000) ≠
        s'.speicher.bytes (BitVec.ofNat 64 0x2000) ∧
      (BitVec.ofNat 64 0x2000) ∈ (zugriff d s).schreiben := by
  have hex : ∃ s',
      schritt ⟨.store64 .rsp .rax (BitVec.ofNat 32 0), 8⟩
        zeugenZustand847 = some s' ∧
      zeugenZustand847.speicher.bytes (BitVec.ofNat 64 0x2000) ≠
        s'.speicher.bytes (BitVec.ofNat 64 0x2000) := by
    cases hsch : schritt ⟨.store64 .rsp .rax (BitVec.ofNat 32 0), 8⟩
        zeugenZustand847 with
    | none =>
      have hstep := zeugenSchritt847
      simp [hsch] at hstep
    | some s' =>
      have hmap : (s'.rip, s'.speicher.bytes (BitVec.ofNat 64 0x2000)) =
          (BitVec.ofNat 64 0x1008, natByte 42) := by
        have hstep := zeugenSchritt847
        rw [hsch] at hstep
        simpa using hstep
      have hb : s'.speicher.bytes (BitVec.ofNat 64 0x2000) = natByte 42 :=
        congrArg Prod.snd hmap
      refine ⟨s', rfl, ?_⟩
      rw [zeugenAlt847, hb]
      decide
  obtain ⟨s', hs, hchg⟩ := hex
  have hconn := ComposeMapPerms_verbindung .p48 zeugenBild847 0
    zeugenZustand847 s' ⟨.store64 .rsp .rax (BitVec.ofNat 32 0), 8⟩ []
    zeugenBild847_akzeptiert rfl zeugenFetch847 hs
  obtain ⟨_, _, _, _, _, _, _, hframe⟩ := hconn
  exact ⟨zeugenZustand847, s', _, _, zeugenBild847_akzeptiert, rfl,
    zeugenFetch847, hs, hchg, hframe _ (Ne.symm hchg)⟩

/-- Witness state with `rbx` aimed at the code section (non-writable). -/
def zeugenCodeZustand847 : Zustand :=
  { zeugenZustand847 with register := fun q =>
    if q = Register.rbx then BitVec.ofNat 64 0x1000 else zeugenReg847 q }

/-- STORE-INTO-CODE REFUSAL: a store through a non-writable code address
    has no transition. -/
theorem zeugenSpeicherCode847_verweigert :
    ((schritt ⟨.store64 .rbx .rax (BitVec.ofNat 32 0), 7⟩
      zeugenCodeZustand847).map (fun s' => s'.rip)) = none := by
  decide

/-- FETCH-FROM-DATA REFUSAL: fetching at a non-executable data address
    refuses; readability there never substitutes for executability. -/
theorem zeugenFetchDaten847_verweigert :
    ausgangRip (byteschritt
      { zeugenZustand847 with rip := BitVec.ofNat 64 0x2000 }) = none := by
  decide

/-- W^X REFUSAL on the witness shape: making the code section writable
    refuses validation. -/
theorem zeugenWx847_verweigert :
    valX86 .p48 { zeugenBild847 with abschnitte :=
      [{ zeugenCodeAbs847 with schreibbar := true },
        zeugenDatenAbs847] } = false := by
  decide

#print axioms ComposeMapPerms_verbindung
#print axioms ComposeMapPerms_verbindung_zeuge

/- CUTS:
   Proved here, over the ACTUAL accepted vocabulary (`valX86` with
   `wohlgeformt` and decode coverage, `geladen` with per-section
   `ladenLesbar`/`ladenSchreibbar`/`ladenAusfuehrbar`, `fetchDekodiert`
   with the X-gated executable prefix, `zugriff` with read/write
   footprints, `schritt` with permission-checked `read64`/`write64`):
   the `zugriffLesbar`/`zugriffSchreibbar` interface, read/write success
   carrying its eight-byte check, footprint-wide permission from the
   eight-byte check, the generic closing step `ComposeMapPerms_verbindung`
   over arbitrary admitted images, states, fetches and steps (all 14 pilot
   forms, every premise used), its joint companion with a non-degenerate
   two-section witness and a reached memory-changing store step whose
   changed byte lands in the extracted footprint, and three planted
   refusals (store into code, fetch from data, W^X image).
   NOT proved here, and not claimed (missing producer legs, never assumed):
   - No source correspondence: nothing here claims the image bytes are the
     emitted form of any source program; no `Stmt`/`Vertrag` statement, no
     duty, cost, contract or call-log transfer. The source-memory and
     source-validator connections stay with their owners.
   - No concurrency bridge: footprints are per-byte sets shared with
     `Speicher.lean`, not atomic multi-byte events and not a TSO
     interleaving; the per-access target-to-W/GX simulation stays with the
     bridge owners of the connection wave.
   - No hardware claim: memory is the model `Speicher`, bytes model `Byte`
     lists; silicon, caches, TLBs, store buffers, interrupts, faults
     beyond the decoded refusal and timing stay open under named hardware
     assumptions owned elsewhere.
   - No extended forms: only the 14 pilot `Befehl` constructors step; the
     extended decoder/execution path stays with its owner.
   - Arbitrary-input decoder length soundness is reused only through the
     runtime checks of `fetchDekodiert`/`decodeFuel`, never assumed as a
     global premise; its standalone proof stays with the decoder owner.
   - No entry, budget, relocation or whole-binary claim beyond mapping
     admission, entry containment and decode coverage: entry/budget-stop
     connections stay with their owners.
-/

end Gabbro.Grammatik.X86
