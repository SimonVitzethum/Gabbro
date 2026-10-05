/-
  File:      Grammatik/X86/HwVector.lean
  Subject:   SIMD integer forms and enabled-state gates on the coherent machine.

  Lane 1131: lifts the accepted packed-integer rows (lane 686 `IntVecOp`,
  `encodeIntVec`/`decodeIntVec`/`stepIntVec`, `vektorLegacyZugelassen`)
  onto the coherent machine (`HwMaschine`/`HwSchritt`, lane 660).
  Register rows ride a checked adapter over the accepted evaluator
  (lifted, never redefined); the four 16-byte memory rows go through
  footprint-checked TSO byte accesses (`vecEintraege`/`ladeN`/drains)
  with an explicit tearing table -- no whole-vector atomicity claimed.
  Enabled-state gates refuse, never guess. No W/GX bridge is claimed.
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.VectorIntegerHardwareForms
import Grammatik.X86.VectorHardwareProfile
import Grammatik.X86.VectorFootprints

namespace Gabbro.Grammatik.X86

/-! ## 1. The sixteen canonical byte entries of one packed word.

  The low-chunk bytes (`vLo`) then the high-chunk bytes (`vHi`), oldest
  first -- the same two-chunk order the accepted `vecWrite` uses, so
  entry bytes ARE chunk bytes by construction (`rfl`). -/

/-- One vector byte: low-chunk `wortByte` below 8, high-chunk above. -/
def vecByte (v : Vektor) (i : Nat) : Byte :=
  if i < 8 then wortByte (vLo v) i else wortByte (vHi v) (i - 8)

/-- The sixteen canonical byte-store entries of `v` at `a`, oldest
    first: the eight low-chunk bytes then the eight high-chunk bytes.
    Sixteen per-byte events, never one atomic occurrence. -/
def vecEintraege (a : Adresse) (v : Vektor) : List TSOEintrag :=
  [⟨addrOff a 0, wortByte (vLo v) 0⟩,
    ⟨addrOff a 1, wortByte (vLo v) 1⟩,
    ⟨addrOff a 2, wortByte (vLo v) 2⟩,
    ⟨addrOff a 3, wortByte (vLo v) 3⟩,
    ⟨addrOff a 4, wortByte (vLo v) 4⟩,
    ⟨addrOff a 5, wortByte (vLo v) 5⟩,
    ⟨addrOff a 6, wortByte (vLo v) 6⟩,
    ⟨addrOff a 7, wortByte (vLo v) 7⟩,
    ⟨addrOff (vecHiAddr a) 0, wortByte (vHi v) 0⟩,
    ⟨addrOff (vecHiAddr a) 1, wortByte (vHi v) 1⟩,
    ⟨addrOff (vecHiAddr a) 2, wortByte (vHi v) 2⟩,
    ⟨addrOff (vecHiAddr a) 3, wortByte (vHi v) 3⟩,
    ⟨addrOff (vecHiAddr a) 4, wortByte (vHi v) 4⟩,
    ⟨addrOff (vecHiAddr a) 5, wortByte (vHi v) 5⟩,
    ⟨addrOff (vecHiAddr a) 6, wortByte (vHi v) 6⟩,
    ⟨addrOff (vecHiAddr a) 7, wortByte (vHi v) 7⟩]

/-- Register rows: every `IntVecOp` row except the four memory rows.
    The adapter admits only these; loads/stores use the TSO path. -/
def istVecRegisterOp : IntVecOp → Bool
  | .movdqaLd _ _ _ => false
  | .movdqaSt _ _ _ => false
  | .movdquLd _ _ _ => false
  | .movdquSt _ _ _ => false
  | _ => true

/-- Sixteen entries, no more: the vector shape is exact. -/
theorem vecEintraege_laenge (a : Adresse) (v : Vektor) :
    (vecEintraege a v).length = 16 := rfl

/-! ## 2. Footprint: every entry sits in the accepted 16-byte footprint. -/

/-- Every low-chunk entry address lies in the vector footprint. -/
theorem vecEintrag_mem_lo (a : Adresse) (k : Nat)
    (hk : k < 8) :
    addrOff a k ∈ vecFuss a := by
  rw [vecFuss_mem]
  exact Or.inl (fuss_mem_offset a k hk)

/-- Every high-chunk entry address lies in the vector footprint. -/
theorem vecEintrag_mem_hi (a : Adresse) (k : Nat)
    (hk : k < 8) :
    addrOff (vecHiAddr a) k ∈ vecFuss a := by
  rw [vecFuss_mem]
  exact Or.inr (fuss_mem_offset (vecHiAddr a) k hk)

/-- Every one of the sixteen entries sits in the accepted footprint. -/
theorem vecEintraege_mem_fuss (a : Adresse) (v : Vektor) (e : TSOEintrag)
    (hmem : e ∈ vecEintraege a v) : e.addr ∈ vecFuss a := by
  unfold vecEintraege at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact vecEintrag_mem_lo a 0 (by decide)
  · exact vecEintrag_mem_lo a 1 (by decide)
  · exact vecEintrag_mem_lo a 2 (by decide)
  · exact vecEintrag_mem_lo a 3 (by decide)
  · exact vecEintrag_mem_lo a 4 (by decide)
  · exact vecEintrag_mem_lo a 5 (by decide)
  · exact vecEintrag_mem_lo a 6 (by decide)
  · exact vecEintrag_mem_lo a 7 (by decide)
  · exact vecEintrag_mem_hi a 0 (by decide)
  · exact vecEintrag_mem_hi a 1 (by decide)
  · exact vecEintrag_mem_hi a 2 (by decide)
  · exact vecEintrag_mem_hi a 3 (by decide)
  · exact vecEintrag_mem_hi a 4 (by decide)
  · exact vecEintrag_mem_hi a 5 (by decide)
  · exact vecEintrag_mem_hi a 6 (by decide)
  · exact vecEintrag_mem_hi a 7 (by decide)

/-- One byte of a readable chunk is readable. -/
theorem lesbar8_einzeln (m : Speicher) (a : Adresse) (k : Nat)
    (hk : k < 8) (h : lesbar8 m a = true) :
    m.lesbar (addrOff a k) = true := by
  unfold lesbar8 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have h8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 := by
    omega
  rcases h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    assumption

/-- One byte of a writable chunk is writable. -/
theorem schreibbar8_einzeln (m : Speicher) (a : Adresse) (k : Nat)
    (hk : k < 8) (h : schreibbar8 m a = true) :
    m.schreibbar (addrOff a k) = true := by
  unfold schreibbar8 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have h8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 := by
    omega
  rcases h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    assumption

/-- A fold of issues succeeds wherever every entry has write permission.
    Permissions survive each issue (the memory is kept), so the whole
    list goes through. -/
theorem issueListe_erfolg (l : List TSOEintrag) (s : TSOZustand)
    (c : Nat) (h : ∀ e ∈ l, s.mem.schreibbar e.addr = true) :
    ∃ s' : TSOZustand, issueListe s c l = some s' := by
  induction l generalizing s with
  | nil => exact ⟨s, rfl⟩
  | cons e rest ih =>
    have he : s.mem.schreibbar e.addr = true := h e (by simp)
    have h1 : issueByte s c e.addr e.wert =
        some ⟨s.mem, pufferSetze s.puffer c (s.puffer c ++ [e])⟩ := by
      unfold issueByte
      rw [if_pos he]
    have hrest : ∀ e' ∈ rest,
        (⟨s.mem, pufferSetze s.puffer c (s.puffer c ++ [e])⟩ :
          TSOZustand).mem.schreibbar e'.addr = true :=
      fun e' hm => h e' (by simp [hm])
    obtain ⟨s', hs'⟩ := ih _ hrest
    have hfold : issueListe s c (e :: rest) =
        issueListe ⟨s.mem, pufferSetze s.puffer c (s.puffer c ++ [e])⟩
          c rest := by
      show (match issueByte s c e.addr e.wert with
        | none => (none : Option TSOZustand)
        | some s1 => issueListe s1 c rest) = _
      rw [h1]
    rw [hfold]
    exact ⟨s', hs'⟩

/-- Vector store issue on the TSO view: sixteen buffered byte issues,
    never the direct `vecWrite` effect. `none` = a refused byte. -/
def vecSpeichern (s : TSOZustand) (c : Nat) (a : Adresse)
    (v : Vektor) : Option TSOZustand :=
  issueListe s c (vecEintraege a v)

/-- A successful vector issue appends exactly the sixteen entries. -/
theorem vecSpeichern_haengt_an (s s' : TSOZustand) (c : Nat)
    (a : Adresse) (v : Vektor) (h : vecSpeichern s c a v = some s') :
    s'.puffer c = s.puffer c ++ vecEintraege a v :=
  issueListe_haengt_an s s' c _ h

/-- A vector issue changes no canonical byte (buffer only). -/
theorem vecSpeichern_kein_speicher (s s' : TSOZustand) (c : Nat)
    (a : Adresse) (v : Vektor) (h : vecSpeichern s c a v = some s')
    (x : Adresse) :
    s'.mem.bytes x = s.mem.bytes x :=
  issueListe_kein_speicher s s' c _ h x

/-- Write permission across both chunks issues the whole vector. -/
theorem vecSpeichern_erfolg (s : TSOZustand) (c : Nat) (a : Adresse)
    (v : Vektor)
    (h1 : schreibbar8 s.mem a = true)
    (h2 : schreibbar8 s.mem (vecHiAddr a) = true) :
    ∃ s' : TSOZustand, vecSpeichern s c a v = some s' := by
  apply issueListe_erfolg
  intro e hmem
  have hfuss := vecEintraege_mem_fuss a v e hmem
  rw [vecFuss_mem, fuss_mem_iff, fuss_mem_iff] at hfuss
  rcases hfuss with ⟨k, hk, heq⟩ | ⟨k, hk, heq⟩
  · rw [← heq]
    exact schreibbar8_einzeln s.mem a k hk h1
  · rw [← heq]
    exact schreibbar8_einzeln s.mem (vecHiAddr a) k hk h2

/-! ## 3. Vector loads as eight-plus-eight TSO byte observations.

  Each chunk loads through eight `loadByte` observations (youngest
  own-buffer entry wins per byte: forwarding is observed, never
  bypassed); the two chunk words join into the packed word. `none` =
  an unreadable byte. -/

/-- Assemble eight observed bytes into a chunk function: constructor
    patterns, so each literal entry reduces by `rfl`. -/
def achtFun (b0 b1 b2 b3 b4 b5 b6 b7 : Byte) : Fin 8 → Byte :=
  fun j => match j with
  | ⟨0, _⟩ => b0 | ⟨1, _⟩ => b1 | ⟨2, _⟩ => b2 | ⟨3, _⟩ => b3
  | ⟨4, _⟩ => b4 | ⟨5, _⟩ => b5 | ⟨6, _⟩ => b6 | ⟨_, _⟩ => b7

/-- Load one eight-byte chunk at `a` on core `c` through eight TSO
    byte observations, assembled low byte first. -/
def ladeAcht (s : TSOZustand) (c : Nat) (a : Adresse) : Option Wort :=
  match loadByte s c (addrOff a 0), loadByte s c (addrOff a 1),
      loadByte s c (addrOff a 2), loadByte s c (addrOff a 3),
      loadByte s c (addrOff a 4), loadByte s c (addrOff a 5),
      loadByte s c (addrOff a 6), loadByte s c (addrOff a 7) with
  | some b0, some b1, some b2, some b3, some b4, some b5, some b6,
    some b7 =>
    some (bytesWort (achtFun b0 b1 b2 b3 b4 b5 b6 b7))
  | _, _, _, _, _, _, _, _ => none

/-- Load a packed word at `a` on core `c`: the low chunk then the high
    chunk eight bytes past the base, joined back into one word. -/
def vecLaden (s : TSOZustand) (c : Nat) (a : Adresse) :
    Option Vektor :=
  match ladeAcht s c a, ladeAcht s c (vecHiAddr a) with
  | some lo, some hi => some (vecJoin lo hi)
  | _, _ => none

/-- A chunk load with no pending own entry at any of its eight bytes
    observes exactly the canonical chunk word: the accepted `read64`
    value, never a guessed one. -/
theorem ladeAcht_ist_read64 (s : TSOZustand) (c : Nat) (a : Adresse)
    (w : Wort)
    (hmiss : ∀ k : Nat, k < 8 →
      neuestens (s.puffer c) (addrOff a k) = none)
    (hrd : lesbar8 s.mem a = true)
    (h : ladeAcht s c a = some w) :
    read64 s.mem a = some w := by
  unfold ladeAcht at h
  cases h0 : loadByte s c (addrOff a 0) with
  | none =>
    rw [h0] at h
    dsimp only at h
    cases h
  | some b0 =>
    cases h1 : loadByte s c (addrOff a 1) with
    | none =>
      rw [h0, h1] at h
      dsimp only at h
      cases h
    | some b1 =>
      cases h2 : loadByte s c (addrOff a 2) with
      | none =>
        rw [h0, h1, h2] at h
        dsimp only at h
        cases h
      | some b2 =>
        cases h3 : loadByte s c (addrOff a 3) with
        | none =>
          rw [h0, h1, h2, h3] at h
          dsimp only at h
          cases h
        | some b3 =>
          cases h4 : loadByte s c (addrOff a 4) with
          | none =>
            rw [h0, h1, h2, h3, h4] at h
            dsimp only at h
            cases h
          | some b4 =>
            cases h5 : loadByte s c (addrOff a 5) with
            | none =>
              rw [h0, h1, h2, h3, h4, h5] at h
              dsimp only at h
              cases h
            | some b5 =>
              cases h6 : loadByte s c (addrOff a 6) with
              | none =>
                rw [h0, h1, h2, h3, h4, h5, h6] at h
                dsimp only at h
                cases h
              | some b6 =>
                cases h7 : loadByte s c (addrOff a 7) with
                | none =>
                  rw [h0, h1, h2, h3, h4, h5, h6, h7] at h
                  dsimp only at h
                  cases h
                | some b7 =>
                  rw [h0, h1, h2, h3, h4, h5, h6, h7] at h
                  dsimp only at h
                  obtain rfl := Option.some_inj.mp h
                  have m0 : b0 = s.mem.bytes (addrOff a 0) := by
                    have hg := load_ohne_eintrag s c (addrOff a 0)
                      (hmiss 0 (by decide))
                      (lesbar8_einzeln s.mem a 0 (by decide) hrd)
                    rw [h0] at hg
                    exact Option.some_inj.mp hg
                  have m1 : b1 = s.mem.bytes (addrOff a 1) := by
                    have hg := load_ohne_eintrag s c (addrOff a 1)
                      (hmiss 1 (by decide))
                      (lesbar8_einzeln s.mem a 1 (by decide) hrd)
                    rw [h1] at hg
                    exact Option.some_inj.mp hg
                  have m2 : b2 = s.mem.bytes (addrOff a 2) := by
                    have hg := load_ohne_eintrag s c (addrOff a 2)
                      (hmiss 2 (by decide))
                      (lesbar8_einzeln s.mem a 2 (by decide) hrd)
                    rw [h2] at hg
                    exact Option.some_inj.mp hg
                  have m3 : b3 = s.mem.bytes (addrOff a 3) := by
                    have hg := load_ohne_eintrag s c (addrOff a 3)
                      (hmiss 3 (by decide))
                      (lesbar8_einzeln s.mem a 3 (by decide) hrd)
                    rw [h3] at hg
                    exact Option.some_inj.mp hg
                  have m4 : b4 = s.mem.bytes (addrOff a 4) := by
                    have hg := load_ohne_eintrag s c (addrOff a 4)
                      (hmiss 4 (by decide))
                      (lesbar8_einzeln s.mem a 4 (by decide) hrd)
                    rw [h4] at hg
                    exact Option.some_inj.mp hg
                  have m5 : b5 = s.mem.bytes (addrOff a 5) := by
                    have hg := load_ohne_eintrag s c (addrOff a 5)
                      (hmiss 5 (by decide))
                      (lesbar8_einzeln s.mem a 5 (by decide) hrd)
                    rw [h5] at hg
                    exact Option.some_inj.mp hg
                  have m6 : b6 = s.mem.bytes (addrOff a 6) := by
                    have hg := load_ohne_eintrag s c (addrOff a 6)
                      (hmiss 6 (by decide))
                      (lesbar8_einzeln s.mem a 6 (by decide) hrd)
                    rw [h6] at hg
                    exact Option.some_inj.mp hg
                  have m7 : b7 = s.mem.bytes (addrOff a 7) := by
                    have hg := load_ohne_eintrag s c (addrOff a 7)
                      (hmiss 7 (by decide))
                      (lesbar8_einzeln s.mem a 7 (by decide) hrd)
                    rw [h7] at hg
                    exact Option.some_inj.mp hg
                  have hfun : readBytes s.mem a =
                      achtFun b0 b1 b2 b3 b4 b5 b6 b7 := by
                    funext ⟨jv, hj⟩
                    have h8 : jv = 0 ∨ jv = 1 ∨ jv = 2 ∨ jv = 3 ∨
                        jv = 4 ∨ jv = 5 ∨ jv = 6 ∨ jv = 7 := by
                      omega
                    rcases h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
                    · exact m0.symm
                    · exact m1.symm
                    · exact m2.symm
                    · exact m3.symm
                    · exact m4.symm
                    · exact m5.symm
                    · exact m6.symm
                    · exact m7.symm
                  have hrd8 : read64 s.mem a =
                      some (bytesWort (readBytes s.mem a)) := by
                    unfold read64
                    rw [if_pos hrd]
                  rw [hrd8, hfun]

/-- A packed load with no pending own entry anywhere in its sixteen
    footprint bytes observes exactly the accepted `vecRead` value. -/
theorem vecLaden_ist_vecRead (s : TSOZustand) (c : Nat) (a : Adresse)
    (v : Vektor)
    (hmiss : ∀ x ∈ vecFuss a, neuestens (s.puffer c) x = none)
    (hrd1 : lesbar8 s.mem a = true)
    (hrd2 : lesbar8 s.mem (vecHiAddr a) = true)
    (h : vecLaden s c a = some v) :
    vecRead s.mem a = some v := by
  have e : vecLaden s c a = match ladeAcht s c a,
      ladeAcht s c (vecHiAddr a) with
    | some lo, some hi => some (vecJoin lo hi)
    | _, _ => (none : Option Vektor) := rfl
  rw [e] at h
  cases hlo : ladeAcht s c a with
  | none =>
    rw [hlo] at h
    dsimp only at h
    cases h
  | some lo =>
    cases hhi : ladeAcht s c (vecHiAddr a) with
    | none =>
      rw [hlo, hhi] at h
      dsimp only at h
      cases h
    | some hi =>
      rw [hlo, hhi] at h
      dsimp only at h
      obtain rfl := Option.some_inj.mp h
      have rlo := ladeAcht_ist_read64 s c a lo
        (fun k hk => hmiss _ (vecEintrag_mem_lo a k hk)) hrd1 hlo
      have rhi := ladeAcht_ist_read64 s c (vecHiAddr a) hi
        (fun k hk => hmiss _ (vecEintrag_mem_hi a k hk)) hrd2 hhi
      unfold vecRead
      rw [rlo, rhi]

/-! ## 4. Drains: byte-wise flushes with an explicit tearing table.

  A drain flushes one oldest entry at a time: after flushing a prefix
  of the sixteen, the flushed bytes are new while the rest still reads
  the pre-drain bytes (`paket_reisst`/`vecWrite_teilt` shape, at sixteen
  bytes). No whole-vector atomicity is claimed anywhere. -/

/-- Flush the oldest entries of core `c` named by `l`, in order:
    `none` = the buffer ran dry. The entries are named, never trusted:
    every theorem below ties them to the real buffer prefix. -/
def drainListe (s : TSOZustand) (c : Nat) : List TSOEintrag →
    Option TSOZustand
  | [] => some s
  | _e :: rest =>
    match flushKern s c with
    | none => none
    | some s1 => drainListe s1 c rest

/-- A drain changes nothing outside the drained entries (frame). -/
theorem drainListe_rahmen (l : List TSOEintrag) (s s' : TSOZustand)
    (c : Nat) (rest : List TSOEintrag)
    (hbuf : s.puffer c = l ++ rest)
    (h : drainListe s c l = some s')
    (x : Adresse) (hxa : ∀ e ∈ l, e.addr ≠ x) :
    s'.mem.bytes x = s.mem.bytes x := by
  induction l generalizing s with
  | nil =>
    have e : drainListe s c [] = some s := rfl
    rw [e] at h
    obtain rfl := Option.some_inj.mp h
    rfl
  | cons hd tl ih =>
    have e : drainListe s c (hd :: tl) = match flushKern s c with
      | none => (none : Option TSOZustand)
      | some s1 => drainListe s1 c tl := rfl
    rw [e] at h
    cases hk : flushKern s c with
    | none =>
      rw [hk] at h
      dsimp only at h
      cases h
    | some s1 =>
      rw [hk] at h
      dsimp only at h
      have hhead : s.puffer c = hd :: (tl ++ rest) := hbuf
      have hbuf1 : s1.puffer c = tl ++ rest :=
        flush_entfernt_kopf s s1 c hk hd (tl ++ rest) hhead
      have hfr := ih s1 hbuf1 h (fun e hm => hxa e (by simp [hm]))
      have hhx : x ≠ hd.addr := Ne.symm (hxa hd (by simp))
      have hkeep := flush_rahmen s s1 c hk hd (tl ++ rest) hhead x hhx
      rw [hfr, hkeep]

/-- A drain installs the latest drained byte at every touched address:
    `x` reads the value its entries carry (all of them carry `w`). -/
theorem drainListe_schreibt_allg (l : List TSOEintrag) (s s' : TSOZustand)
    (c : Nat) (rest : List TSOEintrag)
    (hbuf : s.puffer c = l ++ rest)
    (h : drainListe s c l = some s')
    (x : Adresse) (w : Byte)
    (hw : ∀ e ∈ l, e.addr = x → e.wert = w)
    (hmem : ∃ e ∈ l, e.addr = x) :
    s'.mem.bytes x = w := by
  induction l generalizing s with
  | nil =>
    simp at hmem
  | cons hd tl ih =>
    have e : drainListe s c (hd :: tl) = match flushKern s c with
      | none => (none : Option TSOZustand)
      | some s1 => drainListe s1 c tl := rfl
    rw [e] at h
    cases hk : flushKern s c with
    | none =>
      rw [hk] at h
      dsimp only at h
      cases h
    | some s1 =>
      rw [hk] at h
      dsimp only at h
      have hhead : s.puffer c = hd :: (tl ++ rest) := hbuf
      have hbuf1 : s1.puffer c = tl ++ rest :=
        flush_entfernt_kopf s s1 c hk hd (tl ++ rest) hhead
      have hwt : ∀ e ∈ tl, e.addr = x → e.wert = w :=
        fun e hm had => hw e (by simp [hm]) had
      by_cases heq : hd.addr = x
      · have hwv : hd.wert = w := hw hd (by simp) heq
        have hinst := flush_schreibt_kopf s s1 c hk hd (tl ++ rest) hhead
        rw [heq] at hinst
        by_cases hex : ∃ e ∈ tl, e.addr = x
        · obtain ⟨e2, hm2, had2⟩ := hex
          exact ih s1 hbuf1 h hwt ⟨e2, hm2, had2⟩
        · have hxa : ∀ e ∈ tl, e.addr ≠ x := by
            intro e hm had
            exact hex ⟨e, hm, had⟩
          have hfr := drainListe_rahmen tl s1 s' c rest hbuf1 h x hxa
          rw [hfr, hinst, hwv]
      · obtain ⟨e, hmeml, hadr⟩ := hmem
        simp only [List.mem_cons] at hmeml
        have hmem2 : e ∈ tl := by
          rcases hmeml with rfl | hm
          · exact absurd hadr heq
          · exact hm
        exact ih s1 hbuf1 h hwt ⟨e, hmem2, hadr⟩

/-! ## 5. Vector drain table: torn halves, installed wholes. -/

/-- The low eight entries of one packed word, oldest first. -/
def vecEintraegeLo (a : Adresse) (v : Vektor) : List TSOEintrag :=
  [⟨addrOff a 0, wortByte (vLo v) 0⟩,
    ⟨addrOff a 1, wortByte (vLo v) 1⟩,
    ⟨addrOff a 2, wortByte (vLo v) 2⟩,
    ⟨addrOff a 3, wortByte (vLo v) 3⟩,
    ⟨addrOff a 4, wortByte (vLo v) 4⟩,
    ⟨addrOff a 5, wortByte (vLo v) 5⟩,
    ⟨addrOff a 6, wortByte (vLo v) 6⟩,
    ⟨addrOff a 7, wortByte (vLo v) 7⟩]

/-- The high eight entries of one packed word, oldest first. -/
def vecEintraegeHi (a : Adresse) (v : Vektor) : List TSOEintrag :=
  [⟨addrOff (vecHiAddr a) 0, wortByte (vHi v) 0⟩,
    ⟨addrOff (vecHiAddr a) 1, wortByte (vHi v) 1⟩,
    ⟨addrOff (vecHiAddr a) 2, wortByte (vHi v) 2⟩,
    ⟨addrOff (vecHiAddr a) 3, wortByte (vHi v) 3⟩,
    ⟨addrOff (vecHiAddr a) 4, wortByte (vHi v) 4⟩,
    ⟨addrOff (vecHiAddr a) 5, wortByte (vHi v) 5⟩,
    ⟨addrOff (vecHiAddr a) 6, wortByte (vHi v) 6⟩,
    ⟨addrOff (vecHiAddr a) 7, wortByte (vHi v) 7⟩]

/-- The sixteen split into low then high chunks. -/
theorem vecEintraege_zerlegt (a : Adresse) (v : Vektor) :
    vecEintraege a v = vecEintraegeLo a v ++ vecEintraegeHi a v := rfl

/-- A low-chunk entry at a chunk address carries that chunk byte. -/
theorem vecEintraegeLo_hw (a : Adresse) (v : Vektor) (k : Nat)
    (hk : k < 8) (e : TSOEintrag) (hmem : e ∈ vecEintraegeLo a v)
    (had : e.addr = addrOff a k) :
    e.wert = wortByte (vLo v) k := by
  unfold vecEintraegeLo at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h0k : 0 = k := addrOff_inj8 (by decide) hk had
    rw [← h0k]
  · have h1k : 1 = k := addrOff_inj8 (by decide) hk had
    rw [← h1k]
  · have h2k : 2 = k := addrOff_inj8 (by decide) hk had
    rw [← h2k]
  · have h3k : 3 = k := addrOff_inj8 (by decide) hk had
    rw [← h3k]
  · have h4k : 4 = k := addrOff_inj8 (by decide) hk had
    rw [← h4k]
  · have h5k : 5 = k := addrOff_inj8 (by decide) hk had
    rw [← h5k]
  · have h6k : 6 = k := addrOff_inj8 (by decide) hk had
    rw [← h6k]
  · have h7k : 7 = k := addrOff_inj8 (by decide) hk had
    rw [← h7k]

/-- A high-chunk entry at a chunk address carries that chunk byte. -/
theorem vecEintraegeHi_hw (a : Adresse) (v : Vektor) (k : Nat)
    (hk : k < 8) (e : TSOEintrag) (hmem : e ∈ vecEintraegeHi a v)
    (had : e.addr = addrOff (vecHiAddr a) k) :
    e.wert = wortByte (vHi v) k := by
  unfold vecEintraegeHi at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h0k : 0 = k := addrOff_inj8 (by decide) hk had
    rw [← h0k]
  · have h1k : 1 = k := addrOff_inj8 (by decide) hk had
    rw [← h1k]
  · have h2k : 2 = k := addrOff_inj8 (by decide) hk had
    rw [← h2k]
  · have h3k : 3 = k := addrOff_inj8 (by decide) hk had
    rw [← h3k]
  · have h4k : 4 = k := addrOff_inj8 (by decide) hk had
    rw [← h4k]
  · have h5k : 5 = k := addrOff_inj8 (by decide) hk had
    rw [← h5k]
  · have h6k : 6 = k := addrOff_inj8 (by decide) hk had
    rw [← h6k]
  · have h7k : 7 = k := addrOff_inj8 (by decide) hk had
    rw [← h7k]

/-- Low-chunk entries never name a high-chunk footprint address: the
    16-byte no-wrap keeps the chunks apart. -/
theorem vecLo_fremd_hi (a : Adresse) (hno : OhneUmbruch16 a)
    (v : Vektor) (e : TSOEintrag) (hmem : e ∈ vecEintraegeLo a v)
    (x : Adresse) (hx : x ∈ Fuss (vecHiAddr a)) :
    e.addr ≠ x := by
  rw [fuss_mem_iff] at hx
  obtain ⟨j, hjk, rfl⟩ := hx
  unfold vecEintraegeLo at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact vecChunks_disjoint a hno 0 j (by decide) hjk
  · exact vecChunks_disjoint a hno 1 j (by decide) hjk
  · exact vecChunks_disjoint a hno 2 j (by decide) hjk
  · exact vecChunks_disjoint a hno 3 j (by decide) hjk
  · exact vecChunks_disjoint a hno 4 j (by decide) hjk
  · exact vecChunks_disjoint a hno 5 j (by decide) hjk
  · exact vecChunks_disjoint a hno 6 j (by decide) hjk
  · exact vecChunks_disjoint a hno 7 j (by decide) hjk

/-- The sixteen entries name pairwise-distinct addresses: same address
    means same entry (hence same byte). Needs the 16-byte no-wrap so
    the two chunks stay apart. -/
theorem vecEintraege_nodup_addr (a : Adresse) (v : Vektor)
    (hno : OhneUmbruch16 a) :
    ∀ e1 ∈ vecEintraege a v, ∀ e2 ∈ vecEintraege a v,
      e1.addr = e2.addr → e1 = e2 := by
  have hoff : ∀ e ∈ vecEintraege a v,
      (∃ k, k < 8 ∧ e = ⟨addrOff a k, wortByte (vLo v) k⟩) ∨
      (∃ k, k < 8 ∧
        e = ⟨addrOff (vecHiAddr a) k, wortByte (vHi v) k⟩) := by
    intro e hmem
    unfold vecEintraege at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by decide, rfl⟩
    · exact Or.inl ⟨1, by decide, rfl⟩
    · exact Or.inl ⟨2, by decide, rfl⟩
    · exact Or.inl ⟨3, by decide, rfl⟩
    · exact Or.inl ⟨4, by decide, rfl⟩
    · exact Or.inl ⟨5, by decide, rfl⟩
    · exact Or.inl ⟨6, by decide, rfl⟩
    · exact Or.inl ⟨7, by decide, rfl⟩
    · exact Or.inr ⟨0, by decide, rfl⟩
    · exact Or.inr ⟨1, by decide, rfl⟩
    · exact Or.inr ⟨2, by decide, rfl⟩
    · exact Or.inr ⟨3, by decide, rfl⟩
    · exact Or.inr ⟨4, by decide, rfl⟩
    · exact Or.inr ⟨5, by decide, rfl⟩
    · exact Or.inr ⟨6, by decide, rfl⟩
    · exact Or.inr ⟨7, by decide, rfl⟩
  intro e1 h1 e2 h2 heq
  rcases hoff e1 h1 with ⟨k1, hk1, rfl⟩ | ⟨k1, hk1, rfl⟩ <;>
    rcases hoff e2 h2 with ⟨k2, hk2, rfl⟩ | ⟨k2, hk2, rfl⟩
  · have hkk : k1 = k2 := addrOff_inj8 hk1 hk2 heq
    subst hkk
    rfl
  · exact absurd heq (vecChunks_disjoint a hno k1 k2 hk1 hk2)
  · exact absurd heq (Ne.symm (vecChunks_disjoint a hno k2 k1 hk2 hk1))
  · have hkk : k1 = k2 := addrOff_inj8 hk1 hk2 heq
    subst hkk
    rfl

/-- TEARING: draining the low eight installs the low bytes while the
    high bytes still read pre-drain. No whole-vector atomicity. -/
theorem vecDrain_teilt (s s1 : TSOZustand) (c : Nat) (a : Adresse)
    (v : Vektor) (rest : List TSOEintrag)
    (hno : OhneUmbruch16 a)
    (hbuf : s.puffer c = vecEintraege a v ++ rest)
    (h : drainListe s c (vecEintraegeLo a v) = some s1)
    (k : Nat) (hk : k < 8) :
    s1.mem.bytes (addrOff a k) = wortByte (vLo v) k ∧
      s1.mem.bytes (addrOff (vecHiAddr a) k) =
        s.mem.bytes (addrOff (vecHiAddr a) k) := by
  rw [vecEintraege_zerlegt, List.append_assoc] at hbuf
  have hmemLo : ∀ k : Nat, k < 8 →
      ∃ e ∈ vecEintraegeLo a v, e.addr = addrOff a k := by
    intro k hk
    have hk8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 := by
      omega
    rcases hk8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨addrOff a 0, wortByte (vLo v) 0⟩, List.Mem.head _, rfl⟩
    · exact ⟨⟨addrOff a 1, wortByte (vLo v) 1⟩,
        List.Mem.tail _ (List.Mem.head _), rfl⟩
    · exact ⟨⟨addrOff a 2, wortByte (vLo v) 2⟩,
        List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), rfl⟩
    · exact ⟨⟨addrOff a 3, wortByte (vLo v) 3⟩,
        List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.head _))), rfl⟩
    · exact ⟨⟨addrOff a 4, wortByte (vLo v) 4⟩,
        List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.head _)))), rfl⟩
    · exact ⟨⟨addrOff a 5, wortByte (vLo v) 5⟩,
        List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))), rfl⟩
    · exact ⟨⟨addrOff a 6, wortByte (vLo v) 6⟩,
        List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.head _)))))), rfl⟩
    · exact ⟨⟨addrOff a 7, wortByte (vLo v) 7⟩,
        List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.head _))))))), rfl⟩
  refine ⟨?_, ?_⟩
  · exact drainListe_schreibt_allg (vecEintraegeLo a v) s s1 c
      (vecEintraegeHi a v ++ rest) hbuf h (addrOff a k)
      (wortByte (vLo v) k)
      (fun e hm had => vecEintraegeLo_hw a v k hk e hm had)
      (hmemLo k hk)
  · exact drainListe_rahmen (vecEintraegeLo a v) s s1 c
      (vecEintraegeHi a v ++ rest) hbuf h
      (addrOff (vecHiAddr a) k) (fun e hm =>
        vecLo_fremd_hi a hno v e hm _ (fuss_mem_offset _ k hk))

/-- FULL DRAIN: draining all sixteen installs every entry byte. -/
theorem vecDrain_schreibt (s s' : TSOZustand) (c : Nat) (a : Adresse)
    (v : Vektor) (rest : List TSOEintrag)
    (hbuf : s.puffer c = vecEintraege a v ++ rest)
    (h : drainListe s c (vecEintraege a v) = some s')
    (hdis : ∀ e1 ∈ vecEintraege a v, ∀ e2 ∈ vecEintraege a v,
      e1.addr = e2.addr → e1 = e2)
    (e : TSOEintrag) (hmem : e ∈ vecEintraege a v) :
    s'.mem.bytes e.addr = e.wert := by
  exact drainListe_schreibt_allg (vecEintraege a v) s s' c rest hbuf h
    e.addr e.wert
    (fun e' hm' had => by
      have heq := hdis e' hm' e hmem had
      rw [heq])
    ⟨e, hmem, rfl⟩

/-! ## 6. Register rows on the coherent machine.

  The eleven register rows ride the accepted `stepIntVec` over the
  machine core projection; the adapter refuses the four memory rows
  (they use the TSO path of §3-§5) and every refused evaluation.
  Profiles are untouched, so `HwWf` survives by the accepted lemmas. -/

/-- Register successor on the machine: the accepted selected step over
    the core projection, re-embedded as core data. Memory rows are
    refused here (their TSO path is `vecLadeSchritt`/`vecSpeicherSchritt`
    below); `none` is a refused gate, a bad length, or a failed
    evaluation. -/
def vecRegSchritt (m : HwMaschine) (c : Nat) (cpu : CpuMerkmal)
    (k : KontrollBild) (d : IntVecDec) : Option HwMaschine :=
  if istVecRegisterOp d.op then
    match stepIntVec d (projFp m c) m.hw (m.bereit c) cpu k with
    | some t' => some (setKernVonFp m c t')
    | none => none
  else none

/-- Register rows change no memory byte: both store shapes are
    constructor-distinct from every register row, so the accepted
    memory-preservation covers them. -/
theorem vecRegSchritt_speicher (d : IntVecDec) (t t' : FpZustand)
    (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal)
    (k : KontrollBild)
    (hreg : istVecRegisterOp d.op = true)
    (hok : laengeOk d.laenge = true)
    (hgate : vektorLegacyZugelassen hw b cpu k = true)
    (hstep : stepIntVec d t hw b cpu k = some t') :
    t'.kern.speicher = t.kern.speicher := by
  have hA : ∀ (base : Register) (src : XmmReg) (disp : BitVec 32),
      d.op ≠ .movdqaSt base src disp := by
    intro base src disp hcon
    have hred : istVecRegisterOp (.movdqaSt base src disp) = false := rfl
    rw [← hcon] at hred
    rw [hred] at hreg
    cases hreg
  have hU : ∀ (base : Register) (src : XmmReg) (disp : BitVec 32),
      d.op ≠ .movdquSt base src disp := by
    intro base src disp hcon
    have hred : istVecRegisterOp (.movdquSt base src disp) = false := rfl
    rw [← hcon] at hred
    rw [hred] at hreg
    cases hreg
  exact stepIntVec_speicher d t t' hw b cpu k hok hgate hstep hA hU

/-- The register plug IS the accepted step: success unfolds to the
    accepted equation over the machine projection (lifted, never
    redefined). -/
theorem vecRegSchritt_gleich (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (k : KontrollBild) (d : IntVecDec)
    (t' : FpZustand)
    (hreg : istVecRegisterOp d.op = true)
    (hs : stepIntVec d (projFp m c) m.hw (m.bereit c) cpu k =
      some t') :
    vecRegSchritt m c cpu k d = some (setKernVonFp m c t') := by
  unfold vecRegSchritt
  rw [if_pos hreg, hs]

/-- Machine vector load: gates (length, legacy admission, `#GP`
    alignment for the `movdqa` shape) then sixteen TSO byte
    observations with forwarding; the destination XMM holds the
    observed word and RIP advances. Memory and buffers are kept. -/
def vecLadeSchritt (m : HwMaschine) (c : Nat) (cpu : CpuMerkmal)
    (k : KontrollBild) (d : IntVecDec) : Option HwMaschine :=
  match d.op with
  | .movdqaLd dst base disp =>
    match laengeOk d.laenge, vektorLegacyZugelassen m.hw (m.bereit c)
      cpu k with
    | true, true =>
      if vektorGpFehler (effAddr (projZustand m c) base disp)
        .ausgerichtet then none
      else
        match vecLaden (tsoAnsicht m) c (effAddr (projZustand m c) base disp) with
        | some v =>
          some (setKernVonFp m c { projFp m c with kern := { (projFp m c).kern with rip := ripNach (projFp m c).kern.rip d.laenge }, xmm := xmmSet (projFp m c).xmm dst v })
        | none => none
    | _, _ => none
  | .movdquLd dst base disp =>
    match laengeOk d.laenge, vektorLegacyZugelassen m.hw (m.bereit c)
      cpu k with
    | true, true =>
      match vecLaden (tsoAnsicht m) c (effAddr (projZustand m c) base disp) with
      | some v =>
        some (setKernVonFp m c { projFp m c with kern := { (projFp m c).kern with rip := ripNach (projFp m c).kern.rip d.laenge }, xmm := xmmSet (projFp m c).xmm dst v })
      | none => none
    | _, _ => none
  | _ => none

/-- Machine vector store: gates (length, legacy admission, `#GP`
    alignment for the `movdqa` shape) then sixteen buffered TSO byte
    issues of the source XMM word. Canonical memory is unchanged
    (buffer only); the accepted direct `vecWrite` effect is never
    substituted. -/
def vecSpeicherSchritt (m : HwMaschine) (c : Nat) (cpu : CpuMerkmal)
    (k : KontrollBild) (d : IntVecDec) : Option HwMaschine :=
  match d.op with
  | .movdqaSt base src disp =>
    match laengeOk d.laenge, vektorLegacyZugelassen m.hw (m.bereit c)
      cpu k with
    | true, true =>
      if vektorGpFehler (effAddr (projZustand m c) base disp)
        .ausgerichtet then none
      else
        match vecSpeichern (tsoAnsicht m) c (effAddr (projZustand m c) base disp) ((projFp m c).xmm src) with
        | some s' => some (setTso m s')
        | none => none
    | _, _ => none
  | .movdquSt base src disp =>
    match laengeOk d.laenge, vektorLegacyZugelassen m.hw (m.bereit c)
      cpu k with
    | true, true =>
      match vecSpeichern (tsoAnsicht m) c (effAddr (projZustand m c) base disp) ((projFp m c).xmm src) with
      | some s' => some (setTso m s')
      | none => none
    | _, _ => none
  | _ => none

/-! ## 7. Events, adapter plug, and the extended step relation.

  The family's event type carries the checked CPU/control inputs, so
  the adapter checks them per step, never assuming them. The extended
  relation embeds `HwSchritt` exactly (`alt`, with projection back)
  and adds the register rows plus the four TSO memory rows. -/

/-- Vector family events on the coherent machine: register execution,
    TSO loads/stores of whole packed words, the old machine events,
    and explicit refusal. -/
inductive HwVecEreignis where
  | hwAlt : HwEreignis → HwVecEreignis
  | vecReg : Nat → CpuMerkmal → KontrollBild → IntVecDec → HwVecEreignis
  | vecLade : Nat → CpuMerkmal → KontrollBild → IntVecDec → HwVecEreignis
  | vecSpeichere : Nat → CpuMerkmal → KontrollBild → IntVecDec →
      HwVecEreignis
  | verweigert : Nat → HwVecEreignis
  deriving DecidableEq, Repr

/-- The vector producer plug: register rows through the accepted
    evaluator, memory rows through the TSO path, everything else
    refused. A mismatched core is refused, never rerouted. -/
def adapterVec : HwAdapter HwVecEreignis :=
  ⟨fun m c e => match e with
    | .vecReg c' cpu k d =>
      if c' = c then vecRegSchritt m c cpu k d else none
    | .vecLade c' cpu k d =>
      if c' = c then vecLadeSchritt m c cpu k d else none
    | .vecSpeichere c' cpu k d =>
      if c' = c then vecSpeicherSchritt m c cpu k d else none
    | _ => none⟩

/-- The extended step relation: the old coherent steps exactly
    (`alt`), the eleven register rows over the accepted evaluator
    (`reg`, memory-unchanged gate like `HwSchritt.reg`), the two
    aligned/unaligned TSO loads (`ladeA`/`ladeU`) and the two TSO
    stores (`speichereA`/`speichereU`), plus explicit fetch refusal
    (`fehler`). -/
inductive HwVecSchritt : HwMaschine → HwMaschine → HwVecEreignis → Prop where
  | alt {m m' : HwMaschine} {e : HwEreignis} (h : HwSchritt m m' e) :
      HwVecSchritt m m' (.hwAlt e)
  | reg {m : HwMaschine} {c : Nat} {cpu : CpuMerkmal}
      {k : KontrollBild} {d : IntVecDec} {t' : FpZustand}
      (hreg : istVecRegisterOp d.op = true)
      (hok : laengeOk d.laenge = true)
      (hgate : vektorLegacyZugelassen m.hw (m.bereit c) cpu k = true)
      (hstep : stepIntVec d (projFp m c) m.hw (m.bereit c) cpu k =
        some t')
      (hmem : t'.kern.speicher = m.mem) :
      HwVecSchritt m (setKernVonFp m c t') (.vecReg c cpu k d)
  | ladeA {m : HwMaschine} {c : Nat} {cpu : CpuMerkmal}
      {k : KontrollBild} {d : IntVecDec} {dst : XmmReg}
      {base : Register} {disp : BitVec 32} {v : Vektor}
      (hop : d.op = .movdqaLd dst base disp)
      (hok : laengeOk d.laenge = true)
      (hgate : vektorLegacyZugelassen m.hw (m.bereit c) cpu k = true)
      (hgp : vektorGpFehler (effAddr (projZustand m c) base disp)
        .ausgerichtet = false)
      (hread : vecLaden (tsoAnsicht m) c
        (effAddr (projZustand m c) base disp) = some v) :
      HwVecSchritt m (setKernVonFp m c { projFp m c with kern := { (projFp m c).kern with rip := ripNach (projFp m c).kern.rip d.laenge }, xmm := xmmSet (projFp m c).xmm dst v }) (.vecLade c cpu k d)
  | ladeU {m : HwMaschine} {c : Nat} {cpu : CpuMerkmal}
      {k : KontrollBild} {d : IntVecDec} {dst : XmmReg}
      {base : Register} {disp : BitVec 32} {v : Vektor}
      (hop : d.op = .movdquLd dst base disp)
      (hok : laengeOk d.laenge = true)
      (hgate : vektorLegacyZugelassen m.hw (m.bereit c) cpu k = true)
      (hread : vecLaden (tsoAnsicht m) c
        (effAddr (projZustand m c) base disp) = some v) :
      HwVecSchritt m (setKernVonFp m c { projFp m c with kern := { (projFp m c).kern with rip := ripNach (projFp m c).kern.rip d.laenge }, xmm := xmmSet (projFp m c).xmm dst v }) (.vecLade c cpu k d)
  | speichereA {m : HwMaschine} {c : Nat} {cpu : CpuMerkmal}
      {k : KontrollBild} {d : IntVecDec} {base : Register}
      {src : XmmReg} {disp : BitVec 32} {s' : TSOZustand}
      (hop : d.op = .movdqaSt base src disp)
      (hok : laengeOk d.laenge = true)
      (hgate : vektorLegacyZugelassen m.hw (m.bereit c) cpu k = true)
      (hgp : vektorGpFehler (effAddr (projZustand m c) base disp)
        .ausgerichtet = false)
      (hwr : vecSpeichern (tsoAnsicht m) c
        (effAddr (projZustand m c) base disp) ((projFp m c).xmm src) =
        some s') :
      HwVecSchritt m (setTso m s') (.vecSpeichere c cpu k d)
  | speichereU {m : HwMaschine} {c : Nat} {cpu : CpuMerkmal}
      {k : KontrollBild} {d : IntVecDec} {base : Register}
      {src : XmmReg} {disp : BitVec 32} {s' : TSOZustand}
      (hop : d.op = .movdquSt base src disp)
      (hok : laengeOk d.laenge = true)
      (hgate : vektorLegacyZugelassen m.hw (m.bereit c) cpu k = true)
      (hwr : vecSpeichern (tsoAnsicht m) c
        (effAddr (projZustand m c) base disp) ((projFp m c).xmm src) =
        some s') :
      HwVecSchritt m (setTso m s') (.vecSpeichere c cpu k d)
  | fehler {m : HwMaschine} {c : Nat}
      (h : fetchIntVec (projFp m c) (geholt (projZustand m c)) = none) :
      HwVecSchritt m m (.verweigert c)

/-- Every extended step preserves well-formedness: core-data and
    memory/buffer updates alike leave the checked profiles untouched. -/
theorem hwVecSchritt_wf (m m' : HwMaschine) (e : HwVecEreignis)
    (h : HwVecSchritt m m' e) (hwf : HwWf m) : HwWf m' := by
  cases h with
  | alt h => exact hwSchritt_wf _ _ _ h hwf
  | reg hreg hok hgate hstep hmem => exact setKernDaten_wf _ _ _ hwf
  | ladeA hop hok hgate hgp hread => exact setKernDaten_wf _ _ _ hwf
  | ladeU hop hok hgate hread => exact setKernDaten_wf _ _ _ hwf
  | speichereA hop hok hgate hgp hwr => exact setTso_wf _ _ hwf
  | speichereU hop hok hgate hwr => exact setTso_wf _ _ hwf
  | fehler h => exact hwf

/-- Exact embedding: every old coherent step is an extended step. -/
theorem hwVecSchritt_einbettet (m m' : HwMaschine) (e : HwEreignis)
    (h : HwSchritt m m' e) : HwVecSchritt m m' (.hwAlt e) :=
  .alt h

/-- Exact projection: an embedded step is the old step back. -/
theorem hwVecSchritt_projiziert (m m' : HwMaschine) (e : HwEreignis)
    (h : HwVecSchritt m m' (.hwAlt e)) : HwSchritt m m' e := by
  cases h with
  | alt h => exact h

/-- The adapter refuses old events: nothing is admitted silently. -/
theorem adapterVec_verweigert_alt (m : HwMaschine) (c : Nat)
    (e : HwEreignis) :
    adapterVec.schritt m c (.hwAlt e) = none := rfl

/-- The adapter refuses bare refusals. -/
theorem adapterVec_verweigert_fehler (m : HwMaschine) (c d : Nat) :
    adapterVec.schritt m c (.verweigert d) = none := rfl

/-- A mismatched core is refused on the register path, never rerouted. -/
theorem adapterVec_fremder_kern_reg (m : HwMaschine) (c c' : Nat)
    (cpu : CpuMerkmal) (k : KontrollBild) (d : IntVecDec)
    (hne : c' ≠ c) :
    adapterVec.schritt m c (.vecReg c' cpu k d) = none := by
  show (if c' = c then vecRegSchritt m c cpu k d else none) = none
  exact if_neg hne

/-- A mismatched core is refused on the load path. -/
theorem adapterVec_fremder_kern_lade (m : HwMaschine) (c c' : Nat)
    (cpu : CpuMerkmal) (k : KontrollBild) (d : IntVecDec)
    (hne : c' ≠ c) :
    adapterVec.schritt m c (.vecLade c' cpu k d) = none := by
  show (if c' = c then vecLadeSchritt m c cpu k d else none) = none
  exact if_neg hne

/-- A mismatched core is refused on the store path. -/
theorem adapterVec_fremder_kern_speichere (m : HwMaschine) (c c' : Nat)
    (cpu : CpuMerkmal) (k : KontrollBild) (d : IntVecDec)
    (hne : c' ≠ c) :
    adapterVec.schritt m c (.vecSpeichere c' cpu k d) = none := by
  show (if c' = c then vecSpeicherSchritt m c cpu k d else none) = none
  exact if_neg hne

/-- On its own core the adapter IS the register plug. -/
theorem adapterVec_reg (m : HwMaschine) (c : Nat) (cpu : CpuMerkmal)
    (k : KontrollBild) (d : IntVecDec) :
    adapterVec.schritt m c (.vecReg c cpu k d) =
      vecRegSchritt m c cpu k d := by
  show (if c = c then vecRegSchritt m c cpu k d else none) = _
  rw [if_pos rfl]

/-- On its own core the adapter IS the load plug. -/
theorem adapterVec_lade (m : HwMaschine) (c : Nat) (cpu : CpuMerkmal)
    (k : KontrollBild) (d : IntVecDec) :
    adapterVec.schritt m c (.vecLade c cpu k d) =
      vecLadeSchritt m c cpu k d := by
  show (if c = c then vecLadeSchritt m c cpu k d else none) = _
  rw [if_pos rfl]

/-- On its own core the adapter IS the store plug. -/
theorem adapterVec_speichere (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (k : KontrollBild) (d : IntVecDec) :
    adapterVec.schritt m c (.vecSpeichere c cpu k d) =
      vecSpeicherSchritt m c cpu k d := by
  show (if c = c then vecSpeicherSchritt m c cpu k d else none) = _
  rw [if_pos rfl]

/-- A successful machine load IS an extended step: the equation
    unfolds to the structured premises. -/
theorem vecLade_ist_schritt (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (k : KontrollBild) (d : IntVecDec)
    (m' : HwMaschine)
    (h : vecLadeSchritt m c cpu k d = some m') :
    HwVecSchritt m m' (.vecLade c cpu k d) := by
  unfold vecLadeSchritt at h
  cases hop : d.op with
  | paddbRR dst src =>
    rw [hop] at h
    dsimp only at h
    cases h
  | paddwRR dst src =>
    rw [hop] at h
    dsimp only at h
    cases h
  | padddRR dst src =>
    rw [hop] at h
    dsimp only at h
    cases h
  | paddqRR dst src =>
    rw [hop] at h
    dsimp only at h
    cases h
  | pandRR dst src =>
    rw [hop] at h
    dsimp only at h
    cases h
  | porRR dst src =>
    rw [hop] at h
    dsimp only at h
    cases h
  | pxorRR dst src =>
    rw [hop] at h
    dsimp only at h
    cases h
  | psllqRR dst cnt =>
    rw [hop] at h
    dsimp only at h
    cases h
  | psrlqRR dst cnt =>
    rw [hop] at h
    dsimp only at h
    cases h
  | psllqImm dst imm =>
    rw [hop] at h
    dsimp only at h
    cases h
  | psrlqImm dst imm =>
    rw [hop] at h
    dsimp only at h
    cases h
  | movdqaLd dst base disp =>
    rw [hop] at h
    dsimp only at h
    cases hg1 : laengeOk d.laenge with
    | false =>
      rw [hg1] at h
      dsimp only at h
      cases h
    | true =>
      cases hg2 : vektorLegacyZugelassen m.hw (m.bereit c) cpu k with
      | false =>
        rw [hg1, hg2] at h
        dsimp only at h
        cases h
      | true =>
        rw [hg1, hg2] at h
        dsimp only at h
        cases hgp : vektorGpFehler (effAddr (projZustand m c) base disp)
            .ausgerichtet with
        | true =>
          rw [if_pos hgp] at h
          cases h
        | false =>
          have hneg : ¬vektorGpFehler (effAddr (projZustand m c) base disp)
            .ausgerichtet = true := by
            simp [hgp]
          rw [if_neg hneg] at h
          cases hrd : vecLaden (tsoAnsicht m) c
              (effAddr (projZustand m c) base disp) with
          | none =>
            rw [hrd] at h
            dsimp only at h
            cases h
          | some v =>
            rw [hrd] at h
            dsimp only at h
            obtain rfl := Option.some_inj.mp h
            exact .ladeA hop hg1 hg2 hgp hrd
  | movdqaSt base src disp =>
    rw [hop] at h
    dsimp only at h
    cases h
  | movdquLd dst base disp =>
    rw [hop] at h
    dsimp only at h
    cases hg1 : laengeOk d.laenge with
    | false =>
      rw [hg1] at h
      dsimp only at h
      cases h
    | true =>
      cases hg2 : vektorLegacyZugelassen m.hw (m.bereit c) cpu k with
      | false =>
        rw [hg1, hg2] at h
        dsimp only at h
        cases h
      | true =>
        rw [hg1, hg2] at h
        dsimp only at h
        cases hrd : vecLaden (tsoAnsicht m) c
            (effAddr (projZustand m c) base disp) with
        | none =>
          rw [hrd] at h
          dsimp only at h
          cases h
        | some v =>
          rw [hrd] at h
          dsimp only at h
          obtain rfl := Option.some_inj.mp h
          exact .ladeU hop hg1 hg2 hrd
  | movdquSt base src disp =>
    rw [hop] at h
    dsimp only at h
    cases h

/-- A successful machine store IS an extended step. -/
theorem vecSpeichere_ist_schritt (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (k : KontrollBild) (d : IntVecDec)
    (m' : HwMaschine)
    (h : vecSpeicherSchritt m c cpu k d = some m') :
    HwVecSchritt m m' (.vecSpeichere c cpu k d) := by
  unfold vecSpeicherSchritt at h
  cases hop : d.op with
  | paddbRR dst src =>
    rw [hop] at h
    dsimp only at h
    cases h
  | paddwRR dst src =>
    rw [hop] at h
    dsimp only at h
    cases h
  | padddRR dst src =>
    rw [hop] at h
    dsimp only at h
    cases h
  | paddqRR dst src =>
    rw [hop] at h
    dsimp only at h
    cases h
  | pandRR dst src =>
    rw [hop] at h
    dsimp only at h
    cases h
  | porRR dst src =>
    rw [hop] at h
    dsimp only at h
    cases h
  | pxorRR dst src =>
    rw [hop] at h
    dsimp only at h
    cases h
  | psllqRR dst cnt =>
    rw [hop] at h
    dsimp only at h
    cases h
  | psrlqRR dst cnt =>
    rw [hop] at h
    dsimp only at h
    cases h
  | psllqImm dst imm =>
    rw [hop] at h
    dsimp only at h
    cases h
  | psrlqImm dst imm =>
    rw [hop] at h
    dsimp only at h
    cases h
  | movdqaLd dst base disp =>
    rw [hop] at h
    dsimp only at h
    cases h
  | movdqaSt base src disp =>
    rw [hop] at h
    dsimp only at h
    cases hg1 : laengeOk d.laenge with
    | false =>
      rw [hg1] at h
      dsimp only at h
      cases h
    | true =>
      cases hg2 : vektorLegacyZugelassen m.hw (m.bereit c) cpu k with
      | false =>
        rw [hg1, hg2] at h
        dsimp only at h
        cases h
      | true =>
        rw [hg1, hg2] at h
        dsimp only at h
        cases hgp : vektorGpFehler (effAddr (projZustand m c) base disp)
            .ausgerichtet with
        | true =>
          rw [if_pos hgp] at h
          cases h
        | false =>
          have hneg : ¬vektorGpFehler (effAddr (projZustand m c) base disp)
            .ausgerichtet = true := by
            simp [hgp]
          rw [if_neg hneg] at h
          cases hwr : vecSpeichern (tsoAnsicht m) c
              (effAddr (projZustand m c) base disp)
              ((projFp m c).xmm src) with
          | none =>
            rw [hwr] at h
            dsimp only at h
            cases h
          | some s' =>
            rw [hwr] at h
            dsimp only at h
            obtain rfl := Option.some_inj.mp h
            exact .speichereA hop hg1 hg2 hgp hwr
  | movdquLd dst base disp =>
    rw [hop] at h
    dsimp only at h
    cases h
  | movdquSt base src disp =>
    rw [hop] at h
    dsimp only at h
    cases hg1 : laengeOk d.laenge with
    | false =>
      rw [hg1] at h
      dsimp only at h
      cases h
    | true =>
      cases hg2 : vektorLegacyZugelassen m.hw (m.bereit c) cpu k with
      | false =>
        rw [hg1, hg2] at h
        dsimp only at h
        cases h
      | true =>
        rw [hg1, hg2] at h
        dsimp only at h
        cases hwr : vecSpeichern (tsoAnsicht m) c
            (effAddr (projZustand m c) base disp)
            ((projFp m c).xmm src) with
        | none =>
          rw [hwr] at h
          dsimp only at h
          cases h
        | some s' =>
          rw [hwr] at h
          dsimp only at h
          obtain rfl := Option.some_inj.mp h
          exact .speichereU hop hg1 hg2 hwr

end Gabbro.Grammatik.X86
