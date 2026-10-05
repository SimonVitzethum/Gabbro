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
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Befehle.Vektor.VectorIntegerHardwareForms
import Grammatik.X86.Befehle.Vektor.VectorHardwareProfile
import Grammatik.X86.Befehle.Vektor.VectorFootprints
import Grammatik.X86.TSO.Verriegelt.ConcurrentIntegerExecution

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

/- Folded-issue memory and foreign-buffer facts (`issueListe_mem`,
   `issueListe_anderer_kern`) are reused from
   `ConcurrentIntegerExecution`, never duplicated here. -/

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

/-! ## 8. Planted refusals: gates refuse, never guess.

  Each enabled-state side (silicon SSE2, control freedom, OS vector
  state, finite profile admission), the decode length, `#GP`
  alignment and per-byte permissions refuse explicitly -- on the
  machine plugs, reusing the accepted gate lemmas. -/

/-- A bad decode length refuses the register plug. -/
theorem vecReg_laenge_verweigert (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (k : KontrollBild) (d : IntVecDec)
    (hreg : istVecRegisterOp d.op = true)
    (h : laengeOk d.laenge = false) :
    vecRegSchritt m c cpu k d = none := by
  have hn := stepIntVec_laenge_verweigert d (projFp m c) m.hw
    (m.bereit c) cpu k h
  simp only [vecRegSchritt, if_pos hreg, hn]

/-- Refused legacy admission refuses the register plug (validator
    admission, not a hardware fault). -/
theorem vecReg_profil_verweigert (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (k : KontrollBild) (d : IntVecDec)
    (hok : laengeOk d.laenge = true)
    (hreg : istVecRegisterOp d.op = true)
    (h : vektorLegacyZugelassen m.hw (m.bereit c) cpu k = false) :
    vecRegSchritt m c cpu k d = none := by
  have hn := stepIntVec_profil_verweigert d (projFp m c) m.hw
    (m.bereit c) cpu k hok h
  simp only [vecRegSchritt, if_pos hreg, hn]

/-- No silicon SSE2 refuses, whatever the rest claims. -/
theorem vecReg_ohne_cpu (m : HwMaschine) (c : Nat) (cpu : CpuMerkmal)
    (k : KontrollBild) (d : IntVecDec)
    (hok : laengeOk d.laenge = true)
    (hreg : istVecRegisterOp d.op = true)
    (hcpu : cpu.hatSse2 = false) :
    vecRegSchritt m c cpu k d = none := by
  have hg := vektorLegacy_ohne_cpu m.hw (m.bereit c) cpu k hcpu
  exact vecReg_profil_verweigert m c cpu k d hok hreg hg

/-- Set control bits (emulation or task-switch) refuse. -/
theorem vecReg_ohne_kontrolle (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (k : KontrollBild) (d : IntVecDec)
    (hok : laengeOk d.laenge = true)
    (hreg : istVecRegisterOp d.op = true)
    (hk : kontrollSseLegacyFrei k = false) :
    vecRegSchritt m c cpu k d = none := by
  have hg := vektorLegacy_ohne_kontrolle m.hw (m.bereit c) cpu k hk
  exact vecReg_profil_verweigert m c cpu k d hok hreg hg

/-- A cleared OS vector-state bit refuses. -/
theorem vecReg_ohne_osxmm (m : HwMaschine) (c : Nat) (cpu : CpuMerkmal)
    (k : KontrollBild) (d : IntVecDec)
    (hok : laengeOk d.laenge = true)
    (hreg : istVecRegisterOp d.op = true)
    (hos : (m.bereit c).osXmm = false) :
    vecRegSchritt m c cpu k d = none := by
  have hg := vektorLegacy_ohne_osxmm m.hw (m.bereit c) cpu k hos
  exact vecReg_profil_verweigert m c cpu k d hok hreg hg

/-- A refused finite profile refuses, however ready the rest is. -/
theorem vecReg_ohne_merkmal (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (k : KontrollBild) (d : IntVecDec)
    (hok : laengeOk d.laenge = true)
    (hreg : istVecRegisterOp d.op = true)
    (hm : merkmalZugelassen m.hw (m.bereit c) .paketInt128 = false) :
    vecRegSchritt m c cpu k d = none := by
  have hg : vektorLegacyZugelassen m.hw (m.bereit c) cpu k = false := by
    unfold vektorLegacyZugelassen
    simp [hm]
  exact vecReg_profil_verweigert m c cpu k d hok hreg hg

/-- SHARED ROW: the admitted PXOR rides the machine plug exactly as
    the accepted gated step under the old (stronger) gate. -/
theorem vecRegSchritt_pxor_agree (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (dst src : XmmReg) (n : Nat) (t' : FpZustand)
    (hgate : vektorHwZugelassen m.hw (m.bereit c) cpu x k = true)
    (hok : laengeOk n = true)
    (hs : stepVector (⟨.pxorRR dst src, n⟩ : VectorDec) (projFp m c)
      (m.bereit c) = some t') :
    vecRegSchritt m c cpu k ⟨.pxorRR dst src, n⟩ =
      some (setKernVonFp m c t') := by
  have hs' := stepIntVec_pxor_agree_step (⟨.pxorRR dst src, n⟩ : VectorDec)
    (projFp m c) t' m.hw (m.bereit c) cpu x k dst src hgate hok rfl hs
  exact vecRegSchritt_gleich m c cpu k ⟨.pxorRR dst src, n⟩ t' rfl hs'

/-- SHARED ROW: the admitted PADDQ rides the machine plug exactly as
    the accepted gated step under the old (stronger) gate. -/
theorem vecRegSchritt_paddq_agree (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (dst src : XmmReg) (n : Nat) (t' : FpZustand)
    (hgate : vektorHwZugelassen m.hw (m.bereit c) cpu x k = true)
    (hok : laengeOk n = true)
    (hs : stepVector (⟨.paddqRR dst src, n⟩ : VectorDec) (projFp m c)
      (m.bereit c) = some t') :
    vecRegSchritt m c cpu k ⟨.paddqRR dst src, n⟩ =
      some (setKernVonFp m c t') := by
  have hs' := stepIntVec_paddq_agree_step (⟨.paddqRR dst src, n⟩ : VectorDec)
    (projFp m c) t' m.hw (m.bereit c) cpu x k dst src hgate hok rfl hs
  exact vecRegSchritt_gleich m c cpu k ⟨.paddqRR dst src, n⟩ t' rfl hs'

/-- FETCH BRIDGE: a fetched selected form steps through the register
    plug and through the fetched byte step together, with canonical
    memory unchanged. A forged `IntVecDec` cannot inject an
    instruction: only `fetchIntVec` over actual memory feeds the step;
    the length guard comes from the fetch discipline itself and the
    hardware gate is recovered from the successful selected step,
    never assumed. -/
theorem hvec_fetch_bruecke (m : HwMaschine) (c : Nat) (cpu : CpuMerkmal)
    (k : KontrollBild) (d : IntVecDec) (rest : List Byte)
    (t' : FpZustand)
    (hf : fetchIntVec (projFp m c) (geholt (projZustand m c)) =
      some (d, rest))
    (hreg : istVecRegisterOp d.op = true)
    (hs : stepIntVec d (projFp m c) m.hw (m.bereit c) cpu k =
      some t') :
    vecRegSchritt m c cpu k d = some (setKernVonFp m c t') ∧
      intVecByteschritt (projFp m c) m.hw (m.bereit c) cpu k =
        some t' ∧
      t'.kern.speicher = m.mem := by
  have hok : laengeOk d.laenge = true :=
    (fetchIntVec_erfolg (projFp m c) (geholt (projZustand m c)) d rest
      hf).2.2.1
  have hgate : vektorLegacyZugelassen m.hw (m.bereit c) cpu k = true := by
    cases hg : vektorLegacyZugelassen m.hw (m.bereit c) cpu k with
    | true => rfl
    | false =>
      have hn := stepIntVec_profil_verweigert d (projFp m c) m.hw
        (m.bereit c) cpu k hok hg
      rw [hn] at hs
      cases hs
  refine ⟨vecRegSchritt_gleich m c cpu k d t' hreg hs,
    intVec_fetch_bridge _ _ _ _ _ _ _ _ hf hs, ?_⟩
  exact vecRegSchritt_speicher d (projFp m c) t' m.hw (m.bereit c)
    cpu k hreg hok hgate hs

/-- A fold of issues refuses wherever any entry lacks write
    permission: one refused byte fails the whole vector. Permissions
    survive each issue, so the first refusal is reached. -/
theorem issueListe_verweigert (l : List TSOEintrag) (s : TSOZustand)
    (c : Nat) (e : TSOEintrag) (hmem : e ∈ l)
    (h : s.mem.schreibbar e.addr = false) :
    issueListe s c l = none := by
  induction l generalizing s with
  | nil =>
    simp at hmem
  | cons hd tl ih =>
    have heq : issueListe s c (hd :: tl) =
        match issueByte s c hd.addr hd.wert with
        | none => (none : Option TSOZustand)
        | some s1 => issueListe s1 c tl := rfl
    rw [heq]
    simp only [List.mem_cons] at hmem
    rcases hmem with hhead | hmem2
    · rw [hhead] at h
      have hn : issueByte s c hd.addr hd.wert = none := by
        unfold issueByte
        simp [h]
      rw [hn]
    · cases hb : issueByte s c hd.addr hd.wert with
      | none => rfl
      | some s1 =>
        have hperm : s1.mem.schreibbar e.addr = false := by
          have hp := issue_erhaelt_berechtigungen s s1 c hd.addr
            hd.wert hb
          rw [hp.2.1]
          exact h
        exact ih s1 hmem2 hperm

/-- A low-chunk entry is in the sixteen, by offset. -/
theorem vecEintraege_mem_lo_entry (a : Adresse) (v : Vektor) (k : Nat)
    (hk : k < 8) :
    (⟨addrOff a k, wortByte (vLo v) k⟩ : TSOEintrag) ∈
      vecEintraege a v := by
  have hk8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 := by
    omega
  rcases hk8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.Mem.head _
  · exact List.Mem.tail _ (List.Mem.head _)
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.head _)))
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.head _))))
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.head _))))))
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.head _)))))))

/-- A store without write permission at any low-chunk byte refuses on
    the machine (the `#GP` classification passes; the byte issue
    fails). -/
theorem vecSpeicherSchritt_schreibrecht (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (k : KontrollBild) (base : Register)
    (src : XmmReg) (disp : BitVec 32) (n k0 : Nat) (hk0 : k0 < 8)
    (hok : laengeOk n = true)
    (hgate : vektorLegacyZugelassen m.hw (m.bereit c) cpu k = true)
    (hperm : (tsoAnsicht m).mem.schreibbar
      (addrOff (effAddr (projZustand m c) base disp) k0) = false) :
    vecSpeicherSchritt m c cpu k ⟨.movdquSt base src disp, n⟩ =
      none := by
  have hn : vecSpeichern (tsoAnsicht m) c
      (effAddr (projZustand m c) base disp) ((projFp m c).xmm src) =
      none := by
    have hmem := vecEintraege_mem_lo_entry
      (effAddr (projZustand m c) base disp) ((projFp m c).xmm src) k0 hk0
    exact issueListe_verweigert _ _ _ _ hmem hperm
  simp only [vecSpeicherSchritt, hok, hgate, hn]

/-- A chunk load with an unreadable byte refuses: one failed `loadByte`
    fails the whole chunk. Cases on all eight bytes; the failing byte
    contradicts its `some` equation. -/
theorem ladeAcht_verweigert (s : TSOZustand) (c : Nat) (a : Adresse)
    (k0 : Nat) (hk0 : k0 < 8)
    (h : loadByte s c (addrOff a k0) = none) :
    ladeAcht s c a = none := by
  unfold ladeAcht
  cases h0 : loadByte s c (addrOff a 0) with
  | none => rfl
  | some b0 =>
    cases h1 : loadByte s c (addrOff a 1) with
    | none => rfl
    | some b1 =>
      cases h2 : loadByte s c (addrOff a 2) with
      | none => rfl
      | some b2 =>
        cases h3 : loadByte s c (addrOff a 3) with
        | none => rfl
        | some b3 =>
          cases h4 : loadByte s c (addrOff a 4) with
          | none => rfl
          | some b4 =>
            cases h5 : loadByte s c (addrOff a 5) with
            | none => rfl
            | some b5 =>
              cases h6 : loadByte s c (addrOff a 6) with
              | none => rfl
              | some b6 =>
                cases h7 : loadByte s c (addrOff a 7) with
                | none => rfl
                | some b7 =>
                  have hk8 : k0 = 0 ∨ k0 = 1 ∨ k0 = 2 ∨ k0 = 3 ∨
                      k0 = 4 ∨ k0 = 5 ∨ k0 = 6 ∨ k0 = 7 := by
                    omega
                  rcases hk8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
                  · rw [h0] at h
                    cases h
                  · rw [h1] at h
                    cases h
                  · rw [h2] at h
                    cases h
                  · rw [h3] at h
                    cases h
                  · rw [h4] at h
                    cases h
                  · rw [h5] at h
                    cases h
                  · rw [h6] at h
                    cases h
                  · rw [h7] at h
                    cases h

/-- A load without read permission at any low-chunk byte refuses on
    the machine. -/
theorem vecLadeSchritt_leserecht (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (k : KontrollBild) (dst : XmmReg)
    (base : Register) (disp : BitVec 32) (n k0 : Nat) (hk0 : k0 < 8)
    (hok : laengeOk n = true)
    (hgate : vektorLegacyZugelassen m.hw (m.bereit c) cpu k = true)
    (hperm : loadByte (tsoAnsicht m) c
      (addrOff (effAddr (projZustand m c) base disp) k0) = none) :
    vecLadeSchritt m c cpu k ⟨.movdquLd dst base disp, n⟩ = none := by
  have hn : ladeAcht (tsoAnsicht m) c
      (effAddr (projZustand m c) base disp) = none :=
    ladeAcht_verweigert _ _ _ k0 hk0 hperm
  have hnV : vecLaden (tsoAnsicht m) c
      (effAddr (projZustand m c) base disp) = none := by
    have e : vecLaden (tsoAnsicht m) c
        (effAddr (projZustand m c) base disp) =
        match ladeAcht (tsoAnsicht m) c
          (effAddr (projZustand m c) base disp),
          ladeAcht (tsoAnsicht m) c
            (vecHiAddr (effAddr (projZustand m c) base disp)) with
        | some lo, some hi => some (vecJoin lo hi)
        | _, _ => (none : Option Vektor) := rfl
    rw [e, hn]
  simp only [vecLadeSchritt, hok, hgate, hnV]

/-- A `#GP` classification refuses the aligned machine load (the
    decoder accepts these bytes; the step refuses them). -/
theorem vecLadeSchritt_gp_a (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (k : KontrollBild) (dst : XmmReg)
    (base : Register) (disp : BitVec 32) (n : Nat)
    (hok : laengeOk n = true)
    (hgate : vektorLegacyZugelassen m.hw (m.bereit c) cpu k = true)
    (hgp : vektorGpFehler (effAddr (projZustand m c) base disp)
      .ausgerichtet = true) :
    vecLadeSchritt m c cpu k ⟨.movdqaLd dst base disp, n⟩ = none := by
  simp only [vecLadeSchritt, hok, hgate, if_pos hgp]

/-- A `#GP` classification refuses the aligned machine store. -/
theorem vecSpeicherSchritt_gp_a (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (k : KontrollBild) (base : Register)
    (src : XmmReg) (disp : BitVec 32) (n : Nat)
    (hok : laengeOk n = true)
    (hgate : vektorLegacyZugelassen m.hw (m.bereit c) cpu k = true)
    (hgp : vektorGpFehler (effAddr (projZustand m c) base disp)
      .ausgerichtet = true) :
    vecSpeicherSchritt m c cpu k ⟨.movdqaSt base src disp, n⟩ =
      none := by
  simp only [vecSpeicherSchritt, hok, hgate, if_pos hgp]

/-! ## 9. Joint witness: two cores, fetched bytes, buffered vector store.

  Core 0 fetches a `paddb` (lane-separated result, low byte wrapping
  `0xFF + 0x02` to `0x01` while higher lanes add independently) then a
  `movdqa` store of the whole packed word through sixteen TSO byte
  issues; core 0 observes its bytes by forwarding while core 1 still
  reads zero; the drain observably changes shared memory on both
  cores, with the torn halfway state standing. Every claim below is a
  closed decidable observation; no machine equality is ever decided. -/

/-- Witness image: `paddb` (5 bytes) then `movdqa` store (9 bytes). -/
def hvecWitBild : List Byte :=
  encodeIntVec (.paddbRR .xmm0 .xmm1) ++
    encodeIntVec (.movdqaSt .rax .xmm0 (0 : BitVec 32))

/-- Witness bytes: the image at 4096, zeroes elsewhere. -/
def hvecWitBytes (a : Adresse) : Byte :=
  if a.toNat < 4096 then BitVec.ofNat 8 0
  else
    match hvecWitBild[a.toNat - 4096]? with
    | some b => b
    | none => BitVec.ofNat 8 0

/-- Witness code permission: exactly the 14 image bytes. -/
def hvecWitCode (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4096 + 14)

/-- Witness data permission: sixteen bytes at 8192. -/
def hvecWitDaten (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8192 + 16)

/-- Witness shared memory: code is execute-only, data read/write. -/
def hvecWitMem : Speicher :=
  { bytes := hvecWitBytes, lesbar := hvecWitDaten,
    schreibbar := hvecWitDaten, ausfuehrbar := hvecWitCode }

/-- Witness packed operands: low byte wraps, higher lanes add cleanly. -/
def hvecWitA : Vektor := BitVec.ofNat 128 0x010101010101010101010101010101FF

/-- Witness packed operands: the low count byte is `0x02`. -/
def hvecWitB : Vektor := BitVec.ofNat 128 0x0F0E0D0C0B0A09080706050403020102

/-- Witness core-0 registers: data address in rax. -/
def hvecWitReg0 : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 8192
  else if q = Register.rsp then BitVec.ofNat 64 8704
  else BitVec.ofNat 64 0

/-- Witness core-0 XMM: the operands in xmm0/xmm1. -/
def hvecWitXmm0 : XmmDatei := fun q =>
  if q = .xmm0 then hvecWitA
  else if q = .xmm1 then hvecWitB
  else BitVec.ofNat 128 0

/-- Witness core data: core 0 runs at 4096, core 1 idles on the
    (non-executable) data page. -/
def hvecWitKern : Nat → HwKern
  | 0 => ⟨hvecWitReg0, zeugeFlags, BitVec.ofNat 64 4096, hvecWitXmm0,
      kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 8192, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness start machine: shared memory, two cores, empty buffers,
    full silicon with OS vector state. -/
def hvecWitStart : HwMaschine :=
  ⟨hvecWitMem, hvecWitKern, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- Witness data address. -/
def hvecWitAdr : Adresse := BitVec.ofNat 64 8192

/-- The legacy gate admits at the witness profiles. -/
theorem hvecWit_gate :
    vektorLegacyZugelassen basisHw basisBereit basisCpu
      basisKontrolle = true := by
  decide

/-- The witness machine is well-formed: full silicon admits all. -/
theorem hvecWitStart_wf : HwWf hvecWitStart := by
  intro c f _
  cases f <;> rfl

/-- The decoded register form: `paddb` over five bytes. -/
def hvecWitD1 : IntVecDec := ⟨.paddbRR .xmm0 .xmm1, 5⟩

/-- The decoded store form: `movdqa` store over nine bytes. -/
def hvecWitD2 : IntVecDec := ⟨.movdqaSt .rax .xmm0 (0 : BitVec 32), 9⟩

/-- The explicit `paddb` successor: RIP past five bytes, destination
    holding the accepted byte-lane sum. -/
def hvecWitT1 : FpZustand :=
  { projFp hvecWitStart 0 with kern := { (projFp hvecWitStart 0).kern with rip := ripNach (projFp hvecWitStart 0).kern.rip hvecWitD1.laenge }, xmm := xmmSet (projFp hvecWitStart 0).xmm .xmm0 (vecAdd .b8 hvecWitA hvecWitB) }

/-- The explicit machine successor after the `paddb`. -/
def hvecWitM1 : HwMaschine := setKernVonFp hvecWitStart 0 hvecWitT1

/-- The stored packed word: the accepted byte-lane sum. -/
def hvecWitC : Vektor := vecAdd .b8 hvecWitA hvecWitB

/-- The explicit TSO state after the sixteen issues: shared memory
    kept, acting buffer carrying exactly the sixteen entries. -/
def hvecWitS2 : TSOZustand :=
  ⟨hvecWitMem, fun d =>
    if d = 0 then vecEintraege hvecWitAdr hvecWitC else []⟩

/-- The explicit machine successor after the `movdqa` store. -/
def hvecWitM2 : HwMaschine := setTso hvecWitM1 hvecWitS2

/-! ## 10. Register stage: the `paddb` with lane separation. -/

/-- A register plug success with checked gates IS an extended step. -/
theorem vecReg_ist_schritt (m : HwMaschine) (c : Nat) (cpu : CpuMerkmal)
    (k : KontrollBild) (d : IntVecDec) (t' : FpZustand)
    (hreg : istVecRegisterOp d.op = true)
    (hok : laengeOk d.laenge = true)
    (hgate : vektorLegacyZugelassen m.hw (m.bereit c) cpu k = true)
    (hs : stepIntVec d (projFp m c) m.hw (m.bereit c) cpu k = some t')
    (hmem : t'.kern.speicher = m.mem) :
    HwVecSchritt m (setKernVonFp m c t') (.vecReg c cpu k d) :=
  .reg hreg hok hgate hs hmem

/-- First machine step: the register plug on core 0. -/
def hvecWitR1 : Option HwMaschine :=
  vecRegSchritt hvecWitStart 0 basisCpu basisKontrolle hvecWitD1

/-- Read core RIP out of a machine outcome. -/
def hvecRipOut (o : Option HwMaschine) (c : Nat) : Option Wort :=
  match o with
  | some m => some (m.kerne c).rip
  | none => none

/-- Read a byte lane out of a machine outcome. -/
def hvecLaneOut (o : Option HwMaschine) (c : Nat) (q : XmmReg)
    (i : Nat) : Option Nat :=
  match o with
  | some m => some (laneNat .b8 ((m.kerne c).xmm q) i)
  | none => none

/-- Read a shared-memory byte out of a machine outcome. -/
def hvecMemOut (o : Option HwMaschine) (a : Adresse) : Option Byte :=
  match o with
  | some m => some (m.mem.bytes a)
  | none => none

/-- Read a buffer length out of a machine outcome. -/
def hvecBufOut (o : Option HwMaschine) (c : Nat) : Option Nat :=
  match o with
  | some m => some (m.puffer c).length
  | none => none

/-- Step one advances RIP past the 5-byte `paddb`. -/
theorem hvecWit_r1_rip :
    hvecRipOut hvecWitR1 0 = some (BitVec.ofNat 64 4101) := by
  decide

/-- Step one wraps lane 0 (`0xFF + 0x02` to `0x01`): no carry out. -/
theorem hvecWit_r1_lane0 :
    hvecLaneOut hvecWitR1 0 .xmm0 0 = some 1 := by
  decide

/-- Step one adds lane 1 independently (`0x01 + 0x01`): no carry in. -/
theorem hvecWit_r1_lane1 :
    hvecLaneOut hvecWitR1 0 .xmm0 1 = some 2 := by
  decide

/-- Step one leaves shared memory alone. -/
theorem hvecWit_r1_mem_still :
    hvecMemOut hvecWitR1 hvecWitAdr =
      some (BitVec.ofNat 8 0) := by
  decide

/-- Step one issues no buffer entry. -/
theorem hvecWit_r1_puffer_leer : hvecBufOut hvecWitR1 0 = some 0 := by
  decide

/-- The accepted `paddb` equation reaches the explicit successor. -/
theorem hvecWit_paddb :
    stepIntVec hvecWitD1 (projFp hvecWitStart 0) basisHw basisBereit
      basisCpu basisKontrolle = some hvecWitT1 :=
  stepIntVec_paddb hvecWitD1 (projFp hvecWitStart 0) basisHw
    basisBereit basisCpu basisKontrolle .xmm0 .xmm1 (by decide)
    hvecWit_gate rfl

/-- The `paddb` successor keeps shared memory. -/
theorem hvecWit_t1_mem : hvecWitT1.kern.speicher = hvecWitMem := rfl

/-- The plug reaches the explicit machine successor. -/
theorem hvecWit_r1 :
    hvecWitR1 = some hvecWitM1 :=
  vecRegSchritt_gleich hvecWitStart 0 basisCpu basisKontrolle
    hvecWitD1 hvecWitT1 rfl hvecWit_paddb

/-- The `paddb` is an extended step on the coherent machine. -/
theorem hvecWit_reg_schritt :
    HwVecSchritt hvecWitStart hvecWitM1
      (.vecReg 0 basisCpu basisKontrolle hvecWitD1) :=
  vecReg_ist_schritt hvecWitStart 0 basisCpu basisKontrolle hvecWitD1
    hvecWitT1 rfl (by decide) hvecWit_gate hvecWit_paddb hvecWit_t1_mem

/-! ## 11. Store stage: sixteen buffered issues, owner-only forwarding. -/

/-- FETCHED PIN: actual code bytes fetch to the `paddb` row with the
    nine store bytes of rest. -/
theorem hvecWit_fetch_pin :
    fetchIntVec (projFp hvecWitStart 0)
      (geholt (projZustand hvecWitStart 0)) =
      some (hvecWitD1, hvecWitBild.drop 5) := by
  decide

/-- Core 1 refuses: its RIP points at non-executable memory. -/
theorem hvecWit_kern1_verweigert :
    fetchIntVec (projFp hvecWitStart 1)
      (geholt (projZustand hvecWitStart 1)) = none := by
  decide

/-- Second machine step: the store plug on core 0 over the `paddb`
    successor. -/
def hvecWitS1 : Option HwMaschine :=
  match hvecWitR1 with
  | some m1 => vecSpeicherSchritt m1 0 basisCpu basisKontrolle hvecWitD2
  | none => none

/-- The store issues exactly sixteen buffer entries. -/
theorem hvecWit_s1_buflen : hvecBufOut hvecWitS1 0 = some 16 := by
  decide

/-- The store changes no canonical byte (buffer only). -/
theorem hvecWit_s1_mem_still :
    hvecMemOut hvecWitS1 hvecWitAdr =
      some (BitVec.ofNat 8 0) := by
  decide

/-- RIP is untouched by the store (driver state, not core data). -/
theorem hvecWit_s1_rip :
    hvecRipOut hvecWitS1 0 = some (BitVec.ofNat 64 4101) := by
  decide

/-- The sixteen issues compute as claimed: shared memory kept, acting
    buffer carrying exactly the sixteen entries. The folded buffer is
    extensionally (not definitionally) the stipulated one, so this goes
    through the fold lemmas. -/
theorem hvecWit_issue :
    vecSpeichern (tsoAnsicht hvecWitM1) 0
      (effAddr (projZustand hvecWitM1 0) .rax 0)
      ((projFp hvecWitM1 0).xmm .xmm0) = some hvecWitS2 := by
  have ha_eff : effAddr (projZustand hvecWitM1 0) .rax
      (0 : BitVec 32) = hvecWitAdr := by
    decide
  have hx_xmm : ((projFp hvecWitM1 0).xmm .xmm0) = hvecWitC := by
    rfl
  rw [ha_eff, hx_xmm]
  have hperm1 : schreibbar8 (tsoAnsicht hvecWitM1).mem hvecWitAdr =
      true := by
    decide
  have hperm2 : schreibbar8 (tsoAnsicht hvecWitM1).mem
      (vecHiAddr hvecWitAdr) = true := by
    decide
  obtain ⟨s', hs'⟩ := vecSpeichern_erfolg (tsoAnsicht hvecWitM1) 0
    hvecWitAdr hvecWitC hperm1 hperm2
  have hsI : issueListe (tsoAnsicht hvecWitM1) 0
      (vecEintraege hvecWitAdr hvecWitC) = some s' := hs'
  have hbuf0 : s'.puffer 0 = vecEintraege hvecWitAdr hvecWitC := by
    have ha := issueListe_haengt_an _ s' 0 _ hsI
    have hempty : (tsoAnsicht hvecWitM1).puffer 0 = [] := rfl
    rw [hempty] at ha
    exact ha
  have hbufd : ∀ d : Nat, d ≠ 0 → s'.puffer d = [] := by
    intro d hd
    have ha := issueListe_anderer_kern _ s' 0 _ d hd hsI
    have hempty : (tsoAnsicht hvecWitM1).puffer d = [] := rfl
    rw [hempty] at ha
    exact ha
  have hpuff : s'.puffer = hvecWitS2.puffer := by
    funext d
    show s'.puffer d =
      (if d = 0 then vecEintraege hvecWitAdr hvecWitC else [])
    by_cases hd : d = 0
    · subst hd
      rw [if_pos rfl]
      exact hbuf0
    · rw [if_neg hd]
      exact hbufd d hd
  have hmemM : s'.mem = hvecWitMem := by
    have hm := issueListe_mem _ s' 0 _ hsI
    have hme : (tsoAnsicht hvecWitM1).mem = hvecWitMem := rfl
    rw [hm]
    exact hme
  have hsurj : s' = ⟨s'.mem, s'.puffer⟩ := rfl
  rw [hs', hsurj, hmemM, hpuff]
  rfl

/-- No `#GP` at the witness store address (8192 is 16-aligned). -/
theorem hvecWit_gg :
    vektorGpFehler (effAddr (projZustand hvecWitM1 0) .rax 0)
      .ausgerichtet = false := by
  decide

/-- The legacy gate still admits over the `paddb` successor: profiles
    are untouched by core-data updates. -/
theorem hvecWit_gate_m1 :
    vektorLegacyZugelassen hvecWitM1.hw (hvecWitM1.bereit 0)
      basisCpu basisKontrolle = true :=
  hvecWit_gate

/-- The plug reaches the explicit machine successor. -/
theorem hvecWit_plug_s2 :
    vecSpeicherSchritt hvecWitM1 0 basisCpu basisKontrolle hvecWitD2 =
      some hvecWitM2 := by
  have hok9 : laengeOk 9 = true := by decide
  have hneg : ¬vektorGpFehler (effAddr (projZustand hvecWitM1 0) .rax 0)
    .ausgerichtet = true := by
    rw [hvecWit_gg]
    exact Bool.false_ne_true
  have eD : hvecWitD2 =
      ⟨.movdqaSt .rax .xmm0 (0 : BitVec 32), 9⟩ := rfl
  rw [eD]
  simp only [vecSpeicherSchritt, hok9, hvecWit_gate_m1, if_neg hneg,
    hvecWit_issue, hvecWitM2]

/-- The option-level step reaches the explicit machine successor. -/
theorem hvecWit_s1 :
    hvecWitS1 = some hvecWitM2 := by
  unfold hvecWitS1
  rw [hvecWit_r1]
  exact hvecWit_plug_s2

/-- The `movdqa` store is an extended step on the coherent machine. -/
theorem hvecWit_speichere_schritt :
    HwVecSchritt hvecWitM1 hvecWitM2
      (.vecSpeichere 0 basisCpu basisKontrolle hvecWitD2) :=
  vecSpeichere_ist_schritt hvecWitM1 0 basisCpu basisKontrolle
    hvecWitD2 hvecWitM2 hvecWit_plug_s2

/-- The TSO view after the sixteen issues. -/
def hvecWitTso : Option TSOZustand :=
  match hvecWitS1 with
  | some m => some (tsoAnsicht m)
  | none => none

/-- Core 0 observes its own byte (forwarding). -/
def hvecWitLoadEigen : Option (Option Byte) :=
  match hvecWitTso with
  | some s => some (loadByte s 0 hvecWitAdr)
  | none => none

/-- Core 1 observes the old byte (no foreign forwarding). -/
def hvecWitLoadFremd : Option (Option Byte) :=
  match hvecWitTso with
  | some s => some (loadByte s 1 hvecWitAdr)
  | none => none

/-- Forwarding: core 0 reads its own unflushed byte (`0x01`). -/
theorem hvecWit_weiterleitung :
    hvecWitLoadEigen = some (some (BitVec.ofNat 8 1)) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem hvecWit_fremd_alt :
    hvecWitLoadFremd = some (some (BitVec.ofNat 8 0)) := by
  decide

/-! ## 12. Drain stage: shared memory observably changes, torn halfway. -/

/-- The full sixteen-drain over the explicit store successor. -/
def hvecWitDrain : Option TSOZustand :=
  drainListe (tsoAnsicht hvecWitM2) 0 (vecEintraege hvecWitAdr hvecWitC)

/-- The low-eight drain: the torn halfway state. -/
def hvecWitDrainLo : Option TSOZustand :=
  drainListe (tsoAnsicht hvecWitM2) 0 (vecEintraegeLo hvecWitAdr hvecWitC)

/-- Read a drained shared-memory byte. -/
def hvecDrainMemOut (o : Option TSOZustand) (a : Adresse) :
    Option Byte :=
  match o with
  | some s => some (s.mem.bytes a)
  | none => none

/-- Read a drained load observation. -/
def hvecDrainLoad (o : Option TSOZustand) (c : Nat) (a : Adresse) :
    Option (Option Byte) :=
  match o with
  | some s => some (loadByte s c a)
  | none => none

/-- The data cell starts zeroed: the run really changes memory. -/
theorem hvecWit_anfang_null :
    hvecWitMem.bytes hvecWitAdr = BitVec.ofNat 8 0 := by
  decide

/-- The drain changes shared memory: the cell reads `0x01`. -/
theorem hvecWit_spuelung_aendert_speicher :
    hvecDrainMemOut hvecWitDrain hvecWitAdr =
      some (BitVec.ofNat 8 1) := by
  decide

/-- After the drain core 1 observes the new byte. -/
theorem hvecWit_fremd_neu :
    hvecDrainLoad hvecWitDrain 1 hvecWitAdr =
      some (some (BitVec.ofNat 8 1)) := by
  decide

/-- Torn halfway: the low byte is new after eight drains. -/
theorem hvecWit_teil_neu :
    hvecDrainMemOut hvecWitDrainLo hvecWitAdr =
      some (BitVec.ofNat 8 1) := by
  decide

/-- Torn halfway: the high byte still reads pre-drain. -/
theorem hvecWit_teil_alt :
    hvecDrainMemOut hvecWitDrainLo (addrOff hvecWitAdr 8) =
      some (BitVec.ofNat 8 0) := by
  decide

/-- OVERLAP: partially overlapping vector footprints classify unknown
    and refuse alias admission (reused, not re-proved). -/
theorem hvecWit_neg_alias :
    klassifiziere (vecFuss (natAdresse 8192))
        (vecFuss (natAdresse 8200)) = .unbekannt ∧
      aliasZulassen (klassifiziere (vecFuss (natAdresse 8192))
        (vecFuss (natAdresse 8200))) = false :=
  vecFuss_teilueberlapp_verweigert

/-- The 256-bit row always refuses: AVX2 is not implemented here. -/
theorem hvecWit_neg_avx :
    stufenZugelassenHw basisHw basisBereit basisCpu basisXcr0
        basisKontrolle .avx256 = false :=
  stufe_avx256_verweigert basisHw basisBereit basisCpu basisXcr0
    basisKontrolle

/-- The unified dispatcher refuses the selected row: no existing form
    is shadowed and no selected row is re-decided. -/
theorem hvecWit_ext_weist_paddb_zurueck :
    decodeExt (encodeIntVec (.paddbRR .xmm0 .xmm1)) = none :=
  intVec_ext_weist_paddb_zurueck

/-! ## 13. Joint witness: a reached two-core vector run. -/

/-- A drain over a present buffer prefix succeeds. -/
theorem drainListe_erfolg (l : List TSOEintrag) (s : TSOZustand)
    (c : Nat) (rest : List TSOEintrag)
    (hbuf : s.puffer c = l ++ rest) :
    ∃ s', drainListe s c l = some s' := by
  induction l generalizing s with
  | nil =>
    exact ⟨s, rfl⟩
  | cons hd tl ih =>
    have hne : s.puffer c ≠ [] := by
      rw [hbuf]
      simp
    cases hb : s.puffer c with
    | nil =>
      simp [hb] at hne
    | cons e rest' =>
      have hhead : s.puffer c = hd :: (tl ++ rest) := hbuf
      obtain ⟨s1, hs1⟩ : ∃ s1, flushKern s c = some s1 := by
        refine ⟨⟨{ s.mem with bytes := fun x =>
          if x = e.addr then e.wert else s.mem.bytes x },
          pufferSetze s.puffer c rest'⟩, ?_⟩
        unfold flushKern
        simp [hb]
      have hbuf1 : s1.puffer c = tl ++ rest :=
        flush_entfernt_kopf s s1 c hs1 hd (tl ++ rest) hhead
      obtain ⟨s', hs'⟩ := ih s1 hbuf1
      have e : drainListe s c (hd :: tl) = match flushKern s c with
        | none => (none : Option TSOZustand)
        | some s1 => drainListe s1 c tl := rfl
      rw [e, hs1]
      exact ⟨s', hs'⟩

/-- WITNESS for `vecRegSchritt_gleich`: the pinned `paddb` row steps
    through the register plug. All premises are instantiated jointly. -/
theorem vecRegSchritt_gleich_zeuge :
    ∃ (m : HwMaschine) (c : Nat) (cpu : CpuMerkmal)
      (k : KontrollBild) (d : IntVecDec) (t' : FpZustand),
      istVecRegisterOp d.op = true ∧
      stepIntVec d (projFp m c) m.hw (m.bereit c) cpu k = some t' ∧
      vecRegSchritt m c cpu k d = some (setKernVonFp m c t') := by
  exact ⟨hvecWitStart, 0, basisCpu, basisKontrolle, hvecWitD1,
    hvecWitT1, rfl, hvecWit_paddb, hvecWit_r1⟩

/-- WITNESS for `vecLaden_ist_vecRead`: the empty-buffer packed load
    observes the accepted `vecRead` value. All premises are
    instantiated jointly. -/
theorem vecLaden_ist_vecRead_zeuge :
    ∃ (s : TSOZustand) (c : Nat) (a : Adresse) (v : Vektor),
      (∀ x ∈ vecFuss a, neuestens (s.puffer c) x = none) ∧
      lesbar8 s.mem a = true ∧
      lesbar8 s.mem (vecHiAddr a) = true ∧
      vecLaden s c a = some v ∧ vecRead s.mem a = some v := by
  refine ⟨tsoAnsicht hvecWitM1, 0, hvecWitAdr, 0, fun x _ => rfl, ?_,
    ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide

/-- The sixteen entries sit apart: the witness no-wrap. -/
theorem hvecWit_ohne_umbruch : OhneUmbruch16 hvecWitAdr := by
  unfold OhneUmbruch16
  decide

/-- WITNESS for `vecDrain_schreibt`: the drained sixteen install every
    entry byte. All premises are instantiated jointly, on the reached
    store successor with a memory-changing drain. -/
theorem vecDrain_schreibt_zeuge :
    ∃ (s s' : TSOZustand) (c : Nat) (a : Adresse) (v : Vektor)
      (rest : List TSOEintrag) (e : TSOEintrag),
      s.puffer c = vecEintraege a v ++ rest ∧
      drainListe s c (vecEintraege a v) = some s' ∧
      (∀ e1 ∈ vecEintraege a v, ∀ e2 ∈ vecEintraege a v,
        e1.addr = e2.addr → e1 = e2) ∧
      e ∈ vecEintraege a v ∧ s'.mem.bytes e.addr = e.wert := by
  have hbuf : (tsoAnsicht hvecWitM2).puffer 0 =
      vecEintraege hvecWitAdr hvecWitC ++ [] := rfl
  obtain ⟨s', hs'⟩ := drainListe_erfolg _ (tsoAnsicht hvecWitM2) 0 []
    hbuf
  have hdis := vecEintraege_nodup_addr hvecWitAdr hvecWitC
    hvecWit_ohne_umbruch
  have hmem : (⟨addrOff hvecWitAdr 0,
      wortByte (vLo hvecWitC) 0⟩ : TSOEintrag) ∈
      vecEintraege hvecWitAdr hvecWitC :=
    List.Mem.head _
  have hbyte := vecDrain_schreibt _ s' 0 _ _ [] hbuf hs' hdis _ hmem
  exact ⟨tsoAnsicht hvecWitM2, s', 0, hvecWitAdr, hvecWitC, [],
    ⟨addrOff hvecWitAdr 0, wortByte (vLo hvecWitC) 0⟩,
    hbuf, hs', hdis, hmem, hbyte⟩

/-- THE JOINT WITNESS: a reached two-core run that fetches real
    bytes, separates lanes, forwards a buffered sixteen-byte store to
    its owner only, drains it into shared memory (0 becomes `0x01`,
    observed from both cores, torn halfway) -- with the
    malformed/control/fault/overlap/AVX refusals beside it.
    Non-degenerate: the drain changes ACTUAL shared memory. -/
theorem hvecWit_zeuge :
    hvecRipOut hvecWitR1 0 = some (BitVec.ofNat 64 4101) ∧
      hvecLaneOut hvecWitR1 0 .xmm0 0 = some 1 ∧
      hvecLaneOut hvecWitR1 0 .xmm0 1 = some 2 ∧
      hvecWitMem.bytes hvecWitAdr = BitVec.ofNat 8 0 ∧
      hvecWitLoadEigen = some (some (BitVec.ofNat 8 1)) ∧
      hvecWitLoadFremd = some (some (BitVec.ofNat 8 0)) ∧
      hvecDrainMemOut hvecWitDrain hvecWitAdr =
        some (BitVec.ofNat 8 1) ∧
      hvecDrainLoad hvecWitDrain 1 hvecWitAdr =
        some (some (BitVec.ofNat 8 1)) ∧
      hvecDrainMemOut hvecWitDrainLo hvecWitAdr =
        some (BitVec.ofNat 8 1) ∧
      hvecDrainMemOut hvecWitDrainLo (addrOff hvecWitAdr 8) =
        some (BitVec.ofNat 8 0) ∧
      fetchIntVec (projFp hvecWitStart 1)
        (geholt (projZustand hvecWitStart 1)) = none ∧
      HwVecSchritt hvecWitStart hvecWitM1
        (.vecReg 0 basisCpu basisKontrolle hvecWitD1) ∧
      HwVecSchritt hvecWitM1 hvecWitM2
        (.vecSpeichere 0 basisCpu basisKontrolle hvecWitD2) ∧
      klassifiziere (vecFuss (natAdresse 8192))
          (vecFuss (natAdresse 8200)) = .unbekannt ∧
      stufenZugelassenHw basisHw basisBereit basisCpu basisXcr0
          basisKontrolle .avx256 = false ∧
      decodeExt (encodeIntVec (.paddbRR .xmm0 .xmm1)) = none := by
  refine ⟨hvecWit_r1_rip, hvecWit_r1_lane0, hvecWit_r1_lane1,
    hvecWit_anfang_null, hvecWit_weiterleitung, hvecWit_fremd_alt,
    hvecWit_spuelung_aendert_speicher, hvecWit_fremd_neu,
    hvecWit_teil_neu, hvecWit_teil_alt, hvecWit_kern1_verweigert,
    hvecWit_reg_schritt, hvecWit_speichere_schritt,
    hvecWit_neg_alias.1, hvecWit_neg_avx,
    hvecWit_ext_weist_paddb_zurueck⟩

/- CUTS: what is not proved here.

   - No hardware correspondence: encodings, fault classes and lane
     effects are the accepted canonical rows of lane 686
     (`VectorIntegerHardwareForms`, whose CUTS cites Intel SDM
     325462-093US September 2026 per entry); no new silicon fact is
     claimed here, and nothing here re-checks the manual. Legacy YMM
     upper bits (`MAXVL-1:128` unmodified) stay unmodelled, as in 686:
     no YMM state exists in `FpZustand`. Timing, power, privilege,
     paging, segments, interrupts, SMM, debug, perfmon and
     virtualization state are absent; execute/read/write permissions
     are per-byte data facts over the canonical `Speicher`.
   - No whole-vector atomicity: every 16-byte memory row is sixteen
     per-byte TSO events (oldest-first issues, oldest-first drains).
     Torn intermediates stand (`vecDrain_teilt`, reused
     `vecWrite_teilt` shape at sixteen bytes); footprint disjointness
     never implies atomicity or reordering. Per-access TSO
     granularity beyond bytes, the GX refinement and any source
     correspondence stay open.
   - No source/IR/ABI/loader/entry/budget link: no per-access
     target-to-W/GX simulation, no budget transfer, no progress or
     call-log effect is proved; `simdFreigabe` is untouched. The
     full bridge to W/GX is not claimed.
   - The extended relation takes decoded values: the no-forgery
     discipline is the fetch bridge (`hvec_fetch_bruecke`,
     `intVec_fetch_bridge`) and the adapter face, not a second
     fetch inside every constructor. LOCK/RMW has no step here
     (refused, as in the coherent machine); faults beyond the
     carried divide halt are absent.
   - The legacy admission is strictly weaker than the accepted
     stronger XCR0 gate (`vektorLegacy_verfeinert`, reused): the old
     gate stays valid as a safe over-approximation, never as a
     hardware fault. The 256-bit AVX row always refuses
     (`stufe_avx256_verweigert`, reused). OS configuration and
     context-preservation code remain user logic: checked inputs,
     never assumed-correct behaviour.
   - Addresses reuse the accepted `effAddr` (no second address
     model); the `0F 73` group still requires a zero REX.R bit
     (canonical subset, as in 686); logical rows step at `.b64`
     only (bitwise, hence width-free, as in 686).
-/

#print axioms vecEintraege_laenge
#print axioms vecSpeichern_haengt_an
#print axioms vecSpeichern_kein_speicher
#print axioms vecSpeichern_erfolg
#print axioms ladeAcht_ist_read64
#print axioms vecLaden_ist_vecRead
#print axioms drainListe_rahmen
#print axioms drainListe_schreibt_allg
#print axioms vecDrain_teilt
#print axioms vecDrain_schreibt
#print axioms vecRegSchritt_gleich
#print axioms vecRegSchritt_speicher
#print axioms hwVecSchritt_wf
#print axioms hwVecSchritt_einbettet
#print axioms hwVecSchritt_projiziert
#print axioms adapterVec_reg
#print axioms adapterVec_fremder_kern_reg
#print axioms vecLade_ist_schritt
#print axioms vecSpeichere_ist_schritt
#print axioms vecReg_ist_schritt
#print axioms vecReg_profil_verweigert
#print axioms vecReg_ohne_cpu
#print axioms vecSpeicherSchritt_gp_a
#print axioms vecSpeicherSchritt_schreibrecht
#print axioms vecLadeSchritt_leserecht
#print axioms vecRegSchritt_pxor_agree
#print axioms vecRegSchritt_paddq_agree
#print axioms hvec_fetch_bruecke
#print axioms hvecWit_zeuge
#print axioms vecRegSchritt_gleich_zeuge
#print axioms vecLaden_ist_vecRead_zeuge
#print axioms vecDrain_schreibt_zeuge

end Gabbro.Grammatik.X86
