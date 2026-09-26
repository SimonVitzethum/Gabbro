/-
  File:      Grammatik/ZeichenfolgeC.lean
  Subject:   Bounded strings in C: the emitted layout and its correspondence.

  Lane 261 lowers `string max N` to `gabbro_string_N` -- one length word
  plus N bytes, no NUL terminator (`OFFEN.md` O24, `emit.rs`
  `ketten_abschnitt`). This file is the layout's value model beside
  `ZeichenfolgeGebunden.lean`'s `BString`: a `CString max` carries the full
  N-byte buffer with the length word beside it, and every emitted operation
  is stated over the live prefix (`nimm`) with its length, refusal and
  comparison behaviour.
-/

import Grammatik.ZeichenfolgeGebunden

namespace Gabbro.Grammatik

/-- The emitted C object for `string max N`: the length word plus the full
    N-byte buffer. Bytes are `Nat` below 256; `len` is the live prefix, and
    the tail past it is unspecified (zero-filled by initializers, stale
    after writes) -- no operation below reads it. -/
structure CString (max : Nat) where
  len : Nat
  bytes : List Nat
  bytes_lang : bytes.length = max
  len_ok : len ≤ max
  bytes_wert : ∀ b ∈ bytes, b < 256

/-- The live prefix: what the length word governs. Every read below goes
    through it, never through the tail. -/
def nimm {max : Nat} (s : CString max) : List Nat :=
  s.bytes.take s.len

/-- `lenof`: the length word the emitter reads (`s.len`). -/
def clen {max : Nat} (s : CString max) : Nat :=
  s.len

/-- The length word fits the buffer: the bridge every read below walks. -/
theorem len_in_bytes {max : Nat} (s : CString max) :
    s.len ≤ s.bytes.length := by
  rw [s.bytes_lang]
  exact s.len_ok

/-- The length word is the live prefix's length: what the checker guards
    (`lenof(s) > k`) is what the layout carries. -/
theorem clen_nimm {max : Nat} (s : CString max) :
    clen s = (nimm s).length := by
  simp [clen, nimm, List.length_take]
  exact (Nat.min_eq_left (len_in_bytes s)).symm

/-- `s[k]`: the emitted byte read (`s.data[k]`). In range exactly where the
    checker's guard holds (`i < len`), refused past it -- the `N454` rule
    over the layout. -/
def cindex {max : Nat} (s : CString max) (i : Nat) : Option Nat :=
  if h : i < s.len then
    some (s.bytes[i]'(Nat.lt_of_lt_of_le h (len_in_bytes s)))
  else none

/-- An in-range read returns the buffer byte. -/
theorem cindex_innen {max : Nat} (s : CString max) (i : Nat)
    (h : i < s.len) :
    cindex s i = some (s.bytes[i]'(Nat.lt_of_lt_of_le h (len_in_bytes s))) := by
  simp [cindex, h]

/-- A read at or past the length is refused. -/
theorem cindex_aussen {max : Nat} (s : CString max) (i : Nat)
    (h : s.len ≤ i) : cindex s i = none := by
  simp [cindex, Nat.not_lt.mpr h]

/-- Copy into a slot of max `tmax`: the widening helper
    (`gabbro_widen_N_M`) keeps the length word and the live bytes. `none`
    is the refusal the checker already rules out (`N455`). -/
def ckopie (tmax : Nat) {m : Nat} (s : CString m) : Option (CString tmax) :=
  if h : s.len ≤ tmax then
    some ⟨s.len, s.bytes.take s.len ++ List.replicate (tmax - s.len) 0,
      by
        simp [List.length_append, List.length_replicate, List.length_take,
          Nat.min_eq_left (len_in_bytes s)]
        exact Nat.add_sub_cancel' h,
      h,
      by
        intro b hb
        simp [List.mem_append, List.mem_replicate] at hb
        rcases hb with hb | ⟨_, hb⟩
        · have := s.bytes_wert b (List.mem_of_mem_take hb)
          omega
        · omega⟩
  else none

/-- A widening copy keeps the live prefix: what the slot reads is what the
    source held (the `N455` copy rule, exact lengths). -/
theorem ckopie_nimm (tmax : Nat) {m : Nat} (s : CString m)
    (h : s.len ≤ tmax) :
    ∃ r : CString tmax, ckopie tmax s = some r ∧ nimm r = nimm s := by
  unfold ckopie
  rw [dif_pos h]
  refine ⟨_, rfl, ?_⟩
  have h0 : s.len - min s.len s.bytes.length = 0 := by
    rw [Nat.min_eq_left (len_in_bytes s)]
    exact Nat.sub_self _
  simp only [nimm, List.take_append, List.take_take, List.length_take,
    Nat.min_self, h0, List.take_zero, List.append_nil]

/-- Concat at the target max: the helper (`gabbro_concat_T`) writes both
    live prefixes back to back. `none` is the over-max refusal the checker
    already rules out (`N453`). The tail is arbitrary fill again. -/
def cconcat (tmax : Nat) {m1 m2 : Nat} (a : CString m1) (b : CString m2) :
    Option (CString tmax) :=
  if h : a.len + b.len ≤ tmax then
    some ⟨a.len + b.len,
      (a.bytes.take a.len ++ b.bytes.take b.len) ++ List.replicate (tmax - (a.len + b.len)) 0,
      by
        simp [List.length_append, List.length_replicate, List.length_take,
          Nat.min_eq_left (len_in_bytes a), Nat.min_eq_left (len_in_bytes b)]
        rw [← Nat.add_assoc]
        exact Nat.add_sub_cancel' h,
      h,
      by
        intro x hx
        rw [List.mem_append] at hx
        rcases hx with hx | hx
        · rw [List.mem_append] at hx
          rcases hx with hx | hx
          · have := a.bytes_wert x (List.mem_of_mem_take hx)
            omega
          · have := b.bytes_wert x (List.mem_of_mem_take hx)
            omega
        · rw [List.mem_replicate] at hx
          obtain ⟨_, rfl⟩ := hx
          omega⟩
  else none

/-- A within-max concat appends the live prefixes: the summed length the
    checker held (`N453`, `bconcat_max_summe`) is what the layout writes. -/
theorem cconcat_nimm (tmax : Nat) {m1 m2 : Nat} (a : CString m1) (b : CString m2)
    (h : a.len + b.len ≤ tmax) :
    ∃ r : CString tmax, cconcat tmax a b = some r ∧
      nimm r = nimm a ++ nimm b := by
  unfold cconcat
  rw [dif_pos h]
  have hX : (a.bytes.take a.len ++ b.bytes.take b.len).length = a.len + b.len := by
    simp [List.length_append, List.length_take,
      Nat.min_eq_left (len_in_bytes a), Nat.min_eq_left (len_in_bytes b)]
  refine ⟨_, rfl, ?_⟩
  simp only [nimm]
  show List.take (a.len + b.len) ((a.bytes.take a.len ++ b.bytes.take b.len) ++
    List.replicate (tmax - (a.len + b.len)) 0) =
    a.bytes.take a.len ++ b.bytes.take b.len
  rw [← hX, List.take_append, List.take_length, Nat.sub_self,
    List.take_zero, List.append_nil]

/-- Comparison of the live prefixes: the `gabbro_streq` / `gabbro_strlt`
    helpers over `(len, data)` pairs. Byte-wise like `memcmp`, and UTF-8
    preserves code point order byte-wise, so this agrees with the Lean
    `vergl` over characters on every encoded string. -/
def cvergleiche : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys =>
    match compare x y with
    | .eq => cvergleiche xs ys
    | .lt => .lt
    | .gt => .gt

/-- Equal exactly on equal prefixes: what `==` decides. -/
theorem cvergleiche_eq (l : List Nat) : cvergleiche l l = .eq := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [cvergleiche]
    have hcmp : compare x x = .eq := by simp
    rw [hcmp]
    exact ih

/-- Witness buffer `"hi"` at max 8. -/
def w1 : CString 8 := ⟨2, [104, 105, 0, 0, 0, 0, 0, 0], rfl, by decide, by decide⟩

/-- Witness buffer `"!"` at max 3. -/
def w2 : CString 3 := ⟨1, [33, 0, 0], rfl, by decide, by decide⟩

/-- Witness buffer `"hi!"` at max 8: the concat of the two above. -/
def w3 : CString 8 := ⟨3, [104, 105, 33, 0, 0, 0, 0, 0], rfl, by decide, by decide⟩

/-- `cstring_zeuge`: every emitted operation on non-empty, distinct
    buffers. `"hi" + "!"` at max 8 is `"hi!"` (length 3); index 2 reads
    `33` (`'!'`); the prefix compares less; equality holds with itself. -/
theorem cstring_zeuge :
    ∃ s3 : CString 8,
      cconcat 8 w1 w2 = some s3 ∧ clen s3 = 3 ∧
      cindex s3 2 = some 33 ∧
      cvergleiche (nimm s3) (nimm s3) = .eq ∧
      cvergleiche (nimm w1) (nimm s3) = .lt :=
  ⟨w3, rfl, rfl, rfl, cvergleiche_eq _, rfl⟩

/-! ## CUTS:
  - VALUE MODEL ONLY: `CString max` as a length word plus the full N-byte
    buffer, with every emitted operation stated over the live prefix
    (`nimm`): `clen` is the prefix length (`clen_nimm`); `cindex` is
    in-range exactly under the checker's guard (`cindex_innen`,
    `cindex_aussen`); `ckopie` keeps the prefix (`ckopie_nimm`);
    `cconcat` appends the prefixes (`cconcat_nimm`); `cvergleiche`
    decides equality on equal prefixes (`cvergleiche_eq`). The witness
    `cstring_zeuge` runs every operation on non-empty, distinct buffers.
  - NO Char bridge: the layout carries BYTES (`Nat` below 256) while
    `BString` carries characters. The checker counts literal bytes and the
    emitter compares UTF-8 bytes, and UTF-8 preserves code point order
    byte-wise -- but no theorem here encodes UTF-8, so `bindex` (over
    `Char`) and `cindex` (over bytes) are the same SHAPE, not one proved
    equal to the other.
  - NO framework hook: nothing here is a `CForm` and nothing plugs into
    `korrOk` / `CSemantik` -- the correspondence is stated per operation
    over the value model, the way `bconcat_max_summe` / `bkopie_max`
    stand beside (not inside) the checker.
  - The tail past `len` is arbitrary fill (zeros here): no theorem reads
    it, and the C leaves whatever the stack held. A claim about the tail
    would be a claim about uninitialized memory.
-/

#print axioms Gabbro.Grammatik.nimm
#print axioms Gabbro.Grammatik.len_in_bytes
#print axioms Gabbro.Grammatik.clen_nimm
#print axioms Gabbro.Grammatik.cindex_innen
#print axioms Gabbro.Grammatik.cindex_aussen
#print axioms Gabbro.Grammatik.ckopie_nimm
#print axioms Gabbro.Grammatik.cconcat_nimm
#print axioms Gabbro.Grammatik.cvergleiche_eq
#print axioms Gabbro.Grammatik.cstring_zeuge
