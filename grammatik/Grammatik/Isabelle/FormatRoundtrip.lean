/-
  File:      Grammatik/Isabelle/FormatRoundtrip.lean
  Port of:   beweise/Format_Roundtrip.thy (template `format.roundtrip`, S11)

  The fixed case: a field at an offset with the width from the declaration.
  (1) The roundtrip `lesen(schreiben(x)) == x` for every representable `x` --
  resting on the LENGTH, as a premise, not on goodwill. The separation of the
  fields -- without it the roundtrip would be worthless. (2) The single entry
  check -- and WHY it holds only for fixed lengths.

  The generator deliberately does NOT lower a `format` to a C struct
  (`emit.rs`): a format is a promise about BYTES. This proof is therefore
  about a byte sequence and a read function, not about a struct.

  Adaptations (same content, Lean core without mathlib):
  - The buffer is `Nat → Nat` with a length (Isabelle: `puffer`, same); byte
    lookup outside the written list is the report default `0` (Isabelle:
    `bs ! k`, arbitrary outside -- the roundtrip premise keeps every access
    inside, so the default is never observed).
  - `liest` folds over an explicit recursive reader (`holtAux`) instead of
    `map p [off ..< off+w]`; `set [...]` becomes an interval predicate. Same
    equations.
-/

namespace Gabbro.Grammatik.Isabelle.FormatRoundtrip

/-- A byte. (Isabelle: `type_synonym byte = nat`.) -/
abbrev Byte := Nat

/-- The buffer: a byte sequence with a length, as the generated C reader sees
    it (pointer plus length). (Isabelle: `type_synonym puffer`.) -/
abbrev Puffer := Nat → Byte

/-- A field: offset and width from the declaration. (Isabelle: `record feld`.) -/
structure Feld where
  versatz : Nat
  breite : Nat

/-- Read `n` bytes at offset `o`. (Isabelle: `map p [versatz ..< versatz+n]`.) -/
def holtAux : Puffer → Nat → Nat → List Byte
  | _, _, 0 => []
  | p, o, n + 1 => p o :: holtAux p (o + 1) n

/-- Read a field. (Isabelle: `liest`.) -/
def liest (p : Puffer) (f : Feld) : List Byte :=
  holtAux p f.versatz f.breite

/-- Index into a byte list with a fixed default (never observed under the
    roundtrip premise). -/
def nimm : List Byte → Nat → Byte
  | [], _ => 0
  | b :: _, 0 => b
  | _ :: bs, n + 1 => nimm bs n

/-- `nimm` past the head is `nimm` of the tail. -/
theorem nimm_succ (b : Byte) (bs : List Byte) (k : Nat) :
    nimm (b :: bs) (k + 1) = nimm bs k := by
  simp only [nimm]

/-- Write a field. (Isabelle: `schreibt`.) -/
def schreibt (p : Puffer) (f : Feld) (bs : List Byte) : Puffer :=
  fun i => if f.versatz ≤ i ∧ i < f.versatz + f.breite
           then nimm bs (i - f.versatz) else p i

/-- The same write, indexed by the list length (the internal form). -/
def schreibtAt (p : Puffer) (o : Nat) (bs : List Byte) : Puffer :=
  fun i => if o ≤ i ∧ i < o + bs.length then nimm bs (i - o) else p i

/-- Two readers agreeing on the whole interval read the same list. -/
theorem holtAux_eq (s₁ s₂ : Puffer) (o n : Nat)
    (h : ∀ i, o ≤ i → i < o + n → s₁ i = s₂ i) :
    holtAux s₁ o n = holtAux s₂ o n := by
  induction n generalizing o with
  | zero => rfl
  | succ n ih =>
    simp only [holtAux]
    have h0 : s₁ o = s₂ o := h o (Nat.le_refl o) (by omega)
    have hr := ih (o + 1) (fun i ho hm => h i (by omega) (by omega))
    rw [h0, hr]

/-- The roundtrip core: reading back what was written, by induction on the
    value list. -/
theorem roundtrip_aux (p : Puffer) (o : Nat) (bs : List Byte) :
    holtAux (schreibtAt p o bs) o bs.length = bs := by
  induction bs generalizing o with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons]
    have h0 : schreibtAt p o (b :: bs) o = b := by
      simp only [schreibtAt]
      have hc : o ≤ o ∧ o < o + (b :: bs).length := by
        simp only [List.length_cons]; omega
      rw [if_pos hc]
      simp only [nimm, Nat.sub_self]
    have heq : ∀ i, o + 1 ≤ i → i < o + 1 + bs.length →
        schreibtAt p o (b :: bs) i = schreibtAt p (o + 1) bs i := by
      intro i ho hm
      simp only [schreibtAt]
      have h1 : o ≤ i ∧ i < o + (b :: bs).length := by
        simp only [List.length_cons]; omega
      have h2 : o + 1 ≤ i ∧ i < o + 1 + bs.length := by omega
      rw [if_pos h1, if_pos h2]
      have hsub : i - o = (i - (o + 1)) + 1 := by omega
      rw [hsub, nimm_succ]
    have hr : holtAux (schreibtAt p o (b :: bs)) (o + 1) bs.length = bs := by
      rw [holtAux_eq _ _ _ _ heq]
      exact ih (o + 1)
    simp only [holtAux]
    rw [h0, hr]

/-- (1) THE ROUNDTRIP: `lesen(schreiben(x)) == x` for every representable `x`.
    The premise `bs.length = f.breite` is the load-bearing half: it keeps
    every access inside the value. (Isabelle: `roundtrip`.) -/
theorem roundtrip (p : Puffer) (f : Feld) (bs : List Byte)
    (h : bs.length = f.breite) :
    liest (schreibt p f bs) f = bs := by
  have hb : f.breite = bs.length := h.symm
  have hfun : schreibt p f bs = schreibtAt p f.versatz bs := by
    funext i
    simp only [schreibt, schreibtAt, hb]
  simp only [liest, hfun, hb]
  exact roundtrip_aux p f.versatz bs

/-! ## The separation of the fields -/

/-- Two fields are separate. (Isabelle: `trennt`.) -/
def trennt (f g : Feld) : Prop :=
  f.versatz + f.breite ≤ g.versatz ∨ g.versatz + g.breite ≤ f.versatz

/-- Writing one field does not disturb a separate one -- the damage a
    generator causes by letting two offsets overlap.
    (Isabelle: `schreiben_stoert_getrennte_felder_nicht`.) -/
theorem schreiben_stoert_getrennte_felder_nicht (p : Puffer) (f g : Feld)
    (bs : List Byte) (h : trennt f g) :
    liest (schreibt p f bs) g = liest p g := by
  simp only [liest]
  apply holtAux_eq _ _ _ _ (fun i ho hm => ?_)
  simp only [schreibt]
  have hn : ¬ (f.versatz ≤ i ∧ i < f.versatz + f.breite) := by
    intro hc
    rcases h with h | h <;> omega
  rw [if_neg hn]

/-! ## (2) The single entry check -/

/-- The entry check: every field end fits in the buffer.
    (Isabelle: `passt`.) -/
def passt (fs : List Feld) (n : Nat) : Prop :=
  ∀ f ∈ fs, f.versatz + f.breite ≤ n

/-- The entry check covers every access: check the buffer length ONCE at
    entry, and every field access is inside. This holds only for FIXED
    lengths -- with content-dependent offsets `fs` is no constant and `passt`
    cannot be evaluated at entry.
    (Isabelle: `eintrittspruefung_deckt_jeden_zugriff`.) -/
theorem eintrittspruefung_deckt_jeden_zugriff (fs : List Feld) (n : Nat)
    (f : Feld) (i : Nat)
    (hpass : passt fs n) (hmem : f ∈ fs)
    (hacc : f.versatz ≤ i ∧ i < f.versatz + f.breite) :
    i < n := by
  have hend := hpass f hmem
  omega

/-! ## Witness: roundtrip on a concrete buffer -/

/-- Witness: writing `[7, 8]` at offset `4` and reading it back, on the zero
    buffer -- plus the entry check covering offset `5`. No lemma above
    quantifies over syntax, so the inhabitation obligation is vacuous; this is
    a data-level witness for the roundtrip. -/
theorem roundtrip_zeuge :
    liest (schreibt (fun _ => 0) ⟨4, 2⟩ [7, 8]) ⟨4, 2⟩ = [7, 8] ∧
    (∀ n, passt [⟨4, 2⟩] n → 4 + 2 ≤ n → 5 < n) := by
  constructor
  · exact roundtrip _ _ _ rfl
  · intro n hpass _
    exact eintrittspruefung_deckt_jeden_zugriff [⟨4, 2⟩] n ⟨4, 2⟩ 5
      hpass (by simp) ⟨by decide, by decide⟩

/-! ## Bridge

  The Lean semantics already ties `format` fields to the model: a `format` is
  a `Tab` with `count 1` whose `where` clause is a `Block.pruefung`
  (`Syntax.lean` §9), read and written through `Expr.leseBytes` /
  `Stmt.schreibBytes` with the offset bound as a constructor argument
  (`hhi : hi + n ≤ D.count t`). That argument IS the entry check
  (`eintrittspruefung_deckt_jeden_zugriff`) at the type level: no
  `leseBytes` term exists whose range escapes the carrier. The value-level
  roundtrip (`roundtrip`: write-then-read is the identity) has no counterpart
  over `eval` yet -- it would need a `schreibBytes`-then-`leseBytes` frame
  lemma over `World.slots`, which no file states. Named, not faked. -/

#print axioms Gabbro.Grammatik.Isabelle.FormatRoundtrip.roundtrip
#print axioms Gabbro.Grammatik.Isabelle.FormatRoundtrip.schreiben_stoert_getrennte_felder_nicht
#print axioms Gabbro.Grammatik.Isabelle.FormatRoundtrip.eintrittspruefung_deckt_jeden_zugriff
#print axioms Gabbro.Grammatik.Isabelle.FormatRoundtrip.roundtrip_zeuge

end Gabbro.Grammatik.Isabelle.FormatRoundtrip
