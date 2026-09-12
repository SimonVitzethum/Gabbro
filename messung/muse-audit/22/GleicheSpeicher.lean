import Grammatik.Maschine

open Gabbro.Grammatik

/-! ## Indistinguishable successors (pattern a/e): the eigen iff is symmetric noise

`SpecTriple.requiresEigen` / `ensuresEigen` conclude an IFF
`Pre (J.code f) vor ↔ Pre (J.code f) nach` (resp. `Post`). The leaf-case proof
in `spec_aus_fuehrung_schritt` closes this iff by chaining
`hMem.memPre` (memory agreement) with `hBlatt` (firing preservation).

Checked observation: where the two worlds provably share memory, the iff is
already forced by `hMem` ALONE -- no firing content is needed. Lock steps
(`nimmt`/`gibt`) are exactly this case: both successor worlds are
`M.speicher.welt ...` over the same `M.speicher`, so `hMem.memPre` bridges
them directly. The leaf case additionally needs `hBlatt`, but the two lock
branches of the SAME theorem need nothing but `hMem`: their `hNew` proofs
never inspect the lock, the trace, or any firing fact beyond the world shape
`M'.welten = M.welten ++ [w]`.

Demonstration: from `hMem` alone, any two same-memory worlds satisfy the
eigen-shaped iff -- the lock-step content of `spec_aus_fuehrung_schritt`
(two of three branches) is memory constancy restated per index.
-/

-- Demonstration: hMem alone proves the eigen-shaped iff for same-memory worlds.
example (Pre Post : D.Fn → World D → Prop) (fn : D.Fn)
    (hMem : SpeicherVertrag Pre Post fn)
    (vor nach : World D)
    (hsame : vor.speicher = nach.speicher) :
    (Pre fn vor ↔ Pre fn nach) ∧ (Post fn vor ↔ Post fn nach) :=
  ⟨hMem.memPre vor nach hsame, hMem.memPost vor nach hsame⟩

-- Demonstration: the same holds with worlds named as the lock-step proof
-- names them -- `vor` from the frontier fact, `nach` a `welt`-built world --
-- where both carry `M.speicher` by `speicher_welt_speicher`.
example (Pre Post : D.Fn → World D → Prop) (fn : D.Fn)
    (hMem : SpeicherVertrag Pre Post fn)
    (M : GenMaschine D) (vor : World D)
    (hvs : vor.speicher = M.speicher)
    (tr : List (Ereignis D)) :
    (Pre fn vor ↔ Pre fn (M.speicher.welt tr)) ∧
      (Post fn vor ↔ Post fn (M.speicher.welt tr)) := by
  have hNs : (M.speicher.welt tr).speicher = M.speicher :=
    speicher_welt_speicher _ _
  exact ⟨hMem.memPre vor _ (hvs.trans hNs.symm),
    hMem.memPost vor _ (hvs.trans hNs.symm)⟩

#print axioms spec_aus_fuehrung_schritt
#print axioms speicher_welt_speicher

/-!
CUTS:
- This does NOT show the leaf branch is vacuous: `hBlatt` is genuinely needed
  there (a writing leaf can break an arbitrary memory predicate, as §22 books).
  The finding covers the two lock branches only (pattern a): they restate
  memory constancy per index.
- `SpeicherVertrag` itself (memory-only contracts) is a strong hypothesis doing
  the real work; its discharge (`hMem` for QRequires/QEnsures) is booked
  downstream and not checked here.
-/
