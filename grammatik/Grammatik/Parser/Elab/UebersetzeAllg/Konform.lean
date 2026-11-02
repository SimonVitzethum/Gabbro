module

public import Grammatik.Kern.Syntax.Zucker
public import Grammatik.Parser.Elab.Uebersetze

@[expose] public section



namespace Gabbro.Grammatik.Parser.UebersetzeAllg

open Gabbro.Grammatik.Parser.Uebersetze

/-! ## Declaration lookups and signature conformance (`Konform`, C06)

  The `UProg` lookups the signatures need, the elaborated signatures
  (`mkSig`/`dummySig`/`sigFns`/`sigAt`), structural conformance
  (`sigPasstB`) and contract conformance (`vertragPasstAt` over
  normalised conjunct lists), combined in `passtAt`: the proof that
  travels with a function-pointer value. Split from `Teil1` (2026-11-02,
  pure move): `Teil1` keeps the carrier/field/foreign/register lookups,
  the invariant bridge and `declOf`. -/

/-- The table at an index. -/
def tabAt (u : UProg) (t : Fin u.tabs.length) : UTab :=
  u.tabs.get t

/-- The lock at an index. -/
def lockAt (u : UProg) (l : Fin u.locks.length) : ULock :=
  u.locks.get l

/-- The function at an index. -/
def fnAt (u : UProg) (f : Fin u.fns.length) : UFn :=
  u.fns.get f

def globAt (u : UProg) (g : Fin u.globs.length) : UGlob := u.globs.get g

/-- A lock index by name. -/
def lockIdx : (locks : List ULock) → (n : String) → Except String (Fin locks.length)
  | [], n => .error ("lock unknown: " ++ n)
  | l :: rest, n =>
    if l.name == n then .ok 0
    else match lockIdx rest n with
      | .error e => .error e
      | .ok j => .ok j.succ

/-- The held locks of a function, as indices (names the declaration
    does not know are dropped; `elabU` output never has them). -/
def heldAt (u : UProg) (f : UFn) : List (Fin u.locks.length) :=
  f.held.filterMap fun n => (lockIdx u.locks n).toOption

/-- The write flag of a function at a static. -/
def writesGAt (u : UProg) (f : UFn) (g : Fin u.globs.length) : Bool :=
  f.gputs.any (· == (globAt u g).name)

/-- The write flag of a function at a table. -/
def writesAt (u : UProg) (f : UFn) (t : Fin u.tabs.length) : Bool :=
  f.puts.any (· == (tabAt u t).name)

/-- The signature of an elaborated function. -/
def mkSig (u : UProg) (f : UFn) :
    Signatur (Fin u.tabs.length) (Fin u.globs.length) (Fin u.locks.length) Empty where
  params := f.params.map (·.2)
  erg := f.ergTy
  gruende := f.gruende
  haelt := heldAt u f
  schreibt := writesAt u f
  gschreibt := writesGAt u f
  konsumiert := []
  produziert := []
  boden := f.boden

/-- The dummy signature: no parameters, no rights. -/
def dummySig (u : UProg) :
    Signatur (Fin u.tabs.length) (Fin u.globs.length) (Fin u.locks.length) Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun _ => false
  konsumiert := []
  produziert := []

/-- The signatures of the unit: the functions', then the pointer types' (`UProg.ptrs`). -/
def sigFns (u : UProg) : List UFn := u.fns ++ u.ptrs

/-- The `n`th signature, or the dummy (an out-of-range number names
    no function and no pointer type). -/
def sigAt (u : UProg) (n : Nat) :
    Signatur (Fin u.tabs.length) (Fin u.globs.length) (Fin u.locks.length) Empty :=
  if h : n < (sigFns u).length then mkSig u ((sigFns u).get ⟨n, h⟩) else dummySig u

/-- **Conformance, decided** (`SigPasst` over the finite carriers of an elaborated unit): the first
    signature fits the second. -/
def sigPasstB {a b c : Nat} (rang : Fin c → Int) (S T : Signatur (Fin a) (Fin b) (Fin c) Empty) : Bool :=
  decide (S.params = T.params) && decide (S.erg = T.erg) && decide (S.gruende = T.gruende) &&
  (List.finRange a).all (fun t => !S.schreibt t || T.schreibt t) &&
  (List.finRange b).all (fun g => !S.gschreibt g || T.gschreibt g) &&
  decide (S.konsumiert = T.konsumiert) && decide (S.produziert = T.produziert) &&
  S.haelt.all (fun L => decide (L ∈ T.haelt)) &&
  T.haelt.all (fun L => decide (L ∈ S.haelt) ||
    (match S.boden with | some c => decide (rang L < c) | none => false)) &&
  (match T.boden with
    | none => true
    | some c => match S.boden with | some c' => decide (c ≤ c') | none => false)

theorem sigPasstB_ok {a b c : Nat} {rang : Fin c → Int} {S T : Signatur (Fin a) (Fin b) (Fin c) Empty}
    (h : sigPasstB rang S T = true) : SigPasst rang S T := by
  unfold sigPasstB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hp, he⟩, hg⟩, hw⟩, hgw⟩, hk⟩, hpr⟩, hh⟩, hx⟩, hb⟩ := h
  refine ⟨hp, he, hg, fun t ht => ?_, fun g' hg' => ?_, hk, hpr, fun L hL => hh L hL, fun L hL hn => ?_,
    fun c hc => ?_, (OwnerFlow.empty_of_empty S.owner).trans (OwnerFlow.empty_of_empty T.owner).symm⟩
  · rcases hw t (List.mem_finRange t) with h1 | h1
    · rw [ht] at h1; cases h1
    · exact h1
  · rcases hgw g' (List.mem_finRange g') with h1 | h1
    · rw [hg'] at h1; cases h1
    · exact h1
  · rcases hx L hL with h1 | h1
    · exact absurd h1 hn
    · revert h1
      cases hS : S.boden with
      | none => intro h1; cases h1
      | some c => intro h1; exact ⟨c, rfl, of_decide_eq_true h1⟩
  · rw [hc] at hb
    revert hb
    cases hS : S.boden with
    | none => intro h1; cases h1
    | some c' => intro h1; exact ⟨c', rfl, of_decide_eq_true h1⟩

/-- Conjunct normal form of one contract side: nested `.and` flattened
    (mirrors `lowEnsList`, which conjoins the list right-nested). -/
def uKonjunkte : UEns → List UEns
  | .and a b => uKonjunkte a ++ uKonjunkte b
  | e => [e]

/-- Syntactic occurrence in a normalised list, decided. -/
def ensEnthalten (sup : List UEns) (c : UEns) : Bool :=
  decide (c ∈ sup)

theorem ensEnthalten_ok {sup : List UEns} {c : UEns} (h : ensEnthalten sup c = true) : c ∈ sup :=
  of_decide_eq_true h

/-- The source inclusion the conformance Bool decides. -/
def UEnsEinschluss (sup sub : List UEns) : Prop :=
  ∀ c ∈ sub, c ∈ sup

/-- The head (function or pointer type) behind signature number `n`:
    functions first, then the pointer types (`sigFns`); out of range
    carries no contract, like `dummySig`. -/
def sigFnAt (u : UProg) (n : Nat) : UFn :=
  if h : n < (sigFns u).length then (sigFns u).get ⟨n, h⟩
  else { name := "", params := [], kinds := [], res := none, held := [], puts := [],
    gives := [], body := [], ret := .empty }

/-- **Contract conformance, decided** (C06, O43): every target-pre conjunct
    occurs among the interface pre (contravariant: the interface pre implies
    the target's), and every interface-post conjunct occurs among the target
    post (covariant). Effects stay structural (`sigPasstB`); `costs` travels
    nowhere, as at a function. A non-`.and` side is compared whole; sides that
    name parameters differently refuse (positional normalisation is the next
    step with the lowering bridge). -/
def vertragPasstAt (u : UProg) (f : Fin u.fns.length) (n : Nat) : Bool :=
  (((fnAt u f).needs.flatMap uKonjunkte).all (ensEnthalten ((sigFnAt u n).needs.flatMap uKonjunkte))) &&
  (((sigFnAt u n).gives.flatMap uKonjunkte).all (ensEnthalten ((fnAt u f).gives.flatMap uKonjunkte)))

theorem vertragPasstAt_ok (u : UProg) (f : Fin u.fns.length) (n : Nat)
    (h : vertragPasstAt u f n = true) :
    UEnsEinschluss ((sigFnAt u n).needs.flatMap uKonjunkte)
      ((fnAt u f).needs.flatMap uKonjunkte) ∧
    UEnsEinschluss ((fnAt u f).gives.flatMap uKonjunkte)
      ((sigFnAt u n).gives.flatMap uKonjunkte) := by
  unfold vertragPasstAt at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hpre, hpost⟩ := h
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · have hm := (List.all_eq_true.mp hpre) c hc
    exact ensEnthalten_ok hm
  · have hm := (List.all_eq_true.mp hpost) c hc
    exact ensEnthalten_ok hm

/-- `f` conforms to the signature number `n` of the unit: a live number, the
    signatures fit, and the contracts include (the proof travels with the
    value: `D.passt f n = true` gains the contract part). -/
def passtAt (u : UProg) (f : Fin u.fns.length) (n : Nat) : Bool :=
  decide (n < (sigFns u).length) && sigPasstB (fun l => (lockAt u l).rank) (sigAt u f.val) (sigAt u n) &&
  vertragPasstAt u f n

theorem passtAt_ok (u : UProg) (f : Fin u.fns.length) (n : Nat) (h : passtAt u f n = true) :
    SigPasst (fun l => (lockAt u l).rank) (sigAt u f.val) (sigAt u n) ∧
    UEnsEinschluss ((sigFnAt u n).needs.flatMap uKonjunkte) ((fnAt u f).needs.flatMap uKonjunkte) ∧
    UEnsEinschluss ((fnAt u f).gives.flatMap uKonjunkte) ((sigFnAt u n).gives.flatMap uKonjunkte) := by
  unfold passtAt at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hlt, hsig⟩, hvertrag⟩ := h
  exact ⟨sigPasstB_ok hsig, (vertragPasstAt_ok u f n hvertrag).1, (vertragPasstAt_ok u f n hvertrag).2⟩

theorem passtAt_lt (u : UProg) (f : Fin u.fns.length) (n : Nat) (h : passtAt u f n = true) :
    n < (sigFns u).length :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1
