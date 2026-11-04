module

public import Grammatik.Parser.Elab.Generic.SignatureData
public import Grammatik.Parser.Elab.Generic.C09Flows

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg

open Gabbro.Grammatik.Parser.Uebersetze

/-- The signature of an elaborated function (C16): the consumed/produced ordinary
    marks are the `nimmt`/`gibt` names resolved against the unit's mark table
    (`nimmtAt`/`gibtAt`); the call-scoped owner loans are the `leiht` names
    (`leihtAt`, C12) -- the callee holds them during the call, the caller gets
    them back on normal return; the linear handoffs are the `moves` names
    (`ownerMovesAt`, C09, including terminal `consumes`) and the checked mints the `mints` names (`praegtAt`).
    Every moved or minted mark is a stage-0 table owner. -/
def mkSig (u : UProg) (f : UFn) :
    Signatur (Fin u.tabs.length) (Fin u.globs.length) (Fin u.locks.length) (Fin u.marken.length) where
  params := f.params.map (·.2)
  erg := f.ergTy
  gruende := f.gruende
  haelt := heldAt u f
  schreibt := writesAt u f
  gschreibt := writesGAt u f
  konsumiert := nimmtAt u f
  produziert := gibtAt u f
  boden := f.boden
  owner := { moves := ownerMovesAt u f, loans := leihtAt u f, mints := praegtAt u f }

/-- The dummy signature: no parameters, no rights. -/
def dummySig (u : UProg) :
    Signatur (Fin u.tabs.length) (Fin u.globs.length) (Fin u.locks.length) (Fin u.marken.length) where
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
    Signatur (Fin u.tabs.length) (Fin u.globs.length) (Fin u.locks.length) (Fin u.marken.length) :=
  if h : n < (sigFns u).length then mkSig u ((sigFns u).get ⟨n, h⟩) else dummySig u

/-- **Conformance, decided** (`SigPasst` over the finite carriers of an elaborated unit): the first
    signature fits the second, with the same owner flow (the C09 handoff is part of conformance). -/
def sigPasstB {a b c : Nat} {Marke : Type} [DecidableEq Marke] (rang : Fin c → Int) (S T : Signatur (Fin a) (Fin b) (Fin c) Marke) : Bool :=
  decide (S.params = T.params) && decide (S.erg = T.erg) && decide (S.gruende = T.gruende) &&
  (List.finRange a).all (fun t => !S.schreibt t || T.schreibt t) &&
  (List.finRange b).all (fun g => !S.gschreibt g || T.gschreibt g) &&
  decide (S.konsumiert = T.konsumiert) && decide (S.produziert = T.produziert) &&
  S.haelt.all (fun L => decide (L ∈ T.haelt)) &&
  T.haelt.all (fun L => decide (L ∈ S.haelt) ||
    (match S.boden with | some c => decide (rang L < c) | none => false)) &&
  (match T.boden with
    | none => true
    | some c => match S.boden with | some c' => decide (c ≤ c') | none => false) &&
  decide (S.owner = T.owner)

theorem sigPasstB_ok {a b c : Nat} {Marke : Type} [DecidableEq Marke] {rang : Fin c → Int} {S T : Signatur (Fin a) (Fin b) (Fin c) Marke}
    (h : sigPasstB rang S T = true) : SigPasst rang S T := by
  unfold sigPasstB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hp, he⟩, hg⟩, hw⟩, hgw⟩, hk⟩, hpr⟩, hh⟩, hx⟩, hb⟩, ho⟩ := h
  refine ⟨hp, he, hg, fun t ht => ?_, fun g' hg' => ?_, hk, hpr, fun L hL => hh L hL, fun L hL hn => ?_,
    fun c hc => ?_, ho⟩
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
def vertragPasstB (actual expected : UFn) : Bool :=
  ((actual.needs.flatMap uKonjunkte).all (ensEnthalten (expected.needs.flatMap uKonjunkte))) &&
  ((expected.gives.flatMap uKonjunkte).all (ensEnthalten (actual.gives.flatMap uKonjunkte)))

/-- The same contract gate is used by runtime pointers and static function arguments. -/
def vertragPasstAt (u : UProg) (f : Fin u.fns.length) (n : Nat) : Bool :=
  vertragPasstB (fnAt u f) (sigFnAt u n)

theorem vertragPasstAt_ok (u : UProg) (f : Fin u.fns.length) (n : Nat)
    (h : vertragPasstAt u f n = true) :
    UEnsEinschluss ((sigFnAt u n).needs.flatMap uKonjunkte)
      ((fnAt u f).needs.flatMap uKonjunkte) ∧
    UEnsEinschluss ((fnAt u f).gives.flatMap uKonjunkte)
      ((sigFnAt u n).gives.flatMap uKonjunkte) := by
  unfold vertragPasstAt vertragPasstB at h
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

end Gabbro.Grammatik.Parser.UebersetzeAllg
