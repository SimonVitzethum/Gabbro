module

public import Arm.Mem.Event
public import Arm.Mem.Exec
public import Arm.Mem.Barriers.Teil1

@[expose] public section

namespace Arm

theorem plain_never_bob (x : Exec)
    (h : x.evs.all (fun e => decide ((e.isDmbFull || e.isDmbLd || e.isDmbSt || e.isDsbFull || e.isDsbLd || e.isDsbSt || e.isAcquire || e.isAcquirePC || e.isRelease || e.isIsb) = false)) = true) :
    bob x = [] := by
  have hdmb : x.evs.all (fun e => decide ((e.isDmbFull || e.isDmbLd || e.isDmbSt) = false)) = true := by
    rw [List.all_eq_true] at h ⊢
    intro e he
    have hp := h e he
    have hs : (e.isDmbFull || e.isDmbLd || e.isDmbSt) = false :=
      (big_plain_split e hp).1
    rw [hs]
    rfl
  have hdsb : x.evs.all (fun e => decide ((e.isDsbFull || e.isDsbLd || e.isDsbSt) = false)) = true := by
    rw [List.all_eq_true] at h ⊢
    intro e he
    have hp := h e he
    have hs : (e.isDsbFull || e.isDsbLd || e.isDsbSt) = false :=
      (big_plain_split e hp).2.1
    rw [hs]
    rfl
  have hacq : x.evs.all (fun e => decide ((e.isAcquire || e.isAcquirePC) = false)) = true := by
    rw [List.all_eq_true] at h ⊢
    intro e he
    have hp := h e he
    have hs : (e.isAcquire || e.isAcquirePC) = false :=
      (big_plain_split e hp).2.2.1
    rw [hs]
    rfl
  have hrel : x.evs.all (fun e => decide (e.isRelease = false)) = true := by
    rw [List.all_eq_true] at h ⊢
    intro e he
    have hp := h e he
    have hs : e.isRelease = false := (big_plain_split e hp).2.2.2.1
    rw [hs]
    rfl
  have hrelacq : x.evs.all (fun e => decide ((e.isRelease || e.isAcquire || e.isAcquirePC) = false)) = true := by
    rw [List.all_eq_true] at h ⊢
    intro e he
    have hp := h e he
    have hs : (e.isRelease || e.isAcquire || e.isAcquirePC) = false :=
      (big_plain_split e hp).2.2.2.2.1
    rw [hs]
    rfl
  have hisb : x.evs.all (fun e => decide (e.isIsb = false)) = true := by
    rw [List.all_eq_true] at h ⊢
    intro e he
    have hp := h e he
    have hs : e.isIsb = false := (big_plain_split e hp).2.2.2.2.2
    rw [hs]
    rfl
  have h1 : ∀ (a c : Nat), dmbHolds x a c = false :=
    fun a c => dmbHolds_false_of_plain x a c hdmb
  have h2 : ∀ (a c : Nat), dsbHolds x a c = false :=
    fun a c => dsbHolds_false_of_plain x a c hdsb
  have h3 : ∀ (a c : Nat), acqHolds x a c = false :=
    fun a c => acqHolds_false_of_plain x a c hacq
  have h4 : ∀ (a c : Nat), relHolds x a c = false :=
    fun a c => relHolds_false_of_plain x a c hrel
  have h5 : ∀ (a c : Nat), relAcqHolds x a c = false :=
    fun a c => relAcqHolds_false_of_plain x a c hrelacq
  have h6 : ∀ (a c : Nat), isbHolds x a c = false :=
    fun a c => isbHolds_false_of_plain x a c hisb
  unfold bob
  rw [List.filter_eq_nil_iff]
  intro p _
  have hfalse : bobHolds x p.1 p.2 = false := by
    unfold bobHolds
    rw [h1 p.1 p.2, h2 p.1 p.2, h3 p.1 p.2, h4 p.1 p.2, h5 p.1 p.2,
      h6 p.1 p.2]
    rfl
  rw [hfalse]
  exact by decide

/-- Witness: the plainness premise is load-bearing — the fenced shape IS
    ordered, so `plain_never_bob` is not vacuous. -/
theorem plain_never_bob_zeuge : bob mpDmbSt ≠ [] := by decide

#print axioms plain_never_bob
#print axioms dmbHolds_false_of_plain
#print axioms dsbHolds_false_of_plain
#print axioms acqHolds_false_of_plain
#print axioms relHolds_false_of_plain
#print axioms relAcqHolds_false_of_plain
#print axioms isbHolds_false_of_plain
#print axioms big_plain_split

/-
CUTS:
- Proved: the six `bob` clauses (DMB full/ld/st, DSB data classes, LDAR,
  LDAPR/RCpc, STLR, STLR`;po;`LDAR/LDAPR, ISB-with-ctrl), `bob` itself, the
  MP witness facts, and `plain_never_bob` with its splitter and witnesses.
- Shareability v1: only `ish`/`sy` barriers order observers (`Domain.v1Orders`);
  `nsh`/`osh` barriers order nothing. No per-observer domainFiltering yet.
- DSB completion beyond data accesses has no event in this model (no
  instruction-completion event): only the data classes are ordered here.
- ISB fetch half has no event in this model (no fetch event): only the
  read`;ctrl;`ISB`;po;`mem leg is ordered here.
- `Exec` well-formedness (unique ids, po transitive/irreflexive, ctrl shape)
  is agent 06's `Exec.lean`, not stated here; `bob` reads `po`/`ctrl` as given.
- `bob` is one leg for agent 07's `OrderingParts.bob`; coherence, reads-from,
  from-reads, dependencies `addr`/`data`, `rmw` and the outer Arm order are
  not in this file.
- `Barrier` (`Arm/Basic.lean`, frozen) has no SB/SSBB/PSSBB form, so those
  barriers cannot be named here; proposed as vocabulary follow-up.
- The `excl` (exclusive-pair) flag carries no extra `bob` edge: exclusives
  order through their `ord` (plain/acquire/release) and barriers, as Arm lists.
-/
