module

public import Grammatik.Kern.Syntax.Syntax.Teil1
public import Grammatik.Kern.Syntax.Syntax.Teil1b
public import Grammatik.Kern.Syntax.Marken.Owner.Flow
public import Grammatik.Kern.Syntax.Marken.Owner.Ledger
public import Grammatik.Kern.Syntax.Marken.Owner.Conservation
public import Grammatik.Kern.Syntax.Marken.Owner.InvocationFlow
public import Grammatik.Zielsatz.Einbettung.Einbettung

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## Checked call-boundary escrow (C09)

    At a call the caller's bindings named in the callee's `owner` inputs move
    into a frame escrow: loans are borrowed (`OwnerState.borrow`), moves are
    transferred (`OwnerState.transfer`). The callee runs with them; the return
    — normal or reason, both channels of `OwnerInvocation.Return` — gives back
    exactly the `owner` outputs: loans are restored (`returnBorrow`), moves are
    transferred back (after an `advance` for a stage-changing move, `retire`
    for a terminal one). Conservation of nominal owners — no duplication, no
    loss — is the grant lemmas below; the static half is
    `OwnerFlow.EscrowReady`, wired into `RufPasst.ownerReady`.

    The ghost ledger (`ownerLedgerOf`) stays the identity fold while no
    recorded event carries an owner payload; the per-call escrow above is the
    checked dynamic replay for the admitted flows. -/

/-- Conservation packaged from the static condition: returning never
    duplicates an input identity, every returned owner has an explicit input,
    and its stage stays in range. -/
theorem OwnerFlow.escrow_outputs_conserve
    {S : Signatur D.Tab D.Glob D.Lock D.Marke}
    {isOwner : D.Marke → Bool} {isEigner : D.Marke → Prop}
    (h : S.owner.EscrowReady isOwner D.stufen isEigner S.konsumiert) :
    (S.owner.outputs.map Prod.fst).Nodup ∧
      (∀ m s, (m, s) ∈ S.owner.outputs → ∃ before, (m, before) ∈ S.owner.inputs) ∧
      (∀ m s, (m, s) ∈ S.owner.outputs → isOwner m = true ∧ s < D.stufen m) :=
  ⟨OwnerFlow.outputs_nodup h.1, fun m s hm => OwnerFlow.output_from_input S.owner hm,
    fun m s hm => OwnerFlow.output_bounded h.1 hm⟩

/-- The exact return inventory is present after the call transformer. -/
theorem escrow_call_outputs_present (S : Signatur D.Tab D.Glob D.Lock D.Marke)
    (Λ : List (Res D)) {m : D.Marke} {s : Nat} (h : (m, s) ∈ S.owner.outputs) :
    Res.marke m s ∈ nachSig D S Λ := by
  unfold nachSig
  exact List.mem_append_right _
    (List.mem_map.mpr ⟨(m, s), List.mem_append_right _ h, rfl⟩)

/-- The static escrow condition implies the availability its inputs need: the
    canonical call transformer already holds every owner input. -/
theorem escrow_call_ready {V : Vertrag D} {S : Signatur D.Tab D.Glob D.Lock D.Marke}
    {Λ : List (Res D)} (hp : RufPasst D V S Λ) {p : D.Marke × Nat}
    (hmem : p ∈ S.owner.inputs) : Res.vonMarke D p ∈ Λ :=
  hp.owner_input_available hmem

/-! ## Call edge: loans are borrowed, moves are transferred -/

/-- A canonical call push borrowing a loan input: the callee frame gains the
    only accessor, the lender loses access, and spent authority and stages
    are untouched. -/
theorem escrow_call_borrow {c : OwnerInvocation D} {P : Programm D} {O : Orakel D}
    {passes : Nat} {M M' : RufMaschineG D} (push : c.Push P O passes M M')
    {N : OwnerNamespace D} {s s' : OwnerState D} {t : OwnerToken D}
    (hv : s.ledger.valid) (hop : push.borrow N s t = some s') :
    s'.ledger.valid ∧ s'.access N c.frame t ∧ ¬ s'.access N c.caller t ∧
      ¬ s'.owns N c.frame t ∧ s'.spent = s.spent ∧ s'.stage = s.stage :=
  push_borrow_valid push hv hop

/-- A canonical call push transferring a move input: the callee frame gains a
    fresh grant for the same owner, every saved use of the old grant dies, and
    spent authority is untouched. -/
theorem escrow_call_transfer {c : OwnerInvocation D} {P : Programm D} {O : Orakel D}
    {passes : Nat} {M M' : RufMaschineG D} (push : c.Push P O passes M M')
    {N : OwnerNamespace D} {s s' : OwnerState D} {t t' : OwnerToken D}
    (hv : s.ledger.valid) (hop : push.transfer N s t = some (s', t')) :
    s'.ledger.valid ∧ s'.owns N c.frame t' ∧ t'.mark = t.mark ∧ t'.stage = t.stage ∧
      (∀ frame, ¬ s'.access N frame t) ∧ s'.spent = s.spent :=
  push_transfer_valid push hv hop

/-- Preservation across a call push carrying escrow: the ghost ledger is
    stable (no recorded event carries an owner payload) while the escrow
    moves above hold the dynamic conservation. -/
theorem escrow_push_preserved {c : OwnerInvocation D} {P : Programm D} {O : Orakel D}
    {passes : Nat} {M M' : RufMaschineG D} (push : c.Push P O passes M M')
    {N : OwnerNamespace D} {base : OwnerState D} {threads : List Faden}
    (hI : OwnerInvG N base M threads) : OwnerInvG N base M' threads :=
  ownerInvG_schritt hI push.step

/-! ## Return edge: exactly the outputs come back, on both channels -/

/-- A canonical return restoring a loan: precisely the saved identity and
    stage come back to the lender. Both `rueck` and `why` outcomes share this
    `Return` evidence, so neither channel recreates a consumed mark. -/
theorem escrow_return_restore {c : OwnerInvocation D} {P : Programm D} {O : Orakel D}
    {passes : Nat} {M M' : RufMaschineG D} (pop : c.Return P O passes M M')
    {N : OwnerNamespace D} {s s' : OwnerState D} {t : OwnerToken D}
    (hv : s.ledger.valid) (hop : pop.restore N s t = some s') :
    s'.ledger.valid ∧ s'.access N c.caller t ∧ s'.spent = s.spent ∧ s'.stage = s.stage :=
  pop_restore_valid pop hv hop

/-- A canonical return handing a moved owner back: a fresh grant for the same
    nominal identity at the lender, with spent authority untouched. -/
theorem escrow_return_transfer {c : OwnerInvocation D} {P : Programm D} {O : Orakel D}
    {passes : Nat} {M M' : RufMaschineG D} (pop : c.Return P O passes M M')
    {N : OwnerNamespace D} {s s' : OwnerState D} {t t' : OwnerToken D}
    (hv : s.ledger.valid) (hback : s.transfer N c.frame c.caller t = some (s', t')) :
    s'.ledger.valid ∧ s'.owns N c.caller t' ∧ t'.mark = t.mark ∧ t'.stage = t.stage ∧
      (∀ frame, ¬ s'.access N frame t) ∧ s'.spent = s.spent :=
  OwnerState.transfer_grant hv hback

/-- A stage-changing move is advanced at the callee before the handoff back:
    the old stage becomes unusable in every frame, the identity and mint
    history survive. -/
theorem escrow_return_advance {c : OwnerInvocation D}
    {N : OwnerNamespace D} {s s' : OwnerState D}
    {t t' : OwnerToken D} (hadv : s.advance N c.frame t = some (s', t')) :
    s'.owns N c.frame t' ∧ t'.mark = t.mark ∧ t'.stage = t.stage + 1 ∧
      s'.spent = s.spent ∧ (∀ frame, ¬ s'.access N frame t) :=
  OwnerState.advance_grant hadv

/-- A terminal move is retired at the return: no accessor remains, and mint
    authority stays spent — the consumed mark cannot be re-minted. -/
theorem escrow_return_retire {c : OwnerInvocation D}
    {N : OwnerNamespace D} {s s' : OwnerState D} {t : OwnerToken D}
    (hv : s.ledger.valid) (hret : s.retire N c.frame t = some s') :
    s'.ledger.valid ∧ (∀ frame, ¬ s'.access N frame t) ∧ s'.spent = s.spent :=
  OwnerState.retire_grant hv hret

/-- Loans restore exactly: a checked borrow has its inverse at the matching
    return, innermost borrow outward for nested loans. -/
theorem escrow_loan_roundtrip {c : OwnerInvocation D} {P : Programm D} {O : Orakel D}
    {passes : Nat} {M₀ M₁ M₂ M₃ : RufMaschineG D}
    (push : c.Push P O passes M₀ M₁) (pop : c.Return P O passes M₂ M₃)
    {N : OwnerNamespace D} {s loaned : OwnerState D} {t : OwnerToken D}
    (hv : s.ledger.valid) (hb : push.borrow N s t = some loaned) :
    pop.restore N loaned t = some s :=
  OwnerInvocation.borrow_restore push pop hv hb

/-- Preservation across a canonical return carrying escrow, on either
    channel: the ghost ledger is stable while the restore above holds the
    dynamic conservation. -/
theorem escrow_pop_preserved {c : OwnerInvocation D} {P : Programm D} {O : Orakel D}
    {passes : Nat} {M M' : RufMaschineG D} (pop : c.Return P O passes M M')
    {N : OwnerNamespace D} {base : OwnerState D} {threads : List Faden}
    (hI : OwnerInvG N base M threads) : OwnerInvG N base M' threads :=
  ownerInvG_schritt hI pop.step

/-! ## Transport across an embedding -/

/-- Mapped fst-lists stay duplicate-free under an injective rename. -/
private theorem nodup_map_fst {Marke Marke' : Type} {l : List (Marke × Nat)}
    {f : Marke → Marke'} (hinj : Function.Injective f)
    (h : (l.map Prod.fst).Nodup) : ((l.map (Prod.map f id)).map Prod.fst).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    simp only [List.map_cons] at h ⊢
    obtain ⟨hnm, hnd⟩ := List.nodup_cons.mp h
    refine List.nodup_cons.mpr ⟨?_, ih hnd⟩
    intro hmem
    obtain ⟨y, hym, hfy⟩ := List.mem_map.mp hmem
    obtain ⟨z, hzm, hzy⟩ := List.mem_map.mp hym
    have heq : f z.1 = f x.1 := by
      have he : (Prod.map f id z).1 = (Prod.map f id x).1 := by
        rw [hzy]
        exact hfy
      exact he
    have hzx : z.1 = x.1 := hinj heq
    have hmem' : z.1 ∈ xs.map Prod.fst := List.mem_map.mpr ⟨z, hzm, rfl⟩
    exact hnm (hzx ▸ hmem')

/-- Escrow readiness transports across an embedding: the rename is injective,
    stages agree, and eigner tables map over. -/
theorem OwnerFlow.escrowReady_map {D D' : Deklaration} (E : Einbettung.Einbettung D D')
    (S : Signatur D.Tab D.Glob D.Lock D.Marke)
    (h : S.owner.EscrowReady (fun m => decide (m ∈ S.owner.inputs.map Prod.fst))
      D.stufen (fun m => ∃ t, m ∈ D.eigner t) S.konsumiert) :
    (E.sigE S).owner.EscrowReady
      (fun m => decide (m ∈ (E.sigE S).owner.inputs.map Prod.fst)) D'.stufen
      (fun m => ∃ t, m ∈ D'.eigner t) (E.sigE S).konsumiert := by
  have hinj : Function.Injective E.marke := fun x y he => by
    have hc := congrArg E.markeZ he
    rw [E.markeZ_marke, E.markeZ_marke] at hc
    exact Option.some.inj hc
  have hS : (E.sigE S).owner = S.owner.map E.marke := rfl
  have hK : (E.sigE S).konsumiert = S.konsumiert.map (Prod.map E.marke id) := rfl
  have hmoves : (S.owner.map E.marke).moves =
      S.owner.moves.map (fun y => (⟨E.marke y.mark, y.before, y.after⟩ : OwnerMove _)) := rfl
  have hloans : (S.owner.map E.marke).loans =
      S.owner.loans.map (Prod.map E.marke id) := rfl
  have hmints : (S.owner.map E.marke).mints =
      S.owner.mints.map (Prod.map E.marke id) := rfl
  rw [hS, hK]
  obtain ⟨hv, hd, hr⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · -- Validity: nodup via injectivity, bounds via the stage agreement.
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [OwnerFlow.inputs_map]
      exact nodup_map_fst hinj hv.1
    · intro x hx
      rw [hmoves] at hx
      obtain ⟨y, hym, heq⟩ := List.mem_map.mp hx
      have e_mark : x.mark = E.marke y.mark := (congrArg OwnerMove.mark heq).symm
      have e_bef : x.before = y.before := (congrArg OwnerMove.before heq).symm
      have e_aft : x.after = y.after := (congrArg OwnerMove.after heq).symm
      have hyin : (y.mark, y.before) ∈ S.owner.inputs := by
        simp only [OwnerFlow.inputs]
        exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨y, hym, rfl⟩))
      have hmem : (E.marke y.mark, y.before) ∈ (S.owner.map E.marke).inputs := by
        rw [OwnerFlow.inputs_map]
        exact List.mem_map.mpr ⟨(y.mark, y.before), hyin, rfl⟩
      have htrue : decide (E.marke y.mark ∈
          ((S.owner.map E.marke).inputs.map Prod.fst)) = true := by
        rw [decide_eq_true_eq]
        exact List.mem_map.mpr ⟨(E.marke y.mark, y.before), hmem, rfl⟩
      have hb := (hv.2.1 y hym).2
      simp only [e_mark, e_bef, e_aft, E.stufen]
      exact ⟨htrue, hb.1, hb.2⟩
    · intro p hp
      rw [hloans] at hp
      obtain ⟨q, hqm, heq⟩ := List.mem_map.mp hp
      have f1 : p.1 = E.marke q.1 := (congrArg Prod.fst heq).symm
      have f2 : p.2 = q.2 := (congrArg Prod.snd heq).symm
      have hqmem : E.marke q.1 ∈ ((S.owner.map E.marke).inputs.map Prod.fst) := by
        have hqin : q ∈ S.owner.inputs := by
          simp only [OwnerFlow.inputs]
          exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hqm)))
        have hmem : (E.marke q.1, q.2) ∈ (S.owner.map E.marke).inputs := by
          rw [OwnerFlow.inputs_map]
          exact List.mem_map.mpr ⟨q, hqin, rfl⟩
        exact List.mem_map.mpr ⟨(E.marke q.1, q.2), hmem, rfl⟩
      have hb := hv.2.2.1 q hqm
      simp only [f1, f2, E.stufen]
      exact ⟨decide_eq_true hqmem, hb.2⟩
    · intro p hp
      rw [hmints] at hp
      obtain ⟨q, hqm, heq⟩ := List.mem_map.mp hp
      have f1 : p.1 = E.marke q.1 := (congrArg Prod.fst heq).symm
      have f2 : p.2 = q.2 := (congrArg Prod.snd heq).symm
      have hqmem : E.marke q.1 ∈ ((S.owner.map E.marke).inputs.map Prod.fst) := by
        have hqin : q ∈ S.owner.inputs := by
          simp only [OwnerFlow.inputs]
          exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hqm)))
        have hmem : (E.marke q.1, q.2) ∈ (S.owner.map E.marke).inputs := by
          rw [OwnerFlow.inputs_map]
          exact List.mem_map.mpr ⟨q, hqin, rfl⟩
        exact List.mem_map.mpr ⟨(E.marke q.1, q.2), hmem, rfl⟩
      have hb := hv.2.2.2 q hqm
      simp only [f1, f2, E.stufen]
      exact ⟨decide_eq_true hqmem, hb.2⟩
  · -- Disjointness: a mapped ordinary consume cannot name a mapped owner.
    intro p hp
    obtain ⟨q, hqm, rfl⟩ := List.mem_map.mp hp
    intro hmem
    obtain ⟨y, hym, hfy⟩ := List.mem_map.mp hmem
    rw [OwnerFlow.inputs_map] at hym
    obtain ⟨z, hzm, hzy⟩ := List.mem_map.mp hym
    have heq : E.marke z.1 = E.marke q.1 := by
      have he : (Prod.map E.marke id z).1 = (Prod.map E.marke id q).1 := by
        rw [hzy]
        exact hfy
      exact he
    have hzx : z.1 = q.1 := hinj heq
    have hmem' : z.1 ∈ S.owner.inputs.map Prod.fst :=
      List.mem_map.mpr ⟨z, hzm, rfl⟩
    exact hd q hqm (hzx ▸ hmem')
  · -- Resolution: every mapped input has a mapped eigner table.
    intro m hm
    obtain ⟨y, hym, hfy⟩ := List.mem_map.mp hm
    rw [OwnerFlow.inputs_map] at hym
    obtain ⟨z, hzm, hzy⟩ := List.mem_map.mp hym
    have hz : z.1 ∈ S.owner.inputs.map Prod.fst :=
      List.mem_map.mpr ⟨z, hzm, rfl⟩
    obtain ⟨t, ht⟩ := hr z.1 hz
    refine ⟨E.tab t, ?_⟩
    rw [E.eigner]
    have he : E.marke z.1 = m := by
      have he' : (Prod.map E.marke id z).1 = y.1 := congrArg Prod.fst hzy
      rw [hfy] at he'
      exact he'
    rw [← he]
    exact List.mem_map.mpr ⟨z.1, ht, rfl⟩

end Gabbro.Grammatik
