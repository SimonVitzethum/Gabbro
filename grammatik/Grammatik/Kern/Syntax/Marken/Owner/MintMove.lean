module

public import Grammatik.Kern.Syntax.Marken.Owner.Interface
public import Grammatik.Kern.Syntax.Marken.Owner.State

@[expose] public section

namespace Gabbro.Grammatik.OwnerFlow

variable {D : Deklaration}

/-- Every minted owner is held from the start frame: mints are inputs. -/
theorem mint_mem_inputs (F : OwnerFlow D.Marke) {m : D.Marke} {s : Nat}
    (h : (m, s) ∈ F.mints) : (m, s) ∈ F.inputs := by
  simp only [inputs]
  exact List.mem_append.mpr (Or.inr (Or.inr h))

/-- Every minted owner is returned: mints are outputs, never ordinaria
    production (`eigner_nie_erzeugt` stays about `produziert` alone). -/
theorem mint_mem_outputs (F : OwnerFlow D.Marke) {m : D.Marke} {s : Nat}
    (h : (m, s) ∈ F.mints) : (m, s) ∈ F.outputs := by
  simp only [outputs]
  exact List.mem_append.mpr (Or.inr (Or.inr h))

/-- A call appends every mint output: the minter's caller (and, by the same
    transformer, the checked start frame) gains the fresh owner. Ghost:
    no runtime word, the `nachSig` inventory alone. -/
theorem mint_present_nachSig (S : Signatur D.Tab D.Glob D.Lock D.Marke)
    (Λ : List (Res D)) {m : D.Marke} {s : Nat} (h : (m, s) ∈ S.owner.mints) :
    Res.vonMarke D (m, s) ∈ nachSig D S Λ := by
  unfold nachSig
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨(m, s), ?_, rfl⟩
  simp only [Signatur.outputMarks]
  exact List.mem_append.mpr (Or.inr (mint_mem_outputs S.owner h))

/-- The start frame holds every minted owner: the admitted minter runs with
    its fresh owner in hand. `anfang` is `haelt` plus the input marks. -/
theorem mint_anfang_mem (S : Signatur D.Tab D.Glob D.Lock D.Marke)
    {m : D.Marke} {s : Nat} (h : (m, s) ∈ S.owner.mints) :
    Res.vonMarke D (m, s) ∈ Signatur.anfang D S := by
  simp only [Signatur.anfang, Signatur.inputMarks]
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨(m, s), ?_, rfl⟩
  exact List.mem_append.mpr (Or.inr (mint_mem_inputs S.owner h))

/-- The return carries every minted owner on either channel: `ende` is the
    one inventory both `Stmt.ret` and `Stmt.retWhy` balance against. -/
theorem mint_ende_mem (V : Vertrag D) (S : Signatur D.Tab D.Glob D.Lock D.Marke)
    (hV : V.owner = S.owner) {m : D.Marke} {s : Nat} (h : (m, s) ∈ S.owner.mints) :
    Res.vonMarke D (m, s) ∈ V.ende := by
  simp only [Vertrag.ende, hV]
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨(m, s), ?_, rfl⟩
  simp only [Signatur.outputMarks]
  exact List.mem_append.mpr (Or.inr (mint_mem_outputs S.owner h))

/-- A minted output is a declared eigner: provenance from the checked
    escrow condition, never from ordinary production. -/
theorem mint_resolved {S : Signatur D.Tab D.Glob D.Lock D.Marke}
    {isOwner : D.Marke → Bool} {isEigner : D.Marke → Prop}
    (h : S.owner.EscrowReady isOwner D.stufen isEigner S.konsumiert)
    {m : D.Marke} {s : Nat} (hm : (m, s) ∈ S.owner.mints) : isEigner m := by
  have hmem : m ∈ S.owner.inputs.map Prod.fst :=
    List.mem_map.mpr ⟨(m, s), mint_mem_inputs S.owner hm, rfl⟩
  exact h.2.2 m hmem

/-- A consumed mark is never also minted in one signature: the disjointness
    half of the checked escrow condition covers mints through `inputs`. -/
theorem mint_disjoint {S : Signatur D.Tab D.Glob D.Lock D.Marke}
    {isOwner : D.Marke → Bool} {isEigner : D.Marke → Prop}
    (h : S.owner.EscrowReady isOwner D.stufen isEigner S.konsumiert)
    {p : D.Marke × Nat} (hp : p ∈ S.konsumiert) (hm : p.1 ∈ S.owner.mints.map Prod.fst) : False := by
  obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
  have hmem : q.1 ∈ S.owner.inputs.map Prod.fst :=
    List.mem_map.mpr ⟨q, mint_mem_inputs S.owner hq, rfl⟩
  have hne := h.2.1 p hp
  have heq : q.1 = p.1 := congrArg Prod.fst he
  rw [heq] at hmem
  exact hne hmem

end Gabbro.Grammatik.OwnerFlow

namespace Gabbro.Grammatik.OwnerMove

variable {D : Deklaration}

/-- The handoff input: a move names its before-stage in the inputs. -/
theorem before_mem_inputs (F : OwnerFlow D.Marke) (x : OwnerMove D.Marke)
    (h : x ∈ F.moves) : (x.mark, x.before) ∈ F.inputs := by
  simp only [OwnerFlow.inputs]
  exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨x, h, rfl⟩))

/-- A handing-back move is received as an output: the same nominal identity
    at the indicated stage, on the normal and the reason channel alike
    (`ende` is channel-independent). -/
theorem output_of_some (F : OwnerFlow D.Marke) (x : OwnerMove D.Marke)
    (h : x ∈ F.moves) {s : Nat} (hs : x.after = some s) :
    (x.mark, s) ∈ F.outputs := by
  simp only [OwnerFlow.outputs]
  apply List.mem_append.mpr
  refine Or.inl ?_
  apply List.mem_filterMap.mpr
  refine ⟨x, h, ?_⟩
  simp only [hs, Option.map_some]

/-- A single terminal move contributes no moved output at all. -/
theorem single_none_outputs (m : D.Marke) (b : Nat) :
    ({ moves := [{ mark := m, before := b, after := none }] } : OwnerFlow D.Marke).outputs = [] := by
  rfl

end Gabbro.Grammatik.OwnerMove

namespace Gabbro.Grammatik.OwnerState

variable {D : Deklaration}

/-- A successful mint issues exactly the declared identity and stage: the
    ledger token carries the mint declaration's mark and stage. -/
theorem mint_token_identity {N : OwnerNamespace D} {d : OwnerMintDecl D}
    {s s' : OwnerState D} {f : ArenaOwnership.Frame} {t : OwnerToken D}
    (h : recordMint N d s f = some (s', t)) : t.mark = d.mark ∧ t.stage = d.stage := by
  unfold recordMint at h
  split at h
  · cases ha : s.ledger.allocate f (N.key d.mark) with
    | none => simp only [ha] at h; cases h
    | some result =>
      simp only [ha] at h
      cases h
      exact ⟨rfl, rfl⟩
  · cases h

end Gabbro.Grammatik.OwnerState
