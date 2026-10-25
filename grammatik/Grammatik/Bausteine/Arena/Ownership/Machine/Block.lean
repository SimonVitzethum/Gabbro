import Grammatik.Bausteine.Arena.Ownership.Machine.Leaf

/-! Residue bookkeeping for the unfold steps: a binder block in front of a
`schrumpf`, a weakened end context, and an end block run in block position
(an `else` branch, an unfolded end-block former), which never falls
through and so admits every end context. -/

namespace Gabbro.Grammatik.ArenaOwnership.Machine

open Source Body

variable {D : Deklaration}

/-- A context with one more name without provenance. -/
def _root_.Gabbro.Grammatik.ArenaOwnership.Source.Context.pad (c : Context) : Context :=
  { c with references := c.references ++ [none] }

theorem Context.pad_drop (c : Context) : c.pad.drop = c := by
  simp [Context.pad, Context.drop]

/-- The end context of a binder block: the binder's context `c1` dropped, possibly weakened. -/
def DropW (cout c1 : Context) : Prop := cout = c1.drop ∨ Weaker cout c1.drop

theorem DropW.weaken {c2 cout c1 : Context} (h : DropW cout c1) (hw : Weaker c2 cout) : DropW c2 c1 := by
  rcases h with rfl | h
  · exact Or.inr hw
  · exact Or.inr (hw.trans h)

theorem Weaker.pad {c2 c1 : Context} (hw : Weaker c2 c1.drop) (hlen : c1.references.length ≠ 0) :
    Weaker c2.pad c1 := by
  obtain ⟨hr, hn, hl, hrefs⟩ := hw
  refine ⟨fun i => hr i, hn, ?_, ?_⟩
  · simp only [Context.pad, List.length_append, List.length_singleton]
    simp only [Context.drop, List.length_dropLast] at hl
    omega
  · intro p o hp
    simp only [Context.pad] at hp
    have hpl : p < c2.references.length := by
      rcases Nat.lt_or_ge p c2.references.length with h | h
      · exact h
      · rw [List.getElem?_append_right h] at hp
        rcases Nat.eq_zero_or_pos (p - c2.references.length) with he | he
        · rw [he] at hp; simp at hp
        · rw [List.getElem?_eq_none (by simp; omega)] at hp; cases hp
    rw [List.getElem?_append_left hpl] at hp
    obtain ⟨h1, h2⟩ := hrefs p o hp
    refine ⟨?_, h2⟩
    simp only [Context.drop, List.getElem?_dropLast] at h1
    split at h1
    · exact h1
    · cases h1

section Cont

variable {A : FreiForm D} {I : Interfaces A} {V : Vertrag D} {out : Flow.Output A V.erg}

theorem Cont.schrumpf {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} {k c1 : Context}
    {r : GRest D V l Γ Λ} (hk : k.references.length ≤ Γ.length) (h : Cont A I out k c1.drop r) :
    Cont A I out (Γ := τ :: Γ) k c1 (.schrumpf r) := by
  rcases h with h | ⟨hu, hx⟩
  · exact Or.inl (.schrumpf r hk h)
  · refine Or.inr ⟨?_, .schrumpf r hk hx⟩
    intro he
    apply hu
    simp only [Context.drop, List.length_dropLast, he, List.length_cons]
    omega

/-- **A binder block in front of a shrink**, whatever weakening its end context went through. -/
theorem OR.binder {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} {k c0 c1 cout : Context}
    {b : Block D V l (τ :: Γ) Λ Λ'} {r : GRest D V l Γ Λ'} (hb : OB A I out k c0 b c1) (hd : DropW cout c1)
    (hk : k.references.length ≤ Γ.length) (hc : Cont A I out k cout r) :
    OR A I out k c0 (.dann b (.schrumpf r)) := by
  rcases hd with rfl | hw
  · exact OR.of_cont hb (Cont.schrumpf hk hc)
  · by_cases hlen : c1.references.length = (τ :: Γ).length
    · have hw' := Weaker.pad hw (by rw [hlen]; simp)
      refine OR.of_cont (.weaken _ hb hw') (Cont.schrumpf hk ?_)
      rw [Context.pad_drop]; exact hc
    · exact .dannDead b _ hb hlen (.schrumpf r hk hc.exits)

/-- A weakened end context. -/
theorem OR.weakened {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {k c0 c1 c2 : Context}
    {b : Block D V l Γ Λ Λ'} {r : GRest D V l Γ Λ'} (hb : OB A I out k c0 b c1) (hw : c2 = c1 ∨ Weaker c2 c1)
    (hc : Cont A I out k c2 r) : OR A I out k c0 (.dann b r) := by
  rcases hw with rfl | hw
  · exact OR.of_cont hb hc
  · exact OR.of_cont (.weaken _ hb hw) hc

end Cont

/-! ## An end block in block position -/

section Ende

variable {A : FreiForm D} {I : Interfaces A} {V : Vertrag D} {out : Flow.Output A V.erg}

/-- **An end block run as a block never falls through: it admits every end context.** -/
theorem oe_alsBlock : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {k c : Context} {e : Endblock D V l Γ Λ},
    OE A I out k c e → ∀ c', OB A I out k c e.alsBlock.2 c'
  | _, _, _, _, _, _, .ret e hΛ he, c' => .cons _ _ (.ret e hΛ he) .nil
  | _, _, _, _, _, _, .retWhy r hΛ hf, c' => .cons _ _ (.retWhy r hΛ hf) .nil
  | _, _, _, _, _, _, .leave h hx, c' => .cons _ _ (.leave h hx) .nil
  | _, _, _, _, _, _, .next h hx, c' => .cons _ _ (.next h hx) .nil
  | _, _, _, _, _, _, .cons s rest hs hr, c' => .cons _ _ hs (oe_alsBlock hr c')
  | _, _, _, _, _, _, .dead s rest hs, c' => .dead _ _ hs
  | _, _, _, _, _, _, .bind e rest he hr, c' => by
    have := OB.bind (out := out) e rest.alsBlock.2 he (oe_alsBlock hr c'.pad)
    rwa [Context.pad_drop] at this
  | _, _, _, _, _, _, .bindCall f args he hp hr rest ha hplan hrest, c' => by
    have := OB.bindCall (out := out) f args he hp hr rest.alsBlock.2 ha hplan (oe_alsBlock hrest c'.pad)
    rwa [Context.pad_drop] at this
  | _, _, _, _, _, _, .bindCallElse f args he hp hr err rest ha hplan herr hrest, c' => by
    have := OB.bindCallElse (out := out) f args he hp hr err rest.alsBlock.2 ha hplan herr
      (oe_alsBlock hrest c'.pad)
    rwa [Context.pad_drop] at this
  | _, _, _, _, _, _, .bindAxiom a args he hw hg hd hgd rest hfree ha hrest, c' => by
    have := OB.bindAxiom (out := out) a args he hw hg hd hgd rest.alsBlock.2 hfree ha (oe_alsBlock hrest c'.pad)
    rwa [Context.pad_drop] at this
  | _, _, _, _, _, _, .bindAxiomElse a args he hr hw hg hd hgd err rest hfree ha herr hrest, c' => by
    have := OB.bindAxiomElse (out := out) a args he hr hw hg hd hgd err rest.alsBlock.2 hfree ha herr
      (oe_alsBlock hrest c'.pad)
    rwa [Context.pad_drop] at this
  | _, _, _, _, _, _, .regRead r hk rest hrest, c' => by
    have := OB.regRead (out := out) r hk rest.alsBlock.2 (oe_alsBlock hrest c'.pad)
    rwa [Context.pad_drop] at this
  | _, _, _, _, _, _, .regReadElse r hk z sonst rest hz hs hrest, c' => by
    have := OB.regReadElse (out := out) r hk z sonst rest.alsBlock.2 hz hs (oe_alsBlock hrest c'.pad)
    rwa [Context.pad_drop] at this
  | _, _, _, _, _, _, .awaits g pl hp hL ha rest hrest, c' => by
    have := OB.awaits (out := out) g pl hp hL ha rest.alsBlock.2 (oe_alsBlock hrest c'.pad)
    rwa [Context.pad_drop] at this
  | _, _, _, _, _, _, .bindCallInd p args he hp hr rest J owner hJ hpc ha hplan hrest, c' => by
    have := OB.bindCallInd (out := out) p args he hp hr rest.alsBlock.2 J owner hJ hpc ha hplan
      (oe_alsBlock hrest c'.pad)
    rwa [Context.pad_drop] at this

/-- **An `else` branch in front of its continuation.** -/
theorem OR.sonst {l : Bool} {Γ : Ctx} {Λ Λk : List (Res D)} {k c : Context} {e : Endblock D V l Γ Λ}
    {r : GRest D V l Γ Λk} (he : OE A I out k c e) (hx : OX A I out k r) :
    OR A I out k c (.dann e.alsBlock.2 (.abbruch r)) :=
  OR.of_dead (oe_alsBlock he _) (.abbruch r hx)

end Ende

end Gabbro.Grammatik.ArenaOwnership.Machine
