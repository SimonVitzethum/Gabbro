module

public import Grammatik.Bausteine.Arena.Ownership.Body.Check.Lemmas
public import Grammatik.Bausteine.Arena.Ownership.Body.Check.Sound.Teil1
public import Grammatik.Bausteine.Arena.Ownership.Body.Check.Sound.Teil2.Teil2

@[expose] public section

namespace Gabbro.Grammatik.ArenaOwnership.Body
open Source
variable {D : Deklaration}
section Sound
variable {A : FreiForm D} {I : Interfaces A} {fs : List D.Fn} {V : Vertrag D} {out : Flow.Output A V.erg}
variable (hvoll : ∀ f, f ∈ fs)
include hvoll

set_option linter.unusedSectionVars false in
theorem chkB_sound_floatOf 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_l1}
    {zi_h1}
    (e)
    (lo)
    (hi)
    (rest)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (ih_chkB_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c rest) (chkB A I fs out rest k c))
    : Supports (OB A I out k c (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Block D V l Γ Λ Λ')) (chkB A I fs out (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Block D V l Γ Λ Λ') k c) :=
  by
  simp only [chkB]
  exact supports_condDrop (fun _ => ih_chkB_sound_rest k _ hk (Context.bindNone_bounded hc))
    (fun h c1 h1 => OB.floatOf e lo hi rest h h1)

set_option linter.unusedSectionVars false in
theorem chkB_sound_floatNarrow 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_l1}
    {zi_h1}
    (e)
    (lo)
    (hi)
    (sonst)
    (rest)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (ih_chkB_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c rest) (chkB A I fs out rest k c))
    (ih_chkE_sound_sonst : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → chkE A I fs out sonst k c = true → OE A I out k c sonst)
    : Supports (OB A I out k c (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Block D V l Γ Λ Λ')) (chkB A I fs out (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Block D V l Γ Λ Λ') k c) :=
  by
  simp only [chkB]
  exact supports_condDrop (fun _ => ih_chkB_sound_rest k _ hk (Context.bindNone_bounded hc))
    (fun h c1 h1 => by
      simp only [Bool.and_eq_true] at h
      exact OB.floatNarrow e lo hi sonst rest h.1 (ih_chkE_sound_sonst k c hk hc h.2) h1)

set_option linter.unusedSectionVars false in
theorem chkE_sound_cons 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_Λ'}
    (s)
    (rest)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (h : chkE A I fs out (.cons (Λ' := zi_Λ') s rest : Endblock D V l Γ Λ) k c = true)
    (ih_chkS_sound_s : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OS A I out k c s) (chkS A I fs out s k c))
    (ih_chkE_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → chkE A I fs out rest k c = true → OE A I out k c rest)
    : OE A I out k c (.cons (Λ' := zi_Λ') s rest : Endblock D V l Γ Λ) :=
  by
  have hs := ih_chkS_sound_s k c hk hc
  have ih := fun c1 hc1 => ih_chkE_sound_rest k c1 hk hc1
  simp only [chkE] at h
  generalize chkS A I fs out s k c = r at hs h
  match r, hs, h with
  | some (some c1), hs, h => exact OE.cons s rest hs.1 (ih c1 hs.2 h)
  | some none, hs, _ => exact OE.dead s rest hs
  | none, _, h => cases h

set_option linter.unusedSectionVars false in
theorem chkE_sound_bindCall 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (f)
    (args)
    (he)
    (hp)
    (hr)
    (rest)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (h : chkE A I fs out (.bindCall (τ := zi_τ) f args he hp hr rest : Endblock D V l Γ Λ) k c = true)
    (ih_chkE_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → chkE A I fs out rest k c = true → OE A I out k c rest)
    : OE A I out k c (.bindCall (τ := zi_τ) f args he hp hr rest : Endblock D V l Γ Λ) :=
  by
  simp only [chkE, Bool.and_eq_true] at h
  exact OE.bindCall f args he hp hr rest h.1.1 h.1.2
    (ih_chkE_sound_rest k _ hk (resultContext_bounded (afterCall_bounded hc) _) h.2)

set_option linter.unusedSectionVars false in
theorem chkE_sound_bindCallElse 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (f)
    (args)
    (he)
    (hp)
    (hr)
    (err)
    (rest)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (h : chkE A I fs out (.bindCallElse (τ := zi_τ) f args he hp hr err rest : Endblock D V l Γ Λ) k c = true)
    (ih_chkE_sound_err : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → chkE A I fs out err k c = true → OE A I out k c err)
    (ih_chkE_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → chkE A I fs out rest k c = true → OE A I out k c rest)
    : OE A I out k c (.bindCallElse (τ := zi_τ) f args he hp hr err rest : Endblock D V l Γ Λ) :=
  by
  simp only [chkE, Bool.and_eq_true] at h
  exact OE.bindCallElse f args he hp hr err rest h.1.1.1 h.1.1.2
    (ih_chkE_sound_err k _ hk (Context.bindNone_bounded (afterCall_bounded hc)) h.1.2)
    (ih_chkE_sound_rest k _ hk (resultContext_bounded (afterCall_bounded hc) _) h.2)

set_option linter.unusedSectionVars false in
theorem chkE_sound_bindAxiom 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (a)
    (args)
    (he)
    (hw)
    (hg)
    (hd)
    (hgd)
    (rest)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (h : chkE A I fs out (.bindAxiom (τ := zi_τ) a args he hw hg hd hgd rest : Endblock D V l Γ Λ) k c = true)
    (ih_chkE_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → chkE A I fs out rest k c = true → OE A I out k c rest)
    : OE A I out k c (.bindAxiom (τ := zi_τ) a args he hw hg hd hgd rest : Endblock D V l Γ Λ) :=
  by
  simp only [chkE, Bool.and_eq_true, decide_eq_true_eq] at h
  exact OE.bindAxiom a args he hw hg hd hgd rest h.1.1 h.1.2
    (ih_chkE_sound_rest k _ hk (Context.bindNone_bounded hc) h.2)

set_option linter.unusedSectionVars false in
theorem chkE_sound_bindAxiomElse 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (a)
    (args)
    (he)
    (hr)
    (hw)
    (hg)
    (hd)
    (hgd)
    (err)
    (rest)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (h : chkE A I fs out (.bindAxiomElse (τ := zi_τ) a args he hr hw hg hd hgd err rest : Endblock D V l Γ Λ) k c = true)
    (ih_chkE_sound_err : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → chkE A I fs out err k c = true → OE A I out k c err)
    (ih_chkE_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → chkE A I fs out rest k c = true → OE A I out k c rest)
    : OE A I out k c (.bindAxiomElse (τ := zi_τ) a args he hr hw hg hd hgd err rest : Endblock D V l Γ Λ) :=
  by
  simp only [chkE, Bool.and_eq_true, decide_eq_true_eq] at h
  exact OE.bindAxiomElse a args he hr hw hg hd hgd err rest h.1.1.1 h.1.1.2
    (ih_chkE_sound_err k _ hk (Context.bindNone_bounded hc) h.1.2)
    (ih_chkE_sound_rest k _ hk (Context.bindNone_bounded hc) h.2)

set_option linter.unusedSectionVars false in
theorem chkE_sound_regReadElse 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (r)
    (hk')
    (zusage)
    (sonst)
    (rest)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (h : chkE A I fs out (.regReadElse r hk' zusage sonst rest : Endblock D V l Γ Λ) k c = true)
    (ih_chkE_sound_sonst : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → chkE A I fs out sonst k c = true → OE A I out k c sonst)
    (ih_chkE_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → chkE A I fs out rest k c = true → OE A I out k c rest)
    : OE A I out k c (.regReadElse r hk' zusage sonst rest : Endblock D V l Γ Λ) :=
  by
  simp only [chkE, Bool.and_eq_true] at h
  exact OE.regReadElse r hk' zusage sonst rest h.1.1 (ih_chkE_sound_sonst k c hk hc h.1.2)
    (ih_chkE_sound_rest k _ hk (Context.bindNone_bounded hc) h.2)

set_option linter.unusedSectionVars false in
theorem chkE_sound_bindCallInd 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_n}
    {zi_τ}
    (p)
    (args)
    (he)
    (hp)
    (hr)
    (rest)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (h : chkE A I fs out (.bindCallInd (n := zi_n) (τ := zi_τ) p args he hp hr rest : Endblock D V l Γ Λ) k c = true)
    (ih_chkE_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → chkE A I fs out rest k c = true → OE A I out k c rest)
    : OE A I out k c (.bindCallInd (n := zi_n) (τ := zi_τ) p args he hp hr rest : Endblock D V l Γ Λ) :=
  by
  simp only [chkE, Bool.and_eq_true] at h
  exact OE.bindCallInd p args he hp hr rest _ _ (sigCompatB_sound hvoll h.1.1.2) h.1.1.1.1 h.1.1.1.2 h.1.2
    (ih_chkE_sound_rest k _ hk (resultContextB_bounded (afterCall_bounded hc) _) h.2)

set_option linter.unusedSectionVars false in
theorem chkArms_sound_ca 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (ca)
    (zz1)
    (b)
    (rest)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (ih_chkB_sound_b : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c b) (chkB A I fs out b k c))
    (ih_chkArms_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OArms A I out k c rest) (chkArms A I fs out rest k c))
    : Supports (OArms A I out k c (.cons b rest : Arms D V l Γ Λ Λ' (ca :: zz1 : List (Option (Int × Int))))) (chkArms A I fs out (.cons b rest : Arms D V l Γ Λ Λ' (ca :: zz1 : List (Option (Int × Int)))) k c) :=
  by
  simp only [chkArms]
  exact supports_join
    (supports_map (fun c1 => armDrop c1 ca) (fun x => armBind x ca)
      (fun x => by cases ca <;> simp only [armDrop, armBind, Context.bind_drop])
      (fun x hx => armBind_bounded hx ca) (fun x hx => armDrop_bounded hx ca)
      (ih_chkB_sound_b k (armBind c ca) hk (armBind_bounded hc ca)))
    (ih_chkArms_sound_rest k c hk hc)
    (fun x y z hx hy wx wy => by
      obtain ⟨c1, hb1, rfl⟩ := hx
      exact OArms.cons b rest hb1 wx (OArms.weaken hy wy))

end Sound
end Gabbro.Grammatik.ArenaOwnership.Body
