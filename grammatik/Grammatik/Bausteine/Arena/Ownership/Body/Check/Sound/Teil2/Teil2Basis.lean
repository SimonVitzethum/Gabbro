module

public import Grammatik.Bausteine.Arena.Ownership.Body.Check.Lemmas
public import Grammatik.Bausteine.Arena.Ownership.Body.Check.Sound.Teil1
public import Grammatik.Bausteine.Arena.Ownership.Body.Check.Sound.Teil2.Teil1

@[expose] public section

namespace Gabbro.Grammatik.ArenaOwnership.Body
open Source
variable {D : Deklaration}
section Sound
variable {A : FreiForm D} {I : Interfaces A} {fs : List D.Fn} {V : Vertrag D} {out : Flow.Output A V.erg}
variable (hvoll : ∀ f, f ∈ fs)
include hvoll

set_option linter.unusedSectionVars false in
theorem chkB_sound_cons 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_Λ'}
    (s)
    (rest)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (ih_chkS_sound_s : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OS A I out k c s) (chkS A I fs out s k c))
    (ih_chkB_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c rest) (chkB A I fs out rest k c))
    (ih_relB_sound_rest : ∀ (k : Context), ∀ (c : Context), ∀ (p : Nat), k.bounded → c.bounded → Supports (fun x => ∃ (g : D.Glob) (e2 : Expr D _ _ (D.gtyp g)) (hwK : V.gschreibt g = true) (hLK : gdarf D g _) (rest' : Block D V _ _ _ _), rest = .cons (.assignGlob g e2 hwK hLK) rest' ∧ g = A.kopf ∧ exprVarPos e2 = some p ∧ OB A I out k c rest' x) (relB A I fs out rest k c p))
    : Supports (OB A I out k c (.cons (Λ' := zi_Λ') s rest : Block D V l Γ Λ Λ')) (chkB A I fs out (.cons (Λ' := zi_Λ') s rest : Block D V l Γ Λ Λ') k c) :=
  by
  have hgen := supports_seq (ih_chkS_sound_s k c hk hc) (fun c1 hc1 => ih_chkB_sound_rest k c1 hk hc1)
  have hrel := fun c2 p hc2 => ih_relB_sound_rest k c2 p hk hc2
  cases s with
  | assignSlot t f i e hw hL =>
    simp only [chkB]
    by_cases hcb : ((if ht : t = A.tab then decide (ht ▸ f = A.nxt) else false) &&
        exprGlob e == some A.kopf) = true
    · rw [if_pos hcb]
      simp only [Bool.and_eq_true, beq_iff_eq] at hcb
      obtain ⟨ht, hf⟩ := linkField_sound hcb.1
      split
      · rename_i p c2 o hp hcons
        exact supports_mono (fun x hx => by
          obtain ⟨g, e2, hwK, hLK, rest', rfl, hg, he2, hob⟩ := hx
          exact OB.release t f i e hw hL g e2 hwK hLK rest' ht hf hp hcb.2 hg he2 hcons hob)
          (hrel c2 p (consume_bounded hc hcons))
      · trivial
    · rw [if_neg hcb]
      exact hgen
  | _ => simp only [chkB]; exact hgen

set_option linter.unusedSectionVars false in
theorem chkB_sound_bind 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_τ}
    (e)
    (rest)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (ih_chkB_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c rest) (chkB A I fs out rest k c))
    : Supports (OB A I out k c (.bind (τ := zi_τ) e rest : Block D V l Γ Λ Λ')) (chkB A I fs out (.bind (τ := zi_τ) e rest : Block D V l Γ Λ Λ') k c) :=
  by
  simp only [chkB]
  exact supports_condDrop (fun _ => ih_chkB_sound_rest k _ hk (Context.bindOrigin_bounded hc e))
    (fun h c1 h1 => OB.bind e rest h h1)

set_option linter.unusedSectionVars false in
theorem chkB_sound_bindCall 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
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
    (ih_chkB_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c rest) (chkB A I fs out rest k c))
    : Supports (OB A I out k c (.bindCall (τ := zi_τ) f args he hp hr rest : Block D V l Γ Λ Λ')) (chkB A I fs out (.bindCall (τ := zi_τ) f args he hp hr rest : Block D V l Γ Λ Λ') k c) :=
  by
  simp only [chkB]
  exact supports_condDrop
    (fun _ => ih_chkB_sound_rest k _ hk (resultContext_bounded (afterCall_bounded hc) _))
    (fun h c1 h1 => by
      simp only [Bool.and_eq_true] at h
      exact OB.bindCall f args he hp hr rest h.1 h.2 h1)

set_option linter.unusedSectionVars false in
theorem chkB_sound_bindCallInd 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
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
    (ih_chkB_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c rest) (chkB A I fs out rest k c))
    : Supports (OB A I out k c (.bindCallInd (n := zi_n) (τ := zi_τ) p args he hp hr rest : Block D V l Γ Λ Λ')) (chkB A I fs out (.bindCallInd (n := zi_n) (τ := zi_τ) p args he hp hr rest : Block D V l Γ Λ Λ') k c) :=
  by
  simp only [chkB]
  exact supports_condDrop
    (fun _ => ih_chkB_sound_rest k _ hk (resultContextB_bounded (afterCall_bounded hc) _))
    (fun h c1 h1 => by
      simp only [Bool.and_eq_true] at h
      exact OB.bindCallInd p args he hp hr rest _ _ (sigCompatB_sound hvoll h.1.2) h.1.1.1 h.1.1.2 h.2 h1)

set_option linter.unusedSectionVars false in
theorem chkB_sound_bindCallElse 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
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
    (ih_chkB_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c rest) (chkB A I fs out rest k c))
    (ih_chkE_sound_err : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → chkE A I fs out err k c = true → OE A I out k c err)
    : Supports (OB A I out k c (.bindCallElse (τ := zi_τ) f args he hp hr err rest : Block D V l Γ Λ Λ')) (chkB A I fs out (.bindCallElse (τ := zi_τ) f args he hp hr err rest : Block D V l Γ Λ Λ') k c) :=
  by
  simp only [chkB]
  exact supports_condDrop
    (fun _ => ih_chkB_sound_rest k _ hk (resultContext_bounded (afterCall_bounded hc) _))
    (fun h c1 h1 => by
      simp only [Bool.and_eq_true] at h
      exact OB.bindCallElse f args he hp hr err rest h.1.1 h.1.2
        (ih_chkE_sound_err k _ hk (Context.bindNone_bounded (afterCall_bounded hc)) h.2) h1)

set_option linter.unusedSectionVars false in
theorem chkB_sound_bindAxiom 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
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
    (ih_chkB_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c rest) (chkB A I fs out rest k c))
    : Supports (OB A I out k c (.bindAxiom (τ := zi_τ) a args he hw hg hd hgd rest : Block D V l Γ Λ Λ')) (chkB A I fs out (.bindAxiom (τ := zi_τ) a args he hw hg hd hgd rest : Block D V l Γ Λ Λ') k c) :=
  by
  simp only [chkB]
  exact supports_condDrop (fun _ => ih_chkB_sound_rest k _ hk (Context.bindNone_bounded hc))
    (fun h c1 h1 => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact OB.bindAxiom a args he hw hg hd hgd rest h.1 h.2 h1)

set_option linter.unusedSectionVars false in
theorem chkB_sound_bindAxiomElse 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
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
    (ih_chkB_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c rest) (chkB A I fs out rest k c))
    (ih_chkE_sound_err : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → chkE A I fs out err k c = true → OE A I out k c err)
    : Supports (OB A I out k c (.bindAxiomElse (τ := zi_τ) a args he hr hw hg hd hgd err rest : Block D V l Γ Λ Λ')) (chkB A I fs out (.bindAxiomElse (τ := zi_τ) a args he hr hw hg hd hgd err rest : Block D V l Γ Λ Λ') k c) :=
  by
  simp only [chkB]
  exact supports_condDrop (fun _ => ih_chkB_sound_rest k _ hk (Context.bindNone_bounded hc))
    (fun h c1 h1 => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact OB.bindAxiomElse a args he hr hw hg hd hgd err rest h.1.1 h.1.2
        (ih_chkE_sound_err k _ hk (Context.bindNone_bounded hc) h.2) h1)

end Sound
end Gabbro.Grammatik.ArenaOwnership.Body
