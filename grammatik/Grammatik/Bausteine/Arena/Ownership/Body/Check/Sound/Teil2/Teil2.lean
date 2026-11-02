module
public import Grammatik.Bausteine.Arena.Ownership.Body.Check.Sound.Teil2.Teil2Basis
import all Grammatik.Bausteine.Arena.Ownership.Body.Check.Sound.Teil2.Teil2Basis

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
theorem chkB_sound_bindCallIndElse
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
    (err)
    (rest)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (ih_chkB_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c rest) (chkB A I fs out rest k c))
    (ih_chkE_sound_err : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → chkE A I fs out err k c = true → OE A I out k c err)
    : Supports (OB A I out k c (.bindCallIndElse (n := zi_n) (τ := zi_τ) p args he hp hr err rest : Block D V l Γ Λ Λ')) (chkB A I fs out (.bindCallIndElse (n := zi_n) (τ := zi_τ) p args he hp hr err rest : Block D V l Γ Λ Λ') k c) :=
  by
  simp only [chkB]
  exact supports_condDrop
    (fun _ => ih_chkB_sound_rest k _ hk (resultContextB_bounded (afterCall_bounded hc) _))
    (fun h c1 h1 => by
      simp only [Bool.and_eq_true] at h
      exact OB.bindCallIndElse p args he hp hr err rest _ _ (sigCompatB_sound hvoll h.1.1.2) h.1.1.1.1
        h.1.1.1.2 h.1.2
        (ih_chkE_sound_err k _ hk (Context.bindNone_bounded (afterCall_bounded hc)) h.2) h1)


set_option linter.unusedSectionVars false in
theorem chkB_sound_regRead 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (r)
    (hk')
    (rest)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (ih_chkB_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c rest) (chkB A I fs out rest k c))
    : Supports (OB A I out k c (.regRead r hk' rest : Block D V l Γ Λ Λ')) (chkB A I fs out (.regRead r hk' rest : Block D V l Γ Λ Λ') k c) :=
  by
  simp only [chkB]
  exact supports_mono (fun x ⟨c1, h1, hx⟩ => hx ▸ OB.regRead r hk' rest h1)
    (supports_drop (ih_chkB_sound_rest k _ hk (Context.bindNone_bounded hc)))

set_option linter.unusedSectionVars false in
theorem chkB_sound_regReadElse 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (r)
    (hk')
    (zusage)
    (sonst)
    (rest)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (ih_chkB_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c rest) (chkB A I fs out rest k c))
    (ih_chkE_sound_sonst : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → chkE A I fs out sonst k c = true → OE A I out k c sonst)
    : Supports (OB A I out k c (.regReadElse r hk' zusage sonst rest : Block D V l Γ Λ Λ')) (chkB A I fs out (.regReadElse r hk' zusage sonst rest : Block D V l Γ Λ Λ') k c) :=
  by
  simp only [chkB]
  exact supports_condDrop (fun _ => ih_chkB_sound_rest k _ hk (Context.bindNone_bounded hc))
    (fun h c1 h1 => by
      simp only [Bool.and_eq_true] at h
      exact OB.regReadElse r hk' zusage sonst rest h.1 (ih_chkE_sound_sonst k c hk hc h.2) h1)

set_option linter.unusedSectionVars false in
theorem chkB_sound_awaits 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (g)
    (payload)
    (hp)
    (hL)
    (ha)
    (rest)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (ih_chkB_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c rest) (chkB A I fs out rest k c))
    : Supports (OB A I out k c (.awaits g payload hp hL ha rest : Block D V l Γ Λ Λ')) (chkB A I fs out (.awaits g payload hp hL ha rest : Block D V l Γ Λ Λ') k c) :=
  by
  simp only [chkB]
  exact supports_mono (fun x ⟨c1, h1, hx⟩ => hx ▸ OB.awaits g payload hp hL ha rest h1)
    (supports_drop (ih_chkB_sound_rest k _ hk (Context.bindNone_bounded hc)))

set_option linter.unusedSectionVars false in
theorem chkB_sound_exchange 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (g)
    (neu)
    (hw)
    (hL)
    (rest)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (ih_chkB_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c rest) (chkB A I fs out rest k c))
    : Supports (OB A I out k c (.exchange g neu hw hL rest : Block D V l Γ Λ Λ')) (chkB A I fs out (.exchange g neu hw hL rest : Block D V l Γ Λ Λ') k c) :=
  by
  simp only [chkB]
  exact supports_condDrop (fun _ => ih_chkB_sound_rest k _ hk (Context.bindNone_bounded hc))
    (fun h c1 h1 => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact OB.exchange g neu hw hL rest h.1 h.2 h1)

set_option linter.unusedSectionVars false in
theorem chkB_sound_narrow 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_lo}
    {zi_hi}
    (e)
    (lo')
    (hi')
    (voll)
    (rest)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (ih_chkB_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c rest) (chkB A I fs out rest k c))
    (ih_ctr1B_sound_rest : ∀ (k : Context), ∀ (c : Context), ∀ (p : Nat), k.bounded → c.bounded → Supports (fun x => ∃ (t : D.Tab) (f : D.Feld t) (i : Expr D _ _ (.index (D.count t))) (ev : Expr D _ _ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t _) (rest1 : Block D V _ _ _ _), rest = .cons (.assignSlot t f i ev hw hL) rest1 ∧ NotLink A t f ∧ checkExpression A c i = true ∧ checkExpression A c ev = true ∧ storeCheck A c t i = true ∧ ∃ (g : D.Glob) (e2 : Expr D _ _ (D.gtyp g)) (hwG : V.gschreibt g = true) (hLG : gdarf D g _) (rest2 : Block D V _ _ _ _), rest1 = .cons (.assignGlob g e2 hwG hLG) rest2 ∧ g = A.zaehl ∧ exprSucc e2 = some p ∧ OB A I out k c rest2 x) (ctr1B A I fs out rest k c p))
    (ih_lst1B_sound_rest : ∀ (k : Context), ∀ (c : Context), ∀ (p : Nat), k.bounded → c.bounded → Supports (fun x => ∃ (g : D.Glob) (e2 : Expr D _ _ (D.gtyp g)) (hwK : V.gschreibt g = true) (hLK : gdarf D g _) (rest1 : Block D V _ _ _ _), rest = .cons (.assignGlob g e2 hwK hLK) rest1 ∧ g = A.kopf ∧ exprSlotRead e2 = some ⟨A.tab, A.nxt, p⟩ ∧ ∃ (t : D.Tab) (f : D.Feld t) (i : Expr D _ _ (.index (D.count t))) (ev : Expr D _ _ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t _) (rest2 : Block D V _ _ _ _), rest1 = .cons (.assignSlot t f i ev hw hL) rest2 ∧ NotLink A t f ∧ checkExpression A c i = true ∧ checkExpression A c ev = true ∧ storeCheck A c t i = true ∧ OB A I out k c rest2 x) (lst1B A I fs out rest k c p))
    (ih_chkE_sound_voll : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → chkE A I fs out voll k c = true → OE A I out k c voll)
    : Supports (OB A I out k c (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' voll rest : Block D V l Γ Λ Λ')) (chkB A I fs out (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' voll rest : Block D V l Γ Λ Λ') k c) :=
  by
  simp only [chkB]
  refine supports_orElse ?_ ?_
  · split
    · rename_i hcv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcv
      have hvoll' := ih_chkE_sound_voll k c hk hc hcv.1
      split
      · rename_i hz
        simp only [beq_iff_eq] at hz
        exact supports_mono (fun x hx => by
          obtain ⟨c1, ⟨t, f, i, ev, hw, hL, rest1, rfl, hn, hi, hev, hs, g, e2, hwG, hLG, rest2, rfl, hg,
            he2, hob⟩, rfl⟩ := hx
          exact OB.allocCounter e lo' hi' voll t f i ev hw hL g e2 hwG hLG rest2 hz hcv.2 hn hg he2 hi hev hs
            hvoll' hob)
          (supports_drop (ih_ctr1B_sound_rest k c.bindFresh Γ.length hk (Context.bindFresh_bounded hc)))
      · split
        · rename_i _ hz
          simp only [beq_iff_eq] at hz
          exact supports_mono (fun x hx => by
            obtain ⟨c1, ⟨g, e2, hwK, hLK, rest1, rfl, hg, he2, t, f, i, ev, hw, hL, rest2, rfl, hn, hi, hev,
              hs, hob⟩, rfl⟩ := hx
            exact OB.allocList e lo' hi' voll g e2 hwK hLK t f i ev hw hL rest2 hz hcv.2 hg he2 hn hi hev hs
              hvoll' hob)
            (supports_drop (ih_lst1B_sound_rest k c.bindFresh Γ.length hk (Context.bindFresh_bounded hc)))
        · trivial
    · trivial
  · exact supports_condDrop (fun _ => ih_chkB_sound_rest k _ hk (Context.bindOrigin_bounded hc e))
      (fun h c1 h1 => by
        simp only [Bool.and_eq_true] at h
        exact OB.narrow e lo' hi' voll rest h.1 (ih_chkE_sound_voll k c hk hc h.2) h1)

set_option linter.unusedSectionVars false in
theorem chkB_sound_check 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (cond)
    (sonst)
    (rest)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (ih_chkB_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c rest) (chkB A I fs out rest k c))
    (ih_chkE_sound_sonst : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → chkE A I fs out sonst k c = true → OE A I out k c sonst)
    : Supports (OB A I out k c (.check cond sonst rest : Block D V l Γ Λ Λ')) (chkB A I fs out (.check cond sonst rest : Block D V l Γ Λ Λ') k c) :=
  by
  simp only [chkB]
  exact supports_cond (fun _ => ih_chkB_sound_rest k c hk hc)
    (fun h c1 h1 => by
      simp only [Bool.and_eq_true] at h
      exact OB.check cond sonst rest h.1 (ih_chkE_sound_sonst k c hk hc h.2) h1)

set_option linter.unusedSectionVars false in
theorem chkB_sound_float 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_l1}
    {zi_h1}
    {zi_l2}
    {zi_h2}
    (op)
    (a)
    (b)
    (lo)
    (hi)
    (rest)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (ih_chkB_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c rest) (chkB A I fs out rest k c))
    : Supports (OB A I out k c (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Block D V l Γ Λ Λ')) (chkB A I fs out (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Block D V l Γ Λ Λ') k c) :=
  by
  simp only [chkB]
  exact supports_condDrop (fun _ => ih_chkB_sound_rest k _ hk (Context.bindNone_bounded hc))
    (fun h c1 h1 => by
      simp only [Bool.and_eq_true] at h
      exact OB.float op a b lo hi rest h.1 h.2 h1)

set_option linter.unusedSectionVars false in
theorem chkB_sound_floatLit 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (q)
    (lo)
    (hi)
    (rest)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (ih_chkB_sound_rest : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c rest) (chkB A I fs out rest k c))
    : Supports (OB A I out k c (.floatLit q lo hi rest : Block D V l Γ Λ Λ')) (chkB A I fs out (.floatLit q lo hi rest : Block D V l Γ Λ Λ') k c) :=
  by
  simp only [chkB]
  exact supports_mono (fun x ⟨c1, h1, hx⟩ => hx ▸ OB.floatLit q lo hi rest h1)
    (supports_drop (ih_chkB_sound_rest k _ hk (Context.bindNone_bounded hc)))

end Sound
end Gabbro.Grammatik.ArenaOwnership.Body
