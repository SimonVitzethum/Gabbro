module
public import Grammatik.Bausteine.Arena.Ownership.Body.Check.Sound.Teil2.Teil1Basis

public import Grammatik.Bausteine.Arena.Ownership.Body.Check.Lemmas
public import Grammatik.Bausteine.Arena.Ownership.Body.Check.Sound.Teil1

@[expose] public section

namespace Gabbro.Grammatik.ArenaOwnership.Body
open Source
variable {D : Deklaration}
section Sound
variable {A : FreiForm D} {I : Interfaces A} {fs : List D.Fn} {V : Vertrag D} {out : Flow.Output A V.erg}
variable (hvoll : ∀ f, f ∈ fs)
include hvoll
set_option linter.unusedSectionVars false in
theorem chkS_sound_onWhy 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_n}
    (r)
    (arms)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (ih_chkGrund_sound_arms : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OGrund A I out k c arms) (chkGrund A I fs out arms k c))
    : Supports (OS A I out k c (.onWhy (n := zi_n) r arms : Stmt D V l Γ Λ Λ')) (chkS A I fs out (.onWhy (n := zi_n) r arms : Stmt D V l Γ Λ Λ') k c) :=
  by
  simp only [chkS]
  split
  · rename_i hr
    exact supports_mono (fun z hz => OS.onWhy r arms hr hz) (ih_chkGrund_sound_arms k c hk hc)
  · trivial

set_option linter.unusedSectionVars false in
theorem chkS_sound_call 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (f)
    (args)
    (hp)
    (hr)
    (k : Context)
    (c : Context)
    (zzh1 : k.bounded)
    (hc : c.bounded)
    : Supports (OS A I out k c (.call f args hp hr : Stmt D V l Γ Λ _)) (chkS A I fs out (.call f args hp hr : Stmt D V l Γ Λ _) k c) :=
  by
  simp only [chkS]
  exact supports_if (fun h => by
    simp only [Bool.and_eq_true] at h
    exact OS.call f args hp hr h.1 h.2) (dropContext_bounded (afterCall_bounded hc) _)

set_option linter.unusedSectionVars false in
theorem chkS_sound_traverse 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (t)
    (inv)
    (body)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (ih_chkB_sound_body : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c body) (chkB A I fs out body k c))
    : Supports (OS A I out k c (.traverse t inv body : Stmt D V l Γ Λ _)) (chkS A I fs out (.traverse t inv body : Stmt D V l Γ Λ _) k c) :=
  by
  simp only [chkS]
  have hkk := loopCtx_bounded hc (assignsB body)
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain ⟨x, ⟨c1, hb1, rfl⟩, hw⟩ := back_sound hkk
      (supports_drop (ih_chkB_sound_body _ _ hkk (Context.bindNone_bounded hkk))) h.2
    exact ⟨OS.traverse t inv body (loopCtx_weaker hc _) h.1 hb1 hw, hkk⟩
  · trivial

set_option linter.unusedSectionVars false in
theorem chkS_sound_retry 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (n)
    (bis)
    (body)
    (u)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (ih_chkB_sound_body : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c body) (chkB A I fs out body k c))
    (ih_chkB_sound_u : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c u) (chkB A I fs out u k c))
    : Supports (OS A I out k c (.retry n bis body u : Stmt D V l Γ Λ _)) (chkS A I fs out (.retry n bis body u : Stmt D V l Γ Λ _) k c) :=
  by
  simp only [chkS]
  have hkk := loopCtx_bounded hc (assignsB body ++ assignsB u)
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain ⟨c1, hb1, hw1⟩ := back_sound hkk (ih_chkB_sound_body _ _ hkk hkk) h.1.2
    obtain ⟨cu, hbu, hwu⟩ := back_sound hkk (ih_chkB_sound_u k _ hk hkk) h.2
    exact ⟨OS.retry n bis body u (loopCtx_weaker hc _) h.1.1 hb1 hw1 (OB.weaken u hbu hwu), hkk⟩
  · trivial

set_option linter.unusedSectionVars false in
theorem chkS_sound_forever 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (a)
    (inv)
    (body)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (ih_chkB_sound_body : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c body) (chkB A I fs out body k c))
    : Supports (OS A I out k c (.forever a inv body : Stmt D V l Γ Λ _)) (chkS A I fs out (.forever a inv body : Stmt D V l Γ Λ _) k c) :=
  by
  simp only [chkS]
  have hkk := loopCtx_bounded hc (assignsB body)
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain ⟨c1, hb1, hw1⟩ := back_sound hkk (ih_chkB_sound_body _ _ hkk hkk) h.2
    exact ⟨OS.forever a inv body (loopCtx_weaker hc _) h.1 hb1 hw1, hkk⟩
  · trivial

set_option linter.unusedSectionVars false in
theorem chkS_sound_axiomCall 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (a)
    (args)
    (hres)
    (hw)
    (hg)
    (hd)
    (hgd)
    (k : Context)
    (c : Context)
    (zzh1 : k.bounded)
    (hc : c.bounded)
    : Supports (OS A I out k c (.axiomCall a args hres hw hg hd hgd : Stmt D V l Γ Λ _)) (chkS A I fs out (.axiomCall a args hres hw hg hd hgd : Stmt D V l Γ Λ _) k c) :=
  by
  simp only [chkS]
  exact supports_if (fun h => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact OS.axiomCall a args hres hw hg hd hgd h.1 h.2) hc

set_option linter.unusedSectionVars false in
theorem chkS_sound_publish 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (g)
    (e)
    (payload)
    (hp)
    (hw)
    (hL)
    (k : Context)
    (c : Context)
    (zzh1 : k.bounded)
    (hc : c.bounded)
    : Supports (OS A I out k c (.publish g e payload hp hw hL : Stmt D V l Γ Λ _)) (chkS A I fs out (.publish g e payload hp hw hL : Stmt D V l Γ Λ _) k c) :=
  by
  simp only [chkS]
  exact supports_if (fun h => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact OS.publish g e payload hp hw hL h.1 h.2) hc

set_option linter.unusedSectionVars false in
theorem chkS_sound_assignSlotRef 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_n}
    (r)
    (t)
    (ht)
    (ho)
    (f)
    (e)
    (hw)
    (hL)
    (k : Context)
    (c : Context)
    (zzh1 : k.bounded)
    (hc : c.bounded)
    : Supports (OS A I out k c (.assignSlotRef (n := zi_n) r t ht ho f e hw hL : Stmt D V l Γ Λ _)) (chkS A I fs out (.assignSlotRef (n := zi_n) r t ht ho f e hw hL : Stmt D V l Γ Λ _) k c) :=
  by
  simp only [chkS]
  exact supports_if (fun h => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact OS.assignSlotRef r t ht ho f e hw hL h.1.1 h.1.2 h.2) hc

end Sound
end Gabbro.Grammatik.ArenaOwnership.Body
