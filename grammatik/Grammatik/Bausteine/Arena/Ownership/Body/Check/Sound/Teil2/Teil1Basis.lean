module

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
theorem chkS_sound_assignSlot 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (t)
    (f)
    (i)
    (e)
    (hw)
    (hL)
    (k : Context)
    (c : Context)
    (zzh1 : k.bounded)
    (hc : c.bounded)
    : Supports (OS A I out k c (.assignSlot t f i e hw hL : Stmt D V l Γ Λ _)) (chkS A I fs out (.assignSlot t f i e hw hL : Stmt D V l Γ Λ _) k c) :=
  by
  simp only [chkS]
  exact supports_if (fun h => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact OS.assignSlot t f i e hw hL h.1.1.1 h.1.1.2 h.1.2 h.2) hc

set_option linter.unusedSectionVars false in
theorem chkS_sound_assignThru 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_n}
    (p)
    (t)
    (ht)
    (f)
    (i)
    (e)
    (hw)
    (hL)
    (k : Context)
    (c : Context)
    (zzh1 : k.bounded)
    (hc : c.bounded)
    : Supports (OS A I out k c (.assignThru (n := zi_n) (read := zi_read) (space := zi_space) p t ht f i e hw hL : Stmt D V l Γ Λ _)) (chkS A I fs out (.assignThru (n := zi_n) (read := zi_read) (space := zi_space) p t ht f i e hw hL : Stmt D V l Γ Λ _) k c) :=
  by
  simp only [chkS]
  exact supports_if (fun h => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact OS.assignThru p t ht f i e hw hL h.1.1.1.1 h.1.1.1.2 h.1.1.2 h.1.2 h.2) hc

set_option linter.unusedSectionVars false in
theorem chkS_sound_assignThruOwn
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_n}
    (p)
    (t)
    (ht)
    (f)
    (i)
    (e)
    (m)
    (s)
    (ho)
    (he)
    (hg)
    (hw)
    (hL)
    (k : Context)
    (c : Context)
    (zzh1 : k.bounded)
    (hc : c.bounded)
    : Supports (OS A I out k c (.assignThruOwn (n := zi_n) (read := zi_read) (space := zi_space) (o := zi_eig) p t ht f i e m s ho he hg hw hL : Stmt D V l Γ Λ _)) (chkS A I fs out (.assignThruOwn (n := zi_n) (read := zi_read) (space := zi_space) (o := zi_eig) p t ht f i e m s ho he hg hw hL : Stmt D V l Γ Λ _) k c) :=
  by
  simp only [chkS]
  exact supports_if (fun h => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact OS.assignThruOwn p t ht f i e m s ho he hg hw hL h.1.1.1.1 h.1.1.1.2 h.1.1.2 h.1.2 h.2) hc

set_option linter.unusedSectionVars false in
theorem chkS_sound_assignGlob 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (g)
    (e)
    (hw)
    (hL)
    (k : Context)
    (c : Context)
    (zzh1 : k.bounded)
    (hc : c.bounded)
    : Supports (OS A I out k c (.assignGlob g e hw hL : Stmt D V l Γ Λ _)) (chkS A I fs out (.assignGlob g e hw hL : Stmt D V l Γ Λ _) k c) :=
  by
  simp only [chkS]
  exact supports_if (fun h => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact OS.assignGlob g e hw hL h.1 h.2) hc

set_option linter.unusedSectionVars false in
theorem chkS_sound_putBytes 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_lo}
    {zi_hi}
    (t)
    (f)
    (hf)
    (n)
    (i)
    (hlo)
    (hhi)
    (e)
    (hw)
    (hL)
    (k : Context)
    (c : Context)
    (zzh1 : k.bounded)
    (hc : c.bounded)
    : Supports (OS A I out k c (.putBytes (lo := zi_lo) (hi := zi_hi) t f hf n i hlo hhi e hw hL : Stmt D V l Γ Λ _)) (chkS A I fs out (.putBytes (lo := zi_lo) (hi := zi_hi) t f hf n i hlo hhi e hw hL : Stmt D V l Γ Λ _) k c) :=
  by
  simp only [chkS]
  exact supports_if (fun h => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact OS.putBytes t f hf n i hlo hhi e hw hL h.1.1 h.1.2 h.2) hc

set_option linter.unusedSectionVars false in
theorem chkS_sound_shift 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_lo}
    {zi_hi}
    (t)
    (f)
    (hτ)
    (i)
    (von)
    (nach)
    (hn)
    (he)
    (hw)
    (hL)
    (k : Context)
    (c : Context)
    (zzh1 : k.bounded)
    (hc : c.bounded)
    : Supports (OS A I out k c (.shift (lo := zi_lo) (hi := zi_hi) t f hτ i von nach hn he hw hL : Stmt D V l Γ Λ _)) (chkS A I fs out (.shift (lo := zi_lo) (hi := zi_hi) t f hτ i von nach hn he hw hL : Stmt D V l Γ Λ _) k c) :=
  by
  simp only [chkS]
  exact supports_if (fun h => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact OS.shift t f hτ i von nach hn he hw hL h.1.1 h.1.2 h.2) hc

set_option linter.unusedSectionVars false in
theorem chkS_sound_ite 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (cond)
    (t)
    (e)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (ih_chkB_sound_t : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c t) (chkB A I fs out t k c))
    (ih_chkB_sound_e : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c e) (chkB A I fs out e k c))
    : Supports (OS A I out k c (.ite cond t e : Stmt D V l Γ Λ Λ')) (chkS A I fs out (.ite cond t e : Stmt D V l Γ Λ Λ') k c) :=
  by
  simp only [chkS]
  split
  · rename_i hcond
    exact supports_join (ih_chkB_sound_t k c hk hc) (ih_chkB_sound_e k c hk hc)
      (fun x y z hx hy wx wy => OS.ite cond t e hcond (OB.weaken t hx wx) (OB.weaken e hy wy))
  · trivial

set_option linter.unusedSectionVars false in
theorem chkS_sound_onOption 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_n}
    (o)
    (p)
    (a)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (ih_chkB_sound_p : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c p) (chkB A I fs out p k c))
    (ih_chkB_sound_a : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OB A I out k c a) (chkB A I fs out a k c))
    : Supports (OS A I out k c (.onOption (n := zi_n) o p a : Stmt D V l Γ Λ Λ')) (chkS A I fs out (.onOption (n := zi_n) o p a : Stmt D V l Γ Λ Λ') k c) :=
  by
  simp only [chkS]
  split
  · rename_i ho
    exact supports_join (supports_drop (ih_chkB_sound_p k (c.bind none) hk (Context.bindNone_bounded hc)))
      (ih_chkB_sound_a k c hk hc)
      (fun x y z hx hy wx wy => by
        obtain ⟨c1, hp1, rfl⟩ := hx
        exact OS.onOption o p a ho hp1 wx (OB.weaken a hy wy))
  · trivial

set_option linter.unusedSectionVars false in
theorem chkS_sound_onTag 
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_cs}
    (v)
    (arms)
    (k : Context)
    (c : Context)
    (hk : k.bounded)
    (hc : c.bounded)
    (ih_chkArms_sound_arms : ∀ (k : Context), ∀ (c : Context), k.bounded → c.bounded → Supports (OArms A I out k c arms) (chkArms A I fs out arms k c))
    : Supports (OS A I out k c (.onTag (cs := zi_cs) v arms : Stmt D V l Γ Λ Λ')) (chkS A I fs out (.onTag (cs := zi_cs) v arms : Stmt D V l Γ Λ Λ') k c) :=
  by
  simp only [chkS]
  split
  · rename_i hv
    exact supports_mono (fun z hz => OS.onTag v arms hv hz) (ih_chkArms_sound_arms k c hk hc)
  · trivial


end Sound
end Gabbro.Grammatik.ArenaOwnership.Body
