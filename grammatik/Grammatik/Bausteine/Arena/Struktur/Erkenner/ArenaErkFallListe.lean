/-
  File:      Grammatik/ArenaErkFallListe.lean
  Subject:   THE CASES OF THE RECOGNIZER'S SOUNDNESS PROOF, part 2: the list moves (`push`, `pop`, `unlink`, `kopf`,
             `nach`). Each case applies the executed-form theorem of `ArenaLinkForm.lean`; its hypotheses (a live slot in
             neither structure, a member, a non-empty list) are exactly what the abstract state says. The tree is
             untouched (the frame of the executed form and `Dekl.getrennt`), and the two structures stay disjoint
             (the slot that joins the list was in neither, the slot that leaves it is no tree member either).
-/
import Grammatik.Bausteine.Arena.Struktur.Erkenner.ArenaErkFallAlloc

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

variable {D : Deklaration}

/-- The head is a member when the list is non-empty. -/
theorem kopf_auf {A : FreiForm D} {L : LinkFeld A} {G : LinkKopf A} {σ : World D} (hl : ListOk A L G σ)
    (hne : G.st σ < D.count A.tab) : Auf (D.count A.tab) (L.wert σ) (G.st σ) (G.st σ) := by
  obtain ⟨Ls, hk, -, -⟩ := hl
  exact auf_kopf hne ⟨Ls, hk⟩

section Faelle
variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {A : FreiForm D} (K : Dekl A) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

/-- A move that writes only the list's own words leaves the tree alone. -/
theorem Dekl.GlB.liste {d : ListDekl A} (hd : K.liste = some d) {fs : List (D.Feld A.tab)} {gs : List D.Glob}
    {σ σ' : World D} (hr : LinkRahmen A fs gs σ σ') (hf : fs ⊆ [d.L.f]) (hg : gs ⊆ [d.G.g]) : Dekl.GlB K σ σ' :=
  Dekl.GlB.rahmen hr (fun b hb => by
    obtain ⟨h1, h2, h3⟩ := K.getrennt d b hd hb
    refine ⟨fun e => h1 ?_, fun e => h2 ?_, fun e => h3 ?_⟩
    · have := hf e; simp at this; exact this.symm
    · have := hf e; simp at this; exact this.symm
    · have := hg e; simp at this; exact this.symm)

theorem fall_push {a a' : Abs} (d : ListDekl A) (hd : K.liste = some d)
    (x : Var Γ (Ty.index (D.count A.tab))) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt d.G.g = true) (hLG : gdarf D d.G.g Λ) (rest : Block D V l Γ Λ Λ')
    (hx : a x.pos = .frei) (ih : Folgt K O passes R (a.set x.pos .liste) rest a') :
    Folgt K O passes R a (Block.linkPush d.L d.G x hwT hLT hwG hLG rest) a' := by
  intro σ ρ hS hP
  obtain ⟨hlebt, hnotL, hnotB⟩ := hP.1 x hx
  have hl : ListOk A d.L d.G σ := (Dekl.LOk_some hd σ).mp hS.2.1
  have hnot : ¬ Auf (D.count A.tab) (d.L.wert σ) (d.G.st σ) (ρ.get x).n :=
    fun h => hnotL ((Dekl.InL_some hd σ _).mpr h)
  obtain ⟨σ', he, hrm, hl', hok', hlebt', hg, hli, hvor, hnach⟩ :=
    liste_push_zug O passes R d.L d.G x hwT hLT hwG hLG rest σ ρ hl hS.1 hlebt hnot
  rw [he]
  have hGB : Dekl.GlB K σ σ' := Dekl.GlB.liste K hd hrm (by simp) (by simp)
  have hOk : K.Ok σ' := by
    refine ⟨hok', (Dekl.LOk_some hd σ').mpr hl',
      hGB.bok (fun j hj => (hlebt' j).mpr (Dekl.InB.lebt hS.2.2.1 hj)) hS.2.2.1, ?_⟩
    rintro j ⟨hjL, hjB⟩
    rcases hvor j ((Dekl.InL_some hd σ' j).mp hjL) with rfl | hm
    · exact hnotB ((hGB.inB _).mp hjB)
    · exact hS.2.2.2 j ⟨(Dekl.InL_some hd σ j).mpr hm, (hGB.inB _).mp hjB⟩
  refine ih σ' ρ hOk (Passt.wechsel K hP (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_))
  · rcases Abs.set_eq hy with ⟨-, h⟩ | ⟨hyx, hy'⟩
    · cases h
    · obtain ⟨hly, hnl, hnb⟩ := hP.1 y hy'
      have hne : (ρ.get y).n ≠ (ρ.get x).n := hP.2.2.2 y x hy' hx hyx
      refine ⟨hy', (hlebt' _).mpr hly, fun hm => ?_, fun hm => hnb ((hGB.inB _).mp hm)⟩
      rcases hvor _ ((Dekl.InL_some hd σ' _).mp hm) with e | hm'
      · exact hne e
      · exact hnl ((Dekl.InL_some hd σ _).mpr hm')
  · rcases Abs.set_eq hy with ⟨hyx, -⟩ | ⟨-, hy'⟩
    · have := Var.pos_inj y x hyx
      subst this
      have hne : (ρ.get y).n < D.count A.tab := by
        have := hlebt.2.1; have := A.stand_le σ; omega
      have h0 := kopf_auf hl' (by rw [hg]; exact hne)
      rw [Dekl.InL_some hd]
      rw [← hg]; exact h0
    · exact (Dekl.InL_some hd σ' _).mpr (hnach _ ((Dekl.InL_some hd σ _).mp (hP.2.1 y hy')))
  · rcases Abs.set_eq hy with ⟨-, h⟩ | ⟨-, hy'⟩
    · cases h
    · exact (hGB.inB _).mpr (hP.2.2.1 y hy')

theorem fall_pop {a a'' : Abs} (d : ListDekl A) (hd : K.liste = some d)
    (hwG : V.gschreibt d.G.g = true) (hLG : gdarf D d.G.g Λ) (hLT : darf D A.tab Λ) (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hv : Rein voll)
    (ih : Folgt K O passes R ((a.forget .liste).ext .frei) rest a'') :
    Folgt K O passes R a (Block.linkPop d.L d.G hwG hLG hLT voll rest) a''.tail := by
  intro σ ρ hS hP
  have hl : ListOk A d.L d.G σ := (Dekl.LOk_some hd σ).mp hS.2.1
  by_cases hne : d.G.st σ < D.count A.tab
  · obtain ⟨σ', k, he, hrm, hkn, hl', hok', hlebt, hnot, hlebtk, hg, hsub⟩ :=
      liste_pop_zug O passes R d.L d.G hwG hLG hLT voll rest σ ρ hl hS.1 hne
    rw [he]
    apply Post.schrumpf
    have hGB : Dekl.GlB K σ σ' := Dekl.GlB.liste K hd hrm (by simp) (by simp)
    have hhead : K.InL σ k.n := (Dekl.InL_some hd σ _).mpr (by rw [hkn]; exact kopf_auf hl hne)
    have hnotB : ¬ K.InB σ k.n := fun hb => hS.2.2.2 _ ⟨hhead, hb⟩
    have hOk : K.Ok σ' := by
      refine ⟨hok', (Dekl.LOk_some hd σ').mpr hl',
        hGB.bok (fun j hj => (hlebt j).mpr (Dekl.InB.lebt hS.2.2.1 hj)) hS.2.2.1, ?_⟩
      rintro j ⟨hjL, hjB⟩
      exact hS.2.2.2 j ⟨(Dekl.InL_some hd σ j).mpr (hsub _ ((Dekl.InL_some hd σ' j).mp hjL)),
        (hGB.inB _).mp hjB⟩
    have hP0 : Passt K (a.forget .liste) σ' ρ := by
      refine Passt.wechsel K hP (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_)
      · obtain ⟨hy', -⟩ := Abs.forget_eq hy (by decide)
        obtain ⟨hly, hnl, hnb⟩ := hP.1 y hy'
        exact ⟨hy', (hlebt _).mpr hly, fun hm => hnl ((Dekl.InL_some hd σ _).mpr
          (hsub _ ((Dekl.InL_some hd σ' _).mp hm))), fun hm => hnb ((hGB.inB _).mp hm)⟩
      · exact absurd rfl (Abs.forget_eq hy (by decide)).2
      · exact (hGB.inB _).mpr (hP.2.2.1 y (Abs.forget_eq hy (by decide)).1)
    refine ih σ' (.cons k ρ) hOk (Passt.ext_frei K k hP0 hlebtk ?_ (fun hm => hnotB ((hGB.inB _).mp hm)) ?_)
    · exact fun hm => hnot ((Dekl.InL_some hd σ' _).mp hm)
    · intro y hy e
      have hy' := (Abs.forget_eq hy (by decide)).1
      exact (hP.1 y hy').2.1 (by rw [e]; exact hhead)
  · rw [linkPop_voll O passes R d.L d.G hwG hLG hLT voll rest σ ρ hne]
    exact Rein.post K O passes R hv _ _ (Dekl.Ok.lese K _ _ hS)

theorem fall_unlink {a a'' : Abs} (d : ListDekl A) (hd : K.liste = some d)
    (p : Var Γ (Ty.index (D.count A.tab))) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (hp : a p.pos = .liste) (hv : Rein voll)
    (ih : Folgt K O passes R ((a.forget .liste).ext .frei) rest a'') :
    Folgt K O passes R a (Block.linkUnlink d.L p hwT hLT voll rest) a''.tail := by
  intro σ ρ hS hP
  have hl : ListOk A d.L d.G σ := (Dekl.LOk_some hd σ).mp hS.2.1
  by_cases hi : d.L.wert σ (ρ.get p).n < D.count A.tab
  · have hpa := (Dekl.InL_some hd σ _).mp (hP.2.1 p hp)
    obtain ⟨σ', k, he, hrm, hkn, hl', hok', hlebt, hnot, hlebtk, hnp, hsub⟩ :=
      liste_unlink_zug O passes R d.L d.G p hwT hLT voll rest σ ρ hl hS.1 hpa hi
    rw [he]
    apply Post.schrumpf
    have hGB : Dekl.GlB K σ σ' := Dekl.GlB.liste K hd hrm (by simp) (by simp)
    have hmem : K.InL σ k.n := (Dekl.InL_some hd σ _).mpr (by rw [hkn]; exact auf_nach hpa hi)
    have hnotB : ¬ K.InB σ k.n := fun hb => hS.2.2.2 _ ⟨hmem, hb⟩
    have hOk : K.Ok σ' := by
      refine ⟨hok', (Dekl.LOk_some hd σ').mpr hl',
        hGB.bok (fun j hj => (hlebt j).mpr (Dekl.InB.lebt hS.2.2.1 hj)) hS.2.2.1, ?_⟩
      rintro j ⟨hjL, hjB⟩
      exact hS.2.2.2 j ⟨(Dekl.InL_some hd σ j).mpr (hsub _ ((Dekl.InL_some hd σ' j).mp hjL)),
        (hGB.inB _).mp hjB⟩
    have hP0 : Passt K (a.forget .liste) σ' ρ := by
      refine Passt.wechsel K hP (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_)
      · obtain ⟨hy', -⟩ := Abs.forget_eq hy (by decide)
        obtain ⟨hly, hnl, hnb⟩ := hP.1 y hy'
        exact ⟨hy', (hlebt _).mpr hly, fun hm => hnl ((Dekl.InL_some hd σ _).mpr
          (hsub _ ((Dekl.InL_some hd σ' _).mp hm))), fun hm => hnb ((hGB.inB _).mp hm)⟩
      · exact absurd rfl (Abs.forget_eq hy (by decide)).2
      · exact (hGB.inB _).mpr (hP.2.2.1 y (Abs.forget_eq hy (by decide)).1)
    refine ih σ' (.cons k ρ) hOk (Passt.ext_frei K k hP0 hlebtk ?_ (fun hm => hnotB ((hGB.inB _).mp hm)) ?_)
    · exact fun hm => hnot ((Dekl.InL_some hd σ' _).mp hm)
    · intro y hy e
      have hy' := (Abs.forget_eq hy (by decide)).1
      exact (hP.1 y hy').2.1 (by rw [e]; exact hmem)
  · rw [linkUnlink_voll O passes R d.L p hwT hLT voll rest σ ρ hi]
    exact Rein.post K O passes R hv _ _ (Dekl.Ok.lese K _ _ hS)

theorem fall_kopf {a a'' : Abs} (d : ListDekl A) (hd : K.liste = some d)
    (hLG : gdarf D d.G.g Λ) (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hv : Rein voll)
    (ih : Folgt K O passes R (a.ext .liste) rest a'') :
    Folgt K O passes R a (Block.linkKopfBind d.G hLG voll rest) a''.tail := by
  intro σ ρ hS hP
  have hl : ListOk A d.L d.G σ := (Dekl.LOk_some hd σ).mp hS.2.1
  by_cases hne : d.G.st σ < D.count A.tab
  · obtain ⟨k, he, hkn⟩ := linkKopfBind_ausfuehren O passes R d.G hLG voll rest σ ρ hne
    rw [he]
    apply Post.schrumpf
    have hgl : Dekl.Gleich K σ (σ.lese Λ [Sum.inr d.G.g]) := Dekl.Gleich.lese σ Λ _
    exact ih _ (.cons k ρ) (hgl.ok hS) (Passt.ext_liste K k (hgl.passt hP)
      ((hgl.l.inL _).mpr ((Dekl.InL_some hd σ _).mpr (by rw [hkn]; exact kopf_auf hl hne))))
  · rw [linkKopfBind_voll O passes R d.G hLG voll rest σ ρ hne]
    exact Rein.post K O passes R hv _ _ (Dekl.Ok.lese K _ _ hS)

theorem fall_nach {a a'' : Abs} (d : ListDekl A) (hd : K.liste = some d)
    (p : Var Γ (Ty.index (D.count A.tab))) (hLT : darf D A.tab Λ) (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hp : a p.pos = .liste) (hv : Rein voll)
    (ih : Folgt K O passes R (a.ext .liste) rest a'') :
    Folgt K O passes R a (Block.linkNachBind d.L p hLT voll rest) a''.tail := by
  intro σ ρ hS hP
  by_cases hn : d.L.wert σ (ρ.get p).n < D.count A.tab
  · obtain ⟨k, he, hkn⟩ := linkNachBind_ausfuehren O passes R d.L p hLT voll rest σ ρ hn
    rw [he]
    apply Post.schrumpf
    have hgl : Dekl.Gleich K σ (σ.lese Λ [Sum.inl A.tab]) := Dekl.Gleich.lese σ Λ _
    exact ih _ (.cons k ρ) (hgl.ok hS) (Passt.ext_liste K k (hgl.passt hP)
      ((hgl.l.inL _).mpr ((Dekl.InL_some hd σ _).mpr
        (by rw [hkn]; exact auf_nach ((Dekl.InL_some hd σ _).mp (hP.2.1 p hp)) hn))))
  · rw [linkNachBind_voll O passes R d.L p hLT voll rest σ ρ hn]
    exact Rein.post K O passes R hv _ _ (Dekl.Ok.lese K _ _ hS)

end Faelle

end Gabbro.Grammatik
