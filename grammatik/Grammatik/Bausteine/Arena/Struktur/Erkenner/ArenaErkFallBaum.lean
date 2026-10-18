/-
  File:      Grammatik/ArenaErkFallBaum.lean
  Subject:   THE CASES OF THE RECOGNIZER'S SOUNDNESS PROOF, part 3: the tree moves (`wurzelEin`, `wurzelKopf`, `kind`,
             `haengen`, `abschneiden`, `wurzelAus`). Each case applies the executed-form theorem of `ArenaBaumForm.lean` /
             `ArenaBaumFormZug.lean`. The guard of a form is either passed (the form runs, its hypotheses are the facts
             the guard decided plus what the abstract state says) or failed (the `else` branch, store-free by `Rein`).
             The list is untouched (the frame of the executed form and `Dekl.getrennt`), and the two structures stay
             disjoint (the slot that joins the tree was in neither, the slot that leaves it is no list member either).
-/
import Grammatik.Bausteine.Arena.Struktur.Erkenner.ArenaErkFallListe

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

variable {D : Deklaration}

section Faelle
variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {A : FreiForm D} (K : Dekl A) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

/-- A move that writes only the tree's own words leaves the list alone. -/
theorem Dekl.GlL.baum {b : BaumDekl A} (hb : K.baum = some b) {fs : List (D.Feld A.tab)} {gs : List D.Glob}
    {σ σ' : World D} (hr : LinkRahmen A fs gs σ σ') (hf : fs ⊆ [b.Lf.f, b.Rf.f]) (hg : gs ⊆ [b.Wz.g]) :
    Dekl.GlL K σ σ' :=
  Dekl.GlL.rahmen hr (fun d hd => by
    obtain ⟨h1, h2, h3⟩ := K.getrennt d b hd hb
    refine ⟨fun e => ?_, fun e => h3 ?_⟩
    · have := hf e; simp at this
      rcases this with h | h
      exacts [h1 h, h2 h]
    · have := hg e; simp at this; exact this)

/-! ## 1. The first node -/

theorem kern_wurzelEin {a a' : Abs} (b : BaumDekl A) (hb : K.baum = some b)
    (x : Var Γ (Ty.index (D.count A.tab))) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt b.Wz.g = true) (hLG : gdarf D b.Wz.g Λ)
    (rest : Block D V l Γ Λ Λ') (hx : a x.pos = .frei)
    (ih : Folgt K O passes R (a.set x.pos .baum) rest a')
    (σ : World D) (ρ : Env D Γ) (hS : K.Ok σ) (hP : Passt K a σ ρ) (hg : b.Wz.st σ = D.count A.tab) :
    Post K a' (execBlock O passes R (Block.wurzelSetze b.Lf b.Rf b.Wz x hwT hLT hwG hLG rest) σ ρ) := by
  obtain ⟨hlebt, hnotL, hnotB⟩ := hP.1 x hx
  obtain ⟨σ', he, hrm, hbok, hok', hlebt', hmem⟩ :=
    baum_wurzel_ein_zug O passes R b.Lf b.Rf b.Wz b.hd x hwT hLT hwG hLG rest σ ρ hS.1 hlebt
  rw [he]
  have hGL : Dekl.GlL K σ σ' := Dekl.GlL.baum K hb hrm (by simp) (by simp)
  have hleer : ∀ j, ¬ K.InB σ j := fun j h =>
    (wurzel_aus_ok (c := D.count A.tab) (l := b.Lf.wert σ) (r := b.Rf.wert σ) (Live := A.Lebt σ)).2 j (by
      have := (Dekl.InB_some hb σ j).mp h
      rwa [hg] at this)
  have hOk : K.Ok σ' := by
    refine ⟨hok', hGL.lok (fun j hj => (hlebt' j).mpr (Dekl.InL.lebt hS.2.1 hj)) hS.2.1,
      (Dekl.BOk_some hb σ').mpr hbok, ?_⟩
    rintro j ⟨hjL, hjB⟩
    have hjx := (hmem j).mp ((Dekl.InB_some hb σ' j).mp hjB)
    subst hjx
    exact hnotL ((hGL.inL _).mp hjL)
  refine ih σ' ρ hOk (Passt.wechsel K hP (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_))
  · rcases Abs.set_eq hy with ⟨-, h⟩ | ⟨hyx, hy'⟩
    · cases h
    · obtain ⟨hly, hnl, hnb⟩ := hP.1 y hy'
      have hne := hP.2.2.2 y x hy' hx hyx
      exact ⟨hy', (hlebt' _).mpr hly, fun hm => hnl ((hGL.inL _).mp hm),
        fun hm => hne ((hmem _).mp ((Dekl.InB_some hb σ' _).mp hm))⟩
  · rcases Abs.set_eq hy with ⟨-, h⟩ | ⟨-, hy'⟩
    · cases h
    · exact (hGL.inL _).mpr (hP.2.1 y hy')
  · rcases Abs.set_eq hy with ⟨hyx, -⟩ | ⟨-, hy'⟩
    · have := Var.pos_inj y x hyx
      subst this
      exact (Dekl.InB_some hb σ' _).mpr ((hmem _).mpr rfl)
    · exact absurd (hP.2.2.1 y hy') (hleer _)

theorem fall_wurzelEin {a a' : Abs} (b : BaumDekl A) (hb : K.baum = some b)
    (x : Var Γ (Ty.index (D.count A.tab))) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt b.Wz.g = true) (hLG : gdarf D b.Wz.g Λ) (voll : Endblock D V l Γ Λ)
    (rest : Block D V l Γ Λ Λ') (hx : a x.pos = .frei) (hv : Rein voll)
    (ih : Folgt K O passes R (a.set x.pos .baum) rest a') :
    Folgt K O passes R a (Block.wurzelEin b.Lf b.Rf b.Wz x hwT hLT hwG hLG voll rest) a' := by
  intro σ ρ hS hP
  simp only [Block.wurzelEin, execBlock]
  split
  · rename_i hc
    exact kern_wurzelEin O passes R K b hb x hwT hLT hwG hLG rest hx ih _ ρ (Dekl.Ok.lese K Λ _ hS)
      (Passt.lese K Λ _ hP) ((wurzelLeer_wahr b.Wz hLG _ ρ).mp hc)
  · exact Rein.post K O passes R hv _ _ (Dekl.Ok.lese K Λ _ hS)

/-! ## 2. Reading the tree -/

theorem fall_wurzelKopf {a a'' : Abs} (b : BaumDekl A) (hb : K.baum = some b)
    (hLG : gdarf D b.Wz.g Λ) (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hv : Rein voll)
    (ih : Folgt K O passes R (a.ext .baum) rest a'') :
    Folgt K O passes R a (Block.linkKopfBind b.Wz hLG voll rest) a''.tail := by
  intro σ ρ hS hP
  have hbok : BaumOk A b.Lf b.Rf b.Wz σ := (Dekl.BOk_some hb σ).mp hS.2.2.1
  by_cases hne : b.Wz.st σ < D.count A.tab
  · obtain ⟨k, he, hkn⟩ := linkKopfBind_ausfuehren O passes R b.Wz hLG voll rest σ ρ hne
    rw [he]
    apply Post.schrumpf
    have hgl : Dekl.Gleich K σ (σ.lese Λ [Sum.inr b.Wz.g]) := Dekl.Gleich.lese σ Λ _
    exact ih _ (.cons k ρ) (hgl.ok hS) (Passt.ext_baum K k (hgl.passt hP)
      ((hgl.b.inB _).mpr ((Dekl.InB_some hb σ _).mpr (by rw [hkn]; exact InBaum.wurzel hbok hne))))
  · rw [linkKopfBind_voll O passes R b.Wz hLG voll rest σ ρ hne]
    exact Rein.post K O passes R hv _ _ (Dekl.Ok.lese K _ _ hS)

theorem fall_kind {a a'' : Abs} (b : BaumDekl A) (hb : K.baum = some b)
    (C : LinkFeld A) (hC : C = b.Lf ∨ C = b.Rf) (p : Var Γ (Ty.index (D.count A.tab))) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (hp : a p.pos = .baum) (hv : Rein voll) (ih : Folgt K O passes R (a.ext .baum) rest a'') :
    Folgt K O passes R a (Block.linkNachBind C p hLT voll rest) a''.tail := by
  intro σ ρ hS hP
  by_cases hn : C.wert σ (ρ.get p).n < D.count A.tab
  · obtain ⟨k, he, hkn⟩ := linkNachBind_ausfuehren O passes R C p hLT voll rest σ ρ hn
    rw [he]
    apply Post.schrumpf
    have hgl : Dekl.Gleich K σ (σ.lese Λ [Sum.inl A.tab]) := Dekl.Gleich.lese σ Λ _
    have hpb := (Dekl.InB_some hb σ _).mp (hP.2.2.1 p hp)
    have hmem : InBaum (D.count A.tab) (b.Lf.wert σ) (b.Rf.wert σ) (b.Wz.st σ) (C.wert σ (ρ.get p).n) := by
      rcases hC with rfl | rfl
      · exact hpb.links hn
      · exact hpb.rechts hn
    exact ih _ (.cons k ρ) (hgl.ok hS) (Passt.ext_baum K k (hgl.passt hP)
      ((hgl.b.inB _).mpr ((Dekl.InB_some hb σ _).mpr (by rw [hkn]; exact hmem))))
  · rw [linkNachBind_voll O passes R C p hLT voll rest σ ρ hn]
    exact Rein.post K O passes R hv _ _ (Dekl.Ok.lese K _ _ hS)

/-! ## 3. Hanging a slot -/

/-- What follows a leaf in, from the facts the executed form leaves. -/
theorem haengen_nach {a a' : Abs} (b : BaumDekl A) (hb : K.baum = some b) (i : Var Γ (Ty.index (D.count A.tab)))
    (hx : a i.pos = .frei) {σ σ' : World D} (ρ : Env D Γ) (hS : K.Ok σ) (hP : Passt K a σ ρ)
    (hrm : LinkRahmen A [b.Lf.f, b.Rf.f] [] σ σ') (hbok : BaumOk A b.Lf b.Rf b.Wz σ') (hok' : A.FreiOk σ')
    (hlebt' : ∀ j, A.Lebt σ' j ↔ A.Lebt σ j)
    (hmem : ∀ j, InBaum (D.count A.tab) (b.Lf.wert σ') (b.Rf.wert σ') (b.Wz.st σ') j ↔
      (j = (ρ.get i).n ∨ InBaum (D.count A.tab) (b.Lf.wert σ) (b.Rf.wert σ) (b.Wz.st σ) j))
    {rest : Block D V l Γ Λ Λ'} (ih : Folgt K O passes R (a.set i.pos .baum) rest a') :
    Post K a' (execBlock O passes R rest σ' ρ) := by
  obtain ⟨hlebt, hnotL, hnotB⟩ := hP.1 i hx
  have hGL : Dekl.GlL K σ σ' := Dekl.GlL.baum K hb hrm (by simp) (by simp)
  have hmemK : ∀ j, K.InB σ' j ↔ (j = (ρ.get i).n ∨ K.InB σ j) := fun j => by
    rw [Dekl.InB_some hb, Dekl.InB_some hb]; exact hmem j
  have hOk : K.Ok σ' := by
    refine ⟨hok', hGL.lok (fun j hj => (hlebt' j).mpr (Dekl.InL.lebt hS.2.1 hj)) hS.2.1,
      (Dekl.BOk_some hb σ').mpr hbok, ?_⟩
    rintro j ⟨hjL, hjB⟩
    rcases (hmemK j).mp hjB with rfl | hm
    · exact hnotL ((hGL.inL _).mp hjL)
    · exact hS.2.2.2 j ⟨(hGL.inL _).mp hjL, hm⟩
  refine ih σ' ρ hOk (Passt.wechsel K hP (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_))
  · rcases Abs.set_eq hy with ⟨-, h⟩ | ⟨hyi, hy'⟩
    · cases h
    · obtain ⟨hly, hnl, hnb⟩ := hP.1 y hy'
      have hne : (ρ.get y).n ≠ (ρ.get i).n := hP.2.2.2 y i hy' hx hyi
      refine ⟨hy', (hlebt' _).mpr hly, fun hm => hnl ((hGL.inL _).mp hm), fun hm => ?_⟩
      rcases (hmemK _).mp hm with e | hm'
      · exact hne e
      · exact hnb hm'
  · rcases Abs.set_eq hy with ⟨-, h⟩ | ⟨-, hy'⟩
    · cases h
    · exact (hGL.inL _).mpr (hP.2.1 y hy')
  · rcases Abs.set_eq hy with ⟨hyx, -⟩ | ⟨-, hy'⟩
    · have := Var.pos_inj y i hyx
      subst this
      exact (hmemK _).mpr (Or.inl rfl)
    · exact (hmemK _).mpr (Or.inr (hP.2.2.1 y hy'))

theorem kern_haengen {a a' : Abs} (b : BaumDekl A) (hb : K.baum = some b) (Cp Co : LinkFeld A)
    (hs : (Cp = b.Lf ∧ Co = b.Rf) ∨ (Cp = b.Rf ∧ Co = b.Lf))
    (p i : Var Γ (Ty.index (D.count A.tab))) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (rest : Block D V l Γ Λ Λ') (hp : a p.pos = .baum) (hi : a i.pos = .frei)
    (ih : Folgt K O passes R (a.set i.pos .baum) rest a')
    (σ : World D) (ρ : Env D Γ) (hS : K.Ok σ) (hP : Passt K a σ ρ) (hg : Cp.wert σ (ρ.get p).n = D.count A.tab) :
    Post K a' (execBlock O passes R (Block.blattEin Cp Co p i hwT hLT rest) σ ρ) := by
  have hbok : BaumOk A b.Lf b.Rf b.Wz σ := (Dekl.BOk_some hb σ).mp hS.2.2.1
  have hpb := (Dekl.InB_some hb σ _).mp (hP.2.2.1 p hp)
  obtain ⟨hlebt, hnotL, hnotB⟩ := hP.1 i hi
  have hnb : ¬ InBaum (D.count A.tab) (b.Lf.wert σ) (b.Rf.wert σ) (b.Wz.st σ) (ρ.get i).n :=
    fun h => hnotB ((Dekl.InB_some hb σ _).mpr h)
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨σ', he, hrm, hbok', hmemi, hok', hlebt', hmem⟩ :=
      baum_einfuegen_links_zug O passes R b.Wz b.Lf b.Rf b.hd p i hwT hLT rest σ ρ hS.1 hbok hpb hg hlebt hnb
    rw [he]
    exact haengen_nach O passes R K b hb i hi ρ hS hP hrm hbok' hok' hlebt' hmem ih
  · obtain ⟨σ', he, hrm, hbok', hmemi, hok', hlebt', hmem⟩ :=
      baum_einfuegen_rechts_zug O passes R b.Wz b.Lf b.Rf b.hd.symm p i hwT hLT rest σ ρ hS.1 hbok hpb hg hlebt hnb
    rw [he]
    refine haengen_nach O passes R K b hb i hi ρ hS hP (hrm.mono ?_ ?_) hbok' hok' hlebt' hmem ih
    · intro f hf; simp at hf ⊢; tauto
    · intro g hg; simp at hg

theorem fall_haengen {a a' : Abs} (b : BaumDekl A) (hb : K.baum = some b) (Cp Co : LinkFeld A)
    (hs : (Cp = b.Lf ∧ Co = b.Rf) ∨ (Cp = b.Rf ∧ Co = b.Lf))
    (p i : Var Γ (Ty.index (D.count A.tab))) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (hp : a p.pos = .baum) (hi : a i.pos = .frei)
    (hv : Rein voll) (ih : Folgt K O passes R (a.set i.pos .baum) rest a') :
    Folgt K O passes R a (Block.haengen Cp Co p i hwT hLT voll rest) a' := by
  intro σ ρ hS hP
  simp only [Block.haengen, execBlock]
  split
  · rename_i hc
    exact kern_haengen O passes R K b hb Cp Co hs p i hwT hLT rest hp hi ih _ ρ (Dekl.Ok.lese K Λ _ hS)
      (Passt.lese K Λ _ hP) ((leerTest_wahr Cp p hLT _ ρ).mp hc)
  · exact Rein.post K O passes R hv _ _ (Dekl.Ok.lese K Λ _ hS)

/-! ## 4. Cutting a leaf off -/

/-- What follows a cut, from the facts the executed form leaves: the slot `k` left the tree (it was in it), the
    other members are among the old ones, the list is where it was. The binder is a new OWNED slot. -/
theorem nach_schnitt {a a'' : Abs} {σ σ' : World D} {k : Wert D (Ty.index (D.count A.tab))} (ρ : Env D Γ)
    (hS : K.Ok σ) (hP : Passt K a σ ρ) (hGL : Dekl.GlL K σ σ') (hok' : A.FreiOk σ') (hbok' : K.BOk σ')
    (hlebt' : ∀ j, A.Lebt σ' j ↔ A.Lebt σ j) (hsub : ∀ j, K.InB σ' j → K.InB σ j) (hk : K.InB σ k.n)
    (hnotin : ¬ K.InB σ' k.n) (hlebtk : A.Lebt σ' k.n)
    {rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ'}
    (ih : Folgt K O passes R ((a.forget .baum).ext .frei) rest a'') :
    Post K a'' (execBlock O passes R rest σ' (.cons k ρ)) := by
  have hkL : ¬ K.InL σ k.n := fun h => hS.2.2.2 _ ⟨h, hk⟩
  have hOk : K.Ok σ' := by
    refine ⟨hok', hGL.lok (fun j hj => (hlebt' j).mpr (Dekl.InL.lebt hS.2.1 hj)) hS.2.1, hbok', ?_⟩
    rintro j ⟨hjL, hjB⟩
    exact hS.2.2.2 j ⟨(hGL.inL j).mp hjL, hsub j hjB⟩
  have hP0 : Passt K (a.forget .baum) σ' ρ := by
    refine Passt.wechsel K hP (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨hy', -⟩ := Abs.forget_eq hy (by decide)
      obtain ⟨hly, hnl, hnb⟩ := hP.1 y hy'
      exact ⟨hy', (hlebt' _).mpr hly, fun hm => hnl ((hGL.inL _).mp hm), fun hm => hnb (hsub _ hm)⟩
    · exact (hGL.inL _).mpr (hP.2.1 y (Abs.forget_eq hy (by decide)).1)
    · exact absurd rfl (Abs.forget_eq hy (by decide)).2
  refine ih σ' (.cons k ρ) hOk (Passt.ext_frei K k hP0 hlebtk (fun hm => hkL ((hGL.inL _).mp hm)) hnotin ?_)
  intro y hy e
  have hy' := (Abs.forget_eq hy (by decide)).1
  exact (hP.1 y hy').2.2 (by rw [e]; exact hk)

theorem fall_abschneiden {a a'' : Abs} (b : BaumDekl A) (hb : K.baum = some b)
    (C : LinkFeld A) (hC : C = b.Lf ∨ C = b.Rf) (p : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (voll : Endblock D V l Γ Λ)
    (voll2 : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hp : a p.pos = .baum) (hv : Rein voll)
    (hv2 : Rein voll2) (ih : Folgt K O passes R ((a.forget .baum).ext .frei) rest a'') :
    Folgt K O passes R a (Block.abschneiden b.Lf b.Rf C p hwT hLT voll voll2 rest) a''.tail := by
  intro σ ρ hS hP
  have hbok : BaumOk A b.Lf b.Rf b.Wz σ := (Dekl.BOk_some hb σ).mp hS.2.2.1
  have hpb := (Dekl.InB_some hb σ _).mp (hP.2.2.1 p hp)
  by_cases hi : C.wert σ (ρ.get p).n < D.count A.tab
  · by_cases hl : b.Lf.wert σ (C.wert σ (ρ.get p).n) = D.count A.tab ∧
        b.Rf.wert σ (C.wert σ (ρ.get p).n) = D.count A.tab
    · rcases hC with rfl | rfl
      · obtain ⟨σ', k, he, hrm, hkn, hbok', hok', hlebt', hnotin, hlebtk, hkin, hsub⟩ :=
          baum_abschneiden_links_zug O passes R b.Wz b.Lf b.Rf b.hd.symm p hwT hLT voll voll2 rest σ ρ hS.1 hbok
            hpb hi hl.1 hl.2
        rw [he]
        apply Post.schrumpf
        exact nach_schnitt O passes R K ρ hS hP (Dekl.GlL.baum K hb hrm (by simp) (by simp)) hok'
          ((Dekl.BOk_some hb σ').mpr hbok') hlebt'
          (fun j hj => (Dekl.InB_some hb σ j).mpr (hsub j ((Dekl.InB_some hb σ' j).mp hj)))
          ((Dekl.InB_some hb σ _).mpr hkin) (fun h => hnotin ((Dekl.InB_some hb σ' _).mp h)) hlebtk ih
      · obtain ⟨σ', k, he, hrm, hkn, hbok', hok', hlebt', hnotin, hlebtk, hkin, hsub⟩ :=
          baum_abschneiden_rechts_zug O passes R b.Wz b.Lf b.Rf b.hd p hwT hLT voll voll2 rest σ ρ hS.1 hbok
            hpb hi hl.1 hl.2
        rw [he]
        apply Post.schrumpf
        exact nach_schnitt O passes R K ρ hS hP (Dekl.GlL.baum K hb hrm (by simp) (by simp)) hok'
          ((Dekl.BOk_some hb σ').mpr hbok') hlebt'
          (fun j hj => (Dekl.InB_some hb σ j).mpr (hsub j ((Dekl.InB_some hb σ' j).mp hj)))
          ((Dekl.InB_some hb σ _).mpr hkin) (fun h => hnotin ((Dekl.InB_some hb σ' _).mp h)) hlebtk ih
    · obtain ⟨k, o2, he⟩ := abschneiden_nichtblatt O passes R b.Lf b.Rf C p hwT hLT voll voll2 rest σ ρ hi hl
      rw [he]
      apply Post.schrumpf
      exact Rein.post K O passes R hv2 _ _ (Dekl.Ok.lese K Λ o2 (Dekl.Ok.lese K Λ _ hS))
  · rw [abschneiden_voll O passes R b.Lf b.Rf C p hwT hLT voll voll2 rest σ ρ hi]
    exact Rein.post K O passes R hv _ _ (Dekl.Ok.lese K _ _ hS)

theorem fall_wurzelAus {a a'' : Abs} (b : BaumDekl A) (hb : K.baum = some b)
    (hwG : V.gschreibt b.Wz.g = true) (hLG : gdarf D b.Wz.g Λ) (hLT : darf D A.tab Λ) (voll : Endblock D V l Γ Λ)
    (voll2 : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hv : Rein voll) (hv2 : Rein voll2)
    (ih : Folgt K O passes R ((a.forget .baum).ext .frei) rest a'') :
    Folgt K O passes R a (Block.wurzelAus b.Lf b.Rf b.Wz hwG hLG hLT voll voll2 rest) a''.tail := by
  intro σ ρ hS hP
  have hbok : BaumOk A b.Lf b.Rf b.Wz σ := (Dekl.BOk_some hb σ).mp hS.2.2.1
  by_cases hi : b.Wz.st σ < D.count A.tab
  · by_cases hl : b.Lf.wert σ (b.Wz.st σ) = D.count A.tab ∧ b.Rf.wert σ (b.Wz.st σ) = D.count A.tab
    · obtain ⟨σ', k, he, hrm, hkn, hbok', hok', hlebt', hempty, hlebtk, hkin⟩ :=
        baum_wurzel_aus_zug O passes R b.Lf b.Rf b.Wz hwG hLG hLT voll voll2 rest σ ρ hS.1 hbok hi hl.1 hl.2
      rw [he]
      apply Post.schrumpf
      exact nach_schnitt O passes R K ρ hS hP (Dekl.GlL.baum K hb hrm (by simp) (by simp)) hok'
        ((Dekl.BOk_some hb σ').mpr hbok') hlebt'
        (fun j hj => absurd ((Dekl.InB_some hb σ' j).mp hj) (hempty j))
        ((Dekl.InB_some hb σ _).mpr hkin) (fun h => hempty _ ((Dekl.InB_some hb σ' _).mp h)) hlebtk ih
    · obtain ⟨k, o2, he⟩ := wurzelAus_nichtblatt O passes R b.Lf b.Rf b.Wz hwG hLG hLT voll voll2 rest σ ρ hi hl
      rw [he]
      apply Post.schrumpf
      exact Rein.post K O passes R hv2 _ _ (Dekl.Ok.lese K Λ o2 (Dekl.Ok.lese K Λ _ hS))
  · rw [wurzelAus_voll O passes R b.Lf b.Rf b.Wz hwG hLG hLT voll voll2 rest σ ρ hi]
    exact Rein.post K O passes R hv _ _ (Dekl.Ok.lese K _ _ hS)

end Faelle

end Gabbro.Grammatik
