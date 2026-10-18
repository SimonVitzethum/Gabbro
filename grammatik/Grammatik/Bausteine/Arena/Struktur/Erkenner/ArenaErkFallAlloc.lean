/-
  File:      Grammatik/ArenaErkFallAlloc.lean
  Subject:   THE CASES OF THE RECOGNIZER'S SOUNDNESS PROOF, part 1: the allocator moves and the moves that touch no
             structure word (`frisch`, `nimm`, `frei`, `wachs`, `pruefe`, `nutzlast`, `ite`, `nil`). Each case is the
             executed-form theorem of `ArenaAllocForm.lean`/`ArenaWachs.lean` with its side conditions discharged by the
             abstract state: a fresh slot is in neither structure, a released slot was in neither, a commit and a payload
             store move no word either structure reads.
-/
import Grammatik.Bausteine.Arena.Struktur.Erkenner.ArenaErkennerLemmas

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

variable {D : Deklaration}

section Faelle
variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {A : FreiForm D} (K : Dekl A) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

theorem fall_nil (a : Abs) : Folgt K (V := V) (l := l) O passes R a (Block.nil (Γ := Γ) (Λ := Λ)) a :=
  fun _ _ hS hP => ⟨hS, hP⟩

theorem fall_frisch {a a'' : Abs} (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (hwG : V.gschreibt A.zaehl = true)
    (hLG : gdarf D A.zaehl Λ) (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hv : Rein voll)
    (ih : Folgt K O passes R (a.ext .frei) rest a'') :
    Folgt K O passes R a (Block.arenaAlloc A.toArenaForm v hwT hLT hwG hLG voll rest) a''.tail := by
  intro σ ρ hS hP
  by_cases hlt : A.stand σ < D.count A.tab
  · obtain ⟨σ', k, he, hkn, hf, hok', hmono, hnew⟩ :=
      frischAlloc_ausfuehren O passes R A v hwT hLT hwG hLG voll rest σ ρ hlt hS.1
    rw [he]
    apply Post.schrumpf
    have hGL : Dekl.GlL K σ σ' := Dekl.GlL.fremd hf
    have hGB : Dekl.GlB K σ σ' := Dekl.GlB.fremd hf
    have hnot := Dekl.nicht_in_stand K hS (j := k.n) (by omega)
    refine ih σ' (.cons k ρ) (Dekl.Ok.gleich hGL hGB hok' (fun j hj => hmono j ?_) hS)
      (Passt.ext_frei K k (Passt.gleich K hGL hGB hmono hP) hnew (fun hm => hnot.1 ((hGL.inL _).mp hm))
        (fun hm => hnot.2 ((hGB.inB _).mp hm)) (fun y hy e => by have := (hP.1 y hy).1.2.1; omega))
    rcases hj with hj | hj
    · exact Dekl.InL.lebt hS.2.1 hj
    · exact Dekl.InB.lebt hS.2.2.1 hj
  · rw [frischAlloc_voll O passes R A v hwT hLT hwG hLG voll rest σ ρ hlt]
    exact Rein.post K O passes R hv _ _ (Dekl.Ok.lese K _ _ hS)

theorem fall_nimm {a a'' : Abs} (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (hwK : V.gschreibt A.kopf = true)
    (hLK : gdarf D A.kopf Λ) (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hv : Rein voll)
    (ih : Folgt K O passes R (a.ext .frei) rest a'') :
    Folgt K O passes R a (Block.freiNimm A v hwT hLT hwK hLK voll rest) a''.tail := by
  intro σ ρ hS hP
  by_cases hlt : A.kopfSt σ < D.count A.tab
  · obtain ⟨σ', k, he, hkn, hf, hok', hmono, hnew, hauf⟩ :=
      nimmAlloc_ausfuehren O passes R A v hwT hLT hwK hLK voll rest σ ρ hlt hS.1
    rw [he]
    apply Post.schrumpf
    have hGL : Dekl.GlL K σ σ' := Dekl.GlL.fremd hf
    have hGB : Dekl.GlB K σ σ' := Dekl.GlB.fremd hf
    have hnot := Dekl.nicht_in_frei K hS hauf
    refine ih σ' (.cons k ρ) (Dekl.Ok.gleich hGL hGB hok' (fun j hj => hmono j ?_) hS)
      (Passt.ext_frei K k (Passt.gleich K hGL hGB hmono hP) hnew (fun hm => hnot.1 ((hGL.inL _).mp hm))
        (fun hm => hnot.2 ((hGB.inB _).mp hm)) (fun y hy e => (hP.1 y hy).1.2.2 (by rw [e]; exact hauf)))
    rcases hj with hj | hj
    · exact Dekl.InL.lebt hS.2.1 hj
    · exact Dekl.InB.lebt hS.2.2.1 hj
  · rw [nimmAlloc_voll O passes R A v hwT hLT hwK hLK voll rest σ ρ hlt]
    exact Rein.post K O passes R hv _ _ (Dekl.Ok.lese K _ _ hS)

theorem fall_frei {a a' : Abs} (x : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (hwK : V.gschreibt A.kopf = true)
    (hLK : gdarf D A.kopf Λ) (rest : Block D V l Γ Λ Λ') (hx : a x.pos = .frei)
    (ih : Folgt K O passes R (a.set x.pos .offen) rest a') :
    Folgt K O passes R a (Block.freiVar A x hwT hLT hwK hLK rest) a' := by
  intro σ ρ hS hP
  obtain ⟨hlebt, hnotL, hnotB⟩ := hP.1 x hx
  obtain ⟨σ', he, hf, hok', hmono, hdead⟩ :=
    freiVar_lebt O passes R A x hwT hLT hwK hLK rest σ ρ hlebt hS.1
  rw [he]
  have hGL : Dekl.GlL K σ σ' := Dekl.GlL.fremd hf
  have hGB : Dekl.GlB K σ σ' := Dekl.GlB.fremd hf
  refine ih σ' ρ (Dekl.Ok.gleich hGL hGB hok' (fun j hj => hmono j ?_ ?_) hS)
    (Passt.wechsel K hP (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_))
  · rcases hj with hj | hj
    · exact Dekl.InL.lebt hS.2.1 hj
    · exact Dekl.InB.lebt hS.2.2.1 hj
  · rintro rfl
    rcases hj with hj | hj
    · exact hnotL hj
    · exact hnotB hj
  · rcases Abs.set_eq hy with ⟨-, h⟩ | ⟨hyx, hy'⟩
    · cases h
    · obtain ⟨hly, hnl, hnb⟩ := hP.1 y hy'
      have hne : (ρ.get y).n ≠ (ρ.get x).n := hP.2.2.2 y x hy' hx hyx
      exact ⟨hy', hmono _ hly hne, fun hm => hnl ((hGL.inL _).mp hm), fun hm => hnb ((hGB.inB _).mp hm)⟩
  · rcases Abs.set_eq hy with ⟨-, h⟩ | ⟨-, hy'⟩
    · cases h
    · exact (hGL.inL _).mpr (hP.2.1 y hy')
  · rcases Abs.set_eq hy with ⟨-, h⟩ | ⟨-, hy'⟩
    · cases h
    · exact (hGB.inB _).mpr (hP.2.2.1 y hy')

theorem fall_wachs {a a'' : Abs} (n : Int) (hwK : V.gschreibt A.komm = true)
    (hLK : gdarf D A.komm Λ) (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.int 0 (D.count A.tab) :: Γ) Λ Λ') (hv : Rein voll)
    (ih : Folgt K O passes R (a.ext .offen) rest a'') :
    Folgt K O passes R a (Block.dynGrowB A.toDynForm n hwK hLK voll rest) a''.tail := by
  intro σ ρ hS hP
  by_cases hg : 0 ≤ A.komSt σ + n ∧ A.komSt σ + n ≤ D.count A.tab
  · obtain ⟨he, -, -, -⟩ := dynGrow_commit O passes R A.toDynForm n hwK hLK voll rest σ ρ hg.1 hg.2
    rw [he]
    apply Post.schrumpf
    have hgl := Dekl.Gleich.wachs A K n Λ σ hg.1 hg.2
    exact ih _ _ (hgl.ok hS) (Passt.ext_offen K (hgl.passt hP))
  · rw [dynGrow_voll O passes R A.toDynForm n hwK hLK voll rest σ ρ hg]
    exact Rein.post K O passes R hv _ _ (Dekl.Ok.lese K _ _ hS)

theorem fall_pruefe {a a' : Abs} (c : Expr D Γ Λ .bool) (voll : Endblock D V l Γ Λ)
    (rest : Block D V l Γ Λ Λ') (hv : Rein voll) (ih : Folgt K O passes R a rest a') :
    Folgt K O passes R a (Block.check c voll rest) a' := by
  intro σ ρ hS hP
  simp only [execBlock]
  split
  · exact ih _ ρ (Dekl.Ok.lese K Λ _ hS) (Passt.lese K Λ _ hP)
  · exact Rein.post K O passes R hv _ _ (Dekl.Ok.lese K Λ _ hS)

theorem fall_nutzlast {a a' : Abs} (i : Expr D Γ Λ (.index (D.count A.tab)))
    (e : Expr D Γ Λ (D.typ A.tab A.feld)) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (rest : Block D V l Γ Λ Λ') (ih : Folgt K O passes R a rest a') :
    Folgt K O passes R a (Block.cons (Stmt.assignSlot A.tab A.feld i e hwT hLT) rest) a' := by
  intro σ ρ hS hP
  obtain ⟨σ', hex, hgl⟩ : ∃ σ' : World D,
      execStmt O passes R (Stmt.assignSlot (l := l) A.tab A.feld i e hwT hLT) σ ρ = .ok σ' ρ ∧
      Dekl.Gleich K σ σ' :=
    ⟨_, rfl, (Dekl.Gleich.lese σ Λ _).trans (Dekl.Gleich.nutzlast _ Λ _ _)⟩
  refine Post.cons_stmt K O passes R (a := a) ?_ ih
  rw [hex]
  exact ⟨hgl.ok hS, hgl.passt hP⟩

theorem fall_ite {Λ1 : List (Res D)} {a a1 a2 a3 a' : Abs} (c : Expr D Γ Λ .bool)
    (t e : Block D V l Γ Λ Λ1) (rest : Block D V l Γ Λ1 Λ') (h1 : Abs.Schwacher a3 a1)
    (h2 : Abs.Schwacher a3 a2) (iht : Folgt K O passes R a t a1) (ihe : Folgt K O passes R a e a2)
    (ih : Folgt K O passes R a3 rest a') :
    Folgt K O passes R a (Block.cons (Stmt.ite c t e) rest) a' := by
  intro σ ρ hS hP
  have hgl : Dekl.Gleich K σ (σ.lese Λ c.orte) := Dekl.Gleich.lese σ Λ c.orte
  refine Post.cons_stmt K O passes R (a := a3) ?_ ih
  simp only [execStmt]
  split
  · exact Post.schwacher K h1 (iht _ ρ (hgl.ok hS) (hgl.passt hP))
  · exact Post.schwacher K h2 (ihe _ ρ (hgl.ok hS) (hgl.passt hP))

end Faelle

end Gabbro.Grammatik
