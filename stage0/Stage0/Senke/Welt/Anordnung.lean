/- Source image correctness composed with the canonical full-span world layout. -/
import Stage0.Senke.Welt.AnordnungLayout
import Stage0.Senke.BildSatz
namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR
variable [Kern]
/-- **The program theorem for an elaborated program** (`stage0 --ir`): the image of `bild` with the world laid out
    by `layU`, under the named assumption at the gates (`TorOK`); what is left is that the image's memory holds the start
    world. -/
theorem bild_ok_u [CloneOK] {u : UProg} {P : Programm (declOf u)} {O : Orakel (declOf u)} {passes : Nat}
    {fs : List (declOf u).Fn} {pos : (declOf u).Fn → Nat} {name : (declOf u).Fn → String} {main : (declOf u).Fn}
    {roots : List (declOf u).Fn} {Ks : Nat} {b : Bild (declOf u)} {ρ : Env (declOf u) ((declOf u).params main)}
    {tor : (declOf u).Ax → Option TorB} (hb : bild passes P (layU u tor) fs pos name main ρ roots Ks = .ok b) (hfs : ∀ g, fs[pos g]? = some g)
    {m : Runner.Mem} (hm : BytesAt m Runner.Prog.IMG b.bytes) (σ : World (declOf u))
    (hval : ∀ τ (x : Var ((declOf u).params main) τ), ValueValid b.Y τ (ρ.get x))
    (hWa : WeltAt m b.Y σ) (hT : TorOK b.Y O) (hV : SichtOK O) :
    match rufAt P O b.passes b.depth main σ ρ with
    | .ok _ v => ∃ t' m' q, Star ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 b.fp0⟩ m t' m' ∧ StopAt t' m' q ∧
        q.nr = 231 ∧ ExitErg b.Y ((declOf u).erg main) v q.a1
    | .logik e => Stops ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 b.fp0⟩ m (logikCode e)
    | .hardware h => Stops ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 b.fp0⟩ m (hwCode h)
    | _ => False := by
  have h := bild_ok (O := O) (passes := passes) hb hfs (fun x h => layU_in u tor x h) (fun x => layU_dis u tor x)
    (fun x => by simp only [layU]; omega) (fun x => layU_sync u tor x) hm σ hval hWa hT hV
  generalize rufAt P O b.passes b.depth main σ ρ = o at h ⊢
  cases o <;> exact h

/-- **The thread of root `j`** of an elaborated program, on its own stack. -/
theorem bild_wurzel_ok_u {u : UProg} {P : Programm (declOf u)} {O : Orakel (declOf u)} {passes : Nat}
    {fs : List (declOf u).Fn} {pos : (declOf u).Fn → Nat} {name : (declOf u).Fn → String} {main : (declOf u).Fn}
    {roots : List (declOf u).Fn} {Ks : Nat} {b : Bild (declOf u)} {ρm : Env (declOf u) ((declOf u).params main)}
    {tor : (declOf u).Ax → Option TorB} (hb : bild passes P (layU u tor) fs pos name main ρm roots Ks = .ok b)
    (hfs : ∀ g, fs[pos g]? = some g) {m : Runner.Mem} (hm : BytesAt m Runner.Prog.IMG b.bytes) (j : Nat)
    (hj : j < roots.length) (σ : World (declOf u)) (ρ : Env (declOf u) ((declOf u).params roots[j]))
    (hWa : WeltAt m b.Y σ) (hT : TorOK b.Y O) (hV : SichtOK O) :
    match rufAt P O b.passes b.depth roots[j] σ ρ with
    | .ok _ _ => ∃ t' m' q, Star ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * roots.length + startLen + startLen * j)),
        BitVec.ofNat 64 (b.fp0 + 8 * (b.Ks * (j + 1)))⟩ m t' m' ∧ StopAt t' m' q ∧ q.nr = 60
    | .logik e => Stops ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * roots.length + startLen + startLen * j)),
        BitVec.ofNat 64 (b.fp0 + 8 * (b.Ks * (j + 1)))⟩ m (logikCode e)
    | .hardware e => Stops ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * roots.length + startLen + startLen * j)),
        BitVec.ofNat 64 (b.fp0 + 8 * (b.Ks * (j + 1)))⟩ m (hwCode e)
    | _ => False := by
  have h := bild_wurzel_ok (O := O) (passes := passes) hb hfs (fun x h => layU_in u tor x h)
    (fun x => layU_dis u tor x) (fun x => by simp only [layU]; omega) (fun x => layU_sync u tor x) hm j hj σ ρ hWa hT hV
  generalize rufAt P O b.passes b.depth roots[j] σ ρ = o at h ⊢
  cases o <;> exact h

end Gabbro.Stage0.Senke
