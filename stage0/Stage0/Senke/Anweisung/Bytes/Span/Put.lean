/- Capture complete source values, then connect chunked writes to statement simulation. -/
module
public import Stage0.Senke.Anweisung.Bytes.Span.Write
public import Stage0.Senke.Anweisung.Simulation
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {reserved : Nat}

theorem putBytesWide_ok {L : Lay D} {P : Programm D} {f : D.Fn} {σ0 : World D}
    {ρ0 : Env D (D.params f)} {rp cfp fp pc : Runner.W} {K Ks lo : Nat} {pr : List Nat}
    {ex : Int × Int} {O : Orakel D} {passes : Nat}
    {R : (g : D.Fn) → World D → Env D (D.params g) → RufAusgang g}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {t : D.Tab} {field : D.Feld t} {a b : Int}
    (hf : D.typ t field = .int 0 255) (n : Nat) (wide : 8 < n) (i : Expr D Γ Λ (.int a b))
    (lower : 0 ≤ a) (upper : b + n ≤ D.count t) (e : Expr D Γ Λ (.int 0 (256 ^ n - 1)))
    (hw : (vertragVon D f).schreibt t = true) (hl : darf D t Λ)
    {c : List II} {top : Nat} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (made : putBytesWideL L (Γ := Γ) (Λ := Λ) t field a b n lower upper
      (lowE (reserved := reserved) L e (frei Γ reserved))
      (lowE (reserved := reserved) L i (frei Γ reserved + valueWords (.int 0 (256 ^ n - 1)))) reserved = some (c, top))
    (fits : top ≤ Ks) (hW : WIn L fp Ks K) (pre : PreS L m pc fp K (frei Γ reserved) c ρ reserved)
    (hlow : lo ≤ frei Γ reserved) (world : WeltAt m L σ) (hpr : ∀ j ∈ pr, j < frei Γ reserved) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length))
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2)
      (execStmt O passes R (Stmt.putBytes (l := l) t field hf n i lower upper e hw hl) σ ρ) reserved := by
  simp only [putBytesWideL] at made
  split at made
  · next representable =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at made
    obtain ⟨⟨ce, te⟩, he, ⟨ci', ti⟩, hi, ⟨cb, tb⟩, hb, rfl, rfl⟩ := made
    have bound : b < 2 ^ 64 := by
      by_contra bad
      have cell := hW.lay.1 t field b.toNat (L.bounded (by omega))
      have cw : valueWords (D.typ t field) = 1 := by rw [hf]; rfl
      simp only [Lay.elem, cw] at cell
      have small := hW.lay.2.2
      omega
    have iw : valueWords (.int a b) = 1 := integerWords_unsigned lower bound
    have hks := hW.ks
    have teTop := lowE_top e _ _ _ he
    have tiTop := lowE_top i _ _ _ hi
    let H := (256 : Int) ^ n - 1
    let σE := σ.lese Λ (i.orte ++ e.orte)
    let z := eval σE e σE ρ
    let k := eval σE i σE ρ
    let base := frei Γ reserved
    have p : PreS L m pc fp K base (ce ++ (ci' ++ cb)) ρ reserved := by
      simpa only [base, List.append_assoc] using pre
    have pe := PreS.welt p.left hks world hW.lay (by have := hW.lo; omega)
    obtain ⟨m1, s1, ch1, value⟩ := lowE_ok (same := by intro _; rfl) σE σE (fun _ h => h)
      hW.lay e _ ce te he (by omega) m pc ρ pe
    have a1 := Agree.widen ch1 hks
    have p1 := p.next a1 (by omega : base ≤ base + valueWords (.int 0 H)) (by omega)
    have world1 := pe.wstab m m1 world (ch1.mono (Nat.zero_le _))
    have pi := PreS.welt p1.left hks world1 hW.lay (by have := hW.lo; omega)
    obtain ⟨m2, s2, ch2, index⟩ := lowE_ok (same := by intro _; rfl) σE σE (fun _ h => h)
      hW.lay i _ ci' ti hi (by omega) m1 _ ρ pi
    have a2 := Agree.widen ch2 hks
    have env1 := envAt_cons (envAt_agree pre.env a1 pre.frame (Nat.le_refl _) (by omega)) value
    have env2 := envAt_agree env1 a2 p1.frame
      (by simp only [frei, contextWords_cons]; dsimp only [base]; omega) (by omega)
    have kAt : ValueAt L m2 fp (frei (.int 0 H :: Γ) reserved) (.int a b) k := by
      simpa only [frei, contextWords_cons, Nat.add_assoc, base, H] using index
    have env3 := envAt_cons env2 kAt
    have p2 := p1.next a2 (by omega : base + valueWords (.int 0 H) ≤ frei (ByteCapture Γ a b H) reserved)
      (by simp only [frei, contextWords_cons, ByteCapture] at fits ⊢; dsimp only [base]; omega)
    have pb : PreS L m2 _ fp K (frei (ByteCapture Γ a b H) reserved) cb (Env.cons k (Env.cons z ρ)) reserved :=
      ⟨Nat.le_refl _, p2.small, p2.frame, p2.code, p2.far, env3, trivial, wstab_true _ _⟩
    have world2 := pi.wstab m1 m2 world1 (ch2.mono (Nat.zero_le _))
    obtain ⟨m3, s3, ch3, env4, world3⟩ := putBytesWords_ok hf lower hW z k ρ
      (valueWords (.int 0 H)) n 0 (by simpa using upper) cb tb
      (byteSpan_capacity n) (by omega) hb (by omega) m2 _ σE pb world2
    have changed : AgreeW L fp base K m m3 :=
      (agreeW_of (a1.trans (a2.mono (by omega)))).trans (ch3.mono (by
        simp only [frei, contextWords_cons, ByteCapture]; dsimp only [base]; omega))
    simp only [execStmt, Sim]
    refine ⟨m3, s1.trans (s2.trans ?_), changed.mono hlow,
      envAt_tail (envAt_tail env4), ?_, keeps_of_agreeW hW changed hpr (by omega)⟩
    · simpa only [List.length_append, pc_add, BitVec.add_assoc] using s3
    · simpa only [dropBytes, Nat.mul_zero, Int.natCast_zero, Int.add_zero] using world3
  · cases made

end Gabbro.Stage0.Senke
