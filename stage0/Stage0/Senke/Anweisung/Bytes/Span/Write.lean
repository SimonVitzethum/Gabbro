/- Induction over chunk count preserves the complete machine-G byte-write trace. -/
module
public import Stage0.Senke.Anweisung.Bytes.Span.Chunk
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- Each iteration invokes the existing <=8 kernel. Captured source storage is
    below all scratch and remains available after arbitrary preceding stores. -/
theorem putBytesWords_ok {Γ : Ctx} {Λ : List (Res D)} {a b H : Int}
    {t : D.Tab} {f : D.Feld t} (hf : D.typ t f = .int 0 255) (lower : 0 ≤ a)
    {fp : Runner.W} {Ks K : Nat} (hW : WIn L fp Ks K)
    (z : Zahl 0 H) (k : Zahl a b) (ρ : Env D Γ) :
    ∀ words n q (upper : b + 8 * q + n ≤ D.count t) c top,
      n ≤ 8 * words → q + words ≤ valueWords (.int 0 H) →
      putBytesWordsL L (Γ := Γ) (Λ := Λ) t f a b H lower reserved words n q upper = some (c, top) →
      top ≤ Ks → ∀ m pc σ,
      PreS L m pc fp K (frei (ByteCapture Γ a b H) reserved) c (Env.cons k (Env.cons z ρ)) reserved →
      WeltAt m L σ →
      ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * c.length), fp⟩ m' ∧
        AgreeW L fp (frei (ByteCapture Γ a b H) reserved) K m m' ∧
        EnvAt L m' fp (Env.cons k (Env.cons z ρ)) reserved ∧
        WeltAt m' L (σ.schreibBytes t f hf Λ (k.n + 8 * q) (zahlZuBytes n (dropBytes (8 * q) z.n))) := by
  intro words
  induction words with
  | zero =>
    intro n q upper c top capacity _ made _ m pc σ pre world
    have zero : n = 0 := by omega
    subst n
    simp only [putBytesWordsL, Option.some.injEq, Prod.mk.injEq] at made
    obtain ⟨rfl, rfl⟩ := made
    exact ⟨m, by simpa using Star.refl ⟨pc, fp⟩ m, AgreeW.refl _ _ _ _ _, pre.env, world⟩
  | succ words tailIH =>
    intro n q upper c top capacity limbs made fits m pc σ pre world
    simp only [putBytesWordsL] at made
    split at made
    · next zero =>
      subst n
      simp only [Option.some.injEq, Prod.mk.injEq] at made
      obtain ⟨rfl, rfl⟩ := made
      exact ⟨m, by simpa using Star.refl ⟨pc, fp⟩ m, AgreeW.refl _ _ _ _ _, pre.env, world⟩
    · next nonzero =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at made
      obtain ⟨⟨idx, ti⟩, indexMade, ⟨kernel, tk⟩, kernelMade, ⟨rest, tr⟩, restMade, rfl, rfl⟩ := made
      let s := frei (ByteCapture Γ a b H) reserved
      let prefix := [ci 2 s (frei Γ reserved + q) 0] ++ idx ++ kernel
      have p : PreS L m pc fp K s (prefix ++ rest) (Env.cons k (Env.cons z ρ)) reserved := by
        simpa only [s, prefix, List.append_assoc] using pre
      obtain ⟨m1, s1, ch1, env1, world1⟩ := putBytesChunk_ok hf lower hW z k ρ q (min 8 n)
        (by omega) (by omega) (by omega) (by omega) indexMade kernelMade (by omega)
        p.left world
      have run1 : Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * prefix.length), fp⟩ m1 := by
        simpa only [prefix, List.length_append, List.length_singleton] using s1
      by_cases more : 8 < n
      · simp only [if_pos more] at restMade
        have far := codeFar_right (n := prefix.length) (k := rest.length)
          (by simpa only [List.length_append] using p.far)
        have p1 : PreS L m1 (pc + BitVec.ofNat 64 (16 * prefix.length)) fp K s rest
            (Env.cons k (Env.cons z ρ)) reserved :=
          ⟨p.ctx, p.small, frameOK_agreeW p.frame ch1,
            codeAt_agreeWIn hW ch1 (codeAt_right p.code) far, far, env1, trivial, wstab_true _ _⟩
        obtain ⟨m2, s2, ch2, env2, world2⟩ := tailIH (n - 8) (q + 1) (by omega) rest tr
          (by omega) (by omega) restMade (by omega) m1 _ _ p1 world1
        refine ⟨m2, ?_, ch1.trans ch2, env2, ?_⟩
        · simpa only [prefix, List.length_append, List.length_singleton, pc_add] using run1.trans s2
        · have chunks : zahlZuBytes n (dropBytes (8 * q) z.n) =
              zahlZuBytes 8 (byteLimb z.n q).n ++ zahlZuBytes (n - 8) (dropBytes (8 * (q + 1)) z.n) := by
            rw [zahlZuBytes_limb 8 (by decide)]
            conv_lhs => rw [show n = 8 + (n - 8) by omega, zahlZuBytes_append]
            rw [← dropBytes_add]
            congr 2
            omega
          rw [chunks, World.schreibBytes_append]
          simpa only [Nat.min_eq_left (by omega : 8 ≤ n), zahlZuBytes_length,
            Int.natCast_mul, Int.natCast_add, Int.natCast_one, Int.add_assoc, Int.mul_add,
            Int.mul_one] using world2
      · simp only [if_neg more, Option.some.injEq, Prod.mk.injEq] at restMade
        obtain ⟨rfl, rfl⟩ := restMade
        refine ⟨m1, ?_, ch1, env1, ?_⟩
        · simpa only [prefix, List.length_append, List.length_singleton, List.length_nil, Nat.add_zero] using run1
        · simpa only [Nat.min_eq_right (by omega : n ≤ 8), zahlZuBytes_limb n (by omega)] using world1

end Gabbro.Stage0.Senke
