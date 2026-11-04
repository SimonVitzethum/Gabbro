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
    ∀ (words n q : Nat) (upper : b + 8 * q + n ≤ D.count t) (c : List II) (top : Nat),
      n ≤ 8 * words → q + words ≤ valueWords (.int 0 H) →
      putBytesWordsL L (Γ := Γ) (Λ := Λ) t f a b H lower reserved words n q upper = some (c, top) →
      top ≤ Ks → ∀ m pc σ,
      PreS L m pc fp K (frei (ByteCapture Γ a b H) reserved) c
        (Env.cons (τ := .int a b) k (Env.cons (τ := .int 0 H) z ρ)) reserved →
      WeltAt m L σ →
      ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * c.length), fp⟩ m' ∧
        AgreeW L fp (frei (ByteCapture Γ a b H) reserved) K m m' ∧
        EnvAt L m' fp (Env.cons (τ := .int a b) k (Env.cons (τ := .int 0 H) z ρ)) reserved ∧
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
    by_cases zero : n = 0
    · subst n
      simp only [putBytesWordsL, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at made
      obtain ⟨rfl, rfl⟩ := made
      exact ⟨m, by simpa using Star.refl ⟨pc, fp⟩ m, AgreeW.refl _ _ _ _ _, pre.env, world⟩
    · simp only [putBytesWordsL, ite_eq_right zero, bind, Option.bind_eq_some_iff, pure] at made
      obtain ⟨⟨idx, ti⟩, indexMade, ⟨kernel, tk⟩, kernelMade, continuation⟩ := made
      let s := frei (ByteCapture Γ a b H) reserved
      let leading := [ci 2 s (frei Γ reserved + q) 0] ++ idx ++ kernel
      have guarded :
          (if more : 8 < n then
            (putBytesWordsL L (Γ := Γ) (Λ := Λ) t f a b H lower reserved words
              (n - 8) (q + 1) (by omega)).bind fun result =>
                some (leading ++ result.1, max (s + 2) (max ti (max tk result.2)))
          else some (leading ++ [], max (s + 2) (max ti (max tk (s + 2))))) = some (c, top) := by
        simpa only [s, leading, List.append_assoc, Option.bind] using continuation
      have remainder : ∃ (rest : List II) (tr : Nat),
          (if more : 8 < n then
            putBytesWordsL L (Γ := Γ) (Λ := Λ) t f a b H lower reserved words
              (n - 8) (q + 1) (by omega)
          else some ([], s + 2)) = some (rest, tr) ∧
          (leading ++ rest, max (s + 2) (max ti (max tk tr))) = (c, top) := by
        -- Recover the whole canonical conditional before eliminating its result bind.
        by_cases more : 8 < n
        · have branch := guarded
          rw [dite_eq_left more] at branch
          simp only [Option.bind_eq_some_iff, Option.some.injEq] at branch
          obtain ⟨⟨rest, tr⟩, restMade, output⟩ := branch
          refine ⟨rest, tr, ?_, ?_⟩
          · simpa only [dite_eq_left more] using restMade
          · exact output
        · have branch := guarded
          rw [dite_eq_right more] at branch
          refine ⟨[], s + 2, ?_, Option.some.inj branch⟩
          simp only [dite_eq_right more]
      obtain ⟨rest, tr, restMade, output⟩ := remainder
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj output
      change max (s + 2) (max ti (max tk tr)) ≤ Ks at fits
      have p : PreS L m pc fp K s (leading ++ rest)
          (Env.cons (τ := .int a b) k (Env.cons (τ := .int 0 H) z ρ)) reserved := by
        simpa only [s, leading, List.append_assoc] using pre
      obtain ⟨m1, s1, ch1, env1, world1⟩ := putBytesChunk_ok hf lower hW z k ρ q (min 8 n)
        (by omega) (by omega) (by omega) (by omega) indexMade kernelMade
        (by change max (s + 2) (max ti tk) ≤ Ks; omega)
        p.left world
      have run1 : Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * leading.length), fp⟩ m1 := by
        simpa only [leading, List.length_append, List.length_singleton] using s1
      by_cases more : 8 < n
      · simp only [dite_eq_left more] at restMade
        have chunkSize : min 8 n = 8 := Nat.min_eq_left (by omega)
        have far := codeFar_right (n := leading.length) (k := rest.length)
          (by simpa only [List.length_append] using p.far)
        have p1 : PreS L m1 (pc + BitVec.ofNat 64 (16 * leading.length)) fp K s rest
            (Env.cons (τ := .int a b) k (Env.cons (τ := .int 0 H) z ρ)) reserved :=
          ⟨p.ctx, p.small, frameOK_agreeW p.frame ch1,
            codeAt_agreeWIn hW ch1 (codeAt_right p.code) far, far, env1, trivial, wstab_true _ _⟩
        have firstWorld : WeltAt m1 L
            (σ.schreibBytes t f hf Λ (k.n + 8 * q) (zahlZuBytes 8 (byteLimb z.n q).n)) := by
          simpa only [chunkSize] using world1
        obtain ⟨m2, s2, ch2, env2, world2⟩ := tailIH (n - 8) (q + 1) (by omega) rest tr
          (by omega) (by omega) restMade (by omega) m1 _ _ p1 firstWorld
        refine ⟨m2, ?_, ch1.trans ch2, env2, ?_⟩
        · simpa only [leading, List.length_append, List.length_singleton, pc_add, Nat.add_assoc]
            using run1.trans s2
        · have nextDrop : dropBytes 8 (dropBytes (8 * q) z.n) =
              dropBytes (8 * (q + 1)) z.n := by
            rw [← dropBytes_add]
            congr 1
          have chunks : zahlZuBytes n (dropBytes (8 * q) z.n) =
              zahlZuBytes 8 (byteLimb z.n q).n ++ zahlZuBytes (n - 8) (dropBytes (8 * (q + 1)) z.n) := by
            have splitBytes := zahlZuBytes_append 8 (n - 8) (dropBytes (8 * q) z.n)
            rw [show 8 + (n - 8) = n by omega, nextDrop] at splitBytes
            simpa only [zahlZuBytes_limb 8 (by decide)] using splitBytes
          have advance : k.n + 8 * (q : Int) + 8 = k.n + 8 * ((q + 1 : Nat) : Int) := by
            simp only [Int.natCast_add, Int.natCast_one, Int.mul_add, Int.mul_one, Int.add_assoc]
          rw [chunks, World.schreibBytes_append, zahlZuBytes_length]
          simp only [show ((8 : Nat) : Int) = (8 : Int) from rfl]
          rw [advance]
          exact world2
      · simp only [dite_eq_right more, Option.some.injEq, Prod.mk.injEq] at restMade
        obtain ⟨rfl, rfl⟩ := restMade
        refine ⟨m1, ?_, ch1, env1, ?_⟩
        · simpa only [leading, List.length_append, List.length_singleton, List.length_nil, Nat.add_zero]
            using run1
        · simpa only [Nat.min_eq_right (by omega : n ≤ 8), zahlZuBytes_limb n (by omega)] using world1

end Gabbro.Stage0.Senke
