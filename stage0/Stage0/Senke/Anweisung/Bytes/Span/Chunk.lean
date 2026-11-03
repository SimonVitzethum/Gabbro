/- One chunk transports captured operands into the existing scalar write kernel. -/
module
public import Stage0.Senke.Anweisung.Bytes.Span.Code
public import Stage0.Senke.Anweisung.Bytes.Span.WriteModel
public import Stage0.Senke.Anweisung.Bytes.Write
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- Capture bindings remain unchanged across the chunk. Only its fresh scalar
    value/index bindings and the existing byte kernel's scratch are written. -/
theorem putBytesChunk_ok {Γ : Ctx} {Λ : List (Res D)} {a b H : Int}
    {t : D.Tab} {f : D.Feld t} (hf : D.typ t f = .int 0 255) (lower : 0 ≤ a)
    {fp : Runner.W} {Ks K : Nat} (hW : WIn L fp Ks K)
    (z : Zahl 0 H) (k : Zahl a b) (ρ : Env D Γ) (q n : Nat)
    (positive : 0 < n) (small : n ≤ 8) (limb : q < valueWords (.int 0 H))
    (upper : b + 8 * q + n ≤ D.count t) {idx kernel : List II} {ti tk : Nat}
    (indexMade : lowE (reserved := reserved) L (chunkIndex (Γ := Γ) (Λ := Λ) a b H q)
      (frei (ByteCapture Γ a b H) reserved + 1) = some (idx, ti))
    (kernelMade : putBytesL L (Γ := ByteCapture Γ a b H) (Λ := Λ)
      t f (a + 8 * q) (b + 8 * q) (2 ^ 64 - 1) (by omega) reserved n 0 (by omega) = some (kernel, tk))
    (fits : max (frei (ByteCapture Γ a b H) reserved + 2) (max ti tk) ≤ Ks)
    {m : Runner.Mem} {pc : Runner.W} {σ : World D}
    (pre : PreS L m pc fp K (frei (ByteCapture Γ a b H) reserved)
      ([ci 2 (frei (ByteCapture Γ a b H) reserved) (frei Γ reserved + q) 0] ++ idx ++ kernel)
      (Env.cons k (Env.cons z ρ)) reserved) (world : WeltAt m L σ) :
    ∃ m', Star ⟨pc, fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (1 + idx.length + kernel.length)), fp⟩ m' ∧
      AgreeW L fp (frei (ByteCapture Γ a b H) reserved) K m m' ∧
      EnvAt L m' fp (Env.cons k (Env.cons z ρ)) reserved ∧
      WeltAt m' L (σ.schreibBytes t f hf Λ (k.n + 8 * q) (zahlZuBytes n (byteLimb z.n q).n)) := by
  let s := frei (ByteCapture Γ a b H) reserved
  let env : Env D (ByteCapture Γ a b H) := Env.cons k (Env.cons z ρ)
  let part := byteLimb z.n q
  let ki : Zahl (a + 8 * q) (b + 8 * q) := ⟨k.n + 8 * q, by have := k.lo_le; omega,
    by have := k.le_hi; omega⟩
  have hks := hW.ks
  have bound : b + 8 * q < 2 ^ 64 := by
    by_contra bad
    have cell := hW.lay.1 t f (b + 8 * q).toNat (L.bounded (by omega))
    have cw : valueWords (D.typ t f) = 1 := by rw [hf]; rfl
    simp only [Lay.elem, cw] at cell
    have small := hW.lay.2.2
    omega
  have iw : valueWords (.int (a + 8 * q) (b + 8 * q)) = 1 := integerWords_unsigned (by omega) bound
  have vw : valueWords (.int 0 (2 ^ 64 - 1)) = 1 := by decide
  have captureFits : frei Γ reserved + valueWords (.int 0 H) ≤ s := by
    dsimp only [s, frei, ByteCapture, contextWords_cons]
    have := valueWords_pos (.int a b)
    omega
  have stored := (pre.env (.int 0 H) (.there .here)).2 q
    (by rw [encodeWords_length]; exact limb)
  simp only [vslot_there, vslot_here, Env.get, encodeWords, integerEncoding_byteLimb] at stored
  have p : PreS L m pc fp K s
      ([ci 2 s (frei Γ reserved + q) 0] ++ (idx ++ kernel)) env reserved := by
    simpa only [s, env, List.append_assoc] using pre
  have movePre := PreS.welt p.left hks world hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, s1, ch1, w, read, equal⟩ := mov_ok movePre (by omega) (by omega) stored
  have enc : Enc L (.int 0 (2 ^ 64 - 1)) part w := equal
  have partAt : ValueAt L m1 fp s (.int 0 (2 ^ 64 - 1)) part := ValueAt.of_enc vw read enc
  have p1 := p.next ch1 (Nat.le_succ s) (by omega)
  have env1 : EnvAt L m1 fp (Env.cons part env) reserved := envAt_cons p1.env partAt
  have ip : PreS L m1 _ fp K (s + 1) idx (Env.cons part env) reserved :=
    ⟨by simp only [frei, contextWords_cons, vw]; have := p1.ctx; dsimp only [s] at *; omega,
      p1.small, p1.frame, p1.left.code, p1.left.far, env1, trivial, wstab_true _ _⟩
  have ipw := PreS.welt ip hks (movePre.wstab m m1 world (ch1.mono (Nat.zero_le _)))
    hW.lay (by have := hW.lo; omega)
  obtain ⟨m2, s2, ch2, indexAt⟩ := lowE_ok (same := by intro _; rfl) σ σ (fun _ h => h)
    hW.lay (chunkIndex (Γ := Γ) (Λ := Λ) a b H q) _ idx ti indexMade (by omega) m1 _ _ ipw
  have a2 := Agree.widen ch2 hks
  have p2 := p1.next a2 (Nat.le_refl _) (by omega)
  have env2 := envAt_agree env1 a2 p1.frame
    (by simp only [frei, contextWords_cons, vw]; dsimp only [s]; omega) (by omega)
  have kiAt : ValueAt L m2 fp (frei (.int 0 (2 ^ 64 - 1) :: ByteCapture Γ a b H) reserved)
      (.int (a + 8 * q) (b + 8 * q)) ki := by
    simpa only [chunkIndex, eval, Env.get, ki, frei, contextWords_cons, vw, Nat.add_assoc] using indexAt
  have env3 := envAt_cons env2 kiAt
  have kp : PreS L m2 _ fp K (s + 2) kernel (Env.cons ki (Env.cons part env)) reserved :=
    ⟨by simp only [frei, contextWords_cons, iw, vw]; dsimp only [s]; have := p2.ctx; omega,
      p2.small, p2.frame, p2.code, p2.far, env3, trivial, wstab_true _ _⟩
  have world2 := ipw.wstab m1 m2 ipw.welt (ch2.mono (Nat.zero_le _))
  obtain ⟨m3, s3, ch3, env4, world3⟩ := putBytesL_ok hf (by omega) hW part ki env
    (by have := part.le_hi; omega) n 0 (by omega) (by omega) kernel tk kernelMade (by omega)
    m2 _ σ (by simpa only [s] using kp) world2
  refine ⟨m3, ?_, (agreeW_of (ch1.trans (a2.mono (Nat.le_succ s)))).trans (ch3.mono (by omega)),
    envAt_tail (envAt_tail env4), ?_⟩
  · simpa only [List.length_append, List.length_singleton, pc_add, BitVec.add_assoc] using
      s1.trans (s2.trans s3)
  · simpa only [ki, dropBytes, Int.natCast_zero, Int.add_zero] using world3

end Gabbro.Stage0.Senke
