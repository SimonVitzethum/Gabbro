/- Frame-slot borrowing for expression binders, including nested quantifiers. -/
import Stage0.Senke.Ausdruck.Quant.Frame

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration}

theorem quantBind_ok {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {n : Int} {k : Zahl 0 (n - 1)} {cb : List II} {P : Runner.W → Prop}
    (hk : lit32 k.n = true) (hd : frei Γ < d) (hK : d + 2 < K)
    (hp : Pre m pc fp K d (quantBindC (frei Γ) d k.n cb) ρ W)
    (ih : ∀ m pc, Pre m pc fp K (d + 2) cb (Env.cons (show Wert D (.index n) from k) ρ) W →
      Ok m pc fp K (d + 2) cb P) :
    Ok m pc fp K d (quantBindC (frei Γ) d k.n cb) P := by
  let s := frei Γ
  have hs : s < d := hd
  have h' : Pre m pc fp K d ([ci 2 (d + 1) s 0] ++ ([ci 1 s k.n 0] ++
      (cb ++ ([ci 2 s (d + 1) 0] ++ [ci 2 d (d + 2) 0])))) ρ W := by
    simpa [quantBindC, List.append_assoc, s] using hp
  obtain ⟨v, hv⟩ : ∃ v, m.rd64 (slot fp (BitVec.ofNat 64 s)) = some v := by
    refine ⟨BitVec.ofNat 64 (m.le (slot fp (BitVec.ofNat 64 s)) 8), ?_⟩
    simp only [Runner.Mem.rd64, hp.frame.rd s (by omega), ↓reduceIte]
  let m1 := write m (slot fp (BitVec.ofNat 64 (d + 1))) 8 v.toNat
  have a1 : Agree fp d K m m1 := agree_write hp.frame.room (by omega) (by omega) _
  have r1 : m1.rd64 (slot fp (BitVec.ofNat 64 (d + 1))) = some v := (wr_slot hp.frame (by omega) v).2.1
  have s1 := quant_mov (dst := d + 1) (src := s) hp.frame hp.small (by omega) (by omega) h'.left.code hv
  have h1 := h'.next a1 (Nat.le_refl _) (by omega)
  let m2 := write m1 (slot fp (BitVec.ofNat 64 s)) 8 (BitVec.ofInt 64 k.n).toNat
  have a2 : Agree fp s K m1 m2 := agree_write h1.frame.room (by omega) (by omega) _
  have r2 : m2.rd64 (slot fp (BitVec.ofNat 64 s)) = some (BitVec.ofInt 64 k.n) :=
    (wr_slot h1.frame (by omega) (BitVec.ofInt 64 k.n)).2.1
  have s2 := quant_lit h1.frame hp.small (by omega) h1.left.code hk
  have h1s : Pre m1 _ fp K s ([ci 1 s k.n 0] ++ (cb ++ ([ci 2 s (d + 1) 0] ++ [ci 2 d (d + 2) 0]))) ρ W :=
    { h1 with ctx := Nat.le_refl _ }
  have h2 := h1s.next a2 (show s ≤ d + 2 by omega) (by omega)
  have he : EnvAt m2 fp (Env.cons (show Wert D (.index n) from k) ρ) := envAt_cons h2.env r2 rfl
  have hb : Pre m2 _ fp K (d + 2) cb (Env.cons (show Wert D (.index n) from k) ρ) W :=
    { h2.left with ctx := by simp only [frei, List.length_cons] at *; omega, env := he }
  obtain ⟨m3, s3, a3, w, rw3, pw⟩ := ih m2 _ hb
  have h3 := h2.next a3 (Nat.le_refl _) (by omega)
  have rs3 : m3.rd64 (slot fp (BitVec.ofNat 64 (d + 1))) = some v := by
    rw [agree_rd_low a3 h2.frame.room (by omega) (by omega)]
    rw [rd64_write_far (slot_far h1.frame.room (by omega) (by omega) (by omega))]
    exact r1
  let m4 := write m3 (slot fp (BitVec.ofNat 64 s)) 8 v.toNat
  have a4 : Agree fp s K m3 m4 := agree_write h3.frame.room (by omega) (by omega) _
  have s4 := quant_mov (dst := s) (src := d + 1) h3.frame hp.small (by omega) (by omega) h3.left.code rs3
  have h3s : Pre m3 _ fp K s ([ci 2 s (d + 1) 0] ++ [ci 2 d (d + 2) 0]) ρ W :=
    { h3 with ctx := Nat.le_refl _ }
  have h4 := h3s.next a4 (show s ≤ d by omega) (by omega)
  have rw4 : m4.rd64 (slot fp (BitVec.ofNat 64 (d + 2))) = some w := by
    rw [rd64_write_far (slot_far h3.frame.room (by omega) (by omega) (by omega))]; exact rw3
  obtain ⟨m5, s5, a5, w5, rw5, pw5⟩ := (mov_ok h4 (by omega) (by omega) rw4).mono (fun _ h => h ▸ pw)
  have ar : Agree fp d K m m4 := quant_restore hp.frame hs (by omega) hv (by
    intro x hx hb
    rw [a3.b x (by unfold inSlots at *; omega)]
    have hroom : fp.toNat + 8 * (s + 1) ≤ 2 ^ 64 := by have := hp.frame.room; omega
    rw [(agree_write (K := s + 1) hroom (lo := s) (by omega) (by omega) (BitVec.ofInt 64 k.n).toNat).b x hb]
    exact a1.b x hx) (a3.rd.trans (a2.rd.trans a1.rd)) (a3.wr.trans (a2.wr.trans a1.wr))
  refine ⟨m5, ?_, ar.trans a5, w5, rw5, pw5⟩
  have e4 : ∀ p : Runner.W, p + 16 = p + BitVec.ofNat 64 (16 * 1) := fun _ => rfl
  simp only [List.length_singleton] at s1 s2 s3 s4 s5
  rw [e4] at s1 s2 s4
  have ss := s1.trans (s2.trans (s3.trans (s4.trans s5)))
  refine star_cast ss rfl ?_
  simp only [T.mk.injEq, and_true, quantBindC, List.length_append, List.length_cons, List.length_nil, pc_add]

end Gabbro.Stage0.Senke
