/- Complete table-cell reads and writes through a physical address computed from the
   index word and the full cell span. Both use the shared runtime-pointer transport and
   the canonical `ValueAt` relation; no scalar projection of a cell occurs. -/
import Stage0.Senke.Welt.Spans.StorePointer
import Stage0.Senke.Welt.Spans.Read
import Stage0.Senke.Ausdruck.Quant.OkSeq
namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D}

theorem WordsAt.agree_low {m m' : Runner.Mem} {fp : Runner.W} {lo K base : Nat} {ws : List Runner.W}
    (h : WordsAt m fp base ws) (changed : Agree fp lo K m m') (room : fp.toNat + 8 * K ≤ 2 ^ 64)
    (below : base + ws.length ≤ lo) (inside : lo ≤ K) : WordsAt m' fp base ws := by
  intro i hi
  rw [agree_rd_low changed room (by omega) inside]
  exact h i hi

theorem ValueAt.agree_low {m m' : Runner.Mem} {fp : Runner.W} {lo K base : Nat} {τ : Ty} {v : Wert D τ}
    (h : ValueAt L m fp base τ v) (changed : Agree fp lo K m m') (room : fp.toNat + 8 * K ≤ 2 ^ 64)
    (below : base + valueWords τ ≤ lo) (inside : lo ≤ K) : ValueAt L m' fp base τ v :=
  ⟨h.1, h.2.agree_low changed room (by simpa only [encodeWords_length] using below) inside⟩

theorem cellAddressC_top {L : Lay D} {t : D.Tab} {f : D.Feld t} {d : Nat} {index : List II × Nat}
    {c : List II} {top : Nat} (made : cellAddressC L t f d index = some (c, top)) :
    index.2 ≤ top ∧ d + 2 ≤ top := by
  unfold cellAddressC at made
  split at made
  · simp only [Option.some.injEq, Prod.mk.injEq] at made; omega
  · cases made

/-- The emitted address producer computes the checked physical address of the cell. -/
theorem cellAddressC_ok {Γ : Ctx} {t : D.Tab} {f : D.Feld t} {idx : Nat}
    {d : Nat} {index : List II × Nat} {c : List II} {top K reserved : Nat} {m : Runner.Mem}
    {pc fp : Runner.W} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (made : cellAddressC L t f d index = some (c, top)) (hK : top ≤ K)
    (ih : ∀ m pc, Pre L m pc fp K d index.1 ρ W reserved → Ok m pc fp K d index.1 (· = BitVec.ofNat 64 idx))
    (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (· = BitVec.ofNat 64 (L.elem t f idx)) := by
  unfold cellAddressC at made
  split at made
  · next fits =>
    simp only [Option.some.injEq, Prod.mk.injEq] at made
    obtain ⟨rfl, rfl⟩ := made
    have litStride : lit32 ((8 * valueWords (D.typ t f) : Nat) : Int) = true := by
      simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega
    have litCol : lit32 ((L.col t f : Nat) : Int) = true := by
      simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega
    have hq : Pre L m pc fp K d (index.1 ++ ([ci 1 (d + 1) ((8 * valueWords (D.typ t f) : Nat) : Int) 0,
        ci 5 d d (d + 1)] ++ [ci 1 (d + 1) ((L.col t f : Nat) : Int) 0, ci 3 d d (d + 1)])) ρ W reserved :=
      hp
    have small := hq.small
    have hc := ok_seq hq (ih m pc hq.left) (Pb := (· = BitVec.ofNat 64 (L.elem t f idx)))
      (fun m1 w1 hp1 r1 e1 => ok_seq hp1
        (binK_ok hp1.left r1 litStride rfl (by decide) rfl (by omega))
        (Pb := (· = BitVec.ofNat 64 (L.elem t f idx)))
        (fun m2 w2 hp2 r2 e2 => (binK_ok hp2 r2 litCol rfl (by decide) rfl (by omega)).mono fun x hx => by
          have e := addr_w (n := (idx : Int)) (s := 8 * valueWords (D.typ t f)) (c := L.col t f)
            (Int.natCast_nonneg _)
          rw [e2, e1] at hx
          rw [hx, ← BitVec.ofInt_natCast, e, Int.toNat_natCast]
          simp only [Lay.elem]) (by omega))
      (by omega)
    exact hc
  · cases made

end Gabbro.Stage0.Senke
