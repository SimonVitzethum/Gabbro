/-
  File:      stage0/Stage0/Senke/Bild/Mehr/Blind.lean
  Subject:   Every request tree of the IR is read-blind (multi-thread image theorem, package MT2). The memory models
             of the runner answer a read with the bytes read AND a second word the read leaves free (`SC L`: any
             `w`; the memory itself, `memAns`: zero). `Blind r`: every read in the tree `r` has width one, four or
             eight, and its continuation does not look at the second word -- `k (some (v, w)) = k (some (v, 0))`.
             Every read of the IR goes through `rd8`/`rd32`/`rd64`, which pass on the first word only, so the tree
             of every instruction is read-blind (`blind_step`), and so is every rest of it (`Blind.weiter`). With
             it, a read answered by `SC L` leads to the same thread state as the read answered by the memory
             (`Mehr/SCSchritt.lean`).
-/
module
public import Runner.IR.Step
@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Runner Runner.IR

/-- **A read-blind request tree.** -/
inductive Blind : Res T → Prop
  | next (t : T) : Blind (.next t)
  | fault : Blind .fault
  | unk : Blind .unk
  | ask {o : Op} {k : Ans → Res T} (hk : ∀ a, Blind (k a))
      (hrd : ∀ n x, o = .rd n x → (n = 1 ∨ n = 4 ∨ n = 8) ∧ ∀ v w, k (some (v, w)) = k (some (v, 0))) :
      Blind (.ask o k)

/-- Every rest of a read-blind tree is read-blind. -/
theorem Blind.weiter {o : Op} {k : Ans → Res T} (h : Blind (.ask o k)) (a : Ans) : Blind (k a) := by
  cases h with
  | ask hk _ => exact hk a

/-- A read of a read-blind tree has width one, four or eight and ignores the second word. -/
theorem Blind.lesen {o : Op} {k : Ans → Res T} (h : Blind (.ask o k)) {n : Nat} {x : W} (e : o = .rd n x) :
    (n = 1 ∨ n = 4 ∨ n = 8) ∧ ∀ v w, k (some (v, w)) = k (some (v, 0)) := by
  cases h with
  | ask _ hrd => exact hrd n x e

/-! ## The building blocks of the requests -/

theorem blind_opt {α : Type} (o : Option α) {f : α → Res T} (h : ∀ a, Blind (f a)) : Blind (opt o f) := by
  cases o with
  | none => exact Blind.fault
  | some a => exact h a

/-- A request that is not a read: only its rests matter. -/
theorem blind_ohneLesen {o : Op} {k : Ans → Res T} (ho : ∀ n x, o ≠ .rd n x) (hk : ∀ a, Blind (k a)) :
    Blind (.ask o k) :=
  .ask hk fun n x e => absurd e (ho n x)

theorem blind_wr {a v : W} {k : Ans → Res T} (hk : ∀ r, Blind (k r)) : Blind (.ask (.wr a v) k) :=
  blind_ohneLesen (fun _ _ hE => by cases hE) hk

theorem blind_sys {q : Req} {k : Ans → Res T} (hk : ∀ r, Blind (k r)) : Blind (.ask (.sys q) k) :=
  blind_ohneLesen (fun _ _ hE => by cases hE) hk

theorem blind_ite {c : Prop} [Decidable c] {a b : Res T} (ha : Blind a) (hb : Blind b) :
    Blind (if c then a else b) := by
  by_cases hc : c
  · rw [if_pos hc]
    exact ha
  · rw [if_neg hc]
    exact hb

theorem blind_rd8 (a : W) {f : W → Res T} (h : ∀ v, Blind (f v)) : Blind (rd8 a f) := by
  unfold rd8
  refine .ask (fun r => blind_opt r fun _ => h _) ?_
  intro n x e
  cases e
  exact ⟨Or.inl rfl, fun _ _ => rfl⟩

theorem blind_rd32 (a : W) {f : BitVec 32 → Res T} (h : ∀ v, Blind (f v)) : Blind (rd32 a f) := by
  unfold rd32
  refine .ask (fun r => blind_opt r fun _ => h _) ?_
  intro n x e
  cases e
  exact ⟨Or.inr (Or.inl rfl), fun _ _ => rfl⟩

theorem blind_rd64 (a : W) {f : W → Res T} (h : ∀ v, Blind (f v)) : Blind (rd64 a f) := by
  unfold rd64
  refine .ask (fun r => blind_opt r fun _ => h _) ?_
  intro n x e
  cases e
  exact ⟨Or.inr (Or.inr rfl), fun _ _ => rfl⟩

theorem blind_wr64 (a v : W) (s : T) : Blind (wr64 a v s) := by
  unfold wr64
  exact blind_wr fun r => blind_opt r fun _ => .next s

theorem blind_cas (a e n : W) {f : W → Res T} (h : ∀ v, Blind (f v)) : Blind (Runner.cas a e n f) := by
  unfold Runner.cas
  exact blind_ohneLesen (fun _ _ hE => by cases hE) fun r => blind_opt r fun _ => h _

/-- A native floating request is not a read. -/
theorem blind_fpR (kind : NativeFPOp) (a b : W) {f : W → Res T} (h : ∀ v, Blind (f v)) :
    Blind (Runner.fp kind a b f) := by
  unfold Runner.fp
  exact blind_ohneLesen (fun _ _ hE => by cases hE) fun r => blind_opt r fun _ => h _

theorem blind_fromU (format : FPFormat) (v : W) {f : W → Res T} (h : ∀ v, Blind (f v)) :
    Blind (fpFromUInt64 format v f) := by
  unfold fpFromUInt64
  split
  · exact blind_fpR _ _ _ fun _ => blind_fpR _ _ _ h
  · exact blind_fpR _ _ _ h

theorem blind_toI (format : FPFormat) (v : W) {f : W → Res T} (h : ∀ v, Blind (f v)) :
    Blind (fpToInt64 format v f) := by
  unfold fpToInt64
  split
  · exact h _
  · split
    · exact blind_fpR _ _ _ h
    · exact h _

theorem blind_toU (format : FPFormat) (v : W) {f : W → Res T} (h : ∀ v, Blind (f v)) :
    Blind (fpToUInt64 format v f) := by
  unfold fpToUInt64
  split
  · exact h _
  · split
    · split
      · exact blind_fpR _ _ _ h
      · exact blind_fpR _ _ _ fun _ => blind_fpR _ _ _ fun _ => h _
    · exact h _

theorem blind_fpSequence (kind : NativeFPOp) (a b : W) {f : W → Res T} (h : ∀ v, Blind (f v)) :
    Blind (fpSequence kind a b f) := by
  cases kind <;> first
    | exact blind_fpR _ _ _ h
    | exact h _
    | exact blind_fromU _ _ h
    | exact blind_toI _ _ h
    | exact blind_toU _ _ h

/-! ## The instruction helpers of the IR -/

theorem blind_f1 (t : T) {f : W → Res T} (h : ∀ v, Blind (f v)) : Blind (f1 t f) := by
  unfold f1
  apply blind_rd32
  intro v
  exact h _

theorem blind_f2 (t : T) {f : W → Res T} (h : ∀ v, Blind (f v)) : Blind (f2 t f) := by
  unfold f2
  apply blind_rd32
  intro v
  exact h _

theorem blind_f3 (t : T) {f : W → Res T} (h : ∀ v, Blind (f v)) : Blind (f3 t f) := by
  unfold f3
  apply blind_rd32
  intro v
  exact h _

theorem blind_ld (t : T) (i : W) {f : W → Res T} (h : ∀ v, Blind (f v)) : Blind (ld t i f) := by
  unfold ld
  exact blind_rd64 _ h

theorem blind_ret1 (t : T) (r : W) : Blind (ret1 t r) := by
  unfold ret1
  apply blind_f1
  intro d
  exact blind_wr64 _ _ _

theorem blind_bin (g : W → W → Option W) (t : T) : Blind (bin g t) := by
  unfold bin
  apply blind_f2
  intro a
  apply blind_ld
  intro va
  apply blind_f3
  intro b
  apply blind_ld
  intro vb
  apply blind_opt
  intro r
  exact blind_ret1 _ _

theorem blind_fpIR (kind : NativeFPOp) (t : T) : Blind (Runner.IR.fp kind t) := by
  unfold Runner.IR.fp
  apply blind_f2
  intro a
  apply blind_ld
  intro va
  apply blind_f3
  intro b
  apply blind_ld
  intro vb
  apply blind_fpSequence
  intro r
  exact blind_ret1 _ _

end Gabbro.Stage0.Senke.BildMehr
