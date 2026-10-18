import Grammatik.Code.Lower.Expr

/-
  File:      Grammatik/Code/Refine/Frag.lean
  Subject:   TRACK L, PHASE L1 -- THE BUILDING BLOCKS OF THE EXPRESSION REFINEMENT: what each
             small piece of lowered code does when `seqI` runs it.

  `Frag m rs r c v` says: the lowered fragment `c = (code, operand, next)`, started with registers
  `rs` in memory `m`, `r` being the first free register, runs (`seqI`) to a register file `rs'`,
  leaves the memory alone, defines only registers from `r` up, uses no register beyond `next`
  and its operand evaluates to `v`.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration Wert)

/-- An operand reads no register from `r` up. -/
def OpdLt (o : Opd) (r : Nat) : Prop := ∀ x, o = Opd.reg x → x < r

theorem ev_agree {rs rs' : Regs} {r : Nat} (h : ∀ x, x < r → rs' x = rs x) {o : Opd}
    (ho : OpdLt o r) : o.ev rs' = o.ev rs := by
  cases o with
  | reg x => exact h x (ho x rfl)
  | _ => rfl

def Frag (m : Mem) (rs : Regs) (r : Nat) (c : LR) (v : Val) : Prop :=
  ∃ rs', seqI c.1 m rs = some (m, rs') ∧ r ≤ c.2.2 ∧ (∀ x, x < r → rs' x = rs x) ∧
    OpdLt c.2.1 c.2.2 ∧ c.2.1.ev rs' = some v

theorem opdlt_reg (r n : Nat) (h : r < n) : OpdLt (.reg r) n := by
  intro x hx
  cases hx
  exact h

theorem seqI_append (c1 c2 : List Instr) (m : Mem) (rs : Regs) :
    seqI (c1 ++ c2) m rs = (seqI c1 m rs).bind fun p => seqI c2 p.1 p.2 := by
  induction c1 generalizing m rs with
  | nil => simp [seqI]
  | cons i is ih =>
      simp only [List.cons_append, seqI]
      cases stepI i m rs with
      | none => rfl
      | some p => exact ih p.1 p.2

theorem regs_set_ne (rs : Regs) (d x : Reg) (v : Val) (h : x ≠ d) : rs.set d v x = rs x := by
  simp [Regs.set, h]

theorem regs_set_same (rs : Regs) (d : Reg) (v : Val) : rs.set d v d = some v := by
  simp [Regs.set]

/-- Run a fragment, then a second one from the resulting registers. -/
theorem frag_trans {m : Mem} {rs rs1 : Regs} {r : Nat} {c1 c2 : LR} {v2 : Val}
    (hs : seqI c1.1 m rs = some (m, rs1)) (hr : r ≤ c1.2.2) (hag : ∀ x, x < r → rs1 x = rs x)
    (h2 : Frag m rs1 c1.2.2 c2 v2) : Frag m rs r (c1.1 ++ c2.1, c2.2.1, c2.2.2) v2 := by
  obtain ⟨rs2, hs2, hr2, hag2, hlt2, hev2⟩ := h2
  refine ⟨rs2, ?_, by show r ≤ c2.2.2; omega, fun x hx => ?_, hlt2, hev2⟩
  · rw [seqI_append, hs]; exact hs2
  · rw [hag2 x (by omega), hag x hx]

/-- A one-instruction fragment whose result is its register. -/
theorem frag_one (m : Mem) (rs : Regs) (r : Nat) (i : Instr) (v : Val)
    (h : stepI i m rs = some (m, rs.set r v)) : Frag m rs r ([i], .reg r, r + 1) v := by
  refine ⟨rs.set r v, ?_, by show r ≤ r + 1; omega, ?_, ?_, ?_⟩
  · simp [seqI, h]
  · intro x hx; exact regs_set_ne rs r x v (Nat.ne_of_lt hx)
  · exact opdlt_reg r (r + 1) (by omega)
  · simp [Opd.ev, regs_set_same]

/-- A constant needs no code. -/
theorem frag_const (m : Mem) (rs : Regs) (r : Nat) (o : Opd) (v : Val) (h : o.ev rs = some v)
    (hc : OpdLt o r) : Frag m rs r ([], o, r) v :=
  ⟨rs, rfl, Nat.le_refl _, fun _ _ => rfl, hc, h⟩

/-! ## Changing width -/

/-- `z` is representable in `w` bits, signed or unsigned. -/
def FitS (sg : Bool) (w : Nat) (z : Int) : Prop :=
  if sg then (0 < w ∧ -(2 ^ (w - 1)) ≤ z ∧ z < 2 ^ (w - 1)) else (0 ≤ z ∧ z < 2 ^ w)

theorem fitS_of_fits {lo hi : Int} {w : Nat} {z : Int} (hf : Ar.Fits lo hi w) (hw : 0 < w)
    (h1 : lo ≤ z) (h2 : z ≤ hi) : FitS (decide (lo < 0)) w z := by
  unfold Ar.Fits at hf
  unfold FitS
  by_cases hl : lo < 0
  · have : ¬ (0 ≤ lo) := by omega
    rw [if_neg this] at hf
    simp only [hl, decide_true, if_true]
    omega
  · have : 0 ≤ lo := by omega
    rw [if_pos this] at hf
    simp only [hl, decide_false, Bool.false_eq_true, if_false]
    omega

theorem cvt_frag (src dst : Nat) (sg : Bool) (o : Opd) (r : Nat) (m : Mem) (rs : Regs) (z : Int)
    (hv : o.ev rs = some (Val.ofInt src z)) (hfit : FitS sg src z) (hlt : OpdLt o r) :
    Frag m rs r (cvt src dst sg o r) (Val.ofInt dst z) := by
  unfold cvt
  by_cases h1 : src = dst
  · subst h1
    simp only [if_true]
    exact ⟨rs, rfl, Nat.le_refl _, fun _ _ => rfl, hlt, hv⟩
  · rw [if_neg h1]
    by_cases h2 : src < dst
    · rw [if_pos h2]
      apply frag_one
      cases sg
      · have ⟨h0, h1'⟩ : 0 ≤ z ∧ z < 2 ^ src := by simpa [FitS] using hfit
        simp [stepI, hv, Val.ofInt, Val.ty, Val.cast, Nat.le_of_lt h2,
          Ar.zext_ofInt (Nat.le_of_lt h2) h0 h1']
      · have ⟨h0, h1', h2'⟩ : 0 < src ∧ -(2 ^ (src - 1)) ≤ z ∧ z < 2 ^ (src - 1) := by
          simpa [FitS] using hfit
        simp [stepI, hv, Val.ofInt, Val.ty, Val.cast, Nat.le_of_lt h2,
          Ar.sext_ofInt (Nat.le_of_lt h2) h0 h1' h2']
    · rw [if_neg h2]
      apply frag_one
      simp [stepI, hv, Val.ofInt, Val.ty, Val.cast, show dst ≤ src by omega,
        Ar.trunc_ofInt z (show dst ≤ src by omega)]

/-- `cvtG` between two integer types, for a value of the source range. -/
theorem cvtG_frag {la ha lb hb : Int} {o : Opd} {r : Nat} {m : Mem} {rs : Regs} {z : Int}
    (hfa : Ar.Fits la ha 128) (h1 : la ≤ z) (h2 : z ≤ ha)
    (hv : o.ev rs = some (Val.ofInt (Ar.wid la ha) z)) (hlt : OpdLt o r) :
    ∃ c, cvtG (.int la ha) (.int lb hb) o r = some c ∧
      Frag m rs r c (Val.ofInt (Ar.wid lb hb) z) := by
  refine ⟨_, rfl, ?_⟩
  exact cvt_frag _ _ _ o r m rs z hv
    (fitS_of_fits (Ar.wid_fits hfa) (by show 0 < Ar.wid la ha; have := Ar.wid_pos la ha; omega) h1 h2) hlt

/-! ## Loads -/

theorem stepI_load {m : Mem} {rs : Regs} {d : Reg} {t : Ty} {p : Opd} {b : Nat} {o : Int} {v : Val}
    (hp : p.ev rs = some (.ptr b o)) (hl : m.load b o t = some v) :
    stepI (.load d t p) m rs = some (m, rs.set d v) := by
  simp [stepI, hp, hl]

theorem stepI_trunc {m : Mem} {rs : Regs} {d : Reg} {s t : Nat} {a : Opd} {z : Int}
    (ha : a.ev rs = some (Val.ofInt s z)) (h : t ≤ s) :
    stepI (.cast d .trunc (.int s) (.int t) a) m rs = some (m, rs.set d (Val.ofInt t z)) := by
  simp [stepI, ha, Val.ofInt, Val.ty, Val.cast, h, Ar.trunc_ofInt]

theorem bool_ofInt (b : Bool) : Val.ofInt 1 (if b then 1 else 0) = Val.bool b := by
  cases b <;> rfl

variable {D : Deklaration}

theorem loadG_frag (lay : Layout D) (τ : GTy) (v : Wert D τ) (hs : supp τ = true) (p : Opd)
    (b : Nat) (o : Int) (m : Mem) (rs : Regs) (r : Nat) (hp : p.ev rs = some (.ptr b o))
    (hl : m.load b o (memTy τ) = some (encM lay τ v)) :
    ∃ c, loadG τ p r = some c ∧ Frag m rs r c (encR lay τ v) := by
  cases τ with
  | int lo hi =>
      have hf : Ar.Fits lo hi 128 := by simpa [supp] using hs
      refine ⟨([.load r (.int (Ar.wid lo hi)) p], .reg r, r + 1), by simp [loadG, hf], ?_⟩
      rw [show encR lay (Grammatik.Ty.int lo hi) v = Val.ofInt (Ar.wid lo hi) v.n from rfl]
      apply frag_one
      have hl' : m.load b o (.int (Ar.wid lo hi)) = some (Val.ofInt (Ar.wid lo hi) v.n) := by
        simpa [memTy, regTy, encM, encR] using hl
      exact stepI_load hp hl'
  | bool =>
      refine ⟨([.load r (.int 8) p, .cast (r + 1) .trunc (.int 8) (.int 1) (.reg r)],
        .reg (r + 1), r + 2), by simp [loadG], ?_⟩
      have hl' : m.load b o (.int 8) = some (Val.ofInt 8 (if (wbool v) then 1 else 0)) := by
        simpa [memTy, regTy, encM, encR] using hl
      have h1 := stepI_load (d := r) hp hl'
      have h2 : stepI (.cast (r + 1) .trunc (.int 8) (.int 1) (.reg r)) m
          (rs.set r (Val.ofInt 8 (if (wbool v) then 1 else 0)))
          = some (m, (rs.set r (Val.ofInt 8 (if (wbool v) then 1 else 0))).set (r + 1)
              (Val.ofInt 1 (if (wbool v) then 1 else 0))) :=
        stepI_trunc (by simp [Opd.ev, regs_set_same]) (by omega)
      refine ⟨(rs.set r (Val.ofInt 8 (if (wbool v) then 1 else 0))).set (r + 1)
          (Val.ofInt 1 (if (wbool v) then 1 else 0)), ?_, by show r ≤ r + 2; omega, ?_, ?_, ?_⟩
      · simp only [seqI, h1, h2]
      · intro x hx
        have e1 : x ≠ r + 1 := by omega
        have e2 : x ≠ r := by omega
        rw [regs_set_ne _ _ _ _ e1, regs_set_ne _ _ _ _ e2]
      · exact opdlt_reg (r + 1) (r + 2) (by omega)
      · simp [Opd.ev, regs_set_same, encR, bool_ofInt]
        rfl
  | ptr n rw =>
      refine ⟨([.load r .ptr p], .reg r, r + 1), by simp [loadG], ?_⟩
      apply frag_one
      have hl' : m.load b o .ptr = some (encR lay (.ptr n rw) v) := by
        simpa [memTy, regTy, encM] using hl
      exact stepI_load hp hl'
  | opt n =>
      have hf : Ar.Fits (-1) (n - 1) 128 := by simpa [supp] using hs
      refine ⟨([.load r (.int (Ar.wid (-1) (n - 1))) p], .reg r, r + 1), by simp [loadG, hf], ?_⟩
      apply frag_one
      have hl' : m.load b o (.int (Ar.wid (-1) (n - 1))) = some (encR lay (.opt n) v) := by
        simpa [memTy, regTy, encM] using hl
      exact stepI_load hp hl'
  | why n =>
      have hf : Ar.Fits 0 ((n : Int) - 1) 128 := by simpa [supp] using hs
      refine ⟨([.load r (.int (Ar.wid 0 ((n : Int) - 1))) p], .reg r, r + 1), by simp [loadG, hf], ?_⟩
      apply frag_one
      have hl' : m.load b o (.int (Ar.wid 0 ((n : Int) - 1))) = some (encR lay (.why n) v) := by
        simpa [memTy, regTy, encM] using hl
      exact stepI_load hp hl'
  | _ => simp [supp] at hs

/-! ## Addresses -/

theorem inBlock_of_load {m : Mem} {b : Nat} {o : Int} {t : Ty} {v : Val}
    (h : m.load b o t = some v) : inBlock m b o = true := by
  unfold Mem.load at h
  unfold inBlock
  cases hb : m.blks b with
  | none => simp [hb] at h
  | some blk =>
      simp only [hb] at h ⊢
      by_cases hi : Mem.inside blk.size o t
      · obtain ⟨h0, _, h2, _⟩ := hi
        simp only [decide_eq_true_eq]
        omega
      · simp [hi] at h

theorem wid_word : Ar.wid 0 (2 ^ Conf.wbits - 1) = Conf.wbits := by
  rcases Conf.wide with h | h <;> rw [h] <;> decide

theorem small_lt {n : Int} (h : n < 2 ^ (Conf.wbits - 2)) : n < 2 ^ (Conf.wbits - 1) :=
  Int.lt_of_lt_of_le h (Ar.two_pow_le (by have := Conf.wide; omega))

theorem toInt_ofInt_small {w : Nat} {n : Int} (hw : 0 < w) (h1 : 0 ≤ n) (h2 : n < 2 ^ (w - 1)) :
    (BitVec.ofInt w n).toInt = n :=
  BitVec.toInt_ofInt_eq_self hw (by have : (0 : Int) < 2 ^ (w - 1) := by
                                      exact_mod_cast Nat.two_pow_pos (w - 1)
                                    omega) h2

theorem slotAddr_frag (lay : Layout D) (hL : LayoutOk lay) (t : D.Tab) (f : D.Feld t)
    (hs : supp (D.typ t f) = true) (k : Int) (hk0 : 0 ≤ k) (hk1 : k < D.count t)
    (base oi : Opd) (r : Nat) (m : Mem) (rs : Regs)
    (hbase : base.ev rs = some (.ptr (lay.gblk t) 0)) (hbl : OpdLt base r)
    (hoi : oi.ev rs = some (Val.ofInt (Ar.wid 0 (D.count t - 1)) k)) (hil : OpdLt oi r)
    (hld : ∃ v, m.load (lay.gblk t) (lay.off t k f) (memTy (D.typ t f)) = some v)
    (c : LR) (h : slotAddr lay t f base (.int 0 (D.count t - 1)) oi r = some c) :
    Frag m rs r c (.ptr (lay.gblk t) (lay.off t k f)) := by
  unfold slotAddr at h
  split at h
  · rename_i hc
    obtain ⟨hc1, hc2⟩ := hc
    rcases hcv : cvt (twid (.int 0 (D.count t - 1))) (twid (.int 0 (2 ^ Conf.wbits - 1)))
        (tsgn (.int 0 (D.count t - 1))) oi r with ⟨cc, oo, rr⟩
    simp only [cvtG, hcv] at h
    obtain rfl := Option.some.inj h
    have hfit := Ar.wid_fits hc2
    have hw8 := Ar.wid_pos 0 (D.count t - 1)
    have hcvf := cvt_frag (twid (.int 0 (D.count t - 1))) (twid (.int 0 (2 ^ Conf.wbits - 1)))
      (tsgn (.int 0 (D.count t - 1))) oi r m rs k hoi
      (fitS_of_fits hfit (by omega) hk0 (by omega)) hil
    rw [hcv] at hcvf
    obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := hcvf
    have e64 : twid (.int 0 (2 ^ Conf.wbits - 1)) = Conf.wbits := wid_word
    rw [e64] at hev1
    obtain ⟨gty, hg⟩ := Layout.gep_eq hL t k f hs
    have hfs := hL.fsm t f
    have hkk : k < 2 ^ (Conf.wbits - 2) := Int.lt_of_lt_of_le hk1 hc1
    have i0 : ((Opd.int Conf.wbits 0).ev rs1).bind Val.idx = some 0 := by
      simp only [Opd.ev, Val.ofInt, Option.bind_some, Val.idx]
      rw [toInt_ofInt_small (by have := Conf.wide; omega) (Int.le_refl _)
        (small_lt (by exact_mod_cast Nat.two_pow_pos (Conf.wbits - 2)))]
    have i1 : (oo.ev rs1).bind Val.idx = some k := by
      rw [hev1]
      simp only [Val.ofInt, Option.bind_some, Val.idx]
      rw [toInt_ofInt_small (by have := Conf.wide; omega) hk0 (small_lt hkk)]
    have i2 : ((Opd.int Conf.wbits (lay.fidx t f)).ev rs1).bind Val.idx = some (lay.fidx t f : Int) := by
      simp only [Opd.ev, Val.ofInt, Option.bind_some, Val.idx]
      rw [toInt_ofInt_small (by have := Conf.wide; omega) (Int.natCast_nonneg _)
        (small_lt (by exact_mod_cast hfs))]
    have hidx : ([Opd.int Conf.wbits 0, oo, Opd.int Conf.wbits (lay.fidx t f)].mapM
        (fun i => (i.ev rs1).bind Val.idx)) = some [0, k, (lay.fidx t f : Int)] := by
      simp [List.mapM_cons, List.mapM_nil, i0, i1, i2]
    have hstep : stepI (.gep rr (lay.tty t) base [.int Conf.wbits 0, oo, .int Conf.wbits (lay.fidx t f)] true) m rs1
        = some (m, rs1.set rr (.ptr (lay.gblk t) (lay.off t k f))) := by
      have hb1 : base.ev rs1 = some (.ptr (lay.gblk t) 0) := by
        rw [ev_agree hag1 hbl]; exact hbase
      obtain ⟨v, hv⟩ := hld
      have hin := inBlock_of_load hv
      simp only [stepI, hb1, hidx, hg]
      simp [Int.zero_add, hin]
    have h2 := frag_one m rs1 rr (.gep rr (lay.tty t) base [.int Conf.wbits 0, oo, .int Conf.wbits (lay.fidx t f)] true)
      (.ptr (lay.gblk t) (lay.off t k f)) hstep
    have := frag_trans (c1 := (cc, oo, rr)) (c2 := ([.gep rr (lay.tty t) base
      [.int Conf.wbits 0, oo, .int Conf.wbits (lay.fidx t f)] true], .reg rr, rr + 1)) hs1 hr1 hag1 h2
    exact this
  · simp at h

/-! ## Binary operations and comparisons -/

theorem val_bin_add (W : Nat) (a b : Int) :
    Val.bin .add W (Val.ofInt W a) (Val.ofInt W b) = some (Val.ofInt W (a + b)) := by
  simp [Val.bin, BinOp.ap, Val.ofInt, Ar.add_ofInt]

theorem val_bin_sub (W : Nat) (a b : Int) :
    Val.bin .sub W (Val.ofInt W a) (Val.ofInt W b) = some (Val.ofInt W (a - b)) := by
  simp [Val.bin, BinOp.ap, Val.ofInt, Ar.sub_ofInt]

theorem val_bin_mul (W : Nat) (a b : Int) :
    Val.bin .mul W (Val.ofInt W a) (Val.ofInt W b) = some (Val.ofInt W (a * b)) := by
  simp [Val.bin, BinOp.ap, Val.ofInt, Ar.mul_ofInt]

/-- **A binary integer operation**: both operands moved to the width of the result, then the
    instruction; the result is the exact result, encoded. -/
theorem binRest_frag (op : BinOp) (zf : Int → Int → Int)
    (hop : ∀ W a b, Val.bin op W (Val.ofInt W a) (Val.ofInt W b) = some (Val.ofInt W (zf a b)))
    {la ha lb hb lo hi : Int} (za zb : Int) (hfa : Ar.Fits la ha 128) (hfb : Ar.Fits lb hb 128)
    (h1 : la ≤ za) (h2 : za ≤ ha) (h3 : lb ≤ zb) (h4 : zb ≤ hb)
    (oa ob : Opd) (r : Nat) (m : Mem) (rs : Regs)
    (hoa : oa.ev rs = some (Val.ofInt (Ar.wid la ha) za))
    (hob : ob.ev rs = some (Val.ofInt (Ar.wid lb hb) zb))
    (hla : OpdLt oa r) (hlb : OpdLt ob r) (c : LR)
    (h : binRest op (.int lo hi) (.int la ha) (.int lb hb) oa ob r = some c) :
    Frag m rs r c (Val.ofInt (Ar.wid lo hi) (zf za zb)) := by
  unfold binRest at h
  simp only [cvtG] at h
  rcases hc1 : cvt (twid (.int la ha)) (twid (.int lo hi)) (tsgn (.int la ha)) oa r with ⟨c1, oa', r1⟩
  rcases hc2 : cvt (twid (.int lb hb)) (twid (.int lo hi)) (tsgn (.int lb hb)) ob r1 with ⟨c2, ob', r2⟩
  simp only [hc1, hc2] at h
  split at h
  · rename_i hfit
    obtain rfl := Option.some.inj h
    have f1 := cvt_frag (twid (.int la ha)) (twid (.int lo hi)) (tsgn (.int la ha)) oa r m rs za hoa
      (fitS_of_fits (Ar.wid_fits hfa) (by have := Ar.wid_pos la ha; show 0 < Ar.wid la ha; omega) h1 h2) hla
    rw [hc1] at f1
    obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := f1
    have hob1 : ob.ev rs1 = some (Val.ofInt (Ar.wid lb hb) zb) := by
      rw [ev_agree hag1 hlb]; exact hob
    have f2 := cvt_frag (twid (.int lb hb)) (twid (.int lo hi)) (tsgn (.int lb hb)) ob r1 m rs1 zb hob1
      (fitS_of_fits (Ar.wid_fits hfb) (by have := Ar.wid_pos lb hb; show 0 < Ar.wid lb hb; omega) h3 h4)
      (fun x hx => by have h5 : (x : Nat) < r := hlb x hx; have hr1' : r ≤ r1 := hr1; exact Nat.lt_of_lt_of_le h5 hr1')
    rw [hc2] at f2
    obtain ⟨rs2, hs2, hr2, hag2, hlt2, hev2⟩ := f2
    have hev1' : oa'.ev rs2 = some (Val.ofInt (Ar.wid lo hi) za) := by
      rw [ev_agree hag2 hlt1]; exact hev1
    have hstep : stepI (.bin r2 op (twid (.int lo hi)) oa' ob') m rs2
        = some (m, rs2.set r2 (Val.ofInt (Ar.wid lo hi) (zf za zb))) := by
      simp only [stepI, hev1', hev2]
      have := hop (twid (.int lo hi)) za zb
      simp only [twid] at this ⊢
      simp [this]
    have h3' := frag_one m rs2 r2 _ _ hstep
    have t2 := frag_trans (c1 := (c2, ob', r2)) (c2 := ([.bin r2 op (twid (.int lo hi)) oa' ob'],
      .reg r2, r2 + 1)) (rs := rs1) (r := r1) hs2 hr2 hag2 h3'
    have t1 := frag_trans (c1 := (c1, oa', r1)) (c2 := (c2 ++ [.bin r2 op (twid (.int lo hi)) oa' ob'],
      .reg r2, r2 + 1)) hs1 hr1 hag1 (by simpa using t2)
    rw [List.append_assoc]
    exact t1
  · simp at h

theorem val_icmp_lt (sg : Bool) (W : Nat) (a b : Int) (hW : 0 < W) (ha : FitS sg W a) (hb : FitS sg W b) :
    Val.icmp (if sg then .slt else .ult) W (Val.ofInt W a) (Val.ofInt W b)
      = some (Val.bool (decide (a < b))) := by
  cases sg
  · obtain ⟨a0, a1⟩ : 0 ≤ a ∧ a < 2 ^ W := by simpa [FitS] using ha
    obtain ⟨b0, b1⟩ : 0 ≤ b ∧ b < 2 ^ W := by simpa [FitS] using hb
    simp [Val.icmp, IPred.ap, Val.ofInt, Ar.ult_ofInt a0 a1 b0 b1]
  · obtain ⟨_, a0, a1⟩ : 0 < W ∧ -(2 ^ (W - 1)) ≤ a ∧ a < 2 ^ (W - 1) := by simpa [FitS] using ha
    obtain ⟨_, b0, b1⟩ : 0 < W ∧ -(2 ^ (W - 1)) ≤ b ∧ b < 2 ^ (W - 1) := by simpa [FitS] using hb
    simp [Val.icmp, IPred.ap, Val.ofInt, Ar.slt_ofInt hW a0 a1 b0 b1]

theorem val_icmp_le (sg : Bool) (W : Nat) (a b : Int) (hW : 0 < W) (ha : FitS sg W a) (hb : FitS sg W b) :
    Val.icmp (if sg then .sle else .ule) W (Val.ofInt W a) (Val.ofInt W b)
      = some (Val.bool (decide (a ≤ b))) := by
  cases sg
  · obtain ⟨a0, a1⟩ : 0 ≤ a ∧ a < 2 ^ W := by simpa [FitS] using ha
    obtain ⟨b0, b1⟩ : 0 ≤ b ∧ b < 2 ^ W := by simpa [FitS] using hb
    simp [Val.icmp, IPred.ap, Val.ofInt, Ar.ule_ofInt a0 a1 b0 b1]
  · obtain ⟨_, a0, a1⟩ : 0 < W ∧ -(2 ^ (W - 1)) ≤ a ∧ a < 2 ^ (W - 1) := by simpa [FitS] using ha
    obtain ⟨_, b0, b1⟩ : 0 < W ∧ -(2 ^ (W - 1)) ≤ b ∧ b < 2 ^ (W - 1) := by simpa [FitS] using hb
    simp [Val.icmp, IPred.ap, Val.ofInt, Ar.sle_ofInt hW a0 a1 b0 b1]

theorem val_icmp_eq (sg : Bool) (W : Nat) (a b : Int) (hW : 0 < W) (ha : FitS sg W a) (hb : FitS sg W b) :
    Val.icmp (if sg then .eq else .eq) W (Val.ofInt W a) (Val.ofInt W b)
      = some (Val.bool (decide (a = b))) := by
  have key : BitVec.ofInt W a = BitVec.ofInt W b ↔ a = b := by
    cases sg
    · obtain ⟨a0, a1⟩ : 0 ≤ a ∧ a < 2 ^ W := by simpa [FitS] using ha
      obtain ⟨b0, b1⟩ : 0 ≤ b ∧ b < 2 ^ W := by simpa [FitS] using hb
      exact Ar.ofInt_inj (lo := 0) (hi := 2 ^ W - 1) (by unfold Ar.Fits; simp; omega) hW
        a0 (by omega) b0 (by omega)
    · obtain ⟨_, a0, a1⟩ : 0 < W ∧ -(2 ^ (W - 1)) ≤ a ∧ a < 2 ^ (W - 1) := by simpa [FitS] using ha
      obtain ⟨_, b0, b1⟩ : 0 < W ∧ -(2 ^ (W - 1)) ≤ b ∧ b < 2 ^ (W - 1) := by simpa [FitS] using hb
      exact Ar.ofInt_inj (lo := -(2 ^ (W - 1))) (hi := 2 ^ (W - 1) - 1)
        (by unfold Ar.Fits
            have : ¬ (0 ≤ -(2 : Int) ^ (W - 1)) := by
              have : (0 : Int) < 2 ^ (W - 1) := by exact_mod_cast Nat.two_pow_pos (W - 1)
              omega
            rw [if_neg this]; omega) hW a0 (by omega) b0 (by omega)
  simp [Val.icmp, IPred.ap, Val.ofInt, key]

/-- **A comparison**: both operands moved to the width of the joined range, compared. -/
theorem cmpRest_frag (pu ps : IPred) (P : Int → Int → Prop) [DecidableRel P]
    (hic : ∀ (sg : Bool) (W : Nat) (a b : Int), 0 < W → FitS sg W a → FitS sg W b →
      Val.icmp (if sg then ps else pu) W (Val.ofInt W a) (Val.ofInt W b)
        = some (Val.bool (decide (P a b))))
    {la ha lb hb : Int} (za zb : Int) (hfa : Ar.Fits la ha 128) (hfb : Ar.Fits lb hb 128)
    (h1 : la ≤ za) (h2 : za ≤ ha) (h3 : lb ≤ zb) (h4 : zb ≤ hb)
    (oa ob : Opd) (r : Nat) (m : Mem) (rs : Regs)
    (hoa : oa.ev rs = some (Val.ofInt (Ar.wid la ha) za))
    (hob : ob.ev rs = some (Val.ofInt (Ar.wid lb hb) zb))
    (hla : OpdLt oa r) (hlb : OpdLt ob r) (c : LR)
    (h : cmpRest pu ps (.int la ha) (.int lb hb) oa ob r = some c) :
    Frag m rs r c (Val.bool (decide (P za zb))) := by
  unfold cmpRest at h
  simp only [joinT, cvtG] at h
  rcases hc1 : cvt (twid (.int la ha)) (twid (.int (min la lb) (max ha hb))) (tsgn (.int la ha)) oa r
    with ⟨c1, oa', r1⟩
  rcases hc2 : cvt (twid (.int lb hb)) (twid (.int (min la lb) (max ha hb))) (tsgn (.int lb hb)) ob r1
    with ⟨c2, ob', r2⟩
  simp only [hc1, hc2] at h
  split at h
  · rename_i hfit
    obtain rfl := Option.some.inj h
    have hfj : Ar.Fits (min la lb) (max ha hb) 128 := by simpa [fitsT] using hfit
    have hwj := Ar.wid_fits hfj
    have hwp := Ar.wid_pos (min la lb) (max ha hb)
    have f1 := cvt_frag (twid (.int la ha)) (twid (.int (min la lb) (max ha hb))) (tsgn (.int la ha))
      oa r m rs za hoa
      (fitS_of_fits (Ar.wid_fits hfa) (by have := Ar.wid_pos la ha; show 0 < Ar.wid la ha; omega) h1 h2) hla
    rw [hc1] at f1
    obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := f1
    have hob1 : ob.ev rs1 = some (Val.ofInt (Ar.wid lb hb) zb) := by
      rw [ev_agree hag1 hlb]; exact hob
    have f2 := cvt_frag (twid (.int lb hb)) (twid (.int (min la lb) (max ha hb))) (tsgn (.int lb hb))
      ob r1 m rs1 zb hob1
      (fitS_of_fits (Ar.wid_fits hfb) (by have := Ar.wid_pos lb hb; show 0 < Ar.wid lb hb; omega) h3 h4)
      (fun x hx => by have h5 : (x : Nat) < r := hlb x hx; have hr1' : r ≤ r1 := hr1; exact Nat.lt_of_lt_of_le h5 hr1')
    rw [hc2] at f2
    obtain ⟨rs2, hs2, hr2, hag2, hlt2, hev2⟩ := f2
    have hev1' : oa'.ev rs2 = some (Val.ofInt (Ar.wid (min la lb) (max ha hb)) za) := by
      rw [ev_agree hag2 hlt1]; exact hev1
    have fa := fitS_of_fits hwj (by omega) (show min la lb ≤ za by omega) (show za ≤ max ha hb by omega)
    have fb := fitS_of_fits hwj (by omega) (show min la lb ≤ zb by omega) (show zb ≤ max ha hb by omega)
    have hstep : stepI (.icmp r2 (if tsgn (.int (min la lb) (max ha hb)) then ps else pu)
        (twid (.int (min la lb) (max ha hb))) oa' ob') m rs2
        = some (m, rs2.set r2 (Val.bool (decide (P za zb)))) := by
      simp only [stepI, hev1', hev2]
      have := hic (tsgn (.int (min la lb) (max ha hb))) (Ar.wid (min la lb) (max ha hb)) za zb
        (by omega) (by simpa [tsgn] using fa) (by simpa [tsgn] using fb)
      simp only [twid] at this ⊢
      simp [this]
    have h3' := frag_one m rs2 r2 _ _ hstep
    have t2 := frag_trans (c1 := (c2, ob', r2)) (rs := rs1) (r := r1)
      (c2 := ([.icmp r2 (if tsgn (.int (min la lb) (max ha hb)) then ps else pu)
        (twid (.int (min la lb) (max ha hb))) oa' ob'], .reg r2, r2 + 1)) hs2 hr2 hag2 h3'
    have t1 := frag_trans (c1 := (c1, oa', r1)) (rs := rs) (r := r) hs1 hr1 hag1
      (c2 := (c2 ++ [.icmp r2 (if tsgn (.int (min la lb) (max ha hb)) then ps else pu)
        (twid (.int (min la lb) (max ha hb))) oa' ob'], .reg r2, r2 + 1)) (by simpa using t2)
    rw [List.append_assoc]
    exact t1
  · simp at h

theorem val_bin_and (x y : Bool) :
    Val.bin .and 1 (Val.bool x) (Val.bool y) = some (Val.bool (x && y)) := by
  cases x <;> cases y <;> decide

theorem val_bin_or (x y : Bool) :
    Val.bin .or 1 (Val.bool x) (Val.bool y) = some (Val.bool (x || y)) := by
  cases x <;> cases y <;> decide

theorem val_bin_not (x : Bool) :
    Val.bin .xor 1 (Val.bool x) (Val.ofInt 1 1) = some (Val.bool (!x)) := by
  cases x <;> decide

/-- A lowered binary operation always has a result type that fits. -/
theorem binRest_fits {op : BinOp} {τ σa σb : GTy} {oa ob : Opd} {r : Nat} {c : LR}
    (h : binRest op τ σa σb oa ob r = some c) : fitsT τ = true := by
  unfold binRest at h
  split at h
  · split at h
    · split at h
      · rename_i hf; exact hf
      · simp at h
    · simp at h
  · simp at h

/-! ## Division and remainder -/

theorem val_bin_udiv (W : Nat) (a b : Int) (ha0 : 0 ≤ a) (ha1 : a < 2 ^ W) (hb0 : 0 < b) (hb1 : b < 2 ^ W) :
    Val.bin .udiv W (Val.ofInt W a) (Val.ofInt W b) = some (Val.ofInt W (Int.tdiv a b)) := by
  have hne : BitVec.ofInt W b ≠ 0 := by
    intro h
    have := congrArg BitVec.toNat h
    rw [Ar.toNat_ofInt_lt (by omega) hb1] at this
    simp at this
    omega
  simp only [Val.bin, BinOp.ap, Val.ofInt, hne, if_false, Option.map_some]
  simp only [dite_true]
  rw [Ar.udiv_ofInt ha0 ha1 (by omega) hb1, Gabbro.Grammatik.Int.tdiv_eq_ediv_nonneg ha0]

theorem val_bin_urem (W : Nat) (a b : Int) (ha0 : 0 ≤ a) (ha1 : a < 2 ^ W) (hb0 : 0 < b) (hb1 : b < 2 ^ W) :
    Val.bin .urem W (Val.ofInt W a) (Val.ofInt W b) = some (Val.ofInt W (Int.tmod a b)) := by
  have hne : BitVec.ofInt W b ≠ 0 := by
    intro h
    have := congrArg BitVec.toNat h
    rw [Ar.toNat_ofInt_lt (by omega) hb1] at this
    simp at this
    omega
  simp only [Val.bin, BinOp.ap, Val.ofInt, hne, if_false, Option.map_some]
  simp only [dite_true]
  rw [Ar.urem_ofInt ha0 ha1 (by omega) hb1, Int.tmod_eq_emod_of_nonneg ha0]

theorem divRest_fits {op : BinOp} {τ σa σb : GTy} {oa ob : Opd} {r : Nat} {c : LR}
    (h : divRest op τ σa σb oa ob r = some c) : fitsT τ = true := by
  unfold divRest at h
  split at h
  · rename_i la ha lb hb
    simp only at h
    rcases hc1 : cvtG (.int la ha) (joinT (.int la ha) (.int lb hb)) oa r with _ | ⟨c1, oa', r1⟩
    · simp [hc1] at h
    simp only [hc1] at h
    rcases hc2 : cvtG (.int lb hb) (joinT (.int la ha) (.int lb hb)) ob r1 with _ | ⟨c2, ob', r2⟩
    · simp [hc2] at h
    simp only [hc2] at h
    split at h
    · rename_i hf
      exact ((Bool.and_eq_true _ _).mp hf).2
    · simp at h
  · simp at h

/-- **A division or remainder of non-negative numbers**: both operands at the width of the joined
    range, the instruction (whose precondition, a nonzero divisor, is `1 <= lb`), the result moved to
    its own width. `zf` is the exact result, which is non-negative and below the joined bound. -/
theorem divRest_frag (op : BinOp) (zf : Int → Int → Int)
    (hop : ∀ (W : Nat) (a b : Int), 0 ≤ a → a < 2 ^ W → 0 < b → b < 2 ^ W →
      Val.bin op W (Val.ofInt W a) (Val.ofInt W b) = some (Val.ofInt W (zf a b)))
    {la ha lb hb lo hi : Int} (za zb : Int) (hla0 : 0 ≤ la) (hlb1 : 1 ≤ lb)
    (hfa : Ar.Fits la ha 128) (hfb : Ar.Fits lb hb 128)
    (h1 : la ≤ za) (h2 : za ≤ ha) (h3 : lb ≤ zb) (h4 : zb ≤ hb) (hz0 : 0 ≤ zf za zb)
    (hz1 : zf za zb ≤ max ha hb)
    (oa ob : Opd) (r : Nat) (m : Mem) (rs : Regs)
    (hoa : oa.ev rs = some (Val.ofInt (Ar.wid la ha) za))
    (hob : ob.ev rs = some (Val.ofInt (Ar.wid lb hb) zb))
    (hla : OpdLt oa r) (hlb : OpdLt ob r) (c : LR)
    (h : divRest op (.int lo hi) (.int la ha) (.int lb hb) oa ob r = some c) :
    Frag m rs r c (Val.ofInt (Ar.wid lo hi) (zf za zb)) := by
  unfold divRest at h
  simp only [cvtG, joinT] at h
  rcases hc1 : cvt (twid (.int la ha)) (twid (.int (min la lb) (max ha hb))) (tsgn (.int la ha)) oa r with
    ⟨c1, oa', r1⟩
  rcases hc2 : cvt (twid (.int lb hb)) (twid (.int (min la lb) (max ha hb))) (tsgn (.int lb hb)) ob r1 with
    ⟨c2, ob', r2⟩
  simp only [hc1, hc2] at h
  split at h
  · rename_i hfit
    have hfj : Ar.Fits (min la lb) (max ha hb) 128 := by
      have := ((Bool.and_eq_true _ _).mp hfit).1
      simpa [fitsT] using this
    have hmin : 0 ≤ min la lb := by omega
    have hWj := Ar.wid_fits hfj
    have hWp : 0 < Ar.wid (min la lb) (max ha hb) := by
      have := Ar.wid_pos (min la lb) (max ha hb); omega
    have hbound : max ha hb < 2 ^ Ar.wid (min la lb) (max ha hb) := by
      have := hWj
      unfold Ar.Fits at this
      rw [if_pos hmin] at this
      exact this
    have f1 := cvt_frag (twid (.int la ha)) (twid (.int (min la lb) (max ha hb))) (tsgn (.int la ha)) oa r m rs za
      hoa (fitS_of_fits (Ar.wid_fits hfa) (by have := Ar.wid_pos la ha; show 0 < Ar.wid la ha; omega) h1 h2) hla
    rw [hc1] at f1
    obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := f1
    have hob1 : ob.ev rs1 = some (Val.ofInt (Ar.wid lb hb) zb) := by
      rw [ev_agree hag1 hlb]; exact hob
    have f2 := cvt_frag (twid (.int lb hb)) (twid (.int (min la lb) (max ha hb))) (tsgn (.int lb hb)) ob r1 m rs1 zb
      hob1 (fitS_of_fits (Ar.wid_fits hfb) (by have := Ar.wid_pos lb hb; show 0 < Ar.wid lb hb; omega) h3 h4)
      (fun x hx => by
        have h5 : (x : Nat) < r := hlb x hx
        have hr1' : r ≤ r1 := hr1
        exact Nat.lt_of_lt_of_le h5 hr1')
    rw [hc2] at f2
    obtain ⟨rs2, hs2, hr2, hag2, hlt2, hev2⟩ := f2
    have hev1' : oa'.ev rs2 = some (Val.ofInt (Ar.wid (min la lb) (max ha hb)) za) := by
      rw [ev_agree hag2 hlt1]; exact hev1
    have hstep : stepI (.bin r2 op (twid (.int (min la lb) (max ha hb))) oa' ob') m rs2
        = some (m, rs2.set r2 (Val.ofInt (Ar.wid (min la lb) (max ha hb)) (zf za zb))) := by
      simp only [stepI, hev1', hev2]
      have := hop (twid (.int (min la lb) (max ha hb))) za zb (by omega)
        (by have : za ≤ max ha hb := by omega
            show za < 2 ^ Ar.wid (min la lb) (max ha hb)
            omega)
        (by omega)
        (by have : zb ≤ max ha hb := by omega
            show zb < 2 ^ Ar.wid (min la lb) (max ha hb)
            omega)
      simp only [twid] at this ⊢
      simp [this]
    have tb := frag_one m rs2 r2 _ _ hstep
    rcases hc3 : cvt (twid (.int (min la lb) (max ha hb))) (twid (.int lo hi)) (tsgn (.int (min la lb) (max ha hb)))
      (.reg r2) (r2 + 1) with ⟨c3, o3, r3⟩
    simp only [hc3] at h
    obtain rfl := Option.some.inj h
    have f3 := cvt_frag (twid (.int (min la lb) (max ha hb))) (twid (.int lo hi))
      (tsgn (.int (min la lb) (max ha hb))) (.reg r2) (r2 + 1) m (rs2.set r2 (Val.ofInt
        (Ar.wid (min la lb) (max ha hb)) (zf za zb))) (zf za zb)
      (by simp [Opd.ev, regs_set_same, twid]) (by
        have hsg : tsgn (.int (min la lb) (max ha hb)) = false := by
          simp only [tsgn]
          simp [show ¬ (min la lb < 0) by omega]
        rw [hsg]
        show FitS false (twid (.int (min la lb) (max ha hb))) (zf za zb)
        simp only [FitS, twid, Bool.false_eq_true, if_false]
        exact ⟨hz0, by omega⟩)
      (opdlt_reg r2 (r2 + 1) (by omega))
    rw [hc3] at f3
    -- compose: c1, c2, the instruction, c3
    have t3 := frag_trans (c1 := ([.bin r2 op (twid (.int (min la lb) (max ha hb))) oa' ob'], .reg r2, r2 + 1))
      (c2 := (c3, o3, r3)) (m := m) (rs := rs2) (rs1 := rs2.set r2 (Val.ofInt (Ar.wid (min la lb) (max ha hb)) (zf za zb)))
      (r := r2) (by simp [seqI, hstep]) (by simp) (fun x hx => regs_set_ne rs2 r2 x _ (Nat.ne_of_lt hx))
      (by simpa using f3)
    have t2 := frag_trans (c1 := (c2, ob', r2)) (c2 := ([.bin r2 op (twid (.int (min la lb) (max ha hb))) oa' ob'] ++ c3, o3, r3))
      (rs := rs1) (r := r1) hs2 hr2 hag2 (by simpa using t3)
    have t1 := frag_trans (c1 := (c1, oa', r1)) (c2 := (c2 ++ ([.bin r2 op (twid (.int (min la lb) (max ha hb))) oa' ob'] ++ c3), o3, r3))
      hs1 hr1 hag1 (by simpa using t2)
    simpa [List.append_assoc, twid] using t1
  · simp at h

end Gabbro.Code.Lower
