/- Descending induction for the actual long-string scan code. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Frame.String.OrderAlu
public import Stage0.Senke.Ausdruck.Aggregat.Frame.StringTakeOka
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem

def StringSlots (s : Nat → Runner.W) (a n : Nat) (bs : List (Zahl 0 255)) : Prop :=
  s a = BitVec.ofNat 64 bs.length ∧ ∀ j, j < n →
    s (a + 1 + j) = BitVec.ofInt 64 ((bs[j]?).getD ⟨0, by omega, by omega⟩).n

theorem StringSlots.low {K lo a n : Nat} {code : List II}
    (admitted : ∀ i ∈ code, AluIns K lo i) (ha : a + n + 1 ≤ lo)
    (s : Nat → Runner.W) (bs : List (Zahl 0 255)) (h : StringSlots s a n bs) :
    StringSlots (aluRun code s) a n bs := by
  constructor
  · rw [aluRun_low admitted s (by omega)]; exact h.1
  · intro j hj
    rw [aluRun_low admitted s (by omega)]; exact h.2 j hj

theorem keyAt_bound (bs : List (Zahl 0 255)) (j : Nat) : keyAt (bs.map (·.n)) j < 2 ^ 64 := by
  rw [keyAt_byte]
  split
  · have := ((bs[j]?).getD ⟨0, by omega, by omega⟩).lo_le
    have := ((bs[j]?).getD ⟨0, by omega, by omega⟩).le_hi
    omega
  · decide

/-- Each iteration computes the next suffix flag before descending to the smaller
    byte index. All operand span words survive the comparison scratch writes. -/
theorem stringScan_value {K n q a b acc : Nat}
    (hn : n < 2 ^ 31) (hq : q < 2 ^ 31)
    (ha : a + n + 1 ≤ acc) (hb : b + q + 1 ≤ acc) (hK : acc + 5 ≤ K)
    (as bs : List (Zahl 0 255)) (la : as.length ≤ n) (lb : bs.length ≤ q) :
    ∀ (k : Nat) (s : Nat → Runner.W) (r : Bool),
      StringSlots s a n as → StringSlots s b q bs → s acc = Runner.IR.bool r →
      aluRun (stringScanC k n q a b acc) s acc =
        Runner.IR.bool (keyScan k (as.map (·.n)) (bs.map (·.n)) r) := by
  intro k
  induction k with
  | zero => intro s r _ _ read; exact read
  | succ k ih =>
    intro s r sa sb rr
    let cx := stringKeyC n a k (acc + 1) (acc + 3)
    let cy := stringKeyC q b k (acc + 2) (acc + 3)
    let cc := stringCompareC (acc + 1) (acc + 2) acc (acc + 3)
    have ax : ∀ i ∈ cx, AluIns K (acc + 1) i :=
      stringKey_admitted hn (by omega) (by omega) (by omega)
    have ay : ∀ i ∈ cy, AluIns K (acc + 2) i :=
      stringKey_admitted hq (by omega) (by omega) (by omega)
    have ac : ∀ i ∈ cc, AluIns K acc i := stringCompare_admitted hK
    let sx := aluRun cx s
    let sy := aluRun cy sx
    let sc := aluRun cc sy
    have sax : StringSlots sx a n as := sa.low ax (by omega) s as
    have sbx : StringSlots sx b q bs := sb.low ax (by omega) s bs
    have say : StringSlots sy a n as := sax.low ay (by omega) sx as
    have sby : StringSlots sy b q bs := sbx.low ay (by omega) sx bs
    have sac : StringSlots sc a n as := say.low ac ha sy as
    have sbc : StringSlots sc b q bs := sby.low ac hb sy bs
    have rx : sx (acc + 1) = BitVec.ofNat 64 (keyAt (as.map (·.n)) k) :=
      stringKey_value s as la hn (by omega) (by omega) sa.1 sa.2
    have ry : sy (acc + 2) = BitVec.ofNat 64 (keyAt (bs.map (·.n)) k) :=
      stringKey_value sx bs lb hq (by omega) (by omega) sbx.1 sbx.2
    have rx' : sy (acc + 1) = BitVec.ofNat 64 (keyAt (as.map (·.n)) k) := by
      rw [show sy (acc + 1) = sx (acc + 1) from aluRun_low ay sx (by omega)]
      exact rx
    have rr' : sy acc = Runner.IR.bool r := by
      rw [show sy acc = sx acc from aluRun_low ay sx (by omega),
        show sx acc = s acc from aluRun_low ax s (by omega)]
      exact rr
    have rc : sc acc = Runner.IR.bool
        (scanStep (keyAt (as.map (·.n)) k) (keyAt (bs.map (·.n)) k) r) :=
      stringCompare_value acc sy _ _ r (keyAt_bound as k) (keyAt_bound bs k) rx' ry rr'
    simp only [stringScanC, aluRun_append, keyScan]
    exact ih sc _ sac sbc rc

/-- Canonical long spans provide precisely the length and padded bytes read by the scan. -/
theorem stringSlots_of_span {D : Deklaration} {L : Lay D} {n a K : Nat}
    {m : Runner.Mem} {fp : Runner.W} (hn : 2 ≤ n)
    (frame : FrameOK m fp K) (fits : a + n + 1 ≤ K)
    (v : Wert D (.str n)) (span : ValueAt L m fp a (.str n) v) :
    StringSlots (slotVal m fp) a n v.1 := by
  constructor
  · have h := span_len_read hn v span
    rw [slotVal_rd frame (by omega)] at h
    exact Option.some.inj h
  · intro j hj
    have read := span.2 (j + 1)
      (by rw [encodeWords_length]; simp only [valueWords, if_neg (show ¬ n ≤ 1 by omega)]; omega)
    have get := strBytes_word v j hj
    have range : j + 1 < (encodeWords L (.str n) v).length := by
      rw [encodeWords_length]; simp only [valueWords, if_neg (show ¬ n ≤ 1 by omega)]; omega
    change (encodeWords L (.str n) v)[j + 1]? = _ at get
    rw [List.getElem?_eq_getElem range] at get
    rw [slotVal_rd frame (by omega)] at read
    rw [show a + 1 + j = a + (j + 1) by omega, Option.some.inj read, Option.some.inj get]
    simp only [strGetW, Int.natCast_nonneg, Int.toNat_natCast, ↓reduceIte]

end Gabbro.Stage0.Senke
