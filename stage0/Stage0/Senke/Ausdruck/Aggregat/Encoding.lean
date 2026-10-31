/- Canonical value words, shared by frames, world storage and call boundaries. -/
import Stage0.Senke.Welt.Lay
import Stage0.Senke.Ausdruck.Aggregat.Layout
import Stage0.Senke.Ausdruck.Aggregat.Wert
import Stage0.Senke.Ausdruck.Aggregat.Kopie

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
variable {D : Deklaration}

/-- Concatenated representations occupy consecutive spans without padding gaps. -/
theorem wordsAt_append {m : Runner.Mem} {fp : Runner.W} {base : Nat} (xs ys : List Runner.W) :
    WordsAt m fp base (xs ++ ys) ↔
      WordsAt m fp base xs ∧ WordsAt m fp (base + xs.length) ys := by
  constructor
  · intro words
    constructor
    · intro i hi
      have read := words i (by simp; omega)
      simpa only [List.getElem_append_left hi] using read
    · intro i hi
      have read := words (xs.length + i) (by simp; omega)
      simpa [List.getElem_append_right, Nat.add_assoc] using read
  · intro words i hi
    by_cases left : i < xs.length
    · simpa only [List.getElem_append_left left] using words.1 i left
    · have bound : i - xs.length < ys.length := by simp only [List.length_append] at hi; omega
      have read := words.2 (i - xs.length) bound
      have index : xs.length + (i - xs.length) = i := by omega
      rw [Nat.add_assoc, index] at read
      simpa only [List.getElem_append_right (by omega : xs.length ≤ i)] using read

/-- The payload's distance from the lower bound; a bare arm has offset zero. -/
def sumOff : (c : Option (Int × Int)) → Nutzlast c → Nat
  | none, _ => 0
  | some (lo, _), v => (v.n - lo).toNat

/-- The representation shared by frames, tables and globals. -/
def sumN {cs : List (Option (Int × Int))} (v : Wert D (.sum cs)) : Nat :=
  v.1.val + 256 * sumOff (cs.get v.1) v.2

/-- The number of an option: `-1` for absent, the index otherwise. -/
def optN {n : Int} : Option (Zahl 0 (n - 1)) → Int
  | Option.none => -1
  | Option.some k => k.n

/-- Little-endian two's-complement limbs, sign extended by Euclidean division. -/
def integerEncoding : Nat → Int → List Runner.W
  | 0, _ => []
  | n + 1, v => BitVec.ofInt 64 v :: integerEncoding n (v / 2 ^ 64)

@[simp] theorem integerEncoding_length (n : Nat) (v : Int) :
    (integerEncoding n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [integerEncoding, ih]

/-- Flatten elements in increasing index order. No pointer or allocation is introduced. -/
def elementEncoding : (n : Nat) → (Fin n → List Runner.W) → List Runner.W
  | 0, _ => []
  | n + 1, f => f ⟨0, by omega⟩ ++ elementEncoding n (fun i => f i.succ)

theorem elementEncoding_length (n width : Nat) (f : Fin n → List Runner.W)
    (hf : ∀ i, (f i).length = width) : (elementEncoding n f).length = n * width := by
  induction n with
  | zero => simp [elementEncoding]
  | succ n ih => simp only [elementEncoding, List.length_append, hf, ih _ (fun i => hf i.succ), Nat.succ_mul]; omega

/-- The unique canonical word sequence of a model value. Reference validity, floating
    well-formedness and world permissions remain separate proof obligations. -/
def encodeWords (L : Lay D) : (τ : Ty) → Wert D τ → List Runner.W
  | .int lo hi, v => integerEncoding (integerWords lo hi) v.n
  | .bool, v => [if wahr? (D := D) v then 1 else 0]
  | .opt n, v => if n ≤ 2 ^ 63 then [BitVec.ofInt 64 (optN v)] else
      match v with
      | none => 0 :: List.replicate (integerWords 0 (n - 1)) 0
      | some k => 1 :: integerEncoding (integerWords 0 (n - 1)) k.n
  | .why n, v => integerEncoding (valueWords (.why n)) v.val
  | .ref _, v => [BitVec.ofNat 64 v.zelle]
  | .fnptr _, v => [BitVec.ofNat 64 (L.fa v.1)]
  | .sum cs, v => if sumFits cs then [BitVec.ofNat 64 (sumN v)] else
      integerEncoding (integerWords 0 (cs.length - 1)) v.1.val ++
        integerEncoding (sumPayloadWords cs) (sumOff (cs.get v.1) v.2)
  | .arr τ n, v => if n = 0 then [0] else elementEncoding n (fun i => encodeWords L τ (v i))
  | .str n, v => if n ≤ 1 then [BitVec.ofNat 64 (strN v.1)] else
      BitVec.ofNat 64 v.1.length :: v.1.map (fun b => BitVec.ofInt 64 b.n) ++
        List.replicate (n - v.1.length) 0
  | .fl _ _, v => [BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 v.x)]
  | .ptr _ _, _ => [0]
  | .never, v => nomatch v

/-- Width is determined entirely by the declared type, never by runtime contents. -/
theorem encodeWords_length (L : Lay D) (τ : Ty) (v : Wert D τ) :
    (encodeWords L τ v).length = valueWords τ := by
  induction τ with
  | arr τ n ih =>
    simp only [encodeWords]
    split
    · next hn => subst n; simp [valueWords]
    · next hn =>
      rw [elementEncoding_length n (valueWords τ) _ (fun i => ih (v i))]
      have := valueWords_pos τ
      simp only [valueWords]
      have : 1 ≤ n * valueWords τ := Nat.mul_pos (by omega) (by omega)
      omega
  | str n =>
    simp only [encodeWords, valueWords]
    split
    · rfl
    · simp only [List.length_append, List.length_cons, List.length_map, List.length_replicate]
      have := v.2; omega
  | opt n =>
    simp only [encodeWords, valueWords]
    split
    · rfl
    · cases v <;> simp [integerEncoding_length, Nat.add_comm]
  | sum cs =>
    simp only [encodeWords, valueWords]
    split
    · rfl
    · simp [integerEncoding_length]
  | never => exact Empty.elim v
  | _ => simp [encodeWords, integerEncoding_length, valueWords]

/-- Typed parameters use the same tail-first order as lexical variable offsets.
    Starts and ordinary calls therefore share one encoded parameter sequence. -/
def encodeEnv (L : Lay D) : {Γ : Ctx} → Env D Γ → List Runner.W
  | [], .nil => []
  | τ :: _, .cons v ρ => encodeEnv L ρ ++ encodeWords L τ v

@[simp] theorem encodeEnv_length (L : Lay D) {Γ : Ctx} (ρ : Env D Γ) :
    (encodeEnv L ρ).length = contextWords Γ := by
  induction ρ with
  | nil => rfl
  | cons v ρ ih => simp only [encodeEnv, List.length_append, ih, encodeWords_length, contextWords_cons]

/-- Representation validity retains the target obligations of scalar references
    and IEEE values recursively through every aggregate element. Source ranges,
    string bounds and tag membership are already carried by `Wert`. -/
def ValueValid (L : Lay D) : (τ : Ty) → Wert D τ → Prop
  | .ref n, v => v.zelle < 2 ^ 64 ∧
      ∃ t, D.tabNr n = some t ∧ D.offen t = true ∧ (v.zelle : Int) < L.count t
  | .fl _ _, v => Gleitkomma.wf Gleitkomma.f64 v.x
  | .arr τ _, v => ∀ i, ValueValid L τ (v i)
  | _, _ => True

/-- The memory relation for a complete value span, including all nested elements
    and all validity obligations. It never certifies merely the low limb. -/
def ValueAt (L : Lay D) (m : Runner.Mem) (fp : Runner.W) (base : Nat)
    (τ : Ty) (v : Wert D τ) : Prop :=
  ValueValid L τ v ∧ WordsAt m fp base (encodeWords L τ v)

theorem encodeWords_arrCons {τ : Ty} {n : Nat} (a : Wert D τ) (rest : Wert D (.arr τ n)) :
    encodeWords L (.arr τ (n + 1)) (arrConsW a rest) =
      encodeWords L τ a ++ (if n = 0 then [] else encodeWords L (.arr τ n) rest) := by
  simp only [encodeWords, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false,
    elementEncoding, arrConsW, ↓reduceDIte]
  have tail : (fun i : Fin n => encodeWords L τ
      (if h : i.succ.val = 0 then a else rest ⟨i.succ.val - 1, by have := i.isLt; omega⟩)) =
      (fun i => encodeWords L τ (rest i)) := by
    funext i
    simp only [Fin.val_succ, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceDIte,
      Nat.add_sub_cancel]
  rw [tail]
  by_cases empty : n = 0
  · subst n; simp [elementEncoding]
  · simp only [if_neg empty]

theorem ValueValid.arrCons {τ : Ty} {n : Nat} {a : Wert D τ} {rest : Wert D (.arr τ n)}
    (head : ValueValid L τ a) (tail : ValueValid L (.arr τ n) rest) :
    ValueValid L (.arr τ (n + 1)) (arrConsW a rest) := by
  intro i
  simp only [arrConsW]
  split
  · exact head
  · exact tail _

/-- The expression result contract carries every represented word in the final
    memory, together with execution and the preserved frame prefix. -/
def Executes [Runner.IR.Kern] (m : Runner.Mem) (pc fp : Runner.W) (K d : Nat)
    (code : List Runner.IR.II) (post : Runner.Mem → Prop) : Prop :=
  ∃ m', Runner.IR.Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * code.length), fp⟩ m' ∧
    Runner.IR.Agree fp d K m m' ∧ post m'

theorem Executes.mono [Runner.IR.Kern] {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat}
    {code : List Runner.IR.II} {P Q : Runner.Mem → Prop}
    (run : Executes m pc fp K d code P) (post : ∀ m', P m' → Q m') :
    Executes m pc fp K d code Q := by
  obtain ⟨m', steps, changed, value⟩ := run
  exact ⟨m', steps, changed, post m' value⟩

def ValueOk [Runner.IR.Kern] (L : Lay D) (m : Runner.Mem) (pc fp : Runner.W) (K d : Nat)
    (code : List Runner.IR.II) (τ : Ty) (v : Wert D τ) : Prop :=
  Executes m pc fp K d code (fun m' => ValueAt L m' fp d τ v)

/-- Empty returns carry the reserved area's zero marker; every nonempty return
    has the same complete relation as a variable or argument. -/
def ResultAt (L : Lay D) (m : Runner.Mem) (fp : Runner.W) (base : Nat) :
    (e : Option Ty) → ErgVal D e → Prop
  | none, _ => WordsAt m fp base [0]
  | some τ, v => ValueAt L m fp base τ v

def ResultOk [Runner.IR.Kern] (L : Lay D) (m : Runner.Mem) (pc fp : Runner.W) (K d : Nat)
    (code : List Runner.IR.II) (e : Option Ty) (v : ErgVal D e) : Prop :=
  Executes m pc fp K d code (fun m' => ResultAt L m' fp d e v)

/-- Slot 2 caches the low return word for scalar entry/exit paths. It is tied to
    the canonical result area, never used as an independent result encoding. -/
def ReturnMirror (m : Runner.Mem) (fp : Runner.W) (resultBase : Nat) : Prop :=
  m.rd64 (Runner.IR.slot fp (BitVec.ofNat 64 2)) =
    m.rd64 (Runner.IR.slot fp (BitVec.ofNat 64 resultBase))

end Gabbro.Stage0.Senke
