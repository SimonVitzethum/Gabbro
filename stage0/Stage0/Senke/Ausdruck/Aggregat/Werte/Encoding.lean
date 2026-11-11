/- Canonical value words, shared by frames, world storage and call boundaries. -/
module
public import Grammatik.Kern.Syntax.Typen.Fall
public import Grammatik.Kern.Syntax.Typen.Produkt
public import Stage0.Senke.Ausdruck.Aggregat.Werte.Encodinga
public import Stage0.Senke.Welt.Lay
public import Stage0.Senke.Ausdruck.Aggregat.Layout
public import Stage0.Senke.Ausdruck.Aggregat.Wert
public import Stage0.Senke.Ausdruck.Aggregat.Kopie
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
variable {D : Deklaration}

mutual
/-- The unique canonical word sequence of a model value. Reference validity and
    world permissions remain separate proof obligations. -/
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
        (encodeSumPayload L cs v.1 v.2 ++ List.replicate
          (sumPayloadWords cs - (encodeSumPayload L cs v.1 v.2).length) 0)
  | .prod _ fs, v => if fs = [] then [0] else encodeProductFields L fs v
  | .arr τ n, v => if n = 0 then [0] else elementEncoding n (fun i => encodeWords L τ (v i))
  | .str n, v => if n ≤ 1 then [BitVec.ofNat 64 (strN v.1)] else
      BitVec.ofNat 64 v.1.length :: v.1.map (fun b => BitVec.ofInt 64 b.n) ++
        List.replicate (n - v.1.length) 0
  | .fl _ _, v => [v.x.hwToBits.toBitVec]
  | .ptr _, _ => [0]
  | .never, v => nomatch v

termination_by structural τ => τ
/-- Traverse the selected schema structurally, retaining the payload's own encoding. -/
def encodeSumPayload (L : Lay D) : (cs : List (Option Ty)) →
    (i : Fin cs.length) → Fall D.Fn D.passt cs i → List Runner.W
  | [], i, _ => Fin.elim0 i
  | none :: _, ⟨0, _⟩, _ => []
  | some τ :: _, ⟨0, _⟩, v => encodeWords L τ v
  | _ :: cs, ⟨i + 1, hi⟩, v => encodeSumPayload L cs ⟨i, Nat.lt_of_succ_lt_succ hi⟩ v
termination_by structural cs => cs

/-- Encode heterogeneous fields
 in declaration order. -/
def encodeProductFields (L : Lay D) : (fs : List Ty) →
    ProdVal D.Fn D.passt fs → List Runner.W
  | [], _ => []
  | τ :: rest, v => encodeWords L τ (ProdVal.hd v) ++
      encodeProductFields L rest (ProdVal.tl v)
termination_by structural fs => fs
end


/-- Empty products retain the canonical zero marker. -/
def encodeProduct (L : Lay D) (fs : List Ty)
    (v : ProdVal D.Fn D.passt fs) : List Runner.W :=
  if fs = [] then [0] else encodeProductFields L fs v

/-- The integer branch of `encodeWords` as an equation (the mutual definition is not unfolded by `change`). -/
theorem encodeWords_int (L : Lay D) (lo hi : Int) (v : Wert D (.int lo hi)) :
    encodeWords L (.int lo hi) v = integerEncoding (integerWords lo hi) v.n := by
  rw [encodeWords.eq_def]

theorem encodeWords_prod (L : Lay D) (name : Nat) (fs : List Ty) (v : Wert D (.prod name fs)) :
    encodeWords L (.prod name fs) v = encodeProduct L fs v := by
  rw [encodeWords.eq_def]; rfl

/-- Width is determined entirely by the declared type, never by runtime contents. -/
theorem encodeWords_length (L : Lay D) (τ : Ty) (v : Wert D τ) :
    (encodeWords L τ v).length = valueWords τ := by
  cases τ with
  | arr τ n =>
    simp only [encodeWords]
    split
    · next hn => subst n; simp [valueWords]
    · next hn =>
      rw [elementEncoding_length n (valueWords τ) _ (fun i => encodeWords_length L τ (v i))]
      have := valueWords_pos τ
      simp only [valueWords]
      have : 1 ≤ n * valueWords τ := Nat.mul_pos (by omega) (by omega)
      omega
  | prod name fs =>
    have fields : (∀ σ ∈ fs, ∀ w : Wert D σ,
        (encodeWords L σ w).length = valueWords σ) → ∀ (vs : ProdVal D.Fn D.passt fs),
        (encodeProductFields L fs vs).length = productWords fs := by
      clear v
      induction fs with
      | nil => intro _ vs; simp only [encodeProductFields, productWords, List.length_nil]
      | cons σ rest ih =>
        intro widths vs
        simp only [encodeProductFields, List.length_append, productWords]
        rw [widths σ List.mem_cons_self,
          ih (fun χ member => widths χ (List.mem_cons_of_mem _ member))]
    have widths : ∀ σ ∈ fs, ∀ w : Wert D σ,
        (encodeWords L σ w).length = valueWords σ := by
      intro σ member w
      exact encodeWords_length L σ w
    have hp : ∀ vs : ProdVal D.Fn D.passt fs,
        (encodeProduct L fs vs).length = max 1 (productWords fs) := by
      intro vs
      rw [encodeProduct.eq_def]
      split
      · next h => subst fs; simp [productWords]
      · next h =>
        rw [fields widths]
        cases fs with
        | nil => exact False.elim (h rfl)
        | cons σ rest =>
          have := valueWords_pos σ
          simp only [productWords]
          omega
    simp only [encodeWords, valueWords]
    exact hp v
  | str n =>
    simp only [encodeWords, valueWords]
    split
    · rfl
    · simp only [List.length_append, List.length_cons, List.length_map, List.length_replicate]
      have := v.2; omega
  | opt n =>
    rw [encodeWords.eq_def]; dsimp only
    simp only [valueWords]
    split
    · rfl
    · cases v <;> simp [integerEncoding_length, Nat.add_comm]
  | sum cs =>
    simp only [encodeWords, valueWords]
    split
    · rfl
    · have selected : ∀ (cs : List (Option Ty)) (i : Fin cs.length)
          (v : Fall D.Fn D.passt cs i),
          (∀ τ, some τ ∈ cs → ∀ w : Wert D τ,
            (encodeWords L τ w).length = valueWords τ) →
          (encodeSumPayload L cs i v).length ≤ sumPayloadWords cs := by
        intro cs
        induction cs with
        | nil => intro i; exact Fin.elim0 i
        | cons c rest ih =>
          intro i v widths
          rcases i with ⟨i, hi⟩
          cases i with
          | zero =>
            cases c with
            | none =>
              simp only [encodeSumPayload, List.length_nil]
              exact Nat.zero_le _
            | some τ =>
              have hw := widths τ List.mem_cons_self (v : Wert D τ)
              simp only [encodeSumPayload]
              rw [hw]
              exact Nat.le_max_left _ _
          | succ i =>
            have tail := ih ⟨i, Nat.lt_of_succ_lt_succ hi⟩ v
              (fun τ mem => widths τ (List.mem_cons_of_mem _ mem))
            cases c <;> simp only [encodeSumPayload, sumPayloadWords] <;> omega
      have bound := selected cs v.1 v.2
        (fun τ mem w => encodeWords_length L τ w)
      simp only [List.length_append, integerEncoding_length, List.length_replicate]
      omega
  | never => exact Empty.elim v
  | _ => simp [encodeWords, integerEncoding_length, valueWords]

termination_by sizeOf τ
decreasing_by
  all_goals
    subst_vars
    first
      | decreasing_trivial
      | (simp_wf; simp only [Ty.arr.sizeOf_spec]; omega)
      | (simp_wf
         have hs := List.sizeOf_lt_of_mem ‹_ ∈ _›
         simp only [Ty.prod.sizeOf_spec] at *
         omega)
      | (simp_wf
         have hs := List.sizeOf_lt_of_mem ‹_ ∈ _›
         simp only [Ty.sum.sizeOf_spec] at *
         simp_all
         omega)

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

mutual
/-- Representation validity retains the target obligations of scalar references
    and IEEE values recursively through every aggregate element. Source ranges,
    string bounds and tag membership are already carried by `Wert`. -/
def ValueValid (L : Lay D) : (τ : Ty) → Wert D τ → Prop
  | .ref n, v => v.zelle < 2 ^ 64 ∧
      ∃ t, D.tabNr n = some t ∧ D.offen t = true ∧ (v.zelle : Int) < L.count t
  | .fl _ _, _ => True
  | .arr τ _, v => ∀ i, ValueValid L τ (v i)
  | .prod _ fs, v => ProdValid L fs v
  | .sum cs, v => SumValid L cs v.1 v.2
  | _, _ => True

/-- Sum validity follows the selected payload, including float/reference obligations. -/
def SumValid (L : Lay D) : (cs : List (Option Ty)) →
    (i : Fin cs.length) → Fall D.Fn D.passt cs i → Prop
  | [], i, _ => Fin.elim0 i
  | none :: _, ⟨0, _⟩, _ => True
  | some τ :: _, ⟨0, _⟩, v => ValueValid L τ v
  | _ :: cs, ⟨i + 1, hi⟩, v => SumValid L cs ⟨i, Nat.lt_of_succ_lt_succ hi⟩ v

/-- Representation obligations for each field
 in declaration order. -/
def ProdValid (L : Lay D) : (fs : List Ty) → ProdVal D.Fn D.passt fs → Prop
  | [], _ => True
  | τ :: rest, v => ValueValid L τ (ProdVal.hd v) ∧ ProdValid L rest (ProdVal.tl v)

end

/-- A typed field projects its representation obligations. -/
theorem ProdValid.field {L : Lay D} {fs : List Ty} {σ : Ty}
    (i : FieldAt fs σ) (v : ProdVal D.Fn D.passt fs)
    (valid : ProdValid L fs v) : ValueValid L σ (prodGetW i v) := by
  induction i with
  | head => exact valid.1
  | tail i ih => exact ih (ProdVal.tl v) valid.2

/-- The memory relation for a complete value span, including all nested elements
    and all validity obligations. It never certifies merely the low limb. -/
def ValueAt (L : Lay D) (m : Runner.Mem) (fp : Runner.W) (base : Nat)
    (τ : Ty) (v : Wert D τ) : Prop :=
  ValueValid L τ v ∧ WordsAt m fp base (encodeWords L τ v)

/-- Array indexing projects full validity and all words, including nested elements. -/
theorem ValueAt.array_element {L : Lay D} {m : Runner.Mem} {fp : Runner.W}
    {base n : Nat} {τ : Ty} {v : Wert D (.arr τ n)}
    (input : ValueAt L m fp base (.arr τ n) v) (j : Fin n) :
    ValueAt L m fp (base + j.val * valueWords τ) τ (v j) := by
  refine ⟨input.1 j, ?_⟩
  have nonempty : n ≠ 0 := by have := j.isLt; omega
  have words : WordsAt m fp base (elementEncoding n (fun i => encodeWords L τ (v i))) := by
    simpa only [encodeWords, if_neg nonempty] using input.2
  exact elementEncoding_wordsAt _ (fun i => encodeWords_length L τ (v i)) words j

theorem encodeWords_arrCons {τ : Ty} {n : Nat} (a : Wert D τ) (rest : Wert D (.arr τ n)) :
    encodeWords L (.arr τ (n + 1)) (arrConsW a rest) =
      encodeWords L τ a ++ (if n = 0 then [] else encodeWords L (.arr τ n) rest) := by
  have consEncoding (xs : Fin n → Wert D τ) :
      encodeWords L (.arr τ (n + 1)) (arrConsW a xs) =
        encodeWords L τ a ++ (if n = 0 then [] else encodeWords L (.arr τ n) xs) := by
    rw [encodeWords.eq_def L (.arr τ (n + 1)) (arrConsW a xs)]
    dsimp only
    rw [if_neg (by omega), elementEncoding]
    have head : encodeWords L τ (arrConsW a xs ⟨0, by omega⟩) = encodeWords L τ a := by
      simp only [arrConsW, ↓reduceDIte]
    have tail : (fun i : Fin n => encodeWords L τ (arrConsW a xs i.succ)) =
        (fun i => encodeWords L τ (xs i)) := by
      funext i
      simp only [arrConsW, Fin.val_succ, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
        ↓reduceDIte, Nat.add_sub_cancel]
    rw [head, tail]
    by_cases empty : n = 0
    · subst n; simp [elementEncoding]
    · rw [if_neg empty, encodeWords.eq_def L (.arr τ n) xs]
      dsimp only
      rw [if_neg empty]
  exact consEncoding (fun i => rest i)

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
