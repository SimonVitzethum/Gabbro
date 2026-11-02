/- The single-word fast path is a specialization of the complete value encoding. -/
module
public import Stage0.Senke.Ausdruck.Sim
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable {D : Deklaration} {L : Lay D}

/-- A scalar view is available only for the established word operations. This is
    a proof view of the common encoding, not a second storage representation. -/
def WordCompatible : Ty → Prop
  | .opt n => n ≤ 2 ^ 63
  | .sum cs => sumFits cs = true
  | .arr τ n => match n with
    | 0 => True
    | 1 => WordCompatible τ
    | _ => False
  | .prod .. => False
  | .str n => n ≤ 1
  | _ => True

theorem wordCompatB_sound : (τ : Ty) → wordCompatB τ = true → WordCompatible τ
  | .opt n, h => by
    simp only [wordCompatB, decide_eq_true_eq] at h; exact h
  | .sum cs, h => h
  | .arr τ 0, _ => trivial
  | .arr τ 1, h => wordCompatB_sound τ h
  | .arr τ (n + 2), h => by simp only [wordCompatB] at h; cases h
  | .prod .., h => by cases h
  | .str n, h => by
    simp only [wordCompatB, decide_eq_true_eq] at h; exact h
  | .int .., _ | .bool, _ | .why .., _ | .never, _ | .fl .., _ | .fnptr .., _
  | .ptr .., _ | .ref .., _ => trivial

theorem integerEncoding_read_first {m : Runner.Mem} {fp : Runner.W} {base n : Nat} {z : Int}
    (positive : 0 < n) (words : WordsAt m fp base (integerEncoding n z)) :
    m.rd64 (slot fp (BitVec.ofNat 64 base)) = some (BitVec.ofInt 64 z) := by
  cases n with
  | zero => omega
  | succ n => exact words 0 (by simp [integerEncoding])

theorem ValueAt.word {m : Runner.Mem} {fp : Runner.W} {base : Nat} :
    (τ : Ty) → (v : Wert D τ) → WordCompatible τ → ValueAt L m fp base τ v →
      ∃ w, m.rd64 (slot fp (BitVec.ofNat 64 base)) = some w ∧ Enc L τ v w := by
  intro τ
  induction τ with
  | int lo hi =>
    intro v compatible value
    refine ⟨_, integerEncoding_read_first ?_ value.2, rfl⟩
    unfold integerWords
    omega
  | why n =>
    intro v compatible value
    refine ⟨BitVec.ofInt 64 v.val, integerEncoding_read_first (valueWords_pos (.why n)) value.2, ?_⟩
    exact BitVec.ofInt_natCast 64 v.val
  | bool =>
    intro v compatible value
    exact ⟨_, value.2 0 (by simp [encodeWords]), rfl⟩
  | fnptr n =>
    intro v compatible value
    exact ⟨_, value.2 0 (by simp [encodeWords]), rfl⟩
  | ref n =>
    intro v compatible value
    exact ⟨_, value.2 0 (by simp [encodeWords]), rfl, value.1⟩
  | fl lo hi =>
    intro v compatible value
    exact ⟨_, value.2 0 (by simp [encodeWords]), value.1, rfl⟩
  | ptr cap =>
    intro v compatible value
    exact ⟨_, value.2 0 (by simp [encodeWords]), rfl⟩
  | opt n =>
    intro v compatible value
    change n ≤ 2 ^ 63 at compatible
    have words : WordsAt m fp base [BitVec.ofInt 64 (optN v)] := by
      simpa only [encodeWords, if_pos compatible] using value.2
    exact ⟨_, words 0 (by simp), rfl⟩
  | sum cs =>
    intro v compatible value
    change sumFits cs = true at compatible
    have words : WordsAt m fp base [BitVec.ofNat 64 (sumN v)] := by
      simpa only [encodeWords, compatible, ite_true] using value.2
    exact ⟨_, words 0 (by simp), compatible, rfl⟩
  | str n =>
    intro v compatible value
    change n ≤ 1 at compatible
    have words : WordsAt m fp base [BitVec.ofNat 64 (strN v.1)] := by
      simpa only [encodeWords, if_pos compatible] using value.2
    exact ⟨_, words 0 (by simp), compatible, rfl⟩
  | arr τ n ih =>
    intro v compatible value
    cases n with
    | zero => exact ⟨_, value.2 0 (by simp [encodeWords]), rfl⟩
    | succ n =>
      cases n with
      | zero =>
        have child : ValueAt L m fp base τ (v ⟨0, by decide⟩) :=
          ⟨value.1 ⟨0, by decide⟩, by simpa [encodeWords, elementEncoding] using value.2⟩
        exact ih _ compatible child
      | succ n => exact False.elim compatible
  | prod name fs => intro v compatible; exact False.elim compatible
  | never => intro v; exact Empty.elim v

theorem Enc.single : (τ : Ty) → (v : Wert D τ) → (w : Runner.W) →
    valueWords τ = 1 → Enc L τ v w →
    ValueValid L τ v ∧ encodeWords L τ v = [w] := by
  intro τ
  induction τ with
  | int lo hi =>
    intro v w width encoded
    constructor
    · trivial
    · change integerWords lo hi = 1 at width
      change w = BitVec.ofInt 64 v.n at encoded
      subst w
      simp [encodeWords, width, integerEncoding]
  | arr τ n ih =>
    intro v w width encoded
    cases n with
    | zero =>
      constructor
      · intro i; exact Fin.elim0 i
      · change w = 0 at encoded
        subst w
        simp [encodeWords]
    | succ n =>
      cases n with
      | zero =>
        have childWidth : valueWords τ = 1 := by
          change max 1 (1 * valueWords τ) = 1 at width
          have positive := valueWords_pos τ
          simp only [Nat.one_mul] at width
          omega
        obtain ⟨valid, words⟩ := ih (v ⟨0, by decide⟩) w childWidth encoded
        constructor
        · intro i
          have eq : i = (⟨0, by decide⟩ : Fin 1) := by
            apply Fin.ext
            have := i.isLt
            omega
          rw [eq]
          exact valid
        · simpa [encodeWords, elementEncoding] using words
      | succ n => exact False.elim encoded
  | opt n =>
    intro v w width encoded
    have short : n ≤ 2 ^ 63 := by
      by_cases hn : n ≤ 2 ^ 63
      · exact hn
      · have positive : 0 < integerWords 0 (n - 1) := by unfold integerWords; omega
        simp only [valueWords, if_neg hn] at width
        omega
    constructor
    · trivial
    · change w = BitVec.ofInt 64 (optN v) at encoded
      simp only [encodeWords, if_pos short, encoded]
  | sum cs =>
    intro v w width encoded
    obtain ⟨fits, word⟩ := encoded
    exact ⟨trivial, by simp [encodeWords, fits, word]⟩
  | why n =>
    intro v w width encoded
    constructor
    · trivial
    · change w = BitVec.ofNat 64 v.val at encoded
      simp [encodeWords, width, integerEncoding, BitVec.ofInt_natCast, encoded]
  | ref n =>
    intro v w width encoded
    exact ⟨encoded.2, by simp only [encodeWords, encoded.1]⟩
  | fl low high =>
    intro v w width encoded
    exact ⟨encoded.1, by simp only [encodeWords, encoded.2]⟩
  | bool =>
    intro v w width encoded
    exact ⟨trivial, by simpa only [encodeWords, List.singleton_inj] using encoded.symm⟩
  | fnptr n =>
    intro v w width encoded
    exact ⟨trivial, by simpa only [encodeWords, List.singleton_inj] using encoded.symm⟩
  | ptr cap =>
    intro v w width encoded
    exact ⟨trivial, by simpa only [encodeWords, List.singleton_inj] using encoded.symm⟩
  | str n =>
    intro v w width encoded
    obtain ⟨short, word⟩ := encoded
    exact ⟨trivial, by simp [encodeWords, short, word]⟩
  | prod name fs => intro v w width encoded; exact False.elim encoded
  | never => intro v; exact Empty.elim v

theorem Ok.value [Kern] {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {code : List II}
    {τ : Ty} {v : Wert D τ} (run : Ok m pc fp K d code (Enc L τ v))
    (width : valueWords τ = 1) : ValueOk L m pc fp K d code τ v := by
  obtain ⟨m', steps, changed, w, read, encoded⟩ := run
  obtain ⟨valid, words⟩ := Enc.single τ v w width encoded
  refine ⟨m', steps, changed, valid, ?_⟩
  rw [words]
  intro i hi
  have zero : i = 0 := by simpa using hi
  subst i
  exact read

theorem ValueAt.of_enc {m : Runner.Mem} {fp : Runner.W} {base : Nat} {τ : Ty}
    {v : Wert D τ} {w : Runner.W} (width : valueWords τ = 1)
    (read : m.rd64 (slot fp (BitVec.ofNat 64 base)) = some w) (encoded : Enc L τ v w) :
    ValueAt L m fp base τ v := by
  obtain ⟨valid, words⟩ := Enc.single τ v w width encoded
  refine ⟨valid, ?_⟩
  rw [words]
  intro i hi
  have zero : i = 0 := by simpa using hi
  subst i
  exact read

theorem ValueOk.word [Kern] {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {code : List II}
    {τ : Ty} {v : Wert D τ} (run : ValueOk L m pc fp K d code τ v)
    (compatible : WordCompatible τ) : Ok m pc fp K d code (Enc L τ v) := by
  obtain ⟨m', steps, changed, value⟩ := run
  obtain ⟨w, read, encoded⟩ := ValueAt.word τ v compatible value
  exact ⟨m', steps, changed, w, read, encoded⟩

end Gabbro.Stage0.Senke
