/- Chunk-count induction connects multiword reads to the existing byte kernel. -/
module
public import Stage0.Senke.Anweisung.Bytes.Span.Model
public import Stage0.Senke.Ausdruck.Wort.Bytes
public import Stage0.Senke.Ausdruck.Wort.BytesCode
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat} {currentOld : Bool}

/-- Every chunk produces one canonical limb, including partial and zero chunks. -/
theorem readBytesWords_ok {Λ : List (Res D)} {Γ : Ctx} {a b : Int}
    (i : Expr D Γ Λ (.int a b)) {t : D.Tab} {f : D.Feld t} (hf : D.typ t f = .int 0 255)
    {σ₀ σ : World D} {fp : Runner.W} {K : Nat} {W : Runner.Mem → Prop} {ρ : Env D Γ}
    (world : ∀ m, W m → WeltAt m L σ) (lower : 0 ≤ a)
    (ih : ∀ d c top, lowE (currentOld := currentOld) L i d reserved = some (c, top) → top ≤ K → ∀ m pc,
      Pre L m pc fp K d c ρ W reserved → Ok m pc fp K d c (Enc L (.int a b) (eval σ₀ i σ ρ))) :
    ∀ words n j d c top, b + j + n ≤ D.count t → j + n < 2 ^ 31 →
      readBytesWordsL L t f (lowE (currentOld := currentOld) L i (reserved := reserved)) words n j d = some (c, top) →
      top ≤ K → ∀ m pc, Pre L m pc fp K d c ρ W reserved →
      Executes m pc fp K d c (fun m' => WordsAt m' fp d
        (integerEncoding words (bytesZuZahl (σ.bytesAb t f hf n ((eval σ₀ i σ ρ).n + j))))) := by
  intro words
  induction words with
  | zero =>
    intro n j d c top _ _ made _ m pc pre
    simp only [readBytesWordsL, Option.some.injEq, Prod.mk.injEq] at made
    obtain ⟨rfl, rfl⟩ := made
    exact ⟨m, by simpa using Star.refl ⟨pc, fp⟩ m, Agree.refl _ _ _ _, by simp [WordsAt, integerEncoding]⟩
  | succ words tailIH =>
    intro n j d c top upper offset made fits m pc pre
    simp only [readBytesWordsL, bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq, Prod.mk.injEq] at made
    obtain ⟨⟨head, ht⟩, headMade, ⟨tail, tt⟩, tailMade, rfl, rfl⟩ := made
    have tailTop := readBytesWordsL_top tailMade
    have chunk := readBytesL_ok i hf world lower ih (min 8 n) j d head ht
      (by omega) (by omega) headMade (by omega) m pc pre.left
    obtain ⟨m1, s1, ch1, w, read, value⟩ := chunk
    have p1 := pre.next ch1 (Nat.le_succ d) (by omega)
    obtain ⟨m2, s2, ch2, output⟩ := tailIH (n - 8) (j + min 8 n) (d + 1) tail tt
      (by omega) (by omega) tailMade (by omega) m1 _ p1
    refine ⟨m2, ?_, ch1.trans (ch2.mono (Nat.le_succ d)), ?_⟩
    · simpa only [List.length_append, pc_add] using s1.trans s2
    · simp only [integerEncoding]
      intro limb bound
      cases limb with
      | zero =>
        rw [Nat.add_zero, agree_rd_low ch2 p1.frame.room (by omega) (by omega), read]
        congr 1
        rw [value, bytes_chunk_word σ t f hf n ((eval σ₀ i σ ρ).n + j)]
      | succ limb =>
        have quotient := bytes_chunk_quotient σ t f hf n ((eval σ₀ i σ ρ).n + j)
        rw [quotient]
        simpa only [List.getElem_cons_succ, Nat.add_assoc, Int.natCast_add, Int.add_assoc] using
          output limb (by simpa only [List.length_cons] using bound)

theorem readBytesWide_ok {Λ : List (Res D)} {Γ : Ctx} {a b : Int}
    (i : Expr D Γ Λ (.int a b)) {t : D.Tab} {f : D.Feld t} (hf : D.typ t f = .int 0 255)
    (n : Nat) (lower : 0 ≤ a) (upper : b + n ≤ D.count t) (access : darf D t Λ)
    {σ₀ σ : World D} {fp : Runner.W} {K d top : Nat} {W : Runner.Mem → Prop}
    {ρ : Env D Γ} {m : Runner.Mem} {pc : Runner.W} {c : List II}
    (world : ∀ m, W m → WeltAt m L σ)
    (ih : ∀ d c top, lowE (currentOld := currentOld) L i d reserved = some (c, top) → top ≤ K → ∀ m pc,
      Pre L m pc fp K d c ρ W reserved → Ok m pc fp K d c (Enc L (.int a b) (eval σ₀ i σ ρ)))
    (made : readBytesWideL L t f (lowE (currentOld := currentOld) L i (reserved := reserved)) n d = some (c, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int 0 (256 ^ n - 1))
      (eval σ₀ (.getBytes t f hf n i lower upper access) σ ρ) := by
  simp only [readBytesWideL] at made
  split at made
  · next representable =>
    obtain ⟨m', steps, changed, output⟩ := readBytesWords_ok i hf world lower ih
      (integerWords 0 (256 ^ n - 1)) n 0 d c top (by simpa using upper)
      (by simpa using representable) made fits m pc pre
    refine ⟨m', steps, changed, trivial, ?_⟩
    simpa only [encodeWords, eval, Int.natCast_zero, Int.add_zero] using output
  · cases made

/-- Actual expression lowering uses the same complete-value conclusion for both
    the single-word kernel and the chunk-count induction. -/
theorem getBytes_ok {Λ : List (Res D)} {Γ : Ctx} {a b : Int}
    (i : Expr D Γ Λ (.int a b)) {t : D.Tab} {f : D.Feld t} (hf : D.typ t f = .int 0 255)
    (n : Nat) (hlo : 0 ≤ a) (hhi : b + n ≤ D.count t) (access : darf D t Λ)
    {σ₀ σ : World D} {fp : Runner.W} {K d top : Nat} {W : Runner.Mem → Prop}
    {ρ : Env D Γ} {m : Runner.Mem} {pc : Runner.W} {c : List II}
    (hWL : ∀ m, W m → WeltAt m L σ)
    (ih : ∀ d c top, lowE (currentOld := currentOld) L i d reserved = some (c, top) → top ≤ K → ∀ m pc,
      Pre L m pc fp K d c ρ W reserved → Ok m pc fp K d c (Enc L (.int a b) (eval σ₀ i σ ρ)))
    (h : lowE (currentOld := currentOld) L (reserved := reserved) (.getBytes t f hf n i hlo hhi access) d = some (c, top))
    (hK : top ≤ K) (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int 0 (256 ^ n - 1))
      (eval σ₀ (.getBytes t f hf n i hlo hhi access) σ ρ) := by
    simp only [lowE_eqs] at h
    split at h
    · next hn =>
      have power : (256 : Int) ^ n ≤ (256 : Int) ^ 8 := by
        have natural := Nat.pow_le_pow_right (n := 256) (i := n) (by decide) hn
        have cast : ((256 ^ n : Nat) : Int) ≤ ((256 ^ 8 : Nat) : Int) := Int.ofNat_le.mpr natural
        simpa only [Int.natCast_pow, Int.cast_ofNat_Int] using cast
      have ceiling : (256 : Int) ^ 8 = 2 ^ 64 := by decide
      rw [ceiling] at power
      refine Ok.value ?_ (integerWords_unsigned (by decide) (by omega))
      have hr := readBytesL_ok i hf hWL hlo
        ih
        n 0 d c top (by simpa using hhi) (by omega) h hK m pc hp
      exact hr.mono (fun w hw => by
        change w = BitVec.ofInt 64 (bytesZuZahl (σ.bytesAb t f hf n (eval σ₀ i σ ρ).n))
        simpa only [Int.natCast_zero, Int.add_zero] using hw)
    · exact readBytesWide_ok i hf n hlo hhi access hWL ih h hK hp

end Gabbro.Stage0.Senke
