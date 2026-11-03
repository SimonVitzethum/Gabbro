/- Chunk-count induction connects multiword reads to the existing byte kernel. -/
module
public import Stage0.Senke.Anweisung.Bytes.Span.Model
public import Stage0.Senke.Ausdruck.Wort.Bytes
public import Stage0.Senke.Ausdruck.Wort.BytesCode
public import Stage0.Senke.Ausdruck.Aggregat.KopieSatz
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
    ∀ (words n j d : Nat) (c : List II) (top : Nat), b + j + n ≤ D.count t → j + n < 2 ^ 31 →
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
    have headFits : ht ≤ K := by omega
    have tailFits : tt ≤ K := by omega
    have scratch : d + 1 ≤ K := by omega
    have chunk := readBytesL_ok i hf world lower ih (min 8 n) j d head ht
      (by omega) (by omega) headMade headFits m pc pre.left
    obtain ⟨m1, s1, ch1, w, read, value⟩ := chunk
    have p1 := pre.next ch1 (Nat.le_succ d) (by omega)
    obtain ⟨m2, s2, ch2, output⟩ := tailIH (n - 8) (j + min 8 n) (d + 1) tail tt
      (by omega) (by omega) tailMade tailFits m1 _ p1
    refine ⟨m2, ?_, ch1.trans (ch2.mono (Nat.le_succ d)), ?_⟩
    · simpa only [List.length_append, pc_add] using s1.trans s2
    · let start := (eval σ₀ i σ ρ).n + (j : Int)
      change WordsAt m2 fp d
        ([BitVec.ofInt 64 (bytesZuZahl (σ.bytesAb t f hf n start))] ++
          integerEncoding words (bytesZuZahl (σ.bytesAb t f hf n start) / 2 ^ 64))
      rw [wordsAt_append]
      constructor
      · intro limb bound
        have zero : limb = 0 := by simpa only [List.length_singleton, Nat.lt_one_iff] using bound
        subst limb
        change m2.rd64 (slot fp (BitVec.ofNat 64 d)) =
          some (BitVec.ofInt 64 (bytesZuZahl (σ.bytesAb t f hf n start)))
        rw [agree_rd_low ch2 p1.frame.room (Nat.lt_succ_self d) scratch, read, value,
          bytes_chunk_word σ t f hf n start]
      · change WordsAt m2 fp (d + 1)
          (integerEncoding words (bytesZuZahl (σ.bytesAb t f hf n start) / 2 ^ 64))
        rw [bytes_chunk_quotient σ t f hf n start]
        simpa only [start, Int.natCast_add, Int.add_assoc] using output

theorem readBytesWide_ok {Λ : List (Res D)} {Γ : Ctx} {a b : Int}
    (i : Expr D Γ Λ (.int a b)) {t : D.Tab} {f : D.Feld t} (hf : D.typ t f = .int 0 255)
    (n : Nat) (lower : 0 ≤ a) (upper : b + n ≤ D.count t) (access : darf D t Λ)
    {σ₀ σ : World D} {fp : Runner.W} {K d top : Nat} {W : Runner.Mem → Prop}
    {ρ : Env D Γ} {m : Runner.Mem} {pc : Runner.W} {c : List II}
    (world : ∀ m, W m → WeltAt m L σ) (layout : LayIn L)
    (ih : ∀ d c top, lowE (currentOld := currentOld) L i d reserved = some (c, top) → top ≤ K → ∀ m pc,
      Pre L m pc fp K d c ρ W reserved → Ok m pc fp K d c (Enc L (.int a b) (eval σ₀ i σ ρ)))
    (made : readBytesWideL L t f (lowE (currentOld := currentOld) L i (reserved := reserved)) n d = some (c, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int 0 (256 ^ n - 1))
      (eval σ₀ (.getBytes t f hf n i lower upper access) σ ρ) := by
  simp only [readBytesWideL] at made
  by_cases empty : n = 0
  · rw [if_pos empty] at made
    subst n
    simp only [Option.some.injEq, Prod.mk.injEq] at made
    obtain ⟨rfl, rfl⟩ := made
    refine Ok.value ?_ (by decide)
    exact (const_ok pre (by decide) (by omega)).mono (fun _ equal => equal)
  · rw [if_neg empty] at made
    by_cases representable : n < 2 ^ 31
    · rw [if_pos representable] at made
      simp only [bind, Option.bind_eq_some_iff, pure,
        Option.some.injEq, Prod.mk.injEq] at made
      obtain ⟨⟨captured, tc⟩, captureMade, ⟨chunks, tt⟩, chunksMade, rfl, rfl⟩ := made
      have bound : b < 2 ^ 64 := by
        by_cases nonnegative : 0 ≤ b
        · have cast : (b.toNat : Int) = b := Int.toNat_of_nonneg nonnegative
          have cell := layout.1 t f b.toNat (L.bounded (by omega))
          have byteWidth : valueWords (D.typ t f) = 1 := by rw [hf]; rfl
          simp only [Lay.elem, byteWidth, Nat.mul_one] at cell
          have small := layout.2.2
          omega
        · omega
      have iw : valueWords (.int a b) = 1 := integerWords_unsigned lower bound
      let words := integerWords 0 (256 ^ n - 1)
      have p : Pre L m pc fp K d
          (captured ++ (chunks ++ copyWords words d (d + 1))) ρ W reserved := by
        simpa only [words, List.append_assoc] using pre
      obtain ⟨m1, s1, ch1, w, read, encoded⟩ := ih d captured tc captureMade (by omega) m pc p.left
      have p1 := p.next ch1 (Nat.le_succ d) (by omega)
      -- View the captured index as a one-binding frame context. Its reservation
      -- starts at d, independently of the caller's lexical context and scratch.
      have header : FB ≤ d := by have := p.ctx; unfold frei at this; omega
      have base : frei ([] : Ctx) (d - FB) = d := by
        simp only [frei, contextWords_nil]
        omega
      have depth : frei [.int a b] (d - FB) = d + 1 := by
        simp only [frei, contextWords_cons, contextWords_nil, iw]
        omega
      let k := eval σ₀ i σ ρ
      let capturedEnv : Env D [.int a b] := .cons k .nil
      let capturedExpr : Expr D [.int a b] Λ (.int a b) := .var .here
      have captureAt : ValueAt L m1 fp (frei ([] : Ctx) (d - FB)) (.int a b) k := by
        rw [base]
        exact ValueAt.of_enc iw read encoded
      have capturedAt : EnvAt L m1 fp capturedEnv (d - FB) :=
        envAt_cons (by intro τ x; nomatch x) captureAt
      have emit : (lowE (currentOld := currentOld) L (reserved := d - FB) capturedExpr) =
          (fun dst => some (copyWords 1 dst d, dst + 1)) := by
        funext dst
        simp only [capturedExpr, lowE_eqs, iw, vslot_here, base]
      have cp : Pre L m1 _ fp K (d + 1) chunks capturedEnv W (d - FB) :=
        ⟨by rw [depth], p1.small, p1.frame, p1.left.code, p1.left.far,
          capturedAt, p1.welt, p1.wstab⟩
      have chunksMade' : readBytesWordsL L t f
          (lowE (currentOld := currentOld) L (reserved := d - FB) capturedExpr)
          words n 0 (d + 1) = some (chunks, tt) := by
        rw [emit]
        exact chunksMade
      obtain ⟨m2, s2, ch2, output⟩ := readBytesWords_ok (σ₀ := σ₀) (σ := σ)
        (reserved := d - FB) capturedExpr hf world lower
        (fun dst code top made fits m pc hp =>
          (var_value_ok .here made fits hp).word trivial)
        words n 0 (d + 1) chunks tt (by simpa using upper)
        (by simpa using representable) chunksMade' (by omega) m1 _ cp
      have p2 := p1.next ch2 (Nat.le_refl _) (by omega)
      have out : WordsAt m2 fp (d + 1)
          (encodeWords L (.int 0 (256 ^ n - 1))
            (eval σ₀ (.getBytes t f hf n i lower upper access) σ ρ)) := by
        erw [encodeWords_int]
        simpa only [eval, capturedExpr, capturedEnv, Env.get, k, words,
          Int.natCast_zero, Int.add_zero] using output
      obtain ⟨m3, s3, ch3, result⟩ := copyValue_run
        (τ := .int 0 (256 ^ n - 1))
        (v := eval σ₀ (.getBytes t f hf n i lower upper access) σ ρ) p2.frame p2.small
        (by change d + words ≤ K; omega) (by change d + 1 + words ≤ K; omega)
        (Or.inl (by omega)) p2.code (by simpa only [copyWords_length] using p2.far)
        (show ValueAt L m2 fp (d + 1) (.int 0 (256 ^ n - 1))
          (eval σ₀ (.getBytes t f hf n i lower upper access) σ ρ) from ⟨trivial, out⟩)
      refine ⟨m3, ?_, (ch1.trans (ch2.mono (Nat.le_succ d))).trans
        (Agree.widen ch3 (by change d + words ≤ K; omega)), result⟩
      simpa only [List.length_append, copyWords_length, pc_add, words] using s1.trans (s2.trans s3)
    · rw [if_neg representable] at made
      cases made

/-- Actual expression lowering uses the same complete-value conclusion for both
    the single-word kernel and the chunk-count induction. -/
theorem getBytes_ok {Λ : List (Res D)} {Γ : Ctx} {a b : Int}
    (i : Expr D Γ Λ (.int a b)) {t : D.Tab} {f : D.Feld t} (hf : D.typ t f = .int 0 255)
    (n : Nat) (hlo : 0 ≤ a) (hhi : b + n ≤ D.count t) (access : darf D t Λ)
    {σ₀ σ : World D} {fp : Runner.W} {K d top : Nat} {W : Runner.Mem → Prop}
    {ρ : Env D Γ} {m : Runner.Mem} {pc : Runner.W} {c : List II}
    (hWL : ∀ m, W m → WeltAt m L σ) (layout : LayIn L)
    (ih : ∀ d c top, lowE (currentOld := currentOld) L i d reserved = some (c, top) → top ≤ K → ∀ m pc,
      Pre L m pc fp K d c ρ W reserved → Ok m pc fp K d c (Enc L (.int a b) (eval σ₀ i σ ρ)))
    (h : lowE (currentOld := currentOld) L (reserved := reserved) (.getBytes t f hf n i hlo hhi access) d = some (c, top))
    (hK : top ≤ K) (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int 0 (256 ^ n - 1))
      (eval σ₀ (.getBytes t f hf n i hlo hhi access) σ ρ) := by
  simp only [lowE_eqs] at h
  exact readBytesWide_ok i hf n hlo hhi access hWL layout ih h hK hp

end Gabbro.Stage0.Senke
