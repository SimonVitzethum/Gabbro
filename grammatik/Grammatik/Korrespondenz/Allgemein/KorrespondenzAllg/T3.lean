/- Part 3 of 5 of `KorrespondenzAllg` (split by instrumente/teile/lean-teilen.py; the umbrella `KorrespondenzAllg.lean` imports all parts). -/
import Grammatik.Korrespondenz.Allgemein.KorrespondenzAllg.T2

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Sound

variable (X : TVCtx D) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ)

theorem ptrOk_sound {cp : CX} {t : D.Tab} (h : ptrOk X.EL K cp t = true) : PtrTo X K cp t := by
  match cp, h with
  | .addr (.tab k), h =>
      have hk : k = X.EL.tnr t := of_decide_eq_true h
      subst hk
      exact ptrTo_named X K t
  | .var kp, h =>
      simp only [ptrOk, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ptrTo_param X K (of_decide_eq_true h)
      · obtain ⟨⟨τ, v⟩, -, hv⟩ := List.any_eq_true.mp h
        simp only [Bool.and_eq_true] at hv
        obtain ⟨hl, hz⟩ := hv
        have hl' : K.loc v = kp := of_decide_eq_true hl
        subst hl'
        cases τ with
        | ptr n rw => exact ptrTo_var X K v (of_decide_eq_true hz)
        | _ => simp [istZeigerAuf] at hz

theorem slotOk_sound {b : CX} {n ss off : Nat} {τc : CTy} {t : D.Tab} {f : D.Feld t}
    (h : slotOk X.EL K b n ss off τc t f = true) :
    PtrTo X K b t ∧ n = (X.EL.trec t).count ∧ ss = (X.EL.trec t).ssize ∧
      off = (X.EL.trec t).off (X.EL.fnr t f) ∧ τc = X.EL.slotTy t f ∧ D.geist t = false := by
  simp only [slotOk, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨hp, hn⟩, hs⟩, ho⟩, hτ⟩, hg⟩ := h
  exact ⟨ptrOk_sound X K hp, of_decide_eq_true hn, of_decide_eq_true hs, of_decide_eq_true ho,
    of_decide_eq_true hτ, hg⟩

/-- A table pointer in C against Gabbro's `ptrOf`. -/
theorem ecorr_ptrOf {cp : CX} {t : D.Tab} {n : Nat} {ht : D.tabNr n = some t} {rw : Bool}
    (hp : PtrTo X K cp t) : ExprCorr X K cp (Expr.ptrOf (Λ := Λ) t n ht rw) := by
  intro σ st ρG ρC _ hr
  exact ⟨_, st, hp st ρG ρC hr, t, ht, rfl⟩

/-- `a >= b`: `Zucker.ge a b` is `le b a`, and C writes `>=`. The one
    comparison operator the lemma stock did not name; `ecorr_cmp` (the
    scheme that excludes the signed/unsigned pitfall `-1 < 1u`) with its
    operator fact, nothing new assumed. `Zucker.gt` is `lt b a` and already
    has `ecorr_gt`. -/
theorem ecorr_geSwap (t : CIT) {l1 h1 l2 h2 : Int} {ca cb : CX}
    {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) (hta : t.holds l1 h1)
    (htb : t.holds l2 h2) :
    ExprCorr X K (.cmp .ge t ca cb) (.le b a) :=
  ecorr_cmp X K .ge t ha hb hta htb (fun _ _ => rfl)

/-- **Soundness of the expression check.** -/
theorem exOk_lit {n : Int} {c : CX} (h : exOk X.EL K (Expr.lit (Γ := Γ) (Λ := Λ) n) c = true) :
    ExprCorr X K c (Expr.lit (Γ := Γ) (Λ := Λ) n) := by
  cases c with
  | lit m =>
      have hm : m = n := of_decide_eq_true h
      subst hm
      exact ecorr_lit X K m
  | _ => exact absurd h (by simp [exOk])

theorem exOk_var {τ : Ty} {x : Var Γ τ} {c : CX} (h : exOk X.EL K (Expr.var (Λ := Λ) x) c = true) :
    ExprCorr X K c (Expr.var (Λ := Λ) x) := by
  cases c with
  | var k =>
      have hk : k = K.loc x := of_decide_eq_true h
      subst hk
      exact ecorr_var X K x
  | _ => exact absurd h (by simp [exOk])

/-- The slot-load arm, given the index correspondence. -/
theorem exOk_ld {t : D.Tab} {f : D.Feld t} {e : Expr D Γ Λ (D.typ t f)}
    {i : Expr D Γ Λ (.index (D.count t))} {c : CX}
    (h : (match c with
      | .ld (.slotA b ci n ss off) τc => slotOk X.EL K b n ss off τc t f && exOk X.EL K i ci
      | _ => false) = true)
    (hev : ∀ (σ : World D) (ρG : Env D Γ), eval σ e σ ρG = σ.slots t (eval σ i σ ρG).n f)
    (ih : ∀ ci, exOk X.EL K i ci = true → ExprCorr X K ci i) : ExprCorr X K c e := by
  cases c with
  | ld p τc =>
      cases p with
      | slotA b ci n ss off =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨hs, hi⟩ := h
          obtain ⟨hp, hn, hss, hoff, hτ, hg⟩ := slotOk_sound X K hs
          subst hn hss hoff hτ
          exact ecorr_slotVia X K hp f hg (ih ci hi) hev
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

/-! ### The arms added on 2026-09-15: every one is an existing T4 lemma

    `exOk` was narrower than its own stock of proved lemmas -- the arithmetic,
    bitwise, comparison and boolean families all fell through `_ => false`
    although `ecorr_add` … `ecorr_shr`, `ecorr_lt` … `ecorr_eq`, `ecorr_nicht`,
    `ecorr_und`, `ecorr_oder` and `ecorr_glob` were proved. Each helper below
    takes the arm's own match as its hypothesis (so the check's text and the
    proof's text cannot drift apart) and the soundness of the operands, and
    ends in the lemma. NOTHING new is assumed. -/

theorem exOk_wahr {c : CX} (h : (match c with | .lit m => decide (m = 1) | _ => false) = true) :
    ExprCorr X K c (Expr.tru (D := D) (Γ := Γ) (Λ := Λ)) := by
  cases c with
  | lit m =>
      have hm : m = 1 := of_decide_eq_true h
      subst hm
      exact ecorr_wahr X K
  | _ => exact absurd h (by simp)

theorem exOk_falsch {c : CX} (h : (match c with | .lit m => decide (m = 0) | _ => false) = true) :
    ExprCorr X K c (Expr.fls (D := D) (Γ := Γ) (Λ := Λ)) := by
  cases c with
  | lit m =>
      have hm : m = 0 := of_decide_eq_true h
      subst hm
      exact ecorr_falsch X K
  | _ => exact absurd h (by simp)

theorem exOk_glob {g : D.Glob} {hL : gdarf D g Λ} {c : CX}
    (h : (match c with
      | .ld (.addr (.glob gn)) τc =>
          decide (gn = X.EL.gnr g) && decide (τc = X.EL.gty g) && !(D.ggeist g) && !(D.atomar g)
      | _ => false) = true) :
    ExprCorr X K c (Expr.glob (Γ := Γ) g hL) := by
  cases c with
  | ld p τc =>
      cases p with
      | addr b =>
          cases b with
          | glob gn =>
              simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
              obtain ⟨⟨⟨hn, hτ⟩, hgg⟩, hat⟩ := h
              have hn' : gn = X.EL.gnr g := of_decide_eq_true hn
              have hτ' : τc = X.EL.gty g := of_decide_eq_true hτ
              subst hn'
              subst hτ'
              exact ecorr_glob X K g hgg hat hL
          | _ => exact absurd h (by simp)
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

/-- The three range facts of a `.bin` arm come out of `randOk` and the
    result decide. -/
theorem randOk_sound {t : CIT} {l1 h1 l2 h2 : Int} (h : randOk t l1 h1 l2 h2 = true) :
    t.holds l1 h1 ∧ t.holds l2 h2 := by
  simp only [randOk, Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩

/-- The signed division and remainder need `INT_MIN / -1` excluded: the
    computation type is unsigned, or the dividend's range starts above its
    minimum. -/
theorem sgnMin_sound {t : CIT} {l1 : Int}
    (h : (decide (t.sgn = false) || decide (t.lo < l1)) = true) : t.sgn = true → t.lo < l1 := by
  simp only [Bool.or_eq_true] at h
  intro hs
  rcases h with h | h
  · exact absurd (hs.symm.trans (of_decide_eq_true h)) (by simp)
  · exact of_decide_eq_true h

section BinArme

variable {l1 h1 l2 h2 : Int} {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)}
  (iha : ∀ ca, exOk X.EL K a ca = true → ExprCorr X K ca a)
  (ihb : ∀ cb, exOk X.EL K b cb = true → ExprCorr X K cb b)

include iha ihb

theorem exOk_add {c : CX} (h : (match c with
    | .bin .add t ca cb =>
        randOk t l1 h1 l2 h2 && decide (t.holds (l1 + l2) (h1 + h2)) &&
          exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.add a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | add =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨⟨hr, htr⟩, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_add X K t (iha ca hA) (ihb cb hB) hta htb (of_decide_eq_true htr)
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_sub {c : CX} (h : (match c with
    | .bin .sub t ca cb =>
        randOk t l1 h1 l2 h2 && decide (t.holds (l1 - h2) (h1 - l2)) &&
          exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.sub a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | sub =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨⟨hr, htr⟩, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_sub X K t (iha ca hA) (ihb cb hB) hta htb (of_decide_eq_true htr)
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_mul {c : CX} (h : (match c with
    | .bin .mul t ca cb =>
        randOk t l1 h1 l2 h2 &&
          decide (t.holds (imin (imin (l1*l2) (l1*h2)) (imin (h1*l2) (h1*h2)))
            (imax (imax (l1*l2) (l1*h2)) (imax (h1*l2) (h1*h2)))) &&
          exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.mul a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | mul =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨⟨hr, htr⟩, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_mul X K t (iha ca hA) (ihb cb hB) hta htb (of_decide_eq_true htr)
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_div {c : CX} (h0 : 0 ≤ l1) (h1' : 1 ≤ l2) (h : (match c with
    | .bin .div t ca cb => randOk t l1 h1 l2 h2 && exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.div h0 h1' a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | div =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hr, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_div X K t h0 h1' (iha ca hA) (ihb cb hB) hta htb
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_rem {c : CX} (h0 : 0 ≤ l1) (h1' : 1 ≤ l2) (h : (match c with
    | .bin .mod t ca cb => randOk t l1 h1 l2 h2 && exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.rem h0 h1' a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | mod =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hr, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_rem X K t h0 h1' (iha ca hA) (ihb cb hB) hta htb
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_sdiv {c : CX} (hb0 : 1 ≤ l2 ∨ h2 ≤ -1) (h : (match c with
    | .bin .div t ca cb =>
        randOk t l1 h1 l2 h2 && (decide (t.sgn = false) || decide (t.lo < l1)) &&
          exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.sdiv hb0 a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | div =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨⟨hr, hm⟩, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_sdiv X K t hb0 (iha ca hA) (ihb cb hB) hta htb (sgnMin_sound hm)
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_srem {c : CX} (hb0 : 1 ≤ l2 ∨ h2 ≤ -1) (h : (match c with
    | .bin .mod t ca cb =>
        randOk t l1 h1 l2 h2 && (decide (t.sgn = false) || decide (t.lo < l1)) &&
          exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.srem hb0 a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | mod =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨⟨hr, hm⟩, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_srem X K t hb0 (iha ca hA) (ihb cb hB) hta htb (sgnMin_sound hm)
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_band {c : CX} (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (h : (match c with
    | .bin .band t ca cb => randOk t l1 h1 l2 h2 && exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.band h0 h0' a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | band =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hr, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_band X K t h0 h0' (iha ca hA) (ihb cb hB) hta htb
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_bor {c : CX} {w : Nat} (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (hw1 : h1 < 2 ^ w)
    (hw2 : h2 < 2 ^ w) (h : (match c with
    | .bin .bor t ca cb => randOk t l1 h1 l2 h2 && exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.bor w h0 h0' hw1 hw2 a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | bor =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hr, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_bor X K t w h0 h0' hw1 hw2 (iha ca hA) (ihb cb hB) hta htb
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_bxor {c : CX} {w : Nat} (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (hw1 : h1 < 2 ^ w)
    (hw2 : h2 < 2 ^ w) (h : (match c with
    | .bin .bxor t ca cb => randOk t l1 h1 l2 h2 && exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.bxor w h0 h0' hw1 hw2 a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | bxor =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hr, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_bxor X K t w h0 h0' hw1 hw2 (iha ca hA) (ihb cb hB) hta htb
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_shl {c : CX} {w : Nat} (hw1 : h1 < 2 ^ w) (hw2 : h2 < (w : Int)) (h0 : 0 ≤ l1)
    (h0' : 0 ≤ l2) (h : (match c with
    | .bin .shl t ca cb =>
        randOk t l1 h1 l2 h2 && decide (h2 < (t.bits : Int)) &&
          decide (t.holds 0 (h1 * 2 ^ h2.toNat)) && exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.shl w hw1 hw2 h0 h0' a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | shl =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨⟨⟨hr, hsh⟩, htr⟩, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_shl X K t w hw1 hw2 h0 h0' (iha ca hA) (ihb cb hB) hta htb
            (of_decide_eq_true hsh) (of_decide_eq_true htr)
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_shr {c : CX} {w : Nat} (hw1 : h1 < 2 ^ w) (hw2 : h2 < (w : Int)) (h0 : 0 ≤ l1)
    (h0' : 0 ≤ l2) (h : (match c with
    | .bin .shr t ca cb =>
        randOk t l1 h1 l2 h2 && decide (h2 < (t.bits : Int)) &&
          exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.shr w hw1 hw2 h0 h0' a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | shr =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨⟨hr, hsh⟩, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_shr X K t w hw1 hw2 h0 h0' (iha ca hA) (ihb cb hB) hta htb
            (of_decide_eq_true hsh)
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_lt {c : CX} (h : (match c with
    | .cmp .lt t ca cb => randOk t l1 h1 l2 h2 && exOk X.EL K a ca && exOk X.EL K b cb
    | .cmp .gt t ca cb => randOk t l2 h2 l1 h1 && exOk X.EL K b ca && exOk X.EL K a cb
    | _ => false) = true) : ExprCorr X K c (.lt a b) := by
  cases c with
  | cmp op t ca cb =>
      cases op with
      | lt =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hr, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_lt X K t (iha ca hA) (ihb cb hB) hta htb
      | gt =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hr, hA⟩, hB⟩ := h
          obtain ⟨htb, hta⟩ := randOk_sound hr
          exact ecorr_gt X K t (ihb ca hA) (iha cb hB) htb hta
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_le {c : CX} (h : (match c with
    | .cmp .le t ca cb => randOk t l1 h1 l2 h2 && exOk X.EL K a ca && exOk X.EL K b cb
    | .cmp .ge t ca cb => randOk t l2 h2 l1 h1 && exOk X.EL K b ca && exOk X.EL K a cb
    | _ => false) = true) : ExprCorr X K c (.le a b) := by
  cases c with
  | cmp op t ca cb =>
      cases op with
      | le =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hr, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_le X K t (iha ca hA) (ihb cb hB) hta htb
      | ge =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hr, hA⟩, hB⟩ := h
          obtain ⟨htb, hta⟩ := randOk_sound hr
          exact ecorr_geSwap X K t (ihb ca hA) (iha cb hB) htb hta
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_eqE {c : CX} (h : (match c with
    | .cmp .eq t ca cb => randOk t l1 h1 l2 h2 && exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.eq a b) := by
  cases c with
  | cmp op t ca cb =>
      cases op with
      | eq =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hr, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_eq X K t (iha ca hA) (ihb cb hB) hta htb
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

end BinArme

section BoolArme

variable {a b : Expr D Γ Λ .bool}
  (iha : ∀ ca, exOk X.EL K a ca = true → ExprCorr X K ca a)
  (ihb : ∀ cb, exOk X.EL K b cb = true → ExprCorr X K cb b)

include iha ihb

theorem exOk_und {c : CX} (h : (match c with
    | .land ca cb => exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.and a b) := by
  cases c with
  | land ca cb =>
      simp only [Bool.and_eq_true] at h
      exact ecorr_und X K (iha ca h.1) (ihb cb h.2)
  | _ => exact absurd h (by simp)

theorem exOk_oder {c : CX} (h : (match c with
    | .lor ca cb => exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.or a b) := by
  cases c with
  | lor ca cb =>
      simp only [Bool.and_eq_true] at h
      exact ecorr_oder X K (iha ca h.1) (ihb cb h.2)
  | _ => exact absurd h (by simp)

end BoolArme

/-- `!(e)`. -/
theorem exOk_nicht {a : Expr D Γ Λ .bool} {c : CX}
    (iha : ∀ ca, exOk X.EL K a ca = true → ExprCorr X K ca a)
    (h : (match c with | .lnot ca => exOk X.EL K a ca | _ => false) = true) :
    ExprCorr X K c (.not a) := by
  cases c with
  | lnot ca => exact ecorr_nicht X K (iha ca h)
  | _ => exact absurd h (by simp)

theorem exOk_sound : ∀ {τ : Ty} (e : Expr D Γ Λ τ) (c : CX), exOk X.EL K e c = true →
    ExprCorr X K c e
  | _, .lit _, _, h => exOk_lit X K h
  | _, .var _, _, h => exOk_var X K h
  | _, .widen (lo := lo) (hi := hi) h1 h2 e, c, h => by
      simp only [exOk, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ecorr_weiter X K h1 h2 (exOk_sound e c h)
      · cases c with
        | cast t c' =>
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            exact ecorr_weiter X K h1 h2 (ecorr_cast X K t (exOk_sound e c' h.2) h.1)
        | _ => exact absurd h (by simp)
  | _, .slot _ _ i _, _, h => exOk_ld X K h (fun _ _ => rfl) (fun ci hi => exOk_sound i ci hi)
  | _, .thru _ _ _ _ i _, _, h => exOk_ld X K h (fun _ _ => rfl) (fun ci hi => exOk_sound i ci hi)
  | _, .ptrOf _ _ _ _, _, h => ecorr_ptrOf X K (ptrOk_sound X K h)
  | _, .tru, _, h => exOk_wahr X K h
  | _, .fls, _, h => exOk_falsch X K h
  | _, .glob .., _, h => exOk_glob X K h
  | _, .add a b, _, h =>
      exOk_add X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) h
  | _, .sub a b, _, h =>
      exOk_sub X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) h
  | _, .mul a b, _, h =>
      exOk_mul X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) h
  | _, .div h0 h1' a b, _, h =>
      exOk_div X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) h0 h1' h
  | _, .rem h0 h1' a b, _, h =>
      exOk_rem X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) h0 h1' h
  | _, .sdiv hb0 a b, _, h =>
      exOk_sdiv X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) hb0 h
  | _, .srem hb0 a b, _, h =>
      exOk_srem X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) hb0 h
  | _, .band h0 h0' a b, _, h =>
      exOk_band X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) h0 h0' h
  | _, .bor _ h0 h0' hw1 hw2 a b, _, h =>
      exOk_bor X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc)
        h0 h0' hw1 hw2 h
  | _, .bxor _ h0 h0' hw1 hw2 a b, _, h =>
      exOk_bxor X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc)
        h0 h0' hw1 hw2 h
  | _, .shl _ hw1 hw2 h0 h0' a b, _, h =>
      exOk_shl X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc)
        hw1 hw2 h0 h0' h
  | _, .shr _ hw1 hw2 h0 h0' a b, _, h =>
      exOk_shr X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc)
        hw1 hw2 h0 h0' h
  | _, .lt a b, _, h =>
      exOk_lt X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) h
  | _, .le a b, _, h =>
      exOk_le X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) h
  | _, .eq a b, _, h =>
      exOk_eqE X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) h
  | _, .and a b, _, h =>
      exOk_und X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) h
  | _, .or a b, _, h =>
      exOk_oder X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) h
  | _, .not a, _, h => exOk_nicht X K (fun ca hc => exOk_sound a ca hc) h
  | _, .fnref .., _, h => absurd h (by simp [exOk])
  | _, .oldG .., _, h => absurd h (by simp [exOk])
  | _, .oldS .., _, h => absurd h (by simp [exOk])
  | _, .neg .., _, h => absurd h (by simp [exOk])
  | _, .getBytes .., _, h => absurd h (by simp [exOk])
  | _, .fllt .., _, h => absurd h (by simp [exOk])
  | _, .flle .., _, h => absurd h (by simp [exOk])
  | _, .none .., _, h => absurd h (by simp [exOk])
  | _, .some .., _, h => absurd h (by simp [exOk])
  | _, .istSome .., _, h => absurd h (by simp [exOk])
  | _, .case .., _, h => absurd h (by simp [exOk])
  | _, .why .., _, h => absurd h (by simp [exOk])
  | _, .forallSlots .., _, h => absurd h (by simp [exOk])
  | _, .existsSlots .., _, h => absurd h (by simp [exOk])
  | _, .reaches .., _, h => absurd h (by simp [exOk])

/-- **Soundness of the answer check.** -/
theorem ergOk_sound : ∀ {e : Option Ty} (r : ErgExpr D Γ Λ e) (cr : Option (CTy × CX)),
    ergOk X.EL K r cr = true → ErgCorr X K r cr := by
  intro e r cr h
  cases r with
  | empty =>
      cases cr with
      | none => rfl
      | some _ => exact absurd h (by simp [ergOk])
  | val e =>
      cases cr with
      | none => exact absurd h (by simp [ergOk])
      | some q =>
          obtain ⟨τc, ce⟩ := q
          simp only [ergOk, Bool.and_eq_true] at h
          exact ⟨τc, ce, rfl, exOk_sound X K e ce h.2, h.1⟩

/-- The value of an argument list under a map that IS the C parameter list:
    the locals relation of the bound parameters. -/
theorem argsOk_len : ∀ {τs : List Ty} (args : Args D Γ Λ τs) (cs : List CX)
    (ps : List (Nat × CTy)), argsOk X.EL K args cs ps = true → ps.length = τs.length
  | _, .nil, cs, ps, h => by
      simp only [argsOk, Bool.and_eq_true, List.isEmpty_iff] at h
      rw [h.2]; rfl
  | _, .cons _ rest, cs, ps, h => by
      match cs, ps, h with
      | _ :: cs, _ :: ps, h =>
          simp only [argsOk, Bool.and_eq_true] at h
          simp only [List.length_cons]
          rw [argsOk_len rest cs ps h.2]
      | [], _, h => simp [argsOk] at h
      | _ :: _, [], h => simp [argsOk] at h

/-- **THE ARGUMENT PASSING of a call, for every argument list**: arguments
    that are the emitted forms of Gabbro's, into C parameters that hold their
    types, establish the callee's locals relation under the map that is its
    parameter list. -/
theorem argsTo_of : ∀ {τs : List Ty} (args : Args D Γ Λ τs) (cs : List CX)
    (ps : List (Nat × CTy)), argsOk X.EL K args cs ps = true → (ps.map Prod.fst).Nodup →
    ArgsTo X K args cs ps ⟨ps.map Prod.fst, [], []⟩
  | _, .nil, cs, ps, h, _ => by
      simp only [argsOk, Bool.and_eq_true, List.isEmpty_iff] at h
      obtain ⟨hc, hp⟩ := h
      subst hc hp
      intro σ st ρG ρC _ _
      refine ⟨[], st, fun _ => .undef, rfl, SameML.refl st, rfl, ?_, ?_, ?_⟩
      · intro τ x; exact nomatch x
      · intro q hq; exact absurd hq List.not_mem_nil
      · intro q hq; exact absurd hq List.not_mem_nil
  | _, .cons (τ := τ) e rest, [], _, h, _ => by simp [argsOk] at h
  | _, .cons _ _, _ :: _, [], h, _ => by simp [argsOk] at h
  | _, .cons (τ := τ) e rest, ce :: cs, (x, τc) :: ps, h, hnd => by
      simp only [argsOk, Bool.and_eq_true] at h
      obtain ⟨⟨he, hd⟩, hrest⟩ := h
      have hnd' : (ps.map Prod.fst).Nodup := (List.nodup_cons.mp hnd).2
      have hx : x ∉ ps.map Prod.fst := (List.nodup_cons.mp hnd).1
      have hlen := argsOk_len X K rest cs ps hrest
      intro σ st ρG ρC hc hr
      obtain ⟨v, st1, h1, hv, hc1⟩ := (exOk_sound X K e ce he).run X K hc hr
      have hs1 := ev_same X.EL.lay X.orc X.fr ce st ρC v st1 h1
      obtain ⟨vs, st2, ρ1, h2, hs2, hb, hrel⟩ :=
        argsTo_of rest cs ps hrest hnd' σ st1 ρG ρC hc1 hr
      refine ⟨v :: vs, st2, lokUpd ρ1 x v, ?_, hs1.trans hs2, ?_, ?_⟩
      · simp only [evArgs, h1, h2]
      · show (match convV τc v, bindParams ps vs with
          | some v', some ρ => some (lokUpd ρ x v')
          | _, _ => none) = _
        rw [convV_of_valCorr hv hd, hb]
      · refine ⟨?_, fun q hq => absurd hq List.not_mem_nil, fun q hq => absurd hq List.not_mem_nil⟩
        intro τ' y
        cases y with
        | here =>
            show ValCorr X.EL τ (eval σ e σ ρG) (lokUpd ρ1 x v x)
            simp only [lokUpd, if_pos]
            exact hv
        | there y =>
            show ValCorr X.EL τ' ((evalArgs σ rest σ ρG).get y)
              (lokUpd ρ1 x v ((x :: ps.map Prod.fst).getD (y.idx + 1) 0))
            have hy : y.idx < (ps.map Prod.fst).length := by
              rw [List.length_map, hlen]; exact Var.idx_lt y
            have hne : (x :: ps.map Prod.fst).getD (y.idx + 1) 0 ≠ x := by
              intro heq
              apply hx
              rw [← heq]
              show (ps.map Prod.fst).getD y.idx 0 ∈ ps.map Prod.fst
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hy]
              exact List.getElem_mem _
            simp only [lokUpd]
            rw [if_neg hne]
            exact hrel.1 τ' y

end Sound

end Gabbro.Grammatik
