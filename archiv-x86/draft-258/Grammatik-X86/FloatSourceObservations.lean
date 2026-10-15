/-
  File:      Grammatik/X86/FloatSourceObservations.lean
  Subject:   Finite-value float observation equivalence over real source operations.

  Lane 624 (direct-source closure): proves which ACTUAL source observations can
  distinguish model-equivalent finite floats. Covered operators (pinned by the
  lemmas below): `fllt`/`flle` (`gleitLt`/`gleitLe`), `gleitNarrow` and `gleit`
  range-holding (`gleitPasst`), and the register-write truncation (`gleitRoh`).
  Float `==`/`!=` is EXCLUDED (F-EQ): `Expr.eq` takes only `.int` arguments, so
  no model term equates two floats. NaN non-inhabitation is a corollary: no
  `Gleit` value is NaN. Consumer hook: `cvttPaket`/`ucomiFlags` reuse pins for
  the ScalarFloat decoder consumer. Full source-to-final-bytes stays OPEN.
-/
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.Typen
import Grammatik.Gleitkomma
import Grammatik.X86.Gleitprofil
import Grammatik.X86.ScalarFloat

namespace Gabbro.Grammatik.X86

/-- Two finite floats agree on every model comparison, in all four
    directions, against every third value. This is the premise of the
    observation-equivalence fragment -- comparisons only, never a blanket
    "all observations agree" assumption. -/
def vergleichsGleich (x y : Gabbro.Grammatik.GFloat) : Prop :=
  ∀ z : Gabbro.Grammatik.GFloat,
    Gabbro.Grammatik.gleitLt x z = Gabbro.Grammatik.gleitLt y z ∧
    Gabbro.Grammatik.gleitLt z x = Gabbro.Grammatik.gleitLt z y ∧
    Gabbro.Grammatik.gleitLe x z = Gabbro.Grammatik.gleitLe y z ∧
    Gabbro.Grammatik.gleitLe z x = Gabbro.Grammatik.gleitLe z y

/-- First checked fact: signed zeros compare equal (strict, one direction). -/
theorem null_flt_still :
    Gabbro.Grammatik.gleitLt (Gleitkomma.nullN Gleitkomma.f64)
      (Gleitkomma.nullP Gleitkomma.f64) = false := by
  decide

/-! ## 1. Signed-zero class and exact value (decided facts). -/

/-- Minus zero classifies as zero. -/
theorem nullN_klasse :
    Gleitkomma.klasse Gleitkomma.f64 (Gleitkomma.nullN Gleitkomma.f64) = .null := by
  decide

/-- Plus zero classifies as zero. -/
theorem nullP_klasse :
    Gleitkomma.klasse Gleitkomma.f64 (Gleitkomma.nullP Gleitkomma.f64) = .null := by
  decide

/-- Minus zero has exact value zero. -/
theorem nullN_exakt :
    Gleitkomma.wertExakt Gleitkomma.f64 (Gleitkomma.nullN Gleitkomma.f64) =
      some ⟨0, 0⟩ := by
  decide

/-- Plus zero has exact value zero. -/
theorem nullP_exakt :
    Gleitkomma.wertExakt Gleitkomma.f64 (Gleitkomma.nullP Gleitkomma.f64) =
      some ⟨0, 0⟩ := by
  decide

/-! ## 2. Signed-zero strict-comparison agreement (all four directions). -/

/-- Strict comparison with `-0` on the left agrees with `+0` on the left. -/
theorem null_flt_links (z : Gabbro.Grammatik.GFloat) :
    Gleitkomma.flt Gleitkomma.f64 (Gleitkomma.nullN Gleitkomma.f64) z =
      Gleitkomma.flt Gleitkomma.f64 (Gleitkomma.nullP Gleitkomma.f64) z := by
  unfold Gleitkomma.flt
  rw [nullN_klasse, nullP_klasse, nullN_exakt, nullP_exakt]
  cases hz : Gleitkomma.klasse Gleitkomma.f64 z with
  | nan => rfl
  | unendlich => rfl
  | null => rfl
  | subnormal => rfl
  | normal => rfl

/-- Strict comparison with `-0` on the right agrees with `+0` on the right. -/
theorem null_flt_rechts (z : Gabbro.Grammatik.GFloat) :
    Gleitkomma.flt Gleitkomma.f64 z (Gleitkomma.nullN Gleitkomma.f64) =
      Gleitkomma.flt Gleitkomma.f64 z (Gleitkomma.nullP Gleitkomma.f64) := by
  unfold Gleitkomma.flt
  rw [nullN_klasse, nullP_klasse, nullN_exakt, nullP_exakt]
  cases hz : Gleitkomma.klasse Gleitkomma.f64 z with
  | nan => rfl
  | unendlich => rfl
  | null => rfl
  | subnormal => rfl
  | normal => rfl

/-! ## 3. Non-strict agreement and the comparison-equivalence instance. -/

/-- Non-strict comparison with `-0` on the left agrees with `+0` on the left. -/
theorem null_fle_links (z : Gabbro.Grammatik.GFloat) :
    Gleitkomma.fle Gleitkomma.f64 (Gleitkomma.nullN Gleitkomma.f64) z =
      Gleitkomma.fle Gleitkomma.f64 (Gleitkomma.nullP Gleitkomma.f64) z := by
  unfold Gleitkomma.fle
  rw [nullN_klasse, nullP_klasse, null_flt_rechts z]

/-- Non-strict comparison with `-0` on the right agrees with `+0` on the right. -/
theorem null_fle_rechts (z : Gabbro.Grammatik.GFloat) :
    Gleitkomma.fle Gleitkomma.f64 z (Gleitkomma.nullN Gleitkomma.f64) =
      Gleitkomma.fle Gleitkomma.f64 z (Gleitkomma.nullP Gleitkomma.f64) := by
  unfold Gleitkomma.fle
  rw [nullN_klasse, nullP_klasse, null_flt_links z]

/-- Signed zeros satisfy comparison agreement against every third value:
    the inhabited model-equivalent finite pair. -/
theorem null_vergleichsGleich :
    vergleichsGleich (Gleitkomma.nullN Gleitkomma.f64)
      (Gleitkomma.nullP Gleitkomma.f64) := by
  intro z
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Gleitkomma.flt Gleitkomma.f64 (Gleitkomma.nullN Gleitkomma.f64) z = _
    exact null_flt_links z
  · show Gleitkomma.flt Gleitkomma.f64 z (Gleitkomma.nullN Gleitkomma.f64) = _
    exact null_flt_rechts z
  · show Gleitkomma.fle Gleitkomma.f64 (Gleitkomma.nullN Gleitkomma.f64) z = _
    exact null_fle_links z
  · show Gleitkomma.fle Gleitkomma.f64 z (Gleitkomma.nullN Gleitkomma.f64) = _
    exact null_fle_rechts z

/-! ## 4. Observation consequences: truncation and range-holding. -/

/-- The register-write truncation agrees on signed zeros (both give `0`). -/
theorem null_roh_gleich :
    Gabbro.Grammatik.gleitRoh (Gleitkomma.nullN Gleitkomma.f64) =
      Gabbro.Grammatik.gleitRoh (Gleitkomma.nullP Gleitkomma.f64) := by
  decide

/-- Generic fragment: comparison agreement plus finiteness gives
    range-holding agreement, for every declared range. The premise is the
    comparison part only -- never a blanket all-observations assumption. -/
theorem vergleichsgleich_passt (x y : Gabbro.Grammatik.GFloat)
    (hx : Gabbro.Grammatik.gleitEndlich x = true)
    (hy : Gabbro.Grammatik.gleitEndlich y = true)
    (h : vergleichsGleich x y) (lo hi : Int × Int) :
    (Gabbro.Grammatik.gleitPasst lo hi x).isSome =
      (Gabbro.Grammatik.gleitPasst lo hi y).isSome := by
  have e1 := (h (Gabbro.Grammatik.bruch lo)).2.2.2
  have e2 := (h (Gabbro.Grammatik.bruch hi)).2.2.1
  unfold Gabbro.Grammatik.gleitPasst
  by_cases hP : Gabbro.Grammatik.gleitEndlich x = true ∧
      Gabbro.Grammatik.gleitLe (Gabbro.Grammatik.bruch lo) x = true ∧
      Gabbro.Grammatik.gleitLe x (Gabbro.Grammatik.bruch hi) = true
  · have hQ : Gabbro.Grammatik.gleitEndlich y = true ∧
        Gabbro.Grammatik.gleitLe (Gabbro.Grammatik.bruch lo) y = true ∧
        Gabbro.Grammatik.gleitLe y (Gabbro.Grammatik.bruch hi) = true := by
      obtain ⟨-, b, c⟩ := hP
      exact ⟨hy, by rw [← e1]; exact b, by rw [← e2]; exact c⟩
    rw [dif_pos hP, dif_pos hQ]; rfl
  · have hQ : ¬ (Gabbro.Grammatik.gleitEndlich y = true ∧
        Gabbro.Grammatik.gleitLe (Gabbro.Grammatik.bruch lo) y = true ∧
        Gabbro.Grammatik.gleitLe y (Gabbro.Grammatik.bruch hi) = true) := by
      intro hQ
      obtain ⟨-, b, c⟩ := hQ
      apply hP
      exact ⟨hx, by rw [e1]; exact b, by rw [e2]; exact c⟩
    rw [dif_neg hP, dif_neg hQ]

/-- Range-holding agrees on signed zeros, for every declared range. -/
theorem null_passt_gleich (lo hi : Int × Int) :
    (Gabbro.Grammatik.gleitPasst lo hi (Gleitkomma.nullN Gleitkomma.f64)).isSome =
      (Gabbro.Grammatik.gleitPasst lo hi
        (Gleitkomma.nullP Gleitkomma.f64)).isSome :=
  vergleichsgleich_passt _ _ (by decide) (by decide) null_vergleichsGleich lo hi

/-! ## 5. NaN non-inhabitation (honestly labelled corollary). -/

/-- No accepted float value is NaN: a `Gleit` carries its finiteness proof.
    NaN-payload non-observability holds vacuously -- there is no NaN value
    to observe. -/
theorem kein_gleit_nan (lo hi : Int × Int) (v : Gabbro.Grammatik.Gleit lo hi) :
    Gleitkomma.klasse Gleitkomma.f64 v.x ≠ .nan := by
  intro hcon
  have he := v.endlich
  unfold Gabbro.Grammatik.gleitEndlich at he
  rw [hcon] at he
  exact Bool.false_ne_true he

/-! ## 6. F-EQ exclusion: model equality observes integers only. -/

/-- `eval` of `fllt` IS the model strict comparison -- the covered operator,
    pinned to its actual `eval` arm. -/
theorem eval_fllt_ist_gleitLt {D : Gabbro.Grammatik.Deklaration}
    {Γ : Gabbro.Grammatik.Ctx} {Λ : List (Gabbro.Grammatik.Res D)}
    {l1 h1 l2 h2 : Int × Int} (σ₀ σ : Gabbro.Grammatik.World D)
    (ρ : Gabbro.Grammatik.Env D Γ)
    (a : Gabbro.Grammatik.Expr D Γ Λ (Gabbro.Grammatik.Ty.fl l1 h1))
    (b : Gabbro.Grammatik.Expr D Γ Λ (Gabbro.Grammatik.Ty.fl l2 h2)) :
    Gabbro.Grammatik.eval σ₀ (Gabbro.Grammatik.Expr.fllt a b) σ ρ =
      Gabbro.Grammatik.gleitLt (Gabbro.Grammatik.eval σ₀ a σ ρ).x
        (Gabbro.Grammatik.eval σ₀ b σ ρ).x := rfl

/-- `eval` of `flle` IS the model non-strict comparison -- the covered operator. -/
theorem eval_flle_ist_gleitLe {D : Gabbro.Grammatik.Deklaration}
    {Γ : Gabbro.Grammatik.Ctx} {Λ : List (Gabbro.Grammatik.Res D)}
    {l1 h1 l2 h2 : Int × Int} (σ₀ σ : Gabbro.Grammatik.World D)
    (ρ : Gabbro.Grammatik.Env D Γ)
    (a : Gabbro.Grammatik.Expr D Γ Λ (Gabbro.Grammatik.Ty.fl l1 h1))
    (b : Gabbro.Grammatik.Expr D Γ Λ (Gabbro.Grammatik.Ty.fl l2 h2)) :
    Gabbro.Grammatik.eval σ₀ (Gabbro.Grammatik.Expr.flle a b) σ ρ =
      Gabbro.Grammatik.gleitLe (Gabbro.Grammatik.eval σ₀ a σ ρ).x
        (Gabbro.Grammatik.eval σ₀ b σ ρ).x := rfl

/-- `eval` of `eq` observes INTEGER values only (`decide` on `.n`): `Expr.eq`
    takes `.int` arguments by construction, so no model term equates two
    floats. Checker-accepted float `==`/`!=` (F-EQ) has no meaning here --
    it stays a tracked separate prerequisite, explicitly outside this lemma. -/
theorem eval_eq_beobachtet_int {D : Gabbro.Grammatik.Deklaration}
    {Γ : Gabbro.Grammatik.Ctx} {Λ : List (Gabbro.Grammatik.Res D)}
    {l1 h1 l2 h2 : Int} (σ₀ σ : Gabbro.Grammatik.World D)
    (ρ : Gabbro.Grammatik.Env D Γ)
    (a : Gabbro.Grammatik.Expr D Γ Λ (Gabbro.Grammatik.Ty.int l1 h1))
    (b : Gabbro.Grammatik.Expr D Γ Λ (Gabbro.Grammatik.Ty.int l2 h2)) :
    Gabbro.Grammatik.eval σ₀ (Gabbro.Grammatik.Expr.eq a b) σ ρ =
      decide ((Gabbro.Grammatik.eval σ₀ a σ ρ).n =
        (Gabbro.Grammatik.eval σ₀ b σ ρ).n) := rfl

/-! ## 7. Target reuse hooks for the ScalarFloat decoder consumer. -/

/-- The witness zero patterns are well-formed words. -/
theorem null_wf :
    Gleitkomma.wf Gleitkomma.f64 (Gleitkomma.nullN Gleitkomma.f64) ∧
      Gleitkomma.wf Gleitkomma.f64 (Gleitkomma.nullP Gleitkomma.f64) := by
  decide

/-- Exact word round-trip of the witness zeros: the consumer transports
    target words back to source values bit-exactly -- stronger than the
    class-level `fpRechne_klasse`, which stays the rule for computed NaNs. -/
theorem null_muster_rundweg :
    bites64 (muster64 (Gleitkomma.nullN Gleitkomma.f64)) =
        Gleitkomma.nullN Gleitkomma.f64 ∧
      bites64 (muster64 (Gleitkomma.nullP Gleitkomma.f64)) =
        Gleitkomma.nullP Gleitkomma.f64 := by
  exact ⟨bites64_muster64 _ (by decide), bites64_muster64 _ (by decide)⟩

/-- UCOMISD equal row on the witness pair: target flags report equality,
    matching source `fle`-both-true (`null_fle_links`/`null_fle_rechts`). -/
theorem null_ucomi_gleich :
    ucomiFlags (Gleitkomma.nullN Gleitkomma.f64)
      (Gleitkomma.nullP Gleitkomma.f64) =
      ⟨false, false, some false, true, false, false⟩ := by
  decide

/-- CVTTSD2SI wrapper unfolded once, without the body `let`: a
    klasse/wertExakt dispatch on the injected value. Proved by `rfl`, so the
    main proof below never unfolds through the `let`. -/
theorem cvttPaket_entfaltet (w : Wort) :
    cvttPaket w =
      (match Gleitkomma.klasse Gleitkomma.f64 (bites64 w) with
      | .nan => 0
      | .unendlich => 0
      | _ =>
        match Gleitkomma.wertExakt Gleitkomma.f64 (bites64 w) with
        | Option.none => 0
        | Option.some v =>
          let t : Int :=
            if 0 ≤ v.zweierExp then v.zaehler * ((2 ^ v.zweierExp.toNat : Nat) : Int)
            else v.zaehler.tdiv ((2 ^ (-v.zweierExp).toNat : Nat) : Int)
          if t < -(2 ^ 63 : Int) then -(2 ^ 63 : Int)
          else if (2 ^ 63 - 1 : Int) < t then 2 ^ 63 - 1 else t) := rfl

/-- CVTTSD2SI wrapper equals source truncation on finite well-formed values:
    the decoder consumer reuses `gleitRoh` through `cvttPaket` instead of
    reproving truncation. Payload equality is NOT claimed -- the model only
    preserves class (`fpRechne_klasse`). -/
theorem cvttPaket_gleitRoh (x : Gabbro.Grammatik.GFloat)
    (hw : Gleitkomma.wf Gleitkomma.f64 x)
    (hx : Gabbro.Grammatik.gleitEndlich x = true) :
    cvttPaket (muster64 x) = Gabbro.Grammatik.gleitRoh x := by
  have hr : bites64 (muster64 x) = x := bites64_muster64 x hw
  rw [cvttPaket_entfaltet]
  unfold Gabbro.Grammatik.gleitRoh
  rw [hr]
  cases hk : Gleitkomma.klasse Gleitkomma.f64 x with
  | nan =>
    cases he : Gleitkomma.wertExakt Gleitkomma.f64 x with
    | none => rfl
    | some v =>
      unfold Gabbro.Grammatik.gleitEndlich at hx
      rw [hk] at hx
      exact (Bool.false_ne_true hx).elim
  | unendlich =>
    cases he : Gleitkomma.wertExakt Gleitkomma.f64 x with
    | none => rfl
    | some v =>
      unfold Gabbro.Grammatik.gleitEndlich at hx
      rw [hk] at hx
      exact (Bool.false_ne_true hx).elim
  | null =>
    cases he : Gleitkomma.wertExakt Gleitkomma.f64 x with
    | none => rfl
    | some v => rfl
  | subnormal =>
    cases he : Gleitkomma.wertExakt Gleitkomma.f64 x with
    | none => rfl
    | some v => rfl
  | normal =>
    cases he : Gleitkomma.wertExakt Gleitkomma.f64 x with
    | none => rfl
    | some v => rfl

/-! ## 8. Witness: one float table, one writing contract, one step. -/

/-- Witness signature: parameterless, no answer, writes the table. -/
def fltWitSig : Gabbro.Grammatik.Signatur Unit Empty Empty Empty :=
  { params := [], erg := none, gruende := 0, haelt := [],
    schreibt := fun _ => true, gschreibt := fun g => (nomatch g),
    konsumiert := [], produziert := [], boden := none }

/-- Witness declaration: one table with one `.fl (0,1) (1,1)` field, one
    parameterless function whose contract writes it, nothing else. -/
def fltWitD : Gabbro.Grammatik.Deklaration where
  Tab := Unit
  count := fun _ => 1
  Feld := fun _ => Unit
  typ := fun _ _ => .fl (0, 1) (1, 1)
  erlaubt := fun _ _ _ _ => true
  tabNr := fun _ => some ()
  Glob := Empty
  gtyp := fun g => nomatch g
  nutzlast := fun g => nomatch g
  atomar := fun g => nomatch g
  geteilt := fun _ => false
  ggeteilt := fun g => nomatch g
  Lock := Empty
  rang := fun L => nomatch L
  maskiert := fun L => nomatch L
  Marke := Empty
  stufen := fun m => nomatch m
  braucht := fun _ => []
  gbraucht := fun g => nomatch g
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => fltWitSig
  eigner_nie_erzeugt := fun n t m s _ => nomatch m
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Empty
  aparams := fun a => nomatch a
  aerg := fun a => nomatch a
  aschreibt := fun a => nomatch a
  agschreibt := fun a => nomatch a
  Reg := Empty
  rtyp := fun r => nomatch r
  rklasse := fun r => nomatch r
  spiegel := fun r => nomatch r
  rzusage := fun r => nomatch r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun n i _ => nomatch i
  ggeteilt_bewacht := fun g => nomatch g

/-- The witness contract: writes the table. -/
def fltWitV : Gabbro.Grammatik.Vertrag fltWitD :=
  { schreibt := fun _ => true
    gschreibt := fun g => nomatch g
    erg := none
    gruende := 0
    haelt := []
    produziert := []
    boden := none }

/-- The witness oracle: no axioms, registers or globals to answer. -/
def fltWitO : Gabbro.Grammatik.Orakel fltWitD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun g => nomatch g

/-- The witness callee table: every call succeeds without moving memory. -/
def fltWitR : ∀ f : fltWitD.Fn, Gabbro.Grammatik.World fltWitD →
    Gabbro.Grammatik.Env fltWitD (fltWitD.params f) →
    Gabbro.Grammatik.RufAusgang f :=
  fun _ σ _ => .ok σ ()

/-- Minus zero in `0 .. 1`: finite and inside (decided actual operations). -/
def minusGleit : Gabbro.Grammatik.Gleit (0, 1) (1, 1) :=
  ⟨Gleitkomma.nullN Gleitkomma.f64, by decide, by decide, by decide⟩

/-- Plus zero in `0 .. 1`: finite and inside (decided actual operations). -/
def plusGleit : Gabbro.Grammatik.Gleit (0, 1) (1, 1) :=
  ⟨Gleitkomma.nullP Gleitkomma.f64, by decide, by decide, by decide⟩

/-- The witness world: the slot holds `-0`, no trace yet. -/
def fltWitSigma : Gabbro.Grammatik.World fltWitD where
  slots := fun t _ f => by cases t; cases f; exact minusGleit
  globs := fun g => nomatch g
  spur := []

/-- The witness environment: the variable to write holds `+0`. -/
def fltWitRho :
    Gabbro.Grammatik.Env fltWitD [Gabbro.Grammatik.Ty.fl (0, 1) (1, 1)] :=
  Gabbro.Grammatik.Env.cons plusGleit Gabbro.Grammatik.Env.nil

/-- The witness index: row 0 (in the same context as the value). -/
def fltWitI :
    Gabbro.Grammatik.Expr fltWitD [Gabbro.Grammatik.Ty.fl (0, 1) (1, 1)] []
      (Gabbro.Grammatik.Ty.index (fltWitD.count ())) :=
  Gabbro.Grammatik.Expr.lit 0

/-- The witness value expression: the variable holding `+0`. -/
def fltWitE :
    Gabbro.Grammatik.Expr fltWitD [Gabbro.Grammatik.Ty.fl (0, 1) (1, 1)] []
      (fltWitD.typ () ()) :=
  Gabbro.Grammatik.Expr.var Gabbro.Grammatik.Var.hier

/-- The witness field type. -/
theorem fltWitHT : fltWitD.typ () () = Gabbro.Grammatik.Ty.fl (0, 1) (1, 1) :=
  rfl

/-- The witness contract writes the table. -/
theorem fltWitHw : fltWitV.schreibt () = true := rfl

/-- The witness function writes the table. -/
theorem fltWitSchreibt : fltWitD.schreibt () () = true := rfl

/-- The witness table needs no guards. -/
theorem fltWitHL : Gabbro.Grammatik.darf fltWitD () [] :=
  fun _ h => False.elim (List.not_mem_nil h)

/-! ## 9. Joint witness: one table write, memory-changing, observations agree. -/

/-- JOINT WITNESS: the contract and the function write the one float table;
    the reached one-step run changes the slot `-0 -> +0` (bit patterns
    differ: `zuBits` disagrees); every covered source observation agrees on
    the two values -- comparisons (`vergleichsGleich`), truncation
    (`gleitRoh`), range-holding (`gleitPasst`). -/
theorem null_beobachtung_zeuge :
    ∃ (σ' : Gabbro.Grammatik.World fltWitD)
      (ρ' : Gabbro.Grammatik.Env fltWitD
        [Gabbro.Grammatik.Ty.fl (0, 1) (1, 1)]),
      fltWitD.schreibt () () = true ∧
      fltWitV.schreibt () = true ∧
      Gabbro.Grammatik.execStmt fltWitO 0 fltWitR
        (Gabbro.Grammatik.Stmt.assignSlot (l := false) () () fltWitI fltWitE
          fltWitHw fltWitHL)
        fltWitSigma fltWitRho = .ok σ' ρ' ∧
      (fltWitSigma.slots () 0 ()).x = Gleitkomma.nullN Gleitkomma.f64 ∧
      (σ'.slots () 0 ()).x = Gleitkomma.nullP Gleitkomma.f64 ∧
      (fltWitSigma.slots () 0 ()).x ≠ (σ'.slots () 0 ()).x ∧
      vergleichsGleich (fltWitSigma.slots () 0 ()).x (σ'.slots () 0 ()).x ∧
      Gabbro.Grammatik.gleitRoh (fltWitSigma.slots () 0 ()).x =
        Gabbro.Grammatik.gleitRoh (σ'.slots () 0 ()).x ∧
      (Gabbro.Grammatik.gleitPasst (0, 1) (1, 1)
        (fltWitSigma.slots () 0 ()).x).isSome =
        (Gabbro.Grammatik.gleitPasst (0, 1) (1, 1)
          (σ'.slots () 0 ()).x).isSome ∧
      Gleitkomma.zuBits Gleitkomma.f64 (fltWitSigma.slots () 0 ()).x ≠
        Gleitkomma.zuBits Gleitkomma.f64 (σ'.slots () 0 ()).x := by
  have hExecFull : ∃ σ' ρ', Gabbro.Grammatik.execStmt fltWitO 0 fltWitR
      (Gabbro.Grammatik.Stmt.assignSlot (l := false) () () fltWitI fltWitE
        fltWitHw fltWitHL)
      fltWitSigma fltWitRho = .ok σ' ρ' := by
    simp only [Gabbro.Grammatik.execStmt]
    exact ⟨_, _, rfl⟩
  obtain ⟨σ', ρ', hExec⟩ := hExecFull
  have hBefore : (fltWitSigma.slots () 0 ()).x =
      Gleitkomma.nullN Gleitkomma.f64 := rfl
  have hAfter : (σ'.slots () 0 ()).x =
      Gleitkomma.nullP Gleitkomma.f64 := by
    cases hExec
    rfl
  have hNe : (fltWitSigma.slots () 0 ()).x ≠ (σ'.slots () 0 ()).x := by
    rw [hBefore, hAfter]
    decide
  have hVgl : vergleichsGleich (fltWitSigma.slots () 0 ()).x
      (σ'.slots () 0 ()).x := by
    rw [hBefore, hAfter]
    exact null_vergleichsGleich
  have hRoh : Gabbro.Grammatik.gleitRoh (fltWitSigma.slots () 0 ()).x =
      Gabbro.Grammatik.gleitRoh (σ'.slots () 0 ()).x := by
    rw [hBefore, hAfter]
    exact null_roh_gleich
  have hPasst : (Gabbro.Grammatik.gleitPasst (0, 1) (1, 1)
        (fltWitSigma.slots () 0 ()).x).isSome =
        (Gabbro.Grammatik.gleitPasst (0, 1) (1, 1)
          (σ'.slots () 0 ()).x).isSome := by
    rw [hBefore, hAfter]
    exact null_passt_gleich (0, 1) (1, 1)
  have hBits : Gleitkomma.zuBits Gleitkomma.f64
        (fltWitSigma.slots () 0 ()).x ≠
        Gleitkomma.zuBits Gleitkomma.f64 (σ'.slots () 0 ()).x := by
    rw [hBefore, hAfter]
    decide
  exact ⟨σ', ρ', fltWitSchreibt, fltWitHw, hExec, hBefore, hAfter, hNe, hVgl,
    hRoh, hPasst, hBits⟩

/-! ## 10. Refusals: NaN and out-of-range answers never fit. -/

/-- A NaN gate/oracle answer is refused at `einpassen` (`gleitWortPasst`
    takes the same `none` branch through `gleitPasst`). -/
theorem nan_passt_verweigert (lo hi : Int × Int) :
    (Gabbro.Grammatik.gleitPasst lo hi
      (Gleitkomma.nanQ Gleitkomma.f64)).isSome = false := by
  have hfin :
      Gabbro.Grammatik.gleitEndlich (Gleitkomma.nanQ Gleitkomma.f64) = false := by
    decide
  have hneg : ¬ (Gabbro.Grammatik.gleitEndlich
        (Gleitkomma.nanQ Gleitkomma.f64) = true ∧
      Gabbro.Grammatik.gleitLe (Gabbro.Grammatik.bruch lo)
        (Gleitkomma.nanQ Gleitkomma.f64) = true ∧
      Gabbro.Grammatik.gleitLe (Gleitkomma.nanQ Gleitkomma.f64)
        (Gabbro.Grammatik.bruch hi) = true) := by
    intro hcon
    rw [hfin] at hcon
    exact Bool.false_ne_true hcon.1
  unfold Gabbro.Grammatik.gleitPasst
  rw [dif_neg hneg]
  rfl

/-- A computed answer outside its declared range is refused at the same
    branch (`5.0` against `0 .. 1`): range-holding observes the class. -/
theorem bereich_passt_verweigert :
    (Gabbro.Grammatik.gleitPasst (0, 1) (1, 1)
      (Gabbro.Grammatik.gleitAusInt 5)).isSome = false := by
  decide

/-! ## 11. Inhabitation companions for the syntax-quantified `eval` pins. -/

/-- Joint instance of `eval_fllt_ist_gleitLt` on the witness declaration. -/
theorem eval_fllt_ist_gleitLt_zeuge :
    Gabbro.Grammatik.eval fltWitSigma
        (Gabbro.Grammatik.Expr.fllt fltWitE fltWitE) fltWitSigma fltWitRho =
      Gabbro.Grammatik.gleitLt
        (Gabbro.Grammatik.eval fltWitSigma fltWitE fltWitSigma fltWitRho).x
        (Gabbro.Grammatik.eval fltWitSigma fltWitE fltWitSigma fltWitRho).x :=
  eval_fllt_ist_gleitLt _ _ _ _ _

/-- Joint instance of `eval_flle_ist_gleitLe` on the witness declaration. -/
theorem eval_flle_ist_gleitLe_zeuge :
    Gabbro.Grammatik.eval fltWitSigma
        (Gabbro.Grammatik.Expr.flle fltWitE fltWitE) fltWitSigma fltWitRho =
      Gabbro.Grammatik.gleitLe
        (Gabbro.Grammatik.eval fltWitSigma fltWitE fltWitSigma fltWitRho).x
        (Gabbro.Grammatik.eval fltWitSigma fltWitE fltWitSigma fltWitRho).x :=
  eval_flle_ist_gleitLe _ _ _ _ _

/-- Joint instance of `eval_eq_beobachtet_int` on the witness declaration. -/
theorem eval_eq_beobachtet_int_zeuge :
    Gabbro.Grammatik.eval fltWitSigma
        (Gabbro.Grammatik.Expr.eq fltWitI fltWitI) fltWitSigma fltWitRho =
      decide ((Gabbro.Grammatik.eval fltWitSigma fltWitI fltWitSigma fltWitRho).n =
        (Gabbro.Grammatik.eval fltWitSigma fltWitI fltWitSigma fltWitRho).n) :=
  eval_eq_beobachtet_int _ _ _ _ _

/- CUTS:
    - Covered source operators, pinned to actual `eval`/`exec` arms:
      `fllt`/`flle` (`gleitLt`/`gleitLe`), `gleitNarrow` and `gleit`
      range-holding (`gleitPasst`), register-write truncation (`gleitRoh`).
      Comparison agreement and all consequences are proved for the
      inhabited model-equivalent finite pair `-0`/`+0`; range-holding
      agreement is proved GENERICALLY from comparison agreement plus
      finiteness (`vergleichsgleich_passt`, every range).
    - F-EQ is EXCLUDED, not closed: `Expr.eq` takes only `.int` arguments
      (`eval_eq_beobachtet_int`), so no model term equates two floats.
      Refusing checker-accepted float `==`/`!=` is a tracked separate
      prerequisite (closure P0); no checker file is touched here.
    - Generic comparison-agreement-implies-truncation-agreement is NOT
      proved: from `vergleichsGleich` alone, `gleitRoh` agreement needs
      exact-value uniqueness, which is open. Proved for the inhabited
      `-0`/`+0` pair (`null_roh_gleich`). This is an explicit obstruction,
      not a hardware axiom.
    - Payload equality is NEVER claimed: the target side preserves class
      only (`fpRechne_klasse` stays the rule for computed values); the
      word round-trip (`null_muster_rundweg`) and `ucomiFlags`/`cvttPaket`
      hooks are reuse pins at word level, not decoded-byte steps. The
      decoder (`Codec`) has no FP forms (audit finding, unchanged): no
      byte sequence decodes to a float form today.
    - The witness is a one-step `assignSlot` run (no calls, loops, locks,
      atomics, gates): joint table-write plus memory-changing step with
      agreeing observations and disagreeing bit patterns. sNaN-quieting
      divergence stays conditional on the unreachable sNaN operand;
      MXCSR/sticky flags have no source channel (no form reads them).
    - Full source-to-final-loaded-bytes validation remains OPEN until a
      generic closing proof is derived.
-/

#print axioms null_flt_still
#print axioms null_vergleichsGleich
#print axioms vergleichsgleich_passt
#print axioms null_passt_gleich
#print axioms null_roh_gleich
#print axioms kein_gleit_nan
#print axioms eval_fllt_ist_gleitLt
#print axioms eval_flle_ist_gleitLe
#print axioms eval_eq_beobachtet_int
#print axioms null_wf
#print axioms null_muster_rundweg
#print axioms null_ucomi_gleich
#print axioms cvttPaket_entfaltet
#print axioms cvttPaket_gleitRoh
#print axioms null_beobachtung_zeuge
#print axioms nan_passt_verweigert
#print axioms bereich_passt_verweigert
#print axioms eval_fllt_ist_gleitLt_zeuge
#print axioms eval_flle_ist_gleitLe_zeuge
#print axioms eval_eq_beobachtet_int_zeuge

end Gabbro.Grammatik.X86
