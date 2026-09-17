/-
  File:      Grammatik/Zielsatz/PoolSym.lean
  Subject:   The symmetric worker pool (lane 245): one routine on N threads.

  The checker admits `concurrent { f, f }` (the same routine twice) IFF the
  routine is pool-safe: it holds no lock by signature, declares no reasons,
  and every carrier its thread graphs may write is guarded by a lock or
  atomic (`fusswache2.rs`, narrowed `N304`). This file is the model side of
  that condition: the separation lemma for two threads running one
  pool-safe routine (`PoolSicher` itself, with `PoolSicherW`/`EinzelnPool`,
  lives in `Zielsatz/Spec.lean`, beside `Ruhig`/`StartZulaessig`), the
  decidable pool checks, and the race-freedom and lock legs over
  multiset starts. `Spec.lean`'s `einzeln`/`Laufzeit.einmal` are extended
  by `EinzelnPool`, never weakened (old acceptances preserved, proved);
  the field-type swap itself is specified in MUSE-REPORT-245.md.
-/
import Grammatik.Zielsatz.Akzeptiert
import Grammatik.ReferenzB

namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

/-! ## The separation lemma for a symmetric pair -/

/-- **No unguarded writes on a pool-safe thread.** If thread `t` starts the
    pool-safe routine `w`, no function of its computed graph writes an
    unguarded, non-atomic carrier. Applied to both threads of a symmetric
    pair, no write-write and no write-read race on unguarded carriers
    exists -- the model half of the narrowed `N304`. The footprint half of
    `SchreibGetrenntK` is NOT claimed: a pool-safe routine may read
    unguarded carriers it never writes. -/
theorem pool_schreibt_nicht {P : Programm D} {fs : List D.Fn} {w : D.Fn}
    [DecidableEq D.Fn]
    {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    {t : Faden} (ht : (init t).1 = w)
    (hpool : PoolSicher D (reachB P fs w) w)
    {c : D.Tab ⊕ D.Glob} (hB : ∀ L, ¬ Bewacht c L) (hAt : ¬ AtomarAusgenommen c)
    {g : D.Fn} (hg : kVon P fs init t g = true) :
    TraegerSchreibt g c = false := by
  have hg' : reachB P fs w g = true := by
    unfold kVon at hg
    rw [ht] at hg
    exact hg
  cases hc : TraegerSchreibt g c with
  | true =>
      rcases hpool.2.2 g hg' c hc with ⟨L, hL⟩ | hA
      · exact absurd hL (hB L)
      · exact absurd hA hAt
  | false => rfl

/-! ## The lock-free fixture variant -/

/-- `einzahlen` without the signature-held lock and without global writes:
    the pool worker starts empty-handed. Single-field updates: each parses
    and elaborates alone (multi-field `with` with proof lambdas trips the
    in-tree term parser; see the commit history). -/
def poolSigEin : Signatur Unit Unit Unit Empty :=
  { { refSigEin with haelt := [] } with gschreibt := fun _ => false }

/-- `lies` without the signature-held lock and without global writes. -/
def poolSigLies : Signatur Unit Unit Unit Empty :=
  { { refSigLies with haelt := [] } with gschreibt := fun _ => false }

/-- Signature table of the lock-free variant: `einzahlen` at 0. -/
def poolSigNr : Nat → Signatur Unit Unit Unit Empty
  | 0 => poolSigEin
  | _ => poolSigLies

/-- The `eigner` proof for the variant: `eigner` is empty, so any member
    eliminates. A named theorem (not an inline lambda): only names survive
    the struct-update parser in this import context. Stated against the
    variant's own literals, since the `where` elaborator substitutes field
    values into later proof obligations. -/
theorem poolEignerNie : ∀ (n : Nat) (_t : Unit) (m : Empty) (s : Nat),
    m ∈ ([] : List Empty) → (m, s) ∉ (poolSigNr n).produziert :=
  fun _ _ m _ _ => Empty.elim m

/-- The invariant proof for the variant: there are no invariants, so any
    index eliminates. Stated against the variant's own literals (`Empty.elim`,
    not `nomatch`: the match-compiler term is not defeq to `Empty.elim`). -/
theorem poolInvGehalten : ∀ (n : Nat) (i : Empty),
    (Empty.elim i : List Unit).any (poolSigNr n).schreibt = true → ∀ (t : Unit),
      t ∈ (Empty.elim i : List Unit) → ∀ (L : Unit),
        Sum.inl L ∈ ([Sum.inl ()] : List (Unit ⊕ (Empty × Nat))) →
          L ∈ (poolSigNr n).haelt :=
  fun _ i => Empty.elim i

/-- The lock-free variant of the reference fixture: one table `konto`
    guarded by the single lock (`braucht` kept), one unguarded, non-atomic,
    never-written global `frei` (the witness carrier for `hB`/`hAt`),
    both functions starting with empty hands. A full `where` literal, so
    no struct-update parsing is involved at all; `geteilt_bewacht` is
    copied from `refD` (same shape, same proof). -/
def poolD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Unit
  decGlob := inferInstance
  gtyp := fun _ => .int 0 1
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun _ => true
  ggeteilt := fun _ => false
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => Empty.elim e
  braucht := fun _ => [.inl ()]
  gbraucht := fun _ => []
  eigner := fun _ => []
  Fn := Bool
  sig := fun | true => 0 | false => 1
  sigNr := poolSigNr
  eigner_nie_erzeugt := poolEignerNie
  Inv := Empty
  traeger := fun e => Empty.elim e
  invs := []
  Ax := Empty
  aparams := fun e => Empty.elim e
  aerg := fun e => Empty.elim e
  aschreibt := fun e _ => Empty.elim e
  agschreibt := fun e _ => Empty.elim e
  Reg := Empty
  rtyp := fun e => Empty.elim e
  rklasse := fun e => Empty.elim e
  spiegel := fun e => Empty.elim e
  rzusage := fun r _ => Empty.elim r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t _ => by decide
  invarianten_gehalten := poolInvGehalten
  ggeteilt_bewacht := fun g h => absurd h (by decide)

/-- Parameters of `einzahlen` on the variant, by computation. -/
theorem poolEin_params : poolD.params true = [.int 0 10] := rfl

/-- The witness argument: 7 in `.int 0 10` (same shape as `refRho7`). -/
def poolRho : Env poolD (poolD.params true) :=
  poolEin_params.symm ▸ (.cons ⟨7, by decide, by decide⟩ .nil :
    Env poolD [.int 0 10])

/-- The trivial program over the variant: `wahr` contracts and `ret`
    bodies. The witness graph (`fs = []`) never unfolds a body, so no
    body needs to mean anything; they only need to typecheck. -/
def poolP : Programm poolD where
  invariante := fun i => Empty.elim i
  requires := fun | true => Expr.wahr | false => Expr.wahr
  ensures := fun | true => Expr.wahr | false => Expr.wahr
  rumpf := fun
    | true => Endblock.ret ErgExpr.keine (List.Perm.refl _)
    | false =>
        Endblock.ret
          (ErgExpr.wert (Expr.weiter (by decide) (by decide) (Expr.lit 7)))
          (List.Perm.refl _)

/-! ## The decidable pool checks -/

section PoolBool

variable [DecidableEq D.Fn]

/-- **Pool-safe, decided**: no signature lock, no reasons, and every
    function the graph reaches writes only carriers of the list `cs`
    that are guarded or atomic. Decides `PoolSicherW` given complete
    member lists (mirrors `ruheB`/`ruheB_iff`). -/
def poolSicherWB (P : Programm D) (fs : List D.Fn) (cs : List (D.Tab ⊕ D.Glob))
    (w : D.Fn) : Bool :=
  (D.haelt w).isEmpty && decide (D.gruende w = 0) && fs.all fun f =>
    !(reachB P fs w f) ||
      (cs.all fun c => !(TraegerSchreibt f c) ||
        (!(waechterVon c).isEmpty || atomarB c))

theorem poolSicherWB_iff {P : Programm D} {fs : List D.Fn}
    {cs : List (D.Tab ⊕ D.Glob)}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    {w : D.Fn} : poolSicherWB P fs cs w = true ↔ PoolSicherW P fs w := by
  unfold poolSicherWB PoolSicherW PoolSicher
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, fun f hf c hc => ?_⟩
    have h4 := (List.all_eq_true.mp h3) f (hvoll f)
    rw [hf] at h4
    simp only [Bool.not_true, Bool.false_or] at h4
    have h5 := (List.all_eq_true.mp h4) c (hcs c)
    rw [hc] at h5
    simp only [Bool.not_true, Bool.false_or] at h5
    cases hl : waechterVon c with
    | nil =>
        have he : (([] : List D.Lock).isEmpty) = true := rfl
        rw [hl, he] at h5
        simp only [Bool.not_true, Bool.false_or] at h5
        cases c with
        | inl _ => simp [atomarB] at h5
        | inr g => exact Or.inr ⟨g, rfl, h5⟩
    | cons L _ => exact Or.inl ⟨L, waechterVon_mem.mp (hl.symm ▸ List.mem_cons_self)⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, List.all_eq_true.mpr fun f _ => ?_⟩
    cases hf : reachB P fs w f with
    | false => rfl
    | true =>
        refine List.all_eq_true.mpr fun c _ => ?_
        cases hc : TraegerSchreibt f c with
        | false => rfl
        | true =>
            rcases h3 f hf c hc with ⟨L, hL⟩ | ⟨g, rfl, hg⟩
            · have he : (waechterVon c).isEmpty = false := by
                have hmem : L ∈ waechterVon c := waechterVon_mem.mpr hL
                cases hl : waechterVon c with
                | nil => rw [hl] at hmem; cases hmem
                | cons _ _ => rfl
              rw [he]
              rfl
            · have hag : atomarB (.inr g) = true := hg
              simp [hag]

/-- Filtering for an absent value leaves nothing. -/
theorem pool_filter_nil {l : List D.Fn} {w : D.Fn} (h : w ∉ l) :
    l.filter (fun v => decide (v = w)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.filter_cons]
      by_cases he : decide (a = w) = true
      · have haw : a = w := of_decide_eq_true he
        rw [haw] at h
        exact absurd List.mem_cons_self h
      · simp only [he]
        exact ih (fun hm => h (List.mem_cons_of_mem _ hm))

/-- A routine occurring in a repetition-free list occurs at most once:
    filtering for it leaves at most one element. (The one induction the
    `Nodup` bridge needs; everything below assembles from it.) -/
theorem nodup_filter_length_le_one {ws : List D.Fn} (hnd : ws.Nodup)
    (w : D.Fn) : (ws.filter (fun v => decide (v = w))).length ≤ 1 := by
  induction ws with
  | nil => simp
  | cons a l ih =>
      obtain ⟨hna, hndl⟩ := List.nodup_cons.mp hnd
      by_cases he : decide (a = w) = true
      · have haw : a = w := of_decide_eq_true he
        subst w
        have hempty : l.filter (fun v => decide (v = a)) = [] :=
          pool_filter_nil hna
        simp [hempty]
      · simp [he]
        exact ih hndl

/-- **Duplicates allowed iff pool-safe, decided**: every declared start
    occurring at least twice is pool-safe at its computed graph. Decides
    `EinzelnPool` given complete member lists. -/
def einzelnPoolB (P : Programm D) (fs : List D.Fn) (cs : List (D.Tab ⊕ D.Glob))
    (ws : List D.Fn) : Bool :=
  ws.all fun w =>
    decide ((ws.filter (fun v => decide (v = w))).length ≤ 1) ||
      poolSicherWB P fs cs w

theorem einzelnPoolB_iff {P : Programm D} {fs : List D.Fn}
    {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) :
    einzelnPoolB P fs cs ws = true ↔ EinzelnPool P fs ws := by
  unfold einzelnPoolB EinzelnPool
  rw [List.all_eq_true]
  constructor
  · intro h w hw hlt
    have h1 := h w hw
    rw [Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · have hle := of_decide_eq_true h1
      omega
    · exact (poolSicherWB_iff hvoll hcs).mp h1
  · intro h w hw
    rw [Bool.or_eq_true]
    by_cases hc : (ws.filter (fun v => decide (v = w))).length ≤ 1
    · exact Or.inl (decide_eq_true hc)
    · exact Or.inr ((poolSicherWB_iff hvoll hcs).mpr (h w hw (by omega)))

/-- **Never weakened**: pairwise distinct starts satisfy the new check --
    the old `einzelnB` verdicts all stay acceptances. -/
theorem einzelnPoolB_of_einzelnB {P : Programm D} {fs : List D.Fn}
    {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn}
    (h : einzelnB ws = true) : einzelnPoolB P fs cs ws = true := by
  have hnd : ws.Nodup := of_decide_eq_true h
  refine List.all_eq_true.mpr fun w _ => ?_
  rw [Bool.or_eq_true]
  exact Or.inl (decide_eq_true (nodup_filter_length_le_one hnd w))

/-- **The symmetric pair is admitted exactly when pool-safe**: the
    extension direction the old `einzeln` refused. -/
theorem einzelnPool_paar {P : Programm D} {fs : List D.Fn} {w : D.Fn} :
    EinzelnPool P fs [w, w] ↔ PoolSicherW P fs w := by
  constructor
  · intro h
    have hff : ([w, w].filter (fun v => decide (v = w))) = [w, w] := by
      simp
    have hlt : 1 < ([w, w].filter (fun v => decide (v = w))).length := by
      rw [hff]
      show 1 < 2
      decide
    exact h w List.mem_cons_self hlt
  · intro hpool w' hw' hlt
    have heq : w' = w := by simpa using hw'
    subst heq
    exact hpool

/-- Every program the old checker accepted satisfies the pool condition:
    the Prop-level "never weakened" direction. -/
theorem akzeptiertSpec_pool {P : Programm D} {S : SperrInv D} {fs : List D.Fn}
    {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    (hA : AkzeptiertSpec P S fs ws) : EinzelnPool P fs ws :=
  (einzelnPoolB_iff hvoll hcs).mp
    (einzelnPoolB_of_einzelnB (decide_eq_true hA.einzeln))

end PoolBool

/-- `einzahlen` writes `konto`: the fixture is non-degenerate (some
    function writes a table). -/
theorem pool_schreibt_zeigt :
    TraegerSchreibt (D := poolD) true (.inl ()) = true := rfl

/-- Decidable equality on the variant's functions: `Bool` underneath, as
    a named instance so kernel evaluation (`decide` over computed graphs)
    unfolds it. A `haveI` hypothesis would stay opaque and block `decide`. -/
instance poolDecEq : DecidableEq poolD.Fn := inferInstanceAs (DecidableEq Bool)

/-- **The joint witness for `pool_schreibt_nicht`**: every premise
    instantiated jointly on the lock-free fixture -- the empty member list
    (the graph is then definitionally `{einzahlen}`, so no body is ever
    unfolded), the unguarded, non-atomic, never-written global `frei` as
    the carrier, thread 0 running `einzahlen` with argument 7. -/
theorem pool_schreibt_nicht_zeuge :
    ∃ (D : Deklaration) (_ : DecidableEq D.Fn) (P : Programm D) (fs : List D.Fn)
      (w : D.Fn)
      (init : Faden → Σ f : D.Fn, Env D (D.params f)) (t : Faden)
      (c : D.Tab ⊕ D.Glob) (g : D.Fn),
      (init t).1 = w ∧ PoolSicher D (reachB P fs w) w ∧
      (∀ L, ¬ Bewacht c L) ∧ ¬ AtomarAusgenommen c ∧
      kVon P fs init t g = true := by
  refine ⟨poolD, inferInstance, poolP, [], true, fun _ => ⟨true, poolRho⟩, 0,
    .inr (), true, rfl, ?_, ?_, ?_, ?_⟩
  · refine ⟨rfl, rfl, fun f hf c hc => ?_⟩
    cases f with
    | false => exact absurd hf (by decide)
    | true =>
        cases c with
        | inl _ => exact Or.inl ⟨(), List.mem_cons_self⟩
        | inr x => cases x; exact absurd hc (by decide)
  · intro L h
    cases h
  · intro hA
    obtain ⟨g, _, hg2⟩ := hA
    cases g
    exact absurd hg2 (by decide)
  · unfold kVon
    exact reachB_wurzel _ _ _

/-- **The refusal witness**: on the reference fixture itself, `PoolSicher`
    is uninhabited -- both functions hold the lock by signature. This is
    why the joint witness lives on the lock-free variant, and why the
    checker refuses the fixture's writer on two threads (`N304`). -/
theorem poolSicher_refD_unmoeglich (K : refD.Fn → Bool) (w : refD.Fn) :
    ¬ PoolSicher refD K w := by
  intro h
  cases w with
  | true => exact absurd h.1 (by decide)
  | false => exact absurd h.1 (by decide)

/-! CUTS: what is not proved.
  * The run-level race-freedom leg (`RennfreiBis` over a multiset start)
    is not proved here: it needs `Laufzeit.einmal` lifted (F4, specified
    in MUSE-REPORT-245.md). Proved instead: the separation premise both
    threads of a symmetric pair satisfy (`pool_schreibt_nicht`), jointly
    witnessed above, with the refusal direction on `refD`.
  * Per-core writes are not covered model-side: the surface exempts
    `accumulates … per cpu`, the model has no notion for it.
  * No joint `_zeuge` shape beyond the one above: `poolP`'s bodies are
    trivial by design (the witness graph never unfolds them). -/

#print axioms Gabbro.Grammatik.pool_schreibt_nicht
#print axioms Gabbro.Grammatik.pool_schreibt_nicht_zeuge
#print axioms Gabbro.Grammatik.pool_schreibt_zeigt
#print axioms Gabbro.Grammatik.poolSicher_refD_unmoeglich
