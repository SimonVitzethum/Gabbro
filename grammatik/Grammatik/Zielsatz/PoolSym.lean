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
  multiset starts. Since fix lane F10 (2026-09-22) `Spec.lean`'s
  `AkzeptiertSpec.einzeln` IS `EinzelnPool` and `Laufzeit.einmal` admits a
  routine declared twice on several threads; the goal theorem covers pools
  (`gabbro_ziel`, witnessed in PoolZeuge.lean). This file keeps the
  separation lemmas and the "never weakened" statements of that diff
  (`akzeptiert_nodup_gleich`, `akzeptiertSpecVor_neu`, `pruefer_vor_neu`,
  `laufzeit_vor_neu`).
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

/-! ## The decidable pool checks, and "never weakened" (fix lane F10)

The Bools `poolSicherWB`/`einzelnPoolB` and their iff lemmas live in
`Zielsatz/Akzeptiert.lean` since fix lane F10 (they are a component of
`Akzeptiert` now). What stays here: the vacuity of the pool condition on
repetition-free starts, the symmetric pair, and the statements that the
swap `einzeln : ws.Nodup` -> `EinzelnPool` changes no old verdict. -/

section PoolBool

variable [DecidableEq D.Fn]

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

/-- A routine occurring in a repetition-free list occurs at most once. -/
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

/-- **The pool condition is vacuous on distinct starts** -- the old
    `einzeln` implies the new one. -/
theorem einzelnPool_of_nodup {P : Programm D} {fs ws : List D.Fn} (hnd : ws.Nodup) :
    EinzelnPool P fs ws :=
  fun w hm => absurd hm (nicht_mehrfach_of_nodup hnd w)

/-- **Never weakened, Bool side**: pairwise distinct starts satisfy the new
    component -- every old `einzelnB` verdict stays an acceptance. -/
theorem einzelnPoolB_of_einzelnB {P : Programm D} {fs : List D.Fn}
    {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn}
    (h : einzelnB ws = true) : einzelnPoolB P fs cs ws = true := by
  have hnd : ws.Nodup := of_decide_eq_true h
  refine List.all_eq_true.mpr fun w _ => ?_
  have hm : mehrfachB ws w = false := by
    cases e : mehrfachB ws w
    · rfl
    · exact absurd (mehrfachB_iff.mp e) (nicht_mehrfach_of_nodup hnd w)
  rw [hm]
  rfl

/-- **The symmetric pair is admitted exactly when pool-safe**: the
    extension direction the old `einzeln` refused. -/
theorem einzelnPool_paar {P : Programm D} {fs : List D.Fn} {w : D.Fn} :
    EinzelnPool P fs [w, w] ↔ PoolSicherW P fs w := by
  constructor
  · intro h
    exact h w (List.Sublist.refl _)
  · intro hpool w' hm
    have hw' : w' ∈ [w, w] := hm.subset List.mem_cons_self
    have heq : w' = w := by simpa using hw'
    subst heq
    exact hpool

/-- The thread-locality test BEFORE fix lane F10: DIFFERENT routines only. -/
def getrenntWVor (P : Programm D) (fs ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Bool :=
  ws.all fun w1 => ws.all fun w2 => decide (w1 = w2) ||
    (fs.all fun f => !(reachB P fs w1 f) || !(istIn (fussOrteG P f) c)) ||
    (fs.all fun g => !(reachB P fs w2 g) || !(TraegerSchreibt g c))

/-- The footprint component BEFORE fix lane F10. -/
def fussWBVor (P : Programm D) (S : SperrInv D) (fs ws : List D.Fn) : Bool :=
  fs.all fun f =>
    (fussOrte P f).all (fun c =>
      sigB f c || getrenntWVor P fs ws c || (waechterVon c).any fun L => istIn (S.orte L) c) &&
    ((P.rumpf f).regs.flatMap D.rtraeger).all (fun c => sigB f c || getrenntWVor P fs ws c)

/-- **The checker Bool BEFORE fix lane F10** (`einzelnB`, the old `getrenntW`). -/
def AkzeptiertVor (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) : Bool :=
  programmImFragmentG P fs && abgAlleB P fs && fussWBVor P S fs ws && stufenB P fs &&
    sperrOrteB S ls && wurzelnB ws && einzelnB ws && rennB P fs cs ws && antwortenB P fs

/-- On distinct starts the two thread-locality tests agree. -/
theorem getrenntW_nodup {P : Programm D} {fs ws : List D.Fn} (hnd : ws.Nodup) :
    getrenntW P fs ws = getrenntWVor P fs ws := by
  funext c
  have hm : ∀ w, mehrfachB ws w = false := fun w => by
    cases e : mehrfachB ws w
    · rfl
    · exact absurd (mehrfachB_iff.mp e) (nicht_mehrfach_of_nodup hnd w)
  unfold getrenntW getrenntWVor
  simp only [hm, Bool.not_false, Bool.and_true]

/-- **(a) OF THE REVIEWED DIFF: no old verdict moves.** On every start list the old
    checker accepted (it demanded `ws.Nodup`) the new Bool IS the old Bool; and the old
    Bool accepts only distinct starts. So every unit accepted before is accepted now, and
    every unit refused before with distinct starts is refused now. -/
theorem akzeptiert_nodup_gleich {P : Programm D} {S : SperrInv D} {fs : List D.Fn}
    {ls : List D.Lock} {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn} (hnd : ws.Nodup) :
    Akzeptiert P S fs ls cs ws = AkzeptiertVor P S fs ls cs ws := by
  unfold Akzeptiert AkzeptiertVor fussWB fussWBVor
  rw [getrenntW_nodup hnd, einzelnPoolB_of_einzelnB (P := P) (fs := fs) (cs := cs)
    (decide_eq_true hnd), show einzelnB ws = true from decide_eq_true hnd]

/-- The old Bool accepts only distinct starts. -/
theorem akzeptiertVor_nodup {P : Programm D} {S : SperrInv D} {fs : List D.Fn}
    {ls : List D.Lock} {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn}
    (h : AkzeptiertVor P S fs ls cs ws = true) : ws.Nodup := by
  unfold AkzeptiertVor at h
  simp only [Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.1.2

/-- **Every old acceptance stays an acceptance.** -/
theorem akzeptiert_vor_neu {P : Programm D} {S : SperrInv D} {fs : List D.Fn}
    {ls : List D.Lock} {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn}
    (h : AkzeptiertVor P S fs ls cs ws = true) : Akzeptiert P S fs ls cs ws = true := by
  rw [akzeptiert_nodup_gleich (akzeptiertVor_nodup h)]
  exact h

/-- Spec's `Getrennt` BEFORE fix lane F10: different routines only. -/
def GetrenntVor (P : Programm D) (fs ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Prop :=
  ∀ w₁ ∈ ws, ∀ w₂ ∈ ws, w₁ ≠ w₂ → ∀ f g, reachB P fs w₁ f = true → c ∈ fussOrteG P f →
    reachB P fs w₂ g = true → TraegerSchreibt g c = false

noncomputable def lokWVor (P : Programm D) (fs ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Bool :=
  @decide (GetrenntVor P fs ws c) (Classical.propDecidable _)

/-- **`AkzeptiertSpec` BEFORE fix lane F10** -- the target of every `Pruefer.korrekt`
    until then (`einzeln : ws.Nodup`, the routine-level `Getrennt`). -/
structure AkzeptiertSpecVor (P : Programm D) (S : SperrInv D) (fs ws : List D.Fn) : Prop where
  frag : programmImFragmentG P fs = true
  abg : ∀ w, AbgK P fs (reachB P fs w)
  fuss : ∀ f, FussS P S (lokWVor P fs ws) f
  stufen : StufenM P
  sperrOrte : ∀ L c, c ∈ S.orte L → Bewacht c L
  wurzeln : ∀ w ∈ ws, D.haelt w = [] ∧ D.gruende w = 0
  einzeln : ws.Nodup
  renn : ∀ c, (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c → SchreibGetrennt P fs ws c
  antworten : ∀ f, ∀ x ∈ (P.rumpf f).ants, StelleOk D x

/-- **The old specification implies the new one** (Prop side of (a)): with distinct
    starts the occurrence form of `Getrennt` is the routine form. -/
theorem akzeptiertSpecVor_neu {P : Programm D} {S : SperrInv D} {fs ws : List D.Fn}
    (h : AkzeptiertSpecVor P S fs ws) : AkzeptiertSpec P S fs ws := by
  have hlok : lokWVor P fs ws = lokW P fs ws := by
    funext c
    have e : GetrenntVor P fs ws c ↔ Getrennt P fs ws c := by
      constructor
      · intro hg w₁ h₁ w₂ h₂ hne
        exact hg w₁ h₁ w₂ h₂ (hne.resolve_right (nicht_mehrfach_of_nodup h.einzeln w₁))
      · intro hg w₁ h₁ w₂ h₂ hne
        exact hg w₁ h₁ w₂ h₂ (Or.inl hne)
    unfold lokWVor lokW
    exact @decide_eq_decide _ _ (Classical.propDecidable _) (Classical.propDecidable _) |>.mpr e
  exact ⟨h.frag, h.abg, hlok ▸ h.fuss, h.stufen, h.sperrOrte, h.wurzeln,
    einzelnPool_of_nodup h.einzeln, h.renn, h.antworten⟩

end PoolBool

/-- **(a) OF THE REVIEWED DIFF, for the checker interface: every old checker is a
    `Pruefer`.** A Bool sound against the old specification is sound against the new one,
    so `GabbroZiel`'s `∀ C : Pruefer` ranges over at least every checker it ranged over
    before. -/
def pruefer_vor_neu
    (akz : ∀ {D : Deklaration} [DecidableEq D.Fn],
      Einheit D → List D.Fn → List D.Lock → List (D.Tab ⊕ D.Glob) → Bool)
    (korr : ∀ {D : Deklaration} [DecidableEq D.Fn] (E : Einheit D)
      (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
      akz E fs.1 ls.1 cs.1 = true → AkzeptiertSpecVor E.P E.S fs.1 E.ws) : Pruefer where
  akzeptiert := akz
  korrekt := fun E fs ls cs h => akzeptiertSpecVor_neu (korr E fs ls cs h)

/-- **(d) OF THE REVIEWED DIFF: every run admitted before is admitted now.** The old
    `Laufzeit.einmal` (no declared start on two threads) implies the new one. -/
theorem laufzeit_vor_neu {E : Einheit D} {sp : Speicher D.mitRuhe}
    {init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)}
    (hl : sp = speicherR E.sp0)
    (hs : ∀ t, init t = ⟨none, .nil⟩ ∨ ∃ a ∈ E.starts, init t = ⟨some a.1, envR a.2⟩)
    (he : ∀ t u, t ≠ u → (init t).1 = (init u).1 → (init t).1 = none) :
    Laufzeit E sp init :=
  ⟨hl, hs, fun t u htu h => Or.inl (he t u htu h)⟩

/-! ## The legs over multiset starts -/

section PoolLegs

variable [DecidableEq D.Fn]

/-- **No unguarded write on a run**: if thread `ts k` of a run starts the
    pool-safe routine `w`, its `k`-th step writes no unguarded, non-atomic
    carrier. The run-level lifting of `pool_schreibt_nicht` -- applied to
    both threads of a symmetric pair, no write-write and no write-read
    race on unguarded carriers exists. The footprint half of
    `SchreibGetrenntK` is not needed and not claimed: with no unguarded
    writer, the write side of every race pair is already empty. Guarded
    carriers keep their leg unchanged (`rennfrei_g_voll`, via
    `pool_startExklusiv` below). -/
theorem pool_schreibt_nicht_lauf {P : Programm D} {O : Orakel D} {passes : Nat}
    {fs : List D.Fn} {w : D.Fn}
    (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hAbg : ∀ t, AbgK P fs (kVon P fs init t))
    (hWurzel : ∀ t, kVon P fs init t (init t).1 = true)
    (ms : Nat → RufMaschineG D) (ts : Nat → Faden) (n : Nat)
    (hl : LaufG P O passes (RufStartG P sp init) ms ts n)
    (k : Nat) (hk : k < n)
    (ht : (init (ts k)).1 = w) (hpoolW : PoolSicher D (reachB P fs w) w)
    (c : D.Tab ⊕ D.Glob) (hB : ∀ L, ¬ Bewacht c L) (hAt : ¬ AtomarAusgenommen c)
    (hw : SchreibG (ms k) (ms (k + 1)) (ts k) c) : False := by
  obtain ⟨g, hg, hgw⟩ := (zugriff_im_graph hO hvoll sp init (kVon P fs init) hAbg
    hWurzel (laufG_erreichbar hl k (by omega)) (hl.2 k (by omega)) c).2 hw
  have hnw : TraegerSchreibt g c = false :=
    pool_schreibt_nicht ht hpoolW hB hAt hg
  rw [hnw] at hgw
  cases hgw

end PoolLegs

/-- **Pool starts keep lock exclusivity**: per-thread start hygiene (no
    signature lock, no reasons) over a multiset start assignment gives
    `StartExklusiv` -- the premise the guarded race leg (`rennfrei_g_voll`)
    takes. No distinctness is used anywhere: `wurzeln` is
    membership-based, so the lock legs transfer to duplicates unchanged. -/
theorem pool_startExklusiv {ws : List D.Fn}
    {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    (hws : ∀ w ∈ ws, D.haelt w = [] ∧ D.gruende w = 0)
    (hinit : ∀ t, (init t).1 ∈ ws) : StartExklusiv init :=
  startExklusiv_ohne_haelt init (fun t => (hws _ (hinit t)).1)

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
  * Per-core writes are not covered model-side: the surface exempts
    `accumulates … per cpu`, the model has no notion for it (OFFEN O17); the
    exporter refuses such units.
  * The goal legs over pool starts are NOT in this file any more: since fix
    lane F10 they are `gabbro_ziel` itself (the only proof changes are
    `getrenntK_of`/`schreibGetrenntK_of`, Zielsatz/Akzeptiert.lean), witnessed
    on a two-worker pool in Zielsatz/PoolZeuge.lean. `pool_schreibt_nicht_lauf`
    stays as the run-level form of the write leg. -/

#print axioms Gabbro.Grammatik.pool_schreibt_nicht
#print axioms Gabbro.Grammatik.pool_schreibt_nicht_zeuge
#print axioms Gabbro.Grammatik.pool_schreibt_zeigt
#print axioms Gabbro.Grammatik.poolSicher_refD_unmoeglich
#print axioms Gabbro.Grammatik.poolSicherWB_iff
#print axioms Gabbro.Grammatik.einzelnPoolB_iff
#print axioms Gabbro.Grammatik.einzelnPoolB_of_einzelnB
#print axioms Gabbro.Grammatik.einzelnPool_paar
#print axioms Gabbro.Grammatik.einzelnPool_of_nodup
#print axioms Gabbro.Grammatik.getrenntW_nodup
#print axioms Gabbro.Grammatik.akzeptiert_nodup_gleich
#print axioms Gabbro.Grammatik.akzeptiertVor_nodup
#print axioms Gabbro.Grammatik.akzeptiert_vor_neu
#print axioms Gabbro.Grammatik.akzeptiertSpecVor_neu
#print axioms Gabbro.Grammatik.pruefer_vor_neu
#print axioms Gabbro.Grammatik.laufzeit_vor_neu
#print axioms Gabbro.Grammatik.pool_schreibt_nicht_lauf
#print axioms Gabbro.Grammatik.pool_startExklusiv
#print axioms Gabbro.Grammatik.Zielsatz.PoolSicher
#print axioms Gabbro.Grammatik.Zielsatz.EinzelnPool
