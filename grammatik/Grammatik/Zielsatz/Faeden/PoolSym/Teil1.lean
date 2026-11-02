module
public import Grammatik.Zielsatz.Faeden.PoolSym.Teil1Basis
import all Grammatik.Zielsatz.Faeden.PoolSym.Teil1Basis

import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

public import Grammatik.Zielsatz.Kern.Akzeptiert
public import Grammatik.Bausteine.Kernzelle.Zulassung
public import Grammatik.Korpus.Referenz.ReferenzB

@[expose] public section



namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}
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
  | nil => simp only [List.filter_nil, List.length_nil, Nat.zero_le]
  | cons a l ih =>
      obtain ⟨hna, hndl⟩ := List.nodup_cons.mp hnd
      by_cases he : decide (a = w) = true
      · have haw : a = w := of_decide_eq_true he
        subst w
        have hempty : l.filter (fun v => decide (v = a)) = [] :=
          pool_filter_nil hna
        simp only [decide_true, List.filter_cons_of_pos, hempty, List.length_cons, List.length_nil, Nat.zero_add,
  Std.le_refl]
      · simp only [he, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg]
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
    every unit refused before with distinct starts is refused now. Since Opus agent H
    (2026-09-26) the Bool has the handler component `maskenB` beside the old conjunction; it
    is `true` on every program with no handler (`maskenB_ohne`). Since C18 it also has the
    reset component `resetB`; it is `true` on every program with no zero-less array static. -/
theorem akzeptiert_nodup_gleich {P : Programm D} {S : SperrInv D} {fs : List D.Fn}
    {ls : List D.Lock} {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn} (hnd : ws.Nodup) :
    Akzeptiert P S fs ls cs ws = (AkzeptiertVor P S fs ls cs ws && maskenB P fs && resetB cs && libraryB P fs) := by
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

/-- **Every old acceptance stays an acceptance** -- of a program that meets the handler
    discipline, in particular of every program with no handler (`maskenB_ohne`), and whose
    static arrays admit zero (`resetB`). -/
    discipline, in particular of every program with no handler (`maskenB_ohne`). The library
    component holds on every program (`libraryB_immer`). -/
theorem akzeptiert_vor_neu {P : Programm D} {S : SperrInv D} {fs : List D.Fn}
    {ls : List D.Lock} {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn}
    (h : AkzeptiertVor P S fs ls cs ws = true) (hM : maskenB P fs = true)
    (hR : resetB cs = true) :
    Akzeptiert P S fs ls cs ws = true := by
  rw [akzeptiert_nodup_gleich (akzeptiertVor_nodup h), h, hM, hR, libraryB_immer _ _]
  rfl

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
    starts the occurrence form of `Getrennt` is the routine form. Since Opus agent H
    (2026-09-26) the handler discipline is an extra premise (it holds on every program with
    no handler, `maskenB_ohne`). Since C18 the static-array reset admission is an extra
    premise (it holds on every program with no zero-less array static). -/
theorem akzeptiertSpecVor_neu {P : Programm D} {S : SperrInv D} {fs ws : List D.Fn}
    (h : AkzeptiertSpecVor P S fs ws) (hM : MaskenDisziplin P fs)
    (hR : ∀ (g : D.Glob) (elem : Ty) (len : Nat),
      D.gtyp g = .arr elem len → ZeroAdmitting elem) :
    AkzeptiertSpec P S fs ws [] := by
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
    einzelnPool_of_nodup h.einzeln, h.renn, h.antworten, hM, hR, Kernzelle.accumulatorAdmission_leer _ _, [], CheckAdmission.nil _ _⟩

end PoolBool

/-- **(a) OF THE REVIEWED DIFF, for the checker interface: every old checker is a
    `Pruefer`.** A Bool sound against the old specification is sound against the new one,
    so `GabbroZiel`'s `∀ C : Pruefer` ranges over at least every checker it ranged over
    before. Since Opus agent H (2026-09-26) an old checker is conjoined with the handler
    component `maskenB` it never judged (an old program declares no handler, where the
    conjunct is `true`: `maskenB_ohne`); since C15 with the accumulator admission it never
    judged (an old program declares no accumulator, where it holds vacuously). -/
def pruefer_vor_neu
    (akz : ∀ {D : Deklaration} [DecidableEq D.Fn],
      Einheit D → List D.Fn → List D.Lock → List (D.Tab ⊕ D.Glob) → Bool)
    (korr : ∀ {D : Deklaration} [DecidableEq D.Fn] (E : Einheit D)
      (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
      akz E fs.1 ls.1 cs.1 = true → AkzeptiertSpecVor E.P E.S fs.1 E.ws) : Pruefer where
  akzeptiert := fun E fs ls cs => akz E fs ls cs && maskenB E.P fs && resetB cs && Kernzelle.accumulatorB E.P fs cs E.akku
  korrekt := fun E fs ls cs h => by
    simp only [Bool.and_eq_true] at h
    exact (akzeptiertSpecVor_neu (korr E fs ls cs h.1.1.1) ((maskenB_iff fs.2).mp h.1.1.2)
      ((resetB_iff cs.2).mp h.1.2)).mitAkku ((Kernzelle.accumulatorB_iff fs.2 cs.2).mp h.2)

/-- **(d) OF THE REVIEWED DIFF: every run admitted before is admitted now.** The old
    `Laufzeit.einmal` (no declared start on two threads) implies the new one. -/
theorem laufzeit_vor_neu {E : Einheit D} {sp : Speicher D.mitRuhe}
    {init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)}
    (hl : sp = speicherR E.sp0)
    (hs : ∀ t, init t = ⟨none, .nil⟩ ∨ ∃ a ∈ E.starts, init t = ⟨some a.1, envR a.2⟩)
    (he : ∀ t u, t ≠ u → (init t).1 = (init u).1 → (init t).1 = none) :
    Laufzeit E sp init :=
  ⟨hl, fun t => (hs t).imp id fun ⟨a, ha, h⟩ => ⟨a, List.mem_append_left _ ha, h⟩,
    fun t u htu h => Or.inl (he t u htu h)⟩

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
    TraegerSchreibt (D := poolD) true (.inl ()) = true := by rfl

/-- Decidable equality on the variant's functions: `Bool` underneath, as
    a named instance so kernel evaluation (`decide` over computed graphs)
    unfolds it. A `haveI` hypothesis would stay opaque and block `decide`. -/
instance poolDecEq : DecidableEq poolD.Fn := inferInstanceAs (DecidableEq Bool)

end Gabbro.Grammatik
