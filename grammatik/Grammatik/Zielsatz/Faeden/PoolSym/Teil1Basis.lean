module

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
    (Empty.elim i : List (Unit ⊕ Unit)).any
        (Sum.elim (poolSigNr n).schreibt (poolSigNr n).gschreibt) = true →
      ∀ (c : Unit ⊕ Unit), c ∈ (Empty.elim i : List (Unit ⊕ Unit)) → ∀ (L : Unit),
        Sum.inl L ∈ (Sum.elim (fun _ : Unit => ([Sum.inl ()] : List (Unit ⊕ (Empty × Nat))))
            (fun _ : Unit => ([] : List (Unit ⊕ (Empty × Nat)))) c) →
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
theorem poolEin_params : poolD.params true = [.int 0 10] := by rfl

/-- The witness argument: 7 in `.int 0 10` (same shape as `refRho7`). -/
def poolRho : Env poolD (poolD.params true) :=
  poolEin_params.symm ▸ (.cons ⟨7, by decide, by decide⟩ .nil :
    Env poolD [.int 0 10])

/-- The trivial program over the variant: `wahr` contracts and `ret`
    bodies. The witness graph (`fs = []`) never unfolds a body, so no
    body needs to mean anything; they only need to typecheck. -/
def poolP : Programm poolD where
  invariante := fun i => Empty.elim i
  requires := fun | true => Expr.tru | false => Expr.tru
  ensures := fun | true => Expr.tru | false => Expr.tru
  rumpf := fun
    | true => Endblock.ret ErgExpr.empty (List.Perm.refl _)
    | false =>
        Endblock.ret
          (ErgExpr.val (Expr.widen (by decide) (by decide) (Expr.lit 7)))
          (List.Perm.refl _)


end Gabbro.Grammatik
