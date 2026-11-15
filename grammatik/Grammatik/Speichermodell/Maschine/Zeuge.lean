/- The accepted pool witness and per-core writer checks. -/
module
public import Lean
public import Grammatik.Speichermodell.Maschine.WeakWitness
public import Grammatik.Zielsatz.Faeden.PoolZeuge
public import Grammatik.Zielsatz.Eigenschaften.Schwach
import all Init.Data.Repr
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
@[expose] public section


namespace Gabbro.Grammatik
open Speichermodell
namespace SchwachZeuge
open NIZeuge

/-! ## 2. The goal over the weak machine on an accepted pool -/

open Zielsatz

local instance : DecidableEq zD.Ax := inferInstanceAs (DecidableEq Empty)
local instance : DecidableEq nD.Ax := inferInstanceAs (DecidableEq Empty)

/-- **The pool witness over W.** On the runtime's start of the pool unit `zPool` (accepted by
    the concrete checker), machine W runs thread 0, thread 1, thread 0 (both instances unfold,
    thread 0 takes the lock); at the reached machine thread 0 holds the lock, its G-part is
    reached by G, and every leg of `Ziel` holds there -- by `gabbro_ziel_schwach`. -/
theorem schwach_pool_zeuge [RootNativeFloat.Hardware] (ord : zD.mitRuhe.Glob → Ordnung) :
    ∃ W1 W2 W3 : RufMaschineW zD.mitRuhe,
      RufSchrittW zPB.mitRuhe zO.mitRuhe 0 ord (RufStartW zPoolM0) 0 W1 ∧
      RufSchrittW zPB.mitRuhe zO.mitRuhe 0 ord W1 1 W2 ∧
      RufSchrittW zPB.mitRuhe zO.mitRuhe 0 ord W2 0 W3 ∧
      (() : zD.mitRuhe.Lock) ∈ offen (W3.g.faeden 0).spur ∧
      RufErreichbarG zPool.P.mitRuhe zO.mitRuhe 0 zPoolM0 W3.g ∧
      Ziel zPool.P.mitRuhe zPool.S.mitRuhe zO.mitRuhe 0 zPoolM0 W3.g := by
  obtain ⟨M1, M2, M3, hL, _, _, s1, s2, s3, hlock, _⟩ := pool_ziel_zeuge
  obtain ⟨W1, t1, g1, F1⟩ := schrittW_aus_gW (ord := ord) (scForm_start zPoolM0) s1
  obtain ⟨W2, t2, g2, F2⟩ := schrittW_aus_gW (ord := ord) F1 (by rw [g1]; exact s2)
  obtain ⟨W3, t3, g3, F3⟩ := schrittW_aus_gW (ord := ord) F2 (by rw [g2]; exact s3)
  have hW3 : RufErreichbarW zPool.P.mitRuhe zO.mitRuhe 0 ord (RufStartW zPoolM0) W3 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start t1) t2) t3
  have hZ := gabbro_ziel_schwach akzeptiert_pruefer zD zPool ⟨zFs, zFs_voll⟩ ⟨[()], zLs_voll⟩
    ⟨[.inl ()], zCs_voll⟩
    (by rw [akzeptiert_pruefer_eq]
        exact zPool_akzeptiert)
    zPool_nutzerPflicht zO ⟨zO_gut, zO_lokal, axVertragO_wahr zO, inferInstance⟩ 0 _ _ hL ord W3 hW3
  exact ⟨W1, W2, W3, t1, t2, t3, by rw [g3]; exact hlock, hZ.1, hZ.2⟩

/-! ## 3. Per-core cells (OFFEN O17): the pool rules agree, writes are covered, reads are not -/

/-- **The Rust pool rule with its per-core disjunct** (`fusswache2.rs`, `N304`: every written
    carrier guarded, atomic, OR per-core). `kern` marks the per-core accumulators. -/
def PoolSicherRust (D : Deklaration) (K : D.Fn → Bool) (w : D.Fn) (kern : D.Glob → Bool) : Prop :=
  D.haelt w = [] ∧ D.gruende w = 0 ∧
    ∀ f, K f = true → ∀ c, TraegerSchreibt f c = true →
      (∃ L, Bewacht c L) ∨ AtomarAusgenommen c ∨ ∃ g, c = .inr g ∧ kern g = true

/-- **The two pool rules agree once a per-core accumulator is an `atomic`.** The emitter lowers
    `accumulates X per cpu N` to `_Atomic T X_zellen[N]` with relaxed loads and stores
    (`emit.rs`), so in the model the accumulator is an atomic global, relaxed; with that
    reading (`hk`) the Rust disjunct "per-core" is the Lean disjunct "atomic", and `N304`
    decides `PoolSicher` (lane 245, fix lane F10). -/
theorem poolSicherRust_iff {D : Deklaration} (K : D.Fn → Bool) (w : D.Fn) (kern : D.Glob → Bool)
    (hk : ∀ g, kern g = true → D.atomar g = true) :
    PoolSicherRust D K w kern ↔ PoolSicher D K w := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun f hf c hc => ?_⟩
    rcases h3 f hf c hc with h | h | ⟨g, rfl, hg⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr ⟨g, rfl, hk g hg⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun f hf c hc => (h3 f hf c hc).elim Or.inl (fun h => Or.inr (Or.inl h))⟩

/-- **A pool that WRITES a relaxed atomic from every instance is accepted** -- the write half
    of a per-core accumulator: `kern` (writes the atomic `konfig`, reads nothing) declared
    twice. Pool-safe (the write is atomic), the footprint component has nothing to bound, and
    the multi-writer atomic is covered by the leg `schwach` like every other carrier. -/
theorem proKern_schreiben_akzeptiert :
    Akzeptiert nP nS nFs [] nCs [NFn.kern, NFn.kern] = true := by
  decide

/-- Non-degenerate: both instances really write the atomic. -/
theorem proKern_schreiben_echt :
    TraegerSchreibt (D := nD) NFn.kern (.inr NGlob.konfig) = true ∧ nD.atomar NGlob.konfig = true :=
  ⟨rfl, rfl⟩

/-- **The READ half is refused**: a start that reads an atomic another start writes (the fold
    of an accumulator, or its own update, which loads the cell before it stores) -- `zaehlA`
    writes `zaehler`, `zaehlB` reads it, no lock. The footprint component refuses; the Rust
    checker exempts per-core cells here (`N300`/`N301`/`N304`: "one cell per core -- nothing
    shared"), so this is where O17 stays open, together with O25. -/
theorem proKern_lesen_abgelehnt :
    fussWB nP nS nFs [NFn.zaehlA, NFn.zaehlB] = false := by
  decide

end SchwachZeuge

#print axioms Gabbro.Grammatik.SchwachZeuge.poolSicherRust_iff
#print axioms Gabbro.Grammatik.SchwachZeuge.proKern_schreiben_akzeptiert
#print axioms Gabbro.Grammatik.SchwachZeuge.proKern_lesen_abgelehnt
#print axioms Gabbro.Grammatik.SchwachZeuge.akzeptiert_n1_abgelehnt
#print axioms Gabbro.Grammatik.SchwachZeuge.w_nicht_sc
#print axioms Gabbro.Grammatik.SchwachZeuge.g_schritt_0
#print axioms Gabbro.Grammatik.SchwachZeuge.schwach_nicht_trivial
#print axioms Gabbro.Grammatik.SchwachZeuge.schwach_pool_zeuge

end Gabbro.Grammatik
