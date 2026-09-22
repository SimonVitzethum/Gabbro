/-
  File:      Grammatik/Zielsatz/PoolZeuge.lean
  Subject:   The witnesses of fix lane F10 (2026-09-22, OFFEN O18): the goal theorem over a
             symmetric worker pool.

  Since fix lane F10 `AkzeptiertSpec.einzeln` is `EinzelnPool` (a routine declared twice is
  pool-safe) and `Laufzeit.einmal` lets such a routine run on several threads (Spec.lean,
  "WHAT CHANGED ON 2026-09-22"). This file shows the change is not vacuous in either
  direction:

  * `pool_ziel_zeuge` -- POSITIVE. The unit `zPool` is probe B's program (`zPB`,
    ZielOrtSperreZeuge.lean: `haupt() = locks { wrap() }`, `wrap` calls `lies` and `einzahlen`,
    which WRITES the table `konto` guarded by the lock `()`, lock invariant family `zS`) with
    `haupt` declared TWICE. The concrete checker `akzeptiert_pruefer` accepts it
    (`zPool_akzeptiert`) -- the checker before F10 refused it (`zPool_vor_abgelehnt`) -- the
    user obligation holds (`zPool_nutzerPflicht`), and on the runtime's own start, where
    threads 0 and 1 both run `haupt`, a run in which BOTH instances step (thread 0 unfolds its
    body, thread 1 unfolds its body, thread 0 takes the lock) reaches a machine at which
    `gabbro_ziel` gives every leg of `Ziel`, with the lock held by thread 0.
  * `pool_abgelehnt` -- REFUSAL. `hauptB` of the two-thread fixture `mP` writes its private
    table `privB` UNGUARDED. Declared once beside `hauptA` it is accepted
    (`mP_akzeptiert`); declared TWICE it is refused, and exactly by the pool component: every
    other component of `Akzeptiert` accepts, `einzelnPoolB` refuses, `hauptB` is not
    pool-safe. That is the write-write race of two `hauptB` instances on `privB`, which the
    race component cannot see (it pairs DIFFERENT routines).
  * `pool_schreibt_nicht_voll` -- the separation lemma of lane 245 on a COMPLETE member
    list with a carrier some function of the program really writes (review G06 F4: the
    lane-245 witness had `fs = []` and a carrier nobody writes).
  * `einzelnPoolB_iff_zeuge` -- the decision lemma instantiated on complete member lists in
    both directions.
  * `pool_fuss_paart_vorkommen` -- the footprint component pairs start OCCURRENCES: a
    routine that reads and writes one unguarded carrier, declared twice, is refused there
    (the routine-level test before F10 accepted it).
-/
import Grammatik.Zielsatz.Proben
import Grammatik.Zielsatz.PoolSym

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

/-! ## 1. The pool unit -/

/-- **Probe B's program with `haupt` declared twice**: `concurrent { haupt, haupt }`. -/
def zPool : Einheit zD := ⟨zPB, zS, axWahr zD, [⟨zHaupt, .nil⟩, ⟨zHaupt, .nil⟩], zSp⟩

/-- `haupt` is declared twice. -/
theorem zPool_mehrfach : Mehrfach zPool.ws zHaupt := List.Sublist.refl _

/-- `haupt` is pool-safe: no signature lock, no reasons, and its graph (`haupt`, `wrap`,
    `lies`, `einzahlen`) writes only `konto`, which the lock `()` guards. -/
theorem zPool_poolSicher : PoolSicherW zPB zFs zHaupt :=
  (poolSicherWB_iff zFs_voll zCs_voll).mp (by decide)

/-- Non-degenerate: the pool routine's graph really writes (`einzahlen` writes `konto`). -/
theorem zPool_schreibt : reachB zPB zFs zHaupt zEin = true ∧
    TraegerSchreibt zEin (.inl () : zD.Tab ⊕ zD.Glob) = true := by decide

/-- **The concrete checker accepts the pool.** -/
theorem zPool_akzeptiert : Akzeptiert zPB zS zFs [()] [.inl ()] [zHaupt, zHaupt] = true := by
  decide

/-- **The checker before fix lane F10 refused it** (`einzelnB`: the starts were not distinct). -/
theorem zPool_vor_abgelehnt :
    AkzeptiertVor zPB zS zFs [()] [.inl ()] [zHaupt, zHaupt] = false := by decide

/-- **The user's obligation**: probe B's bodies at every budget (unchanged), the start
    obligation for both occurrences (`requires true`, lock invariant `true`). -/
theorem zPool_nutzerPflicht : NutzerPflicht zPool :=
  ⟨⟨fun passes f => ⟨koerperGutS_alle zFs_voll (by decide) zPB_koerper passes f, zInvGutS f,
      zInvGutGrund f⟩, zS_lokal, axEnsLokal_wahr⟩,
    ⟨fun _ => rfl, fun a ha => by
      simp only [zPool, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> rfl⟩⟩

/-! ## 2. The run: both instances step -/

/-- The runtime's start of the pool. -/
abbrev zPoolM0 : RufMaschineG zD.mitRuhe :=
  RufStartG zPB.mitRuhe (speicherR zSp) (initRuhe zPool.starts)

/-- No thread of the start machine holds a lock (`haupt` holds none by signature, the root
    none). -/
theorem zPool_start_offen (g : Faden) : offen (zPoolM0.faeden g).spur = [] := by
  match g with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- The runtime runs `haupt` on threads 0 AND 1. -/
theorem zPool_zwei_haupt :
    (initRuhe zPool.starts 0).1 = some zHaupt ∧ (initRuhe zPool.starts 1).1 = some zHaupt :=
  ⟨rfl, rfl⟩

/-- `haupt`'s `locks` statement as G runs it (on `zPB.mitRuhe`). -/
abbrev zPoolLocks :=
  ruS (V := vertragVon zD zHaupt) (l := false)
    (Stmt.locks (V := vertragVon zD zHaupt) (l := false) () (fun _ h => absurd h List.not_mem_nil)
      zLocksBody)

/-- `haupt`'s `return` as G runs it. -/
abbrev zPoolRet :=
  ruEnd (V := vertragVon zD zHaupt) (l := false) (Γ := []) (Λ := [])
    (Endblock.ret .keine List.Perm.nil)

/-- **THE POOL WITNESS.** On the runtime's start of `zPool` (threads 0 and 1 both run
    `haupt`), thread 0 steps, thread 1 steps, thread 0 takes the lock; at the reached machine
    thread 0 holds the lock and `gabbro_ziel` -- applied with the concrete checker -- gives
    every leg of `Ziel`: race freedom over the two instances of one routine included. -/
theorem pool_ziel_zeuge : ∃ M1 M2 M3 : RufMaschineG zD.mitRuhe,
    Laufzeit zPool (speicherR zSp) (initRuhe zPool.starts) ∧
    (initRuhe zPool.starts 0).1 = some zHaupt ∧ (initRuhe zPool.starts 1).1 = some zHaupt ∧
    RufSchrittG zPB.mitRuhe zO.mitRuhe 0 zPoolM0 0 M1 ∧
    RufSchrittG zPB.mitRuhe zO.mitRuhe 0 M1 1 M2 ∧
    RufSchrittG zPB.mitRuhe zO.mitRuhe 0 M2 0 M3 ∧
    (() : zD.mitRuhe.Lock) ∈ offen (M3.faeden 0).spur ∧
    Ziel zPool.P.mitRuhe zPool.S.mitRuhe zO.mitRuhe 0 zPoolM0 M3 := by
  -- thread 0: unfold `locks { wrap() }; return`
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := zPB.mitRuhe) (O := zO.mitRuhe) (passes := 0)
    (M := zPoolM0) (f := 0) rfl zPoolLocks zPoolRet .nil rfl rfl
  -- thread 1: the same routine, the same step
  obtain ⟨M2, s2, hZ2⟩ := w_endeEntf (P := zPB.mitRuhe) (O := zO.mitRuhe) (passes := 0)
    (M := M1) (f := 1) (rufSchrittG_fremd s1 1 (by decide)) zPoolLocks zPoolRet .nil rfl rfl
  -- thread 0: take the lock
  have hfrei : RufFreiG M2 0 () := by
    intro g hg
    by_cases h1 : g = 1
    · subst h1
      rw [hZ2.1]
      show () ∉ offen (M1.faeden 1).spur
      rw [rufSchrittG_fremd s1 1 (by decide), zPool_start_offen]
      exact List.not_mem_nil
    · rw [rufSchrittG_fremd s2 g h1, rufSchrittG_fremd s1 g hg, zPool_start_offen]
      exact List.not_mem_nil
  obtain ⟨M3, s3, hZ3⟩ := w_locks (P := zPB.mitRuhe) (O := zO.mitRuhe) (passes := 0)
    (M := M2) (f := 0) ((rufSchrittG_fremd s2 0 (by decide)).trans hZ1.1) ()
    (fun _ h => absurd h List.not_mem_nil) (ruB zLocksBody) .nil (.ende zPoolRet) .nil rfl
    (fun L => by
      show Res.held L ∈ ([] : List (Res zD.mitRuhe)) ↔ L ∈ offen (zPoolM0.faeden 0).spur
      rw [zPool_start_offen]
      simp) hfrei
  have hr : RufErreichbarG zPool.P.mitRuhe zO.mitRuhe 0 zPoolM0 M3 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3
  refine ⟨M1, M2, M3, laufzeit_initRuhe zPool, rfl, rfl, s1, s2, s3, ?_, ?_⟩
  · rw [hZ3.1]
    show () ∈ () :: offen (M2.weltVon 0).spur
    exact List.mem_cons_self
  · exact gabbro_ziel akzeptiert_pruefer zD zPool ⟨zFs, zFs_voll⟩ ⟨[()], zLs_voll⟩
      ⟨[.inl ()], zCs_voll⟩
      (by show Akzeptiert zPB zS zFs [()] [.inl ()] [zHaupt, zHaupt] = true
          exact zPool_akzeptiert)
      zPool_nutzerPflicht zO ⟨zO_gut, zO_lokal, axVertragO_wahr zO⟩ 0 _ _
      (laufzeit_initRuhe zPool) M3 hr

/-! ## 3. The refusal: an unguarded writer declared twice -/

/-- **A pool-UNSAFE duplicate is refused, by the pool component.** `hauptB` writes `privB`
    unguarded (no lock guards it, it is not atomic); nothing reads it, so the footprint
    component passes, and the race component pairs only DIFFERENT routines, so it passes too.
    `einzelnPoolB` refuses: two `hauptB` threads race on `privB`. -/
theorem pool_abgelehnt :
    Akzeptiert mP mSI mFs [()] mCs [mHauptB, mHauptB] = false ∧
    (programmImFragmentG mP mFs && abgAlleB mP mFs && fussWB mP mSI mFs [mHauptB, mHauptB] &&
      stufenB mP mFs && sperrOrteB mSI [()] && wurzelnB [mHauptB, mHauptB] &&
      rennB mP mFs mCs [mHauptB, mHauptB] && antwortenB mP mFs) = true ∧
    einzelnPoolB mP mFs mCs [mHauptB, mHauptB] = false ∧
    ¬ PoolSicherW mP mFs mHauptB := by
  refine ⟨by decide, by decide, by decide, fun h => ?_⟩
  have e := (poolSicherWB_iff mFs_voll mCs_voll).mpr h
  revert e
  decide

/-- The same routine declared ONCE beside another is accepted: the refusal is about the
    second instance, not about `hauptB`. -/
theorem pool_abgelehnt_einmal_ok : Akzeptiert mP mSI mFs [()] mCs [mHauptA, mHauptB] = true :=
  mP_akzeptiert

/-- The refusal at the specification: no `AkzeptiertSpec` for the doubled `hauptB`. -/
theorem pool_abgelehnt_spec : ¬ AkzeptiertSpec mP mSI mFs [mHauptB, mHauptB] := fun h =>
  absurd (h.einzeln mHauptB (List.Sublist.refl _)) pool_abgelehnt.2.2.2

/-- **The footprint component pairs OCCURRENCES** (fix lane F10, `Getrennt` with
    `Mehrfach`). `hauptA` reads `privA` in a footprint (the callee contract of `pruefeA`)
    and writes it. Declared twice, the second instance writes what the first reads, so
    `privA` is not thread-local: the new footprint component refuses, the routine-level
    test of before F10 did not see it. (The Rust footprint legs `N290`-`N293` always
    paired thread indices; `pool_fussabdruck_paart_vorkommen` in
    `crates/gabbro-check/tests/fusswache2.rs` is their surface probe.) -/
theorem pool_fuss_paart_vorkommen :
    fussWB mP mSI mFs [mHauptA, mHauptA] = false ∧
    fussWBVor mP mSI mFs [mHauptA, mHauptA] = true ∧
    fussWB mP mSI mFs [mHauptA, mHauptB] = true := by
  decide

/-! ## 4. The lane-245 lemmas on complete member lists (review G06 F4) -/

/-- **`pool_schreibt_nicht` on a complete member list with a written carrier.** On the
    two-thread fixture, `pruefeA` is pool-safe (it writes nothing), `privA` is unguarded and
    not atomic, and `hauptA` -- outside `pruefeA`'s graph -- writes it: the lemma's conclusion
    is not a property of the carrier (the program writes it) but of the graph. -/
theorem pool_schreibt_nicht_voll :
    PoolSicherW mP mFs mPruefeA ∧
    (∀ L, ¬ Bewacht (.inl MTab.privA : mD.Tab ⊕ mD.Glob) L) ∧
    ¬ AtomarAusgenommen (.inl MTab.privA : mD.Tab ⊕ mD.Glob) ∧
    TraegerSchreibt mHauptA (.inl MTab.privA : mD.Tab ⊕ mD.Glob) = true ∧
    ∀ g, reachB mP mFs mPruefeA g = true →
      TraegerSchreibt g (.inl MTab.privA : mD.Tab ⊕ mD.Glob) = false := by
  have hpool : PoolSicherW mP mFs mPruefeA := (poolSicherWB_iff mFs_voll mCs_voll).mp (by decide)
  have hB : ∀ L, ¬ Bewacht (.inl MTab.privA : mD.Tab ⊕ mD.Glob) L := fun L h => by
    have e := waechterVon_mem.mpr h
    have hw : waechterVon (D := mD) (.inl MTab.privA) = [] := rfl
    rw [hw] at e
    exact List.not_mem_nil e
  have hAt : ¬ AtomarAusgenommen (.inl MTab.privA : mD.Tab ⊕ mD.Glob) := fun ⟨g, _, _⟩ =>
    nomatch g
  refine ⟨hpool, hB, hAt, rfl, fun g hg => ?_⟩
  exact pool_schreibt_nicht (init := fun _ => ⟨mPruefeA, .nil⟩) (t := 0) rfl hpool hB hAt
    (by unfold kVon; exact hg)

/-- **`einzelnPoolB_iff` in both directions on complete member lists**: the pool is decided
    `true` and `EinzelnPool` holds; the doubled unguarded writer is decided `false` and
    `EinzelnPool` fails. -/
theorem einzelnPoolB_iff_zeuge :
    (einzelnPoolB zPB zFs [.inl ()] [zHaupt, zHaupt] = true ∧
      EinzelnPool zPB zFs [zHaupt, zHaupt]) ∧
    (einzelnPoolB mP mFs mCs [mHauptB, mHauptB] = false ∧
      ¬ EinzelnPool mP mFs [mHauptB, mHauptB]) := by
  refine ⟨⟨by decide, (einzelnPoolB_iff zFs_voll zCs_voll).mp (by decide)⟩, ⟨by decide, ?_⟩⟩
  intro h
  have e := (einzelnPoolB_iff mFs_voll mCs_voll).mpr h
  revert e
  decide

#print axioms Gabbro.Grammatik.Zielsatz.zPool_poolSicher
#print axioms Gabbro.Grammatik.Zielsatz.zPool_schreibt
#print axioms Gabbro.Grammatik.Zielsatz.zPool_akzeptiert
#print axioms Gabbro.Grammatik.Zielsatz.zPool_vor_abgelehnt
#print axioms Gabbro.Grammatik.Zielsatz.zPool_nutzerPflicht
#print axioms Gabbro.Grammatik.Zielsatz.zPool_start_offen
#print axioms Gabbro.Grammatik.Zielsatz.pool_ziel_zeuge
#print axioms Gabbro.Grammatik.Zielsatz.pool_abgelehnt
#print axioms Gabbro.Grammatik.Zielsatz.pool_abgelehnt_spec
#print axioms Gabbro.Grammatik.Zielsatz.pool_fuss_paart_vorkommen
#print axioms Gabbro.Grammatik.Zielsatz.pool_schreibt_nicht_voll
#print axioms Gabbro.Grammatik.Zielsatz.einzelnPoolB_iff_zeuge

end Gabbro.Grammatik.Zielsatz
