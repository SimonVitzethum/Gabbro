module

public import Grammatik.Zielsatz.Faeden.FaedenVor
public import Grammatik.Zielsatz.Faeden.PoolZeuge
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG
public import Grammatik.Zielsatz.Faeden.FaedenZeuge.Teil1
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

namespace Gabbro.Grammatik.Zielsatz
open Gabbro.Grammatik

/-- **THE GOAL ON A `start` RUN.** On the accepted unit `zStart`, the idle root starts two
    `haupt` threads (dormant before), both step, thread 1 takes the lock; the starter waits
    for its unfinished roots holding nothing -- and `gabbro_ziel` gives every leg of `ZielF`
    there: `Ziel` over the two spawned threads (race freedom between them included), and the
    join legs. -/
theorem spawn_start_ziel : ∃ K2 K3 K4 : FadenMaschine zD.mitRuhe,
    FadenErreichbar zPB.mitRuhe zO.mitRuhe 0 zsK0 K4 ∧
    zsK0.lebt 1 = false ∧ zsK0.lebt 2 = false ∧ K4.lebt 1 = true ∧ K4.lebt 2 = true ∧
    RufSchrittG zPB.mitRuhe zO.mitRuhe 0 zsK1.m 1 K2.m ∧
    RufSchrittG zPB.mitRuhe zO.mitRuhe 0 K2.m 2 K3.m ∧
    RufSchrittG zPB.mitRuhe zO.mitRuhe 0 K3.m 1 K4.m ∧
    (() : zD.mitRuhe.Lock) ∈ offen (K4.m.faeden 1).spur ∧
    K4.wartet 0 = [1, 2] ∧ JoinWartet K4 0 ∧
    ZielF zStart.P.mitRuhe zStart.S.mitRuhe zO.mitRuhe 0
      (RufStartG zStart.P.mitRuhe (speicherR zSp) zsInit) K4 := by
  have hoff : ∀ g, offen (zsK1.m.faeden g).spur = [] :=
    start_offen_leer zPB.mitRuhe (speicherR zSp) zsInit zsInit_leer
  obtain ⟨M2, s2, hZ2⟩ := w_endeEntf (P := zPB.mitRuhe) (O := zO.mitRuhe) (passes := 0)
    (M := zsK1.m) (f := 1) rfl zPoolLocks zPoolRet .nil rfl rfl
  let K2 : FadenMaschine zD.mitRuhe := ⟨M2, zsK1.lebt, zsK1.wartet, zsK1.rang, zsK1.uhr⟩
  have t2 : FadenSchritt zPB.mitRuhe zO.mitRuhe 0 zsK1 K2 := FadenSchritt.lauf zsK1 1 M2 rfl rfl s2
  obtain ⟨M3, s3, hZ3⟩ := w_endeEntf (P := zPB.mitRuhe) (O := zO.mitRuhe) (passes := 0)
    (M := M2) (f := 2) (rufSchrittG_fremd s2 2 (by decide)) zPoolLocks zPoolRet .nil rfl rfl
  let K3 : FadenMaschine zD.mitRuhe := ⟨M3, K2.lebt, K2.wartet, K2.rang, K2.uhr⟩
  have t3 : FadenSchritt zPB.mitRuhe zO.mitRuhe 0 K2 K3 := FadenSchritt.lauf K2 2 M3 rfl rfl s3
  have hfrei : RufFreiG M3 1 () := by
    intro g hg
    by_cases h2 : g = 2
    · subst h2
      rw [hZ3.1]
      show () ∉ offen (M2.weltVon 2).spur
      show () ∉ offen (M2.faeden 2).spur
      rw [rufSchrittG_fremd s2 2 (by decide), hoff]
      exact List.not_mem_nil
    · rw [rufSchrittG_fremd s3 g h2, rufSchrittG_fremd s2 g hg, hoff]
      exact List.not_mem_nil
  obtain ⟨M4, s4, hZ4⟩ := w_locks (P := zPB.mitRuhe) (O := zO.mitRuhe) (passes := 0)
    (M := M3) (f := 1) ((rufSchrittG_fremd s3 1 (by decide)).trans hZ2.1) ()
    (fun _ h => absurd h List.not_mem_nil) (ruB zLocksBody) .nil (.ende zPoolRet) .nil rfl
    (fun L => by
      show Res.held L ∈ ([] : List (Res zD.mitRuhe)) ↔ L ∈ offen (zsK1.m.faeden 1).spur
      rw [hoff]
      simp only [List.not_mem_nil]) hfrei
  let K4 : FadenMaschine zD.mitRuhe := ⟨M4, K3.lebt, K3.wartet, K3.rang, K3.uhr⟩
  have t4 : FadenSchritt zPB.mitRuhe zO.mitRuhe 0 K3 K4 := FadenSchritt.lauf K3 1 M4 rfl rfl s4
  have hr : FadenErreichbar zPB.mitRuhe zO.mitRuhe 0 zsK0 K4 :=
    .schritt _ _ (.schritt _ _ (.schritt _ _ (.schritt _ _ .start zs_schritt1) t2) t3) t4
  have hL1 : (() : zD.mitRuhe.Lock) ∈ offen (M4.faeden 1).spur := by
    rw [hZ4.1]
    show () ∈ () :: offen (M3.weltVon 1).spur
    exact List.mem_cons_self
  refine ⟨K2, K3, K4, hr, rfl, rfl, rfl, rfl, s2, s3, s4, hL1, rfl, ⟨2, by simp only [zsK1, List.mem_cons, List.not_mem_nil, or_false, Bool.ite_true_left, Bool.decide_or, ↓reduceIte,
  Nat.succ_ne_self, or_true, K3, K2, K4],
    fun hF => ?_⟩, ?_⟩
  · -- root 2 stands at its `locks`, not at a return
    have h := hF.2
    rw [rufSchrittG_fremd s4 2 (by decide), hZ3.1] at h
    exact Bool.false_ne_true h
  · exact gabbro_ziel_sc akzeptiert_pruefer zD zStart ⟨zFs, zFs_voll⟩ ⟨[()], zLs_voll⟩
      ⟨[.inl ()], zCs_voll⟩ zStart_akzeptiert zStart_nutzerPflicht zO
      ⟨zO_gut, zO_lokal, axVertragO_wahr zO⟩ 0 _ _ zStart_laufzeit zsLebt0 K4 hr

/-- **Probe B with a `child`**: `haupt` is a declared start AND the root of a run-time child
    (`gestartet`). `ws = [haupt, haupt, haupt]`. -/
def zKind : Einheit zD := ⟨zPB, zS, axWahr zD, [⟨zHaupt, .nil⟩], zSp, [⟨zHaupt, .nil⟩], []⟩

theorem zKind_ws : zKind.ws = [zHaupt, zHaupt, zHaupt] := by rfl

theorem zKind_akzeptiert :
    akzeptiert_pruefer.akzeptiert zKind zFs [()] [.inl ()] = true :=
  (by show Akzeptiert zPB zS zFs [()] [.inl ()] [zHaupt, zHaupt, zHaupt] = true; decide)

theorem zKind_nutzerPflicht : NutzerPflicht zKind :=
  ⟨⟨fun passes f => ⟨koerperGutS_alle zFs_voll (by decide) zPB_koerper passes f, zInvGutS f,
      zInvGutGrund f⟩, zS_lokal, axEnsLokal_wahr, ptrVerfeinert_trivial (fun f _ _ => by cases f <;> rfl) (fun _ => rfl)⟩,
    ⟨fun _ => rfl, fun a ha => by
      simp only [zKind, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false, or_self] at ha
      subst ha; rfl⟩⟩

/-- Threads 0 (the parent) and 1 (the child slot) at `haupt`, the idle root elsewhere. -/
def zkInit : Faden → Σ f : zD.mitRuhe.Fn, Env zD.mitRuhe (zD.mitRuhe.params f) :=
  fun t => if t = 0 ∨ t = 1 then ⟨some zHaupt, envR .nil⟩ else ⟨none, .nil⟩

theorem zkInit_leer (t : Faden) : zD.mitRuhe.haelt (zkInit t).1 = [] := by
  unfold zkInit; split <;> rfl

theorem zKind_laufzeit : Laufzeit zKind (speicherR zSp) zkInit where
  lader := by rfl
  start t := by
    unfold zkInit
    split
    · exact Or.inr ⟨⟨zHaupt, .nil⟩, by simp only [zKind, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, or_self], rfl⟩
    · exact Or.inl rfl
  einmal t u _ he := by
    revert he
    unfold zkInit
    split
    · intro _; exact Or.inr ⟨zHaupt, rfl, List.Sublist.cons _ (List.Sublist.refl _)⟩
    · intro _; exact Or.inl rfl

/-- Only the child slot 1 is dormant. -/
def zkLebt0 : Faden → Bool := fun t => !(decide (t = 1))

abbrev zkK0 : FadenMaschine zD.mitRuhe := FadenStart zPB.mitRuhe (speicherR zSp) zkInit zkLebt0

/-- Right after the parent (thread 0) spawns the child on thread 1. -/
def zkK1 : FadenMaschine zD.mitRuhe :=
  ⟨zkK0.m, fun t => if t = 1 then true else zkK0.lebt t, zkK0.wartet,
   fun t => if t = 1 then zkK0.rang 0 + 1 else zkK0.rang t, zkK0.uhr + 1⟩

theorem zk_schritt1 : FadenSchritt zPB.mitRuhe zO.mitRuhe 0 zkK0 zkK1 :=
  FadenSchritt.kind zkK0 0 1 rfl rfl rfl

/-- **THE GOAL ON A `child` RUN.** On the accepted unit `zKind`, the live `haupt` on thread 0
    spawns a `haupt` child on thread 1 (dormant before) and goes on: parent step, child step,
    parent takes the lock -- and `gabbro_ziel` gives every leg of `ZielF` there; the child
    entered holding nothing (`schlafendFrei` before the spawn, its empty trace after). -/
theorem spawn_kind_ziel : ∃ K2 K3 K4 : FadenMaschine zD.mitRuhe,
    FadenErreichbar zPB.mitRuhe zO.mitRuhe 0 zkK0 K4 ∧
    zkK0.lebt 1 = false ∧ K4.lebt 1 = true ∧ K4.wartet 0 = [] ∧
    RufSchrittG zPB.mitRuhe zO.mitRuhe 0 zkK1.m 0 K2.m ∧
    RufSchrittG zPB.mitRuhe zO.mitRuhe 0 K2.m 1 K3.m ∧
    RufSchrittG zPB.mitRuhe zO.mitRuhe 0 K3.m 0 K4.m ∧
    (() : zD.mitRuhe.Lock) ∈ offen (K4.m.faeden 0).spur ∧
    offen (K3.m.faeden 1).spur = [] ∧
    ZielF zKind.P.mitRuhe zKind.S.mitRuhe zO.mitRuhe 0
      (RufStartG zKind.P.mitRuhe (speicherR zSp) zkInit) K4 := by
  have hoff : ∀ g, offen (zkK1.m.faeden g).spur = [] :=
    start_offen_leer zPB.mitRuhe (speicherR zSp) zkInit zkInit_leer
  obtain ⟨M2, s2, hZ2⟩ := w_endeEntf (P := zPB.mitRuhe) (O := zO.mitRuhe) (passes := 0)
    (M := zkK1.m) (f := 0) rfl zPoolLocks zPoolRet .nil rfl rfl
  let K2 : FadenMaschine zD.mitRuhe := ⟨M2, zkK1.lebt, zkK1.wartet, zkK1.rang, zkK1.uhr⟩
  have t2 : FadenSchritt zPB.mitRuhe zO.mitRuhe 0 zkK1 K2 := FadenSchritt.lauf zkK1 0 M2 rfl rfl s2
  obtain ⟨M3, s3, hZ3⟩ := w_endeEntf (P := zPB.mitRuhe) (O := zO.mitRuhe) (passes := 0)
    (M := M2) (f := 1) (rufSchrittG_fremd s2 1 (by decide)) zPoolLocks zPoolRet .nil rfl rfl
  let K3 : FadenMaschine zD.mitRuhe := ⟨M3, K2.lebt, K2.wartet, K2.rang, K2.uhr⟩
  have t3 : FadenSchritt zPB.mitRuhe zO.mitRuhe 0 K2 K3 := FadenSchritt.lauf K2 1 M3 rfl rfl s3
  have h3sp : offen (M3.faeden 1).spur = [] := by
    rw [hZ3.1]
    show offen (M2.faeden 1).spur = []
    rw [rufSchrittG_fremd s2 1 (by decide), hoff]
  have hfrei : RufFreiG M3 0 () := by
    intro g hg
    by_cases h1 : g = 1
    · subst h1
      rw [h3sp]
      exact List.not_mem_nil
    · rw [rufSchrittG_fremd s3 g h1, rufSchrittG_fremd s2 g hg, hoff]
      exact List.not_mem_nil
  obtain ⟨M4, s4, hZ4⟩ := w_locks (P := zPB.mitRuhe) (O := zO.mitRuhe) (passes := 0)
    (M := M3) (f := 0) ((rufSchrittG_fremd s3 0 (by decide)).trans hZ2.1) ()
    (fun _ h => absurd h List.not_mem_nil) (ruB zLocksBody) .nil (.ende zPoolRet) .nil rfl
    (fun L => by
      show Res.held L ∈ ([] : List (Res zD.mitRuhe)) ↔ L ∈ offen (zkK1.m.faeden 0).spur
      rw [hoff]
      simp only [List.not_mem_nil]) hfrei
  let K4 : FadenMaschine zD.mitRuhe := ⟨M4, K3.lebt, K3.wartet, K3.rang, K3.uhr⟩
  have t4 : FadenSchritt zPB.mitRuhe zO.mitRuhe 0 K3 K4 := FadenSchritt.lauf K3 0 M4 rfl rfl s4
  have hr : FadenErreichbar zPB.mitRuhe zO.mitRuhe 0 zkK0 K4 :=
    .schritt _ _ (.schritt _ _ (.schritt _ _ (.schritt _ _ .start zk_schritt1) t2) t3) t4
  have hL0 : (() : zD.mitRuhe.Lock) ∈ offen (M4.faeden 0).spur := by
    rw [hZ4.1]
    show () ∈ () :: offen (M3.weltVon 0).spur
    exact List.mem_cons_self
  exact ⟨K2, K3, K4, hr, rfl, rfl, rfl, s2, s3, s4, hL0, h3sp,
    gabbro_ziel_sc akzeptiert_pruefer zD zKind ⟨zFs, zFs_voll⟩ ⟨[()], zLs_voll⟩
      ⟨[.inl ()], zCs_voll⟩ zKind_akzeptiert zKind_nutzerPflicht zO
      ⟨zO_gut, zO_lokal, axVertragO_wahr zO⟩ 0 _ _ zKind_laufzeit zkLebt0 K4 hr⟩

/-! ## 5. The refusals -/

/-- **`start` of a root that is not pool-safe is refused** (the model side of `N462`). `hauptB`
    of the two-thread fixture writes `privB` unguarded. As a run-time root (`gestartet`) it stands
    twice in `ws`, and the checker Bool refuses -- at the pool component alone. The same routine
    as an ordinary declared start beside `hauptA` is accepted: the refusal is the spawn's. -/
def mStartB : Einheit mD := ⟨mP, mSI, axWahr mD, [⟨mHauptA, .nil⟩], mSp, [⟨mHauptB, .nil⟩], []⟩

theorem start_nicht_poolsicher_abgelehnt :
    akzeptiert_pruefer.akzeptiert mStartB mFs [()] mCs = false ∧
    (programmImFragmentG mP mFs && abgAlleB mP mFs &&
      fussWB mP mSI mFs [mHauptA, mHauptB, mHauptB] && stufenB mP mFs && sperrOrteB mSI [()] &&
      wurzelnB [mHauptA, mHauptB, mHauptB] && rennB mP mFs mCs [mHauptA, mHauptB, mHauptB] &&
      antwortenB mP mFs) = true ∧
    einzelnPoolB mP mFs mCs [mHauptA, mHauptB, mHauptB] = false ∧
    Akzeptiert mP mSI mFs [()] mCs [mHauptA, mHauptB] = true := by
  refine ⟨?_, by decide, by decide, mP_akzeptiert⟩
  show Akzeptiert mP mSI mFs [()] mCs [mHauptA, mHauptB, mHauptB] = false
  decide

/-- The same refusal at the specification: no `AkzeptiertSpec` for `mStartB`, because a
    run-time root must be pool-safe (`akzeptiertSpec_gestartet`). -/
theorem start_nicht_poolsicher_spec : ¬ AkzeptiertSpec mP mSI mFs mStartB.ws := fun h =>
  pool_abgelehnt.2.2.2 (akzeptiertSpec_gestartet mStartB mFs h ⟨mHauptB, .nil⟩
    (List.mem_singleton_self _)).2.2

/-- **A `child` inside `locks` is refused** (the model side of `N456`). A region inside
    `locks L` lifts to a root that needs `L` at entry -- `wrap` of probe B, which holds the lock
    by signature (it is called only inside `haupt`'s `locks`). As a run-time root it is refused
    by the checker Bool at the root component (`wurzelnB`: a thread root holds nothing). -/
def zKindUnterSperre : Einheit zD :=
  ⟨zPB, zS, axWahr zD, [⟨zHaupt, .nil⟩], zSp, [⟨zWrap, .nil⟩], []⟩

theorem kind_unter_sperre_abgelehnt :
    zD.haelt zWrap = [()] ∧
    akzeptiert_pruefer.akzeptiert zKindUnterSperre zFs [()] [.inl ()] = false ∧
    wurzelnB [zHaupt, zWrap, zWrap] = false ∧
    Akzeptiert zPB zS zFs [()] [.inl ()] [zHaupt] = true := by
  refine ⟨rfl, ?_, by decide, zPB_akzeptiert⟩
  show Akzeptiert zPB zS zFs [()] [.inl ()] [zHaupt, zWrap, zWrap] = false
  decide

theorem kind_unter_sperre_spec : ¬ AkzeptiertSpec zPB zS zFs zKindUnterSperre.ws := fun h => by
  have := (akzeptiertSpec_gestartet zKindUnterSperre zFs h ⟨zWrap, .nil⟩
    (List.mem_singleton_self _)).1
  exact absurd this (by decide)

/-- **No `start` under a held lock** (the model side of `N461`): a step that makes a thread a
    joining starter needs that thread to hold nothing. -/
theorem start_unter_sperre_kein_schritt {D : Deklaration} {P : Programm D} {O : Orakel D}
    {passes : Nat} {K K' : FadenMaschine D} (hs : FadenSchritt P O passes K K') (p : Faden)
    (h0 : K.wartet p = []) (h1 : K'.wartet p ≠ []) : offen (K.m.faeden p).spur = [] := by
  cases hs with
  | lauf => exact absurd h0 h1
  | start q cs _ _ hfrei _ =>
      by_cases hpq : p = q
      · subst hpq; exact hfrei
      · exact absurd (by show (if p = q then cs else K.wartet p) = []; simp only [hpq, ↓reduceIte, h0]) h1
  | kind => exact absurd h0 h1
  | join q _ _ _ =>
      exact absurd (by show (if p = q then [] else K.wartet p) = []; split <;> simp_all) h1

/-- Instantiated: on the `child` run of §4, thread 0 holds the lock -- no step makes it a
    starter there. -/
theorem start_unter_sperre_zeuge : ∃ K : FadenMaschine zD.mitRuhe,
    FadenErreichbar zPB.mitRuhe zO.mitRuhe 0 zkK0 K ∧
    (() : zD.mitRuhe.Lock) ∈ offen (K.m.faeden 0).spur ∧
    ∀ K', FadenSchritt zPB.mitRuhe zO.mitRuhe 0 K K' → K'.wartet 0 = [] := by
  obtain ⟨_, _, K, hr, _, _, hw, _, _, _, hL, _⟩ := spawn_kind_ziel
  refine ⟨K, hr, hL, fun K' hs => Classical.byContradiction fun hne => ?_⟩
  rw [start_unter_sperre_kein_schritt hs 0 hw hne] at hL
  exact List.not_mem_nil hL

#print axioms Gabbro.Grammatik.Zielsatz.zStart_akzeptiert
#print axioms Gabbro.Grammatik.Zielsatz.zStart_nutzerPflicht
#print axioms Gabbro.Grammatik.Zielsatz.zStart_laufzeit
#print axioms Gabbro.Grammatik.Zielsatz.spawn_start_ziel
#print axioms Gabbro.Grammatik.Zielsatz.zKind_akzeptiert
#print axioms Gabbro.Grammatik.Zielsatz.spawn_kind_ziel
#print axioms Gabbro.Grammatik.Zielsatz.start_nicht_poolsicher_abgelehnt
#print axioms Gabbro.Grammatik.Zielsatz.start_nicht_poolsicher_spec
#print axioms Gabbro.Grammatik.Zielsatz.kind_unter_sperre_abgelehnt
#print axioms Gabbro.Grammatik.Zielsatz.kind_unter_sperre_spec
#print axioms Gabbro.Grammatik.Zielsatz.start_unter_sperre_kein_schritt
#print axioms Gabbro.Grammatik.Zielsatz.start_unter_sperre_zeuge

end Gabbro.Grammatik.Zielsatz
