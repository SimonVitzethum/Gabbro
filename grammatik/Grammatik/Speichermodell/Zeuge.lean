/-
  File:      Grammatik/Speichermodell/Zeuge.lean
  Subject:   The witnesses of the weak-memory leg (Opus agent B, 2026-09-26).

  * `w_nicht_sc` -- NON-DEGENERACY AT THE LEVEL OF G, and the REFUSAL. The configuration 1 of
    the noninterference fixture (`NIZeuge`: `kern` writes the atomic `konfig := 3`, `hauptA`
    copies `konfig` into `tabA[0]`, no lock anywhere) is REFUSED by the checker
    (`akzeptiert_n1_abgelehnt`: `konfig` is read by `hauptA` and written by `kern`, neither
    local nor guarded -- the footprint component). On it machine W does what G cannot on the
    same schedule: after `kern`'s write, `hauptA` reads the INITIAL message of `konfig` (its
    view is still empty) and writes `0`, where G -- `kern`, then `hauptA` -- writes `3`. So
    the leg `schwach` is not true of every program: it needs the checker.
  * `schwach_pool_zeuge` -- POSITIVE. On the pool unit of fix lane F10 (accepted by the
    concrete checker, two threads running one routine), a run of machine W with three steps
    (both instances unfold, thread 0 takes the lock) reaches a machine whose G-part G
    reaches, at which every leg of `Ziel` holds -- by `gabbro_ziel_schwach`, the goal over
    the weak machine, not by `gabbro_ziel`.
-/
import Grammatik.Nichtinterferenz.Zeuge
import Grammatik.Zielsatz.PoolZeuge
import Grammatik.Zielsatz.Schwach

namespace Gabbro.Grammatik

open Speichermodell

namespace SchwachZeuge

open NIZeuge

/-! ## 1. W on a refused program: a stale read that G cannot make -/

/-- No lock in the noninterference fixture. -/
def nS : SperrInv nD := ⟨(fun e => nomatch e), (fun e => nomatch e)⟩

/-- **The checker refuses configuration 1** (`hauptA`, `hauptB`, `kern` as starts): the
    atomic `konfig` is read by the tenants and written by the kernel thread, with no lock. -/
theorem akzeptiert_n1_abgelehnt :
    Akzeptiert nP nS nFs [] nCs [NFn.hauptA, NFn.hauptB, NFn.kern] = false := by
  decide

/-- It is the footprint component that refuses. -/
theorem fuss_n1_abgelehnt : fussWB nP nS nFs [NFn.hauptA, NFn.hauptB, NFn.kern] = false := by
  decide

/-- The initial message of every carrier. -/
def m0 : NachrichtW nD := ⟨0, sp0, Sicht.null⟩

/-- `hauptA`'s statement: `tabA[0] = konfig`. -/
abbrev sA : Stmt nD (vertragVon nD NFn.hauptA) false [] [] [] :=
  .assignSlot NTab.tabA () nI0 (.glob NGlob.konfig (nGd _ _)) rfl (nDarf _ _)

/-- The machine at which `hauptA` runs its statement on the INITIAL memory: G's threads after
    `kern`'s step, and the memory `sp0` presented. -/
abbrev mStale : RufMaschineG nD := mitSpeicher (r1M1 sp0) sp0

theorem stale_schritt :
    RufSchrittG nP nO 0 mStale 0 (blattM mStale 0 sA (.ret .keine List.Perm.nil)) :=
  blattM_schritt mStale 0 _ _ rfl rfl rfl rfl

/-- The accesses the stale step records: the write of `tabA`, the read of `konfig`. -/
theorem stale_zugriffe : zugriffe mStale (blattM mStale 0 sA (.ret .keine List.Perm.nil)) 0 =
    [(.inl NTab.tabA, true), (.inr NGlob.konfig, false)] := rfl

/-- The stale step reads `konfig`. -/
theorem stale_liest :
    LiestG mStale (blattM mStale 0 sA (.ret .keine List.Perm.nil)) 0 (.inr NGlob.konfig) := by
  show (_, false) ∈ zugriffe _ _ _
  rw [stale_zugriffe]
  exact List.mem_cons_of_mem _ List.mem_cons_self

/-- **W READS A STALE VALUE ON A REFUSED PROGRAM.** For every order assignment: W reaches, after
    `kern` wrote `konfig := 3`, a state from which `hauptA` reads the initial `konfig = 0` and
    writes `tabA[0] = 0`; G on the same schedule (`kern`, then `hauptA`) writes `tabA[0] = 3`. -/
theorem w_nicht_sc (ord : nD.Glob → Ordnung) :
    ∃ W1 W2 : RufMaschineW nD,
      RufErreichbarW nP nO 0 ord (RufStartW (RufStartG nP sp0 init1)) W1 ∧
      RufSchrittW nP nO 0 ord W1 0 W2 ∧
      W1.g = r1M1 sp0 ∧ (W1.g.speicher.globs NGlob.konfig).n = 3 ∧
      (W2.g.speicher.slots NTab.tabA 0 ()).n = 0 ∧
      ((r1M2 sp0).speicher.slots NTab.tabA 0 ()).n = 3 := by
  -- step 1: `kern` writes, lifted from G
  have s1 : RufSchrittG nP nO 0 (r1M0 sp0) 2 (r1M1 sp0) := blattM_schritt (r1M0 sp0) 2 _ _ rfl rfl rfl rfl
  obtain ⟨W1, hs1, hg1, hF1⟩ := schrittW_aus_g (ord := ord) (scForm_start (r1M0 sp0)) s1
  have hW1 : RufErreichbarW nP nO 0 ord (RufStartW (RufStartG nP sp0 init1)) W1 :=
    .schritt _ _ _ .start hs1
  -- what step 1 left for thread 0: its empty view, and the initial messages
  obtain ⟨σ1, M1', wahl1, neu1, h1⟩ := hs1
  have hsicht : W1.sicht 0 = Sicht.null := h1.sichtF 0 (by decide)
  have hm0 : ∀ c, m0 ∈ W1.hist c := by
    intro c
    by_cases hw : SchreibG (mitSpeicher (RufStartW (r1M0 sp0)).g σ1) M1' 2 c
    · rw [h1.histS c hw]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    · rw [h1.histU c hw]; exact List.mem_singleton_self _
  obtain ⟨T, hT⟩ := hF1
  -- step 2: `hauptA` on the presented initial memory
  have hs2 : RufSchrittG nP nO 0 (mitSpeicher W1.g sp0) 0
      (blattM mStale 0 sA (.ret .keine List.Perm.nil)) := by
    rw [hg1]; exact stale_schritt
  have hl : ∀ c, LiestG (mitSpeicher W1.g sp0) (blattM mStale 0 sA (.ret .keine List.Perm.nil)) 0 c →
      Lesbar W1.hist (W1.sicht 0) c m0 ∧ TraegerGleich sp0 m0.wert c := by
    intro c _
    refine ⟨⟨hm0 c, ?_⟩, traegerGleich_refl _ c⟩
    rw [hsicht]; exact Nat.zero_le _
  have hu : ∀ c, ¬ LiestG (mitSpeicher W1.g sp0) (blattM mStale 0 sA (.ret .keine List.Perm.nil)) 0 c →
      TraegerGleich sp0 W1.g.speicher c := by
    intro c hc
    rw [hg1] at hc ⊢
    cases c with
    | inl t => rfl
    | inr g =>
        cases g with
        | konfig => exact absurd stale_liest hc
        | zaehler => rfl
  obtain ⟨W2, h2, hS2, _⟩ := schrittW_bau (ord := ord) hs2 (fun _ => m0) hl hu T
    (fun c => ⟨(hT c).2.1, (hT c).2.2.1, (hT c).2.2.2.1, (hT c).2.2.2.2⟩) hm0
  have hwA : SchreibG (mitSpeicher W1.g sp0) (blattM mStale 0 sA (.ret .keine List.Perm.nil)) 0
      (.inl NTab.tabA) := by
    rw [hg1]
    refine Or.inl ?_
    show (_, true) ∈ zugriffe mStale _ 0
    rw [stale_zugriffe]
    exact List.mem_cons_self
  have hA := hS2 _ hwA
  refine ⟨W1, W2, hW1, ⟨sp0, _, _, _, h2⟩, hg1, ?_, ?_, ?_⟩
  · rw [hg1]; rfl
  · have e : W2.g.speicher.slots NTab.tabA = (blattM mStale 0 sA (.ret .keine List.Perm.nil)).speicher.slots NTab.tabA := hA
    rw [e]; rfl
  · rfl

/-! ## 2. The goal over the weak machine on an accepted pool -/

open Zielsatz

/-- **The pool witness over W.** On the runtime's start of the pool unit `zPool` (accepted by
    the concrete checker), machine W runs thread 0, thread 1, thread 0 (both instances unfold,
    thread 0 takes the lock); at the reached machine thread 0 holds the lock, its G-part is
    reached by G, and every leg of `Ziel` holds there -- by `gabbro_ziel_schwach`. -/
theorem schwach_pool_zeuge (ord : zD.mitRuhe.Glob → Ordnung) :
    ∃ W1 W2 W3 : RufMaschineW zD.mitRuhe,
      RufSchrittW zPB.mitRuhe zO.mitRuhe 0 ord (RufStartW zPoolM0) 0 W1 ∧
      RufSchrittW zPB.mitRuhe zO.mitRuhe 0 ord W1 1 W2 ∧
      RufSchrittW zPB.mitRuhe zO.mitRuhe 0 ord W2 0 W3 ∧
      (() : zD.mitRuhe.Lock) ∈ offen (W3.g.faeden 0).spur ∧
      RufErreichbarG zPool.P.mitRuhe zO.mitRuhe 0 zPoolM0 W3.g ∧
      Ziel zPool.P.mitRuhe zPool.S.mitRuhe zO.mitRuhe 0 zPoolM0 W3.g := by
  obtain ⟨M1, M2, M3, hL, _, _, s1, s2, s3, hlock, _⟩ := pool_ziel_zeuge
  obtain ⟨W1, t1, g1, F1⟩ := schrittW_aus_g (ord := ord) (scForm_start zPoolM0) s1
  obtain ⟨W2, t2, g2, F2⟩ := schrittW_aus_g (ord := ord) F1 (by rw [g1]; exact s2)
  obtain ⟨W3, t3, g3, F3⟩ := schrittW_aus_g (ord := ord) F2 (by rw [g2]; exact s3)
  have hW3 : RufErreichbarW zPool.P.mitRuhe zO.mitRuhe 0 ord (RufStartW zPoolM0) W3 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start t1) t2) t3
  have hZ := gabbro_ziel_schwach akzeptiert_pruefer zD zPool ⟨zFs, zFs_voll⟩ ⟨[()], zLs_voll⟩
    ⟨[.inl ()], zCs_voll⟩
    (by show Akzeptiert zPB zS zFs [()] [.inl ()] [zHaupt, zHaupt] = true
        exact zPool_akzeptiert)
    zPool_nutzerPflicht zO ⟨zO_gut, zO_lokal, axVertragO_wahr zO⟩ 0 _ _ hL ord W3 hW3
  exact ⟨W1, W2, W3, t1, t2, t3, by rw [g3]; exact hlock, hZ.1, hZ.2⟩

end SchwachZeuge

#print axioms Gabbro.Grammatik.SchwachZeuge.akzeptiert_n1_abgelehnt
#print axioms Gabbro.Grammatik.SchwachZeuge.w_nicht_sc
#print axioms Gabbro.Grammatik.SchwachZeuge.schwach_pool_zeuge

end Gabbro.Grammatik
