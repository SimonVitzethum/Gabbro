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
    the leg `schwach` is not true of every program: it needs the checker. As a THEOREM:
    `schwach_nicht_trivial` (`¬ SchwachSC` at that machine), via `g_schritt_0` -- every G
    step of that thread there stores `3` (inversion over the rules of `RufSchrittG`).
  * `schwach_pool_zeuge` -- POSITIVE. On the pool unit of fix lane F10 (accepted by the
    concrete checker, two threads running one routine), a run of machine W with three steps
    (both instances unfold, thread 0 takes the lock) reaches a machine whose G-part G
    reaches, at which every leg of `Ziel` holds -- by `gabbro_ziel_schwach`, the goal over
    the weak machine, not by `gabbro_ziel`.
-/
import Lean
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

open Lean Elab Tactic Meta in
/-- Case-analysis helper: find the hypothesis `X = rhs` whose left side is the left side of
    `hR` (after `cases` on a step, the constructor's `hhead`, whose name is inaccessible),
    and add `hk : rhs_of_hR = rhs`. -/
elab "kopf_gleich " hR:term : tactic => withMainContext do
  let hRe ← Term.elabTerm hR none
  let some (_, lhs, _) := (← instantiateMVars (← inferType hRe)).eq? | throwError "hR no eq"
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let some (_, a, _) := ty.eq? then
      if a == lhs then
        let pr ← mkEqTrans (← mkEqSymm hRe) d.toExpr
        let g ← getMainGoal
        let g ← g.assert `hk (← inferType pr) pr
        let (_, g) ← g.intro1P
        replaceMainGoal [g]
        return
  throwError "no head hypothesis"

/-- Whether a frame residue's head is a leaf at the end block. -/
def kopfBlatt {D : Deklaration} {V : Vertrag D} :
    (Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ) → Bool
  | ⟨_, _, _, _, .ende (.cons s _)⟩ => s.istBlatt
  | _ => false

/-- Thread 0 (`hauptA`) at `r1M1`: `tabA[0] = konfig; return` at the start of its body. -/
theorem kopf0 : ((r1M1 sp0).faeden 0).kopf.rest =
    ⟨false, [], [], .nil, .ende (.cons sA (.ret .keine List.Perm.nil))⟩ := rfl

/-- **Determinism of G at the point `w_nicht_sc` uses**: EVERY G step of thread 0 from
    `r1M1` (after `kern` wrote `konfig := 3`) writes `tabA[0] = 3`. Inversion over all rules
    of `RufSchrittG`: every rule but `blatt`, `endeEntf`, `ruf`, `rufCallInd` needs a
    different head residue; `ruf`/`rufCallInd` need a call at the head (not a leaf), and
    `endeEntf` an unfoldable compound; `blatt` runs `execStmt` on the head statement, a
    function of the thread's world. -/
theorem g_schritt_0 {M' : RufMaschineG nD} (h : RufSchrittG nP nO 0 (r1M1 sp0) 0 M') :
    (M'.speicher.slots NTab.tabA 0 ()).n = 3 := by
  cases h
  all_goals (kopf_gleich kopf0)
  all_goals (try (cases hk; done))
  case ruf => exact Bool.noConfusion (congrArg kopfBlatt hk)
  case rufCallInd => exact Bool.noConfusion (congrArg kopfBlatt hk)
  case endeEntf => cases hk; cases (by assumption : GEntfaltbar sA = true)
  case blatt =>
    cases hk
    rename_i σ' _ _ _ ρ' _ _ hstep _
    have hx : execStmt nO 0 keinRuf sA ((r1M1 sp0).weltVon 0) Env.nil =
        Ausgang.ok (blattWelt sA ((r1M1 sp0).weltVon 0) .nil) .nil := rfl
    have he := hx.symm.trans hstep
    cases he
    rfl


/-- **THE LEG `schwach` IS NOT TRUE OF EVERY PROGRAM** (review F3 of the Spec-diff verdict,
    2026-09-26: until now argued, not proved). On the REFUSED configuration 1, at the machine
    `r1M1` G reaches, the weak machine takes a step that is no step of G: `w_nicht_sc` stores
    `0`, and every G step of the same thread stores `3` (`g_schritt_0`). So `SchwachSC` is a
    contentful leg: it needs the checker. -/
theorem schwach_nicht_trivial :
    ¬ Zielsatz.SchwachSC nP nO 0 (RufStartG nP sp0 init1) (r1M1 sp0) := by
  intro hS
  obtain ⟨W1, W2, hW1, hs, hg1, _, h0, _⟩ := w_nicht_sc (fun _ => Ordnung.entspannt)
  have h3 := g_schritt_0 (hS _ W1 W2 0 hW1 hg1 hs)
  omega


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
