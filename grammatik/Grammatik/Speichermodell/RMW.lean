/-
  File:      Grammatik/Speichermodell/RMW.lean
  Subject:   READ-MODIFY-WRITE ATOMICITY OVER MACHINE W -- OFFEN O25, item "RMW" (Opus lane
             O25b, 2026-09-26). Standalone: `Zielsatz/Spec.lean` does not import this file,
             and no definition it imports changes here (`schrittW_aus_g` in MaschineW.lean
             only gained a conjunct in its conclusion).

  THE DEFECT (`zaehler_verloren`, Zaehler.lean). Machine W lets a step that reads and writes one
  atomic -- `exchange`, emitted as `atomic_fetch_*` or a bounded CAS loop, ONE read-modify-write
  of the C abstract machine -- write at ANY fresh timestamp above its view. Two such steps may
  then read the same message and both write above it: the lost update, which C11/RC11 forbids
  for an RMW (its write is immediately after the message it read in modification order).

  THE REPAIR, as a sub-machine. `RufSchrittWR` is a W step with ONE more condition: when the
  acting thread's head is an `exchange` of `g`, the write at `g` takes the timestamp directly
  above the message it read (`neu = ts + 1`). Timestamps are natural numbers and a write must
  be fresh (`Frisch`), so no other write can sit in between, and no second RMW can read the same
  message:
  * `wr_w`             -- every WR run is a W run: every claim over W (the DRF theorems of
                          DRF.lean and Atomar.lean, `hb_uebergabe`) holds over WR unchanged;
  * `wr_aus_g`         -- every G run is a WR run: the SC construction of `schrittW_aus_g`
                          writes every carrier at `T + 1` over the message at `T` it reads, so
                          WR still contains G (nothing G does is lost);
  * `exchange_liest_schreibt` -- an `exchange` step of G reads and writes its global;
  * **`wr_kein_verlust`** -- on every WR run, two `exchange` steps of one global never read the
                          same message (the RC11 atomicity axiom in timestamp form);
  * **`wr_rmw_kette`** -- the write of an `exchange` is the ONLY message directly above the one
                          it read, at every later point of the run.
  WHY A SUB-MACHINE AND NOT AN EDIT OF `SchrittW`: `SchrittW` is imported by the goal statement
  (the leg `schwach`); restricting it is a Spec diff, which O25 makes only as ONE reviewed diff
  together with the replay (messung/OPUS-O25B-ATOMICS.md §5). The sub-machine makes the change
  ready: every theorem of this file transfers to W the moment `SchrittW` gains the condition.
-/
import Lean
import Grammatik.Speichermodell.Atomar

namespace Gabbro.Grammatik

open Speichermodell

open Lean Elab Tactic Meta in
/-- For a hypothesis `hR : lhs = rhs`, find another hypothesis `h : lhs = rhs'` and add
    `hk : rhs = rhs'` (the head of a thread, known two ways, after `cases` on a step). -/
elab "kopf_vergleich " hR:term : tactic => withMainContext do
  let hRe ← Term.elabTerm hR none
  let some (_, lhs, _) := (← instantiateMVars (← inferType hRe)).eq? | throwError "hR no eq"
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if d.toExpr == hRe then continue
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

variable {D : Deklaration}

/-! ## 1. The machine -/

/-- **The acting thread's head is an `exchange` of `g`** (the one read-modify-write form). -/
def ExchangeKopf (M : RufMaschineG D) (u : Faden) (g : D.Glob) : Prop :=
  ∃ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (neuE : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g))
    (hw : (vertragVon D (M.faeden u).kopf.f).gschreibt g = true) (hL : gdarf D g Λ)
    (rest : Block D (vertragVon D (M.faeden u).kopf.f) l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ') (ρ : Env D Γ),
    (M.faeden u).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.exchange g neuE hw hL rest) k⟩

/-- **One step of W with atomic read-modify-writes**: a W step whose `exchange` writes directly
    above the message it read. -/
def RufSchrittWR (P : Programm D) (O : Orakel D) (passes : Nat) (ord : D.Glob → Ordnung)
    (W : RufMaschineW D) (u : Faden) (W' : RufMaschineW D) : Prop :=
  ∃ σ M'' wahl neu, SchrittW P O passes ord W u W' σ M'' wahl neu ∧
    ∀ g, ExchangeKopf W.g u g → neu (.inr g) = (wahl (.inr g)).ts + 1

/-- The machines WR reaches from `W0`. -/
inductive RufErreichbarWR (P : Programm D) (O : Orakel D) (passes : Nat) (ord : D.Glob → Ordnung)
    (W0 : RufMaschineW D) : RufMaschineW D → Prop where
  | start : RufErreichbarWR P O passes ord W0 W0
  | schritt (W W' : RufMaschineW D) (u : Faden) :
      RufErreichbarWR P O passes ord W0 W → RufSchrittWR P O passes ord W u W' →
        RufErreichbarWR P O passes ord W0 W'

section WR

variable {P : Programm D} {O : Orakel D} {passes : Nat} {ord : D.Glob → Ordnung}

/-- **Every WR run is a W run**: every theorem over W holds over WR. -/
theorem wr_w {W0 W : RufMaschineW D} (h : RufErreichbarWR P O passes ord W0 W) :
    RufErreichbarW P O passes ord W0 W := by
  induction h with
  | start => exact .start
  | schritt W W' u _ hs ih =>
      obtain ⟨σ, M'', wahl, neu, h, _⟩ := hs
      exact .schritt _ _ _ ih ⟨σ, M'', wahl, neu, h⟩

/-- **Every G run is a WR run** (for every order assignment): the SC construction writes every
    carrier right above the message it reads. WR loses no behaviour of G. -/
theorem wr_aus_g {M0 M : RufMaschineG D} (hr : RufErreichbarG P O passes M0 M) :
    ∃ W, RufErreichbarWR P O passes ord (RufStartW M0) W ∧ W.g = M ∧ SCForm W := by
  induction hr with
  | start => exact ⟨RufStartW M0, .start, rfl, scForm_start M0⟩
  | schritt M M' u _ hs ih =>
      obtain ⟨W, hW, rfl, hF⟩ := ih
      obtain ⟨W', σ, M'', wahl, neu, hstep, hadj, hg, hF'⟩ := schrittW_aus_g (ord := ord) hF hs
      exact ⟨W', .schritt W W' u hW ⟨σ, M'', wahl, neu, hstep, fun g _ => hadj _⟩, hg, hF'⟩

/-- **An `exchange` step reads and writes its global** (inversion over the rules of G: only
    `dannExchange` fires at an `exchange` head). -/
theorem exchange_liest_schreibt {M M' : RufMaschineG D} {u : Faden} {g : D.Glob}
    (hk : ExchangeKopf M u g) (hs : RufSchrittG P O passes M u M') :
    LiestG M M' u (.inr g) ∧ SchreibG M M' u (.inr g) := by
  obtain ⟨l, Γ, Λ, Λ', neuE, hw, hL, rest, k, ρ, hK⟩ := hk
  cases hs
  all_goals (kopf_vergleich hK)
  all_goals (try (cases hk; done))
  case dannExchange σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
    cases hk
    have hX : (rufUpdateG M.faeden u ⟨(M.faeden u).stapel,
        ⟨(M.faeden u).kopf.f, (M.faeden u).kopf.rho, (M.faeden u).kopf.s0,
         ⟨l, D.gtyp g :: Γ, Λ, .cons (σ₁.globs g) ρ, .dann rest (.schrumpf k)⟩⟩,
        σ₂.spur, (M.faeden u).log⟩ u).spur = (Ereignis.gzugriff g true Λ σ₁.haelt ::
          leseEv (M.weltVon u) Λ (Sum.inr g :: neuE.orte)) ++ (M.faeden u).spur := by
      simp only [rufUpdateG_self]
      rw [hs₂, hs₁]
      rfl
    have hE := ereignisse_eq (M := M) (M' := ⟨σ₂.speicher, _, M.lauf ++ rufEigenG u neu, M.start⟩)
      (f := u) hX
    refine ⟨?_, Or.inl ?_⟩
    · show (Sum.inr g, false) ∈ zugriffe M _ u
      rw [zugriffe_ereignisse, hE]
      exact List.mem_filterMap.mpr ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
    · show (Sum.inr g, true) ∈ zugriffe M _ u
      rw [zugriffe_ereignisse, hE]
      exact List.mem_filterMap.mpr ⟨_, List.mem_cons_self, rfl⟩

end WR

/-! ## 2. No lost update -/

section Atomar

variable {P : Programm D} {O : Orakel D} {passes : Nat} {ord : D.Glob → Ordnung}

/-- **The write of an atomic RMW sits directly above the message it read**: after the step, the
    history of `g` holds a message at `ts + 1` of the read message. -/
theorem wr_schreibt_darueber {W W' : RufMaschineW D} {u : Faden} {σ : Speicher D}
    {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D} {neu : D.Tab ⊕ D.Glob → Nat}
    (h : SchrittW P O passes ord W u W' σ M'' wahl neu) {g : D.Glob}
    (hk : ExchangeKopf W.g u g) (hadj : neu (.inr g) = (wahl (.inr g)).ts + 1) :
    ∃ m ∈ W'.hist (.inr g), m.ts = (wahl (.inr g)).ts + 1 := by
  have hk' : ExchangeKopf (mitSpeicher W.g σ) u g := hk
  have hw := (exchange_liest_schreibt hk' h.schritt).2
  rw [h.histS _ hw]
  exact ⟨_, List.mem_cons_self, hadj⟩

/-- **NO LOST UPDATE.** On every run of WR: an `exchange` of `g` by thread `u₁` in the step
    `W1 → W2`, then any W steps to `W3`, then an `exchange` of `g` by thread `u₂` in the step
    `W3 → W4` -- the two read DIFFERENT messages of `g` (different timestamps). So no two RMWs
    ever build on the same value: RC11's atomicity of read-modify-writes, which W alone does not
    give (`zaehler_verloren`). -/
theorem wr_kein_verlust {W1 W2 W3 W4 : RufMaschineW D} {u₁ u₂ : Faden} {g : D.Glob}
    {σ1 : Speicher D} {N1 : RufMaschineG D} {wahl1 : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu1 : D.Tab ⊕ D.Glob → Nat}
    (h1 : SchrittW P O passes ord W1 u₁ W2 σ1 N1 wahl1 neu1) (hk1 : ExchangeKopf W1.g u₁ g)
    (ha1 : neu1 (.inr g) = (wahl1 (.inr g)).ts + 1)
    (h23 : RufErreichbarW P O passes ord W2 W3)
    {σ3 : Speicher D} {N3 : RufMaschineG D} {wahl3 : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu3 : D.Tab ⊕ D.Glob → Nat}
    (h3 : SchrittW P O passes ord W3 u₂ W4 σ3 N3 wahl3 neu3) (hk3 : ExchangeKopf W3.g u₂ g)
    (ha3 : neu3 (.inr g) = (wahl3 (.inr g)).ts + 1) :
    (wahl1 (.inr g)).ts ≠ (wahl3 (.inr g)).ts := by
  intro he
  obtain ⟨m, hm, hts⟩ := wr_schreibt_darueber h1 hk1 ha1
  have hm3 : m ∈ W3.hist (.inr g) := (laufW_waechst h23).1 _ _ hm
  have hk3' : ExchangeKopf (mitSpeicher W3.g σ3) u₂ g := hk3
  have hw3 := (exchange_liest_schreibt hk3' h3.schritt).2
  have hfr := (h3.frisch _ hw3).2 m hm3
  apply hfr
  rw [hts, ha3, he]

/-- The same over a run of WR (the middle segment is a WR run). -/
theorem wr_kein_verlust_lauf {W0 W1 W2 W3 W4 : RufMaschineW D} {u₁ u₂ : Faden} {g : D.Glob}
    (_h01 : RufErreichbarWR P O passes ord W0 W1)
    {σ1 : Speicher D} {N1 : RufMaschineG D} {wahl1 : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu1 : D.Tab ⊕ D.Glob → Nat}
    (h1 : SchrittW P O passes ord W1 u₁ W2 σ1 N1 wahl1 neu1)
    (hr1 : ∀ g, ExchangeKopf W1.g u₁ g → neu1 (.inr g) = (wahl1 (.inr g)).ts + 1)
    (hk1 : ExchangeKopf W1.g u₁ g)
    (h23 : RufErreichbarWR P O passes ord W2 W3)
    {σ3 : Speicher D} {N3 : RufMaschineG D} {wahl3 : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu3 : D.Tab ⊕ D.Glob → Nat}
    (h3 : SchrittW P O passes ord W3 u₂ W4 σ3 N3 wahl3 neu3)
    (hr3 : ∀ g, ExchangeKopf W3.g u₂ g → neu3 (.inr g) = (wahl3 (.inr g)).ts + 1)
    (hk3 : ExchangeKopf W3.g u₂ g) :
    (wahl1 (.inr g)).ts ≠ (wahl3 (.inr g)).ts :=
  wr_kein_verlust h1 hk1 (hr1 g hk1) (wr_w h23) h3 hk3 (hr3 g hk3)

/-- **The chain**: at every later point of the run, a message of `g` at the timestamp directly
    above the one an `exchange` read is the `exchange`'s own write -- exactly one message sits
    there, and it is the RMW's. -/
theorem wr_rmw_kette {W1 W2 W3 : RufMaschineW D} {u : Faden} {g : D.Glob}
    {σ1 : Speicher D} {N1 : RufMaschineG D} {wahl1 : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu1 : D.Tab ⊕ D.Glob → Nat}
    (h1 : SchrittW P O passes ord W1 u W2 σ1 N1 wahl1 neu1) (hk1 : ExchangeKopf W1.g u g)
    (ha1 : neu1 (.inr g) = (wahl1 (.inr g)).ts + 1)
    (h23 : RufErreichbarW P O passes ord W2 W3) :
    ∃ m ∈ W3.hist (.inr g), m.ts = (wahl1 (.inr g)).ts + 1 := by
  obtain ⟨m, hm, hts⟩ := wr_schreibt_darueber h1 hk1 ha1
  exact ⟨m, (laufW_waechst h23).1 _ _ hm, hts⟩

end Atomar

#print axioms Gabbro.Grammatik.wr_w
#print axioms Gabbro.Grammatik.wr_aus_g
#print axioms Gabbro.Grammatik.exchange_liest_schreibt
#print axioms Gabbro.Grammatik.wr_kein_verlust
#print axioms Gabbro.Grammatik.wr_kein_verlust_lauf
#print axioms Gabbro.Grammatik.wr_rmw_kette

end Gabbro.Grammatik
