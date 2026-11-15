/- The stale-read counterexample, independent of the accepted pool fixture. -/
module
public import Lean
public import Grammatik.Nichtinterferenz.Zeuge
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

local instance : DecidableEq nD.Ax := inferInstanceAs (DecidableEq Empty)

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
    RufSchrittG nP nO 0 mStale 0 (blattM mStale 0 sA (.ret .empty List.Perm.nil)) :=
  blattM_schritt mStale 0 _ _ rfl rfl rfl rfl

/-- The accesses the stale step records: the write of `tabA`, the read of `konfig`. -/
theorem stale_zugriffe : zugriffe mStale (blattM mStale 0 sA (.ret .empty List.Perm.nil)) 0 =
    [(.inl NTab.tabA, true), (.inr NGlob.konfig, false)] := by rfl

/-- The stale step reads `konfig`. -/
theorem stale_liest :
    LiestG mStale (blattM mStale 0 sA (.ret .empty List.Perm.nil)) 0 (.inr NGlob.konfig) := by
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
  obtain ⟨W1, hs1, hg1, hF1⟩ := schrittW_aus_gW (ord := ord) (scForm_start (r1M0 sp0)) s1
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
      (blattM mStale 0 sA (.ret .empty List.Perm.nil)) := by
    rw [hg1]; exact stale_schritt
  have hl : ∀ c, LiestG (mitSpeicher W1.g sp0) (blattM mStale 0 sA (.ret .empty List.Perm.nil)) 0 c →
      Lesbar W1.hist (W1.sicht 0) c m0 ∧ TraegerGleich sp0 m0.wert c := by
    intro c _
    refine ⟨⟨hm0 c, ?_⟩, traegerGleich_refl _ c⟩
    rw [hsicht]; exact Nat.zero_le _
  have hu : ∀ c, ¬ LiestG (mitSpeicher W1.g sp0) (blattM mStale 0 sA (.ret .empty List.Perm.nil)) 0 c →
      TraegerGleich sp0 W1.g.speicher c := by
    intro c hc
    rw [hg1] at hc ⊢
    cases c with
    | inl t => rfl
    | inr g =>
        cases g with
        | konfig => exact absurd stale_liest hc
        | zaehler => rfl
  -- thread 0 stands at the start of `hauptA`: no `exchange` head, so no RMW condition
  have hkein : ∀ g, ¬ ExchangeKopf W1.g 0 g := fun g hk => by
    have h := exchangeKopf_glob hk
    rw [hg1] at h
    have h0 : ((r1M1 sp0).faeden 0).kopf.rest.2.2.2.2.exchangeGlob = none := rfl
    rw [h0] at h
    cases h
  obtain ⟨W2, h2, hS2, _⟩ := schrittW_bau (ord := ord) hs2 (fun _ => m0) hl hu T
    (fun c => ⟨(hT c).2.1, (hT c).2.2.1, (hT c).2.2.2.1, (hT c).2.2.2.2⟩) hm0
    (fun g hk => absurd hk (hkein g))
  have hwA : SchreibG (mitSpeicher W1.g sp0) (blattM mStale 0 sA (.ret .empty List.Perm.nil)) 0
      (.inl NTab.tabA) := by
    rw [hg1]
    refine Or.inl ?_
    show (_, true) ∈ zugriffe mStale _ 0
    rw [stale_zugriffe]
    exact List.mem_cons_self
  have hA := hS2 _ hwA
  refine ⟨W1, W2, hW1, ⟨sp0, _, _, _, h2⟩, hg1, ?_, ?_, ?_⟩
  · rw [hg1]; rfl
  · have e : W2.g.speicher.slots NTab.tabA = (blattM mStale 0 sA (.ret .empty List.Perm.nil)).speicher.slots NTab.tabA := hA
    rw [e]; rfl
  · rfl

open Lean Elab Tactic Meta in
/-- Case-analysis helper: find the hypothesis `X = rhs` whose left side is the left side of
    `hR` (after `cases` on a step, the constructor's `hhead`, whose name is inaccessible),
    and add `hk : rhs_of_hR = rhs`. Head predicates reduce to the same equality. -/
elab "kopf_gleich " hR:term : tactic => withMainContext do
  let hRe ← Term.elabTerm hR none
  let some (_, lhs, _) := (← instantiateMVars (← inferType hRe)).eq? | throwError "hR no eq"
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if d.toExpr == hRe then continue
    let ty ← whnf (← instantiateMVars d.type)
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
    ⟨false, [], [], .nil, .ende (.cons sA (.ret .empty List.Perm.nil))⟩ := by rfl

/-- **Determinism of G at the point `w_nicht_sc` uses**: EVERY G step of thread 0 from
    `r1M1` (after `kern` wrote `konfig := 3`) writes `tabA[0] = 3`. Inversion over all rules
    of `RufSchrittG`: every rule but `blatt`, `endeEntf`, `ruf`, `rufCallInd` needs a
    different head residue; `ruf`/`rufCallInd` need a call at the head (not a leaf), and
    `endeEntf` an unfoldable compound; `blatt` runs `execStmt` on the head statement, a
    function of the thread's world. -/
theorem g_schritt_0 {M' : RufMaschineG nD} (h : RufSchrittG nP nO 0 (r1M1 sp0) 0 M') :
    (M'.speicher.slots NTab.tabA 0 ()).n = 3 := by
  cases h
  case g7 h =>
    cases h with
    | rueckScopedWert ρ r e R hhead hret
    | rueckScopedWertDirekt ρ r e R hhead hret =>
      rcases GRest.scopedWert_faelle hret with he | ⟨rest, he⟩ | ⟨Λ', rest, k, he⟩ <;>
        subst r <;> kopf_gleich kopf0 <;> cases hk
    | rueckScopedGrund ρ r grund R hhead hret
    | rueckScopedGrundDirekt ρ r grund R hhead hret =>
      rcases GRest.scopedGrund_faelle hret with he | ⟨rest, he⟩ | ⟨Λ', rest, k, he⟩ <;>
        subst r <;> kopf_gleich kopf0 <;> cases hk
    | _ => kopf_gleich kopf0; cases hk
  all_goals rename_i h
  all_goals cases h
  all_goals (kopf_gleich kopf0)
  all_goals (try (cases hk; done))
  case ruf => exact Bool.noConfusion (congrArg kopfBlatt hk)
  case rufCallInd => exact Bool.noConfusion (congrArg kopfBlatt hk)
  case endeEntf => cases hk; cases (by assumption : GEntfaltbar sA = true)
  case endeForm => cases hk; exact absurd (by assumption : EndEntfaltbar (Endblock.cons sA (.ret .empty List.Perm.nil)) = true) (by simp only [EndEntfaltbar, Bool.false_eq_true, not_false_eq_true])
  case blatt =>
    rename_i l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein_nimmt
    cases hk
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


end SchwachZeuge
end Gabbro.Grammatik
