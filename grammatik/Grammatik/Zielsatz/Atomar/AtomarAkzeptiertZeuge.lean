/-
  Atomic-rely semantic witnesses and concrete checker refusals. The flag
  satisfies the model specification; the current contract checker refuses
  atomic reads. Sequential reasoning for hP fails under the atomic rely.
-/
module
public import Grammatik.Zielsatz.Atomar.AtomarAkzeptiert
public import Grammatik.Zielsatz.Atomar.AtomarZiel
public import Grammatik.Speichermodell.Atomar.AtomarZeuge
public import Grammatik.Speichermodell.Maschine.Zeuge
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanzZeuge
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


namespace Gabbro.Grammatik.AtomarXZeuge

open Gabbro.Grammatik Speichermodell Zielsatz NIZeuge

local instance : DecidableEq nD.Ax := inferInstanceAs (DecidableEq Empty)

/-! ## 1. The flag, covered -/

/-- The declared starts of configuration 1. -/
abbrev n1ws : List nD.Fn := [NFn.hauptA, NFn.hauptB, NFn.kern]

/-- Atomic reads are outside the current contract-checker fragment. -/
theorem n1_abgelehntX : AkzeptiertX nP SchwachZeuge.nS nFs [] nCs n1ws = false := by
  have refused : Vertraege.Pruefer.KontrakteGeprueftB nP SchwachZeuge.nS nFs = false := by decide
  change (_ && Vertraege.Pruefer.KontrakteGeprueftB nP SchwachZeuge.nS nFs) = false
  rw [refused, Bool.and_false]

theorem n1_alt_abgelehnt : Akzeptiert nP SchwachZeuge.nS nFs [] nCs n1ws = false :=
  AtomarZeuge.n1_abgelehnt

/-- Every body of `nP` returns (no call, no transition, no `forever`): no `logik` outcome. -/
theorem nP_zurueck (S : SperrInv nD) (O' : Orakel nD) (U : Umwelt nD) (A : AUmwelt nD)
    (passes : Nat) (R : ∀ f : nD.Fn, World nD → Env nD (nD.params f) → RufAusgang f)
    (f : nD.Fn) (σ : World nD) (ρ : Env nD (nD.params f)) (e : Logik nD) :
    execEndHA (V := vertragVon nD f) S O' U A passes R (nP.rumpf f) σ ρ ≠ EndAusgang.logik e := by
  cases f <;> simp only [nP, nRumpfA, nRumpfB, nRumpfKern, nKernS, nRumpfZA, nRumpfZB, nRumpfLeck, lkS, lkW, lkRet, execEndHA, execStmtHA, ne_eq, reduceCtorEq, not_false_eq_true, execBlockHA]
  split
  all_goals first | (simp only [reduceCtorEq, not_false_eq_true]; done) | (rename_i heq; split at heq <;> simp only [reduceCtorEq] at heq)

/-- **(b) with the rely on configuration 1**: no contract, no invariant, no reason, and no
    `logik` outcome whatever a shared atomic read answers. -/
theorem n1_logikA (T : nD.Tab ⊕ nD.Glob → Prop) : LogikPflichtA nP SchwachZeuge.nS (axWahr nD) T := by
  refine ⟨fun passes f => ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨(fun (L : nD.Lock) => nomatch L), axEnsLokal_wahr, ptrVerfeinert_trivial (fun f _ _ => by cases f <;> rfl) (fun _ => rfl)⟩⟩
  · intro O' _ _ _ U _ A _ R _ _ σ ρ _
    exact ⟨fun _ _ _ => rfl, fun g => nP_zurueck _ O' U A passes (torRuf nP R) f σ ρ _⟩
  · intro O' _ _ _ U _ A _ R _ _ σ ρ _ e
    exact nP_zurueck _ O' U A passes R f σ ρ e
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i
    exact (nomatch i)
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r _
    cases f <;> exact r.elim0

/-- The flag still satisfies the model's specification. This is a semantic
    witness, not an acceptance claim for the more conservative concrete checker. -/
theorem n1_specX [RootNativeFloat.Hardware] : AkzeptiertSpecX nP SchwachZeuge.nS nFs n1ws [] [] := by
  have closed := (abgAlleB_iff nFs_voll).mp (by decide : abgAlleB nP nFs = true)
  exact {
    frag := by decide
    abg := closed
    fuss := fussWXB_ok nFs_voll closed (by decide)
    stufen := (stufenB_iff nFs_voll).mp (by decide)
    sperrOrte := (sperrOrteB_iff (ls := []) (fun L => nomatch L)).mp (by decide)
    wurzeln := wurzelnB_iff.mp (by decide)
    einzeln := (einzelnPoolB_iff nFs_voll nCs_voll).mp (by decide)
    renn := (rennB_iff nFs_voll nCs_voll).mp (by decide)
    antworten := (antwortenB_iff nFs_voll).mp (by decide)
    masken := (maskenB_iff nFs_voll).mp (by decide)
    schnittstellen := (schnittstellenB_iff nFs_voll).mp (by decide)
    besitz := fun _ h => nomatch h
    worte := fun _ h => nomatch h
    bibliothek := (libraryB_iff _ _).mp (libraryB_immer _ _)
    akku := ((Kernzelle.accumulatorB_iff nFs_voll (tabsOf_voll nCs_voll)
      (globsOf_voll nCs_voll)).mp (by decide)).1
    pruef := ⟨[], (checkB_iff nFs_voll (tabsOf_voll nCs_voll)
      (globsOf_voll nCs_voll)).mp (by decide)⟩
    reset := (resetB_iff nCs_voll).mp (by decide)
    invarianten := by
      intro f passes Q shared subset
      have same : Q = axWahr nD := by funext a; exact nomatch a
      rw [same]
      exact ((n1_logikA shared).1 passes f).2
    kontrakte := by
      intro f passes Q shared subset
      have same : Q = axWahr nD := by funext a; exact nomatch a
      rw [same]
      exact (n1_logikA shared).1 passes f }

/-- **THE FLAG, COVERED**: at every machine W reaches from configuration 1 -- every order
    assignment, budget, start memory -- every leg of `ZielAtomar`. -/
theorem n1_ziel_atomar [RootNativeFloat.Hardware] (sp : Speicher nD) (ord : nD.Glob → Ordnung) (passes : Nat) :
    ∀ W : RufMaschineW nD, RufErreichbarW nP nO passes ord (RufStartW (RufStartG nP sp init1)) W →
      ZielAtomar nP SchwachZeuge.nS nO passes ord (GeteiltV nP n1ws) (RufStartG nP sp init1) W :=
  ziel_atomar_spec nP SchwachZeuge.nS (axWahr nD) nFs_voll (ls := []) (fun L => nomatch L) n1ws
    n1_specX
    (n1_logikA _) nO ⟨nO_gut, nO_lokal, axVertragO_wahr nO, inferInstance⟩ passes ord sp init1
    (AtomarZeuge.n1_start sp)

/-- **Non-degenerate: `konfig` is an admitted shared atomic** -- atomic, unguarded, read by
    `hauptA`'s footprint while `kern` writes it, in no contract. -/
theorem n1_konfig_geteilt : GeteiltV nP n1ws (.inr NGlob.konfig) := by
  refine ⟨⟨⟨_, rfl, rfl⟩, ⟨(fun (L : nD.Lock) _ => nomatch L), fun h => ?_⟩⟩, fun g => ?_, fun i _ => ?_⟩
  · have := h NFn.hauptA List.mem_cons_self NFn.kern
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      (Or.inl (fun e => by cases e)) NFn.hauptA NFn.kern .wurzel (istIn_iff.mp (by decide)) .wurzel
    exact Bool.noConfusion this
  · cases g <;> exact ⟨List.not_mem_nil, List.not_mem_nil, List.not_mem_nil⟩
  · cases i

/-- **Non-degenerate: W's stale read happens on a covered run.** After `kern` wrote
    `konfig := 3`, W lets `hauptA` store the INITIAL `konfig` (0) into `tabA[0]`, where G on the
    same schedule stores 3; the machine after that step satisfies every leg of `ZielAtomar`. -/
theorem n1_stale_gedeckt [RootNativeFloat.Hardware] (ord : nD.Glob → Ordnung) :
    ∃ W1 W2 : RufMaschineW nD,
      RufErreichbarW nP nO 0 ord (RufStartW (RufStartG nP sp0 init1)) W1 ∧
      RufSchrittW nP nO 0 ord W1 0 W2 ∧
      (W1.g.speicher.globs NGlob.konfig).n = 3 ∧ (W2.g.speicher.slots NTab.tabA 0 ()).n = 0 ∧
      ((r1M2 sp0).speicher.slots NTab.tabA 0 ()).n = 3 ∧
      ZielAtomar nP SchwachZeuge.nS nO 0 ord (GeteiltV nP n1ws) (RufStartG nP sp0 init1) W2 := by
  obtain ⟨W1, W2, hW1, hs, _, hk, hA, hG⟩ := SchwachZeuge.w_nicht_sc ord
  exact ⟨W1, W2, hW1, hs, hk, hA, hG, n1_ziel_atomar sp0 ord 0 W2 (.schritt _ _ _ hW1 hs)⟩

/-! ## 2. The rely bites -/

/-- The test `konfig == tabB[0]`. -/
def hC : Expr nD [] [] .bool := .eq (.glob NGlob.konfig (nGd _ _)) (.slot NTab.tabB () nI0 (nDarf _ _))

/-- `tabB[0] = konfig`. -/
def hLies : Stmt nD (vertragVon nD NFn.zaehlB) false [] [] [] :=
  .assignSlot NTab.tabB () nI0 (.glob NGlob.konfig (nGd _ _)) rfl (nDarf _ _)

/-- `tabB[0] = k`. -/
def hSetze (k : Int) (h0 : (0 : Int) ≤ k) (h9 : k ≤ 9) : Stmt nD (vertragVon nD NFn.zaehlB) false [] [] [] :=
  .assignSlot NTab.tabB () nI0 (nW k h0 h9) rfl (nDarf _ _)

/-- `if konfig == tabB[0] { tabB[0] = 1 } else { tabB[0] = 2 }`. -/
def hTest : Stmt nD (vertragVon nD NFn.zaehlB) false [] [] [] :=
  .ite hC (.cons (hSetze 1 (by decide) (by decide)) .nil) (.cons (hSetze 2 (by decide) (by decide)) .nil)

/-- The body of `zaehlB` in `hP`: read `konfig`, then test it again. -/
def hRumpf : Endblock nD (vertragVon nD NFn.zaehlB) false [] [] :=
  .cons hLies (.cons hTest (.ret .empty List.Perm.nil))

/-- `zaehlB` ensures `tabB[0] == 1`. -/
def hEns : Expr nD (ErgCtx (nD.params NFn.zaehlB) (nD.erg NFn.zaehlB)) (vertragVon nD NFn.zaehlB).ende
    .bool :=
  .eq (.slot NTab.tabB () nI0 (nDarf _ _)) (nW 1 (by decide) (by decide))

/-- **The program `hP`**: `nP` with `zaehlB := hRumpf` and its contract `tabB[0] == 1`. -/
def hP : Programm nD where
  invariante := fun i => (nomatch i)
  requires := fun _ => .tru
  ensures
    | .hauptA => .tru
    | .hauptB => .tru
    | .kern => .tru
    | .ruhe => .tru
    | .zaehlA => .tru
    | .zaehlB => hEns
    | .leck => .tru
  rumpf
    | .hauptA => nRumpfA
    | .hauptB => nRumpfB
    | .kern => nRumpfKern
    | .ruhe => .ret .empty List.Perm.nil
    | .zaehlA => nRumpfZA
    | .zaehlB => hRumpf
    | .leck => nRumpfLeck

/-- `kern` writes `konfig`, `zaehlB` reads it. -/
abbrev hws : List nD.Fn := [NFn.kern, NFn.zaehlB]

/-- Refused by the sequential checker because of the unguarded shared read. -/
theorem hP_alt_abgelehnt : Akzeptiert hP SchwachZeuge.nS nFs [] nCs hws = false := by decide

theorem hP_konfig_geteilt : GeteiltA hP hws (.inr NGlob.konfig) := by
  refine ⟨⟨_, rfl, rfl⟩, ⟨(fun (L : nD.Lock) _ => nomatch L), fun h => ?_⟩⟩
  have := h NFn.zaehlB (List.mem_cons_of_mem _ List.mem_cons_self) NFn.kern List.mem_cons_self
    (Or.inl (fun e => by cases e)) NFn.zaehlB NFn.kern .wurzel (istIn_iff.mp (by decide)) .wurzel
  exact Bool.noConfusion this

/-- The value of `tabB[0]` after a normal return (`-1` otherwise). -/
def tabBNach {V : Vertrag nD} {l : Bool} {Γ : Ctx} : EndAusgang V l Γ → Int
  | .zurueck σ' _ => (σ'.slots NTab.tabB 0 ()).n
  | _ => -1

/-- **Sequentially, the body meets its contract**: the second read of `konfig` sees the value
    the first one stored, so the test holds and the body writes 1. -/
theorem hP_seq_wert (S : SperrInv nD) (O' : Orakel nD) (U : Umwelt nD) (passes : Nat)
    (R : ∀ f : nD.Fn, World nD → Env nD (nD.params f) → RufAusgang f) (σ : World nD)
    (ρ : Env nD (nD.params NFn.zaehlB)) :
    tabBNach (execEndH (V := vertragVon nD NFn.zaehlB) S O' U passes R hRumpf σ ρ) = 1 := by
  simp only [hRumpf, hLies, hTest, execEndH, execStmtH, execBlockH]
  split <;> rename_i heq <;> split at heq <;> rename_i hc
  all_goals first
    | exact (hc (decide_eq_true rfl)).elim
    | (simp only [hSetze, execStmtH] at heq <;> cases heq <;> rfl)

/-- The body always returns (both engines, every environment). -/
theorem hRumpf_zurueckA (S : SperrInv nD) (O' : Orakel nD) (U : Umwelt nD) (A : AUmwelt nD)
    (passes : Nat) (R : ∀ f : nD.Fn, World nD → Env nD (nD.params f) → RufAusgang f)
    (σ : World nD) (ρ : Env nD (nD.params NFn.zaehlB)) :
    ∃ σ' v, execEndHA (V := vertragVon nD NFn.zaehlB) S O' U A passes R hRumpf σ ρ =
      EndAusgang.zurueck σ' v := by
  simp only [hRumpf, hLies, hTest, execEndHA, execStmtHA, execBlockHA]
  split <;> rename_i heq <;> split at heq <;>
    (simp only [hSetze, execStmtHA] at heq <;> cases heq <;> exact ⟨_, _, rfl⟩)

theorem hRumpf_zurueck (S : SperrInv nD) (O' : Orakel nD) (U : Umwelt nD) (passes : Nat)
    (R : ∀ f : nD.Fn, World nD → Env nD (nD.params f) → RufAusgang f)
    (σ : World nD) (ρ : Env nD (nD.params NFn.zaehlB)) :
    ∃ σ' v, execEndH (V := vertragVon nD NFn.zaehlB) S O' U passes R hRumpf σ ρ =
      EndAusgang.zurueck σ' v := by
  simp only [hRumpf, hLies, hTest, execEndH, execStmtH, execBlockH]
  split <;> rename_i heq <;> split at heq <;>
    (simp only [hSetze, execStmtH] at heq <;> cases heq <;> exact ⟨_, _, rfl⟩)

theorem hP_seq (passes : Nat) :
    KoerperGutS hP passes (axWahr nD) SchwachZeuge.nS NFn.zaehlB := by
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v h => ?_, fun g h => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e h => ?_⟩
  · have h1 := hP_seq_wert SchwachZeuge.nS O' U passes R σ ρ
    change execEndH _ _ _ _ _ hRumpf σ ρ = _ at h
    rw [h] at h1
    show decide ((σ'.slots NTab.tabB 0 ()).n = 1) = true
    exact decide_eq_true h1
  · obtain ⟨σ', v, h'⟩ := hRumpf_zurueck SchwachZeuge.nS O' U passes (torRuf hP R) σ ρ
    change execEndH _ _ _ _ _ hRumpf σ ρ = _ at h
    rw [h'] at h
    cases h
  · obtain ⟨σ', v, h'⟩ := hRumpf_zurueck SchwachZeuge.nS O' U passes R σ ρ
    change execEndH _ _ _ _ _ hRumpf σ ρ = _ at h
    rw [h'] at h
    cases h

/-- The environment that answers the TEST's read of `konfig` with 5 (another thread wrote it
    between the two reads); every other read unchanged. -/
def aFuenf : AUmwelt nD := fun X σ =>
  if X = hC.orte then σ.storeGlob NGlob.konfig (⟨5, by decide, by decide⟩ : Zahl 0 9) else σ

theorem aFuenf_havoc : HavocA (GeteiltA hP hws) aFuenf := by
  intro X σ
  unfold aFuenf
  split
  · rename_i hX
    refine ⟨rfl, fun c hc => ?_⟩
    cases c with
    | inl t => rfl
    | inr g =>
        cases g with
        | konfig =>
            exact absurd ⟨by rw [hX]; exact List.mem_cons_self, hP_konfig_geteilt⟩ hc
        | zaehler => rfl
  · exact ⟨rfl, fun c _ => traegerGleich_refl _ c⟩

/-- **With the rely, the body breaks its contract**: from the all-zero memory, the first read
    stores 0, the test reads 5, the body writes 2. -/
theorem hP_wert_A (S : SperrInv nD) (O' : Orakel nD) (U : Umwelt nD) (passes : Nat)
    (R : ∀ f : nD.Fn, World nD → Env nD (nD.params f) → RufAusgang f) :
    tabBNach (execEndHA (V := vertragVon nD NFn.zaehlB) S O' U aFuenf passes R hRumpf
      (sp0.welt []) .nil) = 2 := by
  simp only [hRumpf, hLies, hTest, execEndHA, execStmtHA, execBlockHA]
  split <;> rename_i heq <;> split at heq <;> rename_i hc
  all_goals first
    | exact absurd hc (by decide)
    | (simp only [hSetze, execStmtHA] at heq <;> cases heq <;> rfl)

/-- **THE RELY BITES**: the obligation with the rely fails for `zaehlB`, though the sequential
    one holds (`hP_seq`). -/
theorem hP_rely_nicht :
    ¬ KoerperGutSA hP 0 (axWahr nD) SchwachZeuge.nS (GeteiltA hP hws) NFn.zaehlB := by
  intro h
  let R : ∀ f : nD.Fn, World nD → Env nD (nD.params f) → RufAusgang f :=
    fun _ _ _ => .hardware .ieee
  have hR : RespektiertRahmen hP R := ⟨fun _ _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ h => (by cases h)⟩
  have hOV : OhneVorbedingung R := fun _ _ _ _ h => by cases h
  have hU : HavocOk SchwachZeuge.nS (fun _ σ => σ) := fun L => (nomatch L)
  have hE := (h.1 nO (gutO_rahmenO nO_gut) nO_lokal (axVertragOP_of_O _ (axVertragO_wahr nO)) (fun _ σ => σ) hU aFuenf
    aFuenf_havoc R hR hOV (sp0.welt []) .nil rfl).1
  obtain ⟨σ', v, hr⟩ := hRumpf_zurueckA SchwachZeuge.nS nO (fun _ σ => σ) aFuenf 0 R (sp0.welt []) .nil
  have h2 := hP_wert_A SchwachZeuge.nS nO (fun _ σ => σ) 0 R
  rw [hr] at h2
  have h1 := hE σ' v hr
  change decide ((σ'.slots NTab.tabB 0 ()).n = 1) = true at h1
  have := of_decide_eq_true h1
  change (σ'.slots NTab.tabB 0 ()).n = 2 at h2
  omega

/-- So `hP`'s user obligation with the rely FAILS: the goal over GX does not cover it. -/
theorem hP_logikA_nicht : ¬ LogikPflichtA hP SchwachZeuge.nS (axWahr nD) (GeteiltA hP hws) :=
  fun h => hP_rely_nicht (h.1 0 NFn.zaehlB).1

/-- The strengthened checker refuses the body whose contract fails under the
    atomic rely. The refusal follows from soundness, independently of evaluation. -/
theorem hP_abgelehntX : AkzeptiertX hP SchwachZeuge.nS nFs [] nCs hws = false := by
  cases accepted : AkzeptiertX hP SchwachZeuge.nS nFs [] nCs hws with
  | false => rfl
  | true =>
      have contract : Vertraege.Pruefer.KontrakteGeprueftB hP SchwachZeuge.nS nFs = true :=
        (Bool.and_eq_true.mp accepted).2
      have checked := Vertraege.Pruefer.KontrakteGeprueftB_sound nFs_voll contract NFn.zaehlB
      exact False.elim (hP_rely_nicht
        (checked 0 (axWahr nD) (GeteiltA hP hws) (fun _ shared => shared.1)).1)

/-- Sequential reasoning holds at every budget, but fails under the rely;
    the full checker therefore refuses this program. -/
theorem hP_havoc_bites :
    AkzeptiertX hP SchwachZeuge.nS nFs [] nCs hws = false ∧
      (∀ passes, KoerperGutS hP passes (axWahr nD) SchwachZeuge.nS NFn.zaehlB) ∧
      ¬ KoerperGutSA hP 0 (axWahr nD) SchwachZeuge.nS (GeteiltA hP hws) NFn.zaehlB :=
  ⟨hP_abgelehntX, hP_seq, hP_rely_nicht⟩

/-! ## 3. The refusal: a contract over a shared atomic -/

/-- `kern` ensures `konfig == 3`. -/
def vEns : Expr nD (ErgCtx (nD.params NFn.kern) (nD.erg NFn.kern)) (vertragVon nD NFn.kern).ende .bool :=
  .eq (.glob NGlob.konfig (nGd _ _)) (nW 3 (by decide) (by decide))

/-- `nP` with `kern`'s contract `konfig == 3`. -/
def vP : Programm nD where
  invariante := fun i => (nomatch i)
  requires := fun _ => .tru
  ensures
    | .hauptA => .tru
    | .hauptB => .tru
    | .kern => vEns
    | .ruhe => .tru
    | .zaehlA => .tru
    | .zaehlB => .tru
    | .leck => .tru
  rumpf := nP.rumpf

/-- **THE REFUSAL**: on configuration 1 with a contract over the shared `konfig`, `AkzeptiertX`
    refuses at its footprint component, where `AkzeptiertA` (no contract condition) accepts. -/
theorem vertrag_atomar_abgelehnt :
    AkzeptiertX vP SchwachZeuge.nS nFs [] nCs n1ws = false ∧
      fussWXB vP SchwachZeuge.nS nFs n1ws = false ∧
      AkzeptiertA vP SchwachZeuge.nS nFs [] nCs n1ws = true := by
  decide

/-- Non-degenerate: `konfig` is in `kern`'s contract, and shared (as in configuration 1). -/
theorem vertrag_atomar_echt :
    (.inr NGlob.konfig : nD.Tab ⊕ nD.Glob) ∈ (vP.ensures NFn.kern).orte ∧
      ¬ VertragsFrei vP (.inr NGlob.konfig) :=
  ⟨List.mem_cons_self, fun h => (h.1 NFn.kern).2.1 List.mem_cons_self⟩

#print axioms n1_ziel_atomar
#print axioms n1_konfig_geteilt
#print axioms n1_stale_gedeckt
#print axioms hP_havoc_bites
#print axioms hP_logikA_nicht
#print axioms vertrag_atomar_abgelehnt

/-! ## 4. The goal with shared atomics, applied -/

/-- **Configuration 1 as a unit**: `hauptA`, `hauptB`, `kern` declared, all-zero memory. -/
def n1E : Einheit nD where
  P := nP
  S := SchwachZeuge.nS
  Q := axWahr nD
  starts := [⟨NFn.hauptA, .nil⟩, ⟨NFn.hauptB, .nil⟩, ⟨NFn.kern, .nil⟩]
  sp0 := sp0

/-- The old flag unit is refused; its atomic reads are outside the checked fragment. -/
theorem n1E_abgelehnt : akzeptiertX_pruefer.akzeptiert n1E nFs [] nCs = false := by
  change (AkzeptiertX nP SchwachZeuge.nS nFs [] nCs n1ws && besitzB n1E nFs &&
    Kernzelle.akkuStartB n1E [] && invariantenGeprueftB n1E nFs [] &&
    nutzerPflichtGeprueftB n1E nFs []) = false
  rw [n1_abgelehntX]
  rfl

theorem n1E_ws : n1E.ws = n1ws := by rfl


/-- (b) with the rely, bodies and start. -/
theorem n1E_nutzerPflichtA : NutzerPflichtA n1E :=
  ⟨n1_logikA _, ⟨(fun L => nomatch L), fun _ _ => rfl⟩⟩


/-! ## 5. The per-core fold (OFFEN O17) -/

/-- The fold is also refused by the current atomic-read contract gate. -/
theorem faltung_abgelehntX :
    AkzeptiertX nP SchwachZeuge.nS nFs [] nCs [NFn.zaehlA, NFn.zaehlA, NFn.zaehlB] = false := by
  have refused : Vertraege.Pruefer.KontrakteGeprueftB nP SchwachZeuge.nS nFs = false := by decide
  change (_ && Vertraege.Pruefer.KontrakteGeprueftB nP SchwachZeuge.nS nFs) = false
  rw [refused, Bool.and_false]

#print axioms faltung_abgelehntX

end Gabbro.Grammatik.AtomarXZeuge
