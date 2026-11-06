module

public import Grammatik.Zielsatz.Kern.Proben
public import Grammatik.Korpus.Programme.Korpus124.Teil1
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
namespace K124

/-- `hauptB`: the caller duty from the lock invariant at the acquire; the
    release check from `setze`'s `ensures`. -/
theorem kP_koerper_B : KoerperGutS kP 0 (axWahr kD) kSI kHauptB := by
  have hr : kP.rumpf kHauptB = kRumpfB := rfl
  refine ⟨fun O' _ _ _ U hU R hR hOV σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U hU R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    obtain ⟨σ2, e2⟩ := kB_schreib (S := kSI) (O := O') (U := U) (passes := 0)
      (R := torRuf kP R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, kLocksB] at hrun
    erw [execStmtH_locks_eins] at hrun
    have hreq : ReqAmEintritt kP kSetze (((U () σ2).nimmt ()).lese kL [])
        (evalArgs (((U () σ2).nimmt ()).lese kL []) (Args.cons (Λ := kL) (Γ := []) k70 .nil)
          (((U () σ2).nimmt ()).lese kL []) ρ) := (hU () σ2).2.2
    rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := torRuf kP R)
      (l := false) (Γ := []) kSetze (.cons k70 .nil) kHpSetzeB rfl ((U () σ2).nimmt ()) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · cases hi : kSI.inv () σ1.speicher with
      | false => simp only [freiH, hi, Bool.false_eq_true, if_false] at hrun; cases hrun
      | true => simp only [freiH, hi, if_true] at hrun; cases hrun
    · simp only [freiH] at hrun
      cases hrun
      have htor : torRuf kP R kSetze _ _ = R kSetze _ _ := if_pos hreq
      exact hOV _ _ _ _ (htor.symm.trans he1) g rfl
    · simp only [freiH] at hrun; cases hrun
  · rw [hr] at hrun
    obtain ⟨σ2, e2⟩ := kB_schreib (S := kSI) (O := O') (U := U) (passes := 0) (R := R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, kLocksB] at hrun
    erw [execStmtH_locks_eins] at hrun
    have hreq : ReqAmEintritt kP kSetze (((U () σ2).nimmt ()).lese kL [])
        (evalArgs (((U () σ2).nimmt ()).lese kL []) (Args.cons (Λ := kL) (Γ := []) k70 .nil)
          (((U () σ2).nimmt ()).lese kL []) ρ) := (hU () σ2).2.2
    rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := R)
      (l := false) (Γ := []) kSetze (.cons k70 .nil) kHpSetzeB rfl ((U () σ2).nimmt ()) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hinv := kInv_of_ens (hR.1 _ _ _ hreq σ1 v1 hR1)
      simp only [freiH, hinv, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOL _ _ _ _ he1
    · simp only [freiH] at hrun; cases hrun

theorem kP_koerper_setze : KoerperGutS kP 0 (axWahr kD) kSI kSetze := by
  have hr : kP.rumpf kSetze = kRumpfSetze := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [kRumpfSetze, execEndH, execStmtH] at hrun
    cases hrun
    cases ρ with
    | cons x rest =>
      cases rest
      show wahr? (eval σ (kP.ensures kSetze) _ (ergEnv (kD.erg kSetze) () (Env.cons x Env.nil))) = true
      simp only [wahr?, kSetze, kP, kGleich, kI0, Int.reduceSub, kI1, World.lese, World.merke, World.schreibSlot,
  World.storeSlot, List.map_append, List.append_assoc, eval, Zahl.weiter, List.cons_append, List.nil_append, ergEnv,
  Int.reduceEq, ↓reduceIte, dite_eq_ite, ite_self, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨rfl, rfl⟩
  · rw [hr] at hrun
    simp only [kRumpfSetze, execEndH, execStmtH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [kRumpfSetze, execEndH, execStmtH] at hrun
    cases hrun

/-- `pruefeA`: its `requires privA[0] == 7` is its `ensures result == 7`. -/
theorem kP_koerper_P : KoerperGutS kP 0 (axWahr kD) kSI kPruefeA := by
  have hr : kP.rumpf kPruefeA = kRumpfP := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ hreq => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [kRumpfP] at hrun
    cases hrun
    have h7 : (σ.slots KTab.privA 0 ()).n = 7 := by
      have hq : decide ((σ.slots KTab.privA 0 ()).n = 7) = true := hreq
      exact of_decide_eq_true hq
    exact decide_eq_true h7
  · rw [hr] at hrun
    simp only [kRumpfP, execEndH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [kRumpfP, execEndH] at hrun
    cases hrun

theorem kP_koerper : ∀ f : kD.Fn, KoerperGutS kP 0 (axWahr kD) kSI f := by
  intro f
  cases f
  · exact kP_koerper_setze
  · exact kP_koerper_A
  · exact kP_koerper_B
  · exact kP_koerper_P

theorem kP_inv : ∀ f : kD.Fn, InvGutS kP 0 (axWahr kD) kSI f :=
  fun _ => invGutS_ohne fun i _ => (nomatch i)

theorem kP_ohneEwig : ohneEwigB kP kFs = true := by decide

theorem kP_koerper_alle : ∀ (passes : Nat) (f : kD.Fn), KoerperGutS kP passes (axWahr kD) kSI f :=
  koerperGutS_alle kFs_voll kP_ohneEwig kP_koerper

theorem kP_inv_alle : ∀ (passes : Nat) (f : kD.Fn), InvGutS kP passes (axWahr kD) kSI f :=
  invGutS_alle kFs_voll kP_ohneEwig kP_inv

/-! ## 4. The program as one declaration, and every premise group -/

/-- The start memory: every slot zero (the emitted statics are zero-initialised). -/
def kSp : Speicher kD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- **`beispiele/124` as ONE declaration**: code `kP`, lock invariant `kSI`,
    no axiom, declared starts `hauptA` and `hauptB` (no parameters), initial
    memory all zero. -/
def kE : Zielsatz.Einheit kD where
  P := kP
  S := kSI
  Q := axWahr kD
  starts := [⟨kHauptA, .nil⟩, ⟨kHauptB, .nil⟩]
  sp0 := kSp
  gestartet := []
  arenen := []
  akku := []
  pruefungen := []
  grants0 := []

/-- Every admitted pointer uses its target's actual pre/post contract. The
    nontrivial requirements of `setze` and `pruefeA` are retained, not proved
    unconditionally from the old trivial interface. -/
private theorem corpus_pointer_contracts : PtrVerfeinert kP := by
  intro f n hf
  have signature : kSigOf f = n := by
    change decide (kSigOf f = n) = true at hf
    exact of_decide_eq_true hf
  subst n
  cases f <;> constructor
  all_goals first
    | (intro entry arguments accepted; exact accepted)
    | (intro entry current arguments value _ returned; exact returned)

theorem kE_nutzerPflicht : Zielsatz.NutzerPflicht kE :=
  ⟨⟨fun passes f => ⟨kP_koerper_alle passes f, kP_inv_alle passes f,
      invGutGrund_ohneGrund (by cases f <;> rfl)⟩, kSI_ok.2, axEnsLokal_wahr, corpus_pointer_contracts⟩,
    ⟨fun L => by cases L; decide, fun a ha => by
      simp only [kE, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> rfl⟩⟩

/-- No axiom, no register, no global: the oracle is empty. -/
def kO : Orakel kD where
  wirkt := fun a => (nomatch a)
  regLies := fun r => (nomatch r)
  regSchreib := fun r _ => (nomatch r)
  sichtbar := fun g => (nomatch g)

theorem kO_gut : GutO kO := fun a => (nomatch a)

theorem kO_lokal : RegLokal kO := ⟨(fun r _ _ _ => nomatch r), (fun g _ _ _ => nomatch g)⟩

theorem kO_hw [RootNativeFloat.Hardware] : Zielsatz.HardwareAnnahmen kO kE.Q :=
  ⟨kO_gut, kO_lokal, axVertragO_wahr kO, inferInstance⟩

theorem kE_akzeptiert : akzeptiert_pruefer.akzeptiert kE kFs [()] kCs = true := by
  rw [akzeptiert_pruefer_eq]
  exact kP_akzeptiert

/-- **The goal theorem on `beispiele/124`**: for every oracle meeting (c), every
    budget, every runtime start meeting (d), and every reachable machine of
    `kP.mitRuhe`, the conclusion `Ziel` holds -- `gabbro_ziel` with the
    concrete checker. -/
theorem k124_ziel (O : Orakel kD) (hO : Zielsatz.HardwareAnnahmen O kE.Q) (passes : Nat)
    (sp : Speicher kD.mitRuhe)
    (init : Faden → Σ f : kD.mitRuhe.Fn, Env kD.mitRuhe (kD.mitRuhe.params f))
    (hL : Zielsatz.Laufzeit kE sp init) (M : RufMaschineG kD.mitRuhe)
    (hM : RufErreichbarG kE.P.mitRuhe O.mitRuhe passes (RufStartG kE.P.mitRuhe sp init) M) :
    Zielsatz.Ziel kE.P.mitRuhe kE.S.mitRuhe O.mitRuhe passes (RufStartG kE.P.mitRuhe sp init) M :=
  Zielsatz.gabbro_ziel_g akzeptiert_pruefer kD kE ⟨kFs, kFs_voll⟩ ⟨[()], kLocks_voll⟩ ⟨kCs, kCs_voll⟩
    kE_akzeptiert kE_nutzerPflicht O hO passes sp init hL M hM

end K124

#print axioms K124.kP_akzeptiert
#print axioms K124.kE_nutzerPflicht
#print axioms K124.k124_ziel

end Gabbro.Grammatik
