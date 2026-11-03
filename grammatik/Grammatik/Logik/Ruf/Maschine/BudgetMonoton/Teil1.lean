module
public import Grammatik.Logik.Ruf.Maschine.BudgetMonoton.Teil1Basis
import all Grammatik.Logik.Ruf.Maschine.BudgetMonoton.Teil1Basis

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG
public import Grammatik.Speichermodell.Maschine.GXMaschine

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

private theorem plus_weiterOpt (j : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (e : Option Ty) (k : GRest D V l Γ Λ) :
    (GRest.weiterOpt (Λ := Λ) e k).plus j = GRest.weiterOpt (Λ := Λ) e (k.plus j) := by
  cases e <;> rfl

theorem rufSchrittG_plus {P : Programm D} {O : Orakel D} {p : Nat} (j : Nat) {M M' : RufMaschineG D}
    {f : Faden} (h : RufSchrittG P O p M f M') : RufSchrittG P O (p + j) (M.plus j) f (M'.plus j) := by
  cases h with
  | g1 h =>
    cases h with
    | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein_nimmt =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.blatt (passes := p + j) (M.plus j) f l Γ Λ Λ' s rest ρ hleaf (RufRahmenG.plus_rest hhead) hΛ σ' ρ' neu ((execStmt_blatt_passes O p (p + j) keinRuf s hleaf _ _).symm.trans hstep) hneu hkein_nimmt
    | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.ruf (passes := p + j) (M.plus j) f l Γ Λ g args hp hr rest ρ (RufRahmenG.plus_rest hhead) hΛ s0 hs0 rho hrho neu hneu
    | rueck caller rest hpop Γ Λ e hperm ρ hAnon8 g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.rueck (passes := p + j) (M.plus j) f (caller.plus j) (rest.map (RufRahmenG.plus j)) (congrArg (List.map (RufRahmenG.plus j)) hpop) Γ Λ e hperm ρ (RufRahmenG.plus_rest hAnon8) g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu (by rw [RufRahmenG.plus_wartend]; exact hnw)
    | endeEntf l Γ Λ Λ' s rest ρ hent hhead =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.endeEntf (passes := p + j) (M.plus j) f l Γ Λ Λ' s rest ρ hent (RufRahmenG.plus_rest hhead)
    | endeForm l Γ Λ e ρ hl hent hhead =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.endeForm (passes := p + j) (M.plus j) f l Γ Λ e ρ hl hent (RufRahmenG.plus_rest hhead)
    | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein_nimmt =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannBlatt (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' s rest (k.plus j) ρ hleaf (RufRahmenG.plus_rest hhead) hΛ σ' ρ' neu ((execStmt_blatt_passes O p (p + j) keinRuf s hleaf _ _).symm.trans hstep) hneu hkein_nimmt
    | dannLeer l Γ Λ k ρ hhead =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannLeer (passes := p + j) (M.plus j) f l Γ Λ (k.plus j) ρ (RufRahmenG.plus_rest hhead)
    | dannIteWahr l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannIteWahr (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' c t e rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ hw neu hneu hΛ
    | dannIteFalsch l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannIteFalsch (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' c t e rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ hw neu hneu hΛ
    | dannOnOptionSome l Γ Λ Λ' Λ'' n o pB a rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannOnOptionSome (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' n o pB a rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ v hv neu hneu hΛ
    | dannOnOptionNone l Γ Λ Λ' Λ'' n o pB a rest k ρ hhead σ₁ hs₁ hv neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannOnOptionNone (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' n o pB a rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ hv neu hneu hΛ
    | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ τ b nutz hw neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannOnTagSome (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' cs v arms rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ τ b nutz hw neu hneu hΛ
    | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannOnTagNone (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' cs v arms rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ b nutz hw neu hneu hΛ
    | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannOnGrund (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' n r arms rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ b hw neu hneu hΛ
    | endeBind l Γ Λ τ e rest ρ hhead σ₁ hs₁ neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.endeBind (passes := p + j) (M.plus j) f l Γ Λ τ e rest ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ neu hneu hΛ
    | endeBindAxiom l Γ Λ τ a args he hw hg hd hgd rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.endeBindAxiom (passes := p + j) (M.plus j) f l Γ Λ τ a args he hw hg hd hgd rest ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ σ₂ v hax neu hneu hΛ
    | endeBindAxiomOpt l Γ Λ e a args he hp hd hgd rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.endeBindAxiomOpt (passes := p + j) (M.plus j) f l Γ Λ e a args he hp hd hgd rest ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ σ₂ v hax neu hneu hΛ
    | dannBind l Γ Λ Λ' Λ'' τ e rest k ρ hhead σ₁ hs₁ neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannBind (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' τ e rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ neu hneu hΛ
    | dannNarrowOk l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannNarrowOk (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ h neu hneu hΛ
  | g2 h =>
    cases h with
    | dannNarrowElse l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannNarrowElse (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ h neu hneu hΛ
    | dannPruefWahr l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannPruefWahr (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' c sonst rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ hw neu hneu hΛ
    | dannPruefFalsch l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannPruefFalsch (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' c sonst rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ hw neu hneu hΛ
    | dannBreaking l Γ Λ Λ' Λ'' i body rest k ρ hhead =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannBreaking (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' i body rest (k.plus j) ρ (RufRahmenG.plus_rest hhead)
    | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannLocks (passes := p + j) (M.plus j) f l Γ Λ Λ'' L hr body rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) hself hrang hfrei
    | freiGib l Γ Λ L k ρ hhead =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.freiGib (passes := p + j) (M.plus j) f l Γ Λ L (k.plus j) ρ (RufRahmenG.plus_rest hhead)
    | schrumpfVergiss l Γ Λ τ k v ρ hhead =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.schrumpfVergiss (passes := p + j) (M.plus j) f l Γ Λ τ (k.plus j) v ρ (RufRahmenG.plus_rest hhead)
    | dannTrav l Γ Λ Λ'' t inv body rest k ρ hhead =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannTrav (passes := p + j) (M.plus j) f l Γ Λ Λ'' t inv body rest (k.plus j) ρ (RufRahmenG.plus_rest hhead)
    | travNext l Γ Λ t inv body i is k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.travNext (passes := p + j) (M.plus j) f l Γ Λ t inv body i is (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ hw neu hneu hΛ
    | travFort l Γ Λ t inv body is k i ρ hhead =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.travFort (passes := p + j) (M.plus j) f l Γ Λ t inv body is (k.plus j) i ρ (RufRahmenG.plus_rest hhead)
    | travDone l Γ Λ t inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.travDone (passes := p + j) (M.plus j) f l Γ Λ t inv body (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ hw neu hneu hΛ
    | dannRetry l Γ Λ Λ' Λ'' n bis body ueber rest k ρ hhead =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannRetry (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' n bis body ueber rest (k.plus j) ρ (RufRahmenG.plus_rest hhead)
    | wiederUeber l Γ Λ bis body ueber k ρ hhead =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.wiederUeber (passes := p + j) (M.plus j) f l Γ Λ bis body ueber (k.plus j) ρ (RufRahmenG.plus_rest hhead)
    | wiederWeiter l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.wiederWeiter (passes := p + j) (M.plus j) f l Γ Λ n bis body ueber (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ hw neu hneu hΛ
    | wiederSchritt l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.wiederSchritt (passes := p + j) (M.plus j) f l Γ Λ n bis body ueber (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ hw neu hneu hΛ
    | wiederFort l Γ Λ n bis body ueber k ρ hhead =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.wiederFort (passes := p + j) (M.plus j) f l Γ Λ n bis body ueber (k.plus j) ρ (RufRahmenG.plus_rest hhead)
    | dannForever l Γ Λ Λ' Λ'' a inv body rest k ρ hhead =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannForever (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' a inv body rest (k.plus j) ρ (RufRahmenG.plus_rest hhead)
    | ewigWeiter l Γ Λ a n inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.ewigWeiter (passes := p + j) (M.plus j) f l Γ Λ a (n + j) inv body (k.plus j) ρ (by have h := RufRahmenG.plus_rest (j := j) hhead; simp only [GRest.plus] at h; rwa [show n + 1 + j = n + j + 1 by omega] at h) σ₁ hs₁ hw neu hneu hΛ
    | ewigFort l Γ Λ a n inv body k ρ hhead =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.ewigFort (passes := p + j) (M.plus j) f l Γ Λ a (n + j) inv body (k.plus j) ρ (RufRahmenG.plus_rest hhead)
    | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.rufDann (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' g args hp hr rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) hΛ s0 hs0 rho hrho neu hneu
  | g3 h =>
    cases h with
    | dannCallInd l Γ Λ Λ' Λ'' n pB args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannCallInd (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' n pB args hp hr rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) hΛ s0 hs0 g hg hv rho hrho neu hneu
    | rufCallInd l Γ Λ n pB args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.rufCallInd (passes := p + j) (M.plus j) f l Γ Λ n pB args hp hr rest ρ (RufRahmenG.plus_rest hhead) hΛ s0 hs0 g hg hv rho hrho neu hneu
    | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannBindCall (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' τ g args he hp hr rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) hΛ s0 hs0 rho hrho neu hneu
    | dannBindCallInd l Γ Λ Λ' Λ'' τ n pB args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannBindCallInd (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' τ n pB args he hp hr rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) hΛ s0 hs0 g hg hv rho hrho neu hneu
    | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannBindCallElse (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' τ g args he hp hr err rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) hΛ s0 hs0 rho hrho neu hneu
    | dannAxiomCallElseOk l Γ Λ Λ' e a args he hp hd hgd hr err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannAxiomCallElseOk (passes := p + j) (M.plus j) f l Γ Λ Λ' e a args he hp hd hgd hr err rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ σ₂ v hax neu hneu hΛ
    | dannAxiomCallElseGrund l Γ Λ Λ' e a args he hp hd hgd hr err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannAxiomCallElseGrund (passes := p + j) (M.plus j) f l Γ Λ Λ' e a args he hp hd hgd hr err rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ σ₂ r hax neu hneu hΛ
    | dannBindCallIndElse l Γ Λ Λ' Λ'' τ n pB args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho
        neu hneu =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannBindCallIndElse (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' τ n pB args he hp hr err rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) hΛ s0 hs0 g hg hv rho hrho neu hneu
    | dannCallIndElse l Γ Λ Λ' Λ'' τ n pB args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho
        neu hneu =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannCallIndElse (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' τ n pB args he hp hr err rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) hΛ s0 hs0 g hg hv rho hrho neu hneu
    | rueckBind caller rest hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hAnon17 g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.rueckBind (passes := p + j) (M.plus j) f (caller.plus j) (rest.map (RufRahmenG.plus j)) (congrArg (List.map (RufRahmenG.plus j)) hpop) l Γ Λ Λ' τ restb (k.plus j) ρc (hcaller.imp (fun h => RufRahmenG.plus_rest h) (fun ⟨n, err, h⟩ => ⟨n, err, RufRahmenG.plus_rest h⟩)) Γc Λc e hperm ρ (RufRahmenG.plus_rest hAnon17) g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv he neu hneu
    | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hleave hhead σ' ρ' neu hstep hneu hkein_nimmt σ₁ hs₁ hw neu₁ hneu₁ hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannLeaveTrav (passes := p + j) (M.plus j) f l Γ Λ t inv body is (k.plus j) rest i ρ hleave (RufRahmenG.plus_rest hhead) σ' ρ' neu ((execStmt_blatt_passes O p (p + j) keinRuf _ rfl _ _).symm.trans hstep) hneu hkein_nimmt σ₁ hs₁ hw neu₁ hneu₁ hΛ
    | dannNextTrav l Γ Λ t inv body is k rest i ρ hnext hhead σ' ρ' neu hstep hneu hkein_nimmt hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannNextTrav (passes := p + j) (M.plus j) f l Γ Λ t inv body is (k.plus j) rest i ρ hnext (RufRahmenG.plus_rest hhead) σ' ρ' neu ((execStmt_blatt_passes O p (p + j) keinRuf _ rfl _ _).symm.trans hstep) hneu hkein_nimmt hΛ
    | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein_nimmt hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannLeaveWieder (passes := p + j) (M.plus j) f l Γ Λ n bis body ueber (k.plus j) rest ρ hleave (RufRahmenG.plus_rest hhead) σ' ρ' neu ((execStmt_blatt_passes O p (p + j) keinRuf _ rfl _ _).symm.trans hstep) hneu hkein_nimmt hΛ
    | dannNextWieder l Γ Λ n bis body ueber k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein_nimmt hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannNextWieder (passes := p + j) (M.plus j) f l Γ Λ n bis body ueber (k.plus j) rest ρ hnext (RufRahmenG.plus_rest hhead) σ' ρ' neu ((execStmt_blatt_passes O p (p + j) keinRuf _ rfl _ _).symm.trans hstep) hneu hkein_nimmt hΛ
    | dannLeaveEwig l Γ Λ a n inv body k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein_nimmt hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannLeaveEwig (passes := p + j) (M.plus j) f l Γ Λ a (n + j) inv body (k.plus j) rest ρ hleave (RufRahmenG.plus_rest hhead) σ' ρ' neu ((execStmt_blatt_passes O p (p + j) keinRuf _ rfl _ _).symm.trans hstep) hneu hkein_nimmt hΛ
  | g4 h =>
    cases h with
    | dannNextEwig l Γ Λ a n inv body k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein_nimmt hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannNextEwig (passes := p + j) (M.plus j) f l Γ Λ a (n + j) inv body (k.plus j) rest ρ hnext (RufRahmenG.plus_rest hhead) σ' ρ' neu ((execStmt_blatt_passes O p (p + j) keinRuf _ rfl _ _).symm.trans hstep) hneu hkein_nimmt hΛ
    | peelDannLeave l Γ Λ rest b k ρ hleave hhead =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.peelDannLeave (passes := p + j) (M.plus j) f l Γ Λ rest b (k.plus j) ρ hleave (RufRahmenG.plus_rest hhead)
    | peelDannNext l Γ Λ rest b k ρ hnext hhead =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.peelDannNext (passes := p + j) (M.plus j) f l Γ Λ rest b (k.plus j) ρ hnext (RufRahmenG.plus_rest hhead)
    | peelSchrumpfLeave l Γ Λ τ rest k ρ hleave hhead =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.peelSchrumpfLeave (passes := p + j) (M.plus j) f l Γ Λ τ rest (k.plus j) ρ hleave (RufRahmenG.plus_rest hhead)
    | peelSchrumpfNext l Γ Λ τ rest k ρ hnext hhead =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.peelSchrumpfNext (passes := p + j) (M.plus j) f l Γ Λ τ rest (k.plus j) ρ hnext (RufRahmenG.plus_rest hhead)
    | peelFreiLeave l Γ Λ L rest k ρ hleave hhead =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.peelFreiLeave (passes := p + j) (M.plus j) f l Γ Λ L rest (k.plus j) ρ hleave (RufRahmenG.plus_rest hhead)
    | peelFreiNext l Γ Λ L rest k ρ hnext hhead =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.peelFreiNext (passes := p + j) (M.plus j) f l Γ Λ L rest (k.plus j) ρ hnext (RufRahmenG.plus_rest hhead)
    | peelAbbruchLeave Γ Λ Λ1 Λk rest k ρ hleave hhead =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.peelAbbruchLeave (passes := p + j) (M.plus j) f Γ Λ Λ1 Λk rest (k.plus j) ρ hleave (RufRahmenG.plus_rest hhead)
    | peelAbbruchNext Γ Λ Λ1 Λk rest k ρ hnext hhead =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.peelAbbruchNext (passes := p + j) (M.plus j) f Γ Λ Λ1 Λk rest (k.plus j) ρ hnext (RufRahmenG.plus_rest hhead)
    | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv neu hneu hnw =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannRet (passes := p + j) (M.plus j) f l Γ Λ Λ'' e hperm rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) (caller.plus j) (rst.map (RufRahmenG.plus j)) (congrArg (List.map (RufRahmenG.plus j)) hpop) hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv neu hneu (by rw [RufRahmenG.plus_wartend]; exact hnw)
    | rueckCons caller rst hpop Γ Λ e hperm rest ρ hAnon9 g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.rueckCons (passes := p + j) (M.plus j) f (caller.plus j) (rst.map (RufRahmenG.plus j)) (congrArg (List.map (RufRahmenG.plus j)) hpop) Γ Λ e hperm rest ρ (RufRahmenG.plus_rest hAnon9) g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu (by rw [RufRahmenG.plus_wartend]; exact hnw)
    | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannRetBind (passes := p + j) (M.plus j) f lk Γk Λk Λk'' e hperm restk (kk.plus j) ρ (RufRahmenG.plus_rest hhead) (caller.plus j) (rst.map (RufRahmenG.plus j)) (congrArg (List.map (RufRahmenG.plus j)) hpop) l Γ Λ Λ' τ restb (k.plus j) ρc (hcaller.imp (fun h => RufRahmenG.plus_rest h) (fun ⟨n, err, h⟩ => ⟨n, err, RufRahmenG.plus_rest h⟩)) hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu
    | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.rueckConsBind (passes := p + j) (M.plus j) f lk Γk Λk e hperm restk ρ (RufRahmenG.plus_rest hhead) (caller.plus j) (rst.map (RufRahmenG.plus j)) (congrArg (List.map (RufRahmenG.plus j)) hpop) l Γ Λ Λ' τ restb (k.plus j) ρc (hcaller.imp (fun h => RufRahmenG.plus_rest h) (fun ⟨n, err, h⟩ => ⟨n, err, RufRahmenG.plus_rest h⟩)) hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu
    | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho hrho s0 hs0 rg hrg hn =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.rueckGrund (passes := p + j) (M.plus j) f r hperm ρ (RufRahmenG.plus_rest hhead) (caller.plus j) (rst.map (RufRahmenG.plus j)) (congrArg (List.map (RufRahmenG.plus j)) hpop) l Γ Λ Λ' τ n err restb (k.plus j) ρc (RufRahmenG.plus_rest hcaller) hΛ g hfg rho hrho s0 hs0 rg hrg hn
  | g5 h =>
    cases h with
    | rueckConsGrund _ _ r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho hrho s0 hs0 rg hrg hn =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.rueckConsGrund (passes := p + j) (M.plus j) f r hperm restk ρ (RufRahmenG.plus_rest hhead) (caller.plus j) (rst.map (RufRahmenG.plus j)) (congrArg (List.map (RufRahmenG.plus j)) hpop) l Γ Λ Λ' τ n err restb (k.plus j) ρc (RufRahmenG.plus_rest hcaller) hΛ g hfg rho hrho s0 hs0 rg hrg hn
    | dannRetGrund _ _ r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho hrho s0 hs0 rg hrg hn =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannRetGrund (passes := p + j) (M.plus j) f r hperm restk (kk.plus j) ρ (RufRahmenG.plus_rest hhead) (caller.plus j) (rst.map (RufRahmenG.plus j)) (congrArg (List.map (RufRahmenG.plus j)) hpop) l Γ Λ Λ' τ n err restb (k.plus j) ρc (RufRahmenG.plus_rest hcaller) hΛ g hfg rho hrho s0 hs0 rg hrg hn
    | dannRegLies _ _ l Γ Λ Λ' r hk rest k ρ hhead v hv hz hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannRegLies (passes := p + j) (M.plus j) f l Γ Λ Λ' r hk rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) v hv hz hΛ
    | dannRegLiesElseWahr _ _ l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannRegLiesElseWahr (passes := p + j) (M.plus j) f l Γ Λ Λ' r hk zusage sonst rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) v hv σ₁ hs₁ hw neu hneu hΛ
    | dannRegLiesElseFalsch _ _ l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannRegLiesElseFalsch (passes := p + j) (M.plus j) f l Γ Λ Λ' r hk zusage sonst rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) v hv σ₁ hs₁ hw neu hneu hΛ
    | dannAwaits _ _ l Γ Λ Λ' g payload hp hL hat rest k ρ hhead hvis σ₁ hs₁ neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannAwaits (passes := p + j) (M.plus j) f l Γ Λ Λ' g payload hp hL hat rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) hvis σ₁ hs₁ neu hneu hΛ
    | dannExchange _ _ l Γ Λ Λ' g neuE hw hL rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannExchange (passes := p + j) (M.plus j) f l Γ Λ Λ' g neuE hw hL rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ σ₂ hs₂ neu hneu hΛ
    | dannGleit _ _ l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannGleit (passes := p + j) (M.plus j) f l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ v hv neu hneu hΛ
    | dannGleitLit _ _ l Γ Λ Λ' q lo hi rest k ρ hhead v hv =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannGleitLit (passes := p + j) (M.plus j) f l Γ Λ Λ' q lo hi rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) v hv
    | dannGleitVon _ _ l Γ Λ Λ' l₁ h₁ e lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannGleitVon (passes := p + j) (M.plus j) f l Γ Λ Λ' l₁ h₁ e lo hi rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ v hv neu hneu hΛ
    | dannGleitNarrowOk _ _ l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannGleitNarrowOk (passes := p + j) (M.plus j) f l Γ Λ Λ' l₁ h₁ e lo hi sonst rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ v hv neu hneu hΛ
    | dannGleitNarrowElse _ _ l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannGleitNarrowElse (passes := p + j) (M.plus j) f l Γ Λ Λ' l₁ h₁ e lo hi sonst rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ hn neu hneu hΛ
    | dannBindAxiom _ _ l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannBindAxiom (passes := p + j) (M.plus j) f l Γ Λ Λ' τ a args he hw hg hd hgd rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ σ₂ v hax neu hneu hΛ
    | dannBindAxiomElseOk _ _ l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannBindAxiomElseOk (passes := p + j) (M.plus j) f l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ σ₂ v hax neu hneu hΛ
    | dannBindAxiomElseGrund _ _ l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannBindAxiomElseGrund (passes := p + j) (M.plus j) f l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ σ₂ r hax neu hneu hΛ
    | dannBindAxiomOpt _ _ l Γ Λ Λ' e a args he hp hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        change RufSchrittG P O (p + j) (M.plus j) f
          ⟨σ₂.speicher, rufUpdateG (M.plus j).faeden f
            ⟨((M.plus j).faeden f).stapel,
              ⟨((M.plus j).faeden f).kopf.f, ((M.plus j).faeden f).kopf.rho,
                ((M.plus j).faeden f).kopf.s0,
                ⟨l, ErgCtx Γ e, nachSig D (D.asignatur a) Λ, ergEnv e (he ▸ v) ρ,
                  .dann rest ((GRest.weiterOpt (Λ := Λ') e k).plus j)⟩⟩,
              σ₂.spur, ((M.plus j).faeden f).log⟩,
            (M.plus j).lauf ++ rufEigenG f neu, (M.plus j).start⟩
        rw [plus_weiterOpt]
        exact RufSchrittG.dannBindAxiomOpt (passes := p + j) (M.plus j) f l Γ Λ Λ' e a args he hp hd hgd rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ σ₂ v hax neu hneu hΛ
    | dannBindAxiomOptElseOk _ _ l Γ Λ Λ' e a args he hr hp hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        change RufSchrittG P O (p + j) (M.plus j) f
          ⟨σ₂.speicher, rufUpdateG (M.plus j).faeden f
            ⟨((M.plus j).faeden f).stapel,
              ⟨((M.plus j).faeden f).kopf.f, ((M.plus j).faeden f).kopf.rho,
                ((M.plus j).faeden f).kopf.s0,
                ⟨l, ErgCtx Γ e, nachSig D (D.asignatur a) Λ, ergEnv e (he ▸ v) ρ,
                  .dann rest ((GRest.weiterOpt (Λ := Λ') e k).plus j)⟩⟩,
              σ₂.spur, ((M.plus j).faeden f).log⟩,
            (M.plus j).lauf ++ rufEigenG f neu, (M.plus j).start⟩
        rw [plus_weiterOpt]
        exact RufSchrittG.dannBindAxiomOptElseOk (passes := p + j) (M.plus j) f l Γ Λ Λ' e a args he hr hp hd hgd err rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ σ₂ v hax neu hneu hΛ
    | dannBindAxiomOptElseGrund _ _ l Γ Λ Λ' e a args he hr hp hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannBindAxiomOptElseGrund (passes := p + j) (M.plus j) f l Γ Λ Λ' e a args he hr hp hd hgd err rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ σ₂ r hax neu hneu hΛ
  | g6 h =>
    cases h with
    | endeBindAxiomElseOk l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.endeBindAxiomElseOk (passes := p + j) (M.plus j) f l Γ Λ τ a args he hr hw hg hd hgd err rest ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ σ₂ v hax neu hneu hΛ
    | endeBindAxiomElseGrund l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.endeBindAxiomElseGrund (passes := p + j) (M.plus j) f l Γ Λ τ a args he hr hw hg hd hgd err rest ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ σ₂ r hax neu hneu hΛ
    | endeBindAxiomOptElseOk l Γ Λ e a args he hr hp hd hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.endeBindAxiomOptElseOk (passes := p + j) (M.plus j) f l Γ Λ e a args he hr hp hd hgd err rest ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ σ₂ v hax neu hneu hΛ
    | endeBindAxiomOptElseGrund l Γ Λ e a args he hr hp hd hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.endeBindAxiomOptElseGrund (passes := p + j) (M.plus j) f l Γ Λ e a args he hr hp hd hgd err rest ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ σ₂ r hax neu hneu hΛ
  | g7 h =>
    cases h with
    | dannVerbrauch l Γ Λ Λ'' t member edge inv bound mass body rest k ρ hhead =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannVerbrauch (passes := p + j) (M.plus j) f l Γ Λ Λ'' t member edge inv bound mass body rest (k.plus j) ρ (RufRahmenG.plus_rest hhead)
    | verbrauchWeiter l Γ Λ t member edge inv bound mass body rest k ρ hhead σ₁ hs₁ hw σ₂ hs₂ v hv σ₃ hs₃ m hm neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.verbrauchWeiter (passes := p + j) (M.plus j) f l Γ Λ t member edge inv bound mass body rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ hw σ₂ hs₂ v hv σ₃ hs₃ m hm neu hneu hΛ
    | verbrauchLeer l Γ Λ t member edge inv bound mass body rest k ρ hhead σ₁ hs₁ hw σ₂ hs₂ hleer hkein neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.verbrauchLeer (passes := p + j) (M.plus j) f l Γ Λ t member edge inv bound mass body rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ hw σ₂ hs₂ hleer hkein neu hneu hΛ
    | verbrauchFort l Γ Λ t member edge inv bound mass body rest vor k i ρ hhead σ₁ hs₁ m' hm' hfall neu hneu hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.verbrauchFort (passes := p + j) (M.plus j) f l Γ Λ t member edge inv bound mass body rest vor (k.plus j) i ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ m' hm' hfall neu hneu hΛ
    | dannLeaveVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb i ρ hleave hhead σ' ρ' neu hstep hneu hkein_nimmt σm hsm m' hm' hfall σ₁ hs₁ hw neu₁ hneu₁ hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannLeaveVerbrauch (passes := p + j) (M.plus j) f l Γ Λ t member edge inv bound mass body rest vor (k.plus j) restb i ρ hleave (RufRahmenG.plus_rest hhead) σ' ρ' neu ((execStmt_blatt_passes O p (p + j) keinRuf _ rfl _ _).symm.trans hstep) hneu hkein_nimmt σm hsm m' hm' hfall σ₁ hs₁ hw neu₁ hneu₁ hΛ
    | dannNextVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb i ρ hnext hhead σ' ρ' neu hstep hneu hkein_nimmt σm hsm m' hm' hfall neum hneum hΛ =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.dannNextVerbrauch (passes := p + j) (M.plus j) f l Γ Λ t member edge inv bound mass body rest vor (k.plus j) restb i ρ hnext (RufRahmenG.plus_rest hhead) σ' ρ' neu ((execStmt_blatt_passes O p (p + j) keinRuf _ rfl _ _).symm.trans hstep) hneu hkein_nimmt σm hsm m' hm' hfall neum hneum hΛ

    | rueckScopedWert ρ r e R hhead hret hscope hΛ σ₁ σ₂ hs₁ hs₂ neu hneu z hantwort =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.rueckScopedWert (passes := p + j) (M.plus j) f ρ (r.plus j) e R (RufRahmenG.plus_rest hhead) (by rw [GRest.plus_scopedWert]; exact hret) hscope hΛ σ₁ σ₂ hs₁ hs₂ neu hneu (z.plus j) (rufAntwortG_plus j hantwort)
    | rueckScopedGrund ρ r grund R hhead hret hscope hΛ σ₂ hs₂ neu hneu z hantwort =>
        rw [RufMaschineG.plus_update]
        exact RufSchrittG.rueckScopedGrund (passes := p + j) (M.plus j) f ρ (r.plus j) grund R (RufRahmenG.plus_rest hhead) (by rw [GRest.plus_scopedGrund]; exact hret) hscope hΛ σ₂ hs₂ neu hneu (z.plus j) (rufAntwortG_plus j hantwort)

theorem rufErreichbarG_plus {P : Programm D} {O : Orakel D} {p : Nat} (j : Nat) {M0 M : RufMaschineG D}
    (h : RufErreichbarG P O p M0 M) : RufErreichbarG P O (p + j) (M0.plus j) (M.plus j) := by
  induction h with
  | start => exact .start
  | schritt M M' f _ hs ih => exact .schritt _ _ f ih (rufSchrittG_plus j hs)

/-! ## 4. Over GX and on the thread machine -/

theorem mitSpeicher_plus (j : Nat) (M : RufMaschineG D) (σ : Speicher D) :
    mitSpeicher (M.plus j) σ = (mitSpeicher M σ).plus j := by rfl

theorem schreibG_plus (j : Nat) (M M' : RufMaschineG D) (u : Faden) (c : D.Tab ⊕ D.Glob) :
    SchreibG (M.plus j) (M'.plus j) u c ↔ SchreibG M M' u c := Iff.rfl

theorem rufSchrittGX_plus {P : Programm D} {O : Orakel D} {p : Nat} {Tg : D.Tab ⊕ D.Glob → Prop} (j : Nat)
    {M M' : RufMaschineG D} {u : Faden} (h : RufSchrittGX P O p Tg M u M') :
    RufSchrittGX P O (p + j) Tg (M.plus j) u (M'.plus j) := by
  obtain ⟨σ, M'', hs, hσ, h1, h2, h3, h4, h5⟩ := h
  refine ⟨σ, M''.plus j, ?_, hσ, h1, h2, ?_, h4, h5⟩
  · rw [mitSpeicher_plus]; exact rufSchrittG_plus j hs
  · show (fun t => (M'.faeden t).plus j) = fun t => (M''.faeden t).plus j
    rw [h3]

theorem rufErreichbarGX_plus {P : Programm D} {O : Orakel D} {p : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    (j : Nat) {M0 M : RufMaschineG D} (h : RufErreichbarGX P O p Tg M0 M) :
    RufErreichbarGX P O (p + j) Tg (M0.plus j) (M.plus j) := by
  induction h with
  | start => exact .start
  | schritt M M' u _ hs ih => exact .schritt _ _ u ih (rufSchrittGX_plus j hs)

end Gabbro.Grammatik
