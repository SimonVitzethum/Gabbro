module

public import Grammatik.Zielsatz.Einbettung.Simulation
public import Grammatik.Zielsatz.Einbettung.Koerper.Teil2
public import Grammatik.Zielsatz.Einbettung.Koerper.Teil2a

@[expose] public section

namespace Gabbro.Grammatik.Einbettung
open Gabbro.Grammatik
variable {D D' : Deklaration}
namespace Einbettung
variable (E : Einbettung D D')

private theorem readWorld_indirect {Γ : Ctx} {Λ : List (Res D)} {n : Nat} {τs : List Ty}
    (A' : AUmwelt D') (σ' : World D') (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ τs) :
    leseA A' σ' (Λ.map E.resE)
        (List.append (Expr.orte (D := D') (τ := .fnptr (E.num n)) (exE E p)) (args.orte.map E.ortE)) =
      leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE) := by
  have reads : Expr.orte (D := D') (τ := .fnptr (E.num n)) (exE E p) = p.orte.map E.ortE := E.orte_exE p
  exact congrArg (fun xs : List (D'.Tab ⊕ D'.Glob) => leseA A' σ' (Λ.map E.resE) xs)
    ((congrArg (fun xs : List (D'.Tab ⊕ D'.Glob) => List.append xs (args.orte.map E.ortE)) reads).trans
      List.map_append.symm)

variable (hZ : E.Rueck) (hS : E.SigTreu) (pad : List (Ereignis D)) (S : SperrInv D)
  (T : D.Tab ⊕ D.Glob → Prop) (S' : SperrInv D') (T' : D'.Tab ⊕ D'.Glob → Prop) (O' : Orakel D')
  (U' : Umwelt D') (A' : AUmwelt D') (passes : Nat)
  (R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f)
section Sim
variable (hB : E.Bed hZ pad S T S' T' U' A')
include hB

set_option linter.unusedSectionVars false in
theorem sim_block_bindCallInd {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (n)
    (τ)
    (p)
    (args)
    (he)
    (hp)
    (hr)
    (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.bindCallInd (n := n) (τ := τ) p args he hp hr rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.bindCallInd (n := n) (τ := τ) p args he hp hr rest : Block D V l Γ Λ Λ'))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  have readWorld := readWorld_indirect E A' σ' p args
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (p.orte ++ args.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  rcases hvd : eval σ₁ p σ₁ ρ with ⟨f, hf⟩
  have hp' := hev p ρ ρ' hρ
  rw [hvd] at hp'
  rcases hvd' : eval (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exE E p) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ' with ⟨f', hf'⟩
  rw [hvd'] at hp'
  have pointerValue : eval (D := D') (τ := .fnptr (E.num n))
      (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exE E p)
      (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ' = ⟨f', hf'⟩ := hvd'
  have hk : E.Konform hZ f f' := by
    rcases hp' with h | ⟨hz, hr⟩
    · exact Or.inl h
    · exact Or.inr ⟨n, hz, hr, hf'⟩
  have hsig : (D.sigNr n).params.map E.tyE = (D'.sigNr (E.num n)).params := by rw [hS.sigNr]; rfl
  have heS : (D'.sigNr (E.num n)).erg = some (E.tyE τ) := by
    rw [hS.sigNr]; show Option.map E.tyE (D.sigNr n).erg = _; rw [he]; rfl
  have he' : D'.erg f' = some (E.tyE τ) := ergSig hf' heS
  have noReason : (D'.sigNr (E.num n)).gruende = 0 := by rw [hS.sigNr]; exact hr
  let read : World D' := leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)
  let callArgs : Env D' (D'.params f') := umsig hf' (castE hsig (evalArgs read (exA E args) read ρ'))
  have target : execBlockHA S' O' U' A' passes R'
      (exB hS (.bindCallInd (τ := τ) p args he hp hr rest : Block D V l Γ Λ Λ')) σ' ρ' =
      (match R' f' read callArgs with
      | .ok W v => (execBlockHA S' O' U' A' passes R' (exB hS rest) W
          (Env.cons (τ := E.tyE τ) (ergWert he' v) ρ')).schrumpf
      | .why _ r => keinGrundSig hf' noReason r
      | .logik e => .logik e
      | .hardware e => .hardware e : Ausgang (E.vertragE V) l (Γ.map E.tyE)) := by
    simp only [exB, execBlockHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, execBlock_vorΛ]
    erw [readWorld, pointerValue] <;> rfl
  obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schritt hZ hS pad R' hB.pad hI f (umsig hf (evalArgs σ₁ args σ₁ ρ)) f'
    (umsig hf' (castE hsig (evalArgs (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ')))
    (E.envR_umsig hZ hf hf' _ _ ((E.envR_um hZ hsig _ _).mpr
      (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ))) hk
  generalize ha : R' f' (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (umsig hf' (castE hsig (evalArgs (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ'))) = a' at hRΦ
  have answer : R' f' read callArgs = a' := ha
  rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
  · have he₁ : D.erg f = some τ := ergSig hf he
    obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih_sim_block_rest M₂ (E.antwortWelt hZ pad σ₁ W) W
      (.cons (ergWert he₁ (E.ergZ hZ (D.erg f) (castV (konform_sig hS hk).2.1 v'))) ρ)
      (.cons (ergWert he' v') ρ')
      (hI2 W)
      (E.envR_cons hZ hρ _ _ rfl (E.ergWert_ergZ hZ (konform_sig hS hk).2.1.symm he₁ he' v'))
    refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hvd, hRΦ Φ (passt_teil hP hs3),
        antwortR]
      exact congrArg Ausgang.schrumpf (hΦ3 Φ hP)
    · rw [target, answer]
      exact E.ausRel_schrumpf hR3
  · have h0 : D'.gruende f' = 0 := (konform_sig hS hk).2.2.trans ((D.passt_sig hf).gruende.trans hr)
    exact (Fin.cast h0 r').elim0
  · refine ⟨M₂, .logik (logikZ f e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
    · rw [target, answer]
      exact ⟨logikRel_logikZ f e', (hI2 σ').keyOk E⟩
  · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
    · rw [target, answer]
      trivial

set_option linter.unusedSectionVars false in
theorem sim_block_bindCallIndElse {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (n)
    (τ)
    (p)
    (args)
    (he)
    (hp)
    (hr)
    (err)
    (rest)
    (ih_sim_block_rest : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execBlockHA S' O' U' A' passes R' (exB hS rest)))
    (ih_sim_end_err : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') err) (execEndHA S' O' U' A' passes R' (exEnd hS err)))
    : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.bindCallIndElse (n := n) (τ := τ) p args he hp hr err rest : Block D V l Γ Λ Λ')) (execBlockHA S' O' U' A' passes R' (exB hS (.bindCallIndElse (n := n) (τ := τ) p args he hp hr err rest : Block D V l Γ Λ Λ'))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  have readWorld := readWorld_indirect E A' σ' p args
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (p.orte ++ args.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  rcases hvd : eval σ₁ p σ₁ ρ with ⟨f, hf⟩
  have hp' := hev p ρ ρ' hρ
  rw [hvd] at hp'
  rcases hvd' : eval (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exE E p) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ' with ⟨f', hf'⟩
  rw [hvd'] at hp'
  have pointerValue : eval (D := D') (τ := .fnptr (E.num n))
      (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exE E p)
      (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ' = ⟨f', hf'⟩ := hvd'
  have hk : E.Konform hZ f f' := by
    rcases hp' with h | ⟨hz, hr⟩
    · exact Or.inl h
    · exact Or.inr ⟨n, hz, hr, hf'⟩
  have hsig : (D.sigNr n).params.map E.tyE = (D'.sigNr (E.num n)).params := by rw [hS.sigNr]; rfl
  have hchan : (D'.sigNr (E.num n)).gruende = (D.sigNr n).gruende := by rw [hS.sigNr]; rfl
  have heS : (D'.sigNr (E.num n)).erg = some (E.tyE τ) := by
    rw [hS.sigNr]; show Option.map E.tyE (D.sigNr n).erg = _; rw [he]; rfl
  have he' : D'.erg f' = some (E.tyE τ) := ergSig hf' heS
  have hc : (Ty.why (D.sigNr n).gruende :: Γ).map E.tyE =
      Ty.why (D'.sigNr (E.num n)).gruende :: Γ.map E.tyE := by rw [hS.sigNr]; rfl
  let read : World D' := leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)
  let callArgs : Env D' (D'.params f') := umsig hf' (castE hsig (evalArgs read (exA E args) read ρ'))
  let error : Endblock D' (E.vertragE V) l (.why (D'.sigNr (E.num n)).gruende :: Γ.map E.tyE)
      (nachSig D' (D'.sigNr (E.num n)) (Λ.map E.resE)) :=
    Endblock.umΓ hc (Endblock.umΛ (nachSigE_nr hS n Λ) (exEnd hS err))
  have target : execBlockHA S' O' U' A' passes R'
      (exB hS (.bindCallIndElse (τ := τ) p args he hp hr err rest : Block D V l Γ Λ Λ')) σ' ρ' =
      (match R' f' read callArgs with
      | .ok W v => (execBlockHA S' O' U' A' passes R' (exB hS rest) W
          (Env.cons (τ := E.tyE τ) (ergWert he' v) ρ')).schrumpf
      | .why W r => (execEndHA S' O' U' A' passes R' error W
          (Env.cons (τ := .why (D'.sigNr (E.num n)).gruende) (grundSig hf' r) ρ')).schrumpf.zuAusgang
      | .logik e => .logik e
      | .hardware e => .hardware e : Ausgang (E.vertragE V) l (Γ.map E.tyE)) := by
    simp only [exB, execBlockHA, indSonst, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, execBlock_vorΛ]
    erw [readWorld, pointerValue] <;> rfl
  obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schritt hZ hS pad R' hB.pad hI f (umsig hf (evalArgs σ₁ args σ₁ ρ)) f'
    (umsig hf' (castE hsig (evalArgs (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ')))
    (E.envR_umsig hZ hf hf' _ _ ((E.envR_um hZ hsig _ _).mpr
      (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ))) hk
  generalize ha : R' f' (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (umsig hf' (castE hsig (evalArgs (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ'))) = a' at hRΦ
  have answer : R' f' read callArgs = a' := ha
  rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
  · have he₁ : D.erg f = some τ := ergSig hf he
    obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih_sim_block_rest M₂ (E.antwortWelt hZ pad σ₁ W) W
      (.cons (ergWert he₁ (E.ergZ hZ (D.erg f) (castV (konform_sig hS hk).2.1 v'))) ρ)
      (.cons (ergWert he' v') ρ')
      (hI2 W)
      (E.envR_cons hZ hρ _ _ rfl (E.ergWert_ergZ hZ (konform_sig hS hk).2.1.symm he₁ he' v'))
    refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, indSonst, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hvd, hRΦ Φ (passt_teil hP hs3),
        antwortR]
      exact congrArg Ausgang.schrumpf (hΦ3 Φ hP)
    · rw [target, answer]
      exact E.ausRel_schrumpf hR3
  · let sourceReason : Fin (D.sigNr n).gruende := grundSig hf (Fin.cast (konform_sig hS hk).2.2 r')
    let targetReason : Fin (D'.sigNr (E.num n)).gruende := grundSig hf' r'
    have sourceNumber : sourceReason.val = r'.val :=
      congrArg Fin.val (grundSig_eq_cast hf (D.passt_sig hf).gruende (Fin.cast (konform_sig hS hk).2.2 r'))
    have targetNumber : targetReason.val = r'.val :=
      congrArg Fin.val (grundSig_eq_cast hf' (D'.passt_sig hf').gruende r')
    have reasonTy : Ty.why (D'.sigNr (E.num n)).gruende = E.tyE (.why (D.sigNr n).gruende) := by
      rw [hchan] <;> rfl
    have reasons : E.VRel hZ (.why (D.sigNr n).gruende) sourceReason (castW reasonTy targetReason) := by
      change (castW (D := D') reasonTy targetReason : Fin (D.sigNr n).gruende) = sourceReason
      apply Fin.ext
      exact (congrArg Fin.val (castW_why (D' := D') reasonTy targetReason)).trans
        (targetNumber.trans sourceNumber.symm)
    obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih_sim_end_err M₂ (E.antwortWelt hZ pad σ₁ W) W
      (Env.cons (τ := .why (D.sigNr n).gruende) sourceReason ρ)
      (castE hc.symm (Env.cons (τ := .why (D'.sigNr (E.num n)).gruende) targetReason ρ'))
      (hI2 W)
      ((E.envR_um hZ hc.symm _ _).mpr (E.envR_cons (τ := .why (D.sigNr n).gruende)
        (τ' := .why (D'.sigNr (E.num n)).gruende) hZ hρ sourceReason targetReason reasonTy reasons))
    refine ⟨M₃, o.schrumpf.zuAusgang, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, indSonst, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hvd, hRΦ Φ (passt_teil hP hs3),
        antwortR]
      exact congrArg (fun x : EndAusgang V l (.why (D.sigNr n).gruende :: Γ) => x.schrumpf.zuAusgang) (hΦ3 Φ hP)
    · rw [target, answer]
      simp only [error, execEnd_umΓ, execEnd_umΛ]
      exact E.endRel_zuAusgang (E.endRel_schrumpf ((E.endRel_um hc o _).mpr hR3))
  · refine ⟨M₂, .logik (logikZ f e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, indSonst, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
    · rw [target, answer]
      exact ⟨logikRel_logikZ f e', (hI2 σ').keyOk E⟩
  · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execBlockHA, indSonst, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
    · rw [target, answer]
      trivial

end Sim
end Einbettung
end Gabbro.Grammatik.Einbettung
