/-
  File:      Grammatik/ZielOrtEinfaden.lean
  Subject:   ONE ACTIVE THREAD NEEDS NO FOOTPRINT CHECK -- `ziel_ort_einfaden`,
             the goal theorem with lock invariants for programs in which
             every thread but thread `0` is idle (its root is a bare
             `return`: the model of a sequential corpus program, as
             `Referenz104.lean`'s `r4Init`).

  Lane 138 (`messung/muse/MUSE-REPORT-138.md`) found the footprint check
  firing on 15 of 89 corpus programs, mostly single-threaded ones: a
  carrier only one thread touches needs no guard. The general exemption
  ("only carriers reachable from two started threads need a guard") needs
  the call graph of every thread, which no invariant of G carries (see
  THEOREM-MAP §14.6). The case that matters for sequential programs does not:
  when every other thread is idle, only thread 0 ever steps
  (`kein_schritt_ruhig`: a root frame at a bare `return` has no rule), so
  NO carrier moves under thread 0 except by its own steps, and every
  carrier is local (`LokOk` for `lok := fun _ => true`). The footprint
  check disappears from the theorem.
-/
module
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperre
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. A root frame at a bare `return` never steps -/

/-- The end block is a `return` (of a value or of none). -/
def Endblock.istRet {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → Bool
  | .ret _ _ => true
  | .retScoped _ _ => true
  | _ => false

/-- The residue is an end block that is a `return`. -/
def GRest.istRetEnde {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Bool
  | .ende e => e.istRet
  | _ => false

section Stumm

variable {P : Programm D} {O : Orakel D} {passes : Nat}

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- **A thread with an empty stack whose head is at a `return` has no step**:
    every rule of G needs another head shape, and the returns need a
    caller. -/
theorem kein_schritt_ruhig {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M') (hStk : (M.faeden u).stapel = [])
    (hRet : (M.faeden u).kopf.rest.2.2.2.2.istRetEnde = true) : False := by
  cases hs with
  | g1 hs =>
    cases hs with
    | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Endblock.istRet, Bool.false_eq_true] at hRet
    | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | endeEntf l Γ Λ Λ' s rest ρ hent hhead =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Endblock.istRet, Bool.false_eq_true] at hRet
    | endeForm l Γ Λ e ρ hl hent hhead =>
      rw [hhead] at hRet
      cases e <;> simp_all [GRest.istRetEnde, Endblock.istRet, EndEntfaltbar]
    | dannLeer l Γ Λ k ρ hhead =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannIteWahr l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannIteFalsch l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannOnOptionSome l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannOnOptionNone l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ hv neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ τ b nutz hw neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | endeBind l Γ Λ τ e rest ρ hhead σ₁ hs₁ neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Endblock.istRet, Bool.false_eq_true] at hRet
    | dannBind l Γ Λ Λ' Λ'' τ e rest k ρ hhead σ₁ hs₁ neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannNarrowOk l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | endeBindAxiom l Γ Λ τ a args he hw hg hd hgd rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Endblock.istRet, Bool.false_eq_true] at hRet
    | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Endblock.istRet, Bool.false_eq_true] at hRet
    | rueck caller rst hpop Γ Λ e hperm ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
      rw [hpop] at hStk
      cases hStk
  | g2 hs =>
    cases hs with
    | dannNarrowElse l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannPruefWahr l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannPruefFalsch l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannBreaking l Γ Λ Λ' Λ'' i body rest k ρ hhead =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | freiGib l Γ Λ L k ρ hhead =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | schrumpfVergiss l Γ Λ τ k v ρ hhead =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannTrav l Γ Λ Λ'' t inv body rest k ρ hhead =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | travNext l Γ Λ t inv body i is k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | travFort l Γ Λ t inv body is k i ρ hhead =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | travDone l Γ Λ t inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannRetry l Γ Λ Λ' Λ'' n bis body ueber rest k ρ hhead =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | wiederUeber l Γ Λ bis body ueber k ρ hhead =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | wiederWeiter l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | wiederSchritt l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | wiederFort l Γ Λ n bis body ueber k ρ hhead =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannForever l Γ Λ Λ' Λ'' a inv body rest k ρ hhead =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | ewigWeiter l Γ Λ a n inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | ewigFort l Γ Λ a n inv body k ρ hhead =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
  | g3 hs =>
    cases hs with
    | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hleave hhead σ' ρ' neu hstep hneu hkein σ₁ hs₁ hw neu₁ hneu₁ hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannNextTrav l Γ Λ t inv body is k rest i ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannNextWieder l Γ Λ n bis body ueber k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannLeaveEwig l Γ Λ a n inv body k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Endblock.istRet, Bool.false_eq_true] at hRet
    | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannBindCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho
        hrho neu hneu =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho
        hrho neu hneu =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
      rw [hpop] at hStk
      cases hStk
  | g4 hs =>
    cases hs with
    | dannNextEwig l Γ Λ a n inv body k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | peelDannLeave l Γ Λ rest b k ρ hleave hhead =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | peelDannNext l Γ Λ rest b k ρ hnext hhead =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | peelSchrumpfLeave l Γ Λ τ rest k ρ hleave hhead =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | peelSchrumpfNext l Γ Λ τ rest k ρ hnext hhead =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | peelFreiLeave l Γ Λ L rest k ρ hleave hhead =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | peelFreiNext l Γ Λ L rest k ρ hnext hhead =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | peelAbbruchLeave Γ Λ Λ1 Λk rest k ρ hleave hhead =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | peelAbbruchNext Γ Λ Λ1 Λk rest k ρ hnext hhead =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | rueckCons caller rst hpop Γ Λ e hperm rest ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
      rw [hpop] at hStk
      cases hStk
    | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv neu hneu hnw =>
      rw [hpop] at hStk
      cases hStk
    | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      rw [hpop] at hStk
      cases hStk
    | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      rw [hpop] at hStk
      cases hStk
    | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho hrho s0 hs0 rg hrg hn =>
      rw [hpop] at hStk
      cases hStk
  | g5 hs =>
    cases hs with
    | dannExchange l Γ Λ Λ' g neuE hw hLg rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannGleit l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannGleitLit l Γ Λ Λ' q lo hi rest k ρ hhead v hv =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannGleitVon l Γ Λ Λ' l₁ h₁ e lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannGleitNarrowOk l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannGleitNarrowElse l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannBindAxiomElseOk l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannBindAxiomElseGrund l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | rueckConsGrund r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho hrho s0 hs0 rg hrg hn =>
      rw [hpop] at hStk
      cases hStk
    | dannRetGrund r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho hrho s0 hs0 rg hrg hn =>
      rw [hpop] at hStk
      cases hStk
    | dannRegLies l Γ Λ Λ' r hk rest k ρ hhead v hv hz hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannRegLiesElseWahr l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannRegLiesElseFalsch l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
    | dannAwaits l Γ Λ Λ' g payload hp hLg hat rest k ρ hhead hvis σ₁ hs₁ neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Bool.false_eq_true] at hRet
  | g6 hs =>
    cases hs with
    | endeBindAxiomElseOk l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Endblock.istRet, Bool.false_eq_true] at hRet
    | endeBindAxiomElseGrund l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      rw [hhead] at hRet
      simp only [GRest.istRetEnde, Endblock.istRet, Bool.false_eq_true] at hRet

end Stumm
end Gabbro.Grammatik
