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
  SATZKARTE §14.6). The case that matters for sequential programs does not:
  when every other thread is idle, only thread 0 ever steps
  (`kein_schritt_ruhig`: a root frame at a bare `return` has no rule), so
  NO carrier moves under thread 0 except by its own steps, and every
  carrier is local (`LokOk` for `lok := fun _ => true`). The footprint
  check disappears from the theorem.
-/
import Grammatik.ZielOrtSperre

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. A root frame at a bare `return` never steps -/

/-- The end block is a `return` (of a value or of none). -/
def Endblock.istRet {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → Bool
  | .ret _ _ => true
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
  | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | endeEntf l Γ Λ Λ' s rest ρ hent hhead =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannLeer l Γ Λ k ρ hhead =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannIteWahr l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannIteFalsch l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannOnOptionSome l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannOnOptionNone l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ hv neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ lo hi b nutz hw neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | endeBind l Γ Λ τ e rest ρ hhead σ₁ hs₁ neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannBind l Γ Λ Λ' Λ'' τ e rest k ρ hhead σ₁ hs₁ neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannNarrowOk l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannNarrowElse l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannPruefWahr l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannPruefFalsch l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannBreaking l Γ Λ Λ' Λ'' i body rest k ρ hhead =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | freiGib l Γ Λ L k ρ hhead =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | schrumpfVergiss l Γ Λ τ k v ρ hhead =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannTrav l Γ Λ Λ'' t inv body rest k ρ hhead =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | travNext l Γ Λ t inv body i is k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | travFort l Γ Λ t inv body is k i ρ hhead =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | travDone l Γ Λ t inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannRetry l Γ Λ Λ' Λ'' n bis body ueber rest k ρ hhead =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | wiederUeber l Γ Λ bis body ueber k ρ hhead =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | wiederWeiter l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | wiederSchritt l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | wiederFort l Γ Λ n bis body ueber k ρ hhead =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannForever l Γ Λ Λ' Λ'' a inv body rest k ρ hhead =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | ewigWeiter l Γ Λ a n inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | ewigFort l Γ Λ a n inv body k ρ hhead =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hleave hhead σ' ρ' neu hstep hneu hkein σ₁ hs₁ hw neu₁ hneu₁ hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannNextTrav l Γ Λ t inv body is k rest i ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannNextWieder l Γ Λ n bis body ueber k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannLeaveEwig l Γ Λ a n inv body k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannNextEwig l Γ Λ a n inv body k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | peelDannLeave l Γ Λ rest b k ρ hleave hhead =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | peelDannNext l Γ Λ rest b k ρ hnext hhead =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | peelSchrumpfLeave l Γ Λ τ rest k ρ hleave hhead =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | peelSchrumpfNext l Γ Λ τ rest k ρ hnext hhead =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | peelFreiLeave l Γ Λ L rest k ρ hleave hhead =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | peelFreiNext l Γ Λ L rest k ρ hnext hhead =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | peelAbbruchLeave Γ Λ Λ1 Λk rest k ρ hleave hhead =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | peelAbbruchNext Γ Λ Λ1 Λk rest k ρ hnext hhead =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannExchange l Γ Λ Λ' g neuE hw hLg rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannGleit l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannGleitLit l Γ Λ Λ' q lo hi rest k ρ hhead v hv =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannGleitVon l Γ Λ Λ' l₁ h₁ e lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannGleitNarrowOk l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannGleitNarrowElse l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | rueck caller rst hpop Γ Λ e hperm ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
    rw [hpop] at hStk
    cases hStk
  | rueckCons caller rst hpop Γ Λ e hperm rest ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
    rw [hpop] at hStk
    cases hStk
  | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv neu hneu hnw =>
    rw [hpop] at hStk
    cases hStk
  | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
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
  | rueckConsGrund r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho hrho s0 hs0 rg hrg hn =>
    rw [hpop] at hStk
    cases hStk
  | dannRetGrund r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho hrho s0 hs0 rg hrg hn =>
    rw [hpop] at hStk
    cases hStk
  | dannRegLies l Γ Λ Λ' r hk rest k ρ hhead v hv hz hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannRegLiesElseWahr l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannRegLiesElseFalsch l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet
  | dannAwaits l Γ Λ Λ' g payload hp hLg rest k ρ hhead hvis σ₁ hs₁ neu hneu hΛ =>
    rw [hhead] at hRet
    simp [GRest.istRetEnde, Endblock.istRet] at hRet

end Stumm

/-! ## 2. Idle threads -/

/-- **An idle function**: its body is a `return`, its footprint (contract
    carriers, body reads, device carriers) is empty, and it holds no lock
    by signature. Decidable. -/
def ruhig (P : Programm D) (f : D.Fn) : Bool :=
  (P.rumpf f).istRet && (fussOrteG P f).isEmpty && (D.haelt f).isEmpty

theorem start_faden (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (t : Faden) :
    (RufStartG P sp init).faeden t =
      ⟨[], ⟨(init t).1, (init t).2, sp.welt [], ⟨false, D.params (init t).1,
        Signatur.anfang D (D.signatur (init t).1), (init t).2, .ende (P.rumpf (init t).1)⟩⟩,
        startSpur (init t).1, [RufEreignisF.eintritt (init t).1 (init t).2 (sp.welt [])]⟩ := by
  show (match init t with
    | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
        Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
        [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D)) = _
  cases init t
  rfl

section Ruhe

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **An idle thread stays at its start**: on every reachable machine. -/
theorem ruhig_bleibt (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (u : Faden) (hu : ruhig P (init u).1 = true) {M : RufMaschineG D}
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M) :
    M.faeden u = (RufStartG P sp init).faeden u := by
  induction hr with
  | start => rfl
  | schritt M M' v _ hs ih =>
      by_cases hvu : u = v
      · subst hvu
        exfalso
        refine kein_schritt_ruhig hs (by rw [ih, start_faden]) ?_
        rw [ih, start_faden]
        simp only [ruhig, Bool.and_eq_true] at hu
        exact hu.1.1
      · rw [rufSchrittG_fremd hs u hvu, ih]

/-- **Every carrier is local when every thread but `0` is idle**: only
    thread `0` steps, and an idle thread's only frame has an empty
    footprint. -/
theorem lokOk_einfaden (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hRuhe : ∀ u, u ≠ 0 → ruhig P (init u).1 = true) :
    LokOk P O passes (fun _ => true) sp init := by
  intro M M' u hr hs t htu F hF c hc _
  by_cases hu0 : u = 0
  · subst hu0
    have ht := ruhig_bleibt (O := O) (passes := passes) sp init t (hRuhe t htu) hr
    rw [ht, start_faden] at hF
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    subst hF
    have hleer := (sicher_mem.mp hc).1
    have hr0 := hRuhe t htu
    simp only [ruhig, Bool.and_eq_true, List.isEmpty_iff] at hr0
    rw [hr0.1.2] at hleer
    exact absurd hleer List.not_mem_nil
  · exfalso
    have hu := ruhig_bleibt (O := O) (passes := passes) sp init u (hRuhe u hu0) hr
    refine kein_schritt_ruhig hs (by rw [hu, start_faden]) ?_
    rw [hu, start_faden]
    have hr0 := hRuhe u hu0
    simp only [ruhig, Bool.and_eq_true] at hr0
    exact hr0.1.1

/-- With every thread but `0` idle the start is exclusive (idle roots hold
    no lock by signature). -/
theorem startExklusiv_einfaden (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hRuhe : ∀ u, u ≠ 0 → ruhig P (init u).1 = true) : StartExklusiv init := by
  intro t u htu L hLt hLu
  have leer : ∀ w, w ≠ 0 → D.haelt (init w).1 = [] := by
    intro w hw
    have h := hRuhe w hw
    simp only [ruhig, Bool.and_eq_true, List.isEmpty_iff] at h
    exact h.2
  by_cases ht0 : t = 0
  · subst ht0
    rw [leer u (fun h => htu h.symm)] at hLu
    exact List.not_mem_nil hLu
  · rw [leer t ht0] at hLt
    exact List.not_mem_nil hLt

end Ruhe

/-! ## 3. The theorem -/

/-- **ZIEL AM ORT FUER EINEN FADEN -- the goal theorem with lock
    invariants for programs with one active thread, WITHOUT a footprint
    check.** Every thread but `0` is idle (`ruhig`: a bare `return`, empty
    footprint, no signature lock); then only thread `0` ever steps, every
    carrier is stable for it, and the premises of `ziel_ort_sperre` lose
    `fussSperreB` and `StartExklusiv`. The conclusion is that of
    `ziel_ort_sperre`. -/
theorem ziel_ort_einfaden (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true)
    (hRuhe : ∀ u, u ≠ 0 → ruhig P (init u).1 = true)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M ∧ SperrInvG S M ∧ KeinLogikHaltG O passes M ∧
      ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
        AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M' := by
  intro M hr
  have hFS : ∀ f, FussS P S (fun _ => true) f := fussS_alle P S
  have hI := zielInvS_erreichbarL P O passes Q S (fun _ => true) sp init e0 hO hRL hQ hlok hS
    (programmImFragmentS_ok P S hvoll hFrag hFS) hFS (lokOk_einfaden sp init hRuhe) hK hStart
    hSstart (startExklusiv_einfaden init hRuhe) M hr
  have hP : KeinLogikHaltG O passes M :=
    fun t => fadenS_prueft hO hRL hQ hS hSstart hK hFS t (hI.1.1 t)
  exact ⟨fun t ev hev => hI.1.2 t ev hev, hI.2, hP, fun t hH hA => schritt_an_pruefung t (hP t) hH hA⟩

/-! ## CUTS:

  What is proved: a root frame at a `return` with an empty stack has no
  step (`kein_schritt_ruhig`); an idle thread stays at its start
  (`ruhig_bleibt`); with every thread but `0` idle every carrier is local
  (`lokOk_einfaden`) and the start is exclusive (`startExklusiv_einfaden`);
  `ziel_ort_einfaden`: the conclusion of `ziel_ort_sperre` without
  `fussSperreB` and `StartExklusiv`.

  What is NOT covered: several ACTIVE threads with thread-local carriers
  (a carrier read and written by one active thread only, while others run
  too) -- that needs the call graph per thread (SATZKARTE §14.6). Thread
  `0` is the active one by convention; any other numbering is a renaming
  not done here.
-/

#print axioms Gabbro.Grammatik.kein_schritt_ruhig
#print axioms Gabbro.Grammatik.lokOk_einfaden
#print axioms Gabbro.Grammatik.ziel_ort_einfaden

end Gabbro.Grammatik
