module
public import Bruecke.Kette.Andocken.Bild
public import Bruecke.Kette.Ohne.Lauf
@[expose] public section

/-!
# Units with locks: GabbroV's duties supply Stage 0's premise (b)

A unit that declares locks has Stage 0's lock family `sperrFamilie u` in its judged unit. Its
carried functions take no lock (the reader refuses `locks`), and `rumpf_ohne` proves that their
lowered bodies contain no `locks` block; by `koerperGutS_ohne` the lock-invariant duty of each
body is its plain duty. What remains of premise (b) is about the lock family itself:

* `SperrInvLokal (sperrFamilie u)`: every lock invariant reads only the carriers it protects;
* `StartPflicht.sperren`: every lock invariant holds in the initial memory.

Both are decided by Stage 0's own procedure `checkUnitLock` on the judged unit
(`sperrenGeprueftB`); `nutzerA_aus_compiled_sperren` takes that decision as its one premise
beyond the duties and the run facts of `nutzerA_aus_compiled`.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser
  Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Grammatik.Parser.Cover.Differenz

/-- The reason-exit invariant duty holds for every lock family when no invariant is declared. -/
theorem invGutGrund_leer {u : UProg} (hi : u.invs = []) (P : Programm (declOf u)) (passes : Nat)
    (Q : AxEns (declOf u)) (S : SperrInv (declOf u)) (c : (declOf u).Fn) :
    InvGutGrund P passes Q S c := by
  have hl : List.finRange u.invs.length = [] :=
    List.eq_nil_of_length_eq_zero (by rw [List.length_finRange, hi]; rfl)
  intro O hR hL hQ U hU R hRR hOV σ ρ hreq σ' r hrun i him
  have him' : i ∈ List.finRange u.invs.length := him
  rw [hl] at him'
  cases him'

/-- **The logic duty under any local lock family**, from the duties of a unit of carried
    functions: every lowered body is free of `locks`, so each body's duty under the family is its
    plain duty. -/
theorem logik_sperren {u : UProg} (hp : PflichtenEinheit u)
    {P : Programm (declOf u)} {fs : List (declOf u).Fn} (hlow : lowerAllg u = .ok (P, fs))
    (S : SperrInv (declOf u)) (hlok : SperrInvLokal S) :
    LogikPflicht P S (axWahr (declOf u)) := by
  obtain ⟨⟨hn, hs, ht⟩, rk, hf⟩ := hp
  have hS := getragenG_of_bools (stimmigB_of hs fun f hm => (hf f hm).1)
    (ohneTransitionB_of ht) (List.all_eq_true.mpr fun f hm => (hf f hm).2.1)
  have hZ : ∀ c : Fin u.fns.length, (fun _ => True) c → ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body := fun c _ => (hf (fnAt u c) (List.get_mem _ _)).2.2.2
  have M := massPflichtU_of_rang (rang_of (rangB_of fun f hm => (hf f hm).2.2.1)) hZ
  have hi : List.finRange u.invs.length = [] :=
    List.eq_nil_of_length_eq_zero (by rw [List.length_finRange, hS.toGetragen.ohneInv]; rfl)
  refine ⟨fun passes c => ⟨?_, invGutS_leer hi c, invGutGrund_leer hS.toGetragen.ohneInv P passes _ S c⟩,
    hlok, axEnsLokal_wahr⟩
  obtain ⟨body, hbody, _⟩ := hZ c True.intro
  exact koerperGutS_ohne S (rumpf_ohne hS.toGetragen hlow c True.intro hbody)
    ⟨koerperGutRQ_of_R _ (bruecke_koerperGutR_M hlow hS _ M passes c True.intro),
      bruecke_keineLogik_M hlow hS _ M passes _ c True.intro⟩

/-- **Premise (b) for Stage 0's judged unit of a unit with locks**, for every axiom family,
    initial memory, entry, further starts and checks: the duties of the unit, no foreign body,
    the lock invariants local and true in the initial memory. -/
theorem nutzerA_einheitDer_sperren {u : UProg} (hp : PflichtenEinheit u) (ha : u.axs = [])
    {P : Programm (declOf u)} {fs : List (declOf u).Fn} (hlow : lowerAllg u = .ok (P, fs))
    (Q : AxEns (declOf u)) (sp : Speicher (declOf u)) (main : (declOf u).Fn)
    (args : Env (declOf u) ((declOf u).params main))
    (roots gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w)))
    (checks : List (CheckDecl (declOf u)))
    (hlok : SperrInvLokal (sperrFamilie u)) (hinit : ∀ L, (sperrFamilie u).inv L sp = true) :
    NutzerPflichtA (Gabbro.Stage0.OldSource.einheitDer u P Q sp main args roots gestartet checks) := by
  have hax : ∀ a : (declOf u).Ax, False := fun a => by
    have := a.isLt
    simp only [ha, List.length_nil] at this
    exact Nat.not_lt_zero _ this
  have hn := hp.1.1
  have hf := hp.2
  obtain ⟨rk, hf⟩ := hf
  refine Zielsatz.nutzerPflichtA_ohne_atomar (declOf_scalar_kein_atomar u (nullB_statics hn)) ?_
  refine ⟨logikPflicht_Q hax (logik_sperren hp hlow _ hlok), ⟨hinit, fun a _ => ?_⟩⟩
  obtain ⟨w, ρ⟩ := a
  have hneeds : (fnAt u w).needs = [] := by
    have h1 := (hf (fnAt u w) (List.get_mem _ _)).1
    simp only [stimmigFnB, Bool.and_eq_true] at h1
    exact List.isEmpty_iff.mp h1.1.2
  show ReqAmEintritt P w _ ρ
  unfold ReqAmEintritt
  rw [requires_tru_of_needs_leer hlow w hneeds]
  rfl

/-! ## Stage 0's decision of the lock family -/

/-- Stage 0's own lock check (`checkUnitLock`, part of `checkUnitLogic`) accepts every lock. -/
def sperrenGeprueftB {D : Deklaration} (E : Einheit D) (locks : List D.Lock) : Bool :=
  locks.all fun L => (checkUnitLock E L).toOption.isSome

/-- **The decision is exact**: an accepted lock family is local and holds in the initial memory. -/
theorem sperren_of_geprueft {D : Deklaration} {E : Einheit D} {locks : List D.Lock}
    (hall : ∀ L, L ∈ locks) (h : sperrenGeprueftB E locks = true) :
    SperrInvLokal E.S ∧ ∀ L, E.S.inv L E.sp0 = true := by
  have hL : ∀ L, ∃ c, checkUnitLock E L = .ok c := fun L => by
    have := List.all_eq_true.mp h L (hall L)
    cases hc : checkUnitLock E L with
    | error e => rw [hc] at this; cases this
    | ok c => exact ⟨c, rfl⟩
  exact ⟨fun L s s' hs => by
      obtain ⟨c, _⟩ := hL L
      exact c.down.1 s s' hs,
    fun L => by
      obtain ⟨c, _⟩ := hL L
      exact c.down.2⟩

/-- **Premise (b) of Stage 0's image theorem for every compilation of a unit with locks**: the
    duties of the unit, the two run facts of `nutzerA_aus_compiled` and Stage 0's lock decision on
    the judged unit (the same procedure `checkUnitLogic` runs on the image's initial memory). -/
theorem nutzerA_aus_compiled_sperren {u : UProg} (hp : PflichtenEinheit u) (ha : u.axs = [])
    {text : String} {options : Gabbro.Stage0.Profil.Options}
    (c : Gabbro.Stage0.Compiled text options) (hu : c.unit = u)
    (hold : ohneAltGlobalB c.expanded = true)
    (Q : AxEns (declOf c.unit)) (sp : Speicher (declOf c.unit))
    (args : Env (declOf c.unit) ((declOf c.unit).params c.main))
    (roots gestartet : List (Σ w : (declOf c.unit).Fn, Env (declOf c.unit) ((declOf c.unit).params w)))
    (checks : List (CheckDecl (declOf c.unit)))
    (hlock : sperrenGeprueftB
      (Gabbro.Stage0.OldSource.einheitDer c.unit c.program Q sp c.main args roots gestartet checks)
      (List.finRange c.unit.locks.length) = true) :
    NutzerPflichtA (Gabbro.Stage0.OldSource.einheitDer c.unit c.program Q sp c.main args roots gestartet checks) := by
  obtain ⟨hlok, hinit⟩ := sperren_of_geprueft List.mem_finRange hlock
  obtain ⟨raw, fs, hlow, hr⟩ := c.lowered
  have hid := restore_ohneAlt _ c.unit raw c.gateExpansion hold
  rw [hid] at hr
  injection hr with hP
  revert hlok hinit
  rw [← hP]
  intro hlok hinit
  subst hu
  exact nutzerA_einheitDer_sperren hp ha hlow Q sp c.main args roots gestartet checks hlok hinit

#print axioms logik_sperren
#print axioms nutzerA_einheitDer_sperren
#print axioms nutzerA_aus_compiled_sperren

end Gabbro.Bruecke
