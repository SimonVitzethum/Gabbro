module
public import Bruecke.Zertifikat.Lauf
public import Grammatik.Logik.WP.HA.Zertifikat
public import Grammatik.Logik.Vertraege.Pruefer.Unit
@[expose] public section

/-!
# GabbroV's one theorem: the certificate of a compiled unit gives Stage 0's premise (b)

The model's certificate (`Logik/WP/HA/Zertifikat.lean`) names every logic duty of a unit, and
`logikPflichten_iff` proves that together they are EXACTLY premise (b), `NutzerPflichtA E`, for
every program. GabbroV states that certificate for the judged unit Stage 0 compiles
(`OldSource.einheitDer c.unit c.program …`), over the very program Stage 0 lowered: no reading of
the program into another language, no simulation per language form. Every form Stage 0 lowers is
covered by the same theorem.

The certificate splits into
* the logic of each function (`LogikFn`: its returns meet `ensures` and the owed invariants, no
  precondition stop, no logic stop, at every budget) -- the user's program logic;
* `AxLokalAn`: each foreign body's declared `ensures` reads only its write carriers -- part of
  the environment contract the user names;
* the data parts Stage 0's own checker decides on the judged unit (`entschiedenB`): every lock
  invariant local and true in the initial memory, every start's `requires` at the initial memory.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.WP
  Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Grammatik.Parser.Cover.Differenz

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

/-- Stage 0's own decision of the certificate's data parts on a unit: every lock (`checkUnitLock`)
    and every start's `requires` at the initial memory (`checkStartRequires`). -/
def entschiedenB {D : Deklaration} (E : Einheit D) (locks : List D.Lock) : Bool :=
  sperrenGeprueftB E locks &&
    (E.starts ++ E.gestartet).all fun a => (checkStartRequires E.P E.sp0 a).toOption.isSome

/-- **The decision is sound**: accepted data parts are the certificate's lock and start duties. -/
theorem entschieden_sound {D : Deklaration} {E : Einheit D} {locks : List D.Lock}
    (hall : ∀ L, L ∈ locks) (h : entschiedenB E locks = true) :
    (∀ L, SperrLokalAn E.S L) ∧ (∀ L, SperrAmStart E L) ∧
      ∀ a ∈ E.starts ++ E.gestartet, StartAmStart E a := by
  simp only [entschiedenB, Bool.and_eq_true] at h
  obtain ⟨hl, hs⟩ := h
  obtain ⟨hlok, hinit⟩ := sperren_of_geprueft hall hl
  refine ⟨fun L => hlok L, hinit, fun a ha => ?_⟩
  have := List.all_eq_true.mp hs a ha
  cases hc : checkStartRequires E.P E.sp0 a with
  | error e => rw [hc] at this; cases this
  | ok c => exact c.down

/-- **The logic of one function**: at every budget, its returns meet `ensures` and the owed
    invariants, it ends in no precondition stop under the gated call meaning, and in no logic stop
    under a call meaning without logic -- the three duties of the model's certificate. -/
def LogikFn {D : Deklaration} [DecidableEq D.Fn] (E : Einheit D) (f : D.Fn) : Prop :=
  ∀ passes, PflichtRueck E.P passes E.Q E.S (GeteiltA E.P E.ws) f ∧
    PflichtKeineVor E.P passes E.Q E.S (GeteiltA E.P E.ws) f ∧
    PflichtKeinHalt E.P passes E.Q E.S (GeteiltA E.P E.ws) f

/-- **The one theorem, for every unit**: the logic of every function, the foreign bodies' locality
    and Stage 0's decision of the data parts give premise (b). By `logikPflichten_iff` these
    premises are not stronger than (b) except for the decided parts, which (b) also contains. -/
theorem nutzerA_aus_logik {D : Deklaration} [DecidableEq D.Fn] (E : Einheit D) {locks : List D.Lock}
    (hall : ∀ L, L ∈ locks) (hf : ∀ f, LogikFn E f) (hax : ∀ a, AxLokalAn E.Q a)
    (hent : entschiedenB E locks = true) : NutzerPflichtA E := by
  obtain ⟨hS, hSt, hReq⟩ := entschieden_sound hall hent
  exact (logikPflichten_iff E).mp
    ⟨fun f p => (hf f p).1, fun f p => (hf f p).2.1, fun f p => (hf f p).2.2, hS, hax, hSt, hReq⟩

/-- **Conversely, premise (b) gives every function's logic and the foreign bodies' locality**:
    the duties GabbroV states are exactly what (b) asks, nothing more. -/
theorem logik_aus_nutzerA {D : Deklaration} [DecidableEq D.Fn] (E : Einheit D) (h : NutzerPflichtA E) :
    (∀ f, LogikFn E f) ∧ ∀ a, AxLokalAn E.Q a := by
  have hL := (logikPflichten_iff E).mpr h
  exact ⟨fun f p => ⟨hL.rueck f p, hL.keineVor f p, hL.keinHalt f p⟩, hL.axLokal⟩

/-- **Premise (b) of Stage 0's image theorem for every compilation, every language form**: the
    judged unit over the compiled program itself (`c.program`, after the restoration of
    `old(global)`), for every axiom family, initial memory, entry, starts and checks. -/
theorem nutzerA_aus_compiled_logik {text : String} {options : Gabbro.Stage0.Profil.Options}
    (c : Gabbro.Stage0.Compiled text options)
    (Q : AxEns (declOf c.unit)) (sp : Speicher (declOf c.unit))
    (args : Env (declOf c.unit) ((declOf c.unit).params c.main))
    (roots gestartet : List (Σ w : (declOf c.unit).Fn, Env (declOf c.unit) ((declOf c.unit).params w)))
    (checks : List (CheckDecl (declOf c.unit)))
    (hf : ∀ f, LogikFn
      (Gabbro.Stage0.OldSource.einheitDer c.unit c.program Q sp c.main args roots gestartet checks) f)
    (hax : ∀ a, AxLokalAn Q a)
    (hent : entschiedenB
      (Gabbro.Stage0.OldSource.einheitDer c.unit c.program Q sp c.main args roots gestartet checks)
      (List.finRange c.unit.locks.length) = true) :
    NutzerPflichtA (Gabbro.Stage0.OldSource.einheitDer c.unit c.program Q sp c.main args roots gestartet checks) :=
  nutzerA_aus_logik _ List.mem_finRange hf hax hent

#print axioms nutzerA_aus_logik
#print axioms logik_aus_nutzerA
#print axioms nutzerA_aus_compiled_logik


/-! ## The duties of a unit given as data, one per function -/

/-- **The duty of one function of the unit `u`**: its logic in the judged unit over the program the
    lowering builds from `u`, for every axiom family, memory, entry, starts and checks. -/
def ZielF (u : UProg) (f : Fin u.fns.length) : Prop :=
  ∀ (P : Programm (declOf u)) (fs : List (declOf u).Fn), lowerAllg u = .ok (P, fs) →
    ∀ (Q : AxEns (declOf u)) (sp : Speicher (declOf u)) (main : (declOf u).Fn)
      (args : Env (declOf u) ((declOf u).params main))
      (roots gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w)))
      (checks : List (CheckDecl (declOf u))),
      LogikFn (Gabbro.Stage0.OldSource.einheitDer u P Q sp main args roots gestartet checks) f

/-- The duty at a position (vacuous outside the unit), so that proofs collect over index lists. -/
def ZielI (u : UProg) (i : Nat) : Prop := ∀ h : i < u.fns.length, ZielF u ⟨i, h⟩

theorem zielI_nil {u : UProg} : ∀ i ∈ ([] : List Nat), ZielI u i := fun _ h => absurd h List.not_mem_nil

theorem zielI_cons {u : UProg} {i : Nat} {is : List Nat} (hi : ZielI u i) (hs : ∀ j ∈ is, ZielI u j) :
    ∀ j ∈ i :: is, ZielI u j := fun j hj => (List.mem_cons.mp hj).elim (fun h => h ▸ hi) (hs j)

theorem zielI_append {u : UProg} {xs ys : List Nat} (hx : ∀ j ∈ xs, ZielI u j) (hy : ∀ j ∈ ys, ZielI u j) :
    ∀ j ∈ xs ++ ys, ZielI u j := fun j hj => (List.mem_append.mp hj).elim (hx j) (hy j)

/-- Every function's duty, from the duties at the positions `0 … n-1`. -/
theorem alle_ziele {u : UProg} {n : Nat} (hn : u.fns.length = n) (h : ∀ i ∈ List.range n, ZielI u i) :
    ∀ f, ZielF u f := fun f => h f.val (List.mem_range.mpr (hn ▸ f.isLt)) f.isLt

/-- **Premise (b) of Stage 0's image theorem from the duties of the unit given as data**, every
    language form: the run facts `c.unit = u` and `ohneAltGlobalB c.expanded` (Stage 0's run),
    the foreign bodies' locality (part of the environment contract) and Stage 0's decision of the
    data parts. -/
theorem nutzerA_aus_ziele {u : UProg} (hz : ∀ f, ZielF u f)
    {text : String} {options : Gabbro.Stage0.Profil.Options}
    (c : Gabbro.Stage0.Compiled text options) (hu : c.unit = u)
    (hold : ohneAltGlobalB c.expanded = true)
    (Q : AxEns (declOf c.unit)) (sp : Speicher (declOf c.unit))
    (args : Env (declOf c.unit) ((declOf c.unit).params c.main))
    (roots gestartet : List (Σ w : (declOf c.unit).Fn, Env (declOf c.unit) ((declOf c.unit).params w)))
    (checks : List (CheckDecl (declOf c.unit)))
    (hax : ∀ a, AxLokalAn Q a)
    (hent : entschiedenB
      (Gabbro.Stage0.OldSource.einheitDer c.unit c.program Q sp c.main args roots gestartet checks)
      (List.finRange c.unit.locks.length) = true) :
    NutzerPflichtA (Gabbro.Stage0.OldSource.einheitDer c.unit c.program Q sp c.main args roots gestartet checks) := by
  refine nutzerA_aus_compiled_logik c Q sp args roots gestartet checks ?_ hax hent
  obtain ⟨raw, fs, hlow, hr⟩ := c.lowered
  have hid := restore_ohneAlt _ c.unit raw c.gateExpansion hold
  rw [hid] at hr
  injection hr with hP
  rw [← hP]
  subst hu
  exact fun f => hz f raw fs hlow Q sp c.main args roots gestartet checks

#print axioms nutzerA_aus_ziele

end Gabbro.Bruecke
