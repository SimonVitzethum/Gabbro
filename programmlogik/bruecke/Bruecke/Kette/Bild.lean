module
public import Bruecke.Kette.Stufe0
public import Stage0.Senke.Ausdruck.Old.JudgedUnit
@[expose] public section

/-!
# GabbroV's duties supply exactly the premise of Stage 0's image theorem

`nutzer_aus_stage0` gives premise (b) for the bridge's own unit (`einheitAllg`). Stage 0's image
theorem asks for `NutzerPflichtA (output.einheit Q)`: the program after the restoration of
`old(global)` postconditions, the lock family of the unit (`sperrFamilie`), every axiom-ensures
family `Q`, the image's initial memory and its entry `main` with the image's arguments. This
module closes that gap with no new premise beyond facts the run decides:

* `restore_ohneAlt`: when no source postcondition reads `old` of a static, the restoration
  returns the lowered program unchanged;
* `nutzerA_einheitDer`: for a unit that declares no lock and no foreign body, the duties of
  the unit give `NutzerPflichtA` of Stage 0's judged unit, for every `Q`, every initial
  memory and every entry;
* `nutzerA_aus_compiled`: hence for every compilation of the unit; `output.einheit Q` of an
  emitted image is that unit, so this is the image theorem's premise (b).
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser
  Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Grammatik.Parser.Cover.Differenz

/-! ## The restoration of `old(global)` -/

/-- No postcondition of the items reads `old` of a static (`OldSource.hasEntry`). -/
def ohneAltGlobalB (items : List SItemTief) : Bool :=
  items.all fun it => match it with
    | .fnT sig _ => sig.klauseln.all fun k => match k with
        | .gives e => !Gabbro.Stage0.OldSource.hasEntry e
        | _ => true
    | _ => true

theorem collect_ok : ∀ (n : Nat) (T : Fin n → Type) (get : (i : Fin n) → Except String (T i))
    (vals : (i : Fin n) → T i), (∀ i, get i = .ok (vals i)) →
      Gabbro.Stage0.OldSource.collect n T get = .ok vals
  | 0, _, _, vals, _ => by
    simp only [Gabbro.Stage0.OldSource.collect, pure, Except.pure]
    congr
    funext i
    exact i.elim0
  | n + 1, T, get, vals, h => by
    simp only [Gabbro.Stage0.OldSource.collect, h 0,
      collect_ok n (fun i => T i.succ) (fun i => get i.succ) (fun i => vals i.succ) (fun i => h i.succ),
      bind, Except.bind, pure, Except.pure]
    congr
    funext i
    cases i using Fin.cases <;> rfl

/-- **Without `old(global)` the restoration is the identity.** -/
theorem restore_ohneAlt (items : List SItemTief) (u : UProg) (P : Programm (declOf u))
    {expanded : List SItemTief} {requirements : List (STyp × String)}
    (hx : Modules.prepare items = .ok (expanded, requirements))
    (hb : ohneAltGlobalB expanded = true) :
    Gabbro.Stage0.OldSource.restore items u P = .ok P := by
  unfold Gabbro.Stage0.OldSource.restore
  have hx' : expandU items = .ok (expanded, requirements) := hx
  simp only [hx', bind, Except.bind]
  rw [collect_ok _ _ _ P.ensures (fun f => ?_)]
  · rfl
  unfold Gabbro.Stage0.OldSource.atFunction
  have hsrc : (Gabbro.Stage0.OldSource.clauses (Gabbro.Stage0.OldSource.koepfeVon expanded)
      (fnAt u f).name).any Gabbro.Stage0.OldSource.hasEntry = false := by
    unfold Gabbro.Stage0.OldSource.clauses
    split
    · rename_i sig hsig
      have hmem := List.mem_of_find?_eq_some hsig
      obtain ⟨it, hit, hsome⟩ := List.mem_filterMap.mp hmem
      have hall := List.all_eq_true.mp hb it hit
      cases it with
      | fnT s body =>
        simp only [Option.some.injEq] at hsome
        subst hsome
        simp only at hall
        rw [List.any_eq_false]
        intro e he
        obtain ⟨k, hk, hke⟩ := List.mem_filterMap.mp he
        have hkall := List.all_eq_true.mp hall k hk
        cases k <;> simp_all
      | _ => simp at hsome
    · rfl
  simp only [hsrc, Bool.not_false, if_true]
  rfl

open Gabbro.Stage0 in
/-- The run fact `hold` of `nutzerA_aus_compiled`, computed as Stage 0 computes its expanded
    items (the steps of `compile` up to `Modules.prepare`); checked in the generated
    `Pruefung` module by running it. -/
def stufe0AltFreiB (text : String) (options : Profil.Options := {}) : Bool :=
  match Frontend.source text options with
  | .error _ => false
  | .ok source =>
    match Modules.prepare (pre108 source.prepared.elaborierbar) with
    | .ok (expanded, _) => ohneAltGlobalB expanded
    | .error _ => false

/-! ## The judged unit of Stage 0 -/

theorem axVertrag_leer {D : Deklaration} (hax : ∀ a : D.Ax, False) (Pre : AxPre D) (Q : AxEns D)
    (O : Orakel D) : AxVertragOP Pre Q O := fun a => (hax a).elim

/-- Without foreign bodies the axiom-ensures family is irrelevant to the logic duty. -/
theorem logikPflicht_Q {D : Deklaration} {P : Programm D} {S : SperrInv D} {Q Q' : AxEns D}
    (hax : ∀ a : D.Ax, False) (h : LogikPflicht P S Q) : LogikPflicht P S Q' := by
  obtain ⟨hf, hS, _⟩ := h
  refine ⟨fun passes f => ⟨⟨fun O' hr hl _ => (hf passes f).1.1 O' hr hl (axVertrag_leer hax _ _ _),
      fun O' hr hl _ => (hf passes f).1.2 O' hr hl (axVertrag_leer hax _ _ _)⟩,
    fun O' hr hl _ => (hf passes f).2.1 O' hr hl (axVertrag_leer hax _ _ _),
    fun O' hr hl _ => (hf passes f).2.2 O' hr hl (axVertrag_leer hax _ _ _)⟩, hS, fun a => (hax a).elim⟩

/-- Without lock declarations the unit's lock family is the empty family. -/
theorem sperrFamilie_leer {u : UProg} (hl : u.locks = []) : sperrFamilie u = SperrInv.leer (declOf u) := by
  have hL : ∀ L : (declOf u).Lock, False := fun L => by
    have := L.isLt
    simp only [hl, List.length_nil] at this
    exact Nat.not_lt_zero _ this
  unfold sperrFamilie SperrInv.leer
  congr 1 <;> funext L <;> exact (hL L).elim

/-- **Premise (b) for Stage 0's judged unit**, from the duties of the unit, for every axiom
    family, every initial memory, every entry, every further start and every declared check list,
    when the unit declares no lock and no foreign body. -/
theorem nutzerA_einheitDer {u : UProg} (hp : PflichtenEinheit u) (hl : u.locks = []) (ha : u.axs = [])
    {P : Programm (declOf u)} {fs : List (declOf u).Fn} (hlow : lowerAllg u = .ok (P, fs))
    (Q : AxEns (declOf u)) (sp : Speicher (declOf u)) (main : (declOf u).Fn)
    (args : Env (declOf u) ((declOf u).params main))
    (roots gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w)))
    (checks : List (CheckDecl (declOf u))) :
    NutzerPflichtA (Gabbro.Stage0.OldSource.einheitDer u P Q sp main args roots gestartet checks) := by
  have hax : ∀ a : (declOf u).Ax, False := fun a => by
    have := a.isLt
    simp only [ha, List.length_nil] at this
    exact Nat.not_lt_zero _ this
  obtain ⟨hn, hb⟩ := nutzer_aus_senkung hp hlow
  have hfns := hp.2
  obtain ⟨rk, hf⟩ := hfns
  refine Zielsatz.nutzerPflichtA_ohne_atomar (declOf_scalar_kein_atomar u (nullB_statics hn)) ?_
  refine ⟨?_, ⟨fun L => ?_, fun a ha' => ?_⟩⟩
  · show LogikPflicht P (sperrFamilie u) Q
    rw [sperrFamilie_leer hl]
    exact logikPflicht_Q hax hb.logik
  · have := L.isLt
    simp only [hl, List.length_nil] at this
    exact (Nat.not_lt_zero _ this).elim
  · obtain ⟨w, ρ⟩ := a
    have hneeds : (fnAt u w).needs = [] := by
      have h1 := (hf (fnAt u w) (List.get_mem _ _)).1
      simp only [stimmigFnB, Bool.and_eq_true] at h1
      exact List.isEmpty_iff.mp h1.1.2
    show ReqAmEintritt P w _ ρ
    unfold ReqAmEintritt
    rw [requires_tru_of_needs_leer hlow w hneeds]
    rfl

/-- **Premise (b) of Stage 0's image theorem for every compilation of the unit**: Stage 0's judged
    unit over the compiled (restored) program, for every axiom family, initial memory, entry
    arguments, further starts and declared checks. An emitted image's `output.einheit Q` and
    `output.goalUnit Q` are this unit at the image's memory, entry, starts and checks, so this is
    the premise `NutzerPflichtA (output.einheit Q)` (and `(output.goalUnit Q)`) of the image theorems. The two run facts are the premises: `hu` (the compiled unit is `u`) and
    `hold` (a Bool of the run's expanded items). -/
theorem nutzerA_aus_compiled {u : UProg} (hp : PflichtenEinheit u) (hl : u.locks = []) (ha : u.axs = [])
    {text : String} {options : Gabbro.Stage0.Profil.Options}
    (c : Gabbro.Stage0.Compiled text options) (hu : c.unit = u)
    (hold : ohneAltGlobalB c.expanded = true)
    (Q : AxEns (declOf c.unit)) (sp : Speicher (declOf c.unit))
    (args : Env (declOf c.unit) ((declOf c.unit).params c.main))
    (roots gestartet : List (Σ w : (declOf c.unit).Fn, Env (declOf c.unit) ((declOf c.unit).params w)))
    (checks : List (CheckDecl (declOf c.unit))) :
    NutzerPflichtA (Gabbro.Stage0.OldSource.einheitDer c.unit c.program Q sp c.main args roots gestartet checks) := by
  obtain ⟨raw, fs, hlow, hr⟩ := c.lowered
  have hid := restore_ohneAlt _ c.unit raw c.gateExpansion hold
  rw [hid] at hr
  injection hr with hP
  rw [← hP]
  subst hu
  exact nutzerA_einheitDer hp hl ha hlow Q sp c.main args roots gestartet checks

#print axioms nutzerA_einheitDer
#print axioms nutzerA_aus_compiled

end Gabbro.Bruecke
