/-
  File:      Grammatik/Zielsatz/RuheLift/Grenze.lean
  Subject:   **Runs of one thread of `P` beside runs of `P.mitRuhe`, at statement boundaries** (the idle-root lift,
             part 1). The goal theorem speaks about machine G of `P.mitRuhe` (the program with the runtime's idle root
             `none`), started by `initEin thr f rho`: thread `thr` runs the declared start `some f`, every other thread
             the idle root. `RandRuhe thr f rho s0 eb M σ ρ` says that such a machine `M` stands at the boundary in
             front of the end block `eb` of the body of `f`, TRANSLATED: thread `thr` runs its root frame with the
             residue `.ende (ruEnd eb)`, the translated environment `envR ρ` and the translated world `worldR σ`; its
             holdings tie the translated static resources; every other thread holds no lock and has an empty trace.
             * `randRuhe_start`: the start machine stands at the first boundary of `f`'s body (`f` holds no lock by
               signature).
             * `randRuhe_schritt`: across one call-free covered statement `s` (`StmtR … (fun _ => False)`) whose
               sequential run in `D` ends normally at `σ1`, `ρ1`, thread `thr` of the machine of `P.mitRuhe` reaches,
               by its own steps, the boundary behind `s` at `worldR σ1`, `envR ρ1`. The proof is not a step-by-step
               simulation of the 80 rules: the big-step run of `ruS s` in `D.mitRuhe` is the translated run of `s`
               (`execStmt_ru`), and the adequacy of the machine for the call-free fragment (`stmtOkR`,
               `endeConsOkR`), applied to `P.mitRuhe`, realises it by steps of `thr`.
             * `Zerlegt` is the decomposed call-free prefix of a body (the grammar-side form of the image theorem's
               `Zerlegung`), `randRuhe_zerlegt` lifts it boundary by boundary.
-/
module
public import Grammatik.Zielsatz.RuheLift.Fragment
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T6
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik
@[expose] public section

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration}

/-! ## The start of `P.mitRuhe` with one running thread -/

/-- Thread `thr` starts the declared start `f` with `ρ`; every other thread starts the runtime's idle root. -/
def initEin (thr : Faden) (f : D.Fn) (ρ : Env D (D.params f)) :
    Faden → Σ g : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params g) :=
  fun t => if t = thr then ⟨some f, envR ρ⟩ else ⟨none, .nil⟩

theorem initEin_gleich {thr t : Faden} {f : D.Fn} {ρ : Env D (D.params f)} (h : t = thr) :
    initEin thr f ρ t = ⟨some f, envR ρ⟩ := by
  subst h
  exact if_pos rfl

theorem initEin_sonst {thr t : Faden} {f : D.Fn} {ρ : Env D (D.params f)} (h : t ≠ thr) :
    initEin thr f ρ t = ⟨none, .nil⟩ :=
  if_neg h

/-- Thread `t` of the start machine whose start `init t` is `⟨g, rho⟩`. -/
theorem rufStartG_faden_init (P : Programm D) (sp : Speicher D)
    {init : Faden → Σ f : D.Fn, Env D (D.params f)} {t : Faden} {g : D.Fn} {rho : Env D (D.params g)}
    (h : init t = ⟨g, rho⟩) :
    (RufStartG P sp init).faeden t =
      ⟨[], ⟨g, rho, sp.welt [],
        ⟨false, D.params g, Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩,
       startSpur g, [RufEreignisF.eintritt g rho (sp.welt [])]⟩ := by
  unfold RufStartG
  dsimp only
  generalize init t = start at h ⊢
  cases h
  rfl

/-- The trace a thread starts with: its start function's signature locks. -/
theorem rufStartG_spur_init (P : Programm D) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (t : Faden) : ((RufStartG P sp init).faeden t).spur = startSpur (init t).1 := by
  cases hx : init t with
  | mk g rho => rw [rufStartG_faden_init P sp hx] <;> rfl

/-- Every thread but `thr` starts with the empty trace: the idle root holds no lock. -/
theorem initEin_spur (P : Programm D) (sp : Speicher D) {thr t : Faden} {f : D.Fn} (rho : Env D (D.params f))
    (ht : t ≠ thr) : ((RufStartG P.mitRuhe (speicherR sp) (initEin thr f rho)).faeden t).spur = [] := by
  rw [rufStartG_spur_init, initEin_sonst ht]
  rfl

/-- A frame whose residue is a transported end block is the frame of the end block itself. -/
theorem rahmen_umΛ {f' : D.Fn} {rho' : Env D (D.params f')} {s0' : World D} {l : Bool} {Γ : Ctx}
    {Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂) (ρ : Env D Γ) (e : Endblock D (vertragVon D f') l Γ Λ₁) :
    (⟨f', rho', s0', ⟨l, Γ, Λ₂, ρ, .ende (Endblock.umΛ h e)⟩⟩ : RufRahmenG D) =
      ⟨f', rho', s0', ⟨l, Γ, Λ₁, ρ, .ende e⟩⟩ := by
  subst h
  rfl

/-- No thread but `thr` holding a lock, `thr` is free to take any lock. -/
theorem freiA_ruhig {M : RufMaschineG D} {thr : Faden} (A : D.Lock → Prop)
    (h : ∀ t, t ≠ thr → (M.faeden t).spur = []) : FreiA A M thr := by
  intro L _ t ht hL
  rw [h t ht] at hL
  exact List.not_mem_nil hL

/-! ## The handler of `D.mitRuhe` beside a handler of `D` -/

/-- A handler of `D.mitRuhe` answering a translated call of `g` with the translated answer of `R`; the idle root,
    which no translated statement calls, answers `logik schleife`. -/
def rufRuH (R : ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g) :
    ∀ g : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params g) → RufAusgang g
  | some g, σ, ρ => rufR (R g (worldZ σ) (envZ (Γ := D.params g) ρ))
  | none, _, _ => .logik .schleife

theorem rufRu_rufRuH (R : ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g) : RufRu R (rufRuH R) := by
  intro g σ ρ
  show rufR (R g (worldZ (worldR σ)) (envZ (Γ := D.params g) (envR ρ))) = rufR (R g σ ρ)
  rw [worldZ_worldR, envZ_envR (Γ := D.params g) ρ]

/-! ## The boundary relation -/

/-- **Machine `M` of `P.mitRuhe` at the translated boundary** in front of `eb` of the body of `f`: thread `thr` runs
    its root frame of `some f` (entry environment `envR rho`, entry world `worldR s0`) with the residue
    `.ende (ruEnd eb)`, the environment `envR ρ` and the world `worldR σ`; its holdings tie the translated static
    resources; every other thread has an empty trace (it holds no lock). -/
def RandRuhe (thr : Faden) (f : D.Fn) (rho : Env D (D.params f)) (s0 : World D) {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (eb : Endblock D (vertragVon D f) l Γ Λ) (M : RufMaschineG D.mitRuhe) (σ : World D)
    (ρ : Env D Γ) : Prop :=
  (∃ log, ZustandG M thr [] (some f) (envR rho) (worldR s0) log (envR ρ) (.ende (ruEnd eb)) (worldR σ)) ∧
    HeldB (vertragVon D.mitRuhe (some f)).boden (Λ.map resR) (offen (worldR σ).spur) ∧
    ∀ t, t ≠ thr → (M.faeden t).spur = []

/-- **The start machine of `P.mitRuhe` under `initEin` stands at the first boundary of `f`'s body.** -/
theorem randRuhe_start (P : Programm D) (sp : Speicher D) (thr : Faden) {f : D.Fn} (rho : Env D (D.params f))
    (hf : D.haelt f = []) :
    RandRuhe thr f rho (sp.welt []) (P.rumpf f) (RufStartG P.mitRuhe (speicherR sp) (initEin thr f rho))
      (sp.welt []) rho := by
  have hs : startSpur (D := D.mitRuhe) (some f) = [] := by
    simp only [startSpur, show D.mitRuhe.haelt (some f) = [] from hf, nimmtAlle]
  refine ⟨⟨[RufEreignisF.eintritt (D := D.mitRuhe) (some f) (envR rho) ((speicherR sp).welt [])], ?_, rfl⟩,
    ⟨fun L hL => ?_, fun L hL => ?_⟩, fun t ht => initEin_spur P sp rho ht⟩
  · rw [rufStartG_faden_init P.mitRuhe (speicherR sp) (init := initEin thr f rho)
      (initEin_gleich (thr := thr) (f := f) (ρ := rho) rfl), hs]
    exact congrArg (fun k => (⟨[], k, [], [RufEreignisF.eintritt (D := D.mitRuhe) (some f) (envR rho)
        ((speicherR sp).welt [])]⟩ : RufFadenG D.mitRuhe))
      (rahmen_umΛ (D := D.mitRuhe) (f' := some f) (rho' := envR rho) (s0' := (speicherR sp).welt [])
        (anfang_map (D.signatur f)) (envR rho) (ruEnd (P.rumpf f)))
  · have hL' : Res.held (D := D) L ∈ Signatur.anfang D (D.signatur f) := mem_map_rm.mp hL
    have h' := (held_anfang (D.signatur f) L).mp hL'
    rw [show (D.signatur f).haelt = [] from hf] at h'
    exact (List.not_mem_nil h').elim
  · change L ∈ ([] : List D.Lock) at hL
    exact (List.not_mem_nil hL).elim

/-- **One call-free statement, translated**: from the translated boundary in front of `s`, whose sequential run in
    `D` ends normally at `σ1`, `ρ1`, thread `thr` of the machine of `P.mitRuhe` reaches by its own steps the
    translated boundary behind `s`. -/
theorem randRuhe_schritt (P : Programm D) (O : Orakel D) (passes : Nat)
    (R : ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g) {thr : Faden} {f : D.Fn}
    {rho : Env D (D.params f)} {s0 : World D} {Agl : D.Lock → Prop} {mr l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {s : Stmt D (vertragVon D f) l Γ Λ Λ'} {rest : Endblock D (vertragVon D f) l Γ Λ'}
    {M : RufMaschineG D.mitRuhe} {σ σ1 : World D} {ρ ρ1 : Env D Γ}
    (hs : StmtR Agl (fun _ => False) mr s) (hex : execStmt O passes R s σ ρ = .ok σ1 ρ1)
    (h : RandRuhe thr f rho s0 (.cons s rest) M σ ρ) :
    ∃ M', RufLaufG P.mitRuhe O.mitRuhe passes thr M M' ∧ RandRuhe thr f rho s0 rest M' σ1 ρ1 := by
  obtain ⟨⟨log, hZ⟩, hΛ, hO⟩ := h
  simp only [ruEnd] at hZ
  have hs' := stmtR_ru hs
  have hex' : execStmt O.mitRuhe passes (rufRuH R) (ruS s) (worldR σ) (envR ρ) =
      .ok (worldR σ1) (envR ρ1) := by
    have e := execStmt_ru O passes R (rufRuH R) (rufRu_rufRuH R) s σ ρ
    rw [hex] at e
    exact e
  have hRuf : RufOk P.mitRuhe O.mitRuhe passes thr Agl (rufRuH R) (fun _ => False) :=
    ⟨fun _ hC => (hC : False).elim, fun _ hC => (hC : False).elim⟩
  have hA : FreiA (D := D.mitRuhe) Agl M thr := freiA_ruhig (D := D.mitRuhe) Agl hO
  obtain ⟨M', ext, hl, hZ', ho⟩ := endeConsOkR P.mitRuhe O.mitRuhe passes thr (some f) [] (envR rho)
    (worldR s0) Agl (rufRuH R) (fun _ => False) hRuf hs'
    (stmtOkR P.mitRuhe O.mitRuhe passes thr (some f) [] (envR rho) (worldR s0) Agl (rufRuH R)
      (fun _ => False) hRuf (ruS s) hs')
    (worldR σ) (worldR σ1) (envR ρ) (envR ρ1) hex' M (ruEnd rest) hZ hΛ hA
  refine ⟨M', hl, ⟨ext ++ log, hZ'⟩, ?_, fun t ht => ?_⟩
  · rw [ho]
    exact heldB_iff (fun L => (ruS s).held_iff L) hΛ
  · rw [rufLaufG_fremd hl t ht]
    exact hO t ht

/-! ## The decomposed call-free prefix -/

/-- **The decomposed call-free prefix of a body** (the grammar-side form of the image theorem's `Zerlegung`, with no
    admitted callee): from `eb` at world `σ` and environment `ρ`, statements of the call-free fragment
    (`StmtR Agl (fun _ => False)`) whose sequential runs end normally, up to the end block `ebe` at `σe`, `ρe`. -/
inductive Zerlegt (O : Orakel D) (passes : Nat) (R : ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g)
    (Agl : D.Lock → Prop) {V : Vertrag D} {l : Bool} {Γ : Ctx} :
    {Λ : List (Res D)} → Endblock D V l Γ Λ → World D → Env D Γ →
    {Λe : List (Res D)} → Endblock D V l Γ Λe → World D → Env D Γ → Prop where
  | halt {Λ : List (Res D)} (eb : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
      Zerlegt O passes R Agl eb σ ρ eb σ ρ
  | schritt {mr : Bool} {Λ Λ' Λe : List (Res D)} (s : Stmt D V l Γ Λ Λ') (rest : Endblock D V l Γ Λ')
      (ebe : Endblock D V l Γ Λe) (σ σ1 σe : World D) (ρ ρ1 ρe : Env D Γ)
      (hs : StmtR Agl (fun _ => False) mr s) (hex : execStmt O passes R s σ ρ = .ok σ1 ρ1)
      (hk : Zerlegt O passes R Agl rest σ1 ρ1 ebe σe ρe) :
      Zerlegt O passes R Agl (.cons s rest) σ ρ ebe σe ρe

/-- Two decomposed prefixes, one behind the other, are one. -/
theorem Zerlegt.trans {O : Orakel D} {passes : Nat}
    {R : ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g} {Agl : D.Lock → Prop} {V : Vertrag D}
    {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} {eb : Endblock D V l Γ Λ} {eb' : Endblock D V l Γ Λ'}
    {eb'' : Endblock D V l Γ Λ''} {σ σ' σ'' : World D} {ρ ρ' ρ'' : Env D Γ}
    (h1 : Zerlegt O passes R Agl eb σ ρ eb' σ' ρ') :
    Zerlegt O passes R Agl eb' σ' ρ' eb'' σ'' ρ'' → Zerlegt O passes R Agl eb σ ρ eb'' σ'' ρ'' := by
  induction h1 with
  | halt => exact id
  | schritt s rest _ σ σ1 _ ρ ρ1 _ hs hex _ ih =>
      exact fun h2 => Zerlegt.schritt s rest _ σ σ1 _ ρ ρ1 _ hs hex (ih h2)

/-- **The decomposed prefix, translated**: from the translated boundary in front of a decomposed call-free prefix,
    thread `thr` of the machine of `P.mitRuhe` reaches by its own steps the translated boundary behind it. -/
theorem randRuhe_zerlegt (P : Programm D) (O : Orakel D) (passes : Nat)
    (R : ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g) {thr : Faden} {f : D.Fn}
    {rho : Env D (D.params f)} {s0 : World D} {Agl : D.Lock → Prop} {l : Bool} {Γ : Ctx} {Λ Λe : List (Res D)}
    {eb : Endblock D (vertragVon D f) l Γ Λ} {ebe : Endblock D (vertragVon D f) l Γ Λe} {σ σe : World D}
    {ρ ρe : Env D Γ} (hk : Zerlegt O passes R Agl eb σ ρ ebe σe ρe) :
    ∀ {M : RufMaschineG D.mitRuhe}, RandRuhe thr f rho s0 eb M σ ρ →
      ∃ Me, RufLaufG P.mitRuhe O.mitRuhe passes thr M Me ∧ RandRuhe thr f rho s0 ebe Me σe ρe := by
  induction hk with
  | halt =>
      intro M h
      exact ⟨M, RufLaufG.refl M, h⟩
  | schritt _ _ _ _ _ _ _ _ _ hs hex _ ih =>
      intro M h
      obtain ⟨M1, hl1, h1⟩ := randRuhe_schritt P O passes R hs hex h
      obtain ⟨Me, hl2, h2⟩ := ih h1
      exact ⟨Me, hl1.trans hl2, h2⟩

/-- Steps of one thread continue a reachable machine to a reachable machine. -/
theorem rufErreichbarG_von_lauf {P : Programm D} {O : Orakel D} {passes : Nat} {M0 M M' : RufMaschineG D}
    {thr : Faden} (hl : RufLaufG P O passes thr M M') :
    RufErreichbarG P O passes M0 M → RufErreichbarG P O passes M0 M' := by
  induction hl with
  | refl => exact id
  | schritt hs _ ih => exact fun h => ih (RufErreichbarG.schritt _ _ thr h hs)

end Gabbro.Grammatik.Zielsatz
