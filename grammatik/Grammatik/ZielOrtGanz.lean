/-
  File:      Grammatik/ZielOrtGanz.lean
  Subject:   THE ONE GOAL THEOREM `ziel_ort_ganz` -- callee frames, registers
             and `awaits`, declared axiom ensures, AND the stuck hole closed:
             the user obligation now excludes every `logik` outcome of the
             body, and the conclusion says that no reachable machine is
             stuck at a `logik` check of G.

  The hole (verdict `messung/URTEIL-OPUS-2026-09-13.md`, probe A): machine G
  checks a loop invariant (`travNext`/`travDone`/`ewigWeiter`/
  `dannLeaveTrav`) and a `state` pre-state (`uebergang`, a leaf that `blatt`
  fires only on an `ok` outcome) and BLOCKS where the check fails. The old
  obligation `KoerperGutR` constrains `zurueck` outcomes and the
  `vorbedingung` outcome only; a body that runs into `logik schleife` meets
  it vacuously, G stops before any return is logged, and `VertragAmOrtG`
  holds on every reachable machine -- while the emitted C, which does not
  check invariants, runs on and returns with every `ensures` false.

  The repair keeps the obligation a SEQUENTIAL per-function triple against
  handlers (the user's own logic): `KeineLogik` asks that the body, run from
  its `requires` against any frame-respecting handler that itself answers
  no `logik` outcome (`OhneLogik`), never ends in a `logik` outcome. Since a
  body's own `logik` outcomes are exactly the loop invariant (`schleife`)
  and the pre-state (`vorzustand`) -- `nachbedingung`, `invariante`,
  `abstieg` and `vorbedingung` arise only in a CALL (`rufAt`, `torRuf`),
  i.e. in the handler -- this is "the loop invariants hold where they are
  checked and every transition finds its pre-state", nothing more. The
  replay then gives: the head's sequential prediction is never a `logik`
  outcome (`kopfR_keineLogik`), and at every `logik` check of G the check
  passes at the machine world (`KeinLogikHaltG`).
-/
import Grammatik.ZielOrtRahmen

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The obligation -/

/-- A handler that answers no `logik` outcome: a callee that met its own
    obligation, seen from the caller. -/
def OhneLogik (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)) (e : Logik D), R g σ ρ ≠ RufAusgang.logik e

/-- **The body never ends in a `logik` outcome of its own.** From every
    entry world at which `requires f` holds, against every oracle that
    respects the declared axiom frames, is register-local and meets the
    declared axiom ensures `Q`, and every handler that respects the callees'
    contracts and frames and answers no `logik` outcome, the body's result
    is not `logik e` for any `e`: its loop invariants hold at every boundary
    and every `state` transition finds its pre-state. A statement over the
    SEQUENTIAL semantics of `f`'s body only. -/
def KeineLogik (P : Programm D) (passes : Nat) (Q : AxEns D) (f : D.Fn) : Prop :=
  ∀ O' : Orakel D, RahmenO O' → RegLokal O' → AxVertragO Q O' →
  ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
    RespektiertRahmen P R → OhneLogik R →
    ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ →
      ∀ e : Logik D, execEnd (V := vertragVon D f) O' passes R (P.rumpf f) σ ρ ≠ EndAusgang.logik e

/-- **THE USER OBLIGATION OF THE GOAL THEOREM, one per function.** The body
    triple and the caller duty against frame-respecting handlers and the
    oracles meeting the declared axiom ensures (`KoerperGutRQ`), and no
    `logik` outcome of the body (`KeineLogik`). -/
def KoerperGutZ (P : Programm D) (passes : Nat) (Q : AxEns D) (f : D.Fn) : Prop :=
  KoerperGutRQ P passes Q f ∧ KeineLogik P passes Q f

/-! ## 2. The record handler that answers no `logik` outcome -/

/-- The handler of a record, with a HARDWARE default at an unrecorded key
    (`rufAusV` answers `logik (abstieg _)` there, which the new clause could
    not be applied to). -/
noncomputable def rufAusL (H : List (EintragV D)) :
    ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g :=
  fun g σ ρ =>
    haveI := Classical.propDecidable (∃ a : RufAusgang g, (⟨g, σ, ρ, a⟩ : EintragV D) ∈ H)
    if h : ∃ a : RufAusgang g, (⟨g, σ, ρ, a⟩ : EintragV D) ∈ H then Classical.choose h
    else .hardware .ieee

theorem rufAusL_passt {H : List (EintragV D)} (hf : FunkV H) : PasstV (rufAusL H) H := by
  intro g σ ρ a hmem
  have hex : ∃ a : RufAusgang g, (⟨g, σ, ρ, a⟩ : EintragV D) ∈ H := ⟨a, hmem⟩
  simp only [rufAusL, dif_pos hex]
  exact hf g σ ρ _ a (Classical.choose_spec hex) hmem

theorem rufAusL_mem {H : List (EintragV D)} {g : D.Fn} {σ : World D} {ρ : Env D (D.params g)}
    {a : RufAusgang g} (h : rufAusL H g σ ρ = a) (hne : ∀ e, a ≠ .hardware e) :
    (⟨g, σ, ρ, a⟩ : EintragV D) ∈ H := by
  unfold rufAusL at h
  split at h
  · rename_i hex
    rw [← h]
    exact Classical.choose_spec hex
  · exact absurd h.symm (hne _)

theorem rufAusL_rahmen {P : Programm D} {H : List (EintragV D)} (hv : VertraegeOkR P H) :
    RespektiertRahmen P (rufAusL H) := by
  refine ⟨fun g σ ρ _ σ' v h => ?_, fun g σ ρ σ' v h => ?_⟩
  · exact (hv.1 g σ ρ _ (rufAusL_mem h (fun e he => by cases he))).2.1 σ' v rfl
  · exact hv.2 g σ ρ _ (rufAusL_mem h (fun e he => by cases he)) σ' v rfl

theorem rufAusL_ohneLogik {P : Programm D} {H : List (EintragV D)} (hv : VertraegeOkV P H) :
    OhneLogik (rufAusL H) := by
  intro g σ ρ e h
  unfold rufAusL at h
  split at h
  · rename_i hex
    exact (hv g σ ρ _ (Classical.choose_spec hex)).2.2 e h
  · cases h

/-! ## 3. The replay carries it: the head never predicts a `logik` outcome -/

section Kopf

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D}

/-- **The head's prediction is never a `logik` outcome.** From the replay
    of a head frame (`KopfR`) and the obligation `KeineLogik`: the residue,
    run from the replay's sequential world against the record handler with
    hardware default and the record oracle, does not end in `logik e` --
    else the whole body would (`ZErg.folgt_logik`), against a handler and
    an oracle in the class of `KeineLogik`. -/
theorem kopfR_keineLogik (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hL : ∀ f, KeineLogik P passes Q f) {F : RufRahmenG D} {W : World D}
    (hG : KopfR P O passes Q F W) :
    ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (σ : World D),
      GleichAuf (fussOrteG P F.f) σ W ∧ F.rest.2.2.2.2.okG P (fussOrteG P F.f) ∧
      ∀ e : Logik D,
        semV (orakelAus O HA) passes (rufAusL H) F.rest.2.2.2.2 σ F.rest.2.2.2.1 ≠ .logik e := by
  obtain ⟨H, HA, σ, hreq, hf, hv, _, hfa, hra, hqa, _, hg, hok, heq⟩ := hG
  refine ⟨H, HA, σ, hg, hok, fun e he => ?_⟩
  have h1 := heq (rufAusL H) (orakelAus O HA) (rufAusL_passt hf) (orakelAus_passt O hfa)
    (gleichRS_orakelAus O HA)
  rw [he] at h1
  exact hL F.f (orakelAus O HA) (orakelAus_rahmen hO hra) (regLokal_orakelAus hRL HA)
    (orakelAus_vertrag hQ hqa) (rufAusL H) (rufAusL_rahmen hv) (rufAusL_ohneLogik hv.1) F.s0 F.rho
    hreq e (zErg_gleich_logik (ZErg.folgt_logik h1))

/-- The same, for a residue named by its shape. -/
theorem kopfR_keineLogik' (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hL : ∀ f, KeineLogik P passes Q f) {F : RufRahmenG D} {W : World D}
    (hG : KopfR P O passes Q F W) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D F.f) l Γ Λ} (hr : F.rest = ⟨l, Γ, Λ, ρ, r⟩) :
    ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (σ : World D),
      GleichAuf (fussOrteG P F.f) σ W ∧ r.okG P (fussOrteG P F.f) ∧
      ∀ e : Logik D, semV (orakelAus O HA) passes (rufAusL H) r σ ρ ≠ .logik e := by
  obtain ⟨H, HA, σ, hg, hok, hno⟩ := kopfR_keineLogik hO hRL hQ hL hG
  rw [hr] at hok hno
  exact ⟨H, HA, σ, hg, hok, hno⟩

end Kopf

/-! ## 4. The checks of G pass -/

section Pruefung

variable {V : Vertrag D}

/-- A `traverse` head whose invariant is false at `σ` predicts
    `logik schleife`, whatever indices are left. -/
theorem semV_trav_falsch (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (ks : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = false) :
    semV O passes R (.trav t inv body ks k) σ ρ = .logik .schleife := by
  cases ks with
  | nil =>
      simp only [semV, weiterZ, laufA, traverseLauf, leseB, hw]
      exact weiterZ_logik O passes R k _
  | cons i is =>
      simp only [semV, weiterZ, laufA, traverseLauf, leseB, hw]
      exact weiterZ_logik O passes R k _

/-- A `forever` head with budget left whose invariant is false at `σ`
    predicts `logik schleife`. -/
theorem semV_ewig_falsch (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = false) :
    semV O passes R (.ewig a (n + 1) inv body k) σ ρ = .logik .schleife := by
  simp only [semV, weiterZ, laufA, foreverLauf, leseB, hw]
  exact weiterZ_logik O passes R k _

/-- A `leave` out of a `traverse` body whose invariant is false at `σ`
    predicts `logik schleife`. -/
theorem semV_leaveTrav_falsch (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {l : Bool} {Γ : Ctx}
    {Λ Λx : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ)
    (rest : Block D V true (.index (D.count t) :: Γ) Λx Λ) (hl : true = true)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = false) :
    semV O passes R (.dann (.cons (.leave hl) rest) (.travRest t inv body is k)) σ (.cons i ρ) =
      .logik .schleife := by
  rw [semV_dann_cons]
  show weiterZ O passes R (.travRest t inv body is k) (.leave hl σ (.cons i ρ)) = _
  simp only [weiterZ, leseB, Env.tail, hw]
  exact weiterZ_logik O passes R k _

/-- **A leaf's `logik` outcome is decided on the footprint.** The only leaf
    with a `logik` outcome is a `state` transition (`vorzustand`); it reads
    the transition slot and the index, both carriers of `stmtOrteP`, so at
    a world agreeing on the footprint every handler and oracle sees the
    same failure. -/
theorem blatt_logik (P : Programm D) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (hb : s.istBlatt = true) {S : List (D.Tab ⊕ D.Glob)}
    (hS : stmtOrteP P s ⊆ S) {σ W : World D} (hg : GleichAuf S σ W)
    (O O' : Orakel D) (passes : Nat)
    (R R' : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (ρ : Env D Γ)
    (e : Logik D) (h : execStmt O passes R s W ρ = .logik e) :
    execStmt O' passes R' s σ ρ = .logik e := by
  cases s with
  | uebergang t f hτ i von nach hn he hw hL =>
      simp only [stmtOrteP, List.cons_subset] at hS
      have hgl := hg.lese Λ Λ (.inl t :: i.orte) (.inl t :: i.orte)
      have hi : eval (σ.lese Λ (.inl t :: i.orte)) i (σ.lese Λ (.inl t :: i.orte)) ρ =
          eval (W.lese Λ (.inl t :: i.orte)) i (W.lese Λ (.inl t :: i.orte)) ρ :=
        eval_gleichAuf i (fun _ h => hS.2 h) hgl ρ
      have hsl : (σ.lese Λ (.inl t :: i.orte)).slots t = (W.lese Λ (.inl t :: i.orte)).slots t :=
        hgl.1 t hS.1
      simp only [execStmt] at h ⊢
      rw [hi, hsl]
      split at h
      · cases h
      · rename_i hc
        rw [if_neg hc]
        exact h
  | axiomCall a args h' hw hg' hd hgd =>
      simp only [execStmt, axiomAntwort] at h
      split at h <;> cases h
  | ite => simp [Stmt.istBlatt] at hb
  | onOption => simp [Stmt.istBlatt] at hb
  | onTag => simp [Stmt.istBlatt] at hb
  | onGrund => simp [Stmt.istBlatt] at hb
  | call => simp [Stmt.istBlatt] at hb
  | callInd => simp [Stmt.istBlatt] at hb
  | locks => simp [Stmt.istBlatt] at hb
  | breaking => simp [Stmt.istBlatt] at hb
  | traverse => simp [Stmt.istBlatt] at hb
  | retry => simp [Stmt.istBlatt] at hb
  | forever => simp [Stmt.istBlatt] at hb
  | _ => simp [execStmt] at h

end Pruefung

/-! ## 5. The conclusion: no reachable machine is stuck at a `logik` check -/

/-- **The `logik` checks of G pass for thread `t` of `M`.** At each of the
    five places where a rule of G tests a `logik` condition of the running
    frame, the test passes at the thread's machine world:
    * a `traverse` boundary (`travNext`, `travDone`): the invariant holds;
    * a `forever` boundary with budget left (`ewigWeiter`): the invariant
      holds;
    * a `leave` out of a `traverse` body (`dannLeaveTrav`): the invariant
      holds at the exit;
    * a leaf at the head of an end block or of a block (`blatt`,
      `dannBlatt`; the only leaf with a `logik` outcome is a `state`
      transition): its outcome is no `logik` outcome, so the transition
      finds its pre-state.
    `nachbedingung`, `invariante`, `abstieg` and `vorbedingung` are no
    checks of G at all (G logs entries and returns and has no depth
    bound). -/
def PrueftG (O : Orakel D) (passes : Nat) (M : RufMaschineG D) (t : Faden) : Prop :=
    (∀ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ) (tb : D.Tab)
        (inv : Expr D Γ Λ .bool)
        (body : Block D (vertragVon D (M.faeden t).kopf.f) true (.index (D.count tb) :: Γ) Λ Λ)
        (ks : List (Wert D (.index (D.count tb))))
        (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ),
      (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .trav tb inv body ks k⟩ →
      wahr? (eval ((M.weltVon t).lese Λ inv.orte) inv ((M.weltVon t).lese Λ inv.orte) ρ) = true) ∧
    (∀ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ) (a : D.Annahme) (n : Nat)
        (inv : Expr D Γ Λ .bool) (body : Block D (vertragVon D (M.faeden t).kopf.f) true Γ Λ Λ)
        (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ),
      (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .ewig a (n + 1) inv body k⟩ →
      wahr? (eval ((M.weltVon t).lese Λ inv.orte) inv ((M.weltVon t).lese Λ inv.orte) ρ) = true) ∧
    (∀ (l : Bool) (Γ : Ctx) (Λ Λx : List (Res D)) (ρ : Env D Γ) (tb : D.Tab)
        (inv : Expr D Γ Λ .bool)
        (body : Block D (vertragVon D (M.faeden t).kopf.f) true (.index (D.count tb) :: Γ) Λ Λ)
        (is : List (Wert D (.index (D.count tb))))
        (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ)
        (rest : Block D (vertragVon D (M.faeden t).kopf.f) true (.index (D.count tb) :: Γ) Λx Λ)
        (hl : true = true) (i : Wert D (.index (D.count tb))),
      (M.faeden t).kopf.rest = ⟨true, .index (D.count tb) :: Γ, Λx, .cons i ρ,
        .dann (.cons (.leave hl) rest) (.travRest tb inv body is k)⟩ →
      wahr? (eval ((M.weltVon t).lese Λ inv.orte) inv ((M.weltVon t).lese Λ inv.orte) ρ) = true) ∧
    (∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (ρ : Env D Γ)
        (s : Stmt D (vertragVon D (M.faeden t).kopf.f) l Γ Λ Λ')
        (K : Endblock D (vertragVon D (M.faeden t).kopf.f) l Γ Λ'),
      s.istBlatt = true → (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.cons s K)⟩ →
      ∀ e : Logik D, execStmt O passes keinRuf s (M.weltVon t) ρ ≠ .logik e) ∧
    (∀ (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (ρ : Env D Γ)
        (s : Stmt D (vertragVon D (M.faeden t).kopf.f) l Γ Λ Λ')
        (rst : Block D (vertragVon D (M.faeden t).kopf.f) l Γ Λ' Λ'')
        (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ''),
      s.istBlatt = true → (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons s rst) k⟩ →
      ∀ e : Logik D, execStmt O passes keinRuf s (M.weltVon t) ρ ≠ .logik e)

/-- **No thread of `M` is stopped at a `logik` check of G.** -/
def KeinLogikHaltG (O : Orakel D) (passes : Nat) (M : RufMaschineG D) : Prop :=
  ∀ t : Faden, PrueftG O passes M t

/-- A Boolean that is not `false` is `true`. -/
theorem wahr_of_nicht_falsch {b : Bool} (h : b = false → False) : b = true := by
  cases b
  · exact absurd rfl h
  · rfl

section Halt

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D}

/-- **A replayed thread is stopped at no `logik` check**, when every body
    meets `KeineLogik`. -/
theorem fadenR_prueft (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hL : ∀ f, KeineLogik P passes Q f) {M : RufMaschineG D} (t : Faden)
    (hF : FadenR P O passes Q (M.faeden t) (M.weltVon t)) : PrueftG O passes M t := by
  have hK := hF.1
  refine ⟨fun l Γ Λ ρ tb inv body ks k hr => ?_, fun l Γ Λ ρ a n inv body k hr => ?_,
    fun l Γ Λ Λx ρ tb inv body is k rest hl i hr => ?_,
    fun l Γ Λ Λ' ρ s K hb hr e he => ?_, fun l Γ Λ Λ' Λ'' ρ s rst k hb hr e he => ?_⟩
  · obtain ⟨H, HA, σ, hg, hok, hno⟩ := kopfR_keineLogik' hO hRL hQ hL hK hr
    refine wahr_of_nicht_falsch fun hw => hno .schleife ?_
    apply semV_trav_falsch
    rw [eval_gleichAuf inv (fun _ h => hok.1 h) (hg.lese Λ Λ inv.orte inv.orte) ρ]
    exact hw
  · obtain ⟨H, HA, σ, hg, hok, hno⟩ := kopfR_keineLogik' hO hRL hQ hL hK hr
    refine wahr_of_nicht_falsch fun hw => hno .schleife ?_
    apply semV_ewig_falsch
    rw [eval_gleichAuf inv (fun _ h => hok.1 h) (hg.lese Λ Λ inv.orte inv.orte) ρ]
    exact hw
  · obtain ⟨H, HA, σ, hg, hok, hno⟩ := kopfR_keineLogik' hO hRL hQ hL hK hr
    refine wahr_of_nicht_falsch fun hw => hno .schleife ?_
    apply semV_leaveTrav_falsch
    rw [eval_gleichAuf inv (fun _ h => hok.2.2.1 h) (hg.lese Λ Λ inv.orte inv.orte) ρ]
    exact hw
  · obtain ⟨H, HA, σ, hg, hok, hno⟩ := kopfR_keineLogik' hO hRL hQ hL hK hr
    obtain ⟨_, hss, _⟩ := okG_ende_cons hok
    have h' := blatt_logik P s hb hss hg O (orakelAus O HA) passes keinRuf (rufAusL H) ρ e he
    refine hno e ?_
    show zErg (execEnd (orakelAus O HA) passes (rufAusL H) (.cons s K) σ ρ) = _
    simp only [execEnd, h', zErg]
  · obtain ⟨H, HA, σ, hg, hok, hno⟩ := kopfR_keineLogik' hO hRL hQ hL hK hr
    obtain ⟨_, hss, _⟩ := okG_dann_cons hok
    have h' := blatt_logik P s hb hss hg O (orakelAus O HA) passes keinRuf (rufAusL H) ρ e he
    refine hno e ?_
    rw [semV_dann_cons, h']
    exact weiterZ_logik _ _ _ _ e

end Halt

/-! ## 6. The goal theorem -/

/-- **ZIEL AM ORT, GANZ -- the goal theorem.** Over the repaired machine G,
    for every program in the widened fragment (`programmImFragmentG`: every
    form, indirect calls under `KandOk`, register reads under `RegLokal`)
    whose widened footprint check passes (`fussOrtGB`), from an exclusive
    start that meets the entry contracts, with an oracle that keeps the
    declared axiom frames and the held locks (`GutO`), answers registers and
    `awaits` from the declared carriers (`RegLokal`) and meets the declared
    axiom ensures `Q` (`AxVertragO Q O`, `Q` reading only the declared
    carriers, `AxEnsLokal Q`), and whose every function meets the user
    obligation `KoerperGutZ` -- the body triple and caller duty against
    frame-respecting handlers and the oracles meeting `Q`, and NO `logik`
    outcome of the body -- EVERY reachable machine satisfies
    * `VertragAmOrtG`: `requires` at every logged entry, `ensures` at every
      logged return, with the actual values; and
    * `KeinLogikHaltG`: no thread is stopped at a `logik` check of G -- every
      loop invariant G tests holds where G tests it, and every `state`
      transition finds its pre-state.

    Premises, by class: (a) user logic `KoerperGutZ` (per function, over the
    SEQUENTIAL semantics), `StartGut`; (b) hardware `GutO`, `RegLokal`,
    `AxVertragO Q`; (c) decidable program facts `hvoll`, `programmImFragmentG`,
    `fussOrtGB`, `StartExklusiv` (N240 for constant starts), `AxEnsLokal Q`;
    the declaration has an event (`e0`). -/
theorem ziel_ort_ganz (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (fs : List D.Fn) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (e0 : Ereignis D) (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hlok : AxEnsLokal Q) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussOrtGB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutZ P passes Q f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M ∧ KeinLogikHaltG O passes M := by
  intro M hr
  have hI := zielInvR_erreichbar P O passes Q fs sp init e0 hO hRL hQ hlok hvoll hFrag hFuss
    (fun f => (hK f).1) hStart hex M hr
  exact ⟨fun t ev hev => hI.2 t ev hev,
    fun t => fadenR_prueft hO hRL hQ (fun f => (hK f).2) t (hI.1 t)⟩

/-- **The contract half alone** needs only the first conjunct of the
    obligation: `ziel_ort_rahmen` with declared axiom ensures (callee
    frames, registers, `awaits` and `Q` in one statement). -/
theorem ziel_ort_ganz_vertrag (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (fs : List D.Fn) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (e0 : Ereignis D) (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hlok : AxEnsLokal Q) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussOrtGB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutRQ P passes Q f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M := by
  intro M hr
  have hI := zielInvR_erreichbar P O passes Q fs sp init e0 hO hRL hQ hlok hvoll hFrag hFuss
    hK hStart hex M hr
  exact fun t ev hev => hI.2 t ev hev

/-- **`ziel_ort_voll_ax` on register-local oracles is a special case**:
    its fragment and footprint check give the widened ones, its obligation
    `KoerperGutA` gives `KoerperGutRQ` (`koerperGutRQ_of_A`). -/
theorem ziel_ort_voll_ax_lokal_aus_ganz (P : Programm D) (O : Orakel D) (passes : Nat)
    (Q : AxEns D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentV P fs = true) (hFuss : fussOrtB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutA P passes Q f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M :=
  ziel_ort_ganz_vertrag P O passes Q fs sp init e0 hO hRL hQ hlok hvoll
    (programmImFragmentG_of_V P fs hFrag) (fussOrtGB_of_V P fs hFrag hFuss)
    (fun f => koerperGutRQ_of_A (hK f)) hStart hex

/-- **`ziel_ort_rahmen` is the contract half at the trivial ensures.** -/
theorem ziel_ort_rahmen_aus_ganz (P : Programm D) (O : Orakel D) (passes : Nat) (fs : List D.Fn)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hRL : RegLokal O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussOrtGB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutR P passes f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M :=
  ziel_ort_ganz_vertrag P O passes (axWahr D) fs sp init e0 hO hRL (axVertragO_wahr O)
    axEnsLokal_wahr hvoll hFrag hFuss (fun f => koerperGutRQ_of_R (axWahr D) (hK f)) hStart hex

#print axioms Gabbro.Grammatik.kopfR_keineLogik
#print axioms Gabbro.Grammatik.blatt_logik
#print axioms Gabbro.Grammatik.fadenR_prueft
#print axioms Gabbro.Grammatik.ziel_ort_ganz
#print axioms Gabbro.Grammatik.ziel_ort_ganz_vertrag
#print axioms Gabbro.Grammatik.ziel_ort_voll_ax_lokal_aus_ganz
#print axioms Gabbro.Grammatik.ziel_ort_rahmen_aus_ganz

end Gabbro.Grammatik
