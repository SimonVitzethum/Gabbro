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
  passes at the machine world (`KeinLogikHaltG`) and the rule fires
  (`schritt_an_pruefung`, given `HeldGenau` of the head).

  Why the obligation and not the machine: making G continue past a false
  invariant (as the emitted C does) would leave the replay without the
  invariant the user's loop reasoning needs, and every adequacy file would
  have to follow a G that no longer means what the sequential semantics
  means. Keeping G's checks and asking the user to prove the invariants
  they wrote turns each check into a theorem: on G's runs the check always
  passes, so the C's not checking it is harmless there.
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

/-! ## 5. A sufficient syntactic check: bodies without `logik` sources

  A body without a loop invariant (`traverse`, `forever`) and without a
  `state` transition has no `logik` source of its own; against a handler
  that answers no `logik` outcome it ends in none (`logikFrei_keineLogik`).
  The check is conservative: `onTag`/`onGrund` are refused too (their arm
  selection is not unfolded here), `retry` and every block form are
  admitted. For such a body the new clause `KeineLogik` costs the user
  nothing -- it is a Boolean computation over the text. -/

mutual

def Stmt.logikFrei {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Bool
  | .uebergang .. => false
  | .traverse .. => false
  | .forever .. => false
  | .onTag .. => false
  | .onGrund .. => false
  | .ite _ t e => t.logikFrei && e.logikFrei
  | .onOption _ p a => p.logikFrei && a.logikFrei
  | .locks _ _ body => body.logikFrei
  | .breaking _ body => body.logikFrei
  | .retry _ _ body ueber => body.logikFrei && ueber.logikFrei
  | _ => true

def Block.logikFrei {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => s.logikFrei && rest.logikFrei
  | .bind _ rest => rest.logikFrei
  | .bindCall _ _ _ _ _ rest => rest.logikFrei
  | .bindCallInd _ _ _ _ _ rest => rest.logikFrei
  | .bindCallElse _ _ _ _ _ err rest => err.logikFrei && rest.logikFrei
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.logikFrei
  | .regLies _ _ rest => rest.logikFrei
  | .regLiesElse _ _ _ sonst rest => sonst.logikFrei && rest.logikFrei
  | .awaits _ _ _ _ rest => rest.logikFrei
  | .exchange _ _ _ _ rest => rest.logikFrei
  | .narrow _ _ _ sonst rest => sonst.logikFrei && rest.logikFrei
  | .pruefung _ sonst rest => sonst.logikFrei && rest.logikFrei
  | .gleit _ _ _ _ _ rest => rest.logikFrei
  | .gleitLit _ _ _ rest => rest.logikFrei
  | .gleitVon _ _ _ rest => rest.logikFrei
  | .gleitNarrow _ _ _ sonst rest => sonst.logikFrei && rest.logikFrei

def Endblock.logikFrei {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retGrund .. => true
  | .leave .. => true
  | .next .. => true
  | .cons s rest => s.logikFrei && rest.logikFrei
  | .bind _ rest => rest.logikFrei

end

section LogikFrei

variable {V : Vertrag D}

theorem Ausgang.schrumpf_logik {l : Bool} {Γ : Ctx} {τ : Ty} {o : Ausgang V l (τ :: Γ)}
    {e : Logik D} (h : o.schrumpf = .logik e) : o = .logik e := by
  cases o <;> simp_all [Ausgang.schrumpf]

theorem EndAusgang.schrumpf_logik {l : Bool} {Γ : Ctx} {τ : Ty} {o : EndAusgang V l (τ :: Γ)}
    {e : Logik D} (h : o.schrumpf = .logik e) : o = .logik e := by
  cases o <;> simp_all [EndAusgang.schrumpf]

theorem EndAusgang.zuAusgang_logik {l : Bool} {Γ : Ctx} {o : EndAusgang V l Γ}
    {e : Logik D} (h : o.zuAusgang = .logik e) : o = .logik e := by
  cases o <;> simp_all [EndAusgang.zuAusgang]

theorem Ausgang.mapWelt_logik {l : Bool} {Γ : Ctx} {o : Ausgang V l Γ}
    {f : World D → World D} {e : Logik D} (h : o.mapWelt f = .logik e) : o = .logik e := by
  cases o <;> simp_all [Ausgang.mapWelt]

theorem retryLauf_ohneLogik {l : Bool} {Γ : Ctx} (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueber : World D → Env D Γ → Ausgang V l Γ)
    (hs : ∀ σ ρ e, schritt σ ρ ≠ .logik e) (hu : ∀ σ ρ e, ueber σ ρ ≠ .logik e) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ) (e : Logik D),
      retryLauf schritt bis ueber n σ ρ ≠ .logik e
  | 0, σ, ρ, e => hu σ ρ e
  | n + 1, σ, ρ, e => by
      intro h
      simp only [retryLauf] at h
      split at h
      · cases h
      · split at h
        · exact retryLauf_ohneLogik schritt bis ueber hs hu n _ _ e h
        · exact retryLauf_ohneLogik schritt bis ueber hs hu n _ _ e h
        · cases h
        · cases h
        · cases h
        · rename_i heq
          cases h
          exact hs _ _ _ heq
        · cases h

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

mutual

theorem Stmt.logikFrei_ok (hR : OhneLogik R) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → s.logikFrei = true →
      ∀ (σ : World D) (ρ : Env D Γ) (e : Logik D), execStmt O passes R s σ ρ ≠ .logik e
  | .ite c t e, h, σ, ρ, e', he => by
      simp only [Stmt.logikFrei, Bool.and_eq_true] at h
      simp only [execStmt] at he
      split at he
      · exact Block.logikFrei_ok hR t h.1 _ _ _ he
      · exact Block.logikFrei_ok hR e h.2 _ _ _ he
  | .onOption o p a, h, σ, ρ, e', he => by
      simp only [Stmt.logikFrei, Bool.and_eq_true] at h
      simp only [execStmt] at he
      split at he
      · exact Block.logikFrei_ok hR p h.1 _ _ _ (Ausgang.schrumpf_logik he)
      · exact Block.logikFrei_ok hR a h.2 _ _ _ he
  | .locks L hr body, h, σ, ρ, e', he => by
      simp only [Stmt.logikFrei] at h
      simp only [execStmt] at he
      exact Block.logikFrei_ok hR body h _ _ _ (Ausgang.mapWelt_logik he)
  | .breaking i body, h, σ, ρ, e', he => by
      simp only [Stmt.logikFrei] at h
      simp only [execStmt] at he
      exact Block.logikFrei_ok hR body h _ _ _ he
  | .retry n bis body ueber, h, σ, ρ, e', he => by
      simp only [Stmt.logikFrei, Bool.and_eq_true] at h
      simp only [execStmt] at he
      exact retryLauf_ohneLogik _ _ _ (fun σ ρ e => Block.logikFrei_ok hR body h.1 σ ρ e)
        (fun σ ρ e => Block.logikFrei_ok hR ueber h.2 σ ρ e) n σ ρ e' he
  | .call g args hp hr, _, σ, ρ, e', he => by
      simp only [execStmt] at he
      split at he
      · cases he
      · rename_i r _
        exact (Fin.cast hr r).elim0
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
      · cases he
  | .callInd p args hp hr, _, σ, ρ, e', he => by
      simp only [execStmt] at he
      split at he
      rename_i f hf _
      split at he
      · cases he
      · rename_i r _
        exact keinGrundSig hf hr r
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
      · cases he
  | .axiomCall a args h' hw hg hd hgd, _, σ, ρ, e', he => by
      simp only [execStmt, axiomAntwort] at he
      split at he <;> cases he
  | .uebergang .., h, _, _, _, _ => by simp [Stmt.logikFrei] at h
  | .traverse .., h, _, _, _, _ => by simp [Stmt.logikFrei] at h
  | .forever .., h, _, _, _, _ => by simp [Stmt.logikFrei] at h
  | .onTag .., h, _, _, _, _ => by simp [Stmt.logikFrei] at h
  | .onGrund .., h, _, _, _, _ => by simp [Stmt.logikFrei] at h
  | .assignSlot .., _, _, _, _, he => by simp [execStmt] at he
  | .assignDurch .., _, _, _, _, he => by simp [execStmt] at he
  | .assignGlob .., _, _, _, _, he => by simp [execStmt] at he
  | .schreibBytes .., _, _, _, _, he => by simp [execStmt] at he
  | .assignVar .., _, _, _, _, he => by simp [execStmt] at he
  | .regSchreib .., _, _, _, _, he => by simp [execStmt] at he
  | .transition .., _, _, _, _, he => by simp [execStmt] at he
  | .publish .., _, _, _, _, he => by simp [execStmt] at he
  | .advances .., _, _, _, _, he => by simp [execStmt] at he
  | .retires .., _, _, _, _, he => by simp [execStmt] at he
  | .ret .., _, _, _, _, he => by simp [execStmt] at he
  | .retGrund .., _, _, _, _, he => by simp [execStmt] at he
  | .leave .., _, _, _, _, he => by simp [execStmt] at he
  | .next .., _, _, _, _, he => by simp [execStmt] at he

theorem Block.logikFrei_ok (hR : OhneLogik R) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → b.logikFrei = true →
      ∀ (σ : World D) (ρ : Env D Γ) (e : Logik D), execBlock O passes R b σ ρ ≠ .logik e
  | .nil, _, σ, ρ, e, he => by simp [execBlock] at he
  | .cons s rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h.2 _ _ _ he
      · exact Stmt.logikFrei_ok hR s h.1 σ ρ e he
  | .bind x rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock] at he
      exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
  | .bindCall g args he' hp hr rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
      · rename_i r _
        exact (Fin.cast hr r).elim0
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
      · cases he
  | .bindCallInd p args he' hp hr rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock] at he
      split at he
      rename_i f hf _
      split at he
      · exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
      · rename_i r _
        exact keinGrundSig hf hr r
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
      · cases he
  | .bindCallElse g args he' hp hr err rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h.2 _ _ _ (Ausgang.schrumpf_logik he)
      · exact Endblock.logikFrei_ok hR err h.1 _ _ _
          (EndAusgang.schrumpf_logik (EndAusgang.zuAusgang_logik he))
      · rename_i heq
        cases he
        exact hR _ _ _ _ heq
      · cases he
  | .bindAxiom a args he' hw hg hd hgd rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock, axiomAntwort] at he
      split at he
      · exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
      · cases he
  | .regLies r hk rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock] at he
      split at he
      · split at he
        · exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
        · cases he
      · cases he
  | .regLiesElse r hk zusage sonst rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · split at he
        · exact Block.logikFrei_ok hR rest h.2 _ _ _ (Ausgang.schrumpf_logik he)
        · exact Endblock.logikFrei_ok hR sonst h.1 _ _ _ (EndAusgang.zuAusgang_logik he)
      · cases he
  | .awaits g payload hp hL rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
      · cases he
  | .exchange g neu hw hL rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock] at he
      exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
  | .narrow x lo' hi' sonst rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h.2 _ _ _ (Ausgang.schrumpf_logik he)
      · exact Endblock.logikFrei_ok hR sonst h.1 _ _ _ (EndAusgang.zuAusgang_logik he)
  | .pruefung c sonst rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h.2 _ _ _ he
      · exact Endblock.logikFrei_ok hR sonst h.1 _ _ _ (EndAusgang.zuAusgang_logik he)
  | .gleit op a b lo hi rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
      · cases he
  | .gleitLit q lo hi rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
      · cases he
  | .gleitVon x lo hi rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h _ _ _ (Ausgang.schrumpf_logik he)
      · cases he
  | .gleitNarrow x lo hi sonst rest, h, σ, ρ, e, he => by
      simp only [Block.logikFrei, Bool.and_eq_true] at h
      simp only [execBlock] at he
      split at he
      · exact Block.logikFrei_ok hR rest h.2 _ _ _ (Ausgang.schrumpf_logik he)
      · exact Endblock.logikFrei_ok hR sonst h.1 _ _ _ (EndAusgang.zuAusgang_logik he)

theorem Endblock.logikFrei_ok (hR : OhneLogik R) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (b : Endblock D V l Γ Λ) → b.logikFrei = true →
      ∀ (σ : World D) (ρ : Env D Γ) (e : Logik D), execEnd O passes R b σ ρ ≠ .logik e
  | .ret .., _, _, _, _, he => by simp [execEnd] at he
  | .retGrund .., _, _, _, _, he => by simp [execEnd] at he
  | .leave .., _, _, _, _, he => by simp [execEnd] at he
  | .next .., _, _, _, _, he => by simp [execEnd] at he
  | .cons s rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei, Bool.and_eq_true] at h
      simp only [execEnd] at he
      split at he
      · exact Endblock.logikFrei_ok hR rest h.2 _ _ _ he
      · cases he
      · cases he
      · cases he
      · cases he
      · rename_i heq
        cases he
        exact Stmt.logikFrei_ok hR s h.1 σ ρ e heq
      · cases he
  | .bind x rest, h, σ, ρ, e, he => by
      simp only [Endblock.logikFrei] at h
      simp only [execEnd] at he
      exact Endblock.logikFrei_ok hR rest h _ _ _ (EndAusgang.schrumpf_logik he)

end

end LogikFrei

/-- **A body without `logik` sources meets `KeineLogik`** -- for every
    declared axiom ensures, without any reasoning about the program. -/
theorem logikFrei_keineLogik {P : Programm D} (passes : Nat) (Q : AxEns D) {f : D.Fn}
    (h : (P.rumpf f).logikFrei = true) : KeineLogik P passes Q f :=
  fun O' _ _ _ R _ hR σ ρ _ e => Endblock.logikFrei_ok O' passes R hR (P.rumpf f) h σ ρ e

/-- The program-level check over a member list. -/
def programmLogikFrei (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun f => (P.rumpf f).logikFrei

theorem programmLogikFrei_ok {P : Programm D} {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (h : programmLogikFrei P fs = true) (passes : Nat) (Q : AxEns D) :
    ∀ f, KeineLogik P passes Q f :=
  fun f => logikFrei_keineLogik passes Q ((List.all_eq_true.mp h) f (hvoll f))

#print axioms Gabbro.Grammatik.logikFrei_keineLogik
#print axioms Gabbro.Grammatik.programmLogikFrei_ok

/-! ## 6. The conclusion: no reachable machine is stuck at a `logik` check -/

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

/-! ## 7. G moves at every `logik` check

  `KeinLogikHaltG` says the checks PASS. Here the step itself: at every
  place where a rule of G tests a `logik` condition, the rule fires -- given
  the one side condition every reading rule of G carries, `HeldGenau` of
  the head's static holdings (a lock-bookkeeping fact, not a `logik` check;
  `rufG_haelt_statisch` proves its `⊆` half on every reachable machine, the
  `⊇` half is not proved -- `SATZKARTE.md` §13.5). -/

/-- **Thread `t` of `M` stands at a `logik` check of G**: a `traverse`
    boundary, a `forever` boundary with budget left, a `leave` out of a
    `traverse` body, or a `state` transition at the head of an end block or
    of a block. -/
def AnPruefungG (M : RufMaschineG D) (t : Faden) : Prop :=
  (∃ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ) (tb : D.Tab)
      (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden t).kopf.f) true (.index (D.count tb) :: Γ) Λ Λ)
      (ks : List (Wert D (.index (D.count tb))))
      (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ),
    (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .trav tb inv body ks k⟩) ∨
  (∃ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ) (a : D.Annahme) (n : Nat)
      (inv : Expr D Γ Λ .bool) (body : Block D (vertragVon D (M.faeden t).kopf.f) true Γ Λ Λ)
      (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ),
    (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .ewig a (n + 1) inv body k⟩) ∨
  (∃ (l : Bool) (Γ : Ctx) (Λ Λx : List (Res D)) (ρ : Env D Γ) (tb : D.Tab)
      (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden t).kopf.f) true (.index (D.count tb) :: Γ) Λ Λ)
      (is : List (Wert D (.index (D.count tb))))
      (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ)
      (rest : Block D (vertragVon D (M.faeden t).kopf.f) true (.index (D.count tb) :: Γ) Λx Λ)
      (hl : true = true) (i : Wert D (.index (D.count tb))),
    (M.faeden t).kopf.rest = ⟨true, .index (D.count tb) :: Γ, Λx, .cons i ρ,
      .dann (.cons (.leave hl) rest) (.travRest tb inv body is k)⟩) ∨
  (∃ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ) (lo hi : Int) (tb : D.Tab)
      (fl : D.Feld tb) (hτ : D.typ tb fl = .int lo hi) (i : Expr D Γ Λ (.index (D.count tb)))
      (von nach : Int) (hn : lo ≤ nach ∧ nach ≤ hi) (he : D.erlaubt tb fl von nach = true)
      (hw : (vertragVon D (M.faeden t).kopf.f).schreibt tb = true) (hL : darf D tb Λ)
      (K : Endblock D (vertragVon D (M.faeden t).kopf.f) l Γ Λ),
    (M.faeden t).kopf.rest =
      ⟨l, Γ, Λ, ρ, .ende (.cons (.uebergang tb fl hτ i von nach hn he hw hL) K)⟩) ∨
  (∃ (l : Bool) (Γ : Ctx) (Λ Λ'' : List (Res D)) (ρ : Env D Γ) (lo hi : Int) (tb : D.Tab)
      (fl : D.Feld tb) (hτ : D.typ tb fl = .int lo hi) (i : Expr D Γ Λ (.index (D.count tb)))
      (von nach : Int) (hn : lo ≤ nach ∧ nach ≤ hi) (he : D.erlaubt tb fl von nach = true)
      (hw : (vertragVon D (M.faeden t).kopf.f).schreibt tb = true) (hL : darf D tb Λ)
      (rst : Block D (vertragVon D (M.faeden t).kopf.f) l Γ Λ Λ'')
      (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ''),
    (M.faeden t).kopf.rest =
      ⟨l, Γ, Λ, ρ, .dann (.cons (.uebergang tb fl hτ i von nach hn he hw hL) rst) k⟩)

/-- A `state` transition whose outcome is no `logik` outcome is an `ok`
    step that only adds accesses to the trace. -/
theorem uebergang_ok {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {lo hi : Int}
    (O : Orakel D) (passes : Nat) (tb : D.Tab) (fl : D.Feld tb) (hτ : D.typ tb fl = .int lo hi)
    (i : Expr D Γ Λ (.index (D.count tb))) (von nach : Int) (hn : lo ≤ nach ∧ nach ≤ hi)
    (he : D.erlaubt tb fl von nach = true) (hw : V.schreibt tb = true) (hL : darf D tb Λ)
    (W : World D) (ρ : Env D Γ)
    (hno : ∀ e : Logik D, execStmt O passes keinRuf
      (Stmt.uebergang (l := l) tb fl hτ i von nach hn he hw hL) W ρ ≠ .logik e) :
    ∃ σ' ρ', execStmt O passes keinRuf (Stmt.uebergang (l := l) tb fl hτ i von nach hn he hw hL)
      W ρ = .ok σ' ρ' ∧ Erw W σ' := by
  cases hx : execStmt O passes keinRuf (Stmt.uebergang (l := l) tb fl hτ i von nach hn he hw hL)
      W ρ with
  | ok σ' ρ' =>
      refine ⟨σ', ρ', rfl, ?_⟩
      simp only [execStmt] at hx
      split at hx
      · cases hx
        exact (Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)
      · cases hx
  | logik e => exact absurd hx (hno e)
  | _ =>
      simp only [execStmt] at hx
      split at hx <;> cases hx

section Schritt

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **At a `logik` check whose test passes, G fires.** From `PrueftG` (the
    conclusion of the goal theorem) and `HeldGenau` of the head's static
    holdings: `travNext`/`travDone`, `ewigWeiter`, `dannLeaveTrav`, and
    `blatt`/`dannBlatt` on a `state` transition. -/
theorem schritt_an_pruefungI {M : RufMaschineG D} (t : Faden) (hP : PrueftG O passes M t)
    (hH : HeldIn (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur))
    (hA : AnPruefungG M t) : ∃ M', RufSchrittG P O passes M t M' := by
  rcases hA with ⟨l, Γ, Λ, ρ, tb, inv, body, ks, k, hr⟩ | ⟨l, Γ, Λ, ρ, a, n, inv, body, k, hr⟩ |
      ⟨l, Γ, Λ, Λx, ρ, tb, inv, body, is, k, rest, hl, i, hr⟩ |
      ⟨l, Γ, Λ, ρ, lo, hi, tb, fl, hτ, i, von, nach, hn, he, hw, hL, K, hr⟩ |
      ⟨l, Γ, Λ, Λ'', ρ, lo, hi, tb, fl, hτ, i, von, nach, hn, he, hw, hL, rst, k, hr⟩
  · have hwahr := hP.1 l Γ Λ ρ tb inv body ks k hr
    rw [hr] at hH
    cases ks with
    | nil =>
        obtain ⟨M', hs, _⟩ := w_travDone (P := P) (O := O) (passes := passes) (z := M.faeden t) rfl
          tb inv body k ρ hr hwahr hH
        exact ⟨M', hs⟩
    | cons j js =>
        obtain ⟨M', hs, _⟩ := w_travNext (P := P) (O := O) (passes := passes) (z := M.faeden t) rfl
          tb inv body j js k ρ hr hwahr hH
        exact ⟨M', hs⟩
  · have hwahr := hP.2.1 l Γ Λ ρ a n inv body k hr
    rw [hr] at hH
    obtain ⟨M', hs, _⟩ := w_ewigWeiter (P := P) (O := O) (passes := passes) (z := M.faeden t) rfl
      a n inv body k ρ hr hwahr hH
    exact ⟨M', hs⟩
  · have hwahr := hP.2.2.1 l Γ Λ Λx ρ tb inv body is k rest hl i hr
    rw [hr] at hH
    obtain ⟨M', hs, _⟩ := w_leaveTrav (P := P) (O := O) (passes := passes) (z := M.faeden t) rfl
      tb inv body is k rest i ρ hr hwahr hH
    exact ⟨M', hs⟩
  · have hno := hP.2.2.2.1 l Γ Λ Λ ρ _ K rfl hr
    rw [hr] at hH
    obtain ⟨σ', ρ', hst, herw⟩ := uebergang_ok O passes tb fl hτ i von nach hn he hw hL _ ρ hno
    obtain ⟨M', hs, _⟩ := w_blatt (P := P) (O := O) (passes := passes) (z := M.faeden t) rfl
      _ K ρ rfl hr hH σ' ρ' hst herw
    exact ⟨M', hs⟩
  · have hno := hP.2.2.2.2 l Γ Λ Λ Λ'' ρ _ rst k rfl hr
    rw [hr] at hH
    obtain ⟨σ', ρ', hst, herw⟩ := uebergang_ok O passes tb fl hτ i von nach hn he hw hL _ ρ hno
    obtain ⟨M', hs, _⟩ := w_dannBlatt (P := P) (O := O) (passes := passes) (z := M.faeden t) rfl
      _ rst k ρ rfl hr hH σ' ρ' hst herw
    exact ⟨M', hs⟩

/-- The form with the exact held set (before the held-set relaxation the
    rules demanded it; now `HeldIn` suffices, `schritt_an_pruefungI`). -/
theorem schritt_an_pruefung {M : RufMaschineG D} (t : Faden) (hP : PrueftG O passes M t)
    (hH : HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur))
    (hA : AnPruefungG M t) : ∃ M', RufSchrittG P O passes M t M' :=
  schritt_an_pruefungI t hP hH.heldIn hA

end Schritt

/-! ## 8. The goal theorem -/

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
      transition finds its pre-state; and
    * progress at the checks: a thread standing at a `logik` check
      (`AnPruefungG`) whose head's static holdings are exactly its held locks
      (`HeldGenau`, the lock side condition of every reading rule) CAN STEP.
      What else can stop a thread is named in `SATZKARTE.md` §13.5.

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
      VertragAmOrtG P M ∧ KeinLogikHaltG O passes M ∧
      ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
        AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M' := by
  intro M hr
  have hI := zielInvR_erreichbar P O passes Q fs sp init e0 hO hRL hQ hlok hvoll hFrag hFuss
    (fun f => (hK f).1) hStart hex M hr
  have hP : KeinLogikHaltG O passes M :=
    fun t => fadenR_prueft hO hRL hQ (fun f => (hK f).2) t (hI.1 t)
  exact ⟨fun t ev hev => hI.2 t ev hev, hP, fun t hH hA => schritt_an_pruefung t (hP t) hH hA⟩

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

/-- **G MOVES AT EVERY `logik` CHECK -- the progress conjunct of
    `ziel_ort_ganz`, stated alone.** Under the premises of `ziel_ort_ganz`, on every reachable
    machine, a thread that stands at a `logik` check of G (`AnPruefungG`)
    and whose head's static holdings are exactly its held locks can step.
    No reachable machine is stuck at a loop invariant, a `forever`
    boundary with budget left, a `leave` out of a `traverse`, or a `state`
    transition. What else can stop a thread: `SATZKARTE.md` §13.5. -/
theorem ziel_ort_ganz_fortschritt (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (fs : List D.Fn) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (e0 : Ereignis D) (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hlok : AxEnsLokal Q) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussOrtGB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutZ P passes Q f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
        AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M' := by
  intro M hr
  exact (ziel_ort_ganz P O passes Q fs sp init e0 hO hRL hQ hlok hvoll hFrag hFuss hK hStart hex
    M hr).2.2

/-! ## CUTS:

  What is proved: `ziel_ort_ganz` -- over the repaired G, with callee
  frames (`KoerperGutRQ` over `RespektiertRahmen`), registers and `awaits`
  (`RegLokal`), declared axiom ensures `Q` (`AxVertragO Q O`, `AxEnsLokal Q`)
  and the new clause `KeineLogik`, every reachable machine satisfies
  `VertragAmOrtG`, `KeinLogikHaltG` (every `logik` test of G passes) and
  progress at the checks (`AnPruefungG` + `HeldGenau` gives a step).
  `ziel_ort_rahmen` and `ziel_ort_voll_ax` (register-local oracles) are
  special cases of the contract half (`ziel_ort_rahmen_aus_ganz`,
  `ziel_ort_voll_ax_lokal_aus_ganz`). A syntactic sufficient check for the
  new clause (`programmLogikFrei_ok`). Witnesses, probe A:
  `ZielOrtGanzZeuge.lean`.

  What is NOT covered:

  - Table and group invariants (`Logik.invariante`): they arise only in
    `rufAt` at a callee's return; G does not test them, `VertragAmOrtG` does
    not state them, and `KeineLogik` does not ask for them (its handlers
    answer no `logik` outcome, so a callee's owed invariants are neither
    assumed nor proved). NOT CARRIED.
  - Full progress. Proved: no reachable machine is stuck at a `logik` check,
    and at a check the rule fires given `HeldGenau`. Not proved: that every
    unfinished thread steps or waits on a lock or an `awaits`. What else can
    stop a thread (by rule): a lock held by another thread (`dannLocks`,
    `RufFreiG`); an invisible publication (`dannAwaits`, A10); a hardware
    outcome at the head (an axiom answer outside its declared type, a
    register answer outside its type or against its promise, a float result
    outside its range, a spent `forever` budget `ewig 0`); a `leave`/`next`
    inside an `else` end block that replaced the residue (the loop
    continuation is dropped by `dannNarrowElse`/`dannPruefFalsch`/
    `dannGleitNarrowElse`/`dannRegLiesElseFalsch`/the reason pops -- a
    modelling gap of G); the `HeldGenau` side condition, whose `⊇` half is
    no proved invariant; the shape of the caller at a binding or reason pop,
    no proved invariant either. A root frame at `ret`/`retGrund` is
    finished, not stuck.
  - Termination and `abstieg`: G has no depth bound; a recursion that does
    not end runs on in G, and no theorem bounds it.
  - Everything cut in `ZielOrtRahmen.lean` and `ZielOrtGeraet.lean`
    (locks-block-only readers, contracts over shared state at a lock
    boundary -- verdict probes B/C --, no-event declarations, reason answers
    without a frame, whole-carrier frames).
-/

#print axioms Gabbro.Grammatik.kopfR_keineLogik
#print axioms Gabbro.Grammatik.blatt_logik
#print axioms Gabbro.Grammatik.fadenR_prueft
#print axioms Gabbro.Grammatik.ziel_ort_ganz
#print axioms Gabbro.Grammatik.ziel_ort_ganz_vertrag
#print axioms Gabbro.Grammatik.ziel_ort_voll_ax_lokal_aus_ganz
#print axioms Gabbro.Grammatik.ziel_ort_rahmen_aus_ganz

#print axioms Gabbro.Grammatik.schritt_an_pruefung
#print axioms Gabbro.Grammatik.ziel_ort_ganz_fortschritt

end Gabbro.Grammatik
