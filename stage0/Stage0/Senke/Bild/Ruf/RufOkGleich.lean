/-
  File:      stage0/Stage0/Senke/Bild/Ruf/RufOkGleich.lean
  Subject:   **The call obligation up to read events** (package P3 of the closed calls of the image theorem, the (ii)
             of `EmittedZiel`, part 1). The image's handler is `rufAt` (it checks and READS the contracts); machine G
             realises the body run `rufRumpf` (`befund_vertrag`), for which the call obligation `RufOk` is proved at
             every depth (`rufOk_tief`). `RufOkGleich R C` names what connects the two: a handler `R'` related to
             `R` up to read events (`HandlerLG`, P1) that keeps `RufOk`. For `rufAt` it holds at every depth under a
             read-blind oracle, with `R' = rufRumpf` (`rufOk_gleich_tief`, from P2's `rufAt_rufRumpf_lg_alle`).

             The route: a decomposed step is transferred on the SEQUENTIAL side, not on the machine. A statement
             that ends normally under `R` from `σ` ends normally under `R'` from every `σm ≈ σ`, with the same
             environment and a `≈` world (`execStmt_lg`, `AusLG.ok_inv`; an early failure of the `R` side is an
             error outcome, so it cannot occur on a normal end). The exact machine lemma `randG_schritt` then runs
             that `R'` step. So the machine stands at a world `≈` to the sequential one (`RandGL`, `RandG` up to
             `≈`), and no lemma of the call machine (`gepoppt_zustand`, `heldB_eintritt`) is restated. Only the
             short direction of P2 is used: it needs no user duty and no `HeldB` discipline at the entry (that is
             what `NurAbstieg` would need for the converse direction, which this route does not use).

             **The oracle premises** (`LeseblindRS`/`LeseblindP`, `Gleich/Ausgang.lean`). The named class
             `LeseblindOK` beside `TorOK` and `SichtOK` carries the register/visibility half; every oracle of the
             goal theorem has it (`leseblindOK_regLokal`, `Ruf/Hardware.lean`: it follows from the named hardware
             assumption `RegLokal`). A single step of the fragment needs nothing more (the fragment has no foreign
             call, `axFrei_stmtR`); the handler relation for ALL callees (P2) also needs the foreign half or a
             program without foreign calls (`LeseblindP`), which a program whose bodies lie in the fragment is
             (`fremdFrei_endR`).
-/
module
public import Stage0.Senke.Bild.Korrespondenz
public import Stage0.Senke.Bild.Gleich.RufAt
public import Stage0.Senke.Bild.Gleich.AxFreiR
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T8
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-! ## 1. The named oracle property -/

/-- **The named oracle property of the image theorem with calls** (beside `TorOK` and `SichtOK`): register and
    visibility answers do not look at read events (`LeseblindRS`). The trace is ghost state; the extra read events
    of `rufAt` exist only in the sequential witness world. It follows from `RegLokal` (`leseblindOK_regLokal`). -/
class LeseblindOK (O : Orakel D) : Prop where
  blind : LeseblindRS O

/-- The read-blindness the named property carries. -/
theorem leseblind_von (O : Orakel D) [h : LeseblindOK O] : LeseblindRS O :=
  match h with
  | ⟨b⟩ => b

/-- Every read-blind oracle has the named property. -/
theorem leseblindOK_von {O : Orakel D} (h : Leseblind O) : LeseblindOK O :=
  ⟨h.rs⟩

/-- **Every oracle has the named property** (the oracle interface is read-blind, `leseblindRS_alle`). -/
instance leseblindOK_alle (O : Orakel D) : LeseblindOK O :=
  ⟨leseblindRS_alle O⟩

/-! ## 2. A normal end is related only to a normal end -/

/-- A statement outcome related to a normal end is a normal end with the same environment and a `≈` world. -/
theorem AusLG.ok_inv {Er : Fehlermarke D → Prop} {V : Vertrag D} {l : Bool} {Γ : Ctx} {σ : World D}
    {ρ : Env D Γ} {o : Ausgang V l Γ} (h : AusLG Er (.ok σ ρ) o) : ∃ σ', o = .ok σ' ρ ∧ WeltGleich σ σ' := by
  cases h with
  | ok hw => exact ⟨_, rfl, hw⟩

/-! ## 3. The call obligation up to read events -/

/-- **`RufOk` up to read events**: some handler `R'` answers like `R` up to read events (`HandlerLG`, every early
    failure of `R` admitted) and keeps the exact call obligation `RufOk` for the callees `C`. -/
def RufOkGleich (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (A : D.Lock → Prop)
    (R : ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g) (C : D.Fn → Prop) : Prop :=
  ∃ R' : ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g,
    HandlerLG (fun _ => True) R R' ∧ RufOk P O passes f A R' C

/-- A handler that respects `≈` itself and keeps `RufOk` keeps `RufOkGleich` (with `R' = R`). -/
theorem rufOk_aus_gleich {P : Programm D} {O : Orakel D} {passes : Nat} {f : Faden} {A : D.Lock → Prop}
    {R : ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g} {C : D.Fn → Prop}
    (hR : HandlerLG (fun _ => True) R R) (h : RufOk P O passes f A R C) : RufOkGleich P O passes f A R C :=
  ⟨R, hR, h⟩

/-- The body-running handler: `RufOk` gives `RufOkGleich` under a read-blind oracle. -/
theorem rufOkGleich_rufRumpf {P : Programm D} {O : Orakel D} {passes : Nat} {f : Faden} {A : D.Lock → Prop}
    {C : D.Fn → Prop} (hO : LeseblindP P O) (n : Nat) (h : RufOk P O passes f A (rufRumpf P O passes n) C) :
    RufOkGleich P O passes f A (rufRumpf P O passes n) C :=
  rufOk_aus_gleich (rufRumpf_lg (P := P) (passes := passes) (Er := fun _ => True) hO n) h

/-- **THE CALL OBLIGATION OF `rufAt`, UP TO READ EVENTS, AT EVERY DEPTH.** Under a read-blind oracle, the image's
    handler `rufAt n` keeps `RufOkGleich` for every callee admitted at depth `n` (`Tief P A n`): the body run
    `rufRumpf n` is related to it (`rufAt_rufRumpf_lg_alle`, P2) and keeps `RufOk` (`rufOk_tief`). -/
theorem rufOk_gleich_tief {P : Programm D} {O : Orakel D} {passes : Nat} (hO : LeseblindP P O) (f : Faden)
    (A : D.Lock → Prop) (n : Nat) : RufOkGleich P O passes f A (rufAt P O passes n) (Tief P A n) :=
  ⟨rufRumpf P O passes n, rufAt_rufRumpf_lg_alle (P := P) (passes := passes) hO n, rufOk_tief P O passes f A n⟩

/-- Without callees: `rufAt` keeps `RufOkGleich` for the empty callee set (the call-free image theorem). -/
theorem rufOkGleich_leer {P : Programm D} {O : Orakel D} {passes : Nat} (hO : LeseblindP P O) (f : Faden)
    (A : D.Lock → Prop) (n : Nat) : RufOkGleich P O passes f A (rufAt P O passes n) (fun _ => False) :=
  ⟨rufRumpf P O passes n, rufAt_rufRumpf_lg_alle (P := P) (passes := passes) hO n,
    rufOk_leer P O passes f A (rufRumpf P O passes n)⟩

/-! ## 4. Machine G at a boundary, up to read events -/

/-- **`RandG` up to read events**: machine G stands at the boundary in front of `eb` at a world `σm` that is `≈` to
    the sequential world `σ` (same memory, same trace once reads are erased), with the same environment. -/
def RandGL (thr : Faden) (stapel : List (RufRahmenG D)) (f : D.Fn) (rho : Env D (D.params f)) (s0 : World D)
    (Agl : D.Lock → Prop) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (eb : Endblock D (vertragVon D f) l Γ Λ)
    (M : RufMaschineG D) (σ : World D) (ρ : Env D Γ) : Prop :=
  ∃ σm : World D, WeltGleich σ σm ∧ RandG thr stapel f rho s0 Agl eb M σm ρ

/-- The exact boundary is one up to read events. -/
theorem randGL_von {thr : Faden} {stapel : List (RufRahmenG D)} {f : D.Fn} {rho : Env D (D.params f)}
    {s0 : World D} {Agl : D.Lock → Prop} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {eb : Endblock D (vertragVon D f) l Γ Λ} {M : RufMaschineG D} {σ : World D} {ρ : Env D Γ}
    (h : RandG thr stapel f rho s0 Agl eb M σ ρ) : RandGL thr stapel f rho s0 Agl eb M σ ρ :=
  ⟨σ, WeltGleich.refl σ, h⟩

/-- **One statement, machine G, up to read events**: from a boundary `≈` to the sequential world in front of `s`, a
    statement of the G fragment that ends normally under the image's handler `R` (calls of admitted callees
    included) is realised by steps of `thr` alone, to a boundary `≈` to the sequential world behind `s`. -/
theorem randGL_schritt {P : Programm D} {O : Orakel D} {passes : Nat} (hO : LeseblindRS O)
    {R : ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g} {Cg : D.Fn → Prop} {thr : Faden}
    {stapel : List (RufRahmenG D)} {f : D.Fn} {rho : Env D (D.params f)} {s0 : World D} {Agl : D.Lock → Prop}
    (hRuf : RufOkGleich P O passes thr Agl R Cg) {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D (vertragVon D f) l Γ Λ Λ'} {rest : Endblock D (vertragVon D f) l Γ Λ'} {M : RufMaschineG D}
    {σ σ1 : World D} {ρ ρ1 : Env D Γ} (hs : StmtR Agl Cg mr s) (hex : execStmt O passes R s σ ρ = .ok σ1 ρ1)
    (h : RandGL thr stapel f rho s0 Agl (.cons s rest) M σ ρ) :
    ∃ M', RufLaufG P O passes thr M M' ∧ RandGL thr stapel f rho s0 Agl rest M' σ1 ρ1 := by
  obtain ⟨σm, hw, hG⟩ := h
  obtain ⟨R', hRR, hOk⟩ := hRuf
  have hl := execStmt_lg (passes := passes) hRR hO s (Or.inl (axFrei_stmtR hs)) hw ρ
  rw [hex] at hl
  obtain ⟨σm1, hex', hw1⟩ := hl.ok_inv
  obtain ⟨M', hlauf, hG'⟩ := randG_schritt hOk hs hex' hG
  exact ⟨M', hlauf, σm1, hw1, hG'⟩

/-- **One binding, machine G, up to read events**: the step `endeBind` from a boundary `≈` to the sequential world;
    the value of `e` is the same on both sides (expressions do not see the trace). -/
theorem randGL_bind {P : Programm D} {O : Orakel D} {passes : Nat} {thr : Faden}
    {stapel : List (RufRahmenG D)} {f : D.Fn} {rho : Env D (D.params f)} {s0 : World D} {Agl : D.Lock → Prop}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} {e : Expr D Γ Λ τ}
    {rest : Endblock D (vertragVon D f) l (τ :: Γ) Λ} {M : RufMaschineG D} {σ : World D} {ρ : Env D Γ}
    (h : RandGL thr stapel f rho s0 Agl (.bind e rest) M σ ρ) :
    ∃ M', RufLaufG P O passes thr M M' ∧
      RandGL thr stapel f rho s0 Agl rest M' (σ.lese Λ e.orte)
        (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) := by
  obtain ⟨σm, hw, hG⟩ := h
  obtain ⟨M', hl, hG'⟩ := randG_bind (P := P) (O := O) (passes := passes) hG
  have hw1 : WeltGleich (σ.lese Λ e.orte) (σm.lese Λ e.orte) := WeltGleich.lese hw Λ e.orte
  refine ⟨M', hl, σm.lese Λ e.orte, hw1, ?_⟩
  rw [WeltGleich.wert' hw1 e ρ]
  exact hG'

#print axioms rufOk_gleich_tief
#print axioms randGL_schritt

end Gabbro.Stage0.Senke.BildLauf
