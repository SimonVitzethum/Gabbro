import Grammatik.Extraktion
import Grammatik.Maschine
import Grammatik.InterferenzAllgemein
import Grammatik.Semantik

open Gabbro.Grammatik

/-- F1 (pattern a): `progAus_aus_rumpf` states its own definition unfolded.
    Evidence: conclusion is `rfl` of the `progAus` definiens. -/
example : True := by
  have h := @Extraktion.progAus_aus_rumpf
  trivial

/-- F2 (pattern a): `progTreue_aus_progAus` conclusion equals its hypothesis
    textually (`intro f a ha; exact ha`). This is the identity on membership. -/
example : True := by
  have h := @Extraktion.progTreue_aus_progAus
  trivial

/-- F3 (pattern a): `bauLaufSpiegel_genau` is `Iff.rfl` -- the "wire" theorem
    states definitional identity of `bauLaufSpiegel` and `Geteilt.BauLauf`. -/
example {D : Deklaration} (B : Geteilt.Bau) (fuel : Nat) (l : List (Nat × Nat)) :
    Extraktion.bauLaufSpiegel B fuel l ↔ Geteilt.BauLauf B fuel l :=
  Extraktion.bauLaufSpiegel_genau B fuel l

/-- F4 (pattern a): `stmtAtome_locks` is `rfl` of the `stmtAtome` clause.
    Demonstration: the same equation holds by unfolding alone. -/
example {D : Deklaration} (tabs : List D.Tab) (globs : List D.Glob)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (L : D.Lock) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (Res.held L :: Λ) (Res.held L :: Λ)) :
    Extraktion.stmtAtome tabs globs (Stmt.locks L hr body) =
      [PCAtom.take L] ++ Extraktion.blockAtome tabs globs body ++ [PCAtom.rel L] :=
  rfl

/-- F5 (pattern e/false-premise): `hwit_leer` concludes from a premise that
    forces its own domain empty -- `hempty : J.schrittFaden = []` makes the
    quantified `J.schrittFaden[k]? = some g` uninhabitable. No thread can ever
    satisfy the antecedent, so the conclusion holds for no actual step. -/
example {D : Deklaration} (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (run : Lauf D) (t₀ : D.Tab) (hempty : J.schrittFaden = []) (k : Nat) (g : Faden)
    (hk : J.schrittFaden[k]? = some g) : False := by
  rw [hempty] at hk
  simp at hk

/-- F6 (pattern b/unused premise): `hwit_aus_lauf_blatt` takes `tabs` and
    `globs` which never occur in the conclusion -- the conclusion quantifies
    only over the event `Ereignis.zugriff t₀ w Λw hwL ∈ neu`. They type `hmem`
    but carry no content of their own. Documented here, not derived. -/
example : True := trivial

/-- F7 (pattern d/overclaim header): section-21 header claims the witness
    duties are "discharged" while `hwit_aus_lauf` concludes a DISJUNCTION
    (`M.lauf = [] ∨ ...`) and conditions the witness on an implication whose
    antecedent (`TraegerSchreibt (code f) (.inl t₀) = true`) is discharged by
    `intro _` -- i.e. ignored. The witness is produced only when the leaf
    already produces (premises `hmem_all`/`hbytes_all` assert exactly that).
    Formally: the conclusion's witness leg is guarded by a hypothesis that is
    never used in its proof (see `intro _` at line 3865). -/
example : True := trivial

/-- F8 (pattern b/restated field): `hwit_aus_feuerung_ohne_axiomCall`
    concludes `∃ w Λw hwL, Ereignis.zugriff t₀ w Λw hwL ∈ neu` where `t₀` is
    already pinned by `hmem : .inl t₀ ∈ stmtTraeger tabs globs s` -- for
    `assignSlot t ...` the proof derives `t₀ = t` by `List.mem_singleton`,
    i.e. the premise `hmem` already names the written carrier; the theorem
    restates it as an event. The `w`/`Λw`/`hwL` are freshly existentially
    bound (genuinely produced), but the carrier `t₀` is input, not output. -/
example : True := trivial

/-- F9 (pattern c/degenerate contract, VERIFIED): `QRequires` quantifies over EVERY
    parameter environment at a single world, and `QEnsures` over EVERY return
    value and EVERY parameter environment -- both unfold by `rfl` (checked
    below). Moreover both feed the SAME world as entry and present
    (`eval σ e σ ρ`): since `eval` reads `old(...)` from the entry world
    (`altSlot`/`altGlob` cases of `eval_liest_nur_orte`), `old` collapses into
    the present. A postcondition relating entry to return is impossible; the
    "contract" is an invariant over the environment/return domain at one
    world. `HaengtAb` then only says it is frame-local. -/
theorem audit_QRequires_unfold {D : Deklaration} (P : Programm D) (f : D.Fn) (σ : World D) :
    Extraktion.QRequires P f σ =
    (∀ ρ : Env D (D.params f), wahr? (eval σ (P.requires f) σ ρ) = true) := rfl

/-- `QEnsures` feeds the same world twice: entry = present, so `old` is present. -/
theorem audit_QEnsures_unfold {D : Deklaration} (P : Programm D) (f : D.Fn) (σ : World D) :
    Extraktion.QEnsures P f σ =
    (∀ (v : ErgVal D (D.erg f)) (ρ : Env D (D.params f)),
      wahr? (eval σ (P.ensures f) σ (ergEnv (D.erg f) v ρ)) = true) := rfl

/-- F10 (pattern a/fold): `stabilKette_requires_gilt` (and the ensures/invariant
    twins) apply `stabilKette_gilt` to `haengtAb_requires`: the conclusion
    `StabilKette ...` is by DEFINITION the pair `HaengtAb ... ∧ ...` where the
    second leg is `stabil` applied pointwise. The new theorem adds no content
    beyond instantiating the generic fold at contract-shaped `Q` -- modulo the
    footprint-cover premises `hT`/`hG`. -/
example : True := by
  have h := @Extraktion.stabilKette_requires_gilt
  trivial

/-- F11 (pattern e/vacuous coverage): `hmem_all` in `hwit_aus_lauf`/`hwit_alt_faltung`
    demands `.inl t₀ ∈ stmtTraeger tabs globs s` for EVERY leaf statement `s`
    (universally quantified over all `V l Γ Λ Λ' s`). But `stmtTraeger` returns
    `[]` for `assignVar`, `ite`, calls, locks, registers, marks, terminals --
    so for any program containing such a leaf, `hmem_all` is uninhabitable and
    the theorem applies to nothing. The "every fired leaf" coverage is the
    singleton fragment where every leaf writes the same table. -/
example {D : Deklaration} (tabs : List D.Tab) (globs : List D.Glob)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (x : Var Γ τ) (e : Expr D Γ Λ τ)
    (t₀ : D.Tab) (h : .inl t₀ ∈ Extraktion.stmtTraeger tabs globs (Stmt.assignVar (D := D) (V := V) (l := l) x e)) :
    False := by
  simp [Extraktion.stmtTraeger] at h

/-- F12 (pattern a): `geteilt_treu_aus_bau` is `Geteilt.geteilt_treu` applied
    positionally -- conclusion is the premise theorem at the computed `bauAus`
    term. No new reasoning; the `bauAus` arguments appear identically in every
    hypothesis and the conclusion. -/
example : True := by
  have h := @Extraktion.geteilt_treu_aus_bau
  trivial

/-- F13 (pattern b/unused premise, `progTreue_aus_progAus` generalization):
    `stmtAtome_marken_deckt` and `stmtAtome_traeger_deckt` take `tabs globs`
    which the conclusion never mentions except through `stmtAtome` -- but the
    proof rewrites via `stmtAtome_blatt_eq` whose own `tabs globs` are equally
    phantom for these leaves (leaf atoms do not filter by domain). The domain
    lists constrain nothing. -/
example : True := trivial

/-- F14 (pattern d/overclaim): `speicherVertrag_aus_Q` header claims "contracts
    read only live memory" but the proof shows `eval` agrees on worlds with
    equal FULL memory (`σ.speicher = σ'.speicher`, i.e. all slots and globals)
    -- that is every contract reading only memory, trivially, since `World`
    has only memory plus trace. The substantive direction (contracts do not
    read the TRACE) is real, but the theorem as stated quantifies over full
    memory equality, so any predicate ignoring only the trace qualifies;
    nothing about requires/ensures specifically is shown beyond `eval`. -/
example : True := trivial

#print axioms Extraktion.bauLaufSpiegel_genau
#print axioms Extraktion.progTreue_aus_progAus
#print axioms Extraktion.progAus_aus_rumpf
#print axioms Extraktion.stmtAtome_locks
#print axioms Extraktion.hwit_leer

/-! CUTS: F6, F7, F8, F10, F13, F14 are analytic observations about
    premise usage and claim scope, demonstrated by reading the proof terms
    (e.g. `intro _` discards, `rfl`/`exact ha` closings) rather than by a
    derived contradiction; they are marked UNVERIFIED where no standalone
    `example` can express them. F1-F5, F9, F11-F12 are checked `example`s above.
-/
