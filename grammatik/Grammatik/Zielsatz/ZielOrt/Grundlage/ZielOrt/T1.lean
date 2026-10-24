/-
  File:      Grammatik/ZielOrt.lean
  Subject:   THE GOAL OVER THE CONCURRENT CALL MACHINE G -- the premise
             classes, the lock facts on the REPAIRED G, and the re-check
             of the earlier finding.

  The goal: a user proves only their own logic (one Hoare triple per
  function, `KoerperGut`) plus named hardware assumptions (`GutO`); memory
  safety, data-race freedom and "contracts hold at their place in concurrent
  runs" (`VertragAmOrtG`) are carried by the language, with every further
  premise a decidable fact the checker computes (`programmImFragment`,
  `fussOrtB`) or a fact about the start configuration (`StartGut`,
  `StartExklusiv`).

  History. This file first REFUTED the goal over G (2026-09-13): the bare
  `gibt` step of G released a lock while a frame of the thread still named
  it, and a reachable machine violated `ensures lies`. G has since been
  repaired (`RufMaschineG.lean`: no bare `nimmt`/`gibt`, start threads hold
  their signature locks, `HeldGenau` on every step that reads or writes),
  and `rufG_haelt_statisch` (`RufHaeltG.lean`) makes "static holdings ⊆
  held locks" an invariant of every run.

  What this file proves.

  1. The conclusion `VertragAmOrtG` (§1), the user obligation `KoerperGut`
     (§2: the body triple requires -> ensures over the sequential semantics
     with ANY contract-respecting handler, plus the caller duty: every call
     the body makes meets the callee's `requires`), and the decidable
     program facts (§3) with their soundness (`fussOrtB_ok`,
     `schreiberHaeltB_ok`). The footprint `fussOrte` of a function now
     includes the contract carriers of the functions it calls directly: a
     caller reasons with its callees' contracts, so those carriers must be
     protected for the caller's whole frame too.
  2. The lock facts on the repaired G (§4): a step releases only a lock the
     head names (`offen_schrittG`), lock exclusivity from an exclusive start
     (`exklusivG`), and the one-step rely (`schritt_traeger`, `relyG`): a
     step of a thread leaves a carrier alone if it does not hold one of the
     carrier's guards or its head function may not write the carrier.
  3. The re-check of the finding (§5): the pivot of the old run (a frame of
     `lies` naming the lock while its thread does not hold it) is
     unreachable (`ziel_ort_gegenbeispiel_verschwindet`); and the start fact
     is needed: with every thread starting in `einzahlen` (holding the lock
     by signature) the start machine is not exclusive and a reachable
     machine of the repaired G still violates `ensures lies` (`geg_lauf`,
     `ziel_ort_gegenbeispiel`, `ziel_ort_form_falsch`).
  4. The conclusion is not vacuous (§6, `vertragAmOrtG_refP_zeuge`).

  The theorem `ziel_ort` itself is in `ZielOrtBeweis.lean`.
-/
import Grammatik.Logik.Ruf.Umkehr.RufUmkehrRufG
import Grammatik.Logik.Ruf.Umkehr.RufHaeltG
import Grammatik.Logik.Ruf.Hoare.HoareRuf
import Grammatik.Korpus.Referenz.ReferenzB
import Grammatik.Nebenlaeufigkeit.Sperren.RelySperre

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The conclusion: contracts at their place on every thread log of G -/

/-- `VertragAmOrtG`: at every `eintritt` event of every thread log the
    `requires` holds (with the logged actual `rho`, at the logged entry
    world), and at every `rueck` event the `ensures` holds (with the logged
    entry world `s0` as the `old` side, the logged return world `s1`, the
    actual `rho` and the actual result `v`). -/
def VertragAmOrtG (P : Programm D) (M : RufMaschineG D) : Prop :=
  ∀ (f : Faden) (ev : RufEreignisF D), ev ∈ (M.faeden f).log →
    (∀ (g : D.Fn) (rho : Env D (D.params g)) (s0 : World D),
      ev = RufEreignisF.eintritt g rho s0 → ReqAmEintritt P g s0 rho) ∧
    (∀ (g : D.Fn) (rho : Env D (D.params g)) (v : ErgVal D (D.erg g)) (s0 s1 : World D),
      ev = RufEreignisF.rueck g rho v s0 s1 → EnsAmRueck P g s0 s1 rho v)

/-! ## 2. The user obligation, one per function -/

/-- The call handler with the entry gate: a call whose `requires` is false
    at the entry world answers `logik (vorbedingung g)`; otherwise `R`
    answers. -/
def torRuf (P : Programm D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) :
    ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f :=
  fun g σ ρ =>
    if wahr? (eval σ (P.requires g) σ ρ) = true then R g σ ρ
    else RufAusgang.logik (Logik.vorbedingung g)

/-- A handler that never blames a caller itself: the only `vorbedingung`
    outcome of `torRuf P R` is the gate's own. -/
def OhneVorbedingung (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)) (e : Logik D),
    R g σ ρ = RufAusgang.logik e → ∀ g' : D.Fn, e ≠ Logik.vorbedingung g'

/-- **The user obligation of one function `f`.** For every call handler
    `R` that respects the contracts at their place (`RespektiertVertraege`,
    `HoareRuf.lean`) and never blames a caller itself, from every entry
    world `σ` and actual parameters `ρ` at which `requires f` holds:
    (1) whenever the body returns `v` in `σ'`, `ensures f` holds with the
    ACTUAL `σ`, `σ'`, `ρ`, `v` (the Hoare triple of the body), and
    (2) the body with the gated handler never ends in a failed `requires`:
    every call it makes meets the callee's `requires` (the caller duty).
    A statement about `f`'s body over the SEQUENTIAL semantics only. -/
def KoerperGut (P : Programm D) (O : Orakel D) (passes : Nat) (f : D.Fn) : Prop :=
  ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
    RespektiertVertraege P R → OhneVorbedingung R →
    ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ →
      (∀ (σ' : World D) (v : ErgVal D (D.erg f)),
        execEnd (V := vertragVon D f) O passes R (P.rumpf f) σ ρ = EndAusgang.zurueck σ' v →
          EnsAmRueck P f σ σ' ρ v) ∧
      (∀ g : D.Fn,
        execEnd (V := vertragVon D f) O passes (torRuf P R) (P.rumpf f) σ ρ ≠
          EndAusgang.logik (Logik.vorbedingung g))

/-- The entry obligation at the start: every thread's start function has
    its `requires` at the start world with the start parameters. -/
def StartGut (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) : Prop :=
  ∀ t : Faden, ReqAmEintritt P (init t).1 (sp.welt []) (init t).2

/-! ## 3. The decidable program facts

    All three are `Bool` computations over the program text and the
    declaration, over a member list `fs` of the functions (complete by
    `∀ g, g ∈ fs` in the soundness lemmas -- a finite enumeration of the
    declaration's function type). -/

/-- The covered fragment, syntactically: every body passes the check of the
    converse (`Endblock.kOk`, `RufUmkehrRufG.lean`: no loops, no abrupt
    exits, no error channel, no indirect call, no oracle form). -/
def programmImFragment (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun f => (P.rumpf f).kOk

/- Footprint carriers of a function body: what the body may read on any path
   (`e.orte` of every expression it evaluates) AND the carriers of the
   `requires`/`ensures` of every function it calls directly. A caller's
   sequential reasoning about a call uses the callee's contract; those
   carriers must stay put while the caller's frame is live, exactly like
   the caller's own reads. -/
mutual

def stmtOrteP (P : Programm D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → List (D.Tab ⊕ D.Glob)
  | .assignSlot _ _ i e _ _ => i.orte ++ e.orte
  | .assignThru p _ _ _ i e _ _ => p.orte ++ i.orte ++ e.orte
  | .assignSlotRef r _ _ _ _ e _ _ => r.orte ++ e.orte
  | .assignGlob _ e _ _ => e.orte
  | .putBytes _ _ _ _ i _ _ e _ _ => i.orte ++ e.orte
  | .assignVar _ e => e.orte
  | .shift t _ _ i _ _ _ _ _ _ => .inl t :: i.orte
  | .ite c t e => c.orte ++ blockOrteP P t ++ blockOrteP P e
  | .onOption o p a => o.orte ++ blockOrteP P p ++ blockOrteP P a
  | .onTag v arms => v.orte ++ armsOrteP P arms
  | .onWhy r arms => r.orte ++ grundArmsOrteP P arms
  | .call g args _ _ => args.orte ++ ((P.requires g).orte ++ (P.ensures g).orte)
  | .callInd p args _ _ => p.orte ++ args.orte
  | .locks _ _ body => blockOrteP P body
  | .breaking _ body => blockOrteP P body
  | .traverse _ inv body => inv.orte ++ blockOrteP P body
  | .retry _ bis body ueber => bis.orte ++ blockOrteP P body ++ blockOrteP P ueber
  | .forever _ inv body => inv.orte ++ blockOrteP P body
  | .axiomCall _ args _ _ _ _ _ => args.orte
  | .regWrite _ _ e => e.orte
  | .transition _ _ _ _ _ _ _ => []
  | .publish _ e _ _ _ _ => e.orte
  | .advances _ _ _ _ => []
  | .retires _ _ _ _ => []
  | .ret e _ => e.orte
  | .retWhy _ _ => []
  | .leave _ => []
  | .next _ => []

def blockOrteP (P : Programm D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → List (D.Tab ⊕ D.Glob)
  | .nil => []
  | .cons s rest => stmtOrteP P s ++ blockOrteP P rest
  | .bind e rest => e.orte ++ blockOrteP P rest
  | .bindCall g args _ _ _ rest =>
      args.orte ++ ((P.requires g).orte ++ (P.ensures g).orte) ++ blockOrteP P rest
  | .bindCallInd p args _ _ _ rest => p.orte ++ args.orte ++ blockOrteP P rest
  | .bindCallElse g args _ _ _ err rest =>
      args.orte ++ ((P.requires g).orte ++ (P.ensures g).orte) ++ endblockOrteP P err ++
        blockOrteP P rest
  | .bindAxiom _ args _ _ _ _ _ rest => args.orte ++ blockOrteP P rest
  | .bindAxiomElse _ args _ _ _ _ _ _ err rest =>
      args.orte ++ endblockOrteP P err ++ blockOrteP P rest
  | .regRead _ _ rest => blockOrteP P rest
  | .regReadElse _ _ zusage sonst rest =>
      zusage.orte ++ endblockOrteP P sonst ++ blockOrteP P rest
  | .awaits g _ _ _ _ rest => .inr g :: blockOrteP P rest
  | .exchange g neu _ _ rest => .inr g :: neu.orte ++ blockOrteP P rest
  | .narrow e _ _ sonst rest =>
      e.orte ++ endblockOrteP P sonst ++ blockOrteP P rest
  | .check c sonst rest =>
      c.orte ++ endblockOrteP P sonst ++ blockOrteP P rest
  | .float _ a b _ _ rest => a.orte ++ b.orte ++ blockOrteP P rest
  | .floatLit _ _ _ rest => blockOrteP P rest
  | .floatOf e _ _ rest => e.orte ++ blockOrteP P rest
  | .floatNarrow e _ _ sonst rest =>
      e.orte ++ endblockOrteP P sonst ++ blockOrteP P rest

def endblockOrteP (P : Programm D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → List (D.Tab ⊕ D.Glob)
  | .ret e _ => e.orte
  | .retWhy _ _ => []
  | .leave _ => []
  | .next _ => []
  | .cons s rest => stmtOrteP P s ++ endblockOrteP P rest
  | .bind e rest => e.orte ++ endblockOrteP P rest
  | .bindCall g args _ _ _ rest =>
      args.orte ++ ((P.requires g).orte ++ (P.ensures g).orte) ++ endblockOrteP P rest
  | .bindCallElse g args _ _ _ err rest =>
      args.orte ++ ((P.requires g).orte ++ (P.ensures g).orte) ++ endblockOrteP P err ++
        endblockOrteP P rest
  | .bindAxiom _ args _ _ _ _ _ rest => args.orte ++ endblockOrteP P rest
  | .bindAxiomElse _ args _ _ _ _ _ _ err rest =>
      args.orte ++ endblockOrteP P err ++ endblockOrteP P rest
  | .regRead _ _ rest => endblockOrteP P rest
  | .regReadElse _ _ zusage sonst rest =>
      zusage.orte ++ endblockOrteP P sonst ++ endblockOrteP P rest
  | .awaits g _ _ _ _ rest => .inr g :: endblockOrteP P rest
  | .bindCallInd p args _ _ _ rest => p.orte ++ args.orte ++ endblockOrteP P rest

def armsOrteP (P : Programm D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    Arms D V l Γ Λ Λ' cs → List (D.Tab ⊕ D.Glob)
  | .nil => []
  | .cons b rest => blockOrteP P b ++ armsOrteP P rest

def grundArmsOrteP (P : Programm D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} : GrundArms D V l Γ Λ Λ' n → List (D.Tab ⊕ D.Glob)
  | .nil => []
  | .cons b rest => blockOrteP P b ++ grundArmsOrteP P rest

end
/-- An end block run as a block (`Endblock.alsBlock`) reads the places the
    end block reads. -/
theorem blockOrteP_alsBlock (P : Programm D) {V : Vertrag D} {l : Bool} :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ),
      blockOrteP P e.alsBlock.2 = endblockOrteP P e
  | _, _, .ret _ _ => by simp [Endblock.alsBlock, blockOrteP, stmtOrteP, endblockOrteP]
  | _, _, .retWhy _ _ => by simp [Endblock.alsBlock, blockOrteP, stmtOrteP, endblockOrteP]
  | _, _, .leave _ => by simp [Endblock.alsBlock, blockOrteP, stmtOrteP, endblockOrteP]
  | _, _, .next _ => by simp [Endblock.alsBlock, blockOrteP, stmtOrteP, endblockOrteP]
  | _, _, .cons s rest => by
      simp only [Endblock.alsBlock, blockOrteP, endblockOrteP, blockOrteP_alsBlock P rest]
  | _, _, .bind e rest => by
      simp only [Endblock.alsBlock, blockOrteP, endblockOrteP, blockOrteP_alsBlock P rest]
  | _, _, .bindCall _ args _ _ _ rest => by
      simp only [Endblock.alsBlock, blockOrteP, endblockOrteP, blockOrteP_alsBlock P rest]
  | _, _, .bindAxiom _ args _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, blockOrteP, endblockOrteP, blockOrteP_alsBlock P rest]
  | _, _, .bindCallElse _ args _ _ _ err rest => by
      simp only [Endblock.alsBlock, blockOrteP, endblockOrteP, blockOrteP_alsBlock P rest]
  | _, _, .bindAxiomElse _ args _ _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, blockOrteP, endblockOrteP, blockOrteP_alsBlock P rest]
  | _, _, .regRead r hk rest => by
      simp only [Endblock.alsBlock, blockOrteP, endblockOrteP, blockOrteP_alsBlock P rest]
  | _, _, .regReadElse r hk z sonst rest => by
      simp only [Endblock.alsBlock, blockOrteP, endblockOrteP, blockOrteP_alsBlock P rest]
  | _, _, .awaits g pl hp hL hat rest => by
      simp only [Endblock.alsBlock, blockOrteP, endblockOrteP, blockOrteP_alsBlock P rest]
  | _, _, .bindCallInd p args he hp hr rest => by
      simp only [Endblock.alsBlock, blockOrteP, endblockOrteP, blockOrteP_alsBlock P rest]

/-- The carriers of the table and group invariants `f` owes at its return
    (`schuldet`: `f` writes one of their carriers; `rufAt` checks exactly
    these, THEOREM-MAP §15.4). -/
def invOrteP (P : Programm D) (f : D.Fn) : List (D.Tab ⊕ D.Glob) :=
  (D.invs.filter (schuldet f)).flatMap fun i => (P.invariante i).orte

/-- The footprint of `f`: its contract carriers, its body reads, the
    contract carriers of every function it calls directly, and the carriers
    of the invariants it owes (`invOrteP`, since 2026-09-13). A foreign step
    must leave exactly these carriers alone for `f`'s sequential reasoning
    to survive an interleaving. -/
def fussOrte (P : Programm D) (f : D.Fn) : List (D.Tab ⊕ D.Glob) :=
  (P.requires f).orte ++ (P.ensures f).orte ++ endblockOrteP P (P.rumpf f) ++ invOrteP P f

/-- The guard locks of a carrier: the lock entries of its watch list. -/
def waechter : List (D.Lock ⊕ (D.Marke × Nat)) → List D.Lock
  | [] => []
  | .inl L :: rest => L :: waechter rest
  | .inr _ :: rest => waechter rest

theorem waechter_mem {ws : List (D.Lock ⊕ (D.Marke × Nat))} {L : D.Lock} :
    L ∈ waechter ws ↔ Sum.inl L ∈ ws := by
  induction ws with
  | nil => simp [waechter]
  | cons w rest ih =>
      cases w with
      | inl L' => simp [waechter, ih]
      | inr _ => simp [waechter, ih]

/-- The guard locks of a carrier `o`. -/
def waechterVon : D.Tab ⊕ D.Glob → List D.Lock
  | .inl t => waechter (D.braucht t)
  | .inr x => waechter (D.gbraucht x)

theorem waechterVon_mem {o : D.Tab ⊕ D.Glob} {L : D.Lock} :
    L ∈ waechterVon o ↔ Bewacht o L := by
  cases o with
  | inl t => exact waechter_mem
  | inr x => exact waechter_mem

/-- **The footprint check.** Every footprint carrier of `f` is guarded by
    a lock that `f` holds BY SIGNATURE (for its whole body, not in a
    `locks` block), or no function writes it. -/
def fussOrtB (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun f => (fussOrte P f).all fun o =>
    (waechterVon o).any (fun L => decide (L ∈ D.haelt f)) ||
    fs.all (fun g => !(TraegerSchreibt g o))

/-- The footprint property that `fussOrtB` decides. -/
def FussOrtOk (P : Programm D) (f : D.Fn) : Prop :=
  ∀ o ∈ fussOrte P f,
    (∃ L : D.Lock, Bewacht o L ∧ L ∈ D.haelt f) ∨ (∀ g : D.Fn, TraegerSchreibt g o = false)

/-- Soundness of the footprint check. Both premises are used: `h` gives the
    per-carrier test, `hvoll` lifts the member list to every function. -/
theorem fussOrtB_ok (P : Programm D) (fs : List D.Fn) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (h : fussOrtB P fs = true) (f : D.Fn) : FussOrtOk P f := by
  intro o ho
  have h1 := (List.all_eq_true.mp h) f (hvoll f)
  have h2 := (List.all_eq_true.mp h1) o ho
  simp only [Bool.or_eq_true] at h2
  rcases h2 with hg | hfrei
  · obtain ⟨L, hL, hLh⟩ := List.any_eq_true.mp hg
    exact Or.inl ⟨L, waechterVon_mem.mp hL, of_decide_eq_true hLh⟩
  · refine Or.inr fun g => ?_
    have := (List.all_eq_true.mp hfrei) g (hvoll g)
    simpa using this

/-- **The writer discipline.** Every function that writes a footprint
    carrier of some function holds EVERY guard of that carrier by
    signature. -/
def schreiberHaeltB (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun f => (fussOrte P f).all fun o => fs.all fun g =>
    !(TraegerSchreibt g o) || (waechterVon o).all (fun L => decide (L ∈ D.haelt g))

/-- Soundness of the writer discipline check. -/
theorem schreiberHaeltB_ok (P : Programm D) (fs : List D.Fn) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (h : schreiberHaeltB P fs = true) (f : D.Fn) (o : D.Tab ⊕ D.Glob) (ho : o ∈ fussOrte P f)
    (g : D.Fn) (hw : TraegerSchreibt g o = true) (L : D.Lock) (hL : Bewacht o L) :
    L ∈ D.haelt g := by
  have h1 := (List.all_eq_true.mp h) f (hvoll f)
  have h2 := (List.all_eq_true.mp h1) o ho
  have h3 := (List.all_eq_true.mp h2) g (hvoll g)
  rw [hw] at h3
  simp only [Bool.not_true, Bool.false_or] at h3
  exact of_decide_eq_true ((List.all_eq_true.mp h3) L (waechterVon_mem.mpr hL))

/-! ## 4. The lock facts on the repaired G -/


end Gabbro.Grammatik
