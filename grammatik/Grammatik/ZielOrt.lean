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
import Grammatik.RufUmkehrRufG
import Grammatik.RufHaeltG
import Grammatik.HoareRuf
import Grammatik.ReferenzB
import Grammatik.RelySperre

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
  | .assignDurch p _ _ _ i e _ _ => p.orte ++ i.orte ++ e.orte
  | .assignGlob _ e _ _ => e.orte
  | .schreibBytes _ _ _ _ i _ _ e _ _ => i.orte ++ e.orte
  | .assignVar _ e => e.orte
  | .uebergang t _ _ i _ _ _ _ _ _ => .inl t :: i.orte
  | .ite c t e => c.orte ++ blockOrteP P t ++ blockOrteP P e
  | .onOption o p a => o.orte ++ blockOrteP P p ++ blockOrteP P a
  | .onTag v arms => v.orte ++ armsOrteP P arms
  | .onGrund r arms => r.orte ++ grundArmsOrteP P arms
  | .call g args _ _ => args.orte ++ ((P.requires g).orte ++ (P.ensures g).orte)
  | .callInd p args _ _ => p.orte ++ args.orte
  | .locks _ _ body => blockOrteP P body
  | .breaking _ body => blockOrteP P body
  | .traverse _ inv body => inv.orte ++ blockOrteP P body
  | .retry _ bis body ueber => bis.orte ++ blockOrteP P body ++ blockOrteP P ueber
  | .forever _ inv body => inv.orte ++ blockOrteP P body
  | .axiomCall _ args _ _ _ _ _ => args.orte
  | .regSchreib _ _ e => e.orte
  | .transition _ _ _ _ _ _ _ => []
  | .publish _ e _ _ _ _ => e.orte
  | .advances _ _ _ _ => []
  | .retires _ _ _ _ => []
  | .ret e _ => e.orte
  | .retGrund _ _ => []
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
  | .regLies _ _ rest => blockOrteP P rest
  | .regLiesElse _ _ zusage sonst rest =>
      zusage.orte ++ endblockOrteP P sonst ++ blockOrteP P rest
  | .awaits g _ _ _ rest => .inr g :: blockOrteP P rest
  | .exchange g neu _ _ rest => .inr g :: neu.orte ++ blockOrteP P rest
  | .narrow e _ _ sonst rest =>
      e.orte ++ endblockOrteP P sonst ++ blockOrteP P rest
  | .pruefung c sonst rest =>
      c.orte ++ endblockOrteP P sonst ++ blockOrteP P rest
  | .gleit _ a b _ _ rest => a.orte ++ b.orte ++ blockOrteP P rest
  | .gleitLit _ _ _ rest => blockOrteP P rest
  | .gleitVon e _ _ rest => e.orte ++ blockOrteP P rest
  | .gleitNarrow e _ _ sonst rest =>
      e.orte ++ endblockOrteP P sonst ++ blockOrteP P rest

def endblockOrteP (P : Programm D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → List (D.Tab ⊕ D.Glob)
  | .ret e _ => e.orte
  | .retGrund _ _ => []
  | .leave _ => []
  | .next _ => []
  | .cons s rest => stmtOrteP P s ++ endblockOrteP P rest
  | .bind e rest => e.orte ++ endblockOrteP P rest

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

/-- The footprint of `f`: its contract carriers, its body reads, and the
    contract carriers of every function it calls directly. A foreign step
    must leave exactly these carriers alone for `f`'s sequential reasoning
    to survive an interleaving. -/
def fussOrte (P : Programm D) (f : D.Fn) : List (D.Tab ⊕ D.Glob) :=
  (P.requires f).orte ++ (P.ensures f).orte ++ endblockOrteP P (P.rumpf f)

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

section Sperren

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- A leaf keeps the held locks (`stmt_gut`, `Brav` leg). -/
theorem blatt_offen (hO : GutO O) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ)
    (hΛ : HeldGenau Λ (offen σ.spur)) (σ' : World D) (ρ' : Env D Γ)
    (hst : execStmt O passes keinRuf s σ ρ = Ausgang.ok σ' ρ') :
    offen σ'.spur = offen σ.spur := by
  have hw : (execStmt O passes keinRuf s σ ρ).welt = some σ' := by rw [hst]; rfl
  exact ((stmt_gut O passes keinRuf keinRuf_gut hO s σ ρ hΛ) σ' hw).2.1

/-- Reads keep the held locks. -/
theorem lese_offen (σ : World D) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    offen (σ.lese Λ os).spur = offen σ.spur :=
  lese_haelt σ Λ os

/-- **How one step moves the held locks of the acting thread** on the
    repaired G: they stay; or one lock `L` is added while no other thread
    holds it (`dannLocks`, the only take); or one lock is released that the
    head's static holdings NAME (`freiGib` and the `frei` peels, the
    release markers of an enclosing `locks` of the head frame). The bare
    `gibt` -- a release of ANY held lock at ANY time -- is gone: there is
    no step that releases a lock the head does not name. -/
theorem offen_schrittG (hO : GutO O) {M M' : RufMaschineG D} {f : Faden}
    (hs : RufSchrittG P O passes M f M') :
    offen (M'.faeden f).spur = offen (M.faeden f).spur ∨
    (∃ L, RufFreiG M f L ∧ offen (M'.faeden f).spur = L :: offen (M.faeden f).spur) ∨
    (∃ L, Res.held L ∈ (M.faeden f).kopf.rest.2.2.1 ∧
      offen (M'.faeden f).spur = (offen (M.faeden f).spur).erase L) := by
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ _ _ hΛ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      exact Or.inl (blatt_offen hO s _ ρ hΛ σ' ρ' hstep)
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ _ _ hΛ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      exact Or.inl (blatt_offen hO s _ ρ hΛ σ' ρ' hstep)
  | dannLocks l Γ Λ Λ'' L _ _ _ _ _ _ _ _ hfrei =>
      simp only [rufUpdateG_self]
      exact Or.inr (Or.inl ⟨L, hfrei, rfl⟩)
  | freiGib l Γ Λ L k ρ hhead =>
      simp only [rufUpdateG_self]
      refine Or.inr (Or.inr ⟨L, ?_, rfl⟩)
      rw [hhead]
      exact List.mem_cons_self
  | peelFreiLeave l Γ Λ L rest k ρ hl hhead =>
      simp only [rufUpdateG_self]
      refine Or.inr (Or.inr ⟨L, ?_, rfl⟩)
      rw [hhead]
      exact (Block.held_iff rest L).mp List.mem_cons_self
  | peelFreiNext l Γ Λ L rest k ρ hl hhead =>
      simp only [rufUpdateG_self]
      refine Or.inr (Or.inr ⟨L, ?_, rfl⟩)
      rw [hhead]
      exact (Block.held_iff rest L).mp List.mem_cons_self
  | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hl _ σ' ρ' _ hstep _ _ σ₁ hs₁ =>
      simp only [rufUpdateG_self]
      refine Or.inl ?_
      rw [hs₁, lese_offen, leave_welt' _ _ _ _ _ _ _ _ hstep]
      rfl
  | dannNextTrav l Γ Λ t inv body is k rest i ρ hl _ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      refine Or.inl ?_
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      rfl
  | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hl _ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      refine Or.inl ?_
      rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
      rfl
  | dannNextWieder l Γ Λ n bis body ueber k rest ρ hl _ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      refine Or.inl ?_
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      rfl
  | dannLeaveEwig l Γ Λ a n inv body k rest ρ hl _ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      refine Or.inl ?_
      rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
      rfl
  | dannNextEwig l Γ Λ a n inv body k rest ρ hl _ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      refine Or.inl ?_
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      rfl
  | dannExchange l Γ Λ Λ' g neuE hw hL rest k ρ _ σ₁ hs₁ σ₂ hs₂ =>
      simp only [rufUpdateG_self]
      refine Or.inl ?_
      rw [hs₂, hs₁]
      exact lese_offen _ _ _
  | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ _ σ₁ hs₁ σ₂ v hax =>
      simp only [rufUpdateG_self]
      refine Or.inl ?_
      rw [axiom_offen' hO _ _ _ _ _ hax, hs₁]
      exact lese_offen _ _ _
  | _ =>
      subst_vars
      simp only [rufUpdateG_self]
      first
        | exact Or.inl trivial
        | exact Or.inl rfl
        | exact Or.inl (lese_offen _ _ _)

/-- The start trace of a thread holds exactly its start function's
    signature locks. -/
theorem offen_start (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (t : Faden) (L : D.Lock) :
    L ∈ offen ((RufStartG P sp init).faeden t).spur ↔ L ∈ D.haelt (init t).1 := by
  have e : ((RufStartG P sp init).faeden t).spur = startSpur (init t).1 := by
    show (match init t with
      | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
          Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
          [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D)).spur = startSpur (init t).1
    cases init t
    rfl
  rw [e]
  exact offen_startSpur _ L

/-- **Lock exclusivity on the repaired G.** On every reachable machine, a
    lock held by thread `f` is held by no other thread. Induction over
    reachability with `offen_schrittG`: a lock enters a held set only
    through `dannLocks`, whose `RufFreiG` premise says no other thread holds
    it; at the start, only through the start trace, exclusive by
    `StartExklusiv`. -/
theorem exklusivG (hO : GutO O) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M : RufMaschineG D} (h : RufErreichbarG P O passes (RufStartG P sp init) M) :
    ∀ (f g : Faden), f ≠ g → ∀ L : D.Lock,
      L ∈ offen (M.faeden f).spur → L ∉ offen (M.faeden g).spur := by
  induction h with
  | start =>
      intro f g hfg L hLf hLg
      exact hex f g hfg L ((offen_start sp init f L).mp hLf) ((offen_start sp init g L).mp hLg)
  | schritt M M' f0 _ hs ih =>
      intro f g hfg L hLf hLg
      have hfremd : ∀ t, t ≠ f0 → M'.faeden t = M.faeden t :=
        fun t ht => rufSchrittG_fremd hs t ht
      by_cases hf : f = f0
      · subst hf
        have hg : g ≠ f := fun e => hfg e.symm
        rw [hfremd g hg] at hLg
        rcases offen_schrittG hO hs with e | ⟨L', hfrei, e⟩ | ⟨L', _, e⟩
        · rw [e] at hLf
          exact ih f g hfg L hLf hLg
        · rw [e] at hLf
          rcases List.mem_cons.mp hLf with rfl | hLf
          · exact hfrei g hg hLg
          · exact ih f g hfg L hLf hLg
        · rw [e] at hLf
          exact ih f g hfg L (List.mem_of_mem_erase hLf) hLg
      · rw [hfremd f hf] at hLf
        by_cases hg : g = f0
        · subst hg
          rcases offen_schrittG hO hs with e | ⟨L', hfrei, e⟩ | ⟨L', _, e⟩
          · rw [e] at hLg
            exact ih f g hfg L hLf hLg
          · rw [e] at hLg
            rcases List.mem_cons.mp hLg with rfl | hLg
            · exact hfrei f hf hLf
            · exact ih f g hfg L hLf hLg
          · rw [e] at hLg
            exact ih f g hfg L hLf (List.mem_of_mem_erase hLg)
        · rw [hfremd g hg] at hLg
          exact ih f g hfg L hLf hLg

/-- A G machine seen as a generic machine (only memory and traces are read
    by the merged leaf lemmas). -/
def genAusG (M : RufMaschineG D) : GenMaschine D :=
  ⟨M.speicher, fun g => (M.faeden g).spur, M.lauf, M.start, [], 0⟩

/-- Agreement of two memories on one carrier. -/
def TraegerGleich (s s' : Speicher D) : D.Tab ⊕ D.Glob → Prop
  | .inl t => s.slots t = s'.slots t
  | .inr x => s.globs x = s'.globs x

theorem traegerGleich_refl (s : Speicher D) (c : D.Tab ⊕ D.Glob) : TraegerGleich s s c := by
  cases c <;> rfl

/-- **The rely, one step.** A step of thread `u` leaves a carrier `c` alone
    if (a) some lock guarding `c` is not held by `u`, or (b) the signature of
    `u`'s head function does not permit writing `c`. Every writing step
    carries its carrier's guards in the static holdings (`darf`/`gdarf` on
    the write, on `exchange`, on the axiom's declared writes) and the
    signature permission (`hw`), and every writing step now demands
    `HeldGenau`, so (a) contradicts a write; the frame of `stmt_gut` and
    of the oracle (`GutO`) gives (b). -/
theorem schritt_traeger (hO : GutO O) {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M') (c : D.Tab ⊕ D.Glob)
    (hc : (∃ L, Bewacht c L ∧ L ∉ offen (M.faeden u).spur) ∨
      TraegerSchreibt (M.faeden u).kopf.f c = false) :
    TraegerGleich M'.speicher M.speicher c := by
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      have hw : (execStmt O passes keinRuf s ((genAusG M).weltVon u) ρ).welt = some σ' := by
        show (execStmt O passes keinRuf s (M.weltVon u) ρ).welt = some σ'
        rw [hstep]; rfl
      have hR := ((stmt_gut O passes keinRuf keinRuf_gut hO s (M.weltVon u) ρ hΛ) σ'
        (by rw [hstep]; rfl)).1
      cases c with
      | inl t =>
          show σ'.slots t = M.speicher.slots t
          funext k fld
          rcases hc with ⟨L, hB, hfrei⟩ | hW
          · exact blatt_erhaelt_slots O passes hO (genAusG M) u s ρ hleaf σ' hw t L hB hΛ hfrei k fld
          · exact hR.1 t hW k fld
      | inr x =>
          show σ'.globs x = M.speicher.globs x
          rcases hc with ⟨L, hB, hfrei⟩ | hW
          · exact blatt_erhaelt_globs O passes hO (genAusG M) u s ρ hleaf σ' hw x L hB hΛ hfrei
          · exact hR.2 x hW
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      have hw : (execStmt O passes keinRuf s ((genAusG M).weltVon u) ρ).welt = some σ' := by
        show (execStmt O passes keinRuf s (M.weltVon u) ρ).welt = some σ'
        rw [hstep]; rfl
      have hR := ((stmt_gut O passes keinRuf keinRuf_gut hO s (M.weltVon u) ρ hΛ) σ'
        (by rw [hstep]; rfl)).1
      cases c with
      | inl t =>
          show σ'.slots t = M.speicher.slots t
          funext k fld
          rcases hc with ⟨L, hB, hfrei⟩ | hW
          · exact blatt_erhaelt_slots O passes hO (genAusG M) u s ρ hleaf σ' hw t L hB hΛ hfrei k fld
          · exact hR.1 t hW k fld
      | inr x =>
          show σ'.globs x = M.speicher.globs x
          rcases hc with ⟨L, hB, hfrei⟩ | hW
          · exact blatt_erhaelt_globs O passes hO (genAusG M) u s ρ hleaf σ' hw x L hB hΛ hfrei
          · exact hR.2 x hW
  | dannLeaveTrav l Γ Λ t' inv body is k rest i ρ hl _ σ' ρ' _ hstep _ _ σ₁ hs₁ =>
      rw [hs₁, leave_welt' _ _ _ _ _ _ _ _ hstep]
      exact traegerGleich_refl _ c
  | dannNextTrav l Γ Λ t' inv body is k rest i ρ hl _ σ' ρ' _ hstep =>
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      exact traegerGleich_refl _ c
  | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hl _ σ' ρ' _ hstep =>
      rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
      exact traegerGleich_refl _ c
  | dannNextWieder l Γ Λ n bis body ueber k rest ρ hl _ σ' ρ' _ hstep =>
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      exact traegerGleich_refl _ c
  | dannLeaveEwig l Γ Λ a n inv body k rest ρ hl _ σ' ρ' _ hstep =>
      rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
      exact traegerGleich_refl _ c
  | dannNextEwig l Γ Λ a n inv body k rest ρ hl _ σ' ρ' _ hstep =>
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      exact traegerGleich_refl _ c
  | dannExchange l Γ Λ Λ' g neuE hw hL rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
      rw [hs₂, hs₁]
      cases c with
      | inl t => rfl
      | inr x =>
          show (World.storeGlob _ g _).globs x = M.speicher.globs x
          by_cases hgx : x = g
          · subst hgx
            exfalso
            rcases hc with ⟨L, hB, hfrei⟩ | hW
            · have hmem : Res.held L ∈ Λ := by
                have := hL _ hB
                simpa [Res.von] using this
              exact hfrei ((hΛ L).mp hmem)
            · have : TraegerSchreibt (M.faeden u).kopf.f (.inr x) = true := hw
              rw [hW] at this
              exact Bool.false_ne_true this
          · simp only [World.storeGlob, dif_neg hgx]
            rfl
  | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      have e : σ₂ = (O.wirkt a σ₁ (evalArgs σ₁ args σ₁ ρ)).1 := by
        have := congrArg Prod.fst hax
        simp only [axiomAntwort] at this
        exact this.symm
      have hfr := (hO a σ₁ (evalArgs σ₁ args σ₁ ρ)).1
      rw [← e] at hfr
      cases c with
      | inl t =>
          show σ₂.slots t = M.speicher.slots t
          have ha : D.aschreibt a t = false := by
            cases hat : D.aschreibt a t with
            | false => rfl
            | true =>
                exfalso
                rcases hc with ⟨L, hB, hfrei⟩ | hW
                · have hmem : Res.held L ∈ Λ := by
                    have := hd t hat _ hB
                    simpa [Res.von] using this
                  exact hfrei ((hΛ L).mp hmem)
                · have : TraegerSchreibt (M.faeden u).kopf.f (.inl t) = true := hw t hat
                  rw [hW] at this
                  exact Bool.false_ne_true this
          funext k fld
          rw [hfr.1 t ha k fld, hs₁]
          rfl
      | inr x =>
          show σ₂.globs x = M.speicher.globs x
          have ha : D.agschreibt a x = false := by
            cases hax' : D.agschreibt a x with
            | false => rfl
            | true =>
                exfalso
                rcases hc with ⟨L, hB, hfrei⟩ | hW
                · have hmem : Res.held L ∈ Λ := by
                    have := hgd x hax' _ hB
                    simpa [Res.von] using this
                  exact hfrei ((hΛ L).mp hmem)
                · have : TraegerSchreibt (M.faeden u).kopf.f (.inr x) = true := hg x hax'
                  rw [hW] at this
                  exact Bool.false_ne_true this
          rw [hfr.2 x ha, hs₁]
          rfl
  | _ =>
      subst_vars
      exact traegerGleich_refl _ c

/-- **The rely on reachable machines.** If thread `t` holds a lock `L`
    guarding `c`, a step of any other thread leaves `c` alone. -/
theorem relyG (hO : GutO O) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {u : Faden} (hs : RufSchrittG P O passes M u M') (t : Faden) (hut : u ≠ t)
    (c : D.Tab ⊕ D.Glob) (L : D.Lock) (hB : Bewacht c L) (hL : L ∈ offen (M.faeden t).spur) :
    TraegerGleich M'.speicher M.speicher c :=
  schritt_traeger hO hs c (Or.inl ⟨L, hB, exklusivG hO sp init hex hr t u (fun e => hut e.symm) L hL⟩)

/-- The table form of the rely (the shape of the earlier `relyG_tab`). -/
theorem relyG_tab (hO : GutO O) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M) {g : Faden}
    (hs : RufSchrittG P O passes M g M') (f : Faden) (hgf : g ≠ f)
    (t : D.Tab) (L : D.Lock) (hB : Sum.inl L ∈ D.braucht t)
    (hL : L ∈ offen (M.faeden f).spur) :
    ∀ (k : Int) (fld : D.Feld t), M'.speicher.slots t k fld = M.speicher.slots t k fld := by
  have h := relyG hO sp init hex hr hs f hgf (.inl t) L hB hL
  intro k fld
  exact congrFun (congrFun h k) fld

end Sperren


/-! ## 5. The finding: every candidate premise holds, the conclusion fails

    The program `gegP` over the reference declaration `refD`: the reference
    CONTRACTS (`einzahlen`: requires true, ensures `old(konto[0]) ≤
    konto[0]`; `lies`: requires true, ensures `result = konto[0]`), both
    functions holding the lock by signature; the bodies:
    `einzahlen` = `lies(); konto[0] := 100; return`,
    `lies` = `let x = konto[0]; return x`.
    Both are correct sequentially (`gegP_koerperGut`). -/

/-- `lies`: bind `konto[0]`, then return the bound value. -/
def gegRumpfLies : Endblock refD (vertragVon refD refLies) false []
    (Signatur.anfang refD (refD.signatur refLies)) :=
  .bind (.slot () () refIdxBodyLies refDarfBodyLies)
    (.ret (.wert (.var .hier)) (by rfl))

/-- `einzahlen`: call `lies`, write the cap, return. -/
def gegRumpfEin :
    Endblock refD (vertragVon refD refEin) false [.int 0 10] [Res.held (D := refD) ()] :=
  .cons (.call (V := vertragVon refD refEin) refLies refArgsLies refHpLiesAt rfl)
    (.cons refWriteStAt (.ret .keine (by rfl)))

/-- The counterexample program: reference contracts, the two bodies above. -/
def gegP : Programm refD where
  invariante := fun i => nomatch i
  requires
    | true => refReqEin
    | false => refReqLies
  ensures
    | true => refEnsEin
    | false => refEnsLies
  rumpf
    | true => refEin_start ▸ gegRumpfEin
    | false => refLies_start ▸ gegRumpfLies

/-- Every thread starts in `einzahlen 7`. -/
def gegInit : Faden → Σ f : refD.Fn, Env refD (refD.params f) :=
  fun _ => ⟨refEin, refRho7⟩

/-- The member list of `refD`'s functions, complete. -/
def refFs : List refD.Fn := [refEin, refLies]

theorem refFs_voll : ∀ g : refD.Fn, g ∈ refFs := by
  intro g
  cases g
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_self

theorem gegP_fragment : programmImFragment gegP refFs = true := by decide

theorem gegP_fuss : fussOrtB gegP refFs = true := by decide

theorem gegP_schreiber : schreiberHaeltB gegP refFs = true := by decide

theorem gegP_start : StartGut gegP refSp0 gegInit := fun _ => rfl

/-- `lies` is correct sequentially: the bound value IS `konto[0]` of the
    entry world, and reading keeps the slots, so `result = konto[0]` holds
    at the return world. It makes no call. -/
theorem gegP_koerper_lies : KoerperGut gegP refO 0 refLies := by
  intro R _ _ σ ρ _
  have hr : gegP.rumpf refLies = gegRumpfLies := rfl
  refine ⟨?_, ?_⟩
  · intro σ' v hrun
    rw [hr] at hrun
    simp only [gegRumpfLies, execEnd, EndAusgang.schrumpf] at hrun
    cases hrun
    exact (decide_eq_true_eq).mpr rfl
  · intro g hrun
    rw [hr] at hrun
    simp only [gegRumpfLies, execEnd, EndAusgang.schrumpf] at hrun
    cases hrun

/-- `einzahlen` is correct sequentially: whatever the contract-respecting
    handler answers for `lies`, the body then writes the cap `100`, the top
    of the field's range, so `old(konto[0]) ≤ konto[0]` holds at the return
    world; its one call meets `requires lies` (which is `true`). -/
theorem gegP_koerper_ein : KoerperGut gegP refO 0 refEin := by
  intro R _ hOV σ ρ _
  have hr : gegP.rumpf refEin = gegRumpfEin := rfl
  have htor : ∀ (σ1 : World refD) (ρ1 : Env refD (refD.params refLies)),
      torRuf gegP R refLies σ1 ρ1 = R refLies σ1 ρ1 := fun _ _ => if_pos rfl
  refine ⟨?_, ?_⟩
  · intro σ' v hrun
    rw [hr] at hrun
    simp only [gegRumpfEin, execEnd, execStmt] at hrun
    split at hrun
    · rename_i σa ρa heq
      split at heq
      · cases heq
        simp only [refWriteStAt, refWriteSt, execStmt] at hrun
        cases hrun
        have hOld : (σ.slots () 0 ()).n ≤ 100 := (σ.slots () 0 ()).le_hi
        show decide ((σ.slots () 0 ()).n ≤ 100) = true
        exact decide_eq_true_eq.mpr hOld
      · exact Fin.elim0 ‹_›
      · cases heq
      · cases heq
    all_goals first
      | (rename_i heq
         (split at heq <;> first | cases heq | exact Fin.elim0 ‹_›)
         done)
      | cases hrun
  · intro g hrun
    rw [hr] at hrun
    simp only [gegRumpfEin, execEnd, execStmt] at hrun
    simp only [htor] at hrun
    split at hrun
    · rename_i σa ρa heq
      split at heq
      · cases heq
        simp only [refWriteStAt, refWriteSt, execStmt] at hrun
        cases hrun
      · exact Fin.elim0 ‹_›
      · cases heq
      · cases heq
    all_goals first
      | (rename_i heq
         (split at heq <;> first | cases heq | exact Fin.elim0 ‹_›)
         done)
      | cases hrun
      | skip
    rename_i heq
    split at heq
    · cases heq
    · exact Fin.elim0 ‹_›
    · rename_i e' hRv
      cases heq
      exact hOV _ _ _ _ hRv g rfl
    · cases heq

/-- `HeldGenau` at the one-lock holdings, from the held set. -/
theorem heldGenau_ref {s : List (Ereignis refD)} (h : offen s = [()]) :
    HeldGenau [Res.held (D := refD) ()] (offen s) := by
  rw [h]
  intro L
  cases L
  exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩

theorem nicht_in_nil (L : refD.Lock) : L ∉ ([] : List refD.Lock) := fun h => nomatch h

/-- The start thread state of `gegInit` (every thread): `einzahlen 7`,
    HOLDING the lock (the repaired start). -/
def gegZ0 : RufFadenG refD :=
  ⟨[], ⟨refEin, refRho7, refSp0.welt [],
    ⟨false, refD.params refEin, Signatur.anfang refD (refD.signatur refEin), refRho7,
     .ende (gegP.rumpf refEin)⟩⟩, startSpur refEin,
     [RufEreignisF.eintritt refEin refRho7 (refSp0.welt [])]⟩

theorem gegM0_faden (t : Faden) : (RufStartG gegP refSp0 gegInit).faeden t = gegZ0 := rfl

theorem offen_gegZ0 : offen gegZ0.spur = [()] := rfl

/-- The rest of `einzahlen` after its call. -/
def gegRestEin : Endblock refD (vertragVon refD refEin) false [.int 0 10]
    (nach refD refLies [Res.held (D := refD) ()]) :=
  .cons refWriteStAt (.ret .keine (by rfl))

/-- Reachability composes. -/
theorem rufErreichbarG_trans {P : Programm D} {O : Orakel D} {passes : Nat}
    {M0 M1 M2 : RufMaschineG D} (h1 : RufErreichbarG P O passes M0 M1)
    (h2 : RufErreichbarG P O passes M1 M2) : RufErreichbarG P O passes M0 M2 := by
  induction h2 with
  | start => exact h1
  | schritt M M' f _ hs ih => exact RufErreichbarG.schritt M M' f ih hs

/-- `ensures lies` is `result = konto[0]`: false when the result is 0 and
    the return world has `konto[0] = 100`. -/
theorem ens_lies_falsch (s0 s1 : World refD) (rho : Env refD (refD.params refLies))
    (v : ErgVal refD (refD.erg refLies)) (hv : (show Zahl 0 100 from v).n = 0)
    (hs : (s1.slots () 0 ()).n = 100) : ¬ EnsAmRueck gegP refLies s0 s1 rho v := by
  intro hE
  have h : decide ((show Zahl 0 100 from v).n = (s1.slots () 0 ()).n) = true := hE
  rw [hv, hs] at h
  exact absurd h (by decide)

/-! ### 5a. The old counterexample is gone

    The run of the finding passed a machine `M4` in which thread 0's head
    frame (`lies`) names the lock in its static holdings while thread 0
    does not hold it -- reached by the bare `gibt`. On the repaired G no
    reachable machine has such a frame, for ANY program and start
    assignment (`rufG_haelt_statisch`); and every step that releases a lock
    releases one the head names (`offen_schrittG`). -/

/-- **The counterexample's pivot is unreachable.** On every machine of
    the repaired G reachable from ANY start, no thread has a frame (head or
    suspended) whose static holdings name a lock the thread does not hold.
    In particular the machine `M4` of the finding -- thread 0 inside
    `lies` with `Res.held ()` in its holdings and `() ∉ offen` -- is not
    reachable from the start machine of `gegP`. -/
theorem ziel_ort_gegenbeispiel_verschwindet :
    ∀ M : RufMaschineG refD,
      RufErreichbarG gegP refO 0 (RufStartG gegP refSp0 gegInit) M →
      ¬ ((M.faeden 0).kopf.f = refLies ∧
        Res.held (D := refD) () ∈ (M.faeden 0).kopf.rest.2.2.1 ∧
        (() : refD.Lock) ∉ offen (M.faeden 0).spur) := by
  intro M hr ⟨_, hmem, hnot⟩
  exact hnot (rufG_haelt_statisch refO_gut refSp0 gegInit hr 0 _ List.mem_cons_self () hmem)

/-! ### 5b. The start fact is needed

    With every thread starting in `einzahlen` -- which holds the lock by
    signature -- the start machine gives EVERY thread the lock: `gegInit`
    violates `StartExklusiv`. Then the interference is back, without any
    bare step: thread 0 enters `lies` and reads `konto[0] = 0`, thread 1
    (which also "holds" the lock) enters `lies`, returns and writes 100,
    thread 0 returns 0 in a world with `konto[0] = 100`. So the start fact
    is not decoration: dropping it makes `ziel_ort` false. -/

/-- **The run without an exclusive start.** Eight steps of the repaired G
    from the start machine of `gegP` under `gegInit`; thread 0's log ends
    with a return of `lies` whose `ensures` is false. -/
theorem geg_lauf : ∃ M : RufMaschineG refD,
    RufErreichbarG gegP refO 0 (RufStartG gegP refSp0 gegInit) M ∧
    ∃ (rho : Env refD (refD.params refLies)) (v : ErgVal refD (refD.erg refLies))
      (s0 s1 : World refD),
      RufEreignisF.rueck refLies rho v s0 s1 ∈ (M.faeden 0).log ∧
      ¬ EnsAmRueck gegP refLies s0 s1 rho v := by
  -- thread 0: call `lies`, bind `konto[0]`
  have h0 := gegM0_faden (0 : Faden)
  obtain ⟨M2, s2, hZ2⟩ := w_rufEnde (P := gegP) (O := refO) (passes := 0) h0 refLies
    refArgsLies refHpLiesAt rfl gegRestEin refRho7 rfl (heldGenau_ref offen_gegZ0)
  have hoff2 : offen (M2.faeden 0).spur = [()] := by
    rw [hZ2.1]
    exact ((Erw.lese _ _ _).offen).trans offen_gegZ0
  obtain ⟨M3, s3, hZ3⟩ := w_endeBind (P := gegP) (O := refO) (passes := 0) hZ2.1 _ _ _ rfl
    (heldGenau_ref (by first | exact hoff2 | (rw [hZ2.1] at hoff2; exact hoff2)))
  have hoff3 : offen (M3.faeden 0).spur = [()] := by
    rw [hZ3.1]
    exact ((Erw.lese _ _ _).offen).trans hoff2
  have hfremd3 : ∀ t : Faden, t ≠ 0 → M3.faeden t = gegZ0 := by
    intro t ht
    rw [rufSchrittG_fremd s3 t ht, rufSchrittG_fremd s2 t ht, gegM0_faden]
  have hr3 : RufErreichbarG gegP refO 0 (RufStartG gegP refSp0 gegInit) M3 :=
    .schritt _ _ _ (.schritt _ _ _ .start s2) s3
  -- thread 1: call `lies`, bind, return, write 100
  have h13 : M3.faeden 1 = gegZ0 := hfremd3 1 (by decide)
  obtain ⟨M4, s4, hZ4⟩ := w_rufEnde (P := gegP) (O := refO) (passes := 0) h13 refLies
    refArgsLies refHpLiesAt rfl gegRestEin refRho7 rfl (heldGenau_ref offen_gegZ0)
  have hoff4 : offen (M4.faeden 1).spur = [()] := by
    rw [hZ4.1]
    refine ((Erw.lese _ _ _).offen).trans ?_
    show offen (M3.faeden 1).spur = [()]
    rw [h13]; rfl
  obtain ⟨M5, s5, hZ5⟩ := w_endeBind (P := gegP) (O := refO) (passes := 0) hZ4.1 _ _ _ rfl
    (heldGenau_ref (by first | exact hoff4 | (rw [hZ4.1] at hoff4; exact hoff4)))
  have hoff5 : offen (M5.faeden 1).spur = [()] := by
    rw [hZ5.1]
    exact ((Erw.lese _ _ _).offen).trans hoff4
  obtain ⟨M6, s6, hG6⟩ := w_rueckP (P := gegP) (O := refO) (passes := 0) hZ5.1 _ [] rfl
    (PopArt.wie rfl) _ _ _ rfl (heldGenau_ref (by first | exact hoff5 | (rw [hZ5.1] at hoff5; exact hoff5)))
  have hoff6 : offen (M6.faeden 1).spur = [()] := by
    rw [hG6.1]
    exact ((Erw.lese _ _ _).offen).trans hoff5
  obtain ⟨M7, s7, hZ7⟩ := w_blatt (P := gegP) (O := refO) (passes := 0) hG6.1 refWriteStAt
    (.ret .keine (by rfl)) refRho7 rfl rfl
    (heldGenau_ref (by first | exact hoff6 | (rw [hG6.1] at hoff6; exact hoff6))) _ _ rfl
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  -- thread 0 again: return the stale value
  have hfremd7 : ∀ t : Faden, t ≠ 1 → M7.faeden t = M3.faeden t := by
    intro t ht
    rw [rufSchrittG_fremd s7 t ht, rufSchrittG_fremd s6 t ht, rufSchrittG_fremd s5 t ht,
      rufSchrittG_fremd s4 t ht]
  have h7_0 : M7.faeden 0 = _ := (hfremd7 0 (by decide)).trans hZ3.1
  obtain ⟨M8, s8, hG8⟩ := w_rueckP (P := gegP) (O := refO) (passes := 0) h7_0 _ [] rfl
    (PopArt.wie rfl) _ _ _ rfl (heldGenau_ref (by first | exact hoff3 | (rw [hZ3.1] at hoff3; exact hoff3)))
  have hr8 : RufErreichbarG gegP refO 0 (RufStartG gegP refSp0 gegInit) M8 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ hr3 s4) s5)
      s6) s7) s8
  refine ⟨M8, hr8, _, _, _, _, by rw [hG8.1]; exact List.mem_cons_self, ?_⟩
  refine ens_lies_falsch _ _ _ _ ?_ ?_
  · show (M2.speicher.slots () 0 ()).n = 0
    rw [hZ2.2]
    rfl
  · show (M7.speicher.slots () 0 ()).n = 100
    rw [hZ7.2]
    rfl

/-- The bodies of `gegP` are in the SEMANTIC fragment of the converse too:
    `lies` at depth 1, `einzahlen` (calling `lies`) at depth 2, for every
    lock predicate `A` (the bodies take no lock). -/
theorem gegP_tief_lies (A : refD.Lock → Prop) : TiefK gegP A 1 refLies :=
  ⟨show EndR A (TiefK gegP A 0) gegRumpfLies from EndR.bind _ _ (EndR.ret _ _), rfl⟩

theorem gegP_tief_ein (A : refD.Lock → Prop) : TiefK gegP A 2 refEin :=
  ⟨show EndR A (TiefK gegP A 1) gegRumpfEin from
    EndR.cons _ _ (StmtR.call _ refLies rfl (gegP_tief_lies A))
      (EndR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) (EndR.ret _ _)), rfl⟩

/-- `gegInit` is not exclusive: threads 0 and 1 both start holding the
    lock. -/
theorem gegInit_nicht_exklusiv : ¬ StartExklusiv (D := refD) gegInit :=
  fun h => h 0 1 (by decide) () List.mem_cons_self List.mem_cons_self

/-- **Every premise of `ziel_ort` but the start fact holds, and the
    conclusion fails.** On the reference declaration, with the reference
    contracts: `GutO`, the fragment (syntactic and semantic), the footprint
    check `fussOrtB` (the carriers of `lies`'s contract are in
    `einzahlen`'s footprint now, and are guarded by the lock both hold by
    signature), the writer discipline, `KoerperGut` for every function and
    the entry obligations all hold; the start assignment is NOT exclusive;
    and a reachable machine of the REPAIRED G violates `VertragAmOrtG`. -/
theorem ziel_ort_gegenbeispiel :
    GutO refO ∧
    programmImFragment gegP refFs = true ∧
    (∀ A, TiefK gegP A 1 refLies ∧ TiefK gegP A 2 refEin) ∧
    fussOrtB gegP refFs = true ∧
    schreiberHaeltB gegP refFs = true ∧
    (∀ f, KoerperGut gegP refO 0 f) ∧
    StartGut gegP refSp0 gegInit ∧
    ¬ StartExklusiv (D := refD) gegInit ∧
    ∃ M : RufMaschineG refD,
      RufErreichbarG gegP refO 0 (RufStartG gegP refSp0 gegInit) M ∧
      ¬ VertragAmOrtG gegP M := by
  refine ⟨refO_gut, gegP_fragment, fun A => ⟨gegP_tief_lies A, gegP_tief_ein A⟩, gegP_fuss,
    gegP_schreiber, ?_, gegP_start, gegInit_nicht_exklusiv, ?_⟩
  · intro f
    cases f
    · exact gegP_koerper_lies
    · exact gegP_koerper_ein
  · obtain ⟨M, hr, rho, v, s0, s1, hmem, hens⟩ := geg_lauf
    exact ⟨M, hr, fun h => hens ((h 0 _ hmem).2 refLies rho v s0 s1 rfl)⟩

/-- **The shape of `ziel_ort` WITHOUT the start fact is false over the
    repaired G.** Quantified over every declaration, program, oracle,
    forever budget, complete member list, start memory and start
    assignment. (With `StartExklusiv` it is the theorem `ziel_ort`,
    `ZielOrtBeweis.lean`.) -/
theorem ziel_ort_form_falsch :
    ¬ (∀ (D : Deklaration) (P : Programm D) (O : Orakel D) (passes : Nat) (fs : List D.Fn)
        (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)),
        GutO O →
        (∀ g : D.Fn, g ∈ fs) →
        programmImFragment P fs = true →
        fussOrtB P fs = true →
        schreiberHaeltB P fs = true →
        (∀ f : D.Fn, KoerperGut P O passes f) →
        StartGut P sp init →
        ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
          VertragAmOrtG P M) := by
  intro h
  obtain ⟨hO, hFrag, _, hFuss, hSchr, hK, hStart, _, M, hr, hnot⟩ := ziel_ort_gegenbeispiel
  exact hnot (h refD gegP refO 0 refFs refSp0 gegInit hO refFs_voll hFrag hFuss hSchr hK hStart
    M hr)

/-! ## 6. The conclusion is not vacuous: the reference program on G

    On `refP` itself (`einzahlen` = write 100, call `lies`, return), a
    reached run of G with a memory change (`konto[0]` from 0 to 100), a call
    and a return logged satisfies `VertragAmOrtG`: the reference contracts
    hold at their place there. -/

/-- The start thread state of `refP` with every thread in `einzahlen 7`. -/
def refZ0 : RufFadenG refD :=
  ⟨[], ⟨refEin, refRho7, refSp0.welt [],
    ⟨false, refD.params refEin, Signatur.anfang refD (refD.signatur refEin), refRho7,
     .ende (refP.rumpf refEin)⟩⟩, startSpur refEin,
     [RufEreignisF.eintritt refEin refRho7 (refSp0.welt [])]⟩

theorem refM0G_faden (t : Faden) : (RufStartG refP refSp0 gegInit).faeden t = refZ0 := rfl

/-- Both reference `requires` are `true`. -/
theorem refP_req (g : refD.Fn) (s : World refD) (rho : Env refD (refD.params g)) :
    ReqAmEintritt refP g s rho := by
  cases g <;> rfl

/-- The rest of the reference `einzahlen` after its write. -/
def refRestEin : Endblock refD (vertragVon refD refEin) false [.int 0 10]
    [Res.held (D := refD) ()] :=
  .cons (.call (V := vertragVon refD refEin) refLies refArgsLies refHpLiesAt rfl)
    (.ret .keine (by rfl))

/-- **Witness that `VertragAmOrtG` is satisfiable with memory change, a call
    and a return**: thread 1 of the reference program (holding the lock from
    the start) writes `konto[0] := 100`, calls `lies` (entry logged) and
    returns from it (return logged, result 100 in a world with
    `konto[0] = 100`); at the machine reached, the contracts hold at every
    logged event of every thread. -/
theorem vertragAmOrtG_refP_zeuge : ∃ M : RufMaschineG refD,
    RufErreichbarG refP refO 0 (RufStartG refP refSp0 gegInit) M ∧
    (M.speicher.slots () 0 ()).n = 100 ∧
    (∃ rho s0, RufEreignisF.eintritt refLies rho s0 ∈ (M.faeden 1).log) ∧
    (∃ rho v s0 s1, RufEreignisF.rueck refLies rho v s0 s1 ∈ (M.faeden 1).log) ∧
    VertragAmOrtG refP M := by
  have h0 := refM0G_faden (1 : Faden)
  obtain ⟨M2, s2, hZ2⟩ := w_blatt (P := refP) (O := refO) (passes := 0) h0 refWriteStAt
    refRestEin refRho7 rfl rfl (heldGenau_ref rfl) _ _ rfl
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff2 : offen (M2.faeden 1).spur = [()] := by
    rw [hZ2.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans rfl
  obtain ⟨M3, s3, hZ3⟩ := w_rufEnde (P := refP) (O := refO) (passes := 0) hZ2.1 refLies
    refArgsLies refHpLiesAt rfl (.ret .keine (by rfl)) refRho7 rfl
    (heldGenau_ref (by first | exact hoff2 | (rw [hZ2.1] at hoff2; exact hoff2)))
  have hoff3 : offen (M3.faeden 1).spur = [()] := by
    rw [hZ3.spur]
    exact ((Erw.lese _ _ _).offen).trans hoff2
  obtain ⟨M4, s4, hG4⟩ := w_rueckP (P := refP) (O := refO) (passes := 0) hZ3.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (heldGenau_ref (by first | exact hoff3 | (rw [hZ3.1] at hoff3; exact hoff3)))
  have hfremd : ∀ t : Faden, t ≠ 1 → M4.faeden t = refZ0 := by
    intro t ht
    rw [rufSchrittG_fremd s4 t ht, rufSchrittG_fremd s3 t ht, rufSchrittG_fremd s2 t ht,
      refM0G_faden]
  refine ⟨M4, .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s2) s3) s4,
    ?_, ⟨_, _, by rw [hG4.1]; exact List.mem_cons_of_mem _ List.mem_cons_self⟩,
    ⟨_, _, _, _, by rw [hG4.1]; exact List.mem_cons_self⟩, ?_⟩
  · rw [hG4.2]
    show (M3.speicher.slots () 0 ()).n = 100
    rw [hZ3.2]
    show (M2.speicher.slots () 0 ()).n = 100
    rw [hZ2.2]
    rfl
  · intro t ev hev
    refine ⟨fun g rho s0 _ => refP_req g s0 rho, ?_⟩
    intro g rho v s0 s1' he
    subst he
    by_cases ht : t = 1
    · subst ht
      rw [hG4.1] at hev
      rcases List.mem_cons.mp hev with h | h
      · cases h
        show decide (_ = _) = true
        exact decide_eq_true rfl
      · rcases List.mem_cons.mp h with h | h
        · cases h
        · rcases List.mem_cons.mp h with h | h
          · cases h
          · exact absurd h (fun h' => nomatch h')
    · rw [hfremd t ht] at hev
      rcases List.mem_cons.mp hev with h | h
      · cases h
      · exact absurd h (fun h' => nomatch h')

/-! ## CUTS:

  What is proved here (over the REPAIRED G, `RufMaschineG.lean`
  2026-09-13): the conclusion `VertragAmOrtG`, the per-function user
  obligation `KoerperGut`, the start obligation `StartGut`, the decidable
  program facts with soundness (`programmImFragment`, `fussOrtB` ->
  `FussOrtOk` over the footprint INCLUDING the contract carriers of direct
  callees, `schreiberHaeltB`), the lock facts (`offen_schrittG`: a step
  releases only a lock its head names; `exklusivG` from `StartExklusiv`;
  the one-step rely `schritt_traeger`, `relyG`, `relyG_tab`), the re-check
  of the old counterexample (`ziel_ort_gegenbeispiel_verschwindet`: its
  pivot machine is unreachable), the necessity of the start fact
  (`geg_lauf`, `ziel_ort_gegenbeispiel`, `ziel_ort_form_falsch`: without
  `StartExklusiv` a reachable machine of the repaired G still violates the
  contract) and the non-vacuity witness on `refP`
  (`vertragAmOrtG_refP_zeuge`).

  Where the rest is: `ziel_ort` is proved in `ZielOrtBeweis.lean` (with
  premises `GutO`, `hvoll`, `programmImFragment`, `fussOrtB`, `KoerperGut`,
  `StartGut`, `StartExklusiv` and the data `e0`); its witnesses
  (`ziel_ort_zeuge`, `ziel_ort_zeuge_interferenz`) are in
  `ZielOrtZeuge.lean`. `schreiberHaeltB` is proved sound here but is NOT a
  premise of `ziel_ort`: the repaired G enforces the writer discipline per
  step (`HeldGenau`), and the static version would make a written guarded
  carrier the property of one thread forever.

  What is NOT proved in this file: costs (no declared per-function cost exists; the
  repaired G has no bare lock steps, so the non-lock steps of a frame of a
  `kOk` body are bounded by its syntax size plus its callees', which is the
  natural first cost theorem once a declared bound exists).
-/

#print axioms Gabbro.Grammatik.fussOrtB_ok
#print axioms Gabbro.Grammatik.schreiberHaeltB_ok
#print axioms Gabbro.Grammatik.offen_schrittG
#print axioms Gabbro.Grammatik.exklusivG
#print axioms Gabbro.Grammatik.schritt_traeger
#print axioms Gabbro.Grammatik.relyG
#print axioms Gabbro.Grammatik.relyG_tab
#print axioms Gabbro.Grammatik.gegP_koerper_lies
#print axioms Gabbro.Grammatik.gegP_koerper_ein
#print axioms Gabbro.Grammatik.ziel_ort_gegenbeispiel_verschwindet
#print axioms Gabbro.Grammatik.geg_lauf
#print axioms Gabbro.Grammatik.ziel_ort_gegenbeispiel
#print axioms Gabbro.Grammatik.ziel_ort_form_falsch
#print axioms Gabbro.Grammatik.vertragAmOrtG_refP_zeuge

end Gabbro.Grammatik
