/-
  File:      Grammatik/ZielOrt.lean
  Subject:   THE GOAL OVER THE CONCURRENT CALL MACHINE G -- the premise
             classes, the lock facts on G, and a FINDING: over G as it
             stands, the interference class is not a user obligation, not
             a hardware assumption and not a decidable program fact.

  The goal: a user proves only their own logic (one Hoare triple per
  function, `KoerperGut`) plus named hardware assumptions (`GutO`); memory
  safety, data-race freedom and "contracts hold at their place in concurrent
  runs" (`VertragAmOrtG`) are carried by the language, with every further
  premise a decidable fact the checker computes (`programmImFragment`,
  `fussOrtB`, `schreiberHaeltB`).

  What this file proves.

  1. The conclusion `VertragAmOrtG` (§1), the user obligation `KoerperGut`
     (§2: the body triple requires -> ensures over the sequential semantics
     with ANY contract-respecting handler, plus the caller duty: every call
     the body makes meets the callee's `requires`), and the decidable
     program facts (§3) with their soundness (`fussOrtB_ok`,
     `schreiberHaeltB_ok`).
  2. The lock facts on G (§4): the held-lock set moves only by the three
     lock rules (`offen_schrittG`), lock exclusivity over every reachable
     machine (`exklusivG`), and the rely for guarded tables: a step of a
     thread other than `f` never changes a slot of a table guarded by a
     lock `f` holds (`relyG_tab`).
  3. THE FINDING (§5, `ziel_ort_gegenbeispiel`): on the reference
     declaration `refD` (table `konto` guarded by the one lock, `einzahlen`
     writes it, `lies` reads it -- both holding the lock BY SIGNATURE, the
     strongest static discipline there is), with the reference CONTRACTS
     unchanged and two bodies that are sequentially correct, EVERY candidate
     premise of `ziel_ort` holds jointly -- `GutO`, the fragment, the
     footprint check, the writer discipline, `KoerperGut` for every
     function, the entry obligations at the start -- and yet a reachable
     machine of G logs a return of `lies` whose `ensures` is FALSE
     (`result = konto[0]` with result 0 and `konto[0] = 100`).

     The cause is one rule of G: the bare `gibt` step
     (`RufMaschineG.lean:224`) releases any held lock at any time. Thread 0
     enters `lies` holding the lock, reads `konto[0] = 0`, RELEASES the lock
     while the frame of `lies` still names it in its static holdings
     (the run passes a machine where `() ∉ offen` of thread 0 while its head
     frame is `lies`), thread 1 takes it, writes 100, releases it, thread 0
     re-takes it and returns 0. Every premise above is a fact about the
     PROGRAM or the ORACLE; the step that breaks the contract is a fact about
     the RUN. So the premise "every live frame's thread holds the locks its
     frame names, from entry to return" is not reducible to (a) user, (b)
     hardware or (c) decidable program facts on G -- the theorem `ziel_ort`
     of the fixed shape is FALSE over G, whatever decidable premises it
     takes that this disciplined program satisfies.

  The repair belongs to G, not to this file (see CUTS): restrict the bare
  `gibt` to locks no frame of the thread names, and let a start frame begin
  with its signature locks taken (or demand `HeldGenau` on every step that
  reads or writes). Then "static holdings ⊆ held locks" is an invariant of
  every run, the rely of §4 covers the whole call interval, and the
  remaining work is the interleaving form of the converse.
-/
import Grammatik.RufUmkehrRufG
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

/- Read carriers of a function: what `requires`/`ensures` read, and what
   the body may read on any path. -/
mutual

def stmtOrteLese {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → List (D.Tab ⊕ D.Glob)
  | .assignSlot _ _ i e _ _ => i.orte ++ e.orte
  | .assignDurch p _ _ _ i e _ _ => p.orte ++ i.orte ++ e.orte
  | .assignGlob _ e _ _ => e.orte
  | .schreibBytes _ _ _ _ i _ _ e _ _ => i.orte ++ e.orte
  | .assignVar _ e => e.orte
  | .uebergang t _ _ i _ _ _ _ _ _ => .inl t :: i.orte
  | .ite c t e => c.orte ++ blockOrteLese t ++ blockOrteLese e
  | .onOption o p a => o.orte ++ blockOrteLese p ++ blockOrteLese a
  | .onTag v arms => v.orte ++ armsOrteLese arms
  | .onGrund r arms => r.orte ++ grundArmsOrteLese arms
  | .call _ args _ _ => args.orte
  | .callInd p args _ _ => p.orte ++ args.orte
  | .locks _ _ body => blockOrteLese body
  | .breaking _ body => blockOrteLese body
  | .traverse _ inv body => inv.orte ++ blockOrteLese body
  | .retry _ bis body ueber => bis.orte ++ blockOrteLese body ++ blockOrteLese ueber
  | .forever _ inv body => inv.orte ++ blockOrteLese body
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

def blockOrteLese {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → List (D.Tab ⊕ D.Glob)
  | .nil => []
  | .cons s rest => stmtOrteLese s ++ blockOrteLese rest
  | .bind e rest => e.orte ++ blockOrteLese rest
  | .bindCall _ args _ _ _ rest => args.orte ++ blockOrteLese rest
  | .bindCallInd p args _ _ _ rest => p.orte ++ args.orte ++ blockOrteLese rest
  | .bindCallElse _ args _ _ _ err rest =>
      args.orte ++ endblockOrteLese err ++ blockOrteLese rest
  | .bindAxiom _ args _ _ _ _ _ rest => args.orte ++ blockOrteLese rest
  | .regLies _ _ rest => blockOrteLese rest
  | .regLiesElse _ _ zusage sonst rest =>
      zusage.orte ++ endblockOrteLese sonst ++ blockOrteLese rest
  | .awaits g _ _ _ rest => .inr g :: blockOrteLese rest
  | .exchange g neu _ _ rest => .inr g :: neu.orte ++ blockOrteLese rest
  | .narrow e _ _ sonst rest =>
      e.orte ++ endblockOrteLese sonst ++ blockOrteLese rest
  | .pruefung c sonst rest =>
      c.orte ++ endblockOrteLese sonst ++ blockOrteLese rest
  | .gleit _ a b _ _ rest => a.orte ++ b.orte ++ blockOrteLese rest
  | .gleitLit _ _ _ rest => blockOrteLese rest
  | .gleitVon e _ _ rest => e.orte ++ blockOrteLese rest
  | .gleitNarrow e _ _ sonst rest =>
      e.orte ++ endblockOrteLese sonst ++ blockOrteLese rest

def endblockOrteLese {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → List (D.Tab ⊕ D.Glob)
  | .ret e _ => e.orte
  | .retGrund _ _ => []
  | .leave _ => []
  | .next _ => []
  | .cons s rest => stmtOrteLese s ++ endblockOrteLese rest
  | .bind e rest => e.orte ++ endblockOrteLese rest

def armsOrteLese {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    Arms D V l Γ Λ Λ' cs → List (D.Tab ⊕ D.Glob)
  | .nil => []
  | .cons b rest => blockOrteLese b ++ armsOrteLese rest

def grundArmsOrteLese {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} : GrundArms D V l Γ Λ Λ' n → List (D.Tab ⊕ D.Glob)
  | .nil => []
  | .cons b rest => blockOrteLese b ++ grundArmsOrteLese rest

end

/-- The footprint of `f`: contract carriers plus body reads. A foreign step
    must leave exactly these carriers alone for `f`'s sequential reasoning
    to survive an interleaving. -/
def fussOrte (P : Programm D) (f : D.Fn) : List (D.Tab ⊕ D.Glob) :=
  (P.requires f).orte ++ (P.ensures f).orte ++ endblockOrteLese (P.rumpf f)

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

/-! ## 4. The lock facts on G -/

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

/-- A `leave` outcome of `execStmt` carries the entry world. -/
theorem leave_welt {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)}
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) {l : Bool} (h : l = true) (σ' : World D) (ρ' : Env D Γ)
    (hst : execStmt O passes R (Stmt.leave (V := V) (Γ := Γ) (Λ := Λ) h) σ ρ =
      Ausgang.leave h σ' ρ') : σ' = σ := by
  simp only [execStmt] at hst
  cases hst
  rfl

/-- A `next` outcome of `execStmt` carries the entry world. -/
theorem next_welt {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)}
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) {l : Bool} (h : l = true) (σ' : World D) (ρ' : Env D Γ)
    (hst : execStmt O passes R (Stmt.next (V := V) (Γ := Γ) (Λ := Λ) h) σ ρ =
      Ausgang.next h σ' ρ') : σ' = σ := by
  simp only [execStmt] at hst
  cases hst
  rfl

/-- The oracle keeps the held locks (`GutO`, second conjunct). -/
theorem axiom_offen (hO : GutO O) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a))
    (σ₂ : World D) (v : Option (ErgVal D (D.aerg a)))
    (hax : axiomAntwort O a σ ρ = (σ₂, v)) : offen σ₂.spur = offen σ.spur := by
  have e : σ₂ = (O.wirkt a σ ρ).1 := by
    have := congrArg Prod.fst hax
    simp only [axiomAntwort] at this
    exact this.symm
  subst e
  exact (hO a σ ρ).2.1

/-- **How one step moves the held locks of the acting thread**: they stay,
    or one lock `L` is added while no other thread holds it (`nimmt`,
    `dannLocks`), or one lock is released (`gibt`, `freiGib`, the `frei`
    peels). Every other step keeps them: leaves by `stmt_gut`, reads by
    `lese_haelt`, the oracle by `GutO`. -/
theorem offen_schrittG (hO : GutO O) {M M' : RufMaschineG D} {f : Faden}
    (hs : RufSchrittG P O passes M f M') :
    offen (M'.faeden f).spur = offen (M.faeden f).spur ∨
    (∃ L, RufFreiG M f L ∧ offen (M'.faeden f).spur = L :: offen (M.faeden f).spur) ∨
    (∃ L, offen (M'.faeden f).spur = (offen (M.faeden f).spur).erase L) := by
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ _ _ hΛ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      exact Or.inl (blatt_offen hO s _ ρ hΛ σ' ρ' hstep)
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ _ _ hΛ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      exact Or.inl (blatt_offen hO s _ ρ hΛ σ' ρ' hstep)
  | nimmt L _ _ hfrei =>
      simp only [rufUpdateG_self]
      exact Or.inr (Or.inl ⟨L, hfrei, rfl⟩)
  | dannLocks l Γ Λ Λ'' L _ _ _ _ _ _ _ _ hfrei =>
      simp only [rufUpdateG_self]
      exact Or.inr (Or.inl ⟨L, hfrei, rfl⟩)
  | gibt L _ =>
      simp only [rufUpdateG_self]
      exact Or.inr (Or.inr ⟨L, rfl⟩)
  | freiGib l Γ Λ L =>
      simp only [rufUpdateG_self]
      exact Or.inr (Or.inr ⟨L, rfl⟩)
  | peelFreiLeave l Γ Λ L =>
      simp only [rufUpdateG_self]
      exact Or.inr (Or.inr ⟨L, rfl⟩)
  | peelFreiNext l Γ Λ L =>
      simp only [rufUpdateG_self]
      exact Or.inr (Or.inr ⟨L, rfl⟩)
  | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hl _ σ' ρ' _ hstep _ _ σ₁ hs₁ =>
      simp only [rufUpdateG_self]
      refine Or.inl ?_
      rw [hs₁, lese_offen, leave_welt _ _ _ _ _ _ hstep]
      rfl
  | dannNextTrav l Γ Λ t inv body is k rest i ρ hl _ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      refine Or.inl ?_
      rw [next_welt _ _ _ _ _ _ hstep]
      rfl
  | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hl _ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      refine Or.inl ?_
      rw [leave_welt _ _ _ _ _ _ hstep]
      rfl
  | dannNextWieder l Γ Λ n bis body ueber k rest ρ hl _ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      refine Or.inl ?_
      rw [next_welt _ _ _ _ _ _ hstep]
      rfl
  | dannLeaveEwig l Γ Λ a n inv body k rest ρ hl _ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      refine Or.inl ?_
      rw [leave_welt _ _ _ _ _ _ hstep]
      rfl
  | dannNextEwig l Γ Λ a n inv body k rest ρ hl _ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      refine Or.inl ?_
      rw [next_welt _ _ _ _ _ _ hstep]
      rfl
  | dannExchange l Γ Λ Λ' g neuE hw hL rest k ρ _ σ₁ hs₁ σ₂ hs₂ =>
      simp only [rufUpdateG_self]
      refine Or.inl ?_
      rw [hs₂, hs₁]
      exact lese_offen _ _ _
  | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ _ σ₁ hs₁ σ₂ v hax =>
      simp only [rufUpdateG_self]
      refine Or.inl ?_
      rw [axiom_offen hO _ _ _ _ _ hax, hs₁]
      exact lese_offen _ _ _
  | _ =>
      subst_vars
      simp only [rufUpdateG_self]
      first
        | exact Or.inl trivial
        | exact Or.inl rfl
        | exact Or.inl (lese_offen _ _ _)

/-- Every thread holds no lock at the start. -/
theorem offen_start (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (t : Faden) : offen ((RufStartG P sp init).faeden t).spur = [] := by
  have e : ((RufStartG P sp init).faeden t).spur = [] := by
    show (match init t with
      | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
          Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, [],
          [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D)).spur = []
    cases init t
    rfl
  rw [e]
  rfl

/-- **Lock exclusivity on G.** On every reachable machine, a lock held by
    thread `f` is held by no other thread. Induction over reachability with
    `offen_schrittG`: a lock enters a held set only through `nimmt`/
    `dannLocks`, whose `RufFreiG` premise says no other thread holds it. -/
theorem exklusivG (hO : GutO O) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) {M : RufMaschineG D}
    (h : RufErreichbarG P O passes (RufStartG P sp init) M) :
    ∀ (f g : Faden), f ≠ g → ∀ L : D.Lock,
      L ∈ offen (M.faeden f).spur → L ∉ offen (M.faeden g).spur := by
  induction h with
  | start =>
      intro f g _ L hL
      rw [offen_start] at hL
      cases hL
  | schritt M M' f0 _ hs ih =>
      intro f g hfg L hLf hLg
      have hfremd : ∀ t, t ≠ f0 → M'.faeden t = M.faeden t :=
        fun t ht => rufSchrittG_fremd hs t ht
      by_cases hf : f = f0
      · subst hf
        have hg : g ≠ f := fun e => hfg e.symm
        rw [hfremd g hg] at hLg
        rcases offen_schrittG hO hs with e | ⟨L', hfrei, e⟩ | ⟨L', e⟩
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
          rcases offen_schrittG hO hs with e | ⟨L', hfrei, e⟩ | ⟨L', e⟩
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

/-- **The rely for guarded tables on G.** On a reachable machine, a step of
    a thread `g` other than `f` leaves every slot of a table `t` alone that
    is guarded by a lock `L` which `f` holds, provided no axiom writes `t`
    (a declaration fact). Leaves: `g` does not hold `L` (`exklusivG`), and a
    leaf writing `t` needs every guard of `t` in its static holdings, which
    `HeldGenau` makes held (`blatt_erhaelt_slots`). The oracle: its frame
    (`GutO`). Every other step writes no slot. -/
theorem relyG_tab (hO : GutO O) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) {M M' : RufMaschineG D}
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M) {g : Faden}
    (hs : RufSchrittG P O passes M g M') (f : Faden) (hgf : g ≠ f)
    (t : D.Tab) (L : D.Lock) (hB : Sum.inl L ∈ D.braucht t)
    (hL : L ∈ offen (M.faeden f).spur) (hAx : ∀ a : D.Ax, D.aschreibt a t = false) :
    ∀ (k : Int) (fld : D.Feld t), M'.speicher.slots t k fld = M.speicher.slots t k fld := by
  have hfrei : L ∉ offen (M.faeden g).spur :=
    exklusivG hO sp init hr f g (fun e => hgf e.symm) L hL
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf _ hΛ σ' ρ' neu hstep =>
      intro k fld
      have hw : (execStmt O passes keinRuf s ((genAusG M).weltVon g) ρ).welt = some σ' := by
        show (execStmt O passes keinRuf s (M.weltVon g) ρ).welt = some σ'
        rw [hstep]; rfl
      exact blatt_erhaelt_slots O passes hO (genAusG M) g s ρ hleaf σ' hw t L hB hΛ hfrei k fld
  | dannBlatt l Γ Λ Λ' Λ'' s rest k0 ρ hleaf _ hΛ σ' ρ' neu hstep =>
      intro k fld
      have hw : (execStmt O passes keinRuf s ((genAusG M).weltVon g) ρ).welt = some σ' := by
        show (execStmt O passes keinRuf s (M.weltVon g) ρ).welt = some σ'
        rw [hstep]; rfl
      exact blatt_erhaelt_slots O passes hO (genAusG M) g s ρ hleaf σ' hw t L hB hΛ hfrei k fld
  | dannLeaveTrav l Γ Λ t' inv body is k0 rest i ρ hl _ σ' ρ' _ hstep _ _ σ₁ hs₁ =>
      intro k fld
      rw [hs₁, leave_welt _ _ _ _ _ _ hstep]
      rfl
  | dannNextTrav l Γ Λ t' inv body is k0 rest i ρ hl _ σ' ρ' _ hstep =>
      intro k fld
      rw [next_welt _ _ _ _ _ _ hstep]
      rfl
  | dannLeaveWieder l Γ Λ n bis body ueber k0 rest ρ hl _ σ' ρ' _ hstep =>
      intro k fld
      rw [leave_welt _ _ _ _ _ _ hstep]
      rfl
  | dannNextWieder l Γ Λ n bis body ueber k0 rest ρ hl _ σ' ρ' _ hstep =>
      intro k fld
      rw [next_welt _ _ _ _ _ _ hstep]
      rfl
  | dannLeaveEwig l Γ Λ a n inv body k0 rest ρ hl _ σ' ρ' _ hstep =>
      intro k fld
      rw [leave_welt _ _ _ _ _ _ hstep]
      rfl
  | dannNextEwig l Γ Λ a n inv body k0 rest ρ hl _ σ' ρ' _ hstep =>
      intro k fld
      rw [next_welt _ _ _ _ _ _ hstep]
      rfl
  | dannExchange l Γ Λ Λ' x neuE hw hL rest k0 ρ _ σ₁ hs₁ σ₂ hs₂ =>
      intro k fld
      rw [hs₂, hs₁]
      rfl
  | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd hgd rest k0 ρ _ σ₁ hs₁ σ₂ v hax =>
      intro k fld
      have e : σ₂ = (O.wirkt a σ₁ (evalArgs σ₁ args σ₁ ρ)).1 := by
        have := congrArg Prod.fst hax
        simp only [axiomAntwort] at this
        exact this.symm
      have hfr := ((hO a σ₁ (evalArgs σ₁ args σ₁ ρ)).1).1 t (hAx a) k fld
      show σ₂.slots t k fld = M.speicher.slots t k fld
      rw [e, hfr, hs₁]
      rfl
  | _ =>
      intro k fld
      subst_vars
      rfl

end Sperren

end Gabbro.Grammatik
