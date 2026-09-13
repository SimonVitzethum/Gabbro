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

/-- The bare `nimmt` step over a thread state `z`. -/
theorem w_nimmt {P : Programm D} {O : Orakel D} {passes : Nat} {M : RufMaschineG D}
    {f : Faden} {z : RufFadenG D} (hz : M.faeden f = z) (L : D.Lock)
    (hself : L ∉ offen z.spur) (hrang : ∀ K ∈ offen z.spur, D.rang K < D.rang L)
    (hfrei : RufFreiG M f L) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      M'.faeden f = ⟨z.stapel, z.kopf, Ereignis.nimmt L (offen z.spur) :: z.spur, z.log⟩ ∧
      M'.speicher = M.speicher := by
  subst hz
  exact ⟨_, RufSchrittG.nimmt M f L hself hrang hfrei, rufUpdateG_self _ _ _, rfl⟩

/-- The bare `gibt` step over a thread state `z`: ANY held lock, at ANY
    time -- the rule the finding turns on. -/
theorem w_gibt {P : Programm D} {O : Orakel D} {passes : Nat} {M : RufMaschineG D}
    {f : Faden} {z : RufFadenG D} (hz : M.faeden f = z) (L : D.Lock)
    (hhaelt : L ∈ offen z.spur) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      M'.faeden f = ⟨z.stapel, z.kopf, Ereignis.gibt L :: z.spur, z.log⟩ ∧
      M'.speicher = M.speicher := by
  subst hz
  exact ⟨_, RufSchrittG.gibt M f L hhaelt, rufUpdateG_self _ _ _, rfl⟩

/-- `HeldGenau` at the one-lock holdings, from the held set. -/
theorem heldGenau_ref {s : List (Ereignis refD)} (h : offen s = [()]) :
    HeldGenau [Res.held (D := refD) ()] (offen s) := by
  rw [h]
  intro L
  cases L
  exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩

theorem nicht_in_nil (L : refD.Lock) : L ∉ ([] : List refD.Lock) := fun h => nomatch h

/-- The start thread state of the counterexample (every thread). -/
def gegZ0 : RufFadenG refD :=
  ⟨[], ⟨refEin, refRho7, refSp0.welt [],
    ⟨false, refD.params refEin, Signatur.anfang refD (refD.signatur refEin), refRho7,
     .ende (gegP.rumpf refEin)⟩⟩, [], [RufEreignisF.eintritt refEin refRho7 (refSp0.welt [])]⟩

theorem gegM0_faden (t : Faden) : (RufStartG gegP refSp0 gegInit).faeden t = gegZ0 := rfl

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

/-- **The violating run.** Twelve steps of G from the start machine of
    `gegP` (every thread in `einzahlen 7`, `konto` all zero):
    thread 0: `nimmt`, call `lies` (entry logged, `konto[0] = 0`), bind
    `x = konto[0]` (= 0), bare `gibt` -- the lock released while the frame
    of `lies` still names it; thread 1: `nimmt`, call `lies`, bind, return,
    write `konto[0] := 100`, `gibt`; thread 0: `nimmt`, return `x`.
    The machine after thread 0's release (`M4`): head frame `lies`, the
    lock in its static holdings, not held by the thread, the frame a called
    one (a caller below it). The last machine: thread 0's log holds the
    return of `lies` with result 0 in a world with `konto[0] = 100` --
    `ensures lies` (`result = konto[0]`) is false there. -/
theorem geg_lauf : ∃ M4 M12 : RufMaschineG refD,
    RufErreichbarG gegP refO 0 (RufStartG gegP refSp0 gegInit) M4 ∧
    RufErreichbarG gegP refO 0 M4 M12 ∧
    (M4.faeden 0).kopf.f = refLies ∧
    Res.held (D := refD) () ∈ (M4.faeden 0).kopf.rest.2.2.1 ∧
    (() : refD.Lock) ∉ offen (M4.faeden 0).spur ∧
    (M4.faeden 0).stapel ≠ [] ∧
    ∃ (rho : Env refD (refD.params refLies)) (v : ErgVal refD (refD.erg refLies))
      (s0 s1 : World refD),
      RufEreignisF.rueck refLies rho v s0 s1 ∈ (M12.faeden 0).log ∧
      ¬ EnsAmRueck gegP refLies s0 s1 rho v := by
  -- thread 0: take the lock, call `lies`, bind `konto[0]`, release
  have h0 := gegM0_faden (0 : Faden)
  obtain ⟨M1, s1, h1f, h1sp⟩ := w_nimmt (P := gegP) (O := refO) (passes := 0) h0 ()
    (nicht_in_nil _) (fun _ h => nomatch h)
    (fun g _ => by rw [gegM0_faden]; exact nicht_in_nil _)
  obtain ⟨M2, s2, hZ2⟩ := w_rufEnde (P := gegP) (O := refO) (passes := 0) h1f refLies
    refArgsLies refHpLiesAt rfl gegRestEin refRho7 rfl (heldGenau_ref rfl)
  obtain ⟨M3, s3, hZ3⟩ := w_endeBind (P := gegP) (O := refO) (passes := 0) hZ2.1 _ _ _ rfl
  have hoff3 : offen (M3.faeden 0).spur = [()] := by
    rw [hZ3.spur, (Erw.lese _ _ _).offen, hZ2.welt, (Erw.lese _ _ _).offen]
    show offen (M1.faeden 0).spur = [()]
    rw [h1f]
    rfl
  obtain ⟨M4, s4, h4f, h4sp⟩ := w_gibt (P := gegP) (O := refO) (passes := 0) hZ3.1 ()
    (by rw [← hZ3.1, hoff3]; exact List.mem_cons_self)
  have hoff4 : offen (M4.faeden 0).spur = [] := by
    rw [h4f]
    simp only [offen]
    rw [← hZ3.spur, hoff3]
    rfl
  have hfremd4 : ∀ t : Faden, t ≠ 0 → M4.faeden t = gegZ0 := by
    intro t ht
    rw [rufSchrittG_fremd s4 t ht, rufSchrittG_fremd s3 t ht, rufSchrittG_fremd s2 t ht,
      rufSchrittG_fremd s1 t ht, gegM0_faden]
  have hr4 : RufErreichbarG gegP refO 0 (RufStartG gegP refSp0 gegInit) M4 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3) s4
  -- thread 1: take the lock, call `lies`, bind, return, write 100, release
  have h14 : M4.faeden 1 = gegZ0 := hfremd4 1 (by decide)
  obtain ⟨M5, s5, h5f, h5sp⟩ := w_nimmt (P := gegP) (O := refO) (passes := 0) h14 ()
    (nicht_in_nil _) (fun _ h => nomatch h)
    (fun g hg => by
      by_cases hg0 : g = 0
      · subst hg0; rw [hoff4]; exact nicht_in_nil _
      · rw [hfremd4 g hg0]; exact nicht_in_nil _)
  obtain ⟨M6, s6, hZ6⟩ := w_rufEnde (P := gegP) (O := refO) (passes := 0) h5f refLies
    refArgsLies refHpLiesAt rfl gegRestEin refRho7 rfl (heldGenau_ref rfl)
  obtain ⟨M7, s7, hZ7⟩ := w_endeBind (P := gegP) (O := refO) (passes := 0) hZ6.1 _ _ _ rfl
  have hoff7 : offen (M7.faeden 1).spur = [()] := by
    rw [hZ7.spur, (Erw.lese _ _ _).offen, hZ6.welt, (Erw.lese _ _ _).offen]
    show offen (M5.faeden 1).spur = [()]
    rw [h5f]
    rfl
  obtain ⟨M8, s8, hG8⟩ := w_rueckP (P := gegP) (O := refO) (passes := 0) hZ7.1 _ [] rfl
    (PopArt.wie rfl) _ _ _ rfl (heldGenau_ref (by rw [hZ7.1] at hoff7; exact hoff7))
  have hoff8 : offen (M8.faeden 1).spur = [()] := by
    rw [hG8.1]
    exact ((Erw.lese _ _ _).offen).trans hoff7
  obtain ⟨M9, s9, hZ9⟩ := w_blatt (P := gegP) (O := refO) (passes := 0) hG8.1 refWriteStAt
    (.ret .keine (by rfl)) refRho7 rfl rfl
    (heldGenau_ref (by rw [hG8.1] at hoff8; exact hoff8)) _ _ rfl
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff9 : offen (M9.faeden 1).spur = [()] := by
    rw [hZ9.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans hoff8
  obtain ⟨M10, s10, h10f, h10sp⟩ := w_gibt (P := gegP) (O := refO) (passes := 0) hZ9.1 ()
    (by rw [hZ9.1] at hoff9; rw [hoff9]; exact List.mem_cons_self)
  have hoff10 : offen (M10.faeden 1).spur = [] := by
    rw [h10f]
    simp only [offen]
    rw [← hZ9.spur, hoff9]
    rfl
  -- thread 0 again: re-take the lock, return the stale value
  have hfremd10 : ∀ t : Faden, t ≠ 1 → M10.faeden t = M4.faeden t := by
    intro t ht
    rw [rufSchrittG_fremd s10 t ht, rufSchrittG_fremd s9 t ht, rufSchrittG_fremd s8 t ht,
      rufSchrittG_fremd s7 t ht, rufSchrittG_fremd s6 t ht, rufSchrittG_fremd s5 t ht]
  have h10_0 : M10.faeden 0 = _ := (hfremd10 0 (by decide)).trans h4f
  obtain ⟨M11, s11, h11f, h11sp⟩ := w_nimmt (P := gegP) (O := refO) (passes := 0) h10_0 ()
    (by rw [← h10_0, hfremd10 0 (by decide), hoff4]; exact nicht_in_nil _)
    (by intro K hK; rw [← h10_0, hfremd10 0 (by decide), hoff4] at hK; exact nomatch hK)
    (fun g hg => by
      by_cases hg1 : g = 1
      · subst hg1; rw [hoff10]; exact nicht_in_nil _
      · rw [hfremd10 g hg1, hfremd4 g hg]; exact nicht_in_nil _)
  have hoff11 : offen (M11.faeden 0).spur = [()] := by
    rw [h11f]
    simp only [offen]
    rw [← hZ3.spur, hoff3]
    rfl
  obtain ⟨M12, s12, hG12⟩ := w_rueckP (P := gegP) (O := refO) (passes := 0) h11f _ [] rfl
    (PopArt.wie rfl) _ _ _ rfl (heldGenau_ref (by rw [h11f] at hoff11; exact hoff11))
  have hr12 : RufErreichbarG gegP refO 0 M4 M12 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _
      (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s5) s6) s7) s8) s9) s10) s11) s12
  refine ⟨M4, M12, hr4, hr12, by rw [h4f], by rw [h4f]; exact List.mem_cons_self,
    by rw [hoff4]; exact nicht_in_nil _, by rw [h4f]; exact List.cons_ne_nil _ _,
    _, _, _, _, by rw [hG12.1]; exact List.mem_cons_self, ?_⟩
  refine ens_lies_falsch _ _ _ _ ?_ ?_
  · show (M2.speicher.slots () 0 ()).n = 0
    rw [hZ2.2]
    show (M1.speicher.slots () 0 ()).n = 0
    rw [h1sp]
    rfl
  · show (M11.speicher.slots () 0 ()).n = 100
    rw [h11sp, h10sp, hZ9.2]
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

/-- **THE FINDING: `ziel_ort` is false over G as it stands.** On the
    reference declaration, with the reference contracts, EVERY candidate
    premise of `ziel_ort` holds jointly --

    * (b) hardware: `GutO refO`;
    * (c) decidable program facts: the fragment (`programmImFragment`, and
      the semantic coverage `TiefK` at depths 1 and 2), the footprint check
      `fussOrtB` (every carrier `lies` and `einzahlen` read or name in a
      contract is guarded by the lock both hold BY SIGNATURE), the writer
      discipline `schreiberHaeltB`;
    * (a) user: `KoerperGut` for every function (the bodies are correct
      sequentially, every call meets its `requires`), and the entry
      obligations at the start (`StartGut`) --

    and yet a reachable machine of G violates `VertragAmOrtG`: thread 0's
    log carries a return of `lies` whose `ensures` is false. The run
    releases the lock with the bare `gibt` step while the frame of `lies`
    names it (`geg_lauf`: the machine `M4`), so no premise about the
    program can exclude it. -/
theorem ziel_ort_gegenbeispiel :
    GutO refO ∧
    programmImFragment gegP refFs = true ∧
    (∀ A, TiefK gegP A 1 refLies ∧ TiefK gegP A 2 refEin) ∧
    fussOrtB gegP refFs = true ∧
    schreiberHaeltB gegP refFs = true ∧
    (∀ f, KoerperGut gegP refO 0 f) ∧
    StartGut gegP refSp0 gegInit ∧
    ∃ M : RufMaschineG refD,
      RufErreichbarG gegP refO 0 (RufStartG gegP refSp0 gegInit) M ∧
      ¬ VertragAmOrtG gegP M := by
  refine ⟨refO_gut, gegP_fragment, fun A => ⟨gegP_tief_lies A, gegP_tief_ein A⟩, gegP_fuss,
    gegP_schreiber, ?_, gegP_start, ?_⟩
  · intro f
    cases f
    · exact gegP_koerper_lies
    · exact gegP_koerper_ein
  · obtain ⟨M4, M12, hr4, hr12, _, _, _, _, rho, v, s0, s1, hmem, hens⟩ := geg_lauf
    exact ⟨M12, rufErreichbarG_trans hr4 hr12,
      fun h => hens ((h 0 _ hmem).2 refLies rho v s0 s1 rfl)⟩

end Gabbro.Grammatik
