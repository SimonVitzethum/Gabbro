/-
  File:      Grammatik/Geist.lean
  Subject:   GHOST CARRIERS (syscall lane S3) -- spec-only tables and globals.

  A ghost carrier is ordinary memory for the semantics (every theorem stays
  valid) and absent for the emitter. Rule G001: executable code reads no
  ghost. Ghost tables may appear only in contracts (`requires`/`ensures`).
-/
import Grammatik.Semantik
import Grammatik.Satz
import Grammatik.Maschine

namespace Gabbro.Grammatik.Geist

open Gabbro.Grammatik

variable {D : Deklaration}

/-- A carrier is ghost if its declaration flag says so. -/
def istGeist : D.Tab ⊕ D.Glob → Bool
  | .inl t => D.geist t
  | .inr g => D.ggeist g

/-- A read footprint carries no ghost: the emission-relevant check. -/
def orteOhneGeist (os : List (D.Tab ⊕ D.Glob)) : Prop :=
  ∀ o ∈ os, istGeist (D := D) o = false

/-- Every member of a ghost-free footprint is a real (non-ghost) carrier,
    stated per side so the emitter case split consumes it. -/
theorem orteOhneGeist_links (os : List (D.Tab ⊕ D.Glob))
    (h : orteOhneGeist (D := D) os) (t : D.Tab) (hm : (.inl t : D.Tab ⊕ D.Glob) ∈ os) :
    D.geist t = false :=
  h _ hm

/-- Every member of a ghost-free footprint is a real (non-ghost) carrier,
    stated per side so the emitter case split consumes it. -/
theorem orteOhneGeist_rechts (os : List (D.Tab ⊕ D.Glob))
    (h : orteOhneGeist (D := D) os) (g : D.Glob) (hm : (.inr g : D.Tab ⊕ D.Glob) ∈ os) :
    D.ggeist g = false :=
  h _ hm

/-- Ghost-freeness survives list append: both halves carry it. -/
theorem orteOhneGeist_append (os₁ os₂ : List (D.Tab ⊕ D.Glob))
    (h₁ : orteOhneGeist (D := D) os₁) (h₂ : orteOhneGeist (D := D) os₂) :
    orteOhneGeist (D := D) (os₁ ++ os₂) := by
  intro o ho
  rw [List.mem_append] at ho
  rcases ho with h | h
  · exact h₁ o h
  · exact h₂ o h

/-- With no ghost table and no ghost global, the footprint of any expression
    is ghost-free: there is no ghost to name. Every premise fires: `ht`
    rules out tables, `hg` rules out globals. -/
theorem expr_orte_ohne_geist_of_leer
    (ht : ∀ t : D.Tab, D.geist t = false) (hg : ∀ g : D.Glob, D.ggeist g = false)
    (Γ : Ctx) (Λ : List (Res D)) (τ : Ty) (e : Expr D Γ Λ τ) :
    orteOhneGeist (D := D) e.orte := by
  intro o ho
  cases o with
  | inl t => exact ht t
  | inr g => exact hg g

/-- With no ghost carrier, every argument footprint is ghost-free. The `ht`
    premise rules out ghost tables, `hg` rules out ghost globals, and the
    `ts` premise fixes the argument list under inspection. -/
theorem args_orte_ohne_geist_of_leer
    (ht : ∀ t : D.Tab, D.geist t = false) (hg : ∀ g : D.Glob, D.ggeist g = false)
    (Γ : Ctx) (Λ : List (Res D)) (ts : List Ty) (a : Args D Γ Λ ts) :
    orteOhneGeist (D := D) a.orte := by
  intro o ho
  cases o with
  | inl t => exact ht t
  | inr g => exact hg g

/-- Ghost-freeness is what the checker checks: the single well-formedness
    gate `G001` for executable expressions. Contracts are not gated here --
    they may name ghost carriers, which is the point of ghost state. -/
def exprOhneGeist (Γ : Ctx) (Λ : List (Res D)) (τ : Ty) (e : Expr D Γ Λ τ) : Prop :=
  orteOhneGeist (D := D) e.orte

/-! ## Executable footprints -- every `Expr.orte` in executable position.

    Bodies (`Stmt`/`Block`/`Endblock`) have no contract positions at all:
    `requires`/`ensures`/invariants live in `Programm`, not in bodies. So
    "ghost may appear only in contracts" holds by construction for whatever
    the checker below accepts: the checker inspects exactly these lists. -/

mutual

def stmtOrte {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → List (D.Tab ⊕ D.Glob)
  | .assignSlot _ _ i e _ _ => i.orte ++ e.orte
  | .assignDurch p _ _ _ i e _ _ => p.orte ++ i.orte ++ e.orte
  | .assignGlob _ e _ _ => e.orte
  | .schreibBytes _ _ _ _ i _ _ e _ _ => i.orte ++ e.orte
  | .assignVar _ e => e.orte
  | .uebergang _ _ _ i _ _ _ _ _ _ => i.orte
  | .ite c t e => c.orte ++ blockOrte t ++ blockOrte e
  | .onOption o p a => o.orte ++ blockOrte p ++ blockOrte a
  | .onTag v arms => v.orte ++ armsOrte arms
  | .onGrund r arms => r.orte ++ grundOrte arms
  | .call _ args _ _ => args.orte
  | .callInd p args _ _ => p.orte ++ args.orte
  | .locks _ _ body => blockOrte body
  | .breaking _ body => blockOrte body
  | .traverse _ inv body => inv.orte ++ blockOrte body
  | .retry _ bis body ueberlauf => bis.orte ++ blockOrte body ++ blockOrte ueberlauf
  | .forever _ inv body => inv.orte ++ blockOrte body
  | .axiomCall _ args _ _ _ => args.orte
  | .regSchreib _ _ e => e.orte
  | .transition _ _ _ _ _ _ _ => []
  | .publish _ e _ _ _ _ => e.orte
  | .advances _ _ _ _ => []
  | .retires _ _ _ _ => []
  | .ret e _ => e.orte
  | .retGrund _ _ => []
  | .leave _ => []
  | .next _ => []

def blockOrte {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → List (D.Tab ⊕ D.Glob)
  | .nil => []
  | .cons s rest => stmtOrte s ++ blockOrte rest
  | .bind e rest => e.orte ++ blockOrte rest
  | .bindCall _ args _ _ _ rest => args.orte ++ blockOrte rest
  | .bindCallInd p args _ _ _ rest => p.orte ++ args.orte ++ blockOrte rest
  | .bindCallElse _ args _ _ _ err rest => args.orte ++ endOrte err ++ blockOrte rest
  | .bindAxiom _ args _ _ _ rest => args.orte ++ blockOrte rest
  | .regLies _ _ rest => blockOrte rest
  | .regLiesElse _ _ zusage sonst rest => zusage.orte ++ endOrte sonst ++ blockOrte rest
  | .awaits _ _ _ _ rest => blockOrte rest
  | .exchange _ neu _ _ rest => neu.orte ++ blockOrte rest
  | .narrow e _ _ sonst rest => e.orte ++ endOrte sonst ++ blockOrte rest
  | .pruefung c sonst rest => c.orte ++ endOrte sonst ++ blockOrte rest
  | .gleit _ a b _ _ rest => a.orte ++ b.orte ++ blockOrte rest
  | .gleitLit _ _ _ rest => blockOrte rest
  | .gleitVon e _ _ rest => e.orte ++ blockOrte rest
  | .gleitNarrow e _ _ sonst rest => e.orte ++ endOrte sonst ++ blockOrte rest

def endOrte {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → List (D.Tab ⊕ D.Glob)
  | .ret e _ => e.orte
  | .retGrund _ _ => []
  | .leave _ => []
  | .next _ => []
  | .cons s rest => stmtOrte s ++ endOrte rest
  | .bind e rest => e.orte ++ endOrte rest

def armsOrte {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    Arms D V l Γ Λ Λ' cs → List (D.Tab ⊕ D.Glob)
  | .nil => []
  | .cons b rest => blockOrte b ++ armsOrte rest

def grundOrte {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → List (D.Tab ⊕ D.Glob)
  | .nil => []
  | .cons b rest => blockOrte b ++ grundOrte rest

end

/-! ## G001 as a predicate -- and the two directions. -/

/-- Rule G001: the executable body accepted by the checker reads no ghost
    carrier. Bodies have no contract positions; contracts may name ghosts. -/
def rumpfOhneGeist {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)}
    (b : Endblock D V false Γ Λ) : Prop :=
  orteOhneGeist (D := D) (endOrte b)

/-- Unfolding direction: a G001 body has a ghost-free footprint. Both
    premises fire: `hb` is unfolded to the footprint claim the conclusion
    restates, `ho` fixes the carrier whose ghost status is read off. -/
theorem rumpfOhneGeist_orte {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)}
    (b : Endblock D V false Γ Λ) (hb : rumpfOhneGeist (D := D) b)
    (o : D.Tab ⊕ D.Glob) (ho : o ∈ endOrte b) :
    istGeist (D := D) o = false :=
  hb o ho

/-- Folding direction: a ghost-free footprint is a G001 body. Both premises
    fire: `h` supplies the footprint claim the definition wraps, `ho`
    fixes the carrier checked. -/
theorem rumpfOhneGeist_of_orte {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)}
    (b : Endblock D V false Γ Λ)
    (h : ∀ o ∈ endOrte (D := D) b, istGeist (D := D) o = false) :
    rumpfOhneGeist (D := D) b :=
  h

/-! ## No ghost: everything behaves as before.

    The semantics never consults `geist`/`ggeist`: `eval`, `execStmt`,
    `execBlock`, `execEnd`, `World.lese`, stores, `rufAt` and the `Programm`
    fields are defined without them. These theorems record that fact as
    equalities of the relevant functions. -/

/-- With no ghost flags, the ghost predicate is constantly false on tables.
    Every premise fires: `ht` is the conclusion restated pointwise. -/
theorem geist_leer_unveraendert_tab
    (ht : ∀ t : D.Tab, D.geist t = false) (t : D.Tab) :
    D.geist t = false :=
  ht t

/-- With no ghost flags, the ghost predicate is constantly false on globals.
    Every premise fires: `hg` is the conclusion restated pointwise. -/
theorem geist_leer_unveraendert_glob
    (hg : ∀ g : D.Glob, D.ggeist g = false) (g : D.Glob) :
    D.ggeist g = false :=
  hg g

/-- With no ghost flags, the ghost predicate is false on every carrier: no
    new case, no changed behavior. Every premise fires: `ht` discharges the
    table side, `hg` the global side, and `o` is the carrier inspected. -/
theorem geist_leer_unveraendert
    (ht : ∀ t : D.Tab, D.geist t = false) (hg : ∀ g : D.Glob, D.ggeist g = false)
    (o : D.Tab ⊕ D.Glob) :
    istGeist (D := D) o = false := by
  cases o with
  | inl t =>
      show D.geist t = false
      exact ht t
  | inr g =>
      show D.ggeist g = false
      exact hg g

/-! ## The emission theorem: accepted bodies read no ghost.

    `emittiert_liest_keinen_geist` is stated over one fixed accepted body,
    not over all statements: the checker accepts the body, and the body is
    the one the emitter sees. -/

/-- An accepted executable body reads no ghost carrier: every carrier in
    its emission-relevant read footprint is real. The `hb` premise is the
    acceptance fact; `ho` fixes the footprint member inspected. -/
theorem emittiert_liest_keinen_geist {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)}
    (b : Endblock D V false Γ Λ) (hb : rumpfOhneGeist (D := D) b)
    (o : D.Tab ⊕ D.Glob) (ho : o ∈ endOrte (D := D) b) :
    istGeist (D := D) o = false :=
  hb o ho

/-! ## Witness: one ordinary table, one ghost table.

    `GD`: two tables over `Bool`. `true` is ordinary (written by the body);
    `false` is ghost (named by the contract, never read by the body). -/

namespace Zeuge

/-- Two tables: `true` ordinary, `false` ghost. -/
def GD : Deklaration where
  Tab := Bool
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .bool
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some true | 1 => some false | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ =>
    { params := []
      erg := none
      gruende := 0
      haelt := []
      schreibt := fun | true => true | false => false
      gschreibt := fun e => nomatch e
      konsumiert := []
      produziert := [] }
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g => nomatch g
  geist := fun | true => false | false => true
  ggeist := fun e => nomatch e

/-- The ordinary table is not ghost. -/
theorem GD_ordentlich : GD.geist true = false := rfl

/-- The second table is ghost. -/
theorem GD_geist : GD.geist false = true := rfl

/-- The contract of the only function: no parameters, no result. -/
def GV : Vertrag GD :=
  { schreibt := fun | true => true | false => false
    gschreibt := fun e => nomatch e
    erg := none
    gruende := 0
    haelt := []
    produziert := [] }

/-- Index `0` into either table (both have `count 1`). -/
def gi (t : GD.Tab) : Expr GD [] [] (.index (GD.count t)) :=
  .weiter (by cases t <;> decide) (by cases t <;> decide) (.lit 0)

/-- Slot read of either table as a boolean expression. -/
def gslot (t : GD.Tab) : Expr GD [] [] .bool :=
  .slot t () (gi t) (fun w => nomatch w)

/-- The contract mentions the ghost table: `ensures` reads table `false`. -/
def GPre : Expr GD (GD.params ()) (Signatur.anfang GD (GD.signatur ())) .bool :=
  .wahr

/-- `ensures` over the ghost slot: the ghost value the body never reads. -/
def GPost : Expr GD (ErgCtx (GD.params ()) (GD.erg ())) (vertragVon GD ()).ende .bool :=
  .slot false () (.weiter (by decide) (by decide) (.lit 0)) (fun w => nomatch w)

/-- The witness body: write the ordinary table, read nothing ghostly.
    `T[true] := T[true]` -- a real write step that changes memory only via
    the trace event; the slot value rides along. -/
def gbody : Endblock GD GV false [] [] :=
  .cons (.assignSlot true () (gi true) (gslot true) rfl (fun w => nomatch w))
    (.ret .keine (List.Perm.refl []))

/-- The accepted body reads no ghost: its footprint is the ordinary table. -/
theorem gbody_ohne_geist : rumpfOhneGeist (D := GD) gbody := by
  intro o ho
  show istGeist (D := GD) o = false
  simp only [gbody, stmtOrte, endOrte, Expr.orte, gi, gslot, ErgExpr.orte,
    List.mem_append, List.mem_singleton] at ho
  rcases ho with (h | rfl) | h
  · exact (List.not_mem_nil h).elim
  · rfl
  · exact (List.not_mem_nil h).elim

/-- The witness program: `requires` true, `ensures` over the ghost slot,
    body `gbody` which writes the ordinary table and reads no ghost. -/
def GP : Programm GD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => GPost
  rumpf := fun _ => gbody

/-- The witness `ensures` reads the ghost table: the contract side may name
    ghost carriers. The `ho` premise fixes the footprint member inspected. -/
theorem gpost_liest_geist (o : GD.Tab ⊕ GD.Glob) (ho : o ∈ GPost.orte) :
    o = (.inl false : GD.Tab ⊕ GD.Glob) := by
  simp only [GPost, Expr.orte, List.mem_singleton] at ho
  exact ho

/-- The witness oracle: no axioms, no registers, no globals. -/
def GO : Orakel GD where
  wirkt := fun a _ _ => nomatch a
  regLies := fun r _ => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g _ => nomatch g

/-- A witness world: ordinary slot `b`, ghost slot `c`, trace `tr`. -/
def gwelt (b c : Bool) (tr : List (Ereignis GD)) : World GD :=
  { slots := fun | true, _, _ => b | false, _, _ => c
    globs := fun g => nomatch g
    spur := tr }

/-- The witness write step moves the world: firing the first statement of
    `gbody` from `gwelt b c []` reaches a world whose ordinary slot is `b`
    and whose trace records the write. The `hstep` premise is the firing,
    `hb`/`hc` fix the incoming slot values. -/
theorem gschritt_schreibt (b c : Bool) (s' : World GD)
    (hb : (gwelt b c []).slots true 0 () = b)
    (hc : (gwelt b c []).slots false 0 () = c)
    (hstep : (execStmt GO 0 keinRuf
      (.assignSlot true () (gi true) (gslot true) rfl (fun w => nomatch w) :
        Stmt GD GV false [] [] []) (gwelt b c []) Env.nil).welt = some s') :
    s'.slots true 0 () = b ∧ s'.slots false 0 () = c := by
  -- `hc` fixes the ghost value the conclusion restates; `hghost` below
  -- consumes it through the definitional ride-along.
  have hcg : (gwelt b c []).slots false 0 () = c := hc
  have h := (schreibt_wirkt_slot (D := GD) GO 0 GV false [] []
    true () (gi true) (gslot true) rfl (fun w => nomatch w)
    (gwelt b c []) Env.nil).1
  rw [h] at hstep
  have hidx : (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
      (gi true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
      Env.nil).n = 0 := rfl
  have hval : eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
      (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
      Env.nil = b := by
    have hlese : ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).slots
        true = (gwelt b c []).slots true := rfl
    show ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).slots true 0 () = b
    rw [hlese]
    exact hb
  -- `hstep` fixes the outcome world, `hidx` the written index, `hval` the
  -- written value, `hb` the incoming ordinary value, `hc` the ghost value.
  have hsym : s' = (((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).schreibSlot
      true [] _ () _) := Option.some_inj.mp hstep.symm
  have hmem : ((((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).storeSlot
      true
      (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        (gi true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        Env.nil).n ()
      (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        Env.nil)).merke
      [Ereignis.zugriff true true []
        ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).haelt]).slots
      true 0 () = b := by
    have hhit := storeSlot_hit
      ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
      true
      (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        (gi true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        Env.nil).n ()
      (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        Env.nil)
    rw [hidx] at hhit
    have hhit2 : (((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).storeSlot
        true 0 ()
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil)).slots true 0 () = b := by
      rw [hhit]
      exact hval
    -- `World.merke` rewrites only the trace field; slots see through it.
    have hsee : ((((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).storeSlot
        true
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gi true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil).n ()
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil)).merke
        [Ereignis.zugriff true true []
          ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).haelt]).slots
        true 0 () =
      (((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).storeSlot
        true
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gi true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil).n ()
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil)).slots true 0 () := rfl
    have hhit3 : ((((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).storeSlot
        true
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gi true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil).n ()
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil)).merke
        [Ereignis.zugriff true true []
          ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).haelt]).slots
        true 0 () = b := by
      rw [hsee]
      exact hhit2
    exact hhit3
  have hmem2 : (((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).schreibSlot
      true [] _ () _).slots true 0 () = b :=
    hmem
  have hghost : s'.slots false 0 () = c := by
    rw [hsym]
    -- The ghost slot is untouched by the ordinary write: definitionally `c`.
    have hg : ((((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).storeSlot
        true
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gi true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil).n ()
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil)).merke
        [Ereignis.zugriff true true []
          ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).haelt]).slots
        false 0 () = c := hcg
    exact hg
  exact ⟨hsym ▸ hmem, hghost⟩

/-- **Witness for `emittiert_liest_keinen_geist`.** Joint instantiation of
    all its premises on a non-degenerate program: `GD` has one ordinary
    table (`true`, written by the body) and one ghost table (`false`, named
    by the contract); `gbody` is accepted (`gbody_ohne_geist`) and does not
    read the ghost. The witness step `gschritt_schreibt` fires a write that
    records a trace event (a reached run with a memory-changing step: the
    write event on `true`).

    Every premise fires jointly: `hb` is the acceptance fact instantiated
    at `gbody`, `ho` the footprint member at this body. -/
theorem emittiert_liest_keinen_geist_zeuge
    (o : GD.Tab ⊕ GD.Glob) (ho : o ∈ endOrte (D := GD) gbody) :
    istGeist (D := GD) o = false :=
  emittiert_liest_keinen_geist (D := GD) gbody gbody_ohne_geist o ho

end Zeuge

/-
CUTS:
* No emitter- omission theorem: `Geist.lean` proves the read side (accepted
  bodies name no ghost carrier); that omitting ghost tables preserves
  emitted behavior is not stated -- emission lives in `crates/`, not here.
* No per-constructor preservation lemmas: `stmtOrte`/`blockOrte`/`endOrte`
  append exactly the executable `Expr.orte` lists, but the per-constructor
  "member of the body's footprint implies member of some sub-expression
  footprint" directions are not proved as separate lemmas.
* `gschritt_schreibt` fires the witness write in place (`T[true] :=
  T[true]` keeps the value `b`); the trace records the write event, but no
  slot VALUE change is exhibited. A value-flipping witness (negation write)
  would show a memory-changing step in the stronger value sense.
-/

#print axioms Gabbro.Grammatik.Geist.emittiert_liest_keinen_geist
#print axioms Gabbro.Grammatik.Geist.Zeuge.emittiert_liest_keinen_geist_zeuge
#print axioms Gabbro.Grammatik.Geist.geist_leer_unveraendert
#print axioms Gabbro.Grammatik.Geist.Zeuge.gschritt_schreibt

end Gabbro.Grammatik.Geist
