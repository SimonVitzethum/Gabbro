/-
  File:      Grammatik/ArenaErkEnde.lean
  Subject:   THE RECOGNIZER ON FUNCTION BODIES (PLAN-DYNAMISCH.md section 8a.3): a function body is an `Endblock` (it ends in
             a `return`, it never falls off), while `Erk` recognizes `Block`s. `ErkE K a e` says the end block `e` is a run of
             recognized statements ending in `return` / `return why`:

    `ret`, `retWhy`                 -- the end;
    `nutzlast`                      -- a store into the payload field;
    `ite`                           -- a branch whose arms are recognized BLOCKS (`Erk`): this is how the block forms (`alloc`,
                                       `push`, `pop`, `haengen`, ... which are `narrow`/`check` forms, not statements) enter a
                                       function body -- `if true { <block> }` is the embedding;
    `forever`, `traverse`, `retry`  -- loops over recognized bodies.

  `erkE_erhaelt`: if `ErkE K a e`, `K.Ok σ` and `StrukturPasst K a σ ρ`, the run of `e` ends in `return` or `return why`, in a world where
  `K.Ok` holds (a recognized body never produces `leave` or `next`). This is the form of the premise the statement needs:
  every function that writes a word of a declared structure has `ErkE K Abs.leer (P.rumpf f)`.
-/
import Grammatik.Bausteine.Arena.Struktur.Erkenner.ArenaErkennerBeweis

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

variable {D : Deklaration}

section Ende
variable {A : FreiForm D} (K : Dekl A) {V : Vertrag D}

/-- **`ErkE K a e`: the end block `e` is built from recognized statements and ends in a return.** -/
inductive ErkE : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → Abs → Endblock D V l Γ Λ → Prop where
  | ret {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {a : Abs} (e : ErgExpr D Γ Λ V.erg) (hΛ : Λ.Perm V.ende) :
      ErkE (l := l) a (Endblock.ret e hΛ)
  | retWhy {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {a : Abs} (r : Fin V.gruende) (hΛ : Λ.Perm V.ende) :
      ErkE (l := l) (Γ := Γ) (Λ := Λ) a (Endblock.retWhy r hΛ)
  | nutzlast {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {a : Abs} (i : Expr D Γ Λ (.index (D.count A.tab)))
      (e : Expr D Γ Λ (D.typ A.tab A.feld)) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
      (rest : Endblock D V l Γ Λ) (h : ErkE a rest) :
      ErkE a (Endblock.cons (Stmt.assignSlot A.tab A.feld i e hwT hLT) rest)
  | ite {l : Bool} {Γ : Ctx} {Λ Λ1 : List (Res D)} {a a1 a2 a3 : Abs} (c : Expr D Γ Λ .bool)
      (t e : Block D V l Γ Λ Λ1) (rest : Endblock D V l Γ Λ1) (ht : Erk K a t a1) (he : Erk K a e a2)
      (h1 : Abs.Schwacher a3 a1) (h2 : Abs.Schwacher a3 a2) (h : ErkE a3 rest) :
      ErkE a (Endblock.cons (Stmt.ite c t e) rest)
  | forever {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {a a1 k0 : Abs} (an : D.Annahme) (inv : Expr D Γ Λ .bool)
      (body : Block D V true Γ Λ Λ) (rest : Endblock D V l Γ Λ) (hin : Abs.Schwacher k0 a)
      (hb : Erk K k0 body a1) (hs : Abs.Schwacher k0 a1) (h : ErkE a rest) :
      ErkE a (Endblock.cons (Stmt.forever an inv body) rest)
  | traverse {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {a a1 k0 : Abs} (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D V true (Ty.index (D.count t) :: Γ) Λ Λ) (rest : Endblock D V l Γ Λ)
      (hin : Abs.Schwacher k0 a) (hb : Erk K (k0.ext .offen) body a1) (hs : Abs.Schwacher k0 a1.tail)
      (h : ErkE k0 rest) : ErkE a (Endblock.cons (Stmt.traverse t inv body) rest)
  | retry {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {a a1 au a3 k0 : Abs} (n : Nat) (bis : Expr D Γ Λ .bool)
      (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (rest : Endblock D V l Γ Λ)
      (hin : Abs.Schwacher k0 a) (hb : Erk K k0 body a1) (hs : Abs.Schwacher k0 a1) (hu : Erk K k0 ueber au)
      (h3 : Abs.Schwacher a3 k0) (h4 : Abs.Schwacher a3 au) (h : ErkE a3 rest) :
      ErkE a (Endblock.cons (Stmt.retry n bis body ueber) rest)

end Ende

section Beweis
variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {A : FreiForm D} (K : Dekl A) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- **The promise about an end block:** every outcome is a return or a failure in a world where the arena invariant holds. -/
def FolgtE (a : Abs) (e : Endblock D V l Γ Λ) : Prop :=
  ∀ (σ : World D) (ρ : Env D Γ), K.Ok σ → StrukturPasst K a σ ρ →
    ∀ b : Abs, StrukturPost K b (execEnd O passes R e σ ρ).zuAusgang

/-- A statement followed by an end block. -/
theorem StrukturPost.cons_stmtE {a : Abs} {Λ1 : List (Res D)} {s : Stmt D V l Γ Λ Λ1} {rest : Endblock D V l Γ Λ1}
    {σ : World D} {ρ : Env D Γ} (b : Abs) (hp : StrukturPost K a (execStmt O passes R s σ ρ))
    (ihr : ∀ (σ : World D) (ρ : Env D Γ), K.Ok σ → StrukturPasst K a σ ρ →
      StrukturPost K b (execEnd O passes R rest σ ρ).zuAusgang) :
    StrukturPost K b (execEnd O passes R (.cons s rest) σ ρ).zuAusgang := by
  simp only [execEnd]
  generalize execStmt O passes R s σ ρ = o at hp ⊢
  cases o with
  | ok σ' ρ' => exact ihr σ' ρ' hp.1 hp.2
  | zurueck σ' v => exact hp
  | why σ' r => exact hp
  | leave hh σ' ρ' => exact hp
  | next hh σ' ρ' => exact hp
  | logik e => trivial
  | hardware e => trivial

theorem erkE_erhaelt {a : Abs} {e : Endblock D V l Γ Λ} (h : ErkE K a e) : FolgtE O passes R K a e := by
  induction h with
  | @ret Λ a e hΛ =>
    intro σ ρ hS hP b
    exact Dekl.Ok.lese K Λ _ hS
  | @retWhy Λ a r hΛ =>
    intro σ ρ hS hP b
    exact hS
  | @nutzlast Λ a i e hwT hLT rest h ih =>
    intro σ ρ hS hP b
    obtain ⟨σ', hex, hgl⟩ : ∃ σ' : World D,
        execStmt O passes R (Stmt.assignSlot (l := l) A.tab A.feld i e hwT hLT) σ ρ = .ok σ' ρ ∧
        Dekl.Gleich K σ σ' :=
      ⟨_, rfl, (Dekl.Gleich.lese σ Λ _).trans (Dekl.Gleich.nutzlast _ Λ _ _)⟩
    refine StrukturPost.cons_stmtE O passes R K (a := a) b ?_ (fun σ ρ hS hP => ih σ ρ hS hP b)
    rw [hex]
    exact ⟨hgl.ok hS, hgl.passt hP⟩
  | @ite Λ Λ1 a a1 a2 a3 c t e rest ht he h1 h2 h ih =>
    intro σ ρ hS hP b
    have hgl : Dekl.Gleich K σ (σ.lese Λ c.orte) := Dekl.Gleich.lese σ Λ c.orte
    refine StrukturPost.cons_stmtE O passes R K (a := a3) b ?_ (fun σ ρ hS hP => ih σ ρ hS hP b)
    simp only [execStmt]
    split
    · exact StrukturPost.schwacher K h1 (erk_erhaelt O passes R K ht _ ρ (hgl.ok hS) (hgl.passt hP))
    · exact StrukturPost.schwacher K h2 (erk_erhaelt O passes R K he _ ρ (hgl.ok hS) (hgl.passt hP))
  | @forever Λ a a1 k0 an inv body rest hin hb hs h ih =>
    intro σ ρ hS hP b
    refine StrukturPost.cons_stmtE O passes R K (a := a) b ?_ (fun σ ρ hS hP => ih σ ρ hS hP b)
    exact forever_post O passes R K an _ (leseTest_inv inv) body (erk_erhaelt O passes R K hb) hs a passes σ ρ hS
      (StrukturPasst.schwacher K hin hP)
  | @traverse Λ a a1 k0 t inv body rest hin hb hs h ih =>
    intro σ ρ hS hP b
    refine StrukturPost.cons_stmtE O passes R K (a := k0) b ?_ (fun σ ρ hS hP => ih σ ρ hS hP b)
    exact traverse_post O passes R K _ (leseTest_inv inv) body (erk_erhaelt O passes R K hb) hs
      (alleIndizes (D.count t)) σ ρ hS (StrukturPasst.schwacher K hin hP)
  | @retry Λ a a1 au a3 k0 n bis body ueber rest hin hb hs hu h3 h4 h ih =>
    intro σ ρ hS hP b
    refine StrukturPost.cons_stmtE O passes R K (a := a3) b ?_ (fun σ ρ hS hP => ih σ ρ hS hP b)
    exact retry_post O passes R K _ (leseTest_inv bis) body ueber (erk_erhaelt O passes R K hb) hs
      (erk_erhaelt O passes R K hu) h3 h4 n σ ρ hS (StrukturPasst.schwacher K hin hP)

/-- **A function body that knows nothing at entry** (every parameter `offen`) returns, or fails, in a world where the arena
    invariant holds. -/
theorem erkE_koerper {e : Endblock D V l Γ Λ} (h : ErkE K Abs.leer e) (σ : World D) (ρ : Env D Γ) (hS : K.Ok σ)
    (b : Abs) : StrukturPost K b (execEnd O passes R e σ ρ).zuAusgang :=
  erkE_erhaelt O passes R K h σ ρ hS
    ⟨fun _ hx => absurd hx (by simp [Abs.leer]), fun _ hx => absurd hx (by simp [Abs.leer]),
      fun _ hx => absurd hx (by simp [Abs.leer]), fun _ _ hx _ _ => absurd hx (by simp [Abs.leer])⟩ b

end Beweis

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.erkE_erhaelt
#print axioms Gabbro.Grammatik.erkE_koerper
