/-
  File:      Grammatik/ArenaSperreOhne.lean
  Subject:   A RECOGNIZED BODY CONTAINS NO `locks` (PLAN-DYNAMISCH.md section 8a.3, premise 3): the lemma
             `execEndH_eq_execEnd` for the recognized fragment.

  `Erk K a b a'` and `ErkE K a e` are built from the proved moves, payload stores, branches and loops, and from
  `else` branches that are a bare `return`; none of them is a `locks` block. So `Block.ohneLocks` / `Endblock.ohneLocks`
  hold (`erk_ohneLocks`, `erkE_ohneLocks`), and the lock-invariant semantics `execBlockH` / `execEndH` (the one
  `InvGutS`, `KoerperGutS` and the machine bridge talk about) IS the plain `execBlock` / `execEnd` on them
  (`Block.execH_ohne`, `Endblock.execH_ohne`, SperreSem). The soundness theorems `erk_erhaelt`, `erkE_erhaelt` are
  therefore theorems about `execBlockH` / `execEndH` as well (`erk_erhaeltH`, `erkE_koerperH`): that is the form in
  which `InvGutSA` reads them.
-/
import Grammatik.Bausteine.Arena.Struktur.Erkenner.ArenaErkEnde
import Grammatik.Bausteine.Arena.Struktur.Sperre.ArenaSperreTraeger

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette Gabbro.Grammatik.Zielsatz

variable {D : Deklaration}

set_option linter.unusedSimpArgs false

section Ohne
variable {A : FreiForm D} {K : Dekl A} {V : Vertrag D}

/-- An `else` branch that is a bare return contains no `locks`. -/
theorem Rein.ohneLocks {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {e : Endblock D V l Γ Λ} (h : Rein e) :
    e.ohneLocks = true := by
  cases h <;> rfl

/-- **A recognized block contains no `locks`.** -/
theorem erk_ohneLocks {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a a' : Abs} {b : Block D V l Γ Λ Λ'}
    (h : Erk K a b a') : b.ohneLocks = true := by
  induction h with
  | nil => rfl
  | push d hd x hwT hLT hwG hLG rest hx h ih =>
    simpa [Block.linkPush, Block.ohneLocks, Stmt.ohneLocks, Block.arenaRumpf, Block.wurzelSetze, Block.blattEin] using ih
  | pop d hd hwG hLG hLT voll rest hv h ih =>
    simp [Block.linkPop, Block.ohneLocks, Stmt.ohneLocks, Block.arenaRumpf, Block.wurzelSetze, Block.blattEin, hv.ohneLocks, ih]
  | unlink d hd p hwT hLT voll rest hp hv h ih =>
    simp [Block.linkUnlink, Block.ohneLocks, Stmt.ohneLocks, Block.arenaRumpf, Block.wurzelSetze, Block.blattEin, hv.ohneLocks, ih]
  | kopf d hd hLG voll rest hv h ih =>
    simp [Block.linkKopfBind, Block.ohneLocks, hv.ohneLocks, ih]
  | nach d hd p hLT voll rest hp hv h ih =>
    simp [Block.linkNachBind, Block.ohneLocks, hv.ohneLocks, ih]
  | frisch v hwT hLT hwG hLG voll rest hv h ih =>
    simp [Block.arenaAlloc, Block.ohneLocks, Stmt.ohneLocks, Block.arenaRumpf, Block.wurzelSetze, Block.blattEin, hv.ohneLocks, ih]
  | nimm v hwT hLT hwK hLK voll rest hv h ih =>
    simp [Block.freiNimm, Block.ohneLocks, Stmt.ohneLocks, Block.arenaRumpf, Block.wurzelSetze, Block.blattEin, hv.ohneLocks, ih]
  | frei x hwT hLT hwK hLK rest hx h ih =>
    simp [Block.freiVar, Block.ohneLocks, Stmt.ohneLocks, Block.arenaRumpf, Block.wurzelSetze, Block.blattEin, ih]
  | wachs n hwK hLK voll rest hv h ih =>
    simp [Block.dynGrowB, Block.dynSumme, Block.ohneLocks, Stmt.ohneLocks, Block.arenaRumpf, Block.wurzelSetze, Block.blattEin, hv.ohneLocks, ih]
  | pruefe c voll rest hv h ih =>
    simp [Block.ohneLocks, hv.ohneLocks, ih]
  | nutzlast i e hwT hLT rest h ih =>
    simp [Block.ohneLocks, Stmt.ohneLocks, Block.arenaRumpf, Block.wurzelSetze, Block.blattEin, ih]
  | ite c t e rest ht he h1 h2 h iht ihe ih =>
    simp [Block.ohneLocks, Stmt.ohneLocks, Block.arenaRumpf, Block.wurzelSetze, Block.blattEin, iht, ihe, ih]
  | wurzelEin b hb x hwT hLT hwG hLG voll rest hx hv h ih =>
    simp [Block.wurzelEin, Block.ohneLocks, Stmt.ohneLocks, Block.arenaRumpf, Block.wurzelSetze, Block.blattEin, hv.ohneLocks, ih]
  | wurzelKopf b hb hLG voll rest hv h ih =>
    simp [Block.linkKopfBind, Block.ohneLocks, hv.ohneLocks, ih]
  | kind b hb C hC p hLT voll rest hp hv h ih =>
    simp [Block.linkNachBind, Block.ohneLocks, hv.ohneLocks, ih]
  | haengen b hb Cp Co hs p i hwT hLT voll rest hp hi hv h ih =>
    simp [Block.haengen, Block.ohneLocks, Stmt.ohneLocks, Block.arenaRumpf, Block.wurzelSetze, Block.blattEin, hv.ohneLocks, ih]
  | abschneiden b hb C hC p hwT hLT voll voll2 rest hp hv hv2 h ih =>
    simp [Block.abschneiden, Block.ohneLocks, Stmt.ohneLocks, Block.arenaRumpf, Block.wurzelSetze, Block.blattEin, hv.ohneLocks, hv2.ohneLocks, ih]
  | wurzelAus b hb hwG hLG hLT voll voll2 rest hv hv2 h ih =>
    simp [Block.wurzelAus, Block.ohneLocks, Stmt.ohneLocks, Block.arenaRumpf, Block.wurzelSetze, Block.blattEin, hv.ohneLocks, hv2.ohneLocks, ih]
  | forever an inv body rest hin hb hs h ihb ih =>
    simp [Block.ohneLocks, Stmt.ohneLocks, Block.arenaRumpf, Block.wurzelSetze, Block.blattEin, ihb, ih]
  | traverse t inv body rest hin hb hs h ihb ih =>
    simp [Block.ohneLocks, Stmt.ohneLocks, Block.arenaRumpf, Block.wurzelSetze, Block.blattEin, ihb, ih]
  | retry n bis body ueber rest hin hb hs hu h3 h4 h ihb ihu ih =>
    simp [Block.ohneLocks, Stmt.ohneLocks, Block.arenaRumpf, Block.wurzelSetze, Block.blattEin, ihb, ihu, ih]

/-- **A recognized end block contains no `locks`.** -/
theorem erkE_ohneLocks {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {a : Abs} {e : Endblock D V l Γ Λ}
    (h : ErkE K a e) : e.ohneLocks = true := by
  induction h with
  | ret e hΛ => rfl
  | retWhy r hΛ => rfl
  | nutzlast i e hwT hLT rest h ih => simp [Endblock.ohneLocks, Stmt.ohneLocks, ih]
  | ite c t e rest ht he h1 h2 h ih =>
    simp [Endblock.ohneLocks, Stmt.ohneLocks, erk_ohneLocks ht, erk_ohneLocks he, ih]
  | forever an inv body rest hin hb hs h ih =>
    simp [Endblock.ohneLocks, Stmt.ohneLocks, erk_ohneLocks hb, ih]
  | traverse t inv body rest hin hb hs h ih =>
    simp [Endblock.ohneLocks, Stmt.ohneLocks, erk_ohneLocks hb, ih]
  | retry n bis body ueber rest hin hb hs hu h3 h4 h ih =>
    simp [Endblock.ohneLocks, Stmt.ohneLocks, erk_ohneLocks hb, erk_ohneLocks hu, ih]

end Ohne

section Beweis
variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {A : FreiForm D} (K : Dekl A) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

/-- **`execEndH_eq_execEnd` for a recognized end block** (the premise 3 of 8a.3). -/
theorem erkE_execEndH {a : Abs} {e : Endblock D V l Γ Λ} (h : ErkE K a e) (σ : World D) (ρ : Env D Γ) :
    execEndH S O U passes R e σ ρ = execEnd O passes R e σ ρ :=
  Endblock.execH_ohne S O U passes R e (erkE_ohneLocks h) σ ρ

/-- The same for a recognized block. -/
theorem erk_execBlockH {a a' : Abs} {b : Block D V l Γ Λ Λ'} (h : Erk K a b a') (σ : World D) (ρ : Env D Γ) :
    execBlockH S O U passes R b σ ρ = execBlock O passes R b σ ρ :=
  Block.execH_ohne S O U passes R b (erk_ohneLocks h) σ ρ

/-- **Soundness of the recognizer over the lock-invariant semantics:** a recognized block run under `execBlockH` (any lock
    family, any environment move) ends as the state promises. -/
theorem erk_erhaeltH {a a' : Abs} {b : Block D V l Γ Λ Λ'} (h : Erk K a b a') (σ : World D) (ρ : Env D Γ)
    (hS : K.Ok σ) (hP : StrukturPasst K a σ ρ) : StrukturPost K a' (execBlockH S O U passes R b σ ρ) := by
  rw [erk_execBlockH S O U passes R K h]
  exact erk_erhaelt O passes R K h σ ρ hS hP

/-- **A function body that knows nothing at entry**, over `execEndH` -- the shape `InvGutS` quantifies (the arena part
    of D3 of 8a.3): the body returns, or fails, in a world where the arena invariant holds. -/
theorem erkE_koerperH {e : Endblock D V l Γ Λ} (h : ErkE K Abs.leer e) (σ : World D) (ρ : Env D Γ) (hS : K.Ok σ)
    (b : Abs) : StrukturPost K b (execEndH S O U passes R e σ ρ).zuAusgang := by
  rw [erkE_execEndH S O U passes R K h]
  exact erkE_koerper O passes R K h σ ρ hS b

end Beweis

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.erk_ohneLocks
#print axioms Gabbro.Grammatik.erkE_koerperH
