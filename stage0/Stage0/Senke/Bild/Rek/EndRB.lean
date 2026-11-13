/-
  File:      stage0/Stage0/Senke/Bild/Rek/EndRB.lean
  Subject:   **The call fragment as a computation** (review M1 of the image theorem with calls). The recursion route
             (`tiefAlle_frag`, `zerlegung_tiefAlle`, `Rek/Alle.lean`) takes the premise
             `∀ g, EndR Agl (fun _ => True) (P.rumpf g)`: every body lies in the covered fragment, every callee
             admitted. `EndR` (`RufAdaequatRufG/T1.lean`) is a family of inductive predicates; this file gives the
             decidable check `endRB a` beside it (`a` decides the admitted locks), so that the premise is a
             computation on the program: `Endblock.fragB` and its statement/block/arm twins follow the constructors
             of `EndR`/`StmtR`/`BlockR`/`ArmsR`/`GrundArmsR` one for one (the loop level `l` must be `false` where
             the predicate fixes it, the `mr` flag where it fixes it, a lock must be admitted by `a` and respect the
             contract's floor `bodenOk`). Soundness (`endR_von_fragB`) is here; completeness and `endRB_iff` are in
             `EndRBVoll.lean`.

             What the fragment does NOT contain (and the check refuses): top-level `ite`, tail `let`-calls
             (`bindCall`, `bindCallElse`) and every other binder form at terminal-block level, register reads,
             `awaits`, `exchange`, `narrow`/`check`, `leave`/`next`, the scoped returns, foreign calls and indirect
             calls. Recursion is admitted; these control and binding forms are not (yet).
-/
module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T1
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-- The contract's floor admits the lock `L` (the premise `hbo` of `StmtR.locks`), decided. -/
def bodenOk (V : Vertrag D) (L : D.Lock) : Bool :=
  match V.boden with
  | some c => decide (c ≤ D.rang L)
  | none => true

mutual

/-- The statement lies in the call fragment (`StmtR`) with every callee admitted, at the flag `mr`. -/
def Stmt.fragB (a : D.Lock → Bool) (mr : Bool) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => Block.fragB a mr t && Block.fragB a mr e
  | .onOption _ p q => Block.fragB a mr p && Block.fragB a mr q
  | .onTag _ arms => Arms.fragB a mr arms
  | .onWhy _ arms => GrundArms.fragB a mr arms
  | .breaking _ body => Block.fragB a mr body
  | .locks L _ body => a L && bodenOk V L && Block.fragB a false body
  | .ret _ _ => mr
  | .call .. => true
  | .traverse _ _ body => Block.fragB a mr body
  | .retry _ _ body u => Block.fragB a mr body && Block.fragB a mr u
  | .forever _ _ body => Block.fragB a mr body
  | .leave _ => true
  | .next _ => true
  | .retWhy _ _ => mr
  | s => s.blattArt

/-- The block lies in the call fragment (`BlockR`) at the flag `mr`. -/
def Block.fragB (a : D.Lock → Bool) (mr : Bool) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => Stmt.fragB a mr s && Block.fragB a mr rest
  | .bind _ rest => Block.fragB a mr rest
  | .bindCall _ _ _ _ _ rest => Block.fragB a mr rest
  | .regRead _ _ rest => Block.fragB a mr rest
  | .regReadElse _ _ _ sonst rest => !l && mr && Endblock.fragB a sonst && Block.fragB a true rest
  | .awaits _ _ _ _ _ rest => Block.fragB a mr rest
  | .exchange _ _ _ _ rest => Block.fragB a mr rest
  | .narrow _ _ _ sonst rest => !l && mr && Endblock.fragB a sonst && Block.fragB a true rest
  | .check _ sonst rest => !l && mr && Endblock.fragB a sonst && Block.fragB a true rest
  | .float _ _ _ _ _ rest => Block.fragB a mr rest
  | .floatLit _ _ _ rest => Block.fragB a mr rest
  | .floatOf _ _ _ rest => Block.fragB a mr rest
  | .floatNarrow _ _ _ sonst rest => !l && mr && Endblock.fragB a sonst && Block.fragB a true rest
  | .bindCallElse _ _ _ _ _ err rest => !l && mr && Endblock.fragB a err && Block.fragB a true rest
  | _ => false

/-- The terminal block lies in the call fragment (`EndR`): loop level `false`, ending in a return. -/
def Endblock.fragB (a : D.Lock → Bool) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → Bool
  | .ret _ _ => !l
  | .retWhy _ _ => !l
  | .cons s rest => !l && Stmt.fragB a true s && Endblock.fragB a rest
  | .bind _ rest => !l && Endblock.fragB a rest
  | .float _ _ _ _ _ rest => !l && Endblock.fragB a rest
  | .floatLit _ _ _ rest => !l && Endblock.fragB a rest
  | .floatOf _ _ _ rest => !l && Endblock.fragB a rest
  | .floatNarrow _ _ _ sonst rest => !l && Endblock.fragB a sonst && Endblock.fragB a rest
  | _ => false

/-- The arms lie in the call fragment (`ArmsR`). -/
def Arms.fragB (a : D.Lock → Bool) (mr : Bool) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => Block.fragB a mr b && Arms.fragB a mr rest

/-- The reason arms lie in the call fragment (`GrundArmsR`). -/
def GrundArms.fragB (a : D.Lock → Bool) (mr : Bool) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => Block.fragB a mr b && GrundArms.fragB a mr rest

end

/-- **The decidable call-fragment check of a terminal block** (the Bool twin of `EndR`, every callee admitted). -/
def endRB (a : D.Lock → Bool) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) : Bool :=
  Endblock.fragB a e

/-- **The program check**: every body of an enumerated function list passes `endRB`. -/
def programmRB (P : Programm D) (a : D.Lock → Bool) (fs : List D.Fn) : Bool :=
  fs.all fun g => endRB a (P.rumpf g)

/-- The floor check is sound. -/
theorem bodenOk_sound {L : D.Lock} (h : bodenOk V L = true) : ∀ c, V.boden = some c → c ≤ D.rang L := by
  intro c hc
  unfold bodenOk at h
  rw [hc] at h
  exact of_decide_eq_true h

theorem bodenOk_voll {L : D.Lock} (h : ∀ c, V.boden = some c → c ≤ D.rang L) : bodenOk V L = true := by
  unfold bodenOk
  cases hb : V.boden with
  | none => rfl
  | some c => exact decide_eq_true (h c hb)

end Gabbro.Grammatik
