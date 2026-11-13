/-
  File:      stage0/Stage0/Senke/Bild/Rek/Alle.lean
  Subject:   **Recursion in the image theorem: the depth bound of the image is the rank** (package P5 of the closed
             calls of the image theorem, part 1).
             `Tief P A n` (P4) admits at depth `n + 1` the callees whose bodies are in the call fragment with callees
             at depth `n`, and NONE at depth `0`. A recursive callee therefore lies in no `Tief`: its own call chain
             bottoms out in `Tief P A 0 = False`. But the obligation at depth `0` is vacuous: the handler of depth `0`
             never ends normally (`rufRumpf … 0 = logik (abstieg …)`, and so `rufAt … 0`), so `RufOk` holds there for
             EVERY callee set. `TiefAlle` is `Tief` with that bottom: `True` at depth `0`.
             * `rufOk_tiefAlle`: the callee obligation of the body-running handler holds at every depth for
               `TiefAlle` (the induction of `rufOk_tief`, with the vacuous bottom);
             * `rufOk_gleich_tiefAlle`: the same for the image's handler `rufAt`, up to read events;
             * `tief_tiefAlle`: `Tief ⊆ TiefAlle` (nothing of P4 is lost);
             * `tiefAlle_frag`: when every body is in the call fragment with EVERY callee admitted
               (`EndR A (fun _ => True) (P.rumpf g)`) -- recursive bodies included, no rank -- every function is in
               `TiefAlle P A n` at every depth `n`.

             Why this is enough for recursion: the image runs `main`'s callees as `rufAt (depth - 1)` (`rumpfRahmen`),
             every callee one level lower (the prologue's depth guard, `guardC 2 105`, stops the image at depth word
             `0` with the outcome `logik (abstieg …)` of `rufAt 0`), and `depth < 2 ^ 64` is fixed by the stack band
             (`Emitted.bild_anfang_codes`). So every run of the image has a finite call depth `≤ depth - 1`, and the
             call obligation is discharged at EXACTLY that depth by `rufOk_gleich_tiefAlle`. A call deeper than the
             bound is not a normal end (`abstieg`), so no decomposed prefix steps over it. Which check supplies the
             depth bound: the compiler itself (`lowFun`'s depth guard and `depthOf` of the image); the checker
             (`Akzeptiert`) proves no termination and needs not -- non-termination and stack depth are on the
             NOT CLAIMED list of `Spec.lean`. What remains a premise is the fragment fact `EndR A (fun _ => True)`
             about the bodies, decidable for a finite program, as the rank was in P4.
-/
module
public import Stage0.Senke.Bild.Rek.Tief
public import Stage0.Senke.Bild.Ruf.RufOkGleich
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-! ## The callee sets with a vacuous bottom -/

/-- **The callees admitted at depth `n`, recursion included**: at depth `0` every function (the handler of depth `0`
    never ends normally), at depth `n + 1` the functions whose body is in the call fragment with the callees of
    depth `n`. -/
def TiefAlle (P : Programm D) (A : D.Lock → Prop) : Nat → D.Fn → Prop
  | 0, _ => True
  | n + 1, g => EndR A (TiefAlle P A n) (P.rumpf g)

/-- The body-running handler of depth `0` never ends normally. -/
theorem rufRumpf_null_eq (P : Programm D) (O : Orakel D) (passes : Nat) (g : D.Fn) (σ : World D)
    (ρ : Env D (D.params g)) : rufRumpf P O passes 0 g σ ρ = .logik (.abstieg g) := by
  simp only [rufRumpf]

/-- No normal return at depth `0`. -/
theorem rufRumpf_null_ok (P : Programm D) (O : Orakel D) (passes : Nat) (g : D.Fn) (σ : World D)
    (ρ : Env D (D.params g)) {σ' : World D} {v : ErgVal D (D.erg g)} :
    rufRumpf P O passes 0 g σ ρ ≠ .ok σ' v := by
  simp only [rufRumpf, ne_eq, reduceCtorEq, not_false_eq_true]

/-- No reason at depth `0`. -/
theorem rufRumpf_null_why (P : Programm D) (O : Orakel D) (passes : Nat) (g : D.Fn) (σ : World D)
    (ρ : Env D (D.params g)) {σ' : World D} {r : Fin (D.gruende g)} :
    rufRumpf P O passes 0 g σ ρ ≠ .why σ' r := by
  simp only [rufRumpf, ne_eq, reduceCtorEq, not_false_eq_true]

/-- **The callee obligation of the body-running handler, recursion included**: at every depth `n`, `RufOk` holds for
    the callees `TiefAlle P A n`. At depth `0` it is vacuous (no normal end of `rufRumpf … 0`); at `n + 1` it is the
    step of `rufOk_tief` (`endRetR` with the obligation of depth `n`). -/
theorem rufOk_tiefAlle (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden)
    (A : D.Lock → Prop) : ∀ n, RufOk P O passes f A (rufRumpf P O passes n) (TiefAlle P A n)
  | 0 => ⟨fun g _ σ1 _ rhoG _ hR => absurd hR (rufRumpf_null_ok P O passes g σ1 rhoG),
      fun g _ σ1 _ rhoG _ hR => absurd hR (rufRumpf_null_why P O passes g σ1 rhoG)⟩
  | n + 1 => by
      refine ⟨?_, ?_⟩
      · intro g hC σ1 σ' rhoG v hR M caller rst log hZ ziel hart hΛ hA
        exact endRetR P O passes f g caller rst rhoG σ1 A (rufRumpf P O passes n) (TiefAlle P A n)
          ziel (fun _ => caller) (rufOk_tiefAlle P O passes f A n) (P.rumpf g) hC log σ1 rhoG
          (.zurueck σ' v) hart (by rw [rufRumpf_ok hR]; rfl) M hZ hΛ hA
      · intro g hC σ1 σ' rhoG r hR M caller rst log hZ zielG hart hΛ hA
        exact endRetR P O passes f g caller rst rhoG σ1 A (rufRumpf P O passes n) (TiefAlle P A n)
          (fun _ => caller) zielG (rufOk_tiefAlle P O passes f A n) (P.rumpf g) hC log σ1 rhoG
          (.why σ' r) hart (by rw [rufRumpf_grund hR]; rfl) M hZ hΛ hA

/-- **THE CALL OBLIGATION OF `rufAt` AT EVERY DEPTH, RECURSION INCLUDED, UP TO READ EVENTS.** Under a read-blind
    oracle the image's handler `rufAt n` keeps `RufOkGleich` for the callees `TiefAlle P A n`. -/
theorem rufOk_gleich_tiefAlle {P : Programm D} {O : Orakel D} {passes : Nat} (hO : Leseblind O) (f : Faden)
    (A : D.Lock → Prop) (n : Nat) : RufOkGleich P O passes f A (rufAt P O passes n) (TiefAlle P A n) :=
  ⟨rufRumpf P O passes n, rufAt_rufRumpf_lg_alle (P := P) (passes := passes) hO n, rufOk_tiefAlle P O passes f A n⟩

/-! ## `TiefAlle` contains `Tief`, and holds for every function of a program in the fragment -/

/-- **Nothing of P4 is lost**: every callee admitted at depth `n` by `Tief` is admitted by `TiefAlle`. -/
theorem tief_tiefAlle (P : Programm D) (A : D.Lock → Prop) : ∀ (n : Nat) (g : D.Fn), Tief P A n g → TiefAlle P A n g
  | 0, _, _ => trivial
  | n + 1, g, h => by
    show EndR A (TiefAlle P A n) (P.rumpf g)
    exact endR_mono (fun g' (hg' : Tief P A n g') => tief_tiefAlle P A n g' hg') h

/-- **Recursion without a rank**: when every body is in the call fragment with every callee admitted (recursive and
    mutually recursive bodies included), every function is admitted at every depth. -/
theorem tiefAlle_frag (P : Programm D) (A : D.Lock → Prop) (h : ∀ g, EndR A (fun _ => True) (P.rumpf g)) :
    ∀ (n : Nat) (g : D.Fn), TiefAlle P A n g
  | 0, _ => trivial
  | n + 1, g => by
    show EndR A (TiefAlle P A n) (P.rumpf g)
    exact endR_mono (fun g' _ => tiefAlle_frag P A h n g') (h g)

variable [Runner.IR.Kern]

/-- **The program-level discharge, recursion included**: a decomposed prefix in the fragment with every callee
    admitted is one whose callees are admitted at every depth `n`, when every body is in that fragment. -/
theorem zerlegung_tiefAlle {P : Programm D} {Agl : D.Lock → Prop} (h : ∀ g, EndR Agl (fun _ => True) (P.rumpf g))
    {n : Nat} {B : BodyFrame D} {l : Bool} {Γ Γe : Ctx} {Λ Λe : List (Res D)}
    {eb : Endblock D (vertragVon D B.f) l Γ Λ} {ebe : Endblock D (vertragVon D B.f) l Γe Λe} {σ σe : World D}
    {ρ : Env D Γ} {ρe : Env D Γe} (hk : Zerlegung B Agl (fun _ => True) eb σ ρ ebe σe ρe) :
    Zerlegung B Agl (TiefAlle P Agl n) eb σ ρ ebe σe ρe :=
  hk.mono (fun g _ => tiefAlle_frag P Agl h n g)

#print axioms rufOk_tiefAlle
#print axioms rufOk_gleich_tiefAlle

end Gabbro.Stage0.Senke.BildLauf
