module

public import Grammatik.Logik.Fortschritt.KostenG.T1
public import Grammatik.Logik.Fortschritt.KostenG.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Motor
variable {ι : Type} (T : ι → D.Fn → Nat) (S : ι → D.Fn → Bool) (nx : ι → D.Fn → ι)
  (P : Programm D) (O : Orakel D) (pa : Nat)

theorem kinv_lauf
    (hS1 : ∀ i g, S i g = true → kostenEnd (T (nx i g)) pa (P.rumpf g) ≤ T i g)
    (hS2 : ∀ i g, S i g = true → rufeE (S (nx i g)) (fun _ => false) true (P.rumpf g) = true)
    {B : Nat} {f : Faden} {k : Nat} {M1 : RufMaschineG D}
    (h0 : KInv T S pa B f k M1 0) :
    ∀ {M2 : RufMaschineG D} (run : SegLauf P O pa M1 M2), aktivVor f k run →
      segZaehle run f ≤ B ∧
      (k ≤ (M2.faeden f).stapel.length → KInv T S pa B f k M2 (segZaehle run f)) := by
  intro M2 run
  induction run with
  | start =>
    intro _
    refine ⟨?_, fun _ => h0⟩
    obtain ⟨_, _, _, _, _, _, hB⟩ := h0
    simp only [segZaehle]
    omega
  | schritt M M' g run' hs ih =>
    intro hA
    obtain ⟨hA', hk⟩ := hA
    have hI := (ih hA').2 hk
    exact kinv_schritt T S nx P O pa hS1 hS2 hI hs

/-- **The engine theorem**: a frame entered at index `i0` whose body names
    only callees admitted at `i0` takes at most `kostenEnd (T i0)` of its
    body own steps until (and including) its return. -/
theorem rahmen_schritte
    (hS1 : ∀ i g, S i g = true → kostenEnd (T (nx i g)) pa (P.rumpf g) ≤ T i g)
    (hS2 : ∀ i g, S i g = true → rufeE (S (nx i g)) (fun _ => false) true (P.rumpf g) = true)
    {f : Faden} {g : D.Fn} {rho : Env D (D.params g)} {s0 : World D} {k : Nat}
    {M1 M2 : RufMaschineG D} (hE : Eintritt P f g rho s0 k M1) (i0 : ι)
    (hok : rufeE (S i0) (fun _ => false) true (P.rumpf g) = true)
    (run : SegLauf P O pa M1 M2) (hA : aktivVor f k run) :
    segZaehle run f ≤ kostenEnd (T i0) pa (P.rumpf g) :=
  (kinv_lauf T S nx P O pa hS1 hS2 (kinv_eintritt T S P pa hE i0 hok) run hA).1

end Motor
/-! ## 9. TARGET 1: the bound by call depth -/

/-- The cost of `g` with calls nested at most `n` deep: at depth `0` no
    callee is admitted (cost `0`, never used); at depth `n + 1` the body,
    each call counting its callee at depth `n`. -/
def kostenTief (P : Programm D) (pa : Nat) : Nat → D.Fn → Nat
  | 0, _ => 0
  | n + 1, g => kostenEnd (kostenTief P pa n) pa (P.rumpf g)

/-- The call-depth admission, as a Bool: at depth `n + 1` a function is
    admitted if every direct callee of its body is admitted at depth `n`
    and the body has no indirect call; at depth `0` none is. The same depth
    discipline as `TiefK`/`Tief` (RufUmkehrRufG.lean, RufAdaequatRufG.lean),
    over the WHOLE syntax instead of a fragment, and decidable. -/
def rufTief (P : Programm D) : Nat → D.Fn → Bool
  | 0, _ => false
  | n + 1, g => rufeE (rufTief P n) (fun _ => false) true (P.rumpf g)

/-- **TARGET 1 -- `frame_schritte_beschraenkt`.** Let thread `f` enter a
    frame of `g` with `k` frames below it (`Eintritt`, as every start frame
    and every pushed callee does), and let `g` be admitted at call depth
    `n + 1` (`rufTief`: callees nested at most `n` deep, no indirect call).
    On ANY run from there on which the frame has not returned before the
    last step (`aktivVor`), thread `f` takes at most
    `kostenTief P passes (n + 1) g` steps -- the body's cost with each call
    counting its callee's cost one depth down, each `traverse` its body
    times `count`, each `retry n` its body `n` times, each `forever` its
    body `passes` times.

    Counted: firings of `RufSchrittG` by `f`, including the frame's return
    if the run ends with it. Not counted: other threads' steps, and time
    during which a step of `f` cannot fire (a `locks` whose lock another
    thread holds, an `awaits` whose payload is not visible) -- the
    SCHEDULER ASSUMPTION of the file header. -/
theorem frame_schritte_beschraenkt (P : Programm D) (O : Orakel D) (passes : Nat)
    (f : Faden) (g : D.Fn) (n : Nat) (hadm : rufTief P (n + 1) g = true)
    {rho : Env D (D.params g)} {s0 : World D} {k : Nat} {M1 M2 : RufMaschineG D}
    (hE : Eintritt P f g rho s0 k M1)
    (run : SegLauf P O passes M1 M2) (hA : aktivVor f k run) :
    segZaehle run f ≤ kostenTief P passes (n + 1) g :=
  rahmen_schritte (kostenTief P passes) (rufTief P) (fun i _ => i - 1) P O passes
    (fun i h hS => by
      cases i with
      | zero => simp only [rufTief, Bool.false_eq_true] at hS
      | succ m => exact Nat.le_refl _)
    (fun i h hS => by
      cases i with
      | zero => simp only [rufTief, Bool.false_eq_true] at hS
      | succ m => exact hS)
    hE n hadm run hA

/-! ## 10. TARGET 2: the declared costs -/
