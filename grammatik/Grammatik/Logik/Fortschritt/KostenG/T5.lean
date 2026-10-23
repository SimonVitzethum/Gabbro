/- Part 5 of 5 of `KostenG` (split by instrumente/teile/lean-teilen.py; the umbrella `KostenG.lean` imports all parts). -/
import Grammatik.Logik.Fortschritt.KostenG.T4

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- No zero slip, bind site: a foreign bind costs at least one step even at
    declared `0`. -/
theorem fremd_kein_null_bind (fa : D.Ax → Nat) (c : D.Fn → Nat) (pa : Nat)
    (V : Vertrag D) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} (a : D.Ax)
    (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Block D V l (τ :: Γ) Λ Λ') :
    1 ≤ kostenBlockF (V := V) fa c pa (Block.bindAxiom (V := V) (l := l) a args he hw hg hd hgd rest) := by
  simp only [kostenBlockF, kostenBlock]; omega

/-- The depth bound with declared foreign costs on top: the §1 depth cost of
    the body plus the body's foreign costs. -/
def kostenTiefF (P : Programm D) (fa : D.Ax → Nat) (pa : Nat) : Nat → D.Fn → Nat
  | 0, _ => 0
  | n + 1, g => kostenEnd (kostenTief P pa n) pa (P.rumpf g) + fremdEnd fa pa (P.rumpf g)

/-- The foreign-inclusive depth bound covers the §1 depth bound. -/
theorem kostenTiefF_ge (P : Programm D) (fa : D.Ax → Nat) (pa : Nat) (n : Nat) (g : D.Fn) :
    kostenTief P pa n g ≤ kostenTiefF P fa pa n g := by
  cases n with
  | zero => exact Nat.le_refl _
  | succ m => simp only [kostenTief, kostenTiefF]; omega

/-- **Budget preservation over foreign calls.** Let thread `f` enter a frame
    of `g` admitted at call depth `n + 1`, as in `frame_schritte_beschraenkt`.
    On ANY run on which the frame stays active, thread `f` takes at most
    `kostenTiefF P fa passes (n + 1) g` own steps -- foreign (`axiomCall`,
    `bindAxiom`: syscall/Ax/extern) steps included, each counting its
    DECLARED cost `fa` on top of the §1 dispatch step, never slipping
    through at zero. Same premises as `Zielsatz.ZeitAb`, drop-in
    right-hand side; `FortschrittG` is untouched (foreign edges are `blatt`
    steps, `schrittArt` case (A)). -/
theorem fremd_budget_erhalten (P : Programm D) (O : Orakel D) (passes : Nat)
    (fa : D.Ax → Nat) (f : Faden) (g : D.Fn) (n : Nat) (hadm : rufTief P (n + 1) g = true)
    {rho : Env D (D.params g)} {s0 : World D} {k : Nat} {M1 M2 : RufMaschineG D}
    (hE : Eintritt P f g rho s0 k M1)
    (run : SegLauf P O passes M1 M2) (hA : aktivVor f k run) :
    segZaehle run f ≤ kostenTiefF P fa passes (n + 1) g :=
  Nat.le_trans (frame_schritte_beschraenkt P O passes f g n hadm hE run hA)
    (kostenTiefF_ge P fa passes (n + 1) g)

#print axioms Gabbro.Grammatik.fremd_axiomCall
#print axioms Gabbro.Grammatik.fremd_bindAxiom
#print axioms Gabbro.Grammatik.fremd_kein_null_stmt
#print axioms Gabbro.Grammatik.fremd_kein_null_bind
#print axioms Gabbro.Grammatik.kostenTiefF_ge
#print axioms Gabbro.Grammatik.fremd_budget_erhalten

end Gabbro.Grammatik

/-! ## CUTS:

  What is proved (no premise beyond the Bool checks and the run itself):
  * `schrittArt` -- all 72 rules of `RufSchrittG`: a head move lowers the
    potential by at least one, a push hands the callee at most the cost the
    caller counted for it, a pop drops a frame of potential at least one.
  * `frame_schritte_beschraenkt` (TARGET 1) -- callees admitted by call
    depth (`rufTief`, decidable): own steps between entry and return
    `≤ kostenTief P passes (n + 1) g`; `frame_schritte_beschraenkt_tief`
    the same for every function `Tief` admits (`tief_rufTief`,
    `tiefK_rufTief`).
  * `kosten_passt_deklaration` (TARGET 2) -- the Bool `kostenPasst` over a
    closed list with a declared table: own steps `≤ decl g`.
  * `spiegel_stmt`/`spiegel_block`/`spiegel_end`, `frame_schritte_pruefer`
    (TARGET 3) -- Lean bound `≤` checker number `+ zusatz`, per form; the
    findings F1-F9 in §11.
  * `eintritt_start`, `eintritt_push` -- every frame begins in `Eintritt`;
    `segLauf_erreichbar`/`erreichbar_segLauf` -- counted runs are exactly
    the reachability derivations.
  * `fremd_axiomCall`/`fremd_bindAxiom` (§13) -- foreign edges count their
    DECLARED cost `fa`; `fremd_kein_null_stmt`/`fremd_kein_null_bind` -- no
    zero slip; `kostenTiefF_ge`/`fremd_budget_erhalten` -- budget
    preservation over foreign calls, drop-in for `Zielsatz.ZeitAb`
    (`FortschrittG` untouched: foreign edges are `blatt` steps).

  What the bound does NOT say:
  * WAITING. A step that cannot fire is no step: `dannLocks` needs the lock
    free at every other thread (`RufFreiG`), `dannAwaits` needs the oracle's
    `sichtbar`. The time a thread waits is a SCHEDULER ASSUMPTION -- fair
    scheduling and bounded lock hold time -- named here and proved nowhere.
    The hold bound exists in the surface language (`lock L … held <= N
    ops`, checked by `K002`), but `Deklaration` has no field for it, so no
    waiting bound under fairness is stated (TARGET 4 not done: not in the
    model).
  * TERMINATION. The theorems bound the steps UNTIL the return; they do
    not say the frame returns. A frame may stop taking steps for good: a
    lock never freed, an `awaits` never visible, a `forever` whose budget
    `passes` ran out (`ewig 0` has no rule), a leaf whose `execStmt` is not
    `ok` (a logic or hardware outcome), an end block `leave`/`next` (no
    rule steps it). Then it takes fewer steps, never more.
  * TIME. Steps of G are not operations of kosten.rs and not cycles; §11
    relates the first two, `Ziel.lean` `fristAlsAnnahme` the last.
  * Indirect calls (`callInd`, `bindCallInd`) are excluded (gate `ZS = fun _ => false`): the
    Lean signature carries no cost, so a pointer's callee has no number
    (F8). The declared costs are an explicit table `decl`, not a field of
    `Signatur` (a field broke the anonymous constructors in `Satz.lean` and
    `Zeugnis.lean`, lane 132).
  * `kostenK` is a READING of `kosten.rs` over the Lean syntax, written by
    hand from the Rust source; it is not extracted from the checker, and
    the correspondence is only as good as that reading. Forms without a
    checker number in the Lean term are outside `spiegelS`.
  * `forever`: the bound is relative to the machine budget `passes`.

  Reused from lane 132 (`muse-archiv/132`): `kostenExpr`/`kostenArgs`/
  `kostenErg`, the `SegLauf`/`segZaehle`/`aktivVor`/`Eintritt` idea, the
  depth-indexed admission. Redone: the costs (lane 132's end-block bonus
  `1` for an unfoldable compound made `endeEntf` keep the potential equal,
  `1 + k s + k r = k s + 1 + k r` against an empty block of cost `1` -- no
  strict drop, so its step lemma could not close; here the bonus is `2`,
  `entfZ`), the fragment (lane 132 covered leaves, calls, `ite`, `locks`,
  `breaking`; here every form except indirect calls), and the invariant
  (lane 132 tracked the entry frame's key; the bound needs only the
  potential of the frames above the entry depth).
-/

#print axioms Gabbro.Grammatik.schrittArt
#print axioms Gabbro.Grammatik.frame_schritte_beschraenkt
#print axioms Gabbro.Grammatik.frame_schritte_beschraenkt_tief
#print axioms Gabbro.Grammatik.kosten_passt_deklaration
#print axioms Gabbro.Grammatik.frame_schritte_pruefer
#print axioms Gabbro.Grammatik.spiegel_end
#print axioms Gabbro.Grammatik.eintritt_push
#print axioms Gabbro.Grammatik.erreichbar_segLauf

