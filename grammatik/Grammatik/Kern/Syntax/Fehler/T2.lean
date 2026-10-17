/- Part 2 of 2 of `Fehler` (split by instrumente/teile/lean-teilen.py; the umbrella `Fehler.lean` imports all parts). -/
import Grammatik.Kern.Syntax.Fehler.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}
variable {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
variable {V : Vertrag D} {l : Bool}

/-- Stuck-or-fault in the disjunctive form: own logic or named fault. -/
theorem stecken_klassifikation (a : AusF V l Γ) (h : IstStecken a) :
    (∃ e : Logik D, a = .widen (.logik e)) ∨
    (∃ e : Hardware D, a = .widen (.hardware e)) ∨
    (∃ k, a = .fehler k) := by
  cases a with
  | fehler k => exact .inr (.inr ⟨k, rfl⟩)
  | widen o =>
      cases o with
      | ok σ ρ => simp [IstStecken, endZustandF] at h
      | zurueck σ v => simp [IstStecken, endZustandF] at h
      | why σ r => simp [IstStecken, endZustandF] at h
      | leave h' σ ρ => simp [IstStecken, endZustandF] at h
      | next h' σ ρ => simp [IstStecken, endZustandF] at h
      | logik e => exact .inl ⟨e, rfl⟩
      | hardware e => exact .inr (.inl ⟨e, rfl⟩)

/-! ## 10. `evalF` agreement through the step and loop shapes, end to end -/

/-- Agreement through the `evalAll` shape, for EVERY pointwise-agreeing
    evaluator -- including one that faults one day (unlike today's `evalF`). -/
theorem evalArgsMit_stimmt {τs : List Ty}
    (aus : ∀ {t}, Expr D Γ Λ t → ErgebnisF D t)
    (σ₀ σ : World D) (ρ : Env D Γ) (as : Args D Γ Λ τs) (ρ' : Env D τs)
    (hstim : ∀ {t} (e : Expr D Γ Λ t), aus e = .val (eval σ₀ e σ ρ))
    (h : evalArgsMit aus as = .inl ρ') :
    evalArgs σ₀ as σ ρ = ρ' := by
  induction as with
  | nil =>
      simp only [evalArgsMit] at h
      cases h
      rfl
  | cons e rest ih =>
      simp only [evalArgsMit, hstim] at h
      obtain ⟨vs, hs⟩ := evalArgsMit_ok aus rest (fun e => ⟨_, hstim e⟩)
      simp only [hs] at h
      cases h
      exact congrArg (Env.cons (eval σ₀ e σ ρ)) (ih _ hs)

/-- Agreement end to end: what today's fault-free argument list carries is what
    `evalArgs` of `Semantik.lean` computes. -/
theorem evalArgsF_stimmt {τs : List Ty} (σ₀ σ : World D) (ρ : Env D Γ)
    (as : Args D Γ Λ τs) (ρ' : Env D τs)
    (h : evalArgsF σ₀ σ ρ as = .inl ρ') :
    evalArgs σ₀ as σ ρ = ρ' :=
  evalArgsMit_stimmt _ σ₀ σ ρ as ρ' (fun _ => rfl) h

/-- A fault-free world step, lifted into the fault channel. -/
def schrittRein (f : World D → World D) : World D → (World D ⊕ Fehlerklasse) :=
  fun σ => .inl (f σ)

/-- Step-sequence agreement end to end: fault-free steps thread the world as the
    fold does -- the `execBlock` sequencing shape without the fault arm. -/
theorem schrittFolge_rein (fs : List (World D → World D)) (σ : World D) :
    schrittFolge (fs.map schrittRein) σ = .inl (fs.foldl (fun σ f => f σ) σ) := by
  induction fs generalizing σ with
  | nil => rfl
  | cons f fs ih =>
      simp only [List.map_cons, schrittFolge, schrittRein, List.foldl_cons]
      exact ih _

/-- A fault-free element step, lifted into the fault channel. -/
def durchlaufRein {α : Type} (f : α → World D → World D) :
    α → World D → (World D ⊕ Fehlerklasse) :=
  fun x σ => .inl (f x σ)

/-- Traversal agreement end to end: one fault-free pass per element folds the
    world -- the `traverseLauf` skeleton without invariant, `leave` and `next`
    arms (control, carried by `weiter`, not by the fault channel). -/
theorem durchlaufF_rein {α : Type} (f : α → World D → World D) (xs : List α)
    (σ : World D) :
    durchlaufF (durchlaufRein f) xs σ = .inl (xs.foldl (fun σ x => f x σ) σ) := by
  induction xs generalizing σ with
  | nil => rfl
  | cons x xs ih =>
      simp only [durchlaufF, durchlaufRein, List.foldl_cons]
      exact ih _

/-- Loop agreement end to end: a fuel-bounded fault-free loop IS the step
    sequence of its unfoldings -- the `foreverLauf` skeleton without the
    `fortschritt` arm (a hardware assumption, not a fault). -/
theorem schleifeF_als_folge (f : World D → World D) (n : Nat) (σ : World D) :
    schleifeF (schrittRein f) n σ =
      schrittFolge (List.replicate n (schrittRein f)) σ := by
  induction n generalizing σ with
  | zero => rfl
  | succ n ih =>
      simp only [schleifeF, schrittRein, List.replicate_succ, schrittFolge]
      exact ih _

/-- A returned answer carries its world. -/
theorem endZustandF_zurueck (σ : World D) (v : ErgVal D V.erg) :
    endZustandF (AusF.widen (.zurueck σ v) : AusF V l Γ) = some σ :=
  rfl

/-- A raised ground carries its world. -/
theorem endZustandF_grund (σ : World D) (r : Fin V.gruende) :
    endZustandF (AusF.widen (.why σ r) : AusF V l Γ) = some σ :=
  rfl

/-- A consumed `leave` carries its world. -/
theorem endZustandF_leave (h : l = true) (σ : World D) (ρ : Env D Γ) :
    endZustandF (AusF.widen (.leave h σ ρ) : AusF V l Γ) = some σ :=
  rfl

/-- A consumed `next` carries its world. -/
theorem endZustandF_next (h : l = true) (σ : World D) (ρ : Env D Γ) :
    endZustandF (AusF.widen (.next h σ ρ) : AusF V l Γ) = some σ :=
  rfl

/-! ## 11. Fault threading through the `execBlock`/`traverseLauf` shapes -/

/-- The `execBlock` sequencing shape over fault-carrying steps: `nil` answers
    `ok`, `cons` continues through `AusF.folge` -- a faulted head faults the
    block, a non-`ok` exit stops it, exactly as `execBlock`'s `| o => o` arm. -/
def blockF : List (World D → Env D Γ → AusF V l Γ) → World D → Env D Γ → AusF V l Γ
  | [], σ, ρ => .widen (.ok σ ρ)
  | s :: ss, σ, ρ => (s σ ρ).folge (fun σ' ρ' => blockF ss σ' ρ')

/-- The empty block answers `ok` -- the `execBlock.nil` shape. -/
theorem blockF_nil (σ : World D) (ρ : Env D Γ) :
    blockF ([] : List (World D → Env D Γ → AusF V l Γ)) σ ρ = .widen (.ok σ ρ) :=
  rfl

/-- A faulted head faults the block -- the rest does not run. -/
theorem blockF_cons_fehler (s : World D → Env D Γ → AusF V l Γ)
    (ss : List (World D → Env D Γ → AusF V l Γ)) (σ : World D) (ρ : Env D Γ)
    (k : Fehlerklasse) (h : s σ ρ = (AusF.fehler k : AusF V l Γ)) :
    blockF (s :: ss) σ ρ = (AusF.fehler k : AusF V l Γ) := by
  simp only [blockF, h, AusF.folge_fehler]

/-- An `ok` head hands world and scope to the rest -- the `execBlock` step. -/
theorem blockF_cons_ok (s : World D → Env D Γ → AusF V l Γ)
    (ss : List (World D → Env D Γ → AusF V l Γ)) (σ σ' : World D) (ρ ρ' : Env D Γ)
    (h : s σ ρ = (AusF.widen (.ok σ' ρ') : AusF V l Γ)) :
    blockF (s :: ss) σ ρ = blockF ss σ' ρ' := by
  simp only [blockF, h, AusF.folge_ok]

/-- Any other head unfolds to its `folge` -- in particular every non-`ok` exit
    stops the block, as `execBlock`'s `| o => o` arm. -/
theorem blockF_cons_weiter (s : World D → Env D Γ → AusF V l Γ)
    (ss : List (World D → Env D Γ → AusF V l Γ)) (σ : World D) (ρ : Env D Γ)
    (o : Ausgang V l Γ) (h : s σ ρ = (AusF.widen o : AusF V l Γ)) :
    blockF (s :: ss) σ ρ = (AusF.widen o).folge (fun σ' ρ' => blockF ss σ' ρ') := by
  simp only [blockF, h]

/-- A faulted head is named -- the sequencing-to-safety link for blocks. -/
theorem blockF_cons_fehler_benannt (s : World D → Env D Γ → AusF V l Γ)
    (ss : List (World D → Env D Γ → AusF V l Γ)) (σ : World D) (ρ : Env D Γ)
    (k : Fehlerklasse) (h : s σ ρ = (AusF.fehler k : AusF V l Γ)) :
    IstBenannt (blockF (s :: ss) σ ρ) := by
  rw [blockF_cons_fehler s ss σ ρ k h]
  trivial

/-- The `traverseLauf` shape with a fault arm: the step answers in `AusF`, so a
    faulted element faults the run; every `Ausgang` arm continues exactly as
    `traverseLauf` does (`ok`/`next` recurse, `leave` checks the invariant,
    everything else stops). -/
def traverseAusF (schrittF : World D → Env D (τ :: Γ) → AusF V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool) :
    List (Wert D τ) → World D → Env D Γ → AusF V l Γ
  | [], σ, ρ =>
      if (inv σ ρ).2 = true then .widen (.ok (inv σ ρ).1 ρ)
      else .widen (.logik .schleife)
  | k :: ks, σ, ρ =>
      if (inv σ ρ).2 = false then .widen (.logik .schleife)
      else match schrittF (inv σ ρ).1 (.cons k ρ) with
        | .fehler e => .fehler e
        | .widen (.ok σ' ρ') => traverseAusF schrittF inv ks σ' ρ'.tail
        | .widen (.next _ σ' ρ') => traverseAusF schrittF inv ks σ' ρ'.tail
        | .widen (.leave _ σ' ρ') =>
            if (inv σ' ρ'.tail).2 = true then .widen (.ok (inv σ' ρ'.tail).1 ρ'.tail)
            else .widen (.logik .schleife)
        | .widen (.zurueck σ' v) => .widen (.zurueck σ' v)
        | .widen (.why σ' r) => .widen (.why σ' r)
        | .widen (.logik e) => .widen (.logik e)
        | .widen (.hardware e) => .widen (.hardware e)

/-- A faulted element faults the run -- at a held invariant boundary. -/
theorem traverseAusF_kopf_fehler
    (schrittF : World D → Env D (τ :: Γ) → AusF V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (k : Wert D τ) (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ)
    (e : Fehlerklasse)
    (hinv : (inv σ ρ).2 = true)
    (h : schrittF (inv σ ρ).1 (.cons k ρ) = (AusF.fehler e : AusF V true (τ :: Γ))) :
    traverseAusF schrittF inv (k :: ks) σ ρ = (AusF.fehler e : AusF V l Γ) := by
  have hneg : (inv σ ρ).2 ≠ false := by simp [hinv]
  simp only [traverseAusF, if_neg hneg, h]

/-- An `ok` element hands world and scope to the rest of the run. -/
theorem traverseAusF_kopf_ok
    (schrittF : World D → Env D (τ :: Γ) → AusF V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (k : Wert D τ) (ks : List (Wert D τ)) (σ σ' : World D) (ρ : Env D Γ)
    (ρ' : Env D (τ :: Γ))
    (hinv : (inv σ ρ).2 = true)
    (h : schrittF (inv σ ρ).1 (.cons k ρ) =
      (AusF.widen (.ok σ' ρ') : AusF V true (τ :: Γ))) :
    (traverseAusF schrittF inv (k :: ks) σ ρ : AusF V l Γ) =
      traverseAusF schrittF inv ks σ' ρ'.tail := by
  have hneg : (inv σ ρ).2 ≠ false := by simp [hinv]
  simp only [traverseAusF, if_neg hneg, h]

/-- A `next` element ends its pass and hands world and scope to the rest. -/
theorem traverseAusF_kopf_next
    (schrittF : World D → Env D (τ :: Γ) → AusF V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (k : Wert D τ) (ks : List (Wert D τ)) (σ σ' : World D) (ρ : Env D Γ)
    (ρ' : Env D (τ :: Γ))
    (hinv : (inv σ ρ).2 = true)
    (h : schrittF (inv σ ρ).1 (.cons k ρ) =
      (AusF.widen (.next rfl σ' ρ') : AusF V true (τ :: Γ))) :
    (traverseAusF schrittF inv (k :: ks) σ ρ : AusF V l Γ) =
      traverseAusF schrittF inv ks σ' ρ'.tail := by
  have hneg : (inv σ ρ).2 ≠ false := by simp [hinv]
  simp only [traverseAusF, if_neg hneg, h]

/-- A faulted rest faults the run -- past a fault-free head. -/
theorem traverseAusF_ok_rest_fehler
    (schrittF : World D → Env D (τ :: Γ) → AusF V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (k : Wert D τ) (ks : List (Wert D τ)) (σ σ' : World D) (ρ : Env D Γ)
    (ρ' : Env D (τ :: Γ)) (e : Fehlerklasse)
    (hinv : (inv σ ρ).2 = true)
    (h : schrittF (inv σ ρ).1 (.cons k ρ) =
      (AusF.widen (.ok σ' ρ') : AusF V true (τ :: Γ)))
    (hr : traverseAusF schrittF inv ks σ' ρ'.tail = (AusF.fehler e : AusF V l Γ)) :
    traverseAusF schrittF inv (k :: ks) σ ρ = (AusF.fehler e : AusF V l Γ) := by
  rw [traverseAusF_kopf_ok schrittF inv k ks σ σ' ρ ρ' hinv h, hr]

/-- Agreement end to end: a fault-free pass IS the `traverseLauf` pass -- the
    `traverseLauf` skeleton with the fault arm never taken (control, carried by
    `weiter`, not by the fault channel). -/
theorem traverseAusF_stimmt
    (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (schrittF : World D → Env D (τ :: Γ) → AusF V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (xs : List (Wert D τ)) (σ : World D) (ρ : Env D Γ)
    (h : ∀ σ ρ, ∃ o, schrittF σ ρ = AusF.widen o ∧ schritt σ ρ = o) :
    (traverseAusF schrittF inv xs σ ρ : AusF V l Γ) =
      AusF.vonAusgang (traverseLauf schritt inv xs σ ρ) := by
  induction xs generalizing σ ρ with
  | nil =>
      by_cases hg : (inv σ ρ).2 = true
      · simp only [traverseAusF, traverseLauf, AusF.vonAusgang, if_pos hg]
      · simp only [traverseAusF, traverseLauf, AusF.vonAusgang, if_neg hg]
  | cons k ks ih =>
      by_cases hg : (inv σ ρ).2 = false
      · simp only [traverseAusF, traverseLauf, AusF.vonAusgang, if_pos hg]
      · obtain ⟨o, ho1, ho2⟩ := h (inv σ ρ).1 (.cons k ρ)
        simp only [traverseAusF, traverseLauf, AusF.vonAusgang, if_neg hg, ho1, ho2]
        cases o with
        | ok σ' ρ' => exact ih _ _
        | zurueck σ' v => rfl
        | why σ' r => rfl
        | leave h' σ' ρ' =>
            by_cases hi : (inv σ' ρ'.tail).2 = true
            · simp only [if_pos hi]
            · simp only [if_neg hi]
        | next h' σ' ρ' => exact ih _ _
        | logik e => rfl
        | hardware e => rfl

/-- The `foreverLauf` shape with a fault arm: fuel bounds the run, a faulted
    pass faults it; every `Ausgang` arm continues exactly as `foreverLauf`
    does (`ok`/`next` recurse, `leave` answers `ok`, everything else stops). -/
def foreverAusF (a : D.Annahme) (schrittF : World D → Env D Γ → AusF V true Γ)
    (inv : World D → Env D Γ → World D × Bool) :
    Nat → World D → Env D Γ → AusF V l Γ
  | 0, _, _ => .widen (.hardware (.fortschritt a))
  | n + 1, σ, ρ =>
      if (inv σ ρ).2 = false then .widen (.logik .schleife)
      else match schrittF (inv σ ρ).1 ρ with
        | .fehler e => .fehler e
        | .widen (.ok σ' ρ') => foreverAusF a schrittF inv n σ' ρ'
        | .widen (.next _ σ' ρ') => foreverAusF a schrittF inv n σ' ρ'
        | .widen (.leave _ σ' ρ') => .widen (.ok σ' ρ')
        | .widen (.zurueck σ' v) => .widen (.zurueck σ' v)
        | .widen (.why σ' r) => .widen (.why σ' r)
        | .widen (.logik e) => .widen (.logik e)
        | .widen (.hardware e) => .widen (.hardware e)

/-- A faulted pass faults the fuel-bounded run -- in every pass. -/
theorem foreverAusF_kopf_fehler (a : D.Annahme)
    (schrittF : World D → Env D Γ → AusF V true Γ)
    (inv : World D → Env D Γ → World D × Bool)
    (n : Nat) (σ : World D) (ρ : Env D Γ) (e : Fehlerklasse)
    (hinv : (inv σ ρ).2 = true)
    (h : schrittF (inv σ ρ).1 ρ = (AusF.fehler e : AusF V true Γ)) :
    foreverAusF a schrittF inv (n + 1) σ ρ = (AusF.fehler e : AusF V l Γ) := by
  have hneg : (inv σ ρ).2 ≠ false := by simp [hinv]
  simp only [foreverAusF, if_neg hneg, h]

/-- A fault-free `ok` pass hands world and scope to the remaining fuel. -/
theorem foreverAusF_kopf_ok (a : D.Annahme)
    (schrittF : World D → Env D Γ → AusF V true Γ)
    (inv : World D → Env D Γ → World D × Bool)
    (n : Nat) (σ σ' : World D) (ρ ρ' : Env D Γ)
    (hinv : (inv σ ρ).2 = true)
    (h : schrittF (inv σ ρ).1 ρ = (AusF.widen (.ok σ' ρ') : AusF V true Γ)) :
    (foreverAusF a schrittF inv (n + 1) σ ρ : AusF V l Γ) =
      foreverAusF a schrittF inv n σ' ρ' := by
  have hneg : (inv σ ρ).2 ≠ false := by simp [hinv]
  simp only [foreverAusF, if_neg hneg, h]

#print axioms Gabbro.Grammatik.evalF
#print axioms Gabbro.Grammatik.evalF_ok
#print axioms Gabbro.Grammatik.evalF_stimmt
#print axioms Gabbro.Grammatik.indexFalleErgebnis
#print axioms Gabbro.Grammatik.fehlerFallErgebnis
#print axioms Gabbro.Grammatik.evalF_ok_halt
#print axioms Gabbro.Grammatik.evalF_stimmt_halt
#print axioms Gabbro.Grammatik.ErgebnisF.bind
#print axioms Gabbro.Grammatik.ErgebnisF.bind_fehler
#print axioms Gabbro.Grammatik.ErgebnisF.bind_wert
#print axioms Gabbro.Grammatik.ErgebnisF.map_fehler
#print axioms Gabbro.Grammatik.ErgebnisF.map_wert
#print axioms Gabbro.Grammatik.evalArgsMit
#print axioms Gabbro.Grammatik.evalArgsMit_kopf_fehler
#print axioms Gabbro.Grammatik.evalArgsMit_rest_fehler
#print axioms Gabbro.Grammatik.evalArgsMit_ok
#print axioms Gabbro.Grammatik.evalArgsF
#print axioms Gabbro.Grammatik.evalArgsF_ok
#print axioms Gabbro.Grammatik.AusF.folge
#print axioms Gabbro.Grammatik.AusF.folge_fehler
#print axioms Gabbro.Grammatik.AusF.folge_ok
#print axioms Gabbro.Grammatik.AusF.folge_logik
#print axioms Gabbro.Grammatik.AusF.folge_hardware
#print axioms Gabbro.Grammatik.schrittFolge
#print axioms Gabbro.Grammatik.schrittFolge_vorn
#print axioms Gabbro.Grammatik.schrittFolge_hinten
#print axioms Gabbro.Grammatik.schleifeF
#print axioms Gabbro.Grammatik.schleifeF_fehler
#print axioms Gabbro.Grammatik.schleifeF_spaeter
#print axioms Gabbro.Grammatik.durchlaufF
#print axioms Gabbro.Grammatik.durchlaufF_kopf
#print axioms Gabbro.Grammatik.durchlaufF_rest
#print axioms Gabbro.Grammatik.endZustandF
#print axioms Gabbro.Grammatik.endZustandF_fehler
#print axioms Gabbro.Grammatik.endZustandF_logik
#print axioms Gabbro.Grammatik.endZustandF_hardware
#print axioms Gabbro.Grammatik.endZustandF_ok
#print axioms Gabbro.Grammatik.IstBenannt
#print axioms Gabbro.Grammatik.fehler_ist_benannt
#print axioms Gabbro.Grammatik.logik_ist_benannt
#print axioms Gabbro.Grammatik.hardware_ist_benannt
#print axioms Gabbro.Grammatik.folge_benannt_bleibt
#print axioms Gabbro.Grammatik.ausF_klassifikation
#print axioms Gabbro.Grammatik.AusF.vonAusgang
#print axioms Gabbro.Grammatik.AusF.zuAusgang
#print axioms Gabbro.Grammatik.AusF.zuAusgang_vonAusgang
#print axioms Gabbro.Grammatik.AusF.zuAusgang_fehler
#print axioms Gabbro.Grammatik.AusF.folge_weiter
#print axioms Gabbro.Grammatik.AusF.folge_zurueck
#print axioms Gabbro.Grammatik.AusF.folge_grund
#print axioms Gabbro.Grammatik.AusF.folge_leave
#print axioms Gabbro.Grammatik.AusF.folge_next
#print axioms Gabbro.Grammatik.IstStecken
#print axioms Gabbro.Grammatik.stecken_heisst_benannt
#print axioms Gabbro.Grammatik.benannt_heisst_stecken
#print axioms Gabbro.Grammatik.stecken_klassifikation
#print axioms Gabbro.Grammatik.evalArgsMit_stimmt
#print axioms Gabbro.Grammatik.evalArgsF_stimmt
#print axioms Gabbro.Grammatik.schrittRein
#print axioms Gabbro.Grammatik.schrittFolge_rein
#print axioms Gabbro.Grammatik.durchlaufRein
#print axioms Gabbro.Grammatik.durchlaufF_rein
#print axioms Gabbro.Grammatik.schleifeF_als_folge
#print axioms Gabbro.Grammatik.endZustandF_zurueck
#print axioms Gabbro.Grammatik.endZustandF_grund
#print axioms Gabbro.Grammatik.endZustandF_leave
#print axioms Gabbro.Grammatik.endZustandF_next
#print axioms Gabbro.Grammatik.blockF
#print axioms Gabbro.Grammatik.blockF_nil
#print axioms Gabbro.Grammatik.blockF_cons_fehler
#print axioms Gabbro.Grammatik.blockF_cons_ok
#print axioms Gabbro.Grammatik.blockF_cons_weiter
#print axioms Gabbro.Grammatik.blockF_cons_fehler_benannt
#print axioms Gabbro.Grammatik.traverseAusF
#print axioms Gabbro.Grammatik.traverseAusF_kopf_fehler
#print axioms Gabbro.Grammatik.traverseAusF_kopf_ok
#print axioms Gabbro.Grammatik.traverseAusF_kopf_next
#print axioms Gabbro.Grammatik.traverseAusF_ok_rest_fehler
#print axioms Gabbro.Grammatik.traverseAusF_stimmt
#print axioms Gabbro.Grammatik.foreverAusF
#print axioms Gabbro.Grammatik.foreverAusF_kopf_fehler
#print axioms Gabbro.Grammatik.foreverAusF_kopf_ok


end Gabbro.Grammatik
