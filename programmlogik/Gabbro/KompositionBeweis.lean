/-
  Gabbro -- program COMPOSITION: from checked bodies to `UmgebungOK` and `SchleifenOK`.

  `Sicherheit.lean` books this file as its step 2: `(U1)` and `(U2)` are the same safety
  theorem one level down -- for the callee's body and for the loop's iteration -- and
  closing them from `Runs`/`RunsLoop` plus `pruefeBlock_sicher` is the program theorem.
  That closure stands here, and nowhere else.

  WHAT IS PROVED (0 `sorry`, 0 `admit`, 0 new axioms; `import Mathlib` arrives only
  transitively through `Sicherheit.Anweisung`, this file uses no Mathlib lemma):
    * `ergebnis_of_geprueft` -- the bridge both halves walk over: a checked body that
      does not stop at own logic ends in `Ergebnis` (directly from `pruefeBlock_sicher`).
    * `schleifen_ok_of_runsloop` / `schleifen_ok_of_runsloop_in` -- a registered loop
      whose body is checked, whose environment runs its passes (`RunsLoop` /
      `RunsLoopIn`), and whose passes stop at no own logic, keeps world and scope:
      the `SchleifenOK` conjunct, by induction over the `iterate` index list, in the
      shape of `Body.looprule_of_body` (`_in`).
    * `umgebung_ok_of_runs_azyklisch` -- acyclic routines: topological induction over an
      explicit rank. Each duty may assume the contracts of the callees it names
      (`ruftAuf`); the induction discharges them in rank order through
      `Body.contract_of_duty` (the step `Coverage` books as `contractFromDuty`).
    * `vertrag_zyklus_of_pflichten` -- cyclic routines: `Coverage.recursion_cycle_carried`
      applied as stated, so the duty shape here IS the Coverage shape (`ContractBelowM`
      over the `decreases` measure, one induction for cycles of every size).
    * `umgebung_ok_of_runs` -- the cyclic corollary: cycle contracts with the canonical
      pre/post (`Welt` in, `Welt` plus the signature's answer out) fold to `UmgebungOK`.
    * `umgebung_ok_of_vertrag` -- the shared fold both composition theorems end in.

  ASSUMED (as premises of the theorems, never as axioms):
    (F) Foreign bodies (`extern`, `asm`, `entrust`) stay hypotheses: `Fremd` marks the
        names with no body in the list, `hFremd` is their `UmgebungOK` conjuncts taken
        as a premise. A foreign body is refused by the emitter (`foreign-body`) for the
        same reason it is assumed here: there is no body to run a duty over.
    (D) `DivergenzOK` (no declared callee diverges -- `Sicherheit`'s U5).

  CUTS -- places where the file shrinks instead of faking, booked here and not in a
  commit message:
    (C1) Routine duties are total over `Welt`-only entry states. Discharging one from a
         checked body needs `WFU (paramUmgebung S.params)` at entry, which only call
         sites provide (`argumente_sicher`); the per-unit duty proof keeps that as an
         explicit hypothesis. The composition assumes the duty, like `Coverage`'s
         carried lemmas assume theirs.
    (C2) A body that falls off the end (`running`, `finalValue = none`) against a
         declared result (`S.ergebnis = some`) meets no duty: the duty fails rather
         than a value being invented. A missing `return` stays loud.
    (C3) The acyclic rank comes from the checker's call-graph order; the emitter
         instantiates the wiring per unit in that order (`Body.lean` section 5.1 tells
         the same story for `contract_of_duty`/`looprule_of_body`). No call-graph
         datatype stands in the model, so sortedness is a premise, not a computation.
    (C4) Cycles close supply-at-a-time: a cycle member's duty may assume only the
         bounded intra-cycle contracts plus foreign posts. A call to a defined
         outside-cycle routine enters as foreign for that invocation (SCC condensation
         is the emitter's order, as in C3).
    (C5) Only `RunsLoop`/`RunsLoopIn` are closed; the counted `RunsLoopN` variant is
         not (its pass premise carries the ghost counter -- a second induction that
         would shadow `looprule_passes_aux` instead of reusing an idea).
    (C6) The loop theorems take `UmgebungOK`/`SchleifenOK` as premises for the nested
         constructs of the body -- the same shape as `pruefe_sicher` itself, which
         concludes `Ergebnis` under those hypotheses. Same-id nesting is excluded by
         emitter-fresh loop ids.
    (C7) The loop variable is fresh in the registered scope (`such ΔS v = none`); the
         emitter guarantees it, the induction needs it (`wfu_bindLocal_frisch`).
    (C8) Wiring into `Gabbro.lean` is a follow-up: this file is checked standalone
         (`lake env lean`) and must not edit outside itself.

  LAYERING -- how the pieces meet: `umgebung_ok_of_runs*` discharge (U1) from duties;
  `schleifen_ok_of_runsloop*` reduce (U2) to per-pass no-logic duties under (U1)/(U2)
  for nested constructs (C6); `exec_sicher` consumes both. The person's own logic is
  never discharged here: it is the `¬ LogikB` / duty premises, in the open, per unit.
-/
import Gabbro.Body
import Gabbro.Coverage
import Gabbro.Sicherheit.Anweisung

namespace Gabbro.Komposition

open Gabbro.Body
open Gabbro.Sicherheit

/-! ## 1. The bridge both halves walk over -/

/-- **A checked body that stops at no own logic ends in `Ergebnis`.** This is
    `pruefeBlock_sicher` with the disjunction resolved: the `¬ LogikB` premise is the
    person's half (their `requires` hold, their invariants hold on entry), the
    `Ergebnis` conclusion is everything else. Routine duties (section 3) are discharged
    through this lemma per unit; the loop induction (section 2) applies it per pass. -/
theorem ergebnis_of_geprueft (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ)
    (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape)
    (b : List Stmt) (Δ Δ' : Umgebung) (s : State)
    (hcheck : pruefeBlock P erg Δ b = some Δ') (hw : Welt P.D Γ s.world)
    (hl : WFU Δ s.local') (hlogik : ¬ LogikB ρ b s) :
    Ergebnis P Γ erg Δ Δ' (exec ρ b s) := by
  rcases pruefeBlock_sicher P Γ ρ hD hU hS erg b Δ Δ' s hcheck hw hl with hr | hlog
  · exact hr
  · exact absurd hlog hlogik

/-- **A fresh name stays out of the scope's way.** The loop variable `v` is not
    registered in `ΔS` (C7: the emitter guarantees it), so binding it keeps `WFU ΔS`. -/
theorem wfu_bindLocal_frisch (ΔS : Umgebung) (v : String) (β : Binding) (w : Value)
    (hf : such ΔS v = none) (hl : WFU ΔS β) : WFU ΔS (bindLocal β v w) := by
  intro m g hm
  by_cases hmv : m = v
  · subst hmv; rw [hf] at hm; cases hm
  · simpa [bindLocal, hmv] using hl m g hm

/-! ## 2. Loops -- `SchleifenOK` from `RunsLoop`, by induction over the passes -/

/-- A checked loop body: its specification bundle. `erg` is the result shape of the
    routine the loop stands in; `ΔS` is the scope the checker registered for the loop
    (`P.schleife id = some ΔS`), under which the body is checked. -/
structure Schleife where
  id : String
  ΔS : Umgebung
  body : List Stmt
  v : String
  erg : Option Shape

/-- A checked loop body over a ranged domain: the same, with the index range the pass
    may assume (`RunsLoopIn`: every visited index lies in `lo ≤ k < hi`). -/
structure SchleifeIn where
  id : String
  ΔS : Umgebung
  body : List Stmt
  v : String
  erg : Option Shape
  lo : Int
  hi : Int

/-- **One pass of a checked body preserves world and scope.** From the bridge plus an
    outcome analysis: `running` ends under the strengthened scope (weakened back with
    `pruefeBlock_erweitert`), every other non-stuck outcome carries the entry scope by
    construction of `Ergebnis`, and `stuck` is `False`. -/
theorem schleife_pass (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ)
    (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ)
    (ΔS : Umgebung) (body : List Stmt) (v : String) (erg : Option Shape)
    (hcheck : ∃ Δ', pruefeBlock P erg ΔS body = some Δ')
    (hfrisch : such ΔS v = none)
    (t : State) (k : Int) (hw : Welt P.D Γ t.world) (hl : WFU ΔS t.local')
    (hnologik : ¬ LogikB ρ body { t with local' := bindLocal t.local' v (.int k) }) :
    ∃ u', finalState (exec ρ body { t with local' := bindLocal t.local' v (.int k) })
        = some u' ∧ Welt P.D Γ u'.world ∧ WFU ΔS u'.local' := by
  obtain ⟨Δ', hcheck'⟩ := hcheck
  have hlv : WFU ΔS (bindLocal t.local' v (.int k)) :=
    wfu_bindLocal_frisch ΔS v t.local' (.int k) hfrisch hl
  rcases ergebnis_of_geprueft P Γ ρ hD hU hS erg body ΔS Δ'
      { t with local' := bindLocal t.local' v (.int k) } hcheck' hw hlv hnologik with hr
  have hext : erweitert ΔS Δ' := pruefeBlock_erweitert P erg body ΔS Δ' hcheck'
  cases ho : exec ρ body { t with local' := bindLocal t.local' v (.int k) } with
  | running u' =>
      rw [ho] at hr; simp only [Ergebnis] at hr
      exact ⟨u', rfl, hr.1, WFU_erweitert hext hr.2⟩
  | returned u' _ =>
      rw [ho] at hr; simp only [Ergebnis] at hr
      exact ⟨u', rfl, hr.1, hr.2.1⟩
  | exited u' =>
      rw [ho] at hr; simp only [Ergebnis] at hr
      exact ⟨u', rfl, hr.1, hr.2⟩
  | left u' =>
      rw [ho] at hr; simp only [Ergebnis] at hr
      exact ⟨u', rfl, hr.1, hr.2⟩
  | stuck =>
      rw [ho] at hr; simp only [Ergebnis] at hr

/-- **The induction over the passes**, in the shape of `Body.looprule_of_body`: each
    pass ends by falling off, `next`, or `leave` (a fourth outcome contradicts the
    `iterate = some` the environment stands on), and world plus scope travel along. -/
theorem schleife_haelt (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ)
    (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ)
    (l : Schleife)
    (hcheck : ∃ Δ', pruefeBlock P l.erg l.ΔS l.body = some Δ')
    (hruns : RunsLoop ρ l.id l.body l.v)
    (hfrisch : such l.ΔS l.v = none)
    (hnologik : ∀ (t : State) (k : Int), Welt P.D Γ t.world → WFU l.ΔS t.local' →
      ¬ LogikB ρ l.body { t with local' := bindLocal t.local' l.v (.int k) })
    (t : State) (hw : Welt P.D Γ t.world) (hl : WFU l.ΔS t.local') :
    Welt P.D Γ (ρ l.id t).1.world ∧ WFU l.ΔS (ρ l.id t).1.local' := by
  obtain ⟨ks, t', hit, heq⟩ := hruns t
  rw [heq]
  clear heq
  induction ks generalizing t with
  | nil => simp [iterate] at hit; subst hit; exact ⟨hw, hl⟩
  | cons k ks ih =>
      obtain ⟨u', hu', hwf, hlf⟩ :=
        schleife_pass P Γ ρ hD hU hS l.ΔS l.body l.v l.erg hcheck hfrisch t k hw hl
          (hnologik t k hw hl)
      simp only [iterate] at hit
      split at hit
      · rename_i u hu
        rw [hu] at hu'; simp [finalState] at hu'; subst hu'
        exact ih u hwf hlf hit
      · rename_i u hu
        rw [hu] at hu'; simp [finalState] at hu'; subst hu'
        exact ih u hwf hlf hit
      · rename_i u hu
        rw [hu] at hu'; simp [finalState] at hu'; subst hu'
        simp at hit; subst hit; exact ⟨hwf, hlf⟩
      · exact absurd hit (by simp)

/-- **The induction over the passes of a ranged domain**, in the shape of
    `Body.looprule_of_body_in`: the pass may assume its index in range, and the range
    travels with the index list. -/
theorem schleife_haelt_in (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ)
    (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ)
    (l : SchleifeIn)
    (hcheck : ∃ Δ', pruefeBlock P l.erg l.ΔS l.body = some Δ')
    (hruns : RunsLoopIn ρ l.id l.body l.v l.lo l.hi)
    (hfrisch : such l.ΔS l.v = none)
    (hnologik : ∀ (t : State) (k : Int), l.lo ≤ k → k < l.hi → Welt P.D Γ t.world → WFU l.ΔS t.local' →
      ¬ LogikB ρ l.body { t with local' := bindLocal t.local' l.v (.int k) })
    (t : State) (hw : Welt P.D Γ t.world) (hl : WFU l.ΔS t.local') :
    Welt P.D Γ (ρ l.id t).1.world ∧ WFU l.ΔS (ρ l.id t).1.local' := by
  obtain ⟨ks, t', hks, hit, heq⟩ := hruns t
  rw [heq]
  clear heq
  induction ks generalizing t with
  | nil => simp [iterate] at hit; subst hit; exact ⟨hw, hl⟩
  | cons k ks ih =>
      have hk : l.lo ≤ k ∧ k < l.hi := hks k (by simp)
      have hks' : ∀ k' ∈ ks, l.lo ≤ k' ∧ k' < l.hi :=
        fun k' hk' => hks k' (by simp [hk'])
      obtain ⟨u', hu', hwf, hlf⟩ :=
        schleife_pass P Γ ρ hD hU hS l.ΔS l.body l.v l.erg hcheck hfrisch t k hw hl
          (hnologik t k hk.1 hk.2 hw hl)
      simp only [iterate] at hit
      split at hit
      · rename_i u hu
        rw [hu] at hu'; simp [finalState] at hu'; subst hu'
        exact ih u hwf hlf hks' hit
      · rename_i u hu
        rw [hu] at hu'; simp [finalState] at hu'; subst hu'
        exact ih u hwf hlf hks' hit
      · rename_i u hu
        rw [hu] at hu'; simp [finalState] at hu'; subst hu'
        simp at hit; subst hit; exact ⟨hwf, hlf⟩
      · exact absurd hit (by simp)

/-- **Every registered loop keeps world and scope: `SchleifenOK` from `RunsLoop`.**
    Loops are never foreign -- every registered loop has its body in the list (`halle`:
    the program is closed over loops) -- so the fold needs no foreign hypothesis, only
    the per-loop bundle: checked, run by the environment, fresh variable, no own-logic
    stop per pass. -/
theorem schleifen_ok_of_runsloop (P : Programm) (Γ : Typing) (ρ : Env)
    (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ)
    (loops : List Schleife)
    (halle : ∀ id Δ, P.schleife id = some Δ → ∃ l ∈ loops, l.id = id ∧ l.ΔS = Δ)
    (hloop : ∀ l ∈ loops, (∃ Δ', pruefeBlock P l.erg l.ΔS l.body = some Δ')
      ∧ RunsLoop ρ l.id l.body l.v ∧ such l.ΔS l.v = none
      ∧ (∀ (t : State) (k : Int), Welt P.D Γ t.world → WFU l.ΔS t.local' →
          ¬ LogikB ρ l.body { t with local' := bindLocal t.local' l.v (.int k) })) :
    SchleifenOK P Γ ρ := by
  intro id Δ hreg t hw hl
  obtain ⟨l, hlmem, hid, hΔ⟩ := halle id Δ hreg
  subst hid; subst hΔ
  obtain ⟨hcheck, hruns, hfrisch, hnologik⟩ := hloop l hlmem
  exact schleife_haelt P Γ ρ hD hU hS l hcheck hruns hfrisch hnologik t hw hl

/-- **The same over ranged domains: `SchleifenOK` from `RunsLoopIn`.** -/
theorem schleifen_ok_of_runsloop_in (P : Programm) (Γ : Typing) (ρ : Env)
    (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ)
    (loops : List SchleifeIn)
    (halle : ∀ id Δ, P.schleife id = some Δ → ∃ l ∈ loops, l.id = id ∧ l.ΔS = Δ)
    (hloop : ∀ l ∈ loops, (∃ Δ', pruefeBlock P l.erg l.ΔS l.body = some Δ')
      ∧ RunsLoopIn ρ l.id l.body l.v l.lo l.hi ∧ such l.ΔS l.v = none
      ∧ (∀ (t : State) (k : Int), l.lo ≤ k → k < l.hi → Welt P.D Γ t.world → WFU l.ΔS t.local' →
          ¬ LogikB ρ l.body { t with local' := bindLocal t.local' l.v (.int k) })) :
    SchleifenOK P Γ ρ := by
  intro id Δ hreg t hw hl
  obtain ⟨l, hlmem, hid, hΔ⟩ := halle id Δ hreg
  subst hid; subst hΔ
  obtain ⟨hcheck, hruns, hfrisch, hnologik⟩ := hloop l hlmem
  exact schleife_haelt_in P Γ ρ hD hU hS l hcheck hruns hfrisch hnologik t hw hl

/-! ## 3. Routines -- `UmgebungOK` from `Runs`, acyclic and cyclic -/

/-- A defined routine: its body, its signature, and its `decreases` measure. The
    result shape and the error channel travel inside `S` (`S.ergebnis`, `S.gruende`),
    so the post below needs no further fields. -/
structure Routine where
  name : String
  body : List Stmt
  S : Signatur
  mass : Expr

/-- **The answer half of `UmgebungOK`, word for word.** `NachPost S r` is the match
    `UmgebungOK` makes on `S.ergebnis`; it is stated once here so the fold
    (`umgebung_ok_of_vertrag`) holds by construction rather than by case analysis. -/
def NachPost (S : Signatur) (r : Option Value) : Prop :=
  match S.ergebnis with
  | some sh => ∃ v, r = some v ∧ (v.hasShape sh = true ∨ ∃ q, q ∈ S.gruende ∧ v = .reason q)
  | none => r = none ∨ ∃ q, q ∈ S.gruende ∧ r = some (.reason q)

/-- **The contract of a defined routine**: a well-formed world in, a well-formed world
    plus the signature's answer out. The entry scope carries no hypothesis (C1). -/
def Nach (P : Programm) (Γ : Typing) (S : Signatur) :
    State → State → Option Value → Prop :=
  fun _ t' r => Welt P.D Γ t'.world ∧ NachPost S r

/-- A routine as a `Body.Member`: the canonical pre/post, so the cyclic theorem below
    applies `Coverage.recursion_cycle_carried` without restating its duty shape. -/
def Routine.toMember (P : Programm) (Γ : Typing) (r : Routine) : Member :=
  { name := r.name, body := r.body, pre := fun t => Welt P.D Γ t.world,
    post := Nach P Γ r.S, measure := r.mass }

/- **Who a body calls.** Every call form (`call`, `bindCall`, `bindCallElse`,
    `retCall`), through every sub-block (branches, arms, loop bodies, error exits,
    locked and breaking bodies). Stores, publishes, returns and exits call nothing.
    The acyclic sortedness premise (`hsort`) is stated over this relation.

    A mutual block on purpose: the sub-blocks are nested inside the statement, not
    structural subterms of the statement LIST, so a single recursion over lists does
    not terminate-check. -/
mutual
def ruftAuf : List Stmt → String → Prop
  | [], _ => False
  | a :: rest, f => ruftAufStmt a f ∨ ruftAuf rest f
def ruftAufStmt : Stmt → String → Prop
  | .call g _ _ _, f => g = f
  | .bindCall _ g _ _ _, f => g = f
  | .bindCallElse _ g _ _ _ _ onErr, f => g = f ∨ ruftAuf onErr f
  | .retCall g _ _ _, f => g = f
  | .ite _ t e, f => ruftAuf t f ∨ ruftAuf e f
  | .onOption _ _ p a, f => ruftAuf p f ∨ ruftAuf a f
  | .onReason _ arms, f => ruftAufArme arms f
  | .onTag _ arms, f => ruftAufTArme arms f
  | .loop _ _ b, f => ruftAuf b f
  | .locked _ b, f => ruftAuf b f
  | .breaking _ b, f => ruftAuf b f
  | _, _ => False
def ruftAufArme : List (String × List Stmt) → String → Prop
  | [], _ => False
  | (_, b) :: rest, f => ruftAuf b f ∨ ruftAufArme rest f
def ruftAufTArme : List (String × Option String × List Stmt) → String → Prop
  | [], _ => False
  | (_, _, b) :: rest, f => ruftAuf b f ∨ ruftAufTArme rest f
end

/-- **What a duty may assume about a callee `g`**: either `g` is defined earlier in
    rank order with its canonical contract, or `g` is foreign (F) and its post is the
    ambient foreign hypothesis. -/
def Erfuellt (rs : List Routine) (ρ : Env) (P : Programm) (Γ : Typing)
    (Fremd : String → Prop) (g : String) : Prop :=
  (∃ r' ∈ rs, r'.name = g ∧
    Contract ρ g (fun t => Welt P.D Γ t.world) (Nach P Γ r'.S)) ∨ Fremd g

/-- **The acyclic step**: a duty proved over the body IS the contract. This is
    `Body.contract_of_duty` -- the step `Coverage` books as `contractFromDuty` -- with
    the canonical pre/post filled in. The topological ORDER lives in
    `umgebung_ok_of_runs_azyklisch`; this lemma is its single step. -/
theorem vertrag_einzeln_of_pflicht (ρ : Env) (P : Programm) (Γ : Typing) (r : Routine)
    (hruns : Runs ρ r.name r.body)
    (hduty : ∀ (t : State), Welt P.D Γ t.world →
      ∃ s', finalState (exec ρ r.body t) = some s' ∧
        Nach P Γ r.S t s' (finalValue (exec ρ r.body t))) :
    Contract ρ r.name (fun t => Welt P.D Γ t.world) (Nach P Γ r.S) :=
  contract_of_duty ρ r.name r.body _ _ hruns hduty

/-- **The shared fold**: canonical contracts for the defined routines, plus the foreign
    hypothesis (F) and `DivergenzOK` (D), are `UmgebungOK`. The defined case is the
    contract at a well-formed world; the foreign case is the hypothesis. -/
theorem umgebung_ok_of_vertrag (P : Programm) (Γ : Typing) (ρ : Env)
    (rs : List Routine) (Fremd : String → Prop)
    (hcon : ∀ r ∈ rs, Contract ρ r.name (fun t => Welt P.D Γ t.world) (Nach P Γ r.S))
    (hdef : ∀ f S, P.sig f = some S → (∃ r ∈ rs, r.name = f ∧ r.S = S) ∨ Fremd f)
    (hFremd : ∀ g, Fremd g → ∀ S, P.sig g = some S → ∀ (t : State), Welt P.D Γ t.world →
      Welt P.D Γ (ρ g t).1.world ∧ NachPost S (ρ g t).2)
    (hDiv : DivergenzOK P.sig) :
    UmgebungOK P Γ ρ := by
  intro f S hsig t hw
  rcases hdef f S hsig with ⟨r, hr, hname, hS⟩ | hfr
  · subst hname; subst hS
    obtain ⟨hw', ha⟩ := hcon r hr t hw
    exact ⟨hw', ha, hDiv⟩
  · obtain ⟨hw', ha⟩ := hFremd f hfr S hsig t hw
    exact ⟨hw', ha, hDiv⟩

/-- **Acyclic routines: topological induction over an explicit rank.** Each duty may
    assume the canonical contracts of the callees it names; sortedness (`hsort`) says
    every named callee is either defined at smaller rank or foreign. The induction is
    over the rank bound -- the `Nat` induction of `Body.contract_of_duty_rec`'s `key`,
    with the measure replaced by the topological rank. (C3: the rank itself is the
    checker's call-graph order, instantiated per unit.) -/
theorem umgebung_ok_of_runs_azyklisch (P : Programm) (Γ : Typing) (ρ : Env)
    (rs : List Routine) (Fremd : String → Prop) (rank : String → Nat)
    (hsort : ∀ r ∈ rs, ∀ g, ruftAuf r.body g →
      (∃ r' ∈ rs, r'.name = g ∧ rank g < rank r.name) ∨ Fremd g)
    (hrs : ∀ r ∈ rs, Runs ρ r.name r.body)
    (hduty : ∀ r ∈ rs, ∀ (t : State), Welt P.D Γ t.world →
      (∀ g, ruftAuf r.body g → Erfuellt rs ρ P Γ Fremd g) →
      ∃ s', finalState (exec ρ r.body t) = some s' ∧
        Nach P Γ r.S t s' (finalValue (exec ρ r.body t)))
    (hdef : ∀ f S, P.sig f = some S → (∃ r ∈ rs, r.name = f ∧ r.S = S) ∨ Fremd f)
    (hFremd : ∀ g, Fremd g → ∀ S, P.sig g = some S → ∀ (t : State), Welt P.D Γ t.world →
      Welt P.D Γ (ρ g t).1.world ∧ NachPost S (ρ g t).2)
    (hDiv : DivergenzOK P.sig) :
    UmgebungOK P Γ ρ := by
  have key : ∀ (n : Nat) (r : Routine), r ∈ rs → rank r.name < n →
      Contract ρ r.name (fun t => Welt P.D Γ t.world) (Nach P Γ r.S) := by
    intro n
    induction n with
    | zero => intro r _ h; omega
    | succ n ih =>
        intro r hr hlt
        apply contract_of_duty ρ r.name r.body (fun t => Welt P.D Γ t.world)
          (Nach P Γ r.S) (hrs r hr)
        intro t ht
        exact hduty r hr t ht (fun g hg => by
          rcases hsort r hr g hg with ⟨r', hr', hname, hlt'⟩ | hfr
          · left
            have hlt'' : rank r'.name < n := by rw [hname]; omega
            refine ⟨r', hr', hname, ?_⟩
            rw [← hname]
            exact ih r' hr' hlt''
          · right; exact hfr)
  apply umgebung_ok_of_vertrag P Γ ρ rs Fremd _ hdef hFremd hDiv
  intro r hr
  exact key (rank r.name + 1) r hr (by omega)

/-- **Cyclic routines at `Member` level: `Coverage.recursion_cycle_carried`, applied as
    stated.** Each member meeting its duty under the bounded contracts of the cycle
    (`ContractBelowM` over the `decreases` measure -- the `Below` induction) IS every
    contract of the cycle. This theorem names the reuse; `umgebung_ok_of_runs` folds it
    to `UmgebungOK`. -/
theorem vertrag_zyklus_of_pflichten (ρ : Env) (rs : List Member)
    (hr : ∀ r ∈ rs, Runs ρ r.name r.body)
    (hd : ∀ r ∈ rs, ∀ (t : State), r.pre t → (∀ r' ∈ rs, ContractBelowM ρ r' r.measure t) →
      ∃ s', finalState (exec ρ r.body t) = some s' ∧
        r.post t s' (finalValue (exec ρ r.body t))) :
    ∀ r ∈ rs, Contract ρ r.name r.pre r.post :=
  Gabbro.Coverage.recursion_cycle_carried ρ rs hr hd

/-- **Cyclic routines: measure induction to contracts, contracts to `UmgebungOK`.**
    The duties assume only the bounded intra-cycle contracts (plus the ambient foreign
    hypothesis, C4); `Coverage.recursion_cycle_carried` lifts them to full contracts
    over the mapped `Member` list, and the shared fold concludes. -/
theorem umgebung_ok_of_runs (P : Programm) (Γ : Typing) (ρ : Env)
    (rs : List Routine) (Fremd : String → Prop)
    (hrs : ∀ r ∈ rs, Runs ρ r.name r.body)
    (hduty : ∀ r ∈ rs, ∀ (t : State), Welt P.D Γ t.world →
      (∀ r' ∈ rs, ContractBelowM ρ (Routine.toMember P Γ r') r.mass t) →
      (∀ g, Fremd g → ∀ S, P.sig g = some S → ∀ u, Welt P.D Γ u.world →
        Welt P.D Γ (ρ g u).1.world ∧ NachPost S (ρ g u).2) →
      ∃ s', finalState (exec ρ r.body t) = some s' ∧
        Nach P Γ r.S t s' (finalValue (exec ρ r.body t)))
    (hdef : ∀ f S, P.sig f = some S → (∃ r ∈ rs, r.name = f ∧ r.S = S) ∨ Fremd f)
    (hFremd : ∀ g, Fremd g → ∀ S, P.sig g = some S → ∀ (t : State), Welt P.D Γ t.world →
      Welt P.D Γ (ρ g t).1.world ∧ NachPost S (ρ g t).2)
    (hDiv : DivergenzOK P.sig) :
    UmgebungOK P Γ ρ := by
  have hr' : ∀ r ∈ rs.map (Routine.toMember P Γ), Runs ρ r.name r.body := by
    intro m hm
    obtain ⟨r0, hr0, hEq⟩ := List.mem_map.mp hm
    subst hEq
    exact hrs r0 hr0
  have hd' : ∀ (m : Member), m ∈ rs.map (Routine.toMember P Γ) → ∀ (t : State),
      m.pre t →
      (∀ m' ∈ rs.map (Routine.toMember P Γ), ContractBelowM ρ m' m.measure t) →
      ∃ s', finalState (exec ρ m.body t) = some s' ∧
        m.post t s' (finalValue (exec ρ m.body t)) := by
    intro m hm t ht hcb
    obtain ⟨r0, hr0, hEq⟩ := List.mem_map.mp hm
    subst hEq
    exact hduty r0 hr0 t ht
      (fun r' hr' => hcb (Routine.toMember P Γ r')
        (List.mem_map.mpr ⟨r', hr', rfl⟩)) hFremd
  have hcon := vertrag_zyklus_of_pflichten ρ (rs.map (Routine.toMember P Γ)) hr' hd'
  apply umgebung_ok_of_vertrag P Γ ρ rs Fremd _ hdef hFremd hDiv
  intro r hr
  exact hcon (Routine.toMember P Γ r) (List.mem_map.mpr ⟨r, hr, rfl⟩)

/-! ## 4. The axioms -- derived, not asserted -/

#print axioms Gabbro.Komposition.ergebnis_of_geprueft
#print axioms Gabbro.Komposition.schleifen_ok_of_runsloop
#print axioms Gabbro.Komposition.schleifen_ok_of_runsloop_in
#print axioms Gabbro.Komposition.umgebung_ok_of_runs_azyklisch
#print axioms Gabbro.Komposition.vertrag_zyklus_of_pflichten
#print axioms Gabbro.Komposition.umgebung_ok_of_runs

end Gabbro.Komposition
