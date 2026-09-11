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
    * Section 5 closes the S2 cuts (C1-C4) per unit and to minimal form:
      `wfu_eintritt_of_argumente` (C1 call-site half),
      `pflicht_of_geprueft_oder_fehlend` with `nachpost_of_antwortpasst`,
      `nachpost_none_of_kein_ergebnis`, `pflicht_scheitert_ohne_wert` (C1 duty half
      and C2 missing-return failure), `vertrag_blatt_of_pflicht` (C3 rank discharged
      for leaves), `umgebung_ok_kette_of_vertraege` (C3/C4 SCC-at-a-time composition),
      `umgebung_ok_of_runs_zyklus_min` (C4 foreign narrowed to called names),
      `umgebung_antwort_of_vertrag` / `umgebung_ok_of_antwort` (D split to minimal
      passthrough). Residuals are exact and stand in the C-cuts below.

  ASSUMED (as premises of the theorems, never as axioms):
    (F) Foreign bodies (`extern`, `asm`, `entrust`) stay hypotheses: `Fremd` marks the
        names with no body in the list, `hFremd` is their `UmgebungOK` conjuncts taken
        as a premise. Minimal form (§5): the fold queries only declared foreigners
        (`P.sig g = some S` rides along); cycle duties assume foreign posts only for
        the names the body calls (`ruftAuf r.body g`). A foreign body is refused by
        the emitter (`foreign-body`) for the same reason it is assumed here: there is
        no body to run a duty over.
    (D) `DivergenzOK` (no declared callee diverges -- `Sicherheit`'s U5). Minimal form
        (§5): it is a pure passthrough -- `umgebung_antwort_of_vertrag` derives world
        plus answer without it, and `umgebung_ok_of_antwort` adds exactly this
        conjunct. It is used nowhere else in the fold.

  CUTS -- places where the file shrinks instead of faking, booked here and not in a
  commit message:
    (C1) CLOSED per unit (§5). Discharging a duty from a checked body needs
         `WFU (paramUmgebung S.params)` at entry, which only call sites provide
         (`argumente_sicher`); `wfu_eintritt_of_argumente` names exactly that
         call-site half, and `pflicht_of_geprueft_oder_fehlend` keeps the entry `WFU`
         as an explicit duty premise. Exact residual: the entry `WFU` (provided per
         call by the caller, never invented here) and the person's `¬ LogikB`.
    (C2) CLOSED (§5). A body that falls off the end (`running`, `finalValue = none`)
         against a declared result (`S.ergebnis = some`) meets no duty:
         `pflicht_scheitert_ohne_wert` proves `¬ Nach` from `finalValue = none`, so
         the duty fails rather than a value being invented. `NachPost` without a
         declared result holds of `none` (`nachpost_none_of_kein_ergebnis`); a
         missing `return` stays loud as the right disjunct of
         `pflicht_of_geprueft_oder_fehlend`.
    (C3) NARROWED (§5): leaves need no rank (`vertrag_blatt_of_pflicht` discharges
         `hsort` entirely when every callee is foreign), and discharged contract
         sets compose rank-free (`umgebung_ok_kette_of_vertraege`). Exact residual:
         the rank over routines with defined callees in one acyclic group, which the
         emitter instantiates per unit in the checker's call-graph order
         (`Body.lean` section 5.1 tells the same story for
         `contract_of_duty`/`looprule_of_body`). No call-graph datatype stands in
         the model, so sortedness stays a premise, not a computation.
    (C4) NARROWED (§5): a cycle member's duty assumes foreign posts only for the
         names its body calls (`umgebung_ok_of_runs_zyklus_min` -- the ambient
         `∀ g, Fremd g → …` weakened to `∀ g, ruftAuf r.body g → Fremd g → …`),
         and SCCs compose supply-at-a-time through the shared fold
         (`umgebung_ok_kette_of_vertraege`). Exact residual: bounded intra-cycle
         contracts (`ContractBelowM` over `decreases`) plus foreign posts of called
         names; a call to a defined outside-cycle routine enters as foreign for
         that invocation (SCC condensation is the emitter's order, as in C3).
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

/-! ## 5. S2 cut closures -- per-unit discharge and minimal premises -/

/-- **C1, call-site half: entry `WFU` is exactly what `argumente_sicher` provides.**
    A routine duty keeps `WFU (paramUmgebung S.params)` as an explicit premise
    (`pflicht_of_geprueft_oder_fehlend`); this lemma is the matching obligation on
    the caller: fitting arguments evaluate and leave the callee's parameters in
    their scope. Nothing is invented -- the witness list `vs` travels in the open. -/
theorem wfu_eintritt_of_argumente (P : Programm) (Γ : Typing) (hD : Deklariert P.D Γ)
    {Δ : Umgebung} {s : State} (hw : Welt P.D Γ s.world) (hl : WFU Δ s.local')
    (params : List (String × Option Shape)) (as : List Expr) (β : Binding)
    (hfrei : namenFrei (params.map (·.1)) = true)
    (hargs : argumentePassen P (formen Δ) params as = true) :
    ∃ vs, evalAll s as = some vs ∧
      WFU (paramUmgebung params) (bindAll (params.map (·.1)) vs β) :=
  argumente_sicher hD hw hl params as β hfrei hargs

/-- **The answer with a declared result, unfolded once.** `NachPost` against
    `S.ergebnis = some sh`, as an iff, so every use below rewrites instead of
    unfolding a match. -/
theorem nachpost_some (S : Signatur) (sh : Shape) (h : S.ergebnis = some sh)
    (r : Option Value) :
    NachPost S r ↔
      ∃ v, r = some v ∧ (v.hasShape sh = true ∨ ∃ q, q ∈ S.gruende ∧ v = .reason q) := by
  unfold NachPost
  rw [h]

/-- **The answer without a declared result, unfolded once.** -/
theorem nachpost_none (S : Signatur) (h : S.ergebnis = none) (r : Option Value) :
    NachPost S r ↔ (r = none ∨ ∃ q, q ∈ S.gruende ∧ r = some (.reason q)) := by
  unfold NachPost
  rw [h]

/-- **The answer half of a checked routine, word for word.** `AntwortPasst` (what the
    checker guarantees at a `return`, over the caller's error channel `P.ruferR`) and
    `NachPost` (what the contract owes, over the signature's `gruende`) coincide once
    the routine body is checked under its own signature (`erg = S.ergebnis`,
    `P.ruferR = S.gruende` -- the emitter wires both from the signature). Each case
    is `rw [hE] at ha` (constructor arguments) plus definitional match reduction --
    no unfolding tactic that can silently stop. -/
theorem nachpost_of_antwortpasst (S : Signatur) (erg : Option Shape) (R : List String)
    (herg : erg = S.ergebnis) (hR : R = S.gruende) (v : Option Value)
    (ha : AntwortPasst erg R v) : NachPost S v := by
  subst herg; subst hR
  cases hE : S.ergebnis with
  | some sh =>
      cases v with
      | none =>
          rw [hE] at ha
          exact ha.elim
      | some w =>
          rw [hE] at ha
          rw [nachpost_some S sh hE]
          exact ⟨w, rfl, ha⟩
  | none =>
      cases v with
      | none =>
          rw [nachpost_none S hE]
          exact Or.inl rfl
      | some w =>
          rw [hE] at ha
          obtain ⟨q, hq, hwq⟩ := ha
          rw [nachpost_none S hE]
          exact Or.inr ⟨q, hq, by rw [hwq]⟩

/-- **No declared result, no missing `return`.** Against `S.ergebnis = none` the duty
    holds of a body that falls off the end (`finalValue = none`); the C2 failure is
    exactly the declared-result case below. -/
theorem nachpost_none_of_kein_ergebnis (S : Signatur) (h : S.ergebnis = none) :
    NachPost S none := by
  rw [nachpost_none S h]
  exact Or.inl rfl

/-- **C2: a missing `return` fails the duty explicitly.** Where the outcome carries no
    value (`finalValue = none` -- falling off the end, `exit`, `leave`) against a
    declared result, `Nach` is `False`-headed at the answer: no value is invented. -/
theorem pflicht_scheitert_ohne_wert (P : Programm) (Γ : Typing) (S : Signatur)
    (sh : Shape) (ρ : Env) (body : List Stmt) (t s' : State)
    (h : S.ergebnis = some sh) (hfv : finalValue (exec ρ body t) = none) :
    ¬ Nach P Γ S t s' (finalValue (exec ρ body t)) := by
  rw [hfv]
  intro hN
  unfold Nach at hN
  rw [nachpost_some S sh h] at hN
  obtain ⟨v, hv, _⟩ := hN.2
  cases hv

/-- **Valueless outcomes, per outcome value: duty or loud missing `return`.** The
    shared terminal of the `running`/`exited`/`left` (and valueless `returned`)
    branches below, stated over the outcome value `o` so the `cases ho : …`
    substitution in each branch meets it as stated. -/
theorem nach_oder_fehlend_of_kein_wert (P : Programm) (Γ : Typing) (ρ : Env)
    (body : List Stmt) (r : Routine) (t s' : State) (o : Outcome)
    (hw' : Welt P.D Γ s'.world)
    (hfs : finalState o = some s') (hfv : finalValue o = none) :
    (∃ s'', finalState o = some s'' ∧ Nach P Γ r.S t s'' (finalValue o))
    ∨ (finalValue o = none ∧ ∃ sh, r.S.ergebnis = some sh) := by
  by_cases he : ∃ sh, r.S.ergebnis = some sh
  · obtain ⟨sh, hsh⟩ := he
    exact Or.inr ⟨hfv, sh, hsh⟩
  · have hnone : r.S.ergebnis = none := by
      by_contra hne
      exact he (by
        cases hE : r.S.ergebnis with
        | some sh => exact ⟨sh, rfl⟩
        | none => exact absurd hE hne)
    have hnp : Nach P Γ r.S t s' (finalValue o) := by
      rw [hfv]
      exact ⟨hw', nachpost_none_of_kein_ergebnis r.S hnone⟩
    exact Or.inl ⟨s', hfs, hnp⟩

/-- **C1 duty half and C2 ending, per unit: a checked body meets its duty, or its
    missing `return` is named.** From the bridge (`ergebnis_of_geprueft`) plus an
    outcome analysis: `returned` carries the answer through `nachpost_of_antwortpasst`
    (under the emitter's wiring `P.ruferR = S.gruende`); every valueless outcome
    (`running`, `exited`, `left`) meets the duty when no result is declared and stands
    as the loud right disjunct when one is. `stuck` is `False`. Exact residuals: the
    entry `WFU` (C1, provided per call by `wfu_eintritt_of_argumente`), the person's
    `¬ LogikB`, the nested `UmgebungOK`/`SchleifenOK` (C6), and the missing-return
    disjunct (C2). -/
theorem pflicht_of_geprueft_oder_fehlend (P : Programm) (Γ : Typing) (ρ : Env)
    (hD : Deklariert P.D Γ) (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ)
    (r : Routine) (Δ' : Umgebung)
    (hcheck : pruefeBlock P r.S.ergebnis (paramUmgebung r.S.params) r.body = some Δ')
    (hR : P.ruferR = r.S.gruende)
    (t : State) (hw : Welt P.D Γ t.world)
    (hl : WFU (paramUmgebung r.S.params) t.local')
    (hlogik : ¬ LogikB ρ r.body t) :
    (∃ s', finalState (exec ρ r.body t) = some s' ∧
      Nach P Γ r.S t s' (finalValue (exec ρ r.body t)))
    ∨ (finalValue (exec ρ r.body t) = none ∧ ∃ sh, r.S.ergebnis = some sh) := by
  have herg := ergebnis_of_geprueft P Γ ρ hD hU hS r.S.ergebnis r.body
    (paramUmgebung r.S.params) Δ' t hcheck hw hl hlogik
  cases ho : exec ρ r.body t with
  | running s' =>
      rw [ho] at herg; simp only [Ergebnis] at herg
      exact nach_oder_fehlend_of_kein_wert P Γ ρ r.body r t s'
        (Outcome.running s') herg.1 rfl rfl
  | returned s' v =>
      rw [ho] at herg; simp only [Ergebnis] at herg
      cases v with
      | none =>
          exact nach_oder_fehlend_of_kein_wert P Γ ρ r.body r t s'
            (Outcome.returned s' none) herg.1 rfl rfl
      | some w =>
          have hnp : Nach P Γ r.S t s' (some w) :=
            ⟨herg.1, nachpost_of_antwortpasst r.S r.S.ergebnis P.ruferR rfl hR
              (some w) herg.2.2⟩
          exact Or.inl ⟨s', rfl, hnp⟩
  | exited s' =>
      rw [ho] at herg; simp only [Ergebnis] at herg
      exact nach_oder_fehlend_of_kein_wert P Γ ρ r.body r t s'
        (Outcome.exited s') herg.1 rfl rfl
  | left s' =>
      rw [ho] at herg; simp only [Ergebnis] at herg
      exact nach_oder_fehlend_of_kein_wert P Γ ρ r.body r t s'
        (Outcome.left s') herg.1 rfl rfl
  | stuck =>
      rw [ho] at herg; simp only [Ergebnis] at herg

/-- **C3 discharged for leaves: a duty that names only foreign callees IS the
    contract, with no rank.** Where `ruftAuf r.body g → Fremd g` for every `g`, the
    topological order has nothing to order; the single step
    (`vertrag_einzeln_of_pflicht`) is the whole induction. Exact residual: every
    callee foreign. -/
theorem vertrag_blatt_of_pflicht (ρ : Env) (P : Programm) (Γ : Typing)
    (r : Routine) (Fremd : String → Prop)
    (hruns : Runs ρ r.name r.body)
    (hduty : ∀ (t : State), Welt P.D Γ t.world → (∀ g, ruftAuf r.body g → Fremd g) →
      ∃ s', finalState (exec ρ r.body t) = some s' ∧
        Nach P Γ r.S t s' (finalValue (exec ρ r.body t)))
    (hF : ∀ g, ruftAuf r.body g → Fremd g) :
    Contract ρ r.name (fun t => Welt P.D Γ t.world) (Nach P Γ r.S) :=
  vertrag_einzeln_of_pflicht ρ P Γ r hruns (fun t hw => hduty t hw hF)

/-- **C3/C4 SCC-at-a-time in miniature: two discharged contract sets compose through
    the shared fold.** The composition adds no induction and no order -- each set
    carries its own justification (a rank for an acyclic group, `ContractBelowM` for
    a cycle) -- so closing supply-at-a-time is exactly closing each supply. Exact
    residual: the per-set discharges plus the partition (`hdef`) over the union. -/
theorem umgebung_ok_kette_of_vertraege (P : Programm) (Γ : Typing) (ρ : Env)
    (rs1 rs2 : List Routine) (Fremd : String → Prop)
    (hcon1 : ∀ r ∈ rs1, Contract ρ r.name (fun t => Welt P.D Γ t.world) (Nach P Γ r.S))
    (hcon2 : ∀ r ∈ rs2, Contract ρ r.name (fun t => Welt P.D Γ t.world) (Nach P Γ r.S))
    (hdef : ∀ f S, P.sig f = some S → (∃ r ∈ rs1 ++ rs2, r.name = f ∧ r.S = S) ∨ Fremd f)
    (hFremd : ∀ g, Fremd g → ∀ S, P.sig g = some S → ∀ (t : State), Welt P.D Γ t.world →
      Welt P.D Γ (ρ g t).1.world ∧ NachPost S (ρ g t).2)
    (hDiv : DivergenzOK P.sig) :
    UmgebungOK P Γ ρ := by
  apply umgebung_ok_of_vertrag P Γ ρ (rs1 ++ rs2) Fremd _ hdef hFremd hDiv
  intro r hr
  rcases List.mem_append.mp hr with h1 | h2
  · exact hcon1 r h1
  · exact hcon2 r h2

/-- **C4 narrowed: a cycle member's duty assumes foreign posts only for the names its
    body calls.** The ambient `∀ g, Fremd g → …` of `umgebung_ok_of_runs` is weakened
    to `∀ g, ruftAuf r.body g → Fremd g → …` -- an uncalled foreign body is never
    queried along this duty. Exact residual: bounded intra-cycle contracts plus the
    called foreign posts; the emitter's SCC order decides which defined names enter
    as foreign per invocation. -/
theorem umgebung_ok_of_runs_zyklus_min (P : Programm) (Γ : Typing) (ρ : Env)
    (rs : List Routine) (Fremd : String → Prop)
    (hrs : ∀ r ∈ rs, Runs ρ r.name r.body)
    (hduty : ∀ r ∈ rs, ∀ (t : State), Welt P.D Γ t.world →
      (∀ r' ∈ rs, ContractBelowM ρ (Routine.toMember P Γ r') r.mass t) →
      (∀ g, ruftAuf r.body g → Fremd g → ∀ S, P.sig g = some S → ∀ u, Welt P.D Γ u.world →
        Welt P.D Γ (ρ g u).1.world ∧ NachPost S (ρ g u).2) →
      ∃ s', finalState (exec ρ r.body t) = some s' ∧
        Nach P Γ r.S t s' (finalValue (exec ρ r.body t)))
    (hdef : ∀ f S, P.sig f = some S → (∃ r ∈ rs, r.name = f ∧ r.S = S) ∨ Fremd f)
    (hFremd : ∀ g, Fremd g → ∀ S, P.sig g = some S → ∀ (t : State), Welt P.D Γ t.world →
      Welt P.D Γ (ρ g t).1.world ∧ NachPost S (ρ g t).2)
    (hDiv : DivergenzOK P.sig) :
    UmgebungOK P Γ ρ := by
  apply umgebung_ok_of_runs P Γ ρ rs Fremd hrs _ hdef hFremd hDiv
  intro r hr t hw hcb hF
  exact hduty r hr t hw hcb (fun g hg hfr S hs u hu => hF g hfr S hs u hu)

/-- **D split, the answer without the divergence: `UmgebungOK` minus its passthrough
    conjunct.** The world-plus-answer half, derived from canonical contracts and the
    foreign hypothesis alone -- `DivergenzOK` is owed nowhere in it. -/
def UmgebungAntwort (P : Programm) (Γ : Typing) (ρ : Env) : Prop :=
  ∀ f S, P.sig f = some S → ∀ (t : State), Welt P.D Γ t.world →
    Welt P.D Γ (ρ f t).1.world ∧
    (match S.ergebnis with
     | some sh => ∃ v, (ρ f t).2 = some v ∧
        (v.hasShape sh = true ∨ ∃ q, q ∈ S.gruende ∧ v = .reason q)
     | none => (ρ f t).2 = none ∨ ∃ q, q ∈ S.gruende ∧ (ρ f t).2 = some (.reason q))

/-- **The answer half folds without divergence.** Same case split as
    `umgebung_ok_of_vertrag`, minus the conjunct that never touches world or answer. -/
theorem umgebung_antwort_of_vertrag (P : Programm) (Γ : Typing) (ρ : Env)
    (rs : List Routine) (Fremd : String → Prop)
    (hcon : ∀ r ∈ rs, Contract ρ r.name (fun t => Welt P.D Γ t.world) (Nach P Γ r.S))
    (hdef : ∀ f S, P.sig f = some S → (∃ r ∈ rs, r.name = f ∧ r.S = S) ∨ Fremd f)
    (hFremd : ∀ g, Fremd g → ∀ S, P.sig g = some S → ∀ (t : State), Welt P.D Γ t.world →
      Welt P.D Γ (ρ g t).1.world ∧ NachPost S (ρ g t).2) :
    UmgebungAntwort P Γ ρ := by
  intro f S hsig t hw
  rcases hdef f S hsig with ⟨r, hr, hname, hS⟩ | hfr
  · subst hname; subst hS
    obtain ⟨hw', ha⟩ := hcon r hr t hw
    exact ⟨hw', ha⟩
  · obtain ⟨hw', ha⟩ := hFremd f hfr S hsig t hw
    exact ⟨hw', ha⟩

/-- **D minimal: the answer plus exactly the divergence conjunct is `UmgebungOK`.**
    `DivergenzOK P.sig` is used once, here, and nowhere else in the fold. -/
theorem umgebung_ok_of_antwort (P : Programm) (Γ : Typing) (ρ : Env)
    (hA : UmgebungAntwort P Γ ρ) (hDiv : DivergenzOK P.sig) :
    UmgebungOK P Γ ρ := by
  intro f S hsig t hw
  obtain ⟨hw', ha⟩ := hA f S hsig t hw
  exact ⟨hw', ha, hDiv⟩

#print axioms Gabbro.Komposition.wfu_eintritt_of_argumente
#print axioms Gabbro.Komposition.nachpost_some
#print axioms Gabbro.Komposition.nachpost_none
#print axioms Gabbro.Komposition.nachpost_of_antwortpasst
#print axioms Gabbro.Komposition.nachpost_none_of_kein_ergebnis
#print axioms Gabbro.Komposition.pflicht_scheitert_ohne_wert
#print axioms Gabbro.Komposition.nach_oder_fehlend_of_kein_wert
#print axioms Gabbro.Komposition.pflicht_of_geprueft_oder_fehlend
#print axioms Gabbro.Komposition.vertrag_blatt_of_pflicht
#print axioms Gabbro.Komposition.umgebung_ok_kette_of_vertraege
#print axioms Gabbro.Komposition.umgebung_ok_of_runs_zyklus_min
#print axioms Gabbro.Komposition.umgebung_antwort_of_vertrag
#print axioms Gabbro.Komposition.umgebung_ok_of_antwort

end Gabbro.Komposition
