module

public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Kern.Syntax.Marken.Teil2
public import Grammatik.Nebenlaeufigkeit.Allgemein.Wettlauf.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

theorem keine_ueberkreuzung (l : Lauf D) (hg : Gesittet l) (i j : Nat) (f g : Faden)
    (L1 L2 : D.Lock) (h h' : List D.Lock)
    (hi : l[i]? = some (Schritt.mk f (.nimmt L2 h))) (hj : l[j]? = some (Schritt.mk g (.nimmt L1 h')))
    (h1 : L1 ∈ h) (h2 : L2 ∈ h') : False := by
  have gi : (Ereignis.nimmt (D := D) L2 h).gut :=
    hg.gut f (i + 1) _ (by rw [l.spur_succ_eigen f i _ hi]; exact List.mem_cons_self)
  have gj : (Ereignis.nimmt (D := D) L1 h').gut :=
    hg.gut g (j + 1) _ (by rw [l.spur_succ_eigen g j _ hj]; exact List.mem_cons_self)
  simp only [Ereignis.gut] at gi gj
  have a := gi.1 L1 h1
  have b := gj.1 L2 h2
  omega

/-! ## 5. Von den Ruempfen in den Lauf -- was `exec` liefert, und was fehlt

    `exec_spur` (`Satz.lean`) sagt ueber EINEN Rumpf: aus leerer Spur kommen nur
    konsistente Spuren mit guten Ereignissen zurueck (`Brav.konsistent_von_leer`,
    `Brav.gut_von_leer`). Was ein LAUF daraus macht, steht hier: jede
    beobachtete Teilspur ist eine Endstrecke der vollen (Verschraenkung
    unten), und Endstrecken bleiben konsistent (`Konsistent.drop`).

    EHRLICH GESAGT -- was dieser Satz NICHT baut (2026-09-10,
    `messung/ZIEL-BEWERTUNG-2026-09-10.md`, Stand Bahn 78):
    W3 (Ausschluss) und W5 (ungeteilt) bleiben PRAEMISSEN: sie sprechen ueber
    das Verhaeltnis der Faeden zueinander (fremde Sperrprimitive,
    `shared`-Deklaration), und kein Satz ueber je einen Rumpf kann sie
    schliessen. W4 (Marke in einem Faden) ist seit Bahn 78 KEINE blosse
    Praemisse mehr: `Marken.lean` beweist die Einzelfaedrigkeit jedes
    `Verlauf`-Standes, und §7 unten projiziert `Einfaedig` in
    `marke_eindeutig` -- was noch fehlt, ist der Stand HINTER einem echten
    `Lauf D` (ein `Verlauf` je Faden durch `exec`), also reist `hEin` als
    explizite Hypothese. Ebenso fehlt der
    Owicki-Gries-Schritt: dass gueltige sequenzielle Logik (`requires` /
    `ensures`) unter Verschraenkung gueltig bleibt, folgt aus HB-Ordnung nicht
    -- dazu brauchte es eine gemeinsame Semantik mit Rahmen-Disjunktheit
    (`exec_rahmen` ist der Kandidat fuer die Praemisse), und die steht nirgends.
    Rennfreiheit und Logikbeweis sind damit zwei unverbundene Saetze. -/

/-- Eine beobachtete Teilspur ist eine Endstrecke der vollen: so sieht eine
    Verschraenkung aus, die die Faeden nur verzahnt statt umzuschreiben. Ein
    Lauf, der das verletzt, ist keine Verschraenkung dieser Ausfuehrungen. -/
def IstVerschraenkung (l : Lauf D) (voll : Faden → List (Ereignis D)) : Prop :=
  ∀ f j, ∃ k, l.spur f j = (voll f).drop k

/-- W1 und W2 ueber jeder Verschraenkung wohlgeformter Ausfuehrungen: was jeder
    Faden tut, ist konsistent und gut -- vererbt aus `exec_spur` ueber leere
    Spuren, erhalten ueber Endstrecken. Mit W3-W5 als Prämissen ist das
    `Gesittet`; ohne sie ist es genau die Haelfte, die ein Rumpf traegt. -/
theorem lauf_aus_brav (l : Lauf D) (voll : Faden → List (Ereignis D))
    (hvoll : ∀ f, ∃ a b : World D, a.spur = [] ∧ Brav a b ∧ b.spur = voll f)
    (hvers : IstVerschraenkung l voll) :
    (∀ f j, Konsistent (l.spur f j)) ∧ (∀ f j (e : Ereignis D), e ∈ l.spur f j → e.gut) := by
  constructor
  · intro f j
    obtain ⟨k, hk⟩ := hvers f j
    obtain ⟨a, b, hempty, hbrav, hspur⟩ := hvoll f
    rw [hk, ← hspur]
    exact (hbrav.konsistent_von_leer hempty).drop _ _
  · intro f j e he
    obtain ⟨k, hk⟩ := hvers f j
    obtain ⟨a, b, hempty, hbrav, hspur⟩ := hvoll f
    have hmem : e ∈ voll f := List.mem_of_mem_drop (hk ▸ he)
    rw [← hspur] at hmem
    exact hbrav.gut_von_leer hempty hmem

/-! ## 6. Declared concurrency -- who shares a run (lane C, 2026-09-10)

    The declaration `concurrent { f, g };` becomes the premise `Nebeneinander`:
    which bodies share a run. What stands in no set never runs concurrently
    (closed world). `kein_wettlauf` above holds over EVERY interleaving; the
    corollary below names the shape the joint model will consume: the same
    happens-before order, quantified over the RESTRICTED interleaving of
    declared pairs. `kein_wettlauf` itself stays as-is.

    The Owicki-Gries step -- `exec_rahmen` per body plus pairwise disjoint
    frames ⇒ sequential contracts survive interleaving -- is NOT here yet; it
    needs the joint model of the declared pair set, which stands nowhere. -/

/-- Which bodies share a run: the `concurrent { … }` declaration as a premise.
    It travels as an explicit `Nb : Nebeneinander` argument below, not a
    `variable`: the existing theorems above quantify over every interleaving,
    and a section variable here would rewrite their context. -/
abbrev Nebeneinander : Type := Faden → Faden → Prop

/-- A run in which only declared pairs interleave: any two steps of different
    threads stand in the declared relation. -/
def BeschraenkteVerschraenkung (Nb : Nebeneinander) (l : Lauf D) : Prop :=
  ∀ (i j : Nat) (f g : Faden) (ei ej : Ereignis D),
    l[i]? = some (Schritt.mk f ei) → l[j]? = some (Schritt.mk g ej) → f ≠ g →
    Nb f g

/-- **Nur Deklarierte teilen sich den Lauf (closed world, Satzform).** In einem
    Lauf, dessen Verschraenkung auf deklarierte Paare beschraenkt ist, haben
    zwei verschiedene Faeden nur dann Schritte, wenn sie deklariert sind.
    Das ist die Definition `BeschraenkteVerschraenkung`, angewendet -- kein
    neuer Inhalt, sondern die benannte Andockstelle: die Checker-Seite
    (`W002`) verweigert genau die Paare ohne `Nb`, und dieser Satz sagt, dass
    im beschraenkten Lauf nur `Nb`-Paare vorkommen. Die Prämisse wird benutzt;
    was hier stuende und mehr bewiebe, stuende als eigener Satz daneben. -/
theorem nur_deklariert_teilt_lauf (Nb : Nebeneinander) (l : Lauf D)
    (hb : BeschraenkteVerschraenkung (D := D) Nb l)
    (i j : Nat) (f g : Faden) (ei ej : Ereignis D)
    (hi : l[i]? = some (Schritt.mk f ei)) (hj : l[j]? = some (Schritt.mk g ej))
    (hfg : f ≠ g) : Nb f g :=
  hb i j f g ei ej hi hj hfg

/-! ## 7. W4 aus der Konstruktion -- `Einfaedig` liefert `marke_eindeutig`

    `Gesittet.marke_eindeutig` keeps its shape (the consumers in `Ziel.lean` and
    `Interferenz.lean` read exactly this field), but it is no longer a bare
    premise: `marke_eindeutig_aus_einfaedig` derives it from `Marken.Einfaedig`
    over the projected run, and `gesittet_aus_einfaedig` builds the whole
    `Gesittet` from the construction instead of the bare W4. `Marken.lean`
    proves that every `Verlauf` yields single-threaded stands
    (`verlauf_einfaedig`); what REMAINS open (rebooked cut): threading one
    `Verlauf` per run through `exec` -- the per-thread stand behind a real
    `Lauf D` stands nowhere yet, so the projection hypothesis `hEin` still
    travels as an explicit argument. -/

/-- Project a real guard into a code guard over `code`. -/
def markenProj (code : D.Marke → Nat) : Res D → Marken.Res
  | .held _ => .held
  | .marke m s => .marke (code m) s

/-- Project a real event: the same mark list, under codes. -/
def ereignisProj (code : D.Marke → Nat) (ei : Ereignis D) : Marken.Ereignis :=
  ⟨ei.lambda.map (markenProj code)⟩

/-- Project a real step: the same thread, the projected event. -/
def schrittProj (code : D.Marke → Nat) (s : Schritt D) : Marken.Schritt :=
  ⟨s.faden, ereignisProj code s.ereignis⟩

/-- Project a real run, step by step. -/
def laufProj (code : D.Marke → Nat) (l : Lauf D) : Marken.Lauf :=
  l.map (schrittProj code)

/-- Mark membership survives the projection. -/
theorem markenProj_mem (code : D.Marke → Nat) (ei : Ereignis D)
    (m : D.Marke) (s : Nat) (h : Res.marke m s ∈ ei.lambda) :
    Marken.Res.marke (code m) s ∈ (ereignisProj code ei).lambda := by
  unfold ereignisProj
  simp only
  exact List.mem_map.mpr ⟨_, h, rfl⟩

/-- Step lookup survives the projection. -/
theorem laufProj_get (code : D.Marke → Nat) (l : Lauf D)
    (i : Nat) (f : Faden) (ei : Ereignis D)
    (h : l[i]? = some (Schritt.mk f ei)) :
    (laufProj code l)[i]? =
      some (Marken.Schritt.mk f (ereignisProj code ei)) := by
  simp only [laufProj, List.getElem?_map, h, Option.map_some, schrittProj]

/-- **W4 from the construction.** `Einfaedig` over the projected run IS
    `marke_eindeutig` over the real run. -/
theorem marke_eindeutig_aus_einfaedig (code : D.Marke → Nat) (l : Lauf D)
    (hEin : Marken.Einfaedig (laufProj code l))
    (i j : Nat) (f g : Faden) (m : D.Marke) (s s' : Nat)
    (ei ej : Ereignis D)
    (hi : l[i]? = some (Schritt.mk f ei))
    (hj : l[j]? = some (Schritt.mk g ej))
    (hmi : Res.marke m s ∈ ei.lambda)
    (hmj : Res.marke m s' ∈ ej.lambda) : f = g := by
  exact hEin i j f g (code m) s s' _ _
    (laufProj_get code l i f ei hi) (laufProj_get code l j g ej hj)
    (markenProj_mem code ei m s hmi) (markenProj_mem code ej m s' hmj)

/-- **A `Gesittet` from the construction.** The whole bundle with W4 supplied
    by `Einfaedig` instead of the bare premise. -/
theorem gesittet_aus_einfaedig (l : Lauf D)
    (konsistent : ∀ f j, Konsistent (l.spur f j))
    (gut : ∀ f j, ∀ e ∈ l.spur f j, e.gut)
    (ausschluss : ∀ (j : Nat) (f : Faden) (L : D.Lock) (h : List D.Lock),
      l[j]? = some (Schritt.mk f (.nimmt L h)) → ∀ g, g ≠ f → ¬ l.haelt g L j)
    (code : D.Marke → Nat) (hEin : Marken.Einfaedig (laufProj code l))
    (ungeteilt : ∀ (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob)
      (ei ej : Ereignis D),
      l[i]? = some (Schritt.mk f ei) → l[j]? = some (Schritt.mk g ej) →
      ei.traeger = some o → ej.traeger = some o →
      (match o with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) → f = g) :
    Gesittet l :=
  ⟨konsistent, gut, ausschluss, marke_eindeutig_aus_einfaedig code l hEin,
    ungeteilt⟩

#print axioms Gabbro.Grammatik.marke_eindeutig_aus_einfaedig
#print axioms Gabbro.Grammatik.gesittet_aus_einfaedig

#print axioms Gabbro.Grammatik.kein_wettlauf
#print axioms Gabbro.Grammatik.kein_wettlauf_global
#print axioms Gabbro.Grammatik.keine_ueberkreuzung
#print axioms Gabbro.Grammatik.lauf_aus_brav
#print axioms Gabbro.Grammatik.nur_deklariert_teilt_lauf

/-! ## 8. W4 from the Verlauf -- `verlauf_einfaedig` through the trace link

    `marke_eindeutig_aus_einfaedig` (§7) closes W4 against `Marken.Einfaedig`
    over the projected run. What the construction PROVES, though, is
    `Marken.verlauf_einfaedig`: every reachable stand is single-threaded
    (`StandEinfaedig σ` -- one stand, one point in time). That is a different
    level from `Einfaedig` (pairs of steps across time): a mark freed by one
    thread (`verbrauche`) and recreated by another (`erzeuge`) is owned by
    exactly one thread at every stand, yet named by two threads over the run.
    So no proof from `verlauf_einfaedig` alone can discharge W4 -- the trace
    link, that projected events name exactly what their thread owns, is the
    exact remainder, and it stands nowhere yet (no per-thread `Verlauf`
    through `exec` behind a real `Lauf D`).

    `SpurLink` names that remainder in minimal shape: every mark named by a
    projected event is owned by that event's thread at one shared reachable
    stand. Through `verlauf_einfaedig` that stand is single-threaded, and W4
    follows. `gesittet_aus_verlauf` is the bundle with the construction
    consumed: `hEin` narrows to a `Verlauf` plus the link. -/

/-- Trace link (booked remainder): every mark a projected event names is owned
    by that event's thread at one shared reachable stand. -/
def SpurLink (code : D.Marke → Nat) (l : Lauf D) (σ : Marken.Stand) : Prop :=
  ∀ (i : Nat) (f : Faden) (ei : Ereignis D),
    l[i]? = some (Schritt.mk f ei) →
    ∀ (m : D.Marke) (s : Nat), Res.marke m s ∈ ei.lambda →
      Marken.Besitzt σ f (code m)

/-- **W4 from the Verlauf.** `verlauf_einfaedig` through the trace link IS
    `marke_eindeutig` over the real run. -/
theorem marke_eindeutig_aus_verlauf
    (κ : Marken.MarkDekl) {σ : Marken.Stand} (v : Marken.Verlauf κ σ)
    (code : D.Marke → Nat) (l : Lauf D)
    (hlink : SpurLink (D := D) code l σ)
    (i j : Nat) (f g : Faden) (m : D.Marke) (s s' : Nat)
    (ei ej : Ereignis D)
    (hi : l[i]? = some (Schritt.mk f ei))
    (hj : l[j]? = some (Schritt.mk g ej))
    (hmi : Res.marke m s ∈ ei.lambda)
    (hmj : Res.marke m s' ∈ ej.lambda) : f = g :=
  Marken.verlauf_einfaedig κ v (code m) f g
    (hlink i f ei hi m s hmi) (hlink j g ej hj m s' hmj)

/-- **A `Gesittet` from the Verlauf.** The whole bundle with W4 supplied by
    `verlauf_einfaedig` plus the trace link instead of the bare premise. -/
theorem gesittet_aus_verlauf (l : Lauf D)
    (konsistent : ∀ f j, Konsistent (l.spur f j))
    (gut : ∀ f j, ∀ e ∈ l.spur f j, e.gut)
    (ausschluss : ∀ (j : Nat) (f : Faden) (L : D.Lock) (h : List D.Lock),
      l[j]? = some (Schritt.mk f (.nimmt L h)) → ∀ g, g ≠ f → ¬ l.haelt g L j)
    (κ : Marken.MarkDekl) {σ : Marken.Stand} (v : Marken.Verlauf κ σ)
    (code : D.Marke → Nat) (hlink : SpurLink (D := D) code l σ)
    (ungeteilt : ∀ (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob)
      (ei ej : Ereignis D),
      l[i]? = some (Schritt.mk f ei) → l[j]? = some (Schritt.mk g ej) →
      ei.traeger = some o → ej.traeger = some o →
      (match o with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) → f = g) :
    Gesittet l :=
  ⟨konsistent, gut, ausschluss, marke_eindeutig_aus_verlauf κ v code l hlink,
    ungeteilt⟩

#print axioms Gabbro.Grammatik.marke_eindeutig_aus_verlauf
#print axioms Gabbro.Grammatik.gesittet_aus_verlauf

/-! ## 9. The bridge -- from `exec` traces to `Gesittet`, with honest coverage

    `hBridge` (`Ziel.lean`, `ziel_nutzer_last`): every interleaving of well-formed
    bodies is `Gesittet`. One body reaches W1 and W2 (through `Brav` over empty
    traces, inherited over tails -- `lauf_aus_brav`); no single-body sentence can
    reach W3 (exclusion speaks about FOREIGN lock primitives), W4 (one mark in
    one thread, across threads), or W5 (an unshared carrier belongs to one
    thread -- the declaration). This section discharges the bridge over EXACTLY
    the covered class, and names every premise that remains.

    COVERAGE (proved, not claimed):
    - W2 needs no suffix: `gut_without_suffix` -- any observation whose events
      all occur in the full per-thread trace is good. The suffix restriction is
      unnecessary for goodness (membership is all `Brav.gut_von_leer` reads).
    - W1 keeps the suffix: `Konsistent` reads `offen` of the REST (`passt`), so
      only tails (`drop`) inherit it. The covered interleavings are exactly the
      suffix-closed ones -- `IstVerschraenkung` -- and `covered_prefix` shows the
      class is closed under halting early (a temporal prefix stays covered).
    - `bruecke_exec_gesittet` discharges THOSE interleavings: per-thread `Brav`
      provenance (closed per body by `ziel_brav_aus_exec`) plus the three
      cross-thread shapes yields `Gesittet`. `ExecEng` (`Ziel.lean`) is the same
      bundle as a structure -- the narrowed corollary; this theorem is its
      unfolded form beside `lauf_aus_brav`.

    PREMISES (named, bounded):
    - W3 travels as `ForeignExclusion`: the mutual-exclusion promise of the
      FOREIGN lock primitives (`A_lock`). No sentence over one body can close
      it -- the other thread's `nimmt`/`gibt` steps are not in this body's
      trace. Hardware-assumption class, goal-conform: named here, and BOUNDED
      to lock takes (it constrains only `nimmt` steps -- accesses, releases,
      and marks pass through untouched). THE single remaining HW-adjacent
      premise: W4 is construction (`Marken.lean`), W5 is declaration
      (`Geteilt.lean` wiring, see below).
    - W4 travels as `hEin`: `Einfaedig` over the projected run. Where a
      per-thread `Verlauf` plus the trace link stands, `SpurLink` narrows it --
      `bruecke_exec_gesittet_of_verlauf` consumes the construction instead.
      The link itself (projected events name what their thread owns) stands
      nowhere yet: no per-thread `Verlauf` through `exec` behind a real
      `Lauf D` -- rebooked cut, stated in §8.
    - W5 travels inline (the `ungeteilt` shape): the declaration side is
      discharged by `Geteilt.ungeteilt_aus_bau` (passing check plus static
      coverage gives one thread); what remains here is the run-to-`Bau` wiring
      (body-extraction coverage, cut C2 there) -- a declaration premise, not a
      hardware one.
    - The Owicki-Gries step is NOT here: valid sequential contracts surviving
      interleaving needs the joint model with frame disjointness -- stands
      nowhere yet, stays open (as in `Ziel.lean` §2b).
    - No `sorry`, no `admit`, no `axiom` -- the `#print axioms` lines below
      show only Lean's own (`propext`, `Classical.choice`, `Quot.sound`). -/

/-- (W3) as the named HW-adjacent premise: foreign lock exclusion. Who takes `L`
    takes it while no other thread holds it -- the promise of the FOREIGN lock
    primitives (`A_lock`), bounded to `nimmt` steps. -/
def ForeignExclusion (l : Lauf D) : Prop :=
  ∀ (j : Nat) (f : Faden) (L : D.Lock) (h : List D.Lock),
    l[j]? = some (Schritt.mk f (.nimmt L h)) → ∀ g, g ≠ f → ¬ l.haelt g L j

/-- W2 needs no suffix: any observation whose events all occur in the full
    per-thread trace is good. The suffix restriction of `lauf_aus_brav` is
    unnecessary for goodness -- `Brav.gut_von_leer` reads membership only. -/
theorem gut_without_suffix (voll : Faden → List (Ereignis D))
    (hvoll : ∀ f, ∃ a b : World D, a.spur = [] ∧ Brav a b ∧ b.spur = voll f)
    (f : Faden) {s : List (Ereignis D)} (hmem : ∀ e ∈ s, e ∈ voll f) :
    ∀ e ∈ s, e.gut := by
  intro e he
  obtain ⟨a, b, hempty, hbrav, hspur⟩ := hvoll f
  have hmem' : e ∈ b.spur := by rw [hspur]; exact hmem e he
  exact hbrav.gut_von_leer hempty hmem'

/-- The covered class is closed under halting early: a temporal prefix of a
    suffix-closed interleaving is suffix-closed (per thread, the observed trace
    at `j` in the prefix is the observed trace at `min n j` in the full run). -/
theorem covered_prefix (l : Lauf D) (voll : Faden → List (Ereignis D))
    (hvers : IstVerschraenkung l voll) (n : Nat) :
    IstVerschraenkung (l.take n) voll := by
  intro f j
  obtain ⟨k, hk⟩ := hvers f (min n j)
  refine ⟨k, ?_⟩
  unfold Lauf.spur
  rw [List.take_take, Nat.min_comm j n]
  exact hk

/-- **The bridge: from `exec` traces to `Gesittet`, over exactly the covered
    interleavings.** Per-thread `Brav` provenance (W1, W2 via `lauf_aus_brav`)
    plus the three cross-thread shapes (W3 as `ForeignExclusion`, W4 as `hEin`,
    W5 inline) yields `Gesittet`. -/
theorem bruecke_exec_gesittet (l : Lauf D) (voll : Faden → List (Ereignis D))
    (hvoll : ∀ f, ∃ a b : World D, a.spur = [] ∧ Brav a b ∧ b.spur = voll f)
    (hvers : IstVerschraenkung l voll)
    (hausschluss : ForeignExclusion (D := D) l)
    (code : D.Marke → Nat) (hEin : Marken.Einfaedig (laufProj code l))
    (hungeteilt : ∀ (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob)
      (ei ej : Ereignis D),
      l[i]? = some (Schritt.mk f ei) → l[j]? = some (Schritt.mk g ej) →
      ei.traeger = some o → ej.traeger = some o →
      (match o with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) → f = g) :
    Gesittet l := by
  obtain ⟨hkons, hgut⟩ := lauf_aus_brav l voll hvoll hvers
  exact gesittet_aus_einfaedig l hkons hgut hausschluss code hEin hungeteilt

/-- **The bridge through the per-thread Verlauf.** The same covered
    interleavings, with W4 supplied by `verlauf_einfaedig` plus the trace link
    (`SpurLink` narrows `hEin`) instead of the bare `Einfaedig` hypothesis. -/
theorem bruecke_exec_gesittet_of_verlauf (l : Lauf D)
    (voll : Faden → List (Ereignis D))
    (hvoll : ∀ f, ∃ a b : World D, a.spur = [] ∧ Brav a b ∧ b.spur = voll f)
    (hvers : IstVerschraenkung l voll)
    (hausschluss : ForeignExclusion (D := D) l)
    (κ : Marken.MarkDekl) {σ : Marken.Stand} (v : Marken.Verlauf κ σ)
    (code : D.Marke → Nat) (hlink : SpurLink (D := D) code l σ)
    (hungeteilt : ∀ (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob)
      (ei ej : Ereignis D),
      l[i]? = some (Schritt.mk f ei) → l[j]? = some (Schritt.mk g ej) →
      ei.traeger = some o → ej.traeger = some o →
      (match o with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) → f = g) :
    Gesittet l := by
  obtain ⟨hkons, hgut⟩ := lauf_aus_brav l voll hvoll hvers
  exact gesittet_aus_verlauf l hkons hgut hausschluss κ v code hlink hungeteilt

#print axioms Gabbro.Grammatik.ForeignExclusion
#print axioms Gabbro.Grammatik.gut_without_suffix
#print axioms Gabbro.Grammatik.covered_prefix
#print axioms Gabbro.Grammatik.bruecke_exec_gesittet
#print axioms Gabbro.Grammatik.bruecke_exec_gesittet_of_verlauf

end Gabbro.Grammatik
