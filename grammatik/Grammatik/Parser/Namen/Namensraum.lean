
/-!
  File:      Grammatik/Parser/Namen/Namensraum.lean
  Subject:   **Name spaces of linked projects** (BUILD-SYSTEM 7.6): how a path written in one project
             resolves in a unit of several projects.

  The language rule, modelled here before the Rust checker follows:

  * A unit consists of COPIES of projects. A name of the unit is a pair: the copy (`none` for the
    program's own project, `some N` for a dependency copy, one per project and version) and the
    path inside it (`Name`). Two projects with a module of the same name therefore never share a name.
  * A project writes paths relative to its own root. A path whose first segment is the LOCAL name
    of a declared dependency (`use d::m::x;`) goes into the copy the build file
    assigned to that dependency (`qualifiziere`). Versions are never written in the source: a
    project declares each dependency once, so its local name is unambiguous, and the build maps it
    to the copy (`Platz.deps`). A project cannot name a copy it did not declare.
  * The candidates of a path are those of today's checker (`kandidaten`): the path inside the
    using module and every enclosing one, innermost first, then every `use` line of these modules
    whose last segment is the path's last segment. The first candidate that names something
    VISIBLE wins (`aufloese`); visible are the project's own names and the public names of its
    declared dependencies (`sichtbar`), nothing else of the unit.

  Theorems:
  * `mem_sichtbar` -- a candidate is visible exactly when the project or the public part of the
    dependency it names declares it; where the copies sit does not enter.
  * **`aufloeseK_platz`** -- what a path means inside a project (the candidate chosen) is the same
    wherever the project and its dependencies sit in a unit: checked alone as a program or linked
    as any copy under any other program, a library's names resolve alike. Only its own
    names, its dependencies' local names and their public names enter.
  * `aufloese_sichtbar` -- a resolved name is the project's own or a public name of a declared
    dependency: nothing reaches into an undeclared copy.
  * `namen_getrennt` -- names of different copies are disjoint, so composing projects needs no
    renaming (`Projekte` L1).
-/

namespace Gabbro.Grammatik.Parser.Namensraum

/-- A path as written: its segments. -/
abbrev Pfad := List String

/-- A name of the unit: the copy (`none`: the program's own project) and the path inside it. -/
abbrev Name := Option String × Pfad

/-- **One project as written**: its declared names (module path and item, from its root) and its
    `use` lines (the module they stand in, the path they name). -/
structure Quelle where
  namen : List Pfad
  verwendet : List (Pfad × Pfad)

/-- **Where a project sits in a unit**: its own copy and, per declared dependency, its local name,
    the copy the build assigned to it, and that copy's public names. -/
structure Platz where
  ns : Option String
  deps : List (String × String × List Pfad)

/-- The dependency a local name declares: its copy and public names. -/
def ziel : List (String × String × List Pfad) → String → Option (String × List Pfad)
  | [], _ => none
  | e :: es, d => if e.1 = d then some e.2 else ziel es d

/-- The public names a local dependency name declares, without the copy. -/
def pubVon : List (String × List Pfad) → String → Option (List Pfad)
  | [], _ => none
  | e :: es, d => if e.1 = d then some e.2 else pubVon es d

/-- What of a place a project can observe: local names and public names, not the copies. -/
def Platz.schnitt (L : Platz) : List (String × List Pfad) := L.deps.map fun e => (e.1, e.2.2)

/-- The modules enclosing `von` (itself included), innermost first, ending with the root. -/
def umgebend (von : Pfad) : List Pfad :=
  (List.range (von.length + 1)).reverse.map fun k => von.take k

/-- **The candidates of a path** written in module `von`: inside `von` and every enclosing module,
    then the `use` lines of these modules that end in the path's last segment. -/
def kandidaten (Q : Quelle) (von p : Pfad) : List Pfad :=
  (umgebend von).map (· ++ p) ++
    (umgebend von).flatMap fun m =>
      (Q.verwendet.filter fun z => decide (z.1 = m) && decide (z.2.getLast? = p.getLast?)).map Prod.snd

/-- **A written path as a name of the unit**: into the copy of the dependency its first segment
    names, else into the project's own copy. -/
def qualifiziere (L : Platz) : Pfad → Name
  | d :: rest => match ziel L.deps d with
    | some (n, _) => (some n, rest)
    | none => (L.ns, d :: rest)
  | [] => (L.ns, [])

/-- **What a project sees of the unit**: its own names in its copy, and the public names of its
    declared dependencies in theirs. -/
def sichtbar (Q : Quelle) (L : Platz) : List Name :=
  Q.namen.map (fun x => (L.ns, x)) ++ L.deps.flatMap fun e => e.2.2.map fun y => (some e.2.1, y)

/-- The candidate a path resolves to: the first that names something visible. -/
def aufloeseK (Q : Quelle) (L : Platz) (von p : Pfad) : Option Pfad :=
  (kandidaten Q von p).find? fun c => decide (qualifiziere L c ∈ sichtbar Q L)

/-- **The name a path resolves to.** -/
def aufloese (Q : Quelle) (L : Platz) (von p : Pfad) : Option Name :=
  (aufloeseK Q L von p).map (qualifiziere L)

/-- **A well-formed place**: the project's own copy is none of its dependencies' copies, and two
    dependencies are two copies. (The build makes both hold: copies are named per project and
    version, one version reached twice is one copy under one local name.) -/
def Platz.Gut (L : Platz) : Prop :=
  (∀ e ∈ L.deps, L.ns ≠ some e.2.1) ∧ (L.deps.map fun e => e.2.1).Nodup

/-- **Whether a written path names something**, from what the project can observe only. -/
def bed (Q : Quelle) (s : List (String × List Pfad)) : Pfad → Bool
  | d :: rest => match pubVon s d with
    | some pub => decide (rest ∈ pub)
    | none => decide (d :: rest ∈ Q.namen)
  | [] => decide ([] ∈ Q.namen)

theorem ziel_mem : ∀ {ds : List (String × String × List Pfad)} {d : String} {x : String × List Pfad},
    ziel ds d = some x → ∃ e ∈ ds, e.2 = x
  | [], _, _, h => by cases h
  | e :: es, d, x, h => by
      unfold ziel at h
      split at h
      · cases h; exact ⟨e, List.mem_cons_self, rfl⟩
      · obtain ⟨e', he', hx⟩ := ziel_mem h
        exact ⟨e', List.mem_cons_of_mem _ he', hx⟩

theorem ziel_pub : ∀ (ds : List (String × String × List Pfad)) (d : String),
    (ziel ds d).map Prod.snd = pubVon (ds.map fun e => (e.1, e.2.2)) d
  | [], _ => rfl
  | e :: es, d => by
      simp only [ziel, pubVon, List.map_cons]
      split
      · rfl
      · exact ziel_pub es d

theorem ziel_none (ds : List (String × String × List Pfad)) (d : String) :
    ziel ds d = none ↔ pubVon (ds.map fun e => (e.1, e.2.2)) d = none := by
  rw [← ziel_pub]; cases ziel ds d <;> simp only [Option.map_none, reduceCtorEq, Option.map_some]

/-- An injective map on a duplicate-free image (core only: this file stands in the elaborator's import
    chain, where Mathlib's `alias` keyword would break existing field names). -/
theorem inj_von_nodup_map {α β : Type} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup →
    ∀ {x y : α}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => nomatch hx
  | a :: l, h, x, y, hx, hy, hf => by
    simp only [List.Nodup, List.map_cons, List.pairwise_cons] at h
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact absurd hf (h.1 _ (List.mem_map_of_mem hy'))
    · exact absurd hf.symm (h.1 _ (List.mem_map_of_mem hx'))
    · exact inj_von_nodup_map h.2 hx' hy' hf

/-- A copy name among the dependencies stands for one dependency only. -/
theorem kopie_eins {L : Platz} (hG : L.Gut) {e e' : String × String × List Pfad} (he : e ∈ L.deps)
    (he' : e' ∈ L.deps) (h : e.2.1 = e'.2.1) : e = e' :=
  inj_von_nodup_map hG.2 he he' h

/-- **A candidate is visible exactly when the project or the public part of the dependency it
    names declares it** -- the copies do not enter. -/
theorem mem_sichtbar {Q : Quelle} {L : Platz} (hG : L.Gut) (c : Pfad) :
    qualifiziere L c ∈ sichtbar Q L ↔ bed Q L.schnitt c = true := by
  have eigen : ∀ x, (L.ns, x) ∈ sichtbar Q L ↔ x ∈ Q.namen := by
    intro x
    simp only [sichtbar, List.mem_append, List.mem_map, List.mem_flatMap, Prod.mk.injEq]
    constructor
    · rintro (⟨y, hy, -, rfl⟩ | ⟨e, he, y, -, hn, -⟩)
      · exact hy
      · exact absurd hn.symm (hG.1 e he)
    · intro hx; exact Or.inl ⟨x, hx, by simp only [and_self]⟩
  cases c with
  | nil => simp only [qualifiziere, bed, decide_eq_true_eq]; exact eigen []
  | cons d rest =>
      simp only [qualifiziere, bed, Platz.schnitt]
      cases hz : ziel L.deps d with
      | none =>
          rw [(ziel_none L.deps d).mp hz]
          simp only [decide_eq_true_eq]
          exact eigen _
      | some x =>
          obtain ⟨n, pub⟩ := x
          have hp : pubVon (L.deps.map fun e => (e.1, e.2.2)) d = some pub := by
            rw [← ziel_pub, hz]; rfl
          rw [hp]
          simp only [decide_eq_true_eq]
          obtain ⟨e, he, hex⟩ := ziel_mem hz
          simp only [sichtbar, List.mem_append, List.mem_map, List.mem_flatMap, Prod.mk.injEq]
          constructor
          · rintro (⟨y, -, hn, -⟩ | ⟨e', he', y, hy, hn, rfl⟩)
            · exact absurd (hn.trans (by rw [hex])) (hG.1 e he)
            · have hee := kopie_eins hG he' he (by rw [hex]; exact Option.some.inj hn)
              subst hee
              rw [hex] at hy
              exact hy
          · intro hr
            exact Or.inr ⟨e, he, rest, by rw [hex]; exact hr, by rw [hex], rfl⟩

/-- **The meaning of a path inside a project does not depend on where the project sits.** On two
    well-formed places with the same local dependency names and public names -- the project checked
    alone, and the project linked as any copy under any program, its dependencies under any copies --
    every path resolves to the same written candidate. -/
theorem aufloeseK_platz (Q : Quelle) {L₁ L₂ : Platz} (h₁ : L₁.Gut) (h₂ : L₂.Gut)
    (hs : L₁.schnitt = L₂.schnitt) (von p : Pfad) :
    aufloeseK Q L₁ von p = aufloeseK Q L₂ von p := by
  have hf : ∀ L : Platz, L.Gut →
      (fun c => decide (qualifiziere L c ∈ sichtbar Q L)) = fun c => bed Q L.schnitt c := by
    intro L hG; funext c
    exact Bool.eq_iff_iff.mpr (by rw [decide_eq_true_eq]; exact mem_sichtbar hG c)
  unfold aufloeseK
  rw [hf L₁ h₁, hf L₂ h₂, hs]

/-- **Nothing reaches into an undeclared copy**: a resolved name is visible to the project. -/
theorem aufloese_sichtbar {Q : Quelle} {L : Platz} {von p : Pfad} {x : Name}
    (h : aufloese Q L von p = some x) : x ∈ sichtbar Q L := by
  unfold aufloese at h
  cases hk : aufloeseK Q L von p with
  | none => rw [hk] at h; cases h
  | some c =>
      rw [hk] at h
      cases h
      have := List.find?_some hk
      exact of_decide_eq_true this

/-- **Names of different copies are disjoint**: projects compose without renaming. -/
theorem namen_getrennt {Q₁ Q₂ : Quelle} {n₁ n₂ : Option String} (h : n₁ ≠ n₂) (x : Name)
    (h₁ : x ∈ Q₁.namen.map fun y => (n₁, y)) : x ∉ Q₂.namen.map fun y => (n₂, y) := by
  simp only [List.mem_map] at h₁ ⊢
  obtain ⟨y, -, rfl⟩ := h₁
  rintro ⟨z, -, hz⟩
  exact h (congrArg Prod.fst hz).symm

end Gabbro.Grammatik.Parser.Namensraum
