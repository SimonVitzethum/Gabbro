/-
  File:      Grammatik/Parser/Elab/UebersetzePipeline.lean
  Subject:   THE LEAN TRANSLATION PIPELINE for every source text: lex, parse, preprocess,
             elaborate, and lower generically onto the declaration built from the source
             itself (`declOf u`). One function for every source text; every stage a Lean
             function, nothing Rust. Its output is the program the goal theorem's unit is
             built on (`Zielsatz.Einheit`).

  (Until 2026-10-18 this lived in `Schlusssatz.lean`, the closing theorem of the C
  correspondence chain; that chain was deleted with the C emitter -- tag
  `archiv/c-emitter-2026-10-17` -- and the generic pipeline moved here unchanged.)
-/
import Grammatik.Parser.Elab.UebersetzeAllg3

namespace Gabbro.Grammatik

open Parser Parser.Uebersetze Parser.UebersetzeAllg Parser.UebersetzeAllg2

/-- **THE LEAN TRANSLATION PIPELINE**: lex, parse, preprocess (`pre108`:
    the module unwrapped, bare `u32` as its full range), elaborate, lower
    GENERICALLY onto the declaration built from the source. Every stage a
    Lean function; nothing Rust. -/
def uebersetzeAllg (s : String) :
    Except String (Σ u : UProg, Programm (declOf u) × List (declOf u).Fn) :=
  match lex s with
  | .error _ => .error "lex"
  | .ok toks =>
    match parseTopTief toks with
    | .error e => .error e
    | .ok items =>
      match elabU (pre108 items) with
      | .error e => .error e
      | .ok u =>
        match lowerAllg u with
        | .error e => .error e
        | .ok (P, fs) => .ok ⟨u, P, fs⟩

/-- **PARSE FIDELITY FROM A SOURCE PINNED AS CHARACTERS**, stage by stage.
    The four premises are the four stages of `uebersetzeAllg`; the
    conclusion is the pipeline on the `String` the unit is indexed by.

    WHY IT EXISTS, and it is a MEMORY statement, not a proof one (O13):
    unfolding `uebersetzeAllg` at a CONCRETE source makes `simp` look at
    the discriminant `lex src`, and whnf of that runs Lean 4.33's UTF-8
    decoder over the whole text in the kernel -- measured 2026-09-15 on
    `ki-pc-fisch-101` at **70 GB for the unit of `beispiele/104`** (the cold full build
    died with `code 137` on a 16 GB machine). Here `l` is a VARIABLE, so
    there is nothing to decode: `lex_ofList` carries the pin across by
    the core lemmas `String.toList_ofList`/`String.length_ofList`, and
    every stage arrives as a hypothesis. A unit instance applies this
    lemma and the decoder is never run at all.

    Nothing is weakened. The conclusion is the SAME proposition the
    hand-written `unfold`/`rw` script proved -- `uebersetzeAllg src`
    for the unit's own `src` --, and `src = String.ofList l` holds by
    definition, so a guardian comparing the pieces `l` against the file
    still decides whether the unit is about this program. -/
theorem uebersetzeAllg_von_zeichen {l : List Char} {toks : List Token}
    {items : List SItemTief} {u : UProg} {P : Programm (declOf u)}
    {fs : List (declOf u).Fn}
    (hl : lexL l = .ok toks)
    (hp : parseTopTief toks = .ok items)
    (he : elabU (pre108 items) = .ok u)
    (hw : lowerAllg u = .ok (P, fs)) :
    uebersetzeAllg (String.ofList l) = .ok ⟨u, P, fs⟩ := by
  unfold uebersetzeAllg
  rw [lex_ofList, hl]
  dsimp only
  rw [hp]
  dsimp only
  rw [he]
  dsimp only
  rw [hw]

/-- A successful computation is `.ok` of its extracted value (how a unit
    instance names the parser's output without retyping it). -/
theorem except_ok_get {ε α : Type} {x : Except ε α} (h : x.toOption.isSome = true) :
    x = .ok (x.toOption.get h) := by
  cases x with
  | error e => simp [Except.toOption] at h
  | ok a => rfl

/-- The declared starts of an elaborated unit, as functions of its declaration: the thread roots (the
    `concurrent` members, then the dispatch roots of the `entry` items, `UProg.roots`), the functions entered
    by hardware (`UProg.hands`, `Programm.unterbricht`) and the threads created by `start { .. };`
    (`UProg.gestartet`). The elaborator admits only names of parameterless functions of the unit, so no name
    is dropped (`starts_laenge` below). -/
structure Starts (u : UProg) where
  roots : List (declOf u).Fn
  hands : List (declOf u).Fn
  gestartet : List (declOf u).Fn

/-- Names of functions of the unit as functions of the declaration. -/
def fnsVon (u : UProg) (ns : List String) : List (declOf u).Fn :=
  ns.filterMap fun n => (fnIdx u.fns n).toOption

/-- The declared starts of a unit. -/
def startsOf (u : UProg) : Starts u :=
  ⟨fnsVon u u.roots, fnsVon u u.hands, fnsVon u u.gestartet⟩

/-- **THE PIPELINE WITH THE DECLARED STARTS**: `uebersetzeAllg`, and the starts of the unit it built (what the
    goal theorem's runtime premise reads: `Einheit.starts`, `Programm.unterbricht`, `Einheit.gestartet`). -/
def uebersetzeMitStarts (s : String) :
    Except String (Σ u : UProg, Programm (declOf u) × List (declOf u).Fn × Starts u) :=
  match uebersetzeAllg s with
  | .error e => .error e
  | .ok ⟨u, P, fs⟩ => .ok ⟨u, P, fs, startsOf u⟩

/-- The starts ride the pipeline unchanged: same unit, same program. -/
theorem uebersetzeMitStarts_ok {s : String} {u : UProg} {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (h : uebersetzeAllg s = .ok ⟨u, P, fs⟩) :
    uebersetzeMitStarts s = .ok ⟨u, P, fs, startsOf u⟩ := by
  unfold uebersetzeMitStarts
  rw [h]

/-- A `filterMap` that drops nothing keeps the length. -/
theorem filterMap_laenge {α β : Type} (f : α → Option β) (ns : List α) (h : ∀ n ∈ ns, (f n).isSome = true) :
    (ns.filterMap f).length = ns.length := by
  induction ns with
  | nil => rfl
  | cons n rest ih =>
    have hr : ∀ m ∈ rest, (f m).isSome = true := fun m hm => h m (List.mem_cons_of_mem _ hm)
    have hn := h n (List.mem_cons_self ..)
    cases hx : f n with
    | none => rw [hx] at hn; cases hn
    | some b => simp [List.filterMap_cons, hx, ih hr]

/-- A name the unit knows is kept: `fnsVon` drops exactly the unknown names. -/
theorem fnsVon_laenge (u : UProg) (ns : List String) (h : ∀ n ∈ ns, (fnIdx u.fns n).toOption.isSome = true) :
    (fnsVon u ns).length = ns.length :=
  filterMap_laenge (β := Fin u.fns.length) (fun n => (fnIdx u.fns n).toOption) ns h

/-- The functions of a generically lowered program are numbered. -/
instance instDecEqDeclOfFn (u : UProg) : DecidableEq (declOf u).Fn :=
  inferInstanceAs (DecidableEq (Fin u.fns.length))


end Gabbro.Grammatik
