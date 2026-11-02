module

public import Grammatik.Parser.Elab.ExportControl
public import Grammatik.Parser.Elab.UebersetzeSum
public import Grammatik.Bausteine.Arena.ArenaZucker
public import Grammatik.Parser.Namen.Oeffentlich
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
public import Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
public import Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
public import Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Export

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
set_option maxRecDepth 100000

/-- What `lowerEach` checks, per function. -/
theorem lowerEach_all_ok (u : UProg) (fs : List (Fin u.fns.length))
    (f : Fin u.fns.length) (hm : f ∈ fs)
    (h : lowerEach u fs = .ok ()) :
    ∃ v, lowerFnAt u f = .ok v := by
  induction fs with
  | nil =>
    simp only [List.not_mem_nil] at hm
  | cons g gs ih =>
    simp only [List.mem_cons] at hm
    cases hg : lowerFnAt u g with
    | error e =>
      have hE : lowerEach u (g :: gs) = .error e := by
        simp only [lowerEach, hg]
      rw [hE] at h
      simp only [reduceCtorEq] at h
    | ok v =>
      have hO : lowerEach u (g :: gs) = lowerEach u gs := by
        simp only [lowerEach, hg]
      cases hm with
      | inl he =>
        subst he
        exact ⟨v, hg⟩
      | inr hm' =>
        rw [hO] at h
        exact ih hm' h

/-- The lowered pair at an index known good. -/
def lowerAtPair (u : UProg) (f : Fin u.fns.length)
    (h : ∃ v, lowerFnAt u f = .ok v) :
    EnsTy u f × RumpTy u f × ReqTy u f :=
  match hm : lowerFnAt u f with
  | .ok v => v
  | .error e => by
    exfalso
    obtain ⟨v, hv⟩ := h
    rw [hv] at hm
    simp only [reduceCtorEq] at hm

/-- The type of a lowered invariant: a predicate over no parameter, under the guards of its carriers. -/
abbrev InvTy (u : UProg) (i : Fin u.invs.length) := Expr (declOf u) [] (invSicht (declOf u) i) .bool

/-- The requires of a function: `.tru` without a `requires` predicate (what the conjunction of none is),
    else the lowered conjunction. -/
def reqOf (u : UProg) (R : ∀ f : Fin u.fns.length, ReqTy u f) (f : Fin u.fns.length) : ReqTy u f :=
  if (fnAt u f).needs = [] then Expr.tru else R f

theorem reqOf_leer (u : UProg) (R : ∀ f : Fin u.fns.length, ReqTy u f) (f : Fin u.fns.length)
    (h : (fnAt u f).needs = []) : reqOf u R f = Expr.tru := by
  unfold reqOf
  rw [if_pos h]

/-- Assemble lowered functions to a program (no contract
    content in `requires`, per-function `ensures` and bodies). -/
def progOfFn (u : UProg) (E : ∀ f : Fin u.fns.length, EnsTy u f)
    (B : ∀ f : Fin u.fns.length, RumpTy u f) (R : ∀ f : Fin u.fns.length, ReqTy u f)
    (I : ∀ i : Fin u.invs.length, InvTy u i) :
    Programm (declOf u) where
  invariante := I
  requires := fun f => reqOf u R f
  ensures := fun f => E f
  rumpf := fun f => B f
  unterbricht := fun f => u.hands.any (fun n => strEq n (fnAt u f).name)

/-- The function of no parameter in whose scope an invariant is read. -/
def leerFn : UFn :=
  { name := "", params := [], kinds := [], res := none, held := [], puts := [], gives := [], body := [], ret := .empty }

/-- A lowered invariant reads only its declared carriers: every carrier its predicate reads is one of the
    invariant's carriers (tables and statics, C05) -- `InvTraeger` of the exported unit, decided. -/
def invReadsOk (u : UProg) (i : Fin u.invs.length) (e : InvTy u i) : Bool :=
  e.orte.all fun (c : Fin u.tabs.length ⊕ Fin u.globs.length) => decide (c ∈ invTraeger u i)

/-- One invariant, lowered. It is REFUSED -- never lowered over a shortened carrier list -- where a writer of a
    carrier does not hold every guard lock of the carriers (`U003`, `invOkB`; `traegerD` would fall back to
    no carriers there), and where the predicate reads a carrier the invariant does not declare. -/
def lowerInvAt (u : UProg) (i : Fin u.invs.length) : Except String (InvTy u i) :=
  if invOkB u i then
    match lowEns u [] (invSicht (declOf u) i) leerFn none (u.invs.get i).pred with
    | .error e => .error e
    | .ok e =>
      if invReadsOk u i e then .ok e else .error "an invariant reads a carrier it does not declare"
  else .error "a writer of an invariant's carrier does not hold all its locks"

/-- What a lowered invariant guarantees: `U003` holds and the predicate reads only declared carriers. -/
theorem lowerInvAt_facts (u : UProg) (i : Fin u.invs.length) (v : InvTy u i)
    (h : lowerInvAt u i = .ok v) : invOkB u i = true ∧ invReadsOk u i v = true := by
  unfold lowerInvAt at h
  by_cases hok : invOkB u i = true
  · rw [if_pos hok] at h
    refine ⟨hok, ?_⟩
    cases hl : lowEns u [] (invSicht (declOf u) i) leerFn none (u.invs.get i).pred with
    | error e => simp only [hl, reduceCtorEq] at h
    | ok e =>
      simp only [hl] at h
      by_cases hr : invReadsOk u i e = true
      · rw [if_pos hr] at h
        cases h
        exact hr
      · rw [if_neg hr] at h
        cases h
  · rw [if_neg hok] at h
    cases h

/-- Every invariant lowers. -/
def lowerInvs (u : UProg) : List (Fin u.invs.length) → Except String Unit
  | [] => .ok ()
  | i :: is =>
    match lowerInvAt u i with
    | .error e => .error e
    | .ok _ => lowerInvs u is

theorem lowerInvs_all_ok (u : UProg) (is : List (Fin u.invs.length)) (i : Fin u.invs.length) (hm : i ∈ is)
    (h : lowerInvs u is = .ok ()) : ∃ v, lowerInvAt u i = .ok v := by
  induction is with
  | nil => simp only [List.not_mem_nil] at hm
  | cons j js ih =>
    simp only [List.mem_cons] at hm
    cases hj : lowerInvAt u j with
    | error e =>
      have hE : lowerInvs u (j :: js) = .error e := by simp only [lowerInvs, hj]
      rw [hE] at h
      simp only [reduceCtorEq] at h
    | ok v =>
      have hO : lowerInvs u (j :: js) = lowerInvs u js := by simp only [lowerInvs, hj]
      cases hm with
      | inl he => subst he; exact ⟨v, hj⟩
      | inr hm' => rw [hO] at h; exact ih hm' h

/-- The lowered invariant at an index known good. -/
def lowerInvGut (u : UProg) (i : Fin u.invs.length) (h : ∃ v, lowerInvAt u i = .ok v) : InvTy u i :=
  match hm : lowerInvAt u i with
  | .ok v => v
  | .error _ => by
    exfalso
    obtain ⟨v, hv⟩ := h
    rw [hv] at hm
    simp only [reduceCtorEq] at hm

/-- The generically lowered program: every function of the
    elaborated program over the declaration built from it. -/
def lowerAllg (u : UProg) :
    Except String (Programm (declOf u) × List (declOf u).Fn) :=
  match hI : lowerInvs u (List.finRange u.invs.length) with
  | .error e => .error e
  | .ok _ =>
  have wI : ∀ i : Fin u.invs.length, ∃ v, lowerInvAt u i = .ok v := fun i =>
    lowerInvs_all_ok u (List.finRange u.invs.length) i (List.mem_finRange i) hI
  match h : lowerEach u (List.finRange u.fns.length) with
  | .error e => .error e
  | .ok _ =>
    have w : ∀ f : Fin u.fns.length,
        ∃ v, lowerFnAt u f = .ok v := fun f =>
      lowerEach_all_ok u (List.finRange u.fns.length) f
        (List.mem_finRange f) h
    Measures.checkedProgram u (progOfFn u (fun f => (lowerAtPair u f (w f)).1)
      (fun f => (lowerAtPair u f (w f)).2.1) (fun f => (lowerAtPair u f (w f)).2.2)
      (fun i => lowerInvGut u i (wI i)))

/-- The lowered invariant at an index known good: `U003` holds and it reads only declared carriers. -/
theorem lowerInvGut_facts (u : UProg) (i : Fin u.invs.length) (h : ∃ v, lowerInvAt u i = .ok v) :
    invOkB u i = true ∧ invReadsOk u i (lowerInvGut u i h) = true := by
  unfold lowerInvGut
  split
  next v hm => exact lowerInvAt_facts u i v hm
  next e hm =>
    exfalso
    obtain ⟨v, hv⟩ := h
    rw [hv] at hm
    cases hm

/-- A lowered invariant reads only carriers in the declaration's carrier list (`InvTraeger`). -/
theorem lowerInvGut_orte (u : UProg) (i : Fin u.invs.length) (h : ∃ v, lowerInvAt u i = .ok v) :
    ∀ c ∈ (lowerInvGut u i h).orte, c ∈ (declOf u).traeger i := by
  intro c hc
  obtain ⟨hok, hr⟩ := lowerInvGut_facts u i h
  unfold invReadsOk at hr
  have hc' : c ∈ invTraeger u i := by
    have := List.all_eq_true.mp hr c hc
    simp only [decide_eq_true_eq] at this
    exact this
  show c ∈ traegerD u i
  rw [traegerD_of_ok u i hok]
  exact hc'

/-- **The exported unit keeps its whole declared carrier list and reads only it.** A unit that lowers has `U003`
    at every invariant, so the declaration's carriers of each invariant are ALL its carriers, tables and statics
    (never the empty fallback of `traegerD`), and the lowered predicate reads no other carrier. -/
theorem lowerAllg_traeger (u : UProg) (P : Programm (declOf u)) (fs : List (declOf u).Fn)
    (h : lowerAllg u = .ok (P, fs)) (i : Fin u.invs.length) :
    (declOf u).traeger i = invTraeger u i ∧
      ∀ c ∈ (P.invariante i).orte, c ∈ (declOf u).traeger i := by
  unfold lowerAllg at h
  split at h
  next e hI => cases h
  next x hI =>
    split at h
    · cases h
    · obtain ⟨rfl, -⟩ := Measures.checkedProgram_eq h
      have wI : ∀ j : Fin u.invs.length, ∃ v, lowerInvAt u j = .ok v := fun j =>
        lowerInvs_all_ok u (List.finRange u.invs.length) j (List.mem_finRange j) hI
      dsimp only [progOfFn]
      exact ⟨traegerD_of_ok u i (lowerInvGut_facts u i (wI i)).1,
        fun c hc => lowerInvGut_orte u i (wI i) c hc⟩

/-! ## 104 pins on the generically lowered program -/

/-- The fragment check on the generically lowered 104 program. -/
theorem lowerAllg104fragment :
    (match lowerAllg uExp104 with
      | .ok (P, fs) => programmImFragmentG P fs
      | .error _ => false) = true := by
  decide

/-- The footprint check on the generically lowered 104 program. -/
theorem lowerAllg104fuss :
    (match lowerAllg uExp104 with
      | .ok (P, fs) => fussOrtGB P fs
      | .error _ => false) = true := by
  decide

/-- Declaration data agreement, construct by construct: the
    generic declaration built from `uExp104` agrees with the
    exporter universe `G104_referenz.gD` (counts, ranges, ranks,
    guards, held sets, writes). -/
theorem lowerAllg104data :
    (declOf uExp104).count ⟨0, by decide⟩ = 2 ∧
    G104_referenz.gD.count G104_referenz.GTab.Konto = 2 ∧
    (declOf uExp104).typ ⟨0, by decide⟩ ⟨0, by decide⟩ =
      .int 0 100 ∧
    G104_referenz.gD.typ G104_referenz.GTab.Konto
      G104_referenz.GKontoFeld.stand = .int 0 100 ∧
    (declOf uExp104).rang ⟨0, by decide⟩ = 0 ∧
    G104_referenz.gD.rang G104_referenz.GLock.M = 0 ∧
    (declOf uExp104).braucht ⟨0, by decide⟩ =
      ([.inl (⟨0, by decide⟩ : Fin uExp104.locks.length)] :
        List ((declOf uExp104).Lock ⊕
          ((declOf uExp104).Marke × Nat))) ∧
    G104_referenz.gD.braucht G104_referenz.GTab.Konto =
      [.inl G104_referenz.GLock.M] ∧
    ((declOf uExp104).signatur ⟨0, by decide⟩).haelt =
      ([(⟨0, by decide⟩ : Fin uExp104.locks.length)] :
        List (declOf uExp104).Lock) ∧
    G104_referenz.gD.haelt G104_referenz.g_einzahlen =
      [G104_referenz.GLock.M] ∧
    ((declOf uExp104).signatur ⟨1, by decide⟩).haelt =
      ([(⟨0, by decide⟩ : Fin uExp104.locks.length)] :
        List (declOf uExp104).Lock) ∧
    G104_referenz.gD.haelt G104_referenz.g_lies =
      [G104_referenz.GLock.M] ∧
    ((declOf uExp104).signatur ⟨0, by decide⟩).schreibt
      ⟨0, by decide⟩ = true ∧
    (G104_referenz.gD.signatur
      G104_referenz.g_einzahlen).schreibt
      G104_referenz.GTab.Konto = true ∧
    ((declOf uExp104).signatur ⟨1, by decide⟩).schreibt
      ⟨0, by decide⟩ = false ∧
    (G104_referenz.gD.signatur
      G104_referenz.g_lies).schreibt
      G104_referenz.GTab.Konto = false := by
  decide

/-! ## The real-text lexer pin for 104 -/

-- SRC-BEGIN src104real
/-- The real `beispiele/0104-referenz.gab` text, one entry per source line (a long
    line cut again after a space). `zaehle-kette.py` compares the
    pieces against the file, byte for byte. WHY PIECES and not one
    literal: `Parser/Lexer.lean`'s `lex_ofList` -- one 2064-byte
    literal costs the kernel tens of gigabytes (O13). -/
def srcZeilen104 : List (List Char) :=
  ["// 104 -- The reference fixture as a ".toList,
   "real Gabbro program (lane 126).\n".toList,
   "//\n".toList,
   "// This is ".toList,
   "`grammatik/Grammatik/ReferenzB.lean` ".toList,
   "(`refD`/`refP`) in surface\n".toList,
   "// syntax: one table `Konto` of 2 slots ".toList,
   "with one `0 .. 100` field, guarded by\n".toList,
   "// the single lock `M`; `einzahlen` (one ".toList,
   "`0 .. 10` parameter, no result,\n".toList,
   "// writes the table, ensures the slot ".toList,
   "did not decrease) and `lies` (no\n".toList,
   "// parameters, one `0 .. 100` result, ".toList,
   "reads, ensures the answer equals the\n".toList,
   "// slot). Both run under the held lock ".toList,
   "(`requires Held(M)`, the `beispiele/01`\n".toList,
   "// idiom: the caller's duty, so the ".toList,
   "bodies touch the guarded slot ".toList,
   "directly).\n".toList,
   "// Not declared `concurrent`: both ".toList,
   "functions hold `M` by signature, and ".toList,
   "the\n".toList,
   "// start rule N240 (the goal theorem's ".toList,
   "`StartExklusiv`) forbids two threads\n".toList,
   "// starting in functions that share a ".toList,
   "signature lock. The earlier note: the ".toList,
   "declaration\n".toList,
   "// (lane 141: the certificate census ".toList,
   "classifies `concurrent` as erased -- ".toList,
   "the\n".toList,
   "// emitter writes nothing for it -- so ".toList,
   "the declaration passes stage 7 of\n".toList,
   "// `pruefe-emission.sh`). Threads cannot ".toList,
   "be driven from a C driver anyway, so\n".toList,
   "// the driver runs both threads one ".toList,
   "after the other -- the sequential\n".toList,
   "// composition the emitter produces: ".toList,
   "`einzahlen` like thread 1, then `lies`\n".toList,
   "// like thread 0. That is the observable ".toList,
   "half of the fixture\n".toList,
   "// (`refB_schreibt`: slot `0 -> 100`).\n".toList,
   "\n".toList,
   "module beispiel::referenz {\n".toList,
   "\n".toList,
   "const NKONTO : u32 = 2;\n".toList,
   "\n".toList,
   "type Betrag = u32 in 0 .. 10;\n".toList,
   "type Stand = u32 in 0 .. 100;\n".toList,
   "\n".toList,
   "table Konto count NKONTO {\n".toList,
   "    slot {\n".toList,
   "        stand : Stand,\n".toList,
   "    }\n".toList,
   "}\n".toList,
   "\n".toList,
   "lock M protects { stand } rank 0 held <= ".toList,
   "50 ops;\n".toList,
   "\n".toList,
   "impl fn einzahlen(k : ptr<normal, rw> ".toList,
   "Konto, i : index into Konto, b : ".toList,
   "Betrag)\n".toList,
   "    requires Held(M)\n".toList,
   "    ensures  old(k.slots[i].stand) <= ".toList,
   "k.slots[i].stand\n".toList,
   "    effects  { reads k.slots, writes ".toList,
   "k.slots, locks M }\n".toList,
   "    costs    <= 16 ops\n".toList,
   "{\n".toList,
   "    k.slots[i].stand = 100;\n".toList,
   "    lies(k, i);\n".toList,
   "}\n".toList,
   "\n".toList,
   "impl fn lies(k : ptr<normal, r> Konto, i ".toList,
   ": index into Konto) -> Stand\n".toList,
   "    requires Held(M)\n".toList,
   "    ensures  result == k.slots[i].stand\n".toList,
   "    effects  { reads k.slots, locks M }\n".toList,
   "    costs    <= 8 ops\n".toList,
   "{\n".toList,
   "    return k.slots[i].stand;\n".toList,
   "}\n".toList,
   "\n".toList,
   "\n".toList,
   "}\n".toList]
-- SRC-END src104real

/-- The pinned text as characters. -/
def srcQuelle104 : List Char := srcZeilen104.flatten

/-- The pinned text as the `String` the chain is indexed by. -/
def src104real : String := String.ofList srcQuelle104

set_option maxHeartbeats 4000000 in
/-- **THE REAL 104 TEXT LEXES TO `tt104`** -- over the CHARACTERS, which is
    the only form the kernel ever sees (O13): the pieces are short literals,
    and the whole scan costs a fraction of one long literal's decode. -/
theorem lexL104real : lexL srcQuelle104 = .ok tt104 := by
  decide

/-- The same, as a statement about the `String` the chain is indexed by.
    `lex_ofList` carries the pin across WITHOUT running the UTF-8 decoder,
    so this theorem is a rewrite and not a reduction. -/
theorem lex104real : lex src104real = .ok tt104 := by
  show lex (String.ofList srcQuelle104) = _
  rw [lex_ofList]
  exact lexL104real

/-! ## The 104 chain, end to end -/

/-- One theorem chaining every stage for 104: real-text lexing,
    deep parsing, elaboration, generic lowering, and the fragment
    and footprint checks on the lowered program. -/
theorem kette104 : lex src104real = .ok tt104 ∧
    beqTopTief (parseTopTief tt104) (.ok items104) = true ∧
    beqElabU (elabU items104) (.ok uExp104) = true ∧
    (match lowerAllg uExp104 with
      | .ok (P, fs) => programmImFragmentG P fs && fussOrtGB P fs
      | .error _ => false) = true := by
  refine ⟨lex104real, u104parse, u104elab, ?_⟩
  decide

/-! ## 108 preprocessing: `concurrent` stripping, bare-`u32` norms -/

/-- Bare `u32` as its full range (what the exporter computes
    with, per `Export108.lean` CUTS). -/
def u32Voll : STyp :=
  .range (.atom "u32") (.lit 0) (.lit 4294967295) false

/-- A type with bare `u32` normalised (lane 160 has no
    full-range rule by design; the normalisation lives here,
    never by editing `Uebersetze.lean`). -/
def normTypU32 : STyp → STyp
  | .atom a => if a == "u32" then u32Voll else .atom a
  | t => t

/-- A slot field with bare `u32` normalised. -/
def normFeldU32 (f : SFeld) : SFeld :=
  { f with ftyp := normTypU32 f.ftyp }

/-- A table part with bare `u32` normalised. -/
def normTabTeilU32 : STabTeil → STabTeil
  | .tSlot fds => .tSlot (fds.map normFeldU32)
  | t => t

/-- A function head with bare `u32` normalised (parameters and
    result). -/
def normSigU32 (s : FnSig) : FnSig :=
  { s with params := s.params.map (fun p => (p.1, normTypU32 p.2)), res := s.res.map normTypU32 }

/-- One item with bare `u32` normalised (no module recursion:
    `uMembers` unwraps the single module `elabU` supports). -/
def normU32Item : SItemTief → SItemTief
  | .tableT n v c a b g parts =>
    .tableT n v c a b g (parts.map normTabTeilU32)
  | .fnT s k => .fnT (normSigU32 s) k
  | it => it

/-- Bare `u32` normalised over a top-level list. -/
def normTopU32 : List SItemTief → List SItemTief
  | [] => []
  | it :: rest => normU32Item it :: normTopU32 rest

/-- The preprocessing of the bridge instances: check `pub` (`Oeffentlich.huelleZu`), resolve every name
    and open the modules
    (`Aufloesung.loese`: a unit of one name space is unwrapped as `uMembers` does), then normalise
    bare `u32`, before `elabU` (`concurrent` items are elaborated into the thread roots now). -/
def pre108 (items : List SItemTief) : List SItemTief :=
  if Oeffentlich.huelleZu items then normTopU32 (Aufloesung.loese items)
  -- An open export hull (or a `pub` where none may stand) refuses the unit: a lone `use` has no G form.
  else [.useT ["pub"]]

/-! ## 108 pins: strip, normalise, elaborate, lower -/

/-! ## C18 fixture: a closed static-array reset through the generic lowering -/

/-- **A unit with a static-array reset** (C18): `static mut A : [u8; 4]` and one writer that
    zeroes `[1, 3)` via `reset A at 1 count 2;`. Closed: literals only, no parameters. -/
def uReset : UProg :=
  { tabs := [], locks := [],
    fns := [{ name := "leere", params := [], kinds := [], res := none, held := [], puts := [],
              gputs := ["A"], gives := [], body := [.resetRange "A" (.lit 1) (.lit 2)],
              ret := .empty }],
    globs := [{ name := "A", ty := .wert (.arr (.int 0 255) 4), init := 0, var := true }] }

/-- The generic lowering accepts the reset unit: the range elaborates, checks, and expands
    into the typed array store. -/
theorem uReset_lower : (lowerAllg uReset).toOption.isSome = true := by decide

end Gabbro.Grammatik.Parser.UebersetzeAllg2
