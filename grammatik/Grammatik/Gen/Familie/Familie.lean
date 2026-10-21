/-
  File:      Grammatik/Gen/Familie/Familie.lean
  Subject:   THE FAMILY OF DECLARATIONS: small concrete declarations that together exercise every field and every
             variation of `Deklaration` (tables and fields with ranges and transitions, statics, locks with ranks and
             masks, atomics with payload, marks with stages and owners, function signatures with parameters, results,
             reasons, held locks, write rights, consumed and produced marks, foreign bodies, device registers of every
             class, invariants over several tables, function pointers, floats, sums, pointers). One declaration
             exercises few features, because the program generator is exponential in what the declaration offers.

             For every member: the numeric alphabet derived from it (`Spez.zahlen`), the lock family `S` (the maximal
             one: every guarded carrier protected by its lock), and the declared starts `ws` the validity question is
             asked for. The generator's theorems are ∀-quantified over a declaration with its enumerations, so they
             hold for every member (`fam_gueltig_vollst`, `fam_bad_vollst`).
-/
import Grammatik.Gen.Familie.Spez
import Grammatik.Gen.Erzeuger.Gueltig

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

/-! ## The numeric alphabet of a specification -/

/-- The integers a type names. -/
def tyInts : Ty → List Int
  | .int lo hi => [lo, hi]
  | .opt n => [n]
  | .sum cs => cs.flatMap fun | none => [] | some (lo, hi) => [lo, hi]
  | _ => []

/-- The naturals a type names. -/
def tyNats : Ty → List Nat
  | .why n => [n]
  | .fnptr n => [n]
  | .ptr n _ => [n]
  | _ => []

/-- The float bounds a type names. -/
def tyPaare : Ty → List (Int × Int)
  | .fl lo hi => [lo, hi]
  | _ => []

/-- The types a specification names. -/
def Spez.typen (z : Spez) : List Ty :=
  z.tabs.flatMap (fun (t : TabZ) => t.felder.map (fun (f : FeldZ) => f.typ)) ++ z.globs.map (fun (g : GlobZ) => g.typ) ++
    z.sigs.flatMap (fun (s : SigZ) => s.params ++ s.erg.toList) ++
    z.axs.flatMap (fun (a : AxZ) => a.params ++ a.erg.toList) ++ z.regs.map (fun (r : RegZ) => r.typ)

/-- The alphabet of integers: 0, 1, the counts and their last index, every bound a type names, every transition
    endpoint. -/
def Spez.ganze (z : Spez) : List Int :=
  ([0, 1] ++ z.tabs.flatMap (fun (t : TabZ) => [t.count, t.count - 1] ++ t.felder.flatMap fun (f : FeldZ) =>
      f.erlaubt.flatMap fun (p : Int × Int) => [p.1, p.2]) ++ z.typen.flatMap tyInts).eraseDups

/-- The alphabet of naturals: 0, 1, the table numbers, every number a type names, the reasons of a signature; the
    widths and byte counts 2 and 8 only where the declaration has a byte. -/
def Spez.naturen (z : Spez) : List Nat :=
  ([0, 1] ++ (if z.typen.any (fun τ => match τ with | .int _ 255 => true | _ => false) then [2, 8] else []) ++
    (List.range z.tabs.length) ++ z.typen.flatMap tyNats ++ z.sigs.map (fun (s : SigZ) => s.gruende) ++
    z.axs.map (fun (a : AxZ) => a.gruende)).eraseDups

/-- The alphabet of float ranges: the ranges of the float types the specification declares. -/
def Spez.paare (z : Spez) : List (Int × Int) := (z.typen.flatMap tyPaare).eraseDups

/-- The alphabet of BOUNDS: every bound a type names, the first and the last index of a table, the transition
    endpoints. -/
def Spez.schranken (z : Spez) : List Int :=
  (([0] : List Int) ++ z.tabs.flatMap (fun (t : TabZ) => [t.count - 1] ++ t.felder.flatMap fun (f : FeldZ) =>
      f.erlaubt.flatMap fun (p : Int × Int) => [p.1, p.2]) ++ z.typen.flatMap tyInts).eraseDups

/-- The alphabet of VALUES (literals, masks): 0, 1 and the upper bound of every type. -/
def Spez.werte (z : Spez) : List Int :=
  (([0, 1] : List Int) ++ z.typen.flatMap fun (τ : Ty) => match τ with | .int _ hi => [hi] | _ => []).eraseDups

/-- The sum types of a specification: the case lists of its tagged types (and the empty list). -/
def Spez.summen (z : Spez) : List (List (Option (Int × Int))) :=
  ([] :: z.typen.filterMap fun (τ : Ty) => match τ with | .sum cs => some cs | _ => none).eraseDups

/-- The types a `let`-bound expression may have: the types the declaration names, the index of every table, `bool`. -/
def Spez.bindTypen (z : Spez) : List Ty :=
  (([Ty.bool] : List Ty) ++ z.typen ++ z.tabs.map (fun (t : TabZ) => Ty.index t.count)).eraseDups

/-- **The numeric scheme of a specification**: the canonical alphabet derived from it. -/
def Spez.zahlen (z : Spez) : Zahlen := Zahlen.kanon z.schranken z.werte z.naturen z.paare z.summen z.bindTypen

/-! ## The parameters of a declaration -/

/-- The carriers of a declaration: every table and every static. -/
def Spez.traegerListe (z : Spez) : List (z.deklaration.Tab ⊕ z.deklaration.Glob) :=
  (List.finRange z.tabs.length).map Sum.inl ++ (List.finRange z.globs.length).map Sum.inr

/-- **The maximal lock family**: lock `L` protects every carrier it guards. -/
def Spez.sperreMax (z : Spez) : SperrInv z.deklaration where
  orte := fun L => (z.traegerListe.filter fun c => decide (L ∈ waechterVon c))
  inv := fun _ _ => true

/-- The empty lock family. -/
def Spez.sperreLeer (z : Spez) : SperrInv z.deklaration := SperrInv.leer z.deklaration

/-- **The declared starts** the question is asked for: each function alone, each function declared twice (a pool),
    every function once. -/
def Spez.startFamilie (z : Spez) : List (List z.deklaration.Fn) :=
  (List.finRange z.fns.length).map (fun f => [f]) ++ (List.finRange z.fns.length).map (fun f => [f, f]) ++
    [List.finRange z.fns.length]

/-- The functions that can be a start: no held lock by signature, no reasons. -/
def Spez.wurzeln (z : Spez) : List z.deklaration.Fn :=
  (List.finRange z.fns.length).filter fun f =>
    (z.haelt (z.fns.get f)).isEmpty && (z.sigRoh (z.fns.get f)).gruende == 0

/-! ## The members -/

private def u8 : Ty := .int 0 255
private def b1 : Ty := .int 0 1
private def i3 : Ty := .int 0 3

/-- 0 -- the least declaration: one table (count 2, one field `0 .. 3`), one static, one function that writes both. -/
def z0 : Spez where
  tabs := [{ count := 2, felder := [{ typ := i3 }] }]
  globs := [{ typ := b1 }]
  sigs := [{ schreibt := [0], gschreibt := [0] }]

/-- 1 -- locks: a table and a static guarded by locks of different ranks; a function that holds one by signature. -/
def z1 : Spez where
  tabs := [{ count := 2, felder := [{ typ := i3 }], sperre := some 0, geteilt := true }]
  globs := [{ typ := b1, sperre := some 1, geteilt := true }]
  locks := [{ rang := 1 }, { rang := 2 }]
  sigs := [{ schreibt := [0], gschreibt := [0] }, { haelt := [0], schreibt := [0], boden := some 2 }]
  fns := [0, 1]

/-- 2 -- a lock that masks interrupts (a handler may take it). -/
def z2 : Spez where
  tabs := [{ count := 2, felder := [{ typ := i3 }], sperre := some 0, geteilt := true }]
  locks := [{ rang := 1, maskiert := true }]
  sigs := [{ schreibt := [0] }]

/-- 3 -- atomics: a static that publishes a payload, a plain atomic, a shared one with a guard. -/
def z3 : Spez where
  globs := [{ typ := b1, atomar := true, nutzlast := [1], geteilt := true },
            { typ := i3, geteilt := false },
            { typ := b1, atomar := true, geteilt := true }]
  sigs := [{ gschreibt := [0, 1, 2] }]

/-- 4 -- marks: a table owned by a mark, a function that consumes and produces marks of different stages. -/
def z4 : Spez where
  tabs := [{ count := 2, felder := [{ typ := i3 }], eigner := some 0 }]
  marken := [3, 2]
  sigs := [{ schreibt := [0] }, { konsumiert := [(1, 0)], produziert := [(1, 1)] }, { produziert := [(0, 0)] }]
  fns := [0, 1, 2]

/-- 5 -- calls: parameters, a result, a callee with reasons, two functions of one signature (a function pointer). -/
def z5 : Spez where
  tabs := [{ count := 2, felder := [{ typ := i3 }] }]
  sigs := [{ params := [i3], erg := some i3, schreibt := [0] }, { gruende := 2, erg := some b1 },
           { erg := some i3 }]
  fns := [0, 0, 1, 2]

/-- 6 -- foreign bodies: a result, no result, `never`, a fallible one (a channel of two reasons). -/
def z6 : Spez where
  tabs := [{ count := 2, felder := [{ typ := i3 }] }]
  globs := [{ typ := b1 }]
  axs := [{ params := [i3], erg := some i3 }, { schreibt := [0], gschreibt := [0] }, { erg := some .never },
          { params := [b1], erg := some i3, gruende := 2 }, { erg := some (.int 1 0) }]
  sigs := [{ schreibt := [0], gschreibt := [0] }]

/-- 7 -- device registers of every class, a mirror, a register without a promise. -/
def z7 : Spez where
  tabs := [{ count := 1, felder := [{ typ := i3 }] }]
  regs := [{ typ := i3, klasse := .rw, traeger := [0] }, { typ := i3, klasse := .w, spiegel := some 0 },
           { typ := b1, klasse := .rc }, { typ := b1, klasse := .w1c, zusage := false },
           { typ := i3, klasse := .r, zusage := false }]
  sigs := [{ schreibt := [0] }]

/-- 8 -- an invariant over two tables guarded by a lock: the function that writes one holds the lock. -/
def z8 : Spez where
  tabs := [{ count := 2, felder := [{ typ := i3 }], sperre := some 0, geteilt := true },
           { count := 2, felder := [{ typ := b1 }], sperre := some 0, geteilt := true }]
  locks := [{ rang := 1 }]
  invs := [{ traeger := [0, 1] }]
  sigs := [{ schreibt := [0] }, { schreibt := [1] }]
  fns := [0, 1]

/-- 9 -- a `state` field with transitions, a byte field, a chain (`option index`) field. -/
def z9 : Spez where
  tabs := [{ count := 4, felder := [{ typ := .int 0 2, erlaubt := [(0, 1), (1, 2)] }, { typ := u8 },
                                    { typ := .opt 4 }] }]
  sigs := [{ schreibt := [0] }]

/-- 10 -- two tables (pointers name them by number), a function that takes a pointer. -/
def z10 : Spez where
  tabs := [{ count := 2, felder := [{ typ := i3 }] }, { count := 2, felder := [{ typ := b1 }] }]
  sigs := [{ params := [.ptr 0 true], schreibt := [0, 1] }, { params := [.ptr 1 false] }]
  fns := [0, 1]

/-- 11 -- floats: a static and a parameter of float type. -/
def z11 : Spez where
  globs := [{ typ := .fl (0, 1) (1, 1) }]
  sigs := [{ params := [.fl (0, 1) (1, 1)], gschreibt := [0] }]

/-- 12 -- a tagged type and a reason as parameters. -/
def z12 : Spez where
  tabs := [{ count := 2, felder := [{ typ := .sum [none, some (0, 3)] }] }]
  sigs := [{ params := [.sum [none, some (0, 3)], .why 2], schreibt := [0] }]

/-- 13 -- an arena: a slot table, a used counter and a committed prefix. -/
def z13 : Spez where
  tabs := [{ count := 2, felder := [{ typ := i3 }] }]
  globs := [{ typ := .int 0 2 }, { typ := .int 0 2 }]
  sigs := [{ schreibt := [0], gschreibt := [0, 1] }]

/-- 14 -- two writers of the same carriers (the race and pool questions), one with a lock. -/
def z14 : Spez where
  tabs := [{ count := 2, felder := [{ typ := i3 }] }, { count := 2, felder := [{ typ := i3 }], sperre := some 0, geteilt := true }]
  globs := [{ typ := b1 }]
  locks := [{ rang := 1 }]
  sigs := [{ schreibt := [0], gschreibt := [0] }, { schreibt := [1], haelt := [0] }]
  fns := [0, 1]

/-- 15 -- two functions that write the same unguarded table (a second start races with the first). -/
def z15 : Spez where
  tabs := [{ count := 2, felder := [{ typ := b1 }] }]
  sigs := [{ schreibt := [0] }, { schreibt := [0] }]
  fns := [0, 1]

/-- **The family**. -/
def familie : List Spez := [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15]

/-- The members of the family. -/
abbrev Fam := Fin familie.length

/-- The declaration of a member. -/
def famD (s : Fam) : Deklaration := (familie.get s).deklaration

/-- The enumerations of a member. -/
instance famA (s : Fam) : Aufz (famD s) := (familie.get s).aufz

/-- The numeric scheme of a member. -/
def famZ (s : Fam) : Zahlen := (familie.get s).zahlen

theorem fam_alle (s : Fam) : s ∈ List.finRange familie.length := List.mem_finRange s

/-- **(C) over the family, valid**: for EVERY member, every lock family, every list of starts and every skeleton
    whose program the checker accepts, with every body of size at most `n` under the member's numeric scheme, the
    program is generated at its size. -/
theorem fam_gueltig_vollst (s : Fam) :
    letI := famA s
    letI := famZ s
    ∀ (S : SperrInv (famD s)) (ls : List (famD s).Lock) (cs : List ((famD s).Tab ⊕ (famD s).Glob))
      (ws : List (famD s).Fn) (n : Nat) (h : Haut (famD s)),
      AkzeptiertX h.programm S Aufz.fn ls cs ws = true → (∀ f, groesseEnd (h.rumpf f) ≤ n) →
      (∀ f, groesseEnd (h.rumpf f) < unendlich) → h.programm ∈ genGueltig S Aufz.fn ls cs ws n (groesseHaut h) := by
  intro S ls cs ws n h hv hn hu
  exact @gueltig_vollst (famD s) (famA s) (famZ s) S _ ls cs ws (fun g => List.mem_finRange g) n h hv hn hu

/-- **(C) over the family, single fault**: the same for the programs refused by exactly one component. -/
theorem fam_bad_vollst (s : Fam) :
    letI := famA s
    letI := famZ s
    ∀ (c : Fin 10) (S : SperrInv (famD s)) (ls : List (famD s).Lock) (cs : List ((famD s).Tab ⊕ (famD s).Glob))
      (ws : List (famD s).Fn) (n : Nat) (h : Haut (famD s)),
      NurAn c h.programm S Aufz.fn ls cs ws → (∀ f, groesseEnd (h.rumpf f) ≤ n) →
      (∀ f, groesseEnd (h.rumpf f) < unendlich) → h.programm ∈ genBad c S Aufz.fn ls cs ws n (groesseHaut h) := by
  intro c S ls cs ws n h hv hn hu
  exact @bad_vollst (famD s) (famA s) (famZ s) S _ ls cs ws (fun g => List.mem_finRange g) c n h hv hn hu

end Gabbro.Grammatik.Gen
