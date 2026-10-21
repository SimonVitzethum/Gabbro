/-
  File:      Grammatik/Gen/Fein/Universum.lean
  Subject:   THE UNIVERSE OF THE FINE CELLS: which fine cells the typing of the model allows (`moeglich`), as a finite
             list (`uF`), and the theorem that a cell is in the list when it is allowed (`uF_vollst`).

  The constructor table `kTab` is GENERATED from the model (the result type of every expression constructor, whether
  a constructor needs the loop context, whether it is a foreign body, and per child: its family, the type class an
  expression child must have, the loop context of a statement child). `Gen/Fein/Satz.lean` proves that every fine
  cell of every program is allowed, so a wrong row cannot hide a cell: it stops that proof.
-/
import Grammatik.Gen.Fein.Zellen

namespace Gabbro.Grammatik.Gen.Fein

/-- A row of the constructor table: the type class of the result (`none`: any), whether the constructor needs the
    loop context, whether it is a foreign body, and the children (family, required type class of an expression
    child, loop context of a statement child: `none` the node's own). -/
structure Zeile where
  erg : Option Nat
  lnoetig : Bool
  fremd : Bool
  kinder : List (Nat × Option Nat × Option Bool)
  deriving DecidableEq, Repr

/-- **The constructor table**, by family and constructor (GENERATED from the model, `Gen/Fein/Zellen.lean`). -/
def kTab : List (List Zeile) := [
  -- Expr
  [⟨some 0, false, false, []⟩ /- lit -/,
    ⟨some 1, false, false, []⟩ /- tru -/,
    ⟨some 1, false, false, []⟩ /- fls -/,
    ⟨none, false, false, []⟩ /- var -/,
    ⟨none, false, false, []⟩ /- glob -/,
    ⟨none, false, false, [(0, some 0, none)]⟩ /- slot -/,
    ⟨none, false, false, [(0, some 8, none), (0, some 0, none)]⟩ /- thru -/,
    ⟨some 8, false, false, []⟩ /- ptrOf -/,
    ⟨some 7, false, false, []⟩ /- fnref -/,
    ⟨none, false, false, []⟩ /- oldG -/,
    ⟨none, false, false, [(0, some 0, none)]⟩ /- oldS -/,
    ⟨some 0, false, false, [(0, some 0, none)]⟩ /- widen -/,
    ⟨some 0, false, false, [(0, some 0, none), (0, some 0, none)]⟩ /- add -/,
    ⟨some 0, false, false, [(0, some 0, none), (0, some 0, none)]⟩ /- sub -/,
    ⟨some 0, false, false, [(0, some 0, none)]⟩ /- neg -/,
    ⟨some 0, false, false, [(0, some 0, none), (0, some 0, none)]⟩ /- mul -/,
    ⟨some 0, false, false, [(0, some 0, none), (0, some 0, none)]⟩ /- div -/,
    ⟨some 0, false, false, [(0, some 0, none), (0, some 0, none)]⟩ /- rem -/,
    ⟨some 0, false, false, [(0, some 0, none), (0, some 0, none)]⟩ /- sdiv -/,
    ⟨some 0, false, false, [(0, some 0, none), (0, some 0, none)]⟩ /- srem -/,
    ⟨some 0, false, false, [(0, some 0, none)]⟩ /- getBytes -/,
    ⟨some 0, false, false, [(0, some 0, none), (0, some 0, none)]⟩ /- band -/,
    ⟨some 0, false, false, [(0, some 0, none), (0, some 0, none)]⟩ /- bor -/,
    ⟨some 0, false, false, [(0, some 0, none), (0, some 0, none)]⟩ /- bxor -/,
    ⟨some 0, false, false, [(0, some 0, none), (0, some 0, none)]⟩ /- shl -/,
    ⟨some 0, false, false, [(0, some 0, none), (0, some 0, none)]⟩ /- shr -/,
    ⟨some 1, false, false, [(0, some 0, none), (0, some 0, none)]⟩ /- lt -/,
    ⟨some 1, false, false, [(0, some 0, none), (0, some 0, none)]⟩ /- le -/,
    ⟨some 1, false, false, [(0, some 0, none), (0, some 0, none)]⟩ /- eq -/,
    ⟨some 1, false, false, [(0, some 6, none), (0, some 6, none)]⟩ /- fllt -/,
    ⟨some 1, false, false, [(0, some 6, none), (0, some 6, none)]⟩ /- flle -/,
    ⟨some 1, false, false, [(0, some 1, none), (0, some 1, none)]⟩ /- and -/,
    ⟨some 1, false, false, [(0, some 1, none), (0, some 1, none)]⟩ /- or -/,
    ⟨some 1, false, false, [(0, some 1, none)]⟩ /- not -/,
    ⟨some 2, false, false, []⟩ /- none -/,
    ⟨some 2, false, false, [(0, some 0, none)]⟩ /- some -/,
    ⟨some 1, false, false, [(0, some 2, none)]⟩ /- istSome -/,
    ⟨some 3, false, false, [(1, none, none)]⟩ /- case -/,
    ⟨some 4, false, false, []⟩ /- why -/,
    ⟨some 1, false, false, [(0, some 1, none)]⟩ /- forallSlots -/,
    ⟨some 1, false, false, [(0, some 1, none)]⟩ /- existsSlots -/,
    ⟨some 1, false, false, [(0, some 0, none), (0, some 0, none)]⟩ /- reaches -/],
  -- NutzlastExpr
  [⟨none, false, false, []⟩ /- empty -/,
    ⟨none, false, false, [(0, some 0, none)]⟩ /- num -/],
  -- Args
  [⟨none, false, false, []⟩ /- nil -/,
    ⟨none, false, false, [(0, none, none), (2, none, none)]⟩ /- cons -/],
  -- ErgExpr
  [⟨none, false, false, []⟩ /- empty -/,
    ⟨none, false, false, [(0, none, none)]⟩ /- val -/],
  -- Stmt
  [⟨none, false, false, [(0, some 0, none), (0, none, none)]⟩ /- assignSlot -/,
    ⟨none, false, false, [(0, some 8, none), (0, some 0, none), (0, none, none)]⟩ /- assignThru -/,
    ⟨none, false, false, [(0, none, none)]⟩ /- assignGlob -/,
    ⟨none, false, false, [(0, some 0, none), (0, some 0, none)]⟩ /- putBytes -/,
    ⟨none, false, false, [(0, none, none)]⟩ /- assignVar -/,
    ⟨none, false, false, [(0, some 0, none)]⟩ /- shift -/,
    ⟨none, false, false, [(0, some 1, none), (5, none, none), (5, none, none)]⟩ /- ite -/,
    ⟨none, false, false, [(0, some 2, none), (5, none, none), (5, none, none)]⟩ /- onOption -/,
    ⟨none, false, false, [(0, some 3, none), (7, none, none)]⟩ /- onTag -/,
    ⟨none, false, false, [(0, some 4, none), (8, none, none)]⟩ /- onWhy -/,
    ⟨none, false, false, [(2, none, none)]⟩ /- call -/,
    ⟨none, false, false, [(0, some 7, none), (2, none, none)]⟩ /- callInd -/,
    ⟨none, false, false, [(5, none, none)]⟩ /- locks -/,
    ⟨none, false, false, [(5, none, none)]⟩ /- breaking -/,
    ⟨none, false, false, [(0, some 1, none), (5, none, some true)]⟩ /- traverse -/,
    ⟨none, false, false, [(0, some 1, none), (5, none, some true), (5, none, none)]⟩ /- retry -/,
    ⟨none, false, false, [(0, some 1, none), (5, none, some true)]⟩ /- forever -/,
    ⟨none, false, true, [(2, none, none)]⟩ /- axiomCall -/,
    ⟨none, false, false, [(0, none, none)]⟩ /- regWrite -/,
    ⟨none, false, false, []⟩ /- transition -/,
    ⟨none, false, false, [(0, none, none)]⟩ /- publish -/,
    ⟨none, false, false, []⟩ /- advances -/,
    ⟨none, false, false, []⟩ /- retires -/,
    ⟨none, false, false, [(3, none, none)]⟩ /- ret -/,
    ⟨none, false, false, []⟩ /- retWhy -/,
    ⟨none, true, false, []⟩ /- leave -/,
    ⟨none, true, false, []⟩ /- next -/],
  -- Block
  [⟨none, false, false, []⟩ /- nil -/,
    ⟨none, false, false, [(4, none, none), (5, none, none)]⟩ /- cons -/,
    ⟨none, false, false, [(0, none, none), (5, none, none)]⟩ /- bind -/,
    ⟨none, false, false, [(2, none, none), (5, none, none)]⟩ /- bindCall -/,
    ⟨none, false, false, [(0, some 7, none), (2, none, none), (5, none, none)]⟩ /- bindCallInd -/,
    ⟨none, false, false, [(2, none, none), (6, none, none), (5, none, none)]⟩ /- bindCallElse -/,
    ⟨none, false, true, [(2, none, none), (5, none, none)]⟩ /- bindAxiom -/,
    ⟨none, false, true, [(2, none, none), (6, none, none), (5, none, none)]⟩ /- bindAxiomElse -/,
    ⟨none, false, false, [(5, none, none)]⟩ /- regRead -/,
    ⟨none, false, false, [(0, some 1, none), (6, none, none), (5, none, none)]⟩ /- regReadElse -/,
    ⟨none, false, false, [(5, none, none)]⟩ /- awaits -/,
    ⟨none, false, false, [(0, none, none), (5, none, none)]⟩ /- exchange -/,
    ⟨none, false, false, [(0, some 0, none), (6, none, none), (5, none, none)]⟩ /- narrow -/,
    ⟨none, false, false, [(0, some 1, none), (6, none, none), (5, none, none)]⟩ /- check -/,
    ⟨none, false, false, [(0, some 6, none), (0, some 6, none), (5, none, none)]⟩ /- float -/,
    ⟨none, false, false, [(5, none, none)]⟩ /- floatLit -/,
    ⟨none, false, false, [(0, some 0, none), (5, none, none)]⟩ /- floatOf -/,
    ⟨none, false, false, [(0, some 6, none), (6, none, none), (5, none, none)]⟩ /- floatNarrow -/],
  -- Endblock
  [⟨none, false, false, [(3, none, none)]⟩ /- ret -/,
    ⟨none, false, false, []⟩ /- retWhy -/,
    ⟨none, true, false, []⟩ /- leave -/,
    ⟨none, true, false, []⟩ /- next -/,
    ⟨none, false, false, [(4, none, none), (6, none, none)]⟩ /- cons -/,
    ⟨none, false, false, [(0, none, none), (6, none, none)]⟩ /- bind -/,
    ⟨none, false, false, [(2, none, none), (6, none, none)]⟩ /- bindCall -/,
    ⟨none, false, false, [(2, none, none), (6, none, none), (6, none, none)]⟩ /- bindCallElse -/,
    ⟨none, false, true, [(2, none, none), (6, none, none)]⟩ /- bindAxiom -/,
    ⟨none, false, true, [(2, none, none), (6, none, none), (6, none, none)]⟩ /- bindAxiomElse -/,
    ⟨none, false, false, [(6, none, none)]⟩ /- regRead -/,
    ⟨none, false, false, [(0, some 1, none), (6, none, none), (6, none, none)]⟩ /- regReadElse -/,
    ⟨none, false, false, [(6, none, none)]⟩ /- awaits -/,
    ⟨none, false, false, [(0, some 7, none), (2, none, none), (6, none, none)]⟩ /- bindCallInd -/],
  -- Arms
  [⟨none, false, false, []⟩ /- nil -/,
    ⟨none, false, false, [(5, none, none), (7, none, none)]⟩ /- cons -/],
  -- GrundArms
  [⟨none, false, false, []⟩ /- nil -/,
    ⟨none, false, false, [(5, none, none), (8, none, none)]⟩ /- cons -/]]

/-- The row of a constructor. -/
def zeile (f k : Nat) : Option Zeile := (kTab.getD f [])[k]?

/-- The number of constructors of a family. -/
def kAnzahl (f : Nat) : Nat := (kTab.getD f []).length

/-- A type class meets a requirement. -/
def kopfOk : Option Nat → Nat → Bool
  | none, h => decide (h < 9)
  | some q, h => q == h

/-- The type classes of the expression children meet their requirements. -/
def koepfeOk : List (Option Nat) → List Nat → Bool
  | [], [] => true
  | q :: qs, h :: hs => kopfOk q h && koepfeOk qs hs
  | _, _ => false

/-- An expression constructor can have the type class `h`. -/
def ergPasst (k h : Nat) : Bool :=
  match zeile 0 k with
  | some r => (match r.erg with | none => decide (h < 9) | some q => q == h)
  | none => false

/-- A constructor can stand in the loop context `l`. -/
def lPasst (f k : Nat) (l : Bool) : Bool :=
  match zeile f k with
  | some r => !r.fremd && (!r.lnoetig || l)
  | none => false

/-- The requirements of the expression children. -/
def exprReqs (ks : List (Nat × Option Nat × Option Bool)) : List (Option Nat) :=
  ks.filterMap fun c => if c.1 = 0 then some c.2.1 else none

/-- A child of family `cf`, requirement `q`, loop context `lk` can be constructor `k`. -/
def kindOk (cf : Nat) (q : Option Nat) (lk : Bool) (k : Nat) : Bool :=
  if cf = 0 then (List.range 9).any (fun i => kopfOk q i && ergPasst k i) else lPasst cf k lk

/-- The data of a cell fit its row. -/
def datenOk (r : Zeile) (l : Bool) : Nat → List Nat → Bool
  | 0, hs => koepfeOk (exprReqs r.kinder) hs
  | 1, [p, cf, k] => match r.kinder[p]? with
      | some c => cf == c.1 && kindOk cf c.2.1 (c.2.2.getD l) k
      | none => false
  | _, _ => false

/-- **A fine cell the typing allows**: its constructor exists, is no foreign body, stands in its loop context (an
    expression has none), and its data fit. -/
def moeglich (c : FZelle) : Bool :=
  match zeile c.fam c.kon with
  | none => false
  | some r => (decide (4 ≤ c.fam) || !c.l) && !r.fremd && (!r.lnoetig || c.l) && datenOk r c.l c.art c.daten

/-! ## The list -/

/-- The type classes a requirement allows. -/
def kopfListe : Option Nat → List Nat
  | none => List.range 9
  | some q => [q]

/-- The data of a constructor cell. -/
def koepfeListe : List (Option Nat) → List (List Nat)
  | [] => [[]]
  | q :: qs => (kopfListe q).flatMap fun h => (koepfeListe qs).map (h :: ·)

/-- The data of a row's cells of kind `art`. -/
def datenListe (r : Zeile) : Nat → List (List Nat)
  | 0 => koepfeListe (exprReqs r.kinder)
  | _ => (List.range r.kinder.length).flatMap fun p =>
      let cf := (r.kinder.getD p (0, none, none)).1
      (List.range (kAnzahl cf)).map fun k => [p, cf, k]

/-- **The universe**: every allowed fine cell. -/
def uF : List FZelle :=
  ((List.range 9).flatMap fun f => (List.range (kAnzahl f)).flatMap fun k =>
    match zeile f k with
    | none => []
    | some r => [0, 1].flatMap fun art => [false, true].flatMap fun l =>
        (datenListe r art).map fun d => (⟨art, f, k, l, d⟩ : FZelle)).filter moeglich

theorem zeile_lt {f k : Nat} {r : Zeile} (h : zeile f k = some r) : f < 9 ∧ k < kAnzahl f := by
  unfold zeile at h
  refine ⟨?_, ?_⟩
  · rcases Nat.lt_or_ge f 9 with hf | hf
    · exact hf
    · exfalso
      have : kTab.getD f [] = [] := by
        unfold List.getD
        rw [List.getElem?_eq_none (by simp [kTab]; omega)]
        rfl
      rw [this] at h
      simp at h
  · exact (List.getElem?_eq_some_iff.1 h).1

theorem kopf_mem {q : Option Nat} {h : Nat} (hq : kopfOk q h = true) : h ∈ kopfListe q := by
  cases q with
  | none => simp [kopfOk, kopfListe] at *; exact hq
  | some q => simp [kopfOk, kopfListe] at *; exact hq.symm

theorem koepfe_mem : ∀ {qs : List (Option Nat)} {hs : List Nat}, koepfeOk qs hs = true → hs ∈ koepfeListe qs
  | [], [], _ => by simp [koepfeListe]
  | q :: qs, h :: hs, hk => by
    simp only [koepfeOk, Bool.and_eq_true] at hk
    simp only [koepfeListe, List.mem_flatMap, List.mem_map]
    exact ⟨h, kopf_mem hk.1, hs, koepfe_mem hk.2, rfl⟩
  | [], _ :: _, hk => by simp [koepfeOk] at hk
  | _ :: _, [], hk => by simp [koepfeOk] at hk

theorem ergPasst_lt {k h : Nat} (he : ergPasst k h = true) : k < kAnzahl 0 := by
  unfold ergPasst at he
  split at he
  · next r hr => exact (zeile_lt hr).2
  · simp at he

theorem lPasst_lt {f k : Nat} {l : Bool} (he : lPasst f k l = true) : k < kAnzahl f := by
  unfold lPasst at he
  split at he
  · next r hr => exact (zeile_lt hr).2
  · simp at he

theorem kindOk_lt {cf k : Nat} {q : Option Nat} {lk : Bool} (h : kindOk cf q lk k = true) : k < kAnzahl cf := by
  unfold kindOk at h
  split at h
  · next hc =>
    subst hc
    obtain ⟨i, _, hi⟩ := List.any_eq_true.1 h
    exact ergPasst_lt (Bool.and_eq_true _ _ ▸ hi).2
  · exact lPasst_lt h

theorem daten_mem {r : Zeile} {l : Bool} {art : Nat} {d : List Nat} (h : datenOk r l art d = true) :
    d ∈ datenListe r art := by
  match art, d, h with
  | 0, hs, h => exact koepfe_mem h
  | 1, [p, cf, k], h =>
    simp only [datenOk] at h
    split at h
    · next c hc =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, hk⟩ := h
      have hp := (List.getElem?_eq_some_iff.1 hc)
      simp only [datenListe, List.mem_flatMap, List.mem_range, List.mem_map]
      refine ⟨p, hp.1, k, ?_, ?_⟩
      · have : (r.kinder.getD p (0, none, none)).1 = c.1 := by
          simp [List.getD, hc]
        rw [this]; exact kindOk_lt hk
      · simp [List.getD, hc]
    · simp at h
  | art + 2, d, h => simp [datenOk] at h
  | 1, [], h => simp [datenOk] at h
  | 1, [_], h => simp [datenOk] at h
  | 1, [_, _], h => simp [datenOk] at h
  | 1, _ :: _ :: _ :: _ :: _, h => simp [datenOk] at h

/-- **The universe is complete**: every allowed cell is in the list. -/
theorem uF_vollst {c : FZelle} (h : moeglich c = true) : c ∈ uF := by
  obtain ⟨art, f, k, l, d⟩ := c
  unfold moeglich at h
  split at h
  · simp at h
  · next r hr =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨_, _⟩, _⟩, hd⟩ := h
    obtain ⟨hf, hk⟩ := zeile_lt hr
    have hart : art = 0 ∨ art = 1 := by
      match art, hd with
      | 0, _ => exact Or.inl rfl
      | 1, _ => exact Or.inr rfl
      | a + 2, hd => simp [datenOk] at hd
    unfold uF
    refine List.mem_filter.2 ⟨?_, ?_⟩
    · simp only [List.mem_flatMap, List.mem_range]
      refine ⟨f, hf, k, hk, ?_⟩
      rw [hr]
      simp only [List.mem_flatMap, List.mem_cons, List.mem_map, List.not_mem_nil, or_false]
      refine ⟨art, hart, l, by cases l <;> simp, d, daten_mem hd, rfl⟩
    · unfold moeglich
      simp only [hr, Bool.and_eq_true]
      exact ⟨⟨⟨by assumption, by assumption⟩, by assumption⟩, hd⟩

end Gabbro.Grammatik.Gen.Fein
