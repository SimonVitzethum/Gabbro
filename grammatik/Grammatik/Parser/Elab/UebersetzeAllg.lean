/-
  File:      Grammatik/Parser/UebersetzeAllg.lean
  Subject:   T3 PART 5: generic lowering from source to the G program.

  Lane 160 (`Parser/Uebersetze.lean`) elaborates the parsed surface tree
  to plain data (`UProg`) generically, but lowers only onto the 104
  declaration universe (`G104_referenz.gD`). This file builds the
  declaration from the `UProg` itself, with index carriers (`Fin n`
  for tables, locks, fields and functions): `declOf : UProg ->
  Deklaration` and `lowerAllg : (u : UProg) -> Except String
  (Programm (declOf u) x List (declOf u).Fn)`.

  The 104 and 108 instances pin the fragment and footprint checks on
  the generically lowered programs (`by decide`), the data agreement
  with the exporter programs, the real-text lexer pin (comments lex
  away, no lexer change was needed), and one theorem chaining all
  stages for 104.
-/
import Grammatik.Parser.Elab.Uebersetze

namespace Gabbro.Grammatik.Parser.UebersetzeAllg

open Gabbro.Grammatik.Parser.Uebersetze

/-! ## Declaration data looked up from `UProg` -/

/-- The table at an index. -/
def tabAt (u : UProg) (t : Fin u.tabs.length) : UTab :=
  u.tabs.get t

/-- The lock at an index. -/
def lockAt (u : UProg) (l : Fin u.locks.length) : ULock :=
  u.locks.get l

/-- The function at an index. -/
def fnAt (u : UProg) (f : Fin u.fns.length) : UFn :=
  u.fns.get f

/-- The field count of a table. -/
def fieldCount (u : UProg) (t : Fin u.tabs.length) : Nat :=
  (tabAt u t).cols.length

/-- A table index by name (structural, so the `Fin` proof is free). -/
def tabIdx : (tabs : List UTab) → (n : String) → Except String (Fin tabs.length)
  | [], n => .error ("table unknown: " ++ n)
  | t :: rest, n =>
    if t.name == n then .ok 0
    else match tabIdx rest n with
      | .error e => .error e
      | .ok j => .ok j.succ

/-- A lock index by name. -/
def lockIdx : (locks : List ULock) → (n : String) → Except String (Fin locks.length)
  | [], n => .error ("lock unknown: " ++ n)
  | l :: rest, n =>
    if l.name == n then .ok 0
    else match lockIdx rest n with
      | .error e => .error e
      | .ok j => .ok j.succ

/-- A function index by name. -/
def fnIdx : (fns : List UFn) → (n : String) → Except String (Fin fns.length)
  | [], n => .error ("function unknown: " ++ n)
  | f :: rest, n =>
    if f.name == n then .ok 0
    else match fnIdx rest n with
      | .error e => .error e
      | .ok j => .ok j.succ

/-- A field range by table and field index (`some` always: the
    index is inside the table's field list). -/
def fieldRangeO (u : UProg) (t : Fin u.tabs.length)
    (f : Fin (fieldCount u t)) : Option (Int × Int) :=
  ((tabAt u t).cols[f.val]?).map (·.2)

/-- The field is a `bool` field (named in `bools`). -/
def boolFeldAt (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) : Bool :=
  match (tabAt u t).cols[f.val]? with
  | some q => (tabAt u t).bools.contains q.1
  | none => false

/-- The number of the table an option field points at (`none` for a field that is no option). -/
def optNumAt (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) : Option Nat :=
  match (tabAt u t).cols[f.val]? with
  | some q => ((tabAt u t).opts.find? (fun p => p.1 == q.1)).map (·.2)
  | none => none

/-- The count of the table an option field points at: the `n` of its type `Ty.opt n`. -/
def optFeldAt (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) : Option Int :=
  (optNumAt u t f).bind fun num => (u.tabs[num]?).map (·.count)

/-- The type of an aggregate field (`none` for any other field). -/
def wertFeldAt (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) : Option Ty :=
  match (tabAt u t).cols[f.val]? with
  | some q => ((tabAt u t).werte.find? (fun p => p.1 == q.1)).map (·.2)
  | none => none

/-- The field type: `bool` for a bool field, `opt` for an option field, the aggregate of an aggregate field, else
    the recorded range, or `.int 0 0` off the table (unreachable through `fieldRangeO`, kept for totality). -/
def typAt (u : UProg) (t : Fin u.tabs.length)
    (f : Fin (fieldCount u t)) : Ty :=
  if boolFeldAt u t f then .bool else
  match optFeldAt u t f with
  | some n => .opt n
  | none =>
    match wertFeldAt u t f with
    | some τ => τ
    | none =>
    match fieldRangeO u t f with
    | some w => .int w.1 w.2
    | none => .int 0 0

/-- The guards of a table: the locks whose `schutz` names it. -/
def needsAt (u : UProg) (t : Fin u.tabs.length) :
    List (Fin u.locks.length ⊕ (Empty × Nat)) :=
  List.finRange u.locks.length |>.filterMap fun l =>
    if (lockAt u l).guard.any (· == (tabAt u t).name) then some (.inl l)
    else none

def globAt (u : UProg) (g : Fin u.globs.length) : UGlob := u.globs.get g

/-- The guards of a static: the locks whose `protects` list names it (`gbraucht`). -/
def gneedsAt (u : UProg) (g : Fin u.globs.length) :
    List (Fin u.locks.length ⊕ (Empty × Nat)) :=
  List.finRange u.locks.length |>.filterMap fun l =>
    if (lockAt u l).guard.any (· == (globAt u g).name) then some (.inl l)
    else none

/-- The foreign body at an index. -/
def uaxAt (u : UProg) (a : Fin u.axs.length) : UAx := u.axs.get a

/-- A foreign body by name. -/
def uaxIdx : (xs : List UAx) → (n : String) → Except String (Fin xs.length)
  | [], n => .error ("function unknown: " ++ n)
  | a :: rest, n =>
    if a.name == n then .ok 0
    else match uaxIdx rest n with
      | .error e => .error e
      | .ok j => .ok j.succ

/-- The held locks of a function, as indices (names the declaration
    does not know are dropped; `elabU` output never has them). -/
def heldAt (u : UProg) (f : UFn) : List (Fin u.locks.length) :=
  f.held.filterMap fun n => (lockIdx u.locks n).toOption

/-- A static by name. -/
def globIdx : (gs : List UGlob) → (n : String) → Except String (Fin gs.length)
  | [], n => .error ("static unknown: " ++ n)
  | g :: rest, n =>
    if g.name == n then .ok 0
    else match globIdx rest n with
      | .error e => .error e
      | .ok j => .ok j.succ

/-- The payload of an atomic (`D.nutzlast`): its declared statics, by name. -/
def nutzAt (u : UProg) (g : Fin u.globs.length) : List (Fin u.globs.length) :=
  (globAt u g).nutzlast.filterMap fun n => (globIdx u.globs n).toOption

/-- `D.erlaubt`: the field is governed by a state (a `transition` statement applies it there) whose
    `transition` lines allow `von -> nach` (stage numbers). -/
def erlaubtAt (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) (von nach : Int) : Bool :=
  match (tabAt u t).cols[f.val]? with
  | none => false
  | some (fname, _) =>
    u.regiert.any fun (tb, fld, s) => tb == (tabAt u t).name && fld == fname &&
      (u.zustaende.find? (fun z => z.name == s)).any fun z =>
        z.paare.any fun (a, c) => decide ((a : Int) = von) && decide ((c : Int) = nach)

/-- The register at an index. -/
def regAt (u : UProg) (r : Fin u.regs.length) : UReg := u.regs.get r

/-- A register by device and name. -/
def regIdx : (rs : List UReg) → (d n : String) → Except String (Fin rs.length)
  | [], _, n => .error ("register unknown: " ++ n)
  | g :: rest, d, n =>
    if g.dev == d && g.name == n then .ok 0
    else match regIdx rest d n with
      | .error e => .error e
      | .ok j => .ok j.succ

/-- The mirror of a register (`mirrors R from M`): a register of the same device. -/
def spiegelAt (u : UProg) (r : Fin u.regs.length) : Option (Fin u.regs.length) :=
  (regAt u r).spiegel.bind fun m => (regIdx u.regs (regAt u r).dev m).toOption

/-- The carriers a register's answer rests on (`depends { .. }`): tables first by name, else statics. -/
def rtraegerAt (u : UProg) (r : Fin u.regs.length) : List (Fin u.tabs.length ⊕ Fin u.globs.length) :=
  (regAt u r).traeger.filterMap fun n =>
    match (tabIdx u.tabs n).toOption with
    | some t => some (.inl t)
    | none => (globIdx u.globs n).toOption.map .inr

/-- The write flag of a function at a static. -/
def writesGAt (u : UProg) (f : UFn) (g : Fin u.globs.length) : Bool :=
  f.gputs.any (· == (globAt u g).name)

/-- The write flag of a function at a table. -/
def writesAt (u : UProg) (f : UFn) (t : Fin u.tabs.length) : Bool :=
  f.puts.any (· == (tabAt u t).name)

/-- The invariant at an index. -/
def invAt (u : UProg) (i : Fin u.invs.length) : UInv := u.invs.get i

/-- The carrier tables of an invariant, by name. -/
def invTraeger (u : UProg) (i : Fin u.invs.length) : List (Fin u.tabs.length) :=
  (invAt u i).traeger.filterMap fun n => (tabIdx u.tabs n).toOption

/-- `U003` at an invariant, decided over the elaborated functions: a writer of a carrier holds every lock that
    guards a carrier (the elaborator refuses a unit where it fails, `uU003`). -/
def invOkB (u : UProg) (i : Fin u.invs.length) : Bool :=
  (u.fns ++ u.ptrs).all fun f =>
    !((invTraeger u i).any (writesAt u f)) ||
    (invTraeger u i).all fun t => (needsAt u t).all fun w =>
      match w with
      | .inl L => decide (L ∈ heldAt u f)
      | .inr _ => true

/-- The carriers of an invariant in the declaration: its tables where `U003` holds (always, for an elaborated
    unit), none otherwise -- so `invarianten_gehalten` holds for every `UProg`. -/
def traegerD (u : UProg) (i : Fin u.invs.length) : List (Fin u.tabs.length) :=
  if invOkB u i then invTraeger u i else []

/-- The signature of an elaborated function. -/
def mkSig (u : UProg) (f : UFn) :
    Signatur (Fin u.tabs.length) (Fin u.globs.length) (Fin u.locks.length) Empty where
  params := f.params.map (·.2)
  erg := f.ergTy
  gruende := f.gruende
  haelt := heldAt u f
  schreibt := writesAt u f
  gschreibt := writesGAt u f
  konsumiert := []
  produziert := []
  boden := f.boden

/-- The dummy signature: no parameters, no rights. -/
def dummySig (u : UProg) :
    Signatur (Fin u.tabs.length) (Fin u.globs.length) (Fin u.locks.length) Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun _ => false
  konsumiert := []
  produziert := []

/-- The signatures of the unit: the functions', then the pointer types' (`UProg.ptrs`). -/
def sigFns (u : UProg) : List UFn := u.fns ++ u.ptrs

/-- The `n`th signature, or the dummy (an out-of-range number names
    no function and no pointer type). -/
def sigAt (u : UProg) (n : Nat) :
    Signatur (Fin u.tabs.length) (Fin u.globs.length) (Fin u.locks.length) Empty :=
  if h : n < (sigFns u).length then mkSig u ((sigFns u).get ⟨n, h⟩) else dummySig u

/-- **Conformance, decided** (`SigPasst` over the finite carriers of an elaborated unit): the first
    signature fits the second. -/
def sigPasstB {a b c : Nat} (rang : Fin c → Int) (S T : Signatur (Fin a) (Fin b) (Fin c) Empty) : Bool :=
  decide (S.params = T.params) && decide (S.erg = T.erg) && decide (S.gruende = T.gruende) &&
  (List.finRange a).all (fun t => !S.schreibt t || T.schreibt t) &&
  (List.finRange b).all (fun g => !S.gschreibt g || T.gschreibt g) &&
  decide (S.konsumiert = T.konsumiert) && decide (S.produziert = T.produziert) &&
  S.haelt.all (fun L => decide (L ∈ T.haelt)) &&
  T.haelt.all (fun L => decide (L ∈ S.haelt) ||
    (match S.boden with | some c => decide (rang L < c) | none => false)) &&
  (match T.boden with
    | none => true
    | some c => match S.boden with | some c' => decide (c ≤ c') | none => false)

theorem sigPasstB_ok {a b c : Nat} {rang : Fin c → Int} {S T : Signatur (Fin a) (Fin b) (Fin c) Empty}
    (h : sigPasstB rang S T = true) : SigPasst rang S T := by
  unfold sigPasstB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hp, he⟩, hg⟩, hw⟩, hgw⟩, hk⟩, hpr⟩, hh⟩, hx⟩, hb⟩ := h
  refine ⟨hp, he, hg, fun t ht => ?_, fun g' hg' => ?_, hk, hpr, fun L hL => hh L hL, fun L hL hn => ?_,
    fun c hc => ?_⟩
  · rcases hw t (List.mem_finRange t) with h1 | h1
    · rw [ht] at h1; cases h1
    · exact h1
  · rcases hgw g' (List.mem_finRange g') with h1 | h1
    · rw [hg'] at h1; cases h1
    · exact h1
  · rcases hx L hL with h1 | h1
    · exact absurd h1 hn
    · revert h1
      cases hS : S.boden with
      | none => intro h1; cases h1
      | some c => intro h1; exact ⟨c, rfl, of_decide_eq_true h1⟩
  · rw [hc] at hb
    revert hb
    cases hS : S.boden with
    | none => intro h1; cases h1
    | some c' => intro h1; exact ⟨c', rfl, of_decide_eq_true h1⟩

/-- `f` conforms to the signature number `n` of the unit: a live number, and the signatures fit. -/
def passtAt (u : UProg) (f : Fin u.fns.length) (n : Nat) : Bool :=
  decide (n < (sigFns u).length) && sigPasstB (fun l => (lockAt u l).rank) (sigAt u f.val) (sigAt u n)

theorem passtAt_ok (u : UProg) (f : Fin u.fns.length) (n : Nat) (h : passtAt u f n = true) :
    SigPasst (fun l => (lockAt u l).rank) (sigAt u f.val) (sigAt u n) :=
  sigPasstB_ok (Bool.and_eq_true_iff.mp h).2

theorem passtAt_lt (u : UProg) (f : Fin u.fns.length) (n : Nat) (h : passtAt u f n = true) :
    n < (sigFns u).length :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

/-- `invarianten_gehalten` for the declaration of every `UProg`. -/
theorem invGehalten (u : UProg) (n : Nat) (i : Fin u.invs.length)
    (h : (traegerD u i).any (sigAt u n).schreibt = true) (t : Fin u.tabs.length) (ht : t ∈ traegerD u i)
    (L : Fin u.locks.length) (hL : Sum.inl L ∈ needsAt u t) : L ∈ (sigAt u n).haelt := by
  unfold traegerD at h ht
  cases hok : invOkB u i with
  | false => rw [hok] at ht; simp at ht
  | true =>
    rw [hok] at h ht
    simp only [if_true] at h ht
    by_cases hn : n < (sigFns u).length
    · have hs : sigAt u n = mkSig u ((sigFns u).get ⟨n, hn⟩) := by unfold sigAt; rw [dif_pos hn]
      rw [hs] at h ⊢
      unfold invOkB at hok
      have hf := List.all_eq_true.mp hok ((sigFns u).get ⟨n, hn⟩) (List.get_mem _ _)
      simp only [Bool.or_eq_true, Bool.not_eq_true'] at hf
      rcases hf with hf | hf
      · have h' : (invTraeger u i).any (writesAt u ((sigFns u).get ⟨n, hn⟩)) = true := h
        rw [hf] at h'
        cases h'
      · have ht' := List.all_eq_true.mp hf t ht
        have hw := List.all_eq_true.mp ht' (Sum.inl L) hL
        exact of_decide_eq_true hw
    · have hs : sigAt u n = dummySig u := by unfold sigAt; rw [dif_neg hn]
      rw [hs] at h
      simp [dummySig] at h

/-- A non-empty emptiness test means a non-empty list. -/
theorem notEmpty_ne_nil (l : List α) (h : (!l.isEmpty) = true) :
    l ≠ [] := by
  cases l with
  | nil => simp at h
  | cons _ _ => simp

/-- The device's promise at a read value: a truth value is read at `1`/`0`, a number at itself. -/
def regZusage {F : Type} {sig : F → Nat → Bool} : (g : UReg) → Val F sig g.ty → Bool
  | ⟨d, n, lo, hi, k, sp, tr, zu, pr, true⟩ => fun (b : Bool) =>
    UReg.zusageBei ⟨d, n, lo, hi, k, sp, tr, zu, pr, true⟩ (bif b then 1 else 0)
  | ⟨d, n, lo, hi, k, sp, tr, zu, pr, false⟩ => fun (v : Zahl lo hi) =>
    UReg.zusageBei ⟨d, n, lo, hi, k, sp, tr, zu, pr, false⟩ v.n

/-- The provider of the table `t` (`table T from p`): the foreign body named `p`, when it fits -- no parameters, the
    answer a reference into `t` (`Deklaration.anbieter_passt`); a provider that does not fit is none. -/
def anbieterAt (u : UProg) (t : Fin u.tabs.length) : Option (Fin u.axs.length) :=
  match (tabAt u t).von with
  | none => none
  | some p =>
    match uaxIdx u.axs p with
    | .ok a => if (uaxAt u a).params = [] ∧ (uaxAt u a).res = some (.ref t.val) then some a else none
    | .error _ => none

/-- The declaration built from the elaborated program itself: index
    carriers (`Fin`) for tables, statics, locks, fields, functions, foreign bodies and device registers
    (`Reg := Fin u.regs.length`: type, class, mirror, promise and carriers read off `UReg`). -/
def declOf (u : UProg) : Deklaration where
  Tab := Fin u.tabs.length
  decTab := inferInstance
  count := fun t => (tabAt u t).count
  offen := fun t => (tabAt u t).von.isSome
  Feld := fun t => Fin (fieldCount u t)
  decFeld := fun _ => inferInstance
  typ := typAt u
  erlaubt := erlaubtAt u
  tabNr := fun n => if h : n < u.tabs.length then some ⟨n, h⟩ else none
  Glob := Fin u.globs.length
  decGlob := inferInstance
  gtyp := fun g => (globAt u g).ty.toTy
  nutzlast := nutzAt u
  atomar := fun g => (globAt u g).atomic
  geteilt := fun t => (tabAt u t).shared && !((needsAt u t).isEmpty)
  ggeteilt := fun g => (globAt u g).shared && (!((gneedsAt u g).isEmpty) || (globAt u g).atomic)
  Lock := Fin u.locks.length
  decLock := inferInstance
  rang := fun l => (lockAt u l).rank
  maskiert := fun l => (lockAt u l).masks
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := needsAt u
  gbraucht := gneedsAt u
  eigner := fun _ => []
  Fn := Fin u.fns.length
  sig := fun f => f.val
  sigNr := sigAt u
  passt := passtAt u
  passt_ok := passtAt_ok u
  eigner_nie_erzeugt :=
    fun _ _ _ _ h => (List.not_mem_nil (show _ ∈ ([] : List Empty) from h)).elim
  Inv := Fin u.invs.length
  traeger := traegerD u
  invs := List.finRange u.invs.length
  Ax := Fin u.axs.length
  aparams := fun a => (uaxAt u a).params
  aerg := fun a => (uaxAt u a).res
  aschreibt := fun a t => (uaxAt u a).puts.any (· == (tabAt u t).name)
  agschreibt := fun a g => (uaxAt u a).gputs.any (· == (globAt u g).name)
  agruende := fun a => (uaxAt u a).gruende
  anbieter := anbieterAt u
  anbieter_passt := fun t a h => by
    unfold anbieterAt at h
    split at h
    · cases h
    · rename_i p hp
      split at h
      · split at h
        · rename_i hc
          cases h
          exact ⟨by simp [hp], hc.1, t.val, hc.2, by simp [t.isLt]⟩
        · cases h
      · cases h
  Reg := Fin u.regs.length
  rtyp := fun r => (regAt u r).ty
  rklasse := fun r => (regAt u r).klasse
  spiegel := spiegelAt u
  rzusage := fun r => regZusage (regAt u r)
  rtraeger := rtraegerAt u
  Annahme := Option (Fin u.annahmen.length)
  a10 := none
  geteilt_bewacht := fun t h => by
    have h' : ((tabAt u t).shared && !((needsAt u t).isEmpty)) = true := h
    simp only [Bool.and_eq_true] at h'
    exact notEmpty_ne_nil _ h'.2
  invarianten_gehalten := fun n i h t ht L hL => invGehalten u n i h t ht L hL
  ggeteilt_bewacht := fun g h => by
    have h' : ((globAt u g).shared && (!((gneedsAt u g).isEmpty) || (globAt u g).atomic)) = true := h
    simp only [Bool.and_eq_true, Bool.or_eq_true] at h'
    rcases h'.2 with h1 | h2
    · exact Or.inl (notEmpty_ne_nil _ h1)
    · exact Or.inr h2

/-! ## Bridge lemmas: the computed declaration meets the U data -/

/-- `sigAt` at a live index is the elaborated signature. -/
theorem sigAt_get (u : UProg) (i : Fin u.fns.length) :
    sigAt u i.val = mkSig u (fnAt u i) := by
  have hi : i.val < (sigFns u).length := by
    unfold sigFns; rw [List.length_append]; omega
  unfold sigAt fnAt
  rw [dif_pos hi]
  congr 1
  simp only [sigFns, List.get_eq_getElem, List.getElem_append_left i.isLt]

/-- Projections of `sigAt` at a live index. -/
theorem sigAt_params (u : UProg) (i : Fin u.fns.length) :
    (sigAt u i.val).params = (fnAt u i).params.map (·.2) := by
  rw [sigAt_get]; rfl

theorem sigAt_erg (u : UProg) (i : Fin u.fns.length) :
    (sigAt u i.val).erg = (fnAt u i).ergTy := by
  rw [sigAt_get]; rfl

theorem sigAt_haelt (u : UProg) (i : Fin u.fns.length) :
    (sigAt u i.val).haelt = heldAt u (fnAt u i) := by
  rw [sigAt_get]; rfl

theorem sigAt_konsumiert (u : UProg) (i : Fin u.fns.length) :
    (sigAt u i.val).konsumiert = [] := by
  rw [sigAt_get]; rfl

theorem sigAt_produziert (u : UProg) (i : Fin u.fns.length) :
    (sigAt u i.val).produziert = [] := by
  rw [sigAt_get]; rfl

/-- Parameters through the declaration. -/
theorem params_eq (u : UProg) (i : Fin u.fns.length) :
    (declOf u).params i = (fnAt u i).params.map (·.2) := by
  simp [Deklaration.params, Deklaration.signatur, declOf, sigAt_params]

/-- Result through the declaration. -/
theorem erg_eq (u : UProg) (i : Fin u.fns.length) :
    (declOf u).erg i = (fnAt u i).ergTy := by
  simp [Deklaration.erg, Deklaration.signatur, declOf, sigAt_erg]

/-- Held locks through the declaration. -/
theorem haelt_eq (u : UProg) (i : Fin u.fns.length) :
    (declOf u).haelt i = heldAt u (fnAt u i) := by
  simp [Deklaration.haelt, Deklaration.signatur, declOf, sigAt_haelt]

/-- The contract end: held locks only (no marks travel). -/
theorem ende_eq (u : UProg) (f : Fin u.fns.length) :
    (vertragVon (declOf u) f).ende =
      (heldAt u (fnAt u f)).map (Res.held (D := declOf u)) := by
  simp only [vertragVon, Vertrag.vonSig, Vertrag.ende, Deklaration.signatur,
    declOf, sigAt_haelt, sigAt_produziert]
  exact List.append_nil _

/-- Every field index has its recorded range. -/
theorem rangeO_some (u : UProg) (t : Fin u.tabs.length)
    (fld : Fin (fieldCount u t)) :
    ∃ w, fieldRangeO u t fld = some w := by
  unfold fieldRangeO
  have hlt : fld.val < (tabAt u t).cols.length := fld.isLt
  rw [List.getElem?_eq_getElem hlt]
  exact ⟨_, rfl⟩

/-- The type of a field that is neither a bool nor an option is the recorded range. -/
theorem typAt_of (u : UProg) (t : Fin u.tabs.length)
    (fld : Fin (fieldCount u t)) (w : Int × Int)
    (h : fieldRangeO u t fld = some w) (hb : boolFeldAt u t fld = false)
    (ho : optFeldAt u t fld = none) (hw : wertFeldAt u t fld = none) :
    typAt u t fld = .int w.1 w.2 := by
  unfold typAt
  rw [hb, ho, hw, h]
  rfl

/-- The type of an aggregate field is its aggregate. -/
theorem typAt_wert (u : UProg) (t : Fin u.tabs.length)
    (fld : Fin (fieldCount u t)) (τ : Ty) (hb : boolFeldAt u t fld = false)
    (ho : optFeldAt u t fld = none) (hw : wertFeldAt u t fld = some τ) :
    typAt u t fld = τ := by
  unfold typAt
  rw [hb, ho, hw]
  rfl

/-- The type of an option field is `opt` of the count of its table. -/
theorem typAt_opt (u : UProg) (t : Fin u.tabs.length)
    (fld : Fin (fieldCount u t)) (n : Int) (hb : boolFeldAt u t fld = false)
    (ho : optFeldAt u t fld = some n) :
    typAt u t fld = .opt n := by
  unfold typAt
  rw [hb, ho]
  rfl

/-- The type of a bool field is `bool`. -/
theorem typAt_bool (u : UProg) (t : Fin u.tabs.length)
    (fld : Fin (fieldCount u t)) (hb : boolFeldAt u t fld = true) :
    typAt u t fld = .bool := by
  unfold typAt
  rw [hb]
  rfl

/-- `tabNr` at a live number. -/
theorem tabNr_some (u : UProg) (num : Nat) (h : num < u.tabs.length) :
    (declOf u).tabNr num = some (⟨num, h⟩ : Fin u.tabs.length) := by
  show (if h' : num < u.tabs.length then
    (some ⟨num, h'⟩ : Option (Fin u.tabs.length)) else none) = _
  rw [dif_pos h]

/-! ## Generic lowering: field search, variables -/

/-- Position of the first field with a name. -/
def fieldPos : List (String × (Int × Int)) → String → Nat
  | [], _ => 0
  | (m, _) :: rest, n => if m == n then 0 else fieldPos rest n + 1

/-- Range of the first field with a name. -/
def fieldAtPos : List (String × (Int × Int)) → String → Option (Int × Int)
  | [], _ => none
  | (m, w) :: rest, n => if m == n then some w else fieldAtPos rest n

/-- A found field is inside the list. -/
theorem fieldPos_lt (fs : List (String × (Int × Int))) (n : String)
    (w : Int × Int) (h : fieldAtPos fs n = some w) :
    fieldPos fs n < fs.length := by
  induction fs with
  | nil => simp [fieldAtPos] at h
  | cons hd tl ih =>
    cases he : (hd.1 == n) with
    | true =>
      have h1 : fieldPos (hd :: tl) n = 0 := by simp [fieldPos, he]
      rw [h1]
      exact Nat.zero_lt_succ _
    | false =>
      have h1 : fieldPos (hd :: tl) n = fieldPos tl n + 1 := by
        simp [fieldPos, he]
      have h2 : fieldAtPos (hd :: tl) n = fieldAtPos tl n := by
        simp [fieldAtPos, he]
      rw [h2] at h
      have hi := ih h
      rw [h1]
      show fieldPos tl n + 1 < tl.length + 1
      omega

/-- The range at the found position is the found range. -/
theorem fieldAtPos_get (fs : List (String × (Int × Int))) (n : String)
    (w : Int × Int) (h : fieldAtPos fs n = some w) :
    (fs[fieldPos fs n]?).map (·.2) = some w := by
  induction fs with
  | nil => simp [fieldAtPos] at h
  | cons hd tl ih =>
    cases he : (hd.1 == n) with
    | true =>
      have h1 : fieldPos (hd :: tl) n = 0 := by simp [fieldPos, he]
      have h2 : fieldAtPos (hd :: tl) n = some hd.2 := by
        simp [fieldAtPos, he]
      rw [h2] at h
      rw [h1]
      have g0 : (((hd :: tl)[0]?).map (·.2)) = some hd.2 := rfl
      rw [g0]
      exact h
    | false =>
      have h1 : fieldPos (hd :: tl) n = fieldPos tl n + 1 := by
        simp [fieldPos, he]
      have h2 : fieldAtPos (hd :: tl) n = fieldAtPos tl n := by
        simp [fieldAtPos, he]
      rw [h2] at h
      have ih' := ih h
      rw [h1]
      have g1 : ((hd :: tl)[fieldPos tl n + 1]?) = (tl[fieldPos tl n]?) := rfl
      rw [g1]
      exact ih'

/-- A field hit: the index, its range, and the lookup equation. -/
structure FieldHit (u : UProg) (t : Fin u.tabs.length) where
  idx : Fin (fieldCount u t)
  range : Int × Int
  hit : fieldRangeO u t idx = some range
  /-- The field is a number: its type is the recorded range. -/
  hint : typAt u t idx = .int range.1 range.2

/-- A bool field hit: the index and the fact that its type is `bool`. -/
structure BoolHit (u : UProg) (t : Fin u.tabs.length) where
  idx : Fin (fieldCount u t)
  hbool : typAt u t idx = .bool

/-- Find a field of a table by name. -/
def fieldHit (u : UProg) (t : Fin u.tabs.length) (fname : String) :
    Except String (FieldHit u t) :=
  match h : fieldAtPos (tabAt u t).cols fname with
  | none => .error "field unknown"
  | some w =>
    have hlt : fieldPos (tabAt u t).cols fname < fieldCount u t :=
      fieldPos_lt _ _ _ h
    if hb : boolFeldAt u t ⟨fieldPos (tabAt u t).cols fname, hlt⟩ = false then
      if ho : optFeldAt u t ⟨fieldPos (tabAt u t).cols fname, hlt⟩ = none then
        if hw : wertFeldAt u t ⟨fieldPos (tabAt u t).cols fname, hlt⟩ = none then
          .ok ⟨⟨fieldPos (tabAt u t).cols fname, hlt⟩, w, fieldAtPos_get _ _ _ h,
            typAt_of u t _ w (fieldAtPos_get _ _ _ h) hb ho hw⟩
        else .error "aggregate field as a number"
      else .error "option field as a number"
    else .error "bool field as a number"

/-- An aggregate field hit: the index and its type (`typAt` is the aggregate). -/
def fieldHitW (u : UProg) (t : Fin u.tabs.length) (fname : String) : Option (Fin (fieldCount u t)) :=
  match h : fieldAtPos (tabAt u t).cols fname with
  | none => none
  | some w =>
    have hlt : fieldPos (tabAt u t).cols fname < fieldCount u t := fieldPos_lt _ _ _ h
    if (wertFeldAt u t ⟨fieldPos (tabAt u t).cols fname, hlt⟩).isSome then some ⟨fieldPos (tabAt u t).cols fname, hlt⟩
    else none

/-- An option field hit: the index, the count `n` of its table and the fact that its type is `opt n`. -/
structure OptHit (u : UProg) (t : Fin u.tabs.length) where
  idx : Fin (fieldCount u t)
  n : Int
  hopt : typAt u t idx = .opt n
  /-- The table the option indexes, and that its count is `n`. -/
  tnum : Nat
  hlt : tnum < u.tabs.length
  hcnt : (declOf u).count ⟨tnum, hlt⟩ = n

/-- Find an OPTION field of a table by name. -/
def fieldHitO (u : UProg) (t : Fin u.tabs.length) (fname : String) :
    Except String (OptHit u t) :=
  match h : fieldAtPos (tabAt u t).cols fname with
  | none => .error "field unknown"
  | some _ =>
    have hlt : fieldPos (tabAt u t).cols fname < fieldCount u t :=
      fieldPos_lt _ _ _ h
    if hb : boolFeldAt u t ⟨fieldPos (tabAt u t).cols fname, hlt⟩ = false then
      match ho : optFeldAt u t ⟨fieldPos (tabAt u t).cols fname, hlt⟩ with
      | some n =>
        match optNumAt u t ⟨fieldPos (tabAt u t).cols fname, hlt⟩ with
        | none => .error "option table unknown"
        | some tnum =>
          if hl : tnum < u.tabs.length then
            if hc : (declOf u).count ⟨tnum, hl⟩ = n then
              .ok ⟨⟨fieldPos (tabAt u t).cols fname, hlt⟩, n, typAt_opt u t _ n hb ho, tnum, hl, hc⟩
            else .error "option table count foreign"
          else .error "option table unknown"
      | none => .error "number field as an option"
    else .error "bool field as an option"

/-- Find a BOOL field of a table by name. -/
def fieldHitB (u : UProg) (t : Fin u.tabs.length) (fname : String) :
    Except String (BoolHit u t) :=
  match h : fieldAtPos (tabAt u t).cols fname with
  | none => .error "field unknown"
  | some w =>
    have hlt : fieldPos (tabAt u t).cols fname < fieldCount u t :=
      fieldPos_lt _ _ _ h
    if hb : boolFeldAt u t ⟨fieldPos (tabAt u t).cols fname, hlt⟩ = true then
      .ok ⟨⟨fieldPos (tabAt u t).cols fname, hlt⟩, typAt_bool u t _ hb⟩
    else .error "number field as a truth value"

/-- A variable by position and expected type (the `beq` re-checks the
    context, so a divergent caller is an explicit error). -/
def lowVar : (Γ : Ctx) → (j : Nat) → (τ : Ty) → Except String (Var Γ τ)
  | [], _, _ => .error "parameter outside"
  | σ :: Γ, 0, τ =>
    if h : σ = τ then by rw [h]; exact .ok Var.here
    else .error "parameter shape foreign"
  | _ :: Γ, j + 1, τ =>
    match lowVar Γ j τ with
    | .error e => .error e
    | .ok v => .ok (Var.there v)

/-- Position of a parameter name. -/
def paramPos : List (String × Ty) → String → Except String Nat
  | [], p => .error ("name unknown: " ++ p)
  | (q, _) :: rest, p =>
    if q == p then .ok 0
    else
      match paramPos rest p with
      | .error e => .error e
      | .ok k => .ok (k + 1)

/-! ## Generic lowering: indices, sides, contracts -/

/-- An index into a table: a literal inside `count`, or an index
    parameter of a table of the same count (`sh` shifts parameter positions:
    `0` in a body, `1` in an `ensures` context with a result, where
    the result rides first). -/
def lowIdx (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (t : Fin u.tabs.length) : UIdx →
    Except String (Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
  | .lit n =>
    if h1 : 0 ≤ n then
      if h2 : n ≤ (declOf u).count t - 1 then
        .ok (Expr.widen h1 h2 (Expr.lit n))
      else .error "index outside count"
    else .error "index outside count"
  | .param p =>
    match paramPos fn.params p with
    | .error e => .error e
    | .ok j =>
      match fn.kinds[j]? with
      | some (.index _) =>
        -- an index into a table of the same count is an index into `t` (the model's `Ty.index` is the count)
        match lowVar Γ (sh + j) (.index ((declOf u).count t)) with
        | .error _ => .error "index of foreign table"
        | .ok v => .ok (Expr.var v)
      | some .int =>
        match fn.params[j]? with
        | some (_, .int lo hi) =>
          if h1 : 0 ≤ lo then
            if h2 : hi ≤ (declOf u).count t - 1 then
              match lowVar Γ (sh + j) (.int lo hi) with
              | .error e => .error e
              | .ok v => .ok (Expr.widen h1 h2 (Expr.var v))
            else .error "index outside count"
          else .error "index outside count"
        | _ => .error "index without G form"
      | _ => .error "index without G form"

/-- A sided term with its range. -/
structure LowSide (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) where
  range : Int × Int
  term : Expr (declOf u) Γ Λ (.int range.1 range.2)

/-- Arithmetic on sided terms: the range is what `Expr.add`/`sub`/`mul` carry in their type. -/
def LowSide.plus {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x y : LowSide u Γ Λ) :
    LowSide u Γ Λ :=
  { range := (x.range.1 + y.range.1, x.range.2 + y.range.2), term := Expr.add x.term y.term }

def LowSide.minus {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x y : LowSide u Γ Λ) :
    LowSide u Γ Λ :=
  { range := (x.range.1 - y.range.2, x.range.2 - y.range.1), term := Expr.sub x.term y.term }

def LowSide.times {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x y : LowSide u Γ Λ) :
    LowSide u Γ Λ :=
  { range := (imin (imin (x.range.1 * y.range.1) (x.range.1 * y.range.2))
                  (imin (x.range.2 * y.range.1) (x.range.2 * y.range.2)),
             imax (imax (x.range.1 * y.range.1) (x.range.1 * y.range.2))
                  (imax (x.range.2 * y.range.1) (x.range.2 * y.range.2))),
    term := Expr.mul x.term y.term }

/-- The integer conversion `T(e)`: the widening `Expr.weiter` to the target range, when the
    operand's range fits (as M1 decides it); otherwise the lowering REFUSES. -/
def LowSide.conv {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (lo hi : Int)
    (x : LowSide u Γ Λ) : Except String (LowSide u Γ Λ) :=
  if h1 : lo ≤ x.range.1 then
    if h2 : x.range.2 ≤ hi then .ok { range := (lo, hi), term := Expr.widen h1 h2 x.term }
    else .error "conversion outside target range"
  else .error "conversion outside target range"

/-- `a & b` over non-negative ranges (M137): `Expr.band`, range `0 .. hi(a)`. -/
def LowSide.and {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x y : LowSide u Γ Λ) :
    Except String (LowSide u Γ Λ) :=
  if h0 : 0 ≤ x.range.1 then
    if h0' : 0 ≤ y.range.1 then
      .ok { range := (0, x.range.2), term := Expr.band h0 h0' x.term y.term }
    else .error "bit operation over a negative range"
  else .error "bit operation over a negative range"

/-- The number of bits that holds every value up to `m`: `m < 2 ^ bitsFuer m`. -/
def bitsFuer (m : Int) : Nat := Nat.log2 m.toNat + 1

/-- `a | b` over non-negative ranges: `Expr.bor` at the smallest width holding both. The
    result range `0 .. 2^w - 1` contains every value of the bitwise or whatever the width, so the
    narrowest one is sound. -/
def LowSide.or {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x y : LowSide u Γ Λ) :
    Except String (LowSide u Γ Λ) :=
  if h0 : 0 ≤ x.range.1 then
    if h0' : 0 ≤ y.range.1 then
      if hw1 : x.range.2 < (2 : Int) ^ bitsFuer (imax x.range.2 y.range.2) then
        if hw2 : y.range.2 < (2 : Int) ^ bitsFuer (imax x.range.2 y.range.2) then
          .ok { range := (0, (2 : Int) ^ bitsFuer (imax x.range.2 y.range.2) - 1),
                term := Expr.bor (bitsFuer (imax x.range.2 y.range.2)) h0 h0' hw1 hw2 x.term y.term }
        else .error "bit operation outside its width"
      else .error "bit operation outside its width"
    else .error "bit operation over a negative range"
  else .error "bit operation over a negative range"

/-- `a ^ b` over non-negative ranges: `Expr.bxor`, like `oder`. -/
def LowSide.xoder {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x y : LowSide u Γ Λ) :
    Except String (LowSide u Γ Λ) :=
  if h0 : 0 ≤ x.range.1 then
    if h0' : 0 ≤ y.range.1 then
      if hw1 : x.range.2 < (2 : Int) ^ bitsFuer (imax x.range.2 y.range.2) then
        if hw2 : y.range.2 < (2 : Int) ^ bitsFuer (imax x.range.2 y.range.2) then
          .ok { range := (0, (2 : Int) ^ bitsFuer (imax x.range.2 y.range.2) - 1),
                term := Expr.bxor (bitsFuer (imax x.range.2 y.range.2)) h0 h0' hw1 hw2 x.term y.term }
        else .error "bit operation outside its width"
      else .error "bit operation outside its width"
    else .error "bit operation over a negative range"
  else .error "bit operation over a negative range"

/-- `a / b` (M102): `Expr.div` for a non-negative numerator over a denominator from `1`, else the signed
    `Expr.sdiv` when the denominator excludes zero; a denominator that may be zero has no term. -/
def LowSide.durch {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x y : LowSide u Γ Λ) :
    Except String (LowSide u Γ Λ) :=
  if h0 : 0 ≤ x.range.1 then
    if h1 : 1 ≤ y.range.1 then
      .ok { range := (0, x.range.2), term := Expr.div h0 h1 x.term y.term }
    else
      if hb : 1 ≤ y.range.1 ∨ y.range.2 ≤ -1 then
        .ok { range := (-(betragMax x.range.1 x.range.2), betragMax x.range.1 x.range.2),
              term := Expr.sdiv hb x.term y.term }
      else .error "division by a denominator that may be zero"
  else
    if hb : 1 ≤ y.range.1 ∨ y.range.2 ≤ -1 then
      .ok { range := (-(betragMax x.range.1 x.range.2), betragMax x.range.1 x.range.2),
            term := Expr.sdiv hb x.term y.term }
    else .error "division by a denominator that may be zero"

/-- `a % b`: `Expr.rem`, or the signed `Expr.srem`, under the same conditions as `/`. -/
def LowSide.rest {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x y : LowSide u Γ Λ) :
    Except String (LowSide u Γ Λ) :=
  if h0 : 0 ≤ x.range.1 then
    if h1 : 1 ≤ y.range.1 then
      .ok { range := (0, y.range.2 - 1), term := Expr.rem h0 h1 x.term y.term }
    else
      if hb : 1 ≤ y.range.1 ∨ y.range.2 ≤ -1 then
        .ok { range := (-(betragMax y.range.1 y.range.2 - 1), betragMax y.range.1 y.range.2 - 1),
              term := Expr.srem hb x.term y.term }
      else .error "division by a denominator that may be zero"
  else
    if hb : 1 ≤ y.range.1 ∨ y.range.2 ≤ -1 then
      .ok { range := (-(betragMax y.range.1 y.range.2 - 1), betragMax y.range.1 y.range.2 - 1),
            term := Expr.srem hb x.term y.term }
    else .error "division by a denominator that may be zero"

/-- The width a shift of `x` by `y` names: the smallest that holds the operand and exceeds the amount. -/
def schiebeBreite (x y : Int × Int) : Nat := max (bitsFuer x.2) (y.2.toNat + 1)

/-- `a << b` over non-negative ranges (M137): `Expr.shl` at the width `schiebeBreite`. A shift amount beyond 4096
    gives a result range no type holds (and `2 ^ n` would not be computed): refused as a value outside any range. -/
def LowSide.links {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x y : LowSide u Γ Λ) :
    Except String (LowSide u Γ Λ) :=
  if 4096 < y.range.2 then .error "value outside range"
  else if h0 : 0 ≤ x.range.1 then
    if h0' : 0 ≤ y.range.1 then
      if hw1 : x.range.2 < (2 : Int) ^ schiebeBreite x.range y.range then
        if hw2 : y.range.2 < ((schiebeBreite x.range y.range : Nat) : Int) then
          .ok { range := (0, x.range.2 * 2 ^ y.range.2.toNat),
                term := Expr.shl (schiebeBreite x.range y.range) hw1 hw2 h0 h0' x.term y.term }
        else .error "shift outside its width"
      else .error "shift outside its width"
    else .error "bit operation over a negative range"
  else .error "bit operation over a negative range"

/-- `a >> b`: `Expr.shr`, range `0 .. hi(a)`. -/
def LowSide.rechts {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x y : LowSide u Γ Λ) :
    Except String (LowSide u Γ Λ) :=
  if 4096 < y.range.2 then .error "value outside range"
  else if h0 : 0 ≤ x.range.1 then
    if h0' : 0 ≤ y.range.1 then
      if hw1 : x.range.2 < (2 : Int) ^ schiebeBreite x.range y.range then
        if hw2 : y.range.2 < ((schiebeBreite x.range y.range : Nat) : Int) then
          .ok { range := (0, x.range.2),
                term := Expr.shr (schiebeBreite x.range y.range) hw1 hw2 h0 h0' x.term y.term }
        else .error "shift outside its width"
      else .error "shift outside its width"
    else .error "bit operation over a negative range"
  else .error "bit operation over a negative range"

/-- `-a`: `Expr.neg`. -/
def LowSide.minusEins {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x : LowSide u Γ Λ) :
    LowSide u Γ Λ :=
  { range := (-x.range.2, -x.range.1), term := Expr.neg x.term }

/-- Two lowered operands into one lowered result (the first error wins). -/
def lowZwei {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    (f : LowSide u Γ Λ → LowSide u Γ Λ → Except String (LowSide u Γ Λ))
    (a b : Except String (LowSide u Γ Λ)) : Except String (LowSide u Γ Λ) :=
  match a with
  | .error e => .error e
  | .ok x =>
    match b with
    | .error e => .error e
    | .ok y => f x y

/-- The table a basis names: a pointer parameter's target, or a
    table (for `old`, where both spellings travel). -/
def lowBasisTab (u : UProg) (fn : UFn) (b : String) :
    Except String (Fin u.tabs.length) :=
  match paramPos fn.params b with
  | .ok j =>
    match fn.kinds[j]? with
    | some (.ptr num _) =>
      if h : num < u.tabs.length then .ok ⟨num, h⟩
      else .error "pointer table unknown"
    | _ => .error "place without G form"
  | .error _ =>
    match tabIdx u.tabs b with
    | .ok t => .ok t
    | .error e => .error e

/-- A numeric parameter as a side (positions shift by `sh`,
    see `lowIdx`). -/
def lowParamSide (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (p : String) :
    Except String (LowSide u Γ Λ) :=
  match paramPos fn.params p with
  | .error e => .error e
  | .ok j =>
    match fn.kinds[j]? with
    | some (.ptr _ _) => .error "pointer as value without G form"
    | some _ =>
      match fn.params[j]? with
      | some (_, .int a b) =>
        match lowVar Γ (sh + j) (.int a b) with
        | .error e => .error e
        | .ok v => .ok { range := (a, b), term := Expr.var v }
      | _ => .error "parameter without G form"
    | none => .error "parameter without G form"

/-- A `durch` term at its recorded range (the `rw` turns the
    goal into the field type, where the constructor fits). -/
def durchTerm (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (num : Nat) (w : Bool) (h : num < u.tabs.length)
    (fh : FieldHit u ⟨num, h⟩) (v : Var Γ (.ptr num w))
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count ⟨num, h⟩)))
    (hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩,
      Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2) := by
  rw [← fh.hint]
  exact Expr.thru (D := declOf u) (Expr.var v) ⟨num, h⟩
    (tabNr_some u num h) fh.idx i hL

/-- A `slot` term at its recorded range. -/
def slotTerm (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (t : Fin u.tabs.length) (fh : FieldHit u t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2) := by
  rw [← fh.hint]
  exact Expr.slot (D := declOf u) t fh.idx i hL

/-- An `altSlot` term at its recorded range. -/
def altTerm (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (t : Fin u.tabs.length) (fh : FieldHit u t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2) := by
  rw [← fh.hint]
  exact Expr.oldS (D := declOf u) t fh.idx i hL

/-- A slot read through a pointer parameter (positions shift
    by `sh`, see `lowIdx`). -/
def lowDurch (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (b fname : String) (ix : UIdx) :
    Except String (LowSide u Γ Λ) :=
  match paramPos fn.params b with
  | .error e => .error e
  | .ok j =>
    match fn.kinds[j]? with
    | some (.ptr num w) =>
      if h : num < u.tabs.length then
        match fieldHit u ⟨num, h⟩ fname with
        | .error e => .error e
        | .ok fh =>
          match lowVar Γ (sh + j) (.ptr num w) with
          | .error e => .error e
          | .ok v =>
            match lowIdx u Γ Λ fn sh ⟨num, h⟩ ix with
            | .error e => .error e
            | .ok i =>
              if hL : (∀ wdd ∈ (declOf u).braucht ⟨num, h⟩,
                  Res.von (declOf u) wdd ∈ Λ) then
                .ok { range := fh.range, term := durchTerm u Γ Λ num w h fh v i hL }
              else .error "access without held guard"
      else .error "pointer table unknown"
    | _ => .error "place without G form"

/-- A field read through a reference into an open table, at the field's recorded range. -/
def refTerm (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (num : Nat) (h : num < u.tabs.length) (ho : (declOf u).offen ⟨num, h⟩ = true)
    (fh : FieldHit u ⟨num, h⟩) (v : Var Γ (.ref num))
    (hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩, Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2) := by
  rw [← fh.hint]
  exact Expr.slotRef (D := declOf u) (Expr.var v) ⟨num, h⟩ (tabNr_some u num h) ho fh.idx hL

/-- `r->f`: a field read through a reference local `r` (positions shift by `sh`). -/
def lowRefRead (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (r fname : String) :
    Except String (LowSide u Γ Λ) :=
  match paramPos fn.params r with
  | .error e => .error e
  | .ok j =>
    match fn.kinds[j]? with
    | some (.ref num) =>
      if h : num < u.tabs.length then
        if ho : (declOf u).offen ⟨num, h⟩ = true then
          match fieldHit u ⟨num, h⟩ fname with
          | .error e => .error e
          | .ok fh =>
            match lowVar Γ (sh + j) (.ref num) with
            | .error e => .error e
            | .ok v =>
              if hL : (∀ wdd ∈ (declOf u).braucht ⟨num, h⟩,
                  Res.von (declOf u) wdd ∈ Λ) then
                .ok { range := fh.range, term := refTerm u Γ Λ num h ho fh v hL }
              else .error "access without held guard"
        else .error "reference into a table that is not open"
      else .error "reference table unknown"
    | _ => .error "place without G form"

/-- A slot read at a table (positions shift by `sh`). -/
def lowTabRead (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (b fname : String) (ix : UIdx) :
    Except String (LowSide u Γ Λ) :=
  match tabIdx u.tabs b with
  | .error e => .error e
  | .ok t =>
    match fieldHit u t fname with
    | .error e => .error e
    | .ok fh =>
      match lowIdx u Γ Λ fn sh t ix with
      | .error e => .error e
      | .ok i =>
        if hL : (∀ wdd ∈ (declOf u).braucht t,
            Res.von (declOf u) wdd ∈ Λ) then
          .ok { range := fh.range, term := slotTerm u Γ Λ t fh i hL }
        else .error "access without held guard"

/-- An entry read (`old`) at a resolved table (positions
    shift by `sh`). -/
def lowAltRead (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (b fname : String) (ix : UIdx) :
    Except String (LowSide u Γ Λ) :=
  match lowBasisTab u fn b with
  | .error e => .error e
  | .ok t =>
    match fieldHit u t fname with
    | .error e => .error e
    | .ok fh =>
      match lowIdx u Γ Λ fn sh t ix with
      | .error e => .error e
      | .ok i =>
        if hL : (∀ wdd ∈ (declOf u).braucht t,
            Res.von (declOf u) wdd ∈ Λ) then
          .ok { range := fh.range, term := altTerm u Γ Λ t fh i hL }
        else .error "access without held guard"

/-- A number static read (`Expr.glob`): its type is the recorded range. -/
def lowGlobSide (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (p : String) :
    Except String (LowSide u Γ Λ) :=
  match globIdx u.globs p with
  | .error e => .error e
  | .ok g =>
    if hd : (∀ w ∈ (declOf u).gbraucht g, Res.von (declOf u) w ∈ Λ) then
    match h : (globAt u g).ty with
    | .int lo hi =>
      .ok { range := (lo, hi), term := by
              have hg : (declOf u).gtyp g = .int lo hi := by
                show (globAt u g).ty.toTy = _
                rw [h]
                rfl
              show Expr (declOf u) Γ Λ (.int lo hi)
              rw [← hg]
              exact Expr.glob (D := declOf u) g hd }
    | .bool => .error "bool static as a number"
    | .wert _ => .error "aggregate static as a number"
    else .error "access without held guard"

/-- A `bool` static read as a truth value. -/
def lowGlobBool (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (p : String) :
    Except String (Expr (declOf u) Γ Λ .bool) :=
  match globIdx u.globs p with
  | .error e => .error e
  | .ok g =>
    if hd : (∀ w ∈ (declOf u).gbraucht g, Res.von (declOf u) w ∈ Λ) then
    match h : (globAt u g).ty with
    | .bool =>
      .ok (by
        have hg : (declOf u).gtyp g = .bool := by
          show (globAt u g).ty.toTy = _
          rw [h]
          rfl
        rw [← hg]
        exact Expr.glob (D := declOf u) g hd)
    | .int _ _ => .error "number static as a truth value"
    | .wert _ => .error "aggregate static as a truth value"
    else .error "access without held guard"

/-- A `bool` slot read through a pointer parameter (positions shift by `sh`): the place's truth value. -/
def lowBoolDurch (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (b fname : String) (ix : UIdx) :
    Except String (Expr (declOf u) Γ Λ .bool) :=
  match paramPos fn.params b with
  | .error e => .error e
  | .ok j =>
    match fn.kinds[j]? with
    | some (.ptr num w) =>
      if h : num < u.tabs.length then
        match fieldHitB u ⟨num, h⟩ fname with
        | .error e => .error e
        | .ok fh =>
          match lowVar Γ (sh + j) (.ptr num w) with
          | .error e => .error e
          | .ok v =>
            match lowIdx u Γ Λ fn sh ⟨num, h⟩ ix with
            | .error e => .error e
            | .ok i =>
              if hL : (∀ wdd ∈ (declOf u).braucht ⟨num, h⟩,
                  Res.von (declOf u) wdd ∈ Λ) then
                .ok (by
                  rw [← fh.hbool]
                  exact Expr.thru (D := declOf u) (Expr.var v) ⟨num, h⟩
                    (tabNr_some u num h) fh.idx i hL)
              else .error "access without held guard"
      else .error "pointer table unknown"
    | _ => .error "place without G form"

/-- A `bool` slot read at a table. -/
def lowBoolTab (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (b fname : String) (ix : UIdx) :
    Except String (Expr (declOf u) Γ Λ .bool) :=
  match tabIdx u.tabs b with
  | .error e => .error e
  | .ok t =>
    match fieldHitB u t fname with
    | .error e => .error e
    | .ok fh =>
      match lowIdx u Γ Λ fn sh t ix with
      | .error e => .error e
      | .ok i =>
        if hL : (∀ wdd ∈ (declOf u).braucht t,
            Res.von (declOf u) wdd ∈ Λ) then
          .ok (by
            rw [← fh.hbool]
            exact Expr.slot (D := declOf u) t fh.idx i hL)
        else .error "access without held guard"

/-- The result of an `ensures` as a parameter `#erg` in front of the others (a name no source can write): inside a
    quantifier the binder rides in front of the result, so the result is found by its name, not at position 0. -/
def ergAlsParam (fn : UFn) : Option Ty → Except String UFn
  | none => .ok fn
  | some (.int a b) => .ok { fn with params := ("#erg", .int a b) :: fn.params, kinds := .int :: fn.kinds }
  | some .bool => .ok { fn with params := ("#erg", .bool) :: fn.params, kinds := .bool :: fn.kinds }
  | some _ => .error "quantifier beside a result of this type without G form"

/-! ### Aggregate values (`Ty.arr`, `Ty.str`, 2026-10-25)

A value of any type with its term: arrays and strings are lowered by their type, which travels with the term
(`lowWertE`); a number keeps the range the integer lowering gives it. -/

/-- A term with its type. -/
structure LowWert (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) where
  ty : Ty
  term : Expr (declOf u) Γ Λ ty

/-- A number as a value. -/
def LowSide.wert {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x : LowSide u Γ Λ) : LowWert u Γ Λ :=
  ⟨.int x.range.1 x.range.2, x.term⟩

/-- A value that is a number. -/
def LowWert.zahl {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} : LowWert u Γ Λ → Except String (LowSide u Γ Λ)
  | ⟨.int a b, t⟩ => .ok { range := (a, b), term := t }
  | _ => .error "aggregate as a number"

/-- The bytes of a string literal as values of `0 .. 255`. -/
def bytesZahl : List Int → Option (List (Zahl 0 255))
  | [] => some []
  | b :: bs =>
    if h : 0 ≤ b ∧ b ≤ 255 then (bytesZahl bs).map (⟨b, h.1, h.2⟩ :: ·) else none

theorem bytesZahl_laenge : ∀ (bs : List Int) (zs : List (Zahl 0 255)), bytesZahl bs = some zs → zs.length = bs.length
  | [], zs, h => by simp only [bytesZahl, Option.some.injEq] at h; subst h; rfl
  | b :: bs, zs, h => by
    unfold bytesZahl at h
    split at h
    · cases hz : bytesZahl bs with
      | none => rw [hz] at h; cases h
      | some ys =>
        rw [hz] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        simp only [List.length_cons, bytesZahl_laenge bs ys hz]
    · cases h

/-- A string literal at the type of its own length. -/
def lowText {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (bs : List Int) : Except String (LowWert u Γ Λ) :=
  match bytesZahl bs with
  | some zs => .ok ⟨.str zs.length, Expr.strLit zs (Nat.le_refl _)⟩
  | none => .error "string literal outside bytes"

/-- `a[i]`: an element of an array (the index fitted into `0 ..< n`) or a byte of a string. -/
def idxW {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} :
    LowWert u Γ Λ → LowSide u Γ Λ → Except String (LowWert u Γ Λ)
  | ⟨.arr τ n, t⟩, i =>
    if h1 : 0 ≤ i.range.1 then
      if h2 : i.range.2 ≤ (n : Int) - 1 then .ok ⟨τ, Expr.arrGet t (Expr.widen h1 h2 i.term)⟩
      else .error "index outside the array"
    else .error "index outside the array"
  | ⟨.str _, t⟩, i => .ok ⟨.int 0 255, Expr.strGet t i.term⟩
  | _, _ => .error "index of a value without elements"

/-- `lenof(a)`: the length of a string, the (constant) length of an array. -/
def lenW {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} : LowWert u Γ Λ → Except String (LowWert u Γ Λ)
  | ⟨.str n, t⟩ => .ok ⟨.int 0 n, Expr.strLen t⟩
  | ⟨.arr _ n, _⟩ => .ok ⟨.int n n, Expr.lit n⟩
  | _ => .error "lenof of a value without length"

/-- A value fitted to the type `τ`: the same type, a number widened into a larger range, a string under a larger
    maximum; everything else is refused. -/
def fitW {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (τ : Ty) (w : LowWert u Γ Λ) :
    Except String (Expr (declOf u) Γ Λ τ) :=
  if h : w.ty = τ then .ok (h ▸ w.term) else
  match w, τ with
  | ⟨.int a b, t⟩, .int lo hi =>
    if h1 : lo ≤ a then
      if h2 : b ≤ hi then .ok (Expr.widen h1 h2 t) else .error "value outside range"
    else .error "value outside range"
  | ⟨.str n, t⟩, .str m => if n ≤ m then .ok (Expr.strWeit m t) else .error "string longer than the maximum"
  | _, _ => .error "value of another type"

/-- `a[i] = v` on an array value: the array with the element replaced. -/
def updW {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} :
    LowWert u Γ Λ → LowSide u Γ Λ → LowWert u Γ Λ → Except String (LowWert u Γ Λ)
  | ⟨.arr τ n, t⟩, i, v =>
    if h1 : 0 ≤ i.range.1 then
      if h2 : i.range.2 ≤ (n : Int) - 1 then
        match fitW τ v with
        | .ok v' => .ok ⟨.arr τ n, Expr.arrSet t (Expr.widen h1 h2 i.term) v'⟩
        | .error e => .error e
      else .error "index outside the array"
    else .error "index outside the array"
  | _, _, _ => .error "element write into a value without elements"

/-- `s + t` on two strings, the maximum the sum of the maxima. -/
def catW {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} :
    LowWert u Γ Λ → LowWert u Γ Λ → Except String (LowWert u Γ Λ)
  | ⟨.str n, s⟩, ⟨.str m, t⟩ => .ok ⟨.str (n + m), Expr.strCat s t⟩
  | ⟨.int .., _⟩, _ | _, ⟨.int .., _⟩ => .error "number added to an aggregate"
  | _, _ => .error "addition of aggregates without G form"

/-- `[a, rest…]`: the element in front of an array of its type. -/
def consW {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} :
    LowWert u Γ Λ → LowWert u Γ Λ → Except String (LowWert u Γ Λ)
  | a, ⟨.arr τ n, r⟩ =>
    match fitW τ a with
    | .ok a' => .ok ⟨.arr τ (n + 1), Expr.arrCons a' r⟩
    | .error e => .error e
  | _, _ => .error "array literal without G form"

/-- An aggregate parameter or local (a number or any other kind goes to the integer lowering). -/
def lowParamWert (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (sh : Nat) (p : String) :
    Option (Except String (LowWert u Γ Λ)) :=
  match paramPos fn.params p with
  | .error _ => none
  | .ok j =>
    match fn.kinds[j]?, fn.params[j]? with
    | some .wert, some (_, τ) | _, some (_, τ@Ty.never) =>
      some (match lowVar Γ (sh + j) τ with
        | .error e => .error e
        | .ok v => .ok ⟨τ, Expr.var v⟩)
    | _, _ => none

/-- An aggregate static (a number static goes to the integer lowering). -/
def lowGlobWert (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (p : String) :
    Option (Except String (LowWert u Γ Λ)) :=
  match globIdx u.globs p with
  | .error _ => none
  | .ok g =>
    match (globAt u g).ty with
    | .int .. | .bool => none
    | _ =>
      some (if hd : (∀ w ∈ (declOf u).gbraucht g, Res.von (declOf u) w ∈ Λ) then
        .ok ⟨(declOf u).gtyp g, Expr.glob (D := declOf u) g hd⟩
      else .error "access without held guard")

/-- An aggregate field read through a pointer parameter (`p.slots[i].f`); `none` for any other field. -/
def lowDurchWert (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (sh : Nat) (b fname : String)
    (ix : UIdx) : Option (Except String (LowWert u Γ Λ)) :=
  match paramPos fn.params b with
  | .error _ => none
  | .ok j =>
    match fn.kinds[j]? with
    | some (.ptr num w) =>
      if h : num < u.tabs.length then
        (fieldHitW u ⟨num, h⟩ fname).map fun fi =>
          match lowVar Γ (sh + j) (.ptr num w), lowIdx u Γ Λ fn sh ⟨num, h⟩ ix with
          | .ok v, .ok i =>
            if hL : (∀ wdd ∈ (declOf u).braucht ⟨num, h⟩, Res.von (declOf u) wdd ∈ Λ) then
              .ok ⟨_, Expr.thru (D := declOf u) (Expr.var v) ⟨num, h⟩ (tabNr_some u num h) fi i hL⟩
            else .error "access without held guard"
          | .error e, _ | _, .error e => .error e
      else none
    | _ => none

/-- An aggregate field read at a table (`T.slots[i].f`); `none` for any other field. -/
def lowTabWert (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (sh : Nat) (b fname : String)
    (ix : UIdx) : Option (Except String (LowWert u Γ Λ)) :=
  match tabIdx u.tabs b with
  | .error _ => none
  | .ok t =>
    (fieldHitW u t fname).map fun fi =>
      match lowIdx u Γ Λ fn sh t ix with
      | .ok i =>
        if hL : (∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) then
          .ok ⟨_, Expr.slot (D := declOf u) t fi i hL⟩
        else .error "access without held guard"
      | .error e => .error e

/-- A constant literal at its type (`USide.typed`): numbers inside the range, array literals element by element,
    string literals under the maximum. -/
def lowLit {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} : (τ : Ty) → USide → Except String (Expr (declOf u) Γ Λ τ)
  | .int lo hi, .lit n =>
    if h1 : lo ≤ n then
      if h2 : n ≤ hi then .ok (Expr.widen h1 h2 (Expr.lit n)) else .error "constant outside its range"
    else .error "constant outside its range"
  | .arr _ 0, .arrNil => .ok Expr.arrNil
  | .arr τ (k + 1), .arrCons a r =>
    match lowLit τ a, lowLit (.arr τ k) r with
    | .ok a', .ok r' => .ok (Expr.arrCons a' r')
    | .error e, _ | _, .error e => .error e
  | .str m, .text bs =>
    match bytesZahl bs with
    | some zs => if h : zs.length ≤ m then .ok (Expr.strLit zs h) else .error "string literal longer than the maximum"
    | none => .error "string literal outside bytes"
  | _, _ => .error "constant without G form"

/-- The integer side of a value. -/
def zahlVon {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} :
    Except String (LowWert u Γ Λ) → Except String (LowSide u Γ Λ)
  | .ok w => w.zahl
  | .error e => .error e

/-- A value of any type (`LowWert`), in an `ensures` (`er` the result type) or a body (`er = none`): literals,
    parameters, statics, slot reads, `old` and `result`, the integer arithmetic, and the aggregate forms (arrays and
    strings by their type). One structural recursion, so that the lowering stays reducible. -/
def lowWertE (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option Ty) : USide → Except String (LowWert u Γ Λ)
  | .lit n => .ok (LowSide.wert { range := (n, n), term := Expr.lit n })
  | .param p =>
    match lowParamWert u Γ Λ fn (if er.isSome then 1 else 0) p with
    | some r => r
    | none => (lowParamSide u Γ Λ fn (if er.isSome then 1 else 0) p).map LowSide.wert
  | .glob p =>
    match lowGlobWert u Γ Λ p with
    | some r => r
    | none => (lowGlobSide u Γ Λ p).map LowSide.wert
  | .slot b f ix =>
    match lowDurchWert u Γ Λ fn (if er.isSome then 1 else 0) b f ix with
    | some r => r
    | none => (lowDurch u Γ Λ fn (if er.isSome then 1 else 0) b f ix).map LowSide.wert
  | .refSlot r f =>
    (lowRefRead u Γ Λ fn (if er.isSome then 1 else 0) r f).map LowSide.wert
  | .tab b f ix =>
    match lowTabWert u Γ Λ fn (if er.isSome then 1 else 0) b f ix with
    | some r => r
    | none => (lowTabRead u Γ Λ fn (if er.isSome then 1 else 0) b f ix).map LowSide.wert
  | .old b f ix =>
    (lowAltRead u Γ Λ fn (if er.isSome then 1 else 0) b f ix).map LowSide.wert
  | .add a b =>
    match lowWertE u Γ Λ fn er a, lowWertE u Γ Λ fn er b with
    | .ok ⟨.int a1 a2, x⟩, .ok ⟨.int b1 b2, y⟩ =>
      .ok (LowSide.plus { range := (a1, a2), term := x } { range := (b1, b2), term := y }).wert
    | .ok wa, .ok wb => catW wa wb
    | .error e, _ | _, .error e => .error e
  | .sub a b =>
    match zahlVon (lowWertE u Γ Λ fn er a), zahlVon (lowWertE u Γ Λ fn er b) with
    | .ok x, .ok y => .ok (LowSide.minus x y).wert
    | .error e, _ | _, .error e => .error e
  | .mul a b =>
    match zahlVon (lowWertE u Γ Λ fn er a), zahlVon (lowWertE u Γ Λ fn er b) with
    | .ok x, .ok y => .ok (LowSide.times x y).wert
    | .error e, _ | _, .error e => .error e
  | .conv lo hi a =>
    match zahlVon (lowWertE u Γ Λ fn er a) with
    | .error e => .error e
    | .ok x => (LowSide.conv lo hi x).map LowSide.wert
  | .band a b => (lowZwei LowSide.and (zahlVon (lowWertE u Γ Λ fn er a)) (zahlVon (lowWertE u Γ Λ fn er b))).map LowSide.wert
  | .bor a b => (lowZwei LowSide.or (zahlVon (lowWertE u Γ Λ fn er a)) (zahlVon (lowWertE u Γ Λ fn er b))).map LowSide.wert
  | .bxor a b => (lowZwei LowSide.xoder (zahlVon (lowWertE u Γ Λ fn er a)) (zahlVon (lowWertE u Γ Λ fn er b))).map LowSide.wert
  | .div a b => (lowZwei LowSide.durch (zahlVon (lowWertE u Γ Λ fn er a)) (zahlVon (lowWertE u Γ Λ fn er b))).map LowSide.wert
  | .rem a b => (lowZwei LowSide.rest (zahlVon (lowWertE u Γ Λ fn er a)) (zahlVon (lowWertE u Γ Λ fn er b))).map LowSide.wert
  | .shl a b => (lowZwei LowSide.links (zahlVon (lowWertE u Γ Λ fn er a)) (zahlVon (lowWertE u Γ Λ fn er b))).map LowSide.wert
  | .shr a b => (lowZwei LowSide.rechts (zahlVon (lowWertE u Γ Λ fn er a)) (zahlVon (lowWertE u Γ Λ fn er b))).map LowSide.wert
  | .neg a =>
    match zahlVon (lowWertE u Γ Λ fn er a) with
    | .error e => .error e
    | .ok x => .ok (LowSide.minusEins x).wert
  | .erg =>
    match er with
    | some (.int a b) =>
      match lowVar Γ 0 (.int a b) with
      | .error e => .error e
      | .ok v => .ok ⟨.int a b, Expr.var v⟩
    | none =>
      match paramPos fn.params "#erg", fn.params.find? (·.1 == "#erg") with
      | .ok j, some (_, .int a b) =>
        match lowVar Γ j (.int a b) with
        | .error e => .error e
        | .ok v => .ok ⟨.int a b, Expr.var v⟩
      | _, _ => .error "result without result"
    | _ => .error "result without result"
  | .text bs => lowText bs
  | .arrNil => .error "an empty array literal needs its type"
  | .arrCons a r =>
    match lowWertE u Γ Λ fn er a, lowWertE u Γ Λ fn er r with
    | .ok wa, .ok wr => consW wa wr
    | .error e, _ | _, .error e => .error e
  | .idx a i =>
    match lowWertE u Γ Λ fn er a, zahlVon (lowWertE u Γ Λ fn er i) with
    | .ok wa, .ok wi => idxW wa wi
    | .error e, _ | _, .error e => .error e
  | .len a =>
    match lowWertE u Γ Λ fn er a with
    | .ok wa => lenW wa
    | .error e => .error e
  | .upd a i v =>
    match lowWertE u Γ Λ fn er a, zahlVon (lowWertE u Γ Λ fn er i), lowWertE u Γ Λ fn er v with
    | .ok wa, .ok wi, .ok wv => updW wa wi wv
    | .error e, _, _ | _, .error e, _ | _, _, .error e => .error e
  | .typed τ s => (lowLit τ s).map (⟨τ, ·⟩)
  | .eng s lo' hi' =>
    match lowWertE u Γ Λ fn er s with
    | .ok ⟨.int _ _, t⟩ =>
      if h : lo' ≤ hi' then .ok ⟨.int lo' hi', Expr.eng t lo' hi' (Expr.widen (Int.le_refl lo') h (Expr.lit lo'))⟩
      else .error "narrowing to an empty range"
    | .ok _ => .error "narrowing of a non-number"
    | .error e => .error e

/-- A comparison side in `ensures`: literals, numeric parameters,
    slot reads, `old` and `result` travel (the integer values of `lowWertE`). -/
def lowSideEns (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option Ty) (s : USide) : Except String (LowSide u Γ Λ) :=
  zahlVon (lowWertE u Γ Λ fn er s)

/-- A value at the type `τ` (checking mode): an array literal element by element, everything else by `fitW`. -/
def lowWertAtE (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (er : Option Ty) :
    (τ : Ty) → USide → Except String (Expr (declOf u) Γ Λ τ)
  | .arr _ 0, .arrNil => .ok Expr.arrNil
  | .arr τ (k + 1), .arrCons a r =>
    match lowWertAtE u Γ Λ fn er τ a, lowWertAtE u Γ Λ fn er (.arr τ k) r with
    | .ok a', .ok r' => .ok (Expr.arrCons a' r')
    | .error e, _ | _, .error e => .error e
  | τ, s =>
    match lowWertE u Γ Λ fn er s with
    | .ok w => fitW τ w
    | .error e => .error e

/-- A value side in a body: the sides of an `ensures` without `old` and `result` (a body reads neither). -/
def lowSideVal (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (s : USide) : Except String (LowSide u Γ Λ) :=
  if seiteAltErg s then .error "side in body without G form"
  else lowSideEns u Γ Λ fn none s

/-- One comparison in `ensures` (G folds all but `lt`/`le`/`eq`). -/
def lowCmp (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option Ty) :
    String → USide → USide → Except String (Expr (declOf u) Γ Λ .bool)
  | op, a, b =>
    match lowWertE u Γ Λ fn er a, lowWertE u Γ Λ fn er b with
    | .ok ⟨.str _, x⟩, .ok ⟨.str _, y⟩ =>
      match op with
      | "==" => .ok (Expr.strEq x y)
      | "!=" => .ok (Expr.not (Expr.strEq x y))
      | "<" => .ok (Expr.strLt x y)
      | "<=" => .ok (Expr.or (Expr.strLt x y) (Expr.strEq x y))
      | ">" => .ok (Expr.strLt y x)
      | ">=" => .ok (Expr.or (Expr.strLt y x) (Expr.strEq x y))
      | _ => .error "operator without G form"
    | _, _ =>
    match lowSideEns u Γ Λ fn er a with
    | .error e => .error e
    | .ok s1 =>
      match lowSideEns u Γ Λ fn er b with
      | .error e => .error e
      | .ok s2 =>
        match op with
        | "==" => .ok (Expr.eq s1.term s2.term)
        | "!=" => .ok (Expr.not (Expr.eq s1.term s2.term))
        | "<" => .ok (Expr.lt s1.term s2.term)
        | "<=" => .ok (Expr.le s1.term s2.term)
        | ">" => .ok (Expr.lt s2.term s1.term)
        | ">=" => .ok (Expr.le s2.term s1.term)
        | _ => .error "operator without G form"

/-! ### Option values (`Ty.opt n`, `option index into T`)

An option value is `None` (`Expr.none`), `Some(i)` (`Expr.some` of an index expression of the table), an option
variable (a parameter or a `let`) or the read of an option field through a pointer (`Expr.thru`) or at a table
(`Expr.slot`). The field's type is `typAt u t f = .opt n` with `n` the count of the table the option indexes
(`OptHit`); the term is cast along that fact, as the integer reads are (`durchTerm`, `slotTerm`). -/

/-- An option field read through a pointer parameter, at its type `opt n`. -/
def durchTermO (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (num : Nat) (h : num < u.tabs.length)
    (oh : OptHit u ⟨num, h⟩) {w : Bool} (v : Var Γ (.ptr num w))
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count ⟨num, h⟩)))
    (hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩, Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ (.opt oh.n) := by
  rw [← oh.hopt]
  exact Expr.thru (D := declOf u) (Expr.var v) ⟨num, h⟩ (tabNr_some u num h) oh.idx i hL

/-- An option field read at a table, at its type `opt n`. -/
def slotTermO (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (t : Fin u.tabs.length) (oh : OptHit u t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ (.opt oh.n) := by
  rw [← oh.hopt]
  exact Expr.slot (D := declOf u) t oh.idx i hL

/-- An option value over the table `num` (positions of parameters shift by `sh`, see `lowIdx`). -/
def lowOpt (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (sh : Nat)
    (num : Nat) (hnum : num < u.tabs.length) :
    UOpt → Except String (Expr (declOf u) Γ Λ (.opt ((declOf u).count ⟨num, hnum⟩)))
  | .nichts => .ok (Expr.none (D := declOf u) _)
  | .etwas ix =>
    match lowIdx u Γ Λ fn sh ⟨num, hnum⟩ ix with
    | .error e => .error e
    | .ok i => .ok (Expr.some (D := declOf u) i)
  | .var p =>
    match paramPos fn.params p with
    | .error e => .error e
    | .ok j =>
      match fn.kinds[j]? with
      | some (.opt m) =>
        if m == num then
          match lowVar Γ (sh + j) (.opt ((declOf u).count ⟨num, hnum⟩)) with
          | .error e => .error e
          | .ok v => .ok (Expr.var v)
        else .error "option of a foreign table"
      | _ => .error "option without G form"
  | .slot b f ix =>
    match paramPos fn.params b with
    | .error e => .error e
    | .ok j =>
      match fn.kinds[j]? with
      | some (.ptr pnum w) =>
        if h : pnum < u.tabs.length then
          match fieldHitO u ⟨pnum, h⟩ f with
          | .error e => .error e
          | .ok oh =>
            if hn : oh.n = (declOf u).count ⟨num, hnum⟩ then
              match lowVar Γ (sh + j) (.ptr pnum w) with
              | .error e => .error e
              | .ok pv =>
                match lowIdx u Γ Λ fn sh ⟨pnum, h⟩ ix with
                | .error e => .error e
                | .ok i =>
                  if hL : (∀ wdd ∈ (declOf u).braucht ⟨pnum, h⟩, Res.von (declOf u) wdd ∈ Λ) then
                    .ok (by rw [← hn]; exact durchTermO u Γ Λ pnum h oh pv i hL)
                  else .error "access without held guard"
            else .error "option of a foreign table"
        else .error "pointer table unknown"
      | _ => .error "place without G form"
  | .tab b f ix =>
    match tabIdx u.tabs b with
    | .error e => .error e
    | .ok t =>
      match fieldHitO u t f with
      | .error e => .error e
      | .ok oh =>
        if hn : oh.n = (declOf u).count ⟨num, hnum⟩ then
          match lowIdx u Γ Λ fn sh t ix with
          | .error e => .error e
          | .ok i =>
            if hL : (∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) then
              .ok (by rw [← hn]; exact slotTermO u Γ Λ t oh i hL)
            else .error "access without held guard"
        else .error "option of a foreign table"
  | .glob p =>
    match globIdx u.globs p with
    | .error e => .error e
    | .ok g =>
      if hd : (∀ w ∈ (declOf u).gbraucht g, Res.von (declOf u) w ∈ Λ) then
        if h : (declOf u).gtyp g = .opt ((declOf u).count ⟨num, hnum⟩) then
          .ok (h ▸ Expr.glob (D := declOf u) g hd)
        else .error "option of a foreign table"
      else .error "access without held guard"

/-- One `ensures` predicate. -/
def lowEns (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option Ty) :
    UEns → Except String (Expr (declOf u) Γ Λ .bool)
  | .cmp op a b => lowCmp u Γ Λ fn er op a b
  | .tru => .ok Expr.tru
  | .fls => .ok Expr.fls
  | .and a b =>
    match lowEns u Γ Λ fn er a with
    | .error e => .error e
    | .ok x =>
      match lowEns u Γ Λ fn er b with
      | .error e => .error e
      | .ok y => .ok (Expr.and x y)
  | .or a b =>
    match lowEns u Γ Λ fn er a with
    | .error e => .error e
    | .ok x =>
      match lowEns u Γ Λ fn er b with
      | .error e => .error e
      | .ok y => .ok (Expr.or x y)
  | .not a =>
    match lowEns u Γ Λ fn er a with
    | .error e => .error e
    | .ok x => .ok (Expr.not x)
  | .globB p => lowGlobBool u Γ Λ p
  | .ergB =>
    match er with
    | some .bool =>
      match lowVar Γ 0 .bool with
      | .error e => .error e
      | .ok v => .ok (Expr.var v)
    | none =>
      match paramPos fn.params "#erg", fn.params.find? (·.1 == "#erg") with
      | .ok j, some (_, .bool) =>
        match lowVar Γ j .bool with
        | .error e => .error e
        | .ok v => .ok (Expr.var v)
      | _, _ => .error "result without result"
    | _ => .error "result without result"
  | .var p =>
    match paramPos fn.params p with
    | .error e => .error e
    | .ok j =>
      match lowVar Γ ((if er.isSome then 1 else 0) + j) .bool with
      | .error e => .error e
      | .ok v => .ok (Expr.var v)
  | .istSome o num =>
    if h : num < u.tabs.length then
      match lowOpt u Γ Λ fn (if er.isSome then 1 else 0) num h o with
      | .error e => .error e
      | .ok x => .ok (Expr.istSome x)
    else .error "option table unknown"
  | .slotB b f ix => lowBoolDurch u Γ Λ fn (if er.isSome then 1 else 0) b f ix
  | .tabB b f ix => lowBoolTab u Γ Λ fn (if er.isSome then 1 else 0) b f ix
  | .alle tn x body =>
    match tabIdx u.tabs tn, ergAlsParam fn er with
    | .error e, _ => .error e
    | _, .error e => .error e
    | .ok t, .ok fnR =>
      if hL : (∀ w ∈ (declOf u).braucht t, Res.von (declOf u) w ∈ Λ) then
        match lowEns u (.index ((declOf u).count t) :: Γ) Λ (fnR.mitIndex x t.val ((declOf u).count t)) none body with
        | .error e => .error e
        | .ok b => .ok (Expr.forallSlots (D := declOf u) t b hL)
      else .error "access without held guard"
  | .einige tn x body =>
    match tabIdx u.tabs tn, ergAlsParam fn er with
    | .error e, _ => .error e
    | _, .error e => .error e
    | .ok t, .ok fnR =>
      if hL : (∀ w ∈ (declOf u).braucht t, Res.von (declOf u) w ∈ Λ) then
        match lowEns u (.index ((declOf u).count t) :: Γ) Λ (fnR.mitIndex x t.val ((declOf u).count t)) none body with
        | .error e => .error e
        | .ok b => .ok (Expr.existsSlots (D := declOf u) t b hL)
      else .error "access without held guard"

/-- The `ensures` conjunction (empty is `.tru`). -/
def lowEnsList (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option Ty) :
    List UEns → Except String (Expr (declOf u) Γ Λ .bool)
  | [] => .ok Expr.tru
  | e :: rest =>
    match lowEns u Γ Λ fn er e with
    | .error err => .error err
    | .ok x =>
      match lowEnsList u Γ Λ fn er rest with
      | .error err => .error err
      | .ok y =>
        match y with
        | Expr.tru => .ok x
        | _ => .ok (Expr.and x y)

end Gabbro.Grammatik.Parser.UebersetzeAllg

/-
  CUTS: what is not proved here.

  1. This file builds the generic declaration `declOf` (Fin carriers)
     and lowers sides and `ensures` (`lowIdx` through `lowEnsList`).
     NOT yet built: statement lowering (`assign`/`call`), `RufPasst`
     assembly, bodies, `lowerAllg`, the 104/108 fragment and footprint
     pins, the data agreement, the real-text lexer pin and the chaining
     theorem. Those remain open work.
  2. `beq`-style soundness is proved for nothing here; there are no
     `beq` lemmas in this file.
  3. Elaboration lessons (for the lane that continues): pin `D`
     explicitly on every constructor over the Fin carriers
     (`Expr.slot (D := declOf u)` etc.), since `D` never unifies out
     of a stuck `(declOf u).Tab` projection; keep struct literals on
     one line (a trailing comma at end of line misparses); a term
     continuation line must not start with `(` (it parses as a tactic).
-/

#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.notEmpty_ne_nil
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.sigAt_get
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.params_eq
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.erg_eq
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.haelt_eq
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.ende_eq
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.rangeO_some
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.typAt_of
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.tabNr_some
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.fieldPos_lt
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.fieldAtPos_get
