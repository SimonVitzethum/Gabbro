module

public import Grammatik.Kern.Syntax.Zucker
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil12

@[expose] public section



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

/-- The carriers of an invariant, by name: a table, else a static (C05). `uInv` resolves every name to exactly
    one carrier, so for an elaborated unit nothing is dropped. -/
def invTraeger (u : UProg) (i : Fin u.invs.length) : List (Fin u.tabs.length ⊕ Fin u.globs.length) :=
  (invAt u i).traeger.filterMap fun n =>
    match (tabIdx u.tabs n).toOption with
    | some t => some (.inl t)
    | none => (globIdx u.globs n).toOption.map .inr

/-- `U003` at an invariant, decided over the elaborated functions: a writer of a carrier (a table through
    `writesAt`, a static through `writesGAt`) holds every lock that guards a carrier (the elaborator refuses a
    unit where it fails, `uU003`, and so does the lowering, `lowerInvAt`). -/
def invOkB (u : UProg) (i : Fin u.invs.length) : Bool :=
  (u.fns ++ u.ptrs).all fun f =>
    !((invTraeger u i).any (Sum.elim (writesAt u f) (writesGAt u f))) ||
    (invTraeger u i).all fun c => (Sum.elim (needsAt u) (gneedsAt u) c).all fun w =>
      match w with
      | .inl L => decide (L ∈ heldAt u f)
      | .inr _ => true

/-- The carriers of an invariant in the declaration: its carriers where `U003` holds (always, for a lowered
    unit: `lowerInvAt` refuses otherwise), none otherwise -- so `invarianten_gehalten` holds for every `UProg`.
    The fallback is never reached by a unit that lowers (`traegerD_of_ok`, `lowerInvAt_facts`). -/
def traegerD (u : UProg) (i : Fin u.invs.length) : List (Fin u.tabs.length ⊕ Fin u.globs.length) :=
  if invOkB u i then invTraeger u i else []

/-- Where `U003` holds, the declared carriers are ALL the invariant's carriers. -/
theorem traegerD_of_ok (u : UProg) (i : Fin u.invs.length) (h : invOkB u i = true) :
    traegerD u i = invTraeger u i := by
  unfold traegerD
  rw [if_pos h]

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
    fun c hc => ?_, (OwnerFlow.empty_of_empty S.owner).trans (OwnerFlow.empty_of_empty T.owner).symm⟩
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

end Gabbro.Grammatik.Parser.UebersetzeAllg
