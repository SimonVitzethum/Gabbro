module

public import Grammatik.Kern.Syntax.Zucker
public import Grammatik.Parser.Elab.Uebersetze
public import Grammatik.Parser.Elab.UebersetzeAllg.Konform

@[expose] public section



namespace Gabbro.Grammatik.Parser.UebersetzeAllg

open Gabbro.Grammatik.Parser.Uebersetze

/-! ## Declaration data looked up from `UProg` -/

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

/-- Signatures and conformance (`mkSig` through `passtAt_lt`) live in `Konform`
    (C06, 2026-11-02, pure move): this file keeps the carrier/field/foreign
    lookups, the invariant bridge and `declOf`. -/

/-- `invarianten_gehalten` for the declaration of every `UProg`. -/
theorem invGehalten (u : UProg) (n : Nat) (i : Fin u.invs.length)
    (h : (traegerD u i).any (Sum.elim (sigAt u n).schreibt (sigAt u n).gschreibt) = true)
    (c : Fin u.tabs.length ⊕ Fin u.globs.length) (hc : c ∈ traegerD u i)
    (L : Fin u.locks.length) (hL : Sum.inl L ∈ Sum.elim (needsAt u) (gneedsAt u) c) :
    L ∈ (sigAt u n).haelt := by
  unfold traegerD at h hc
  cases hok : invOkB u i with
  | false => rw [hok] at hc; simp only [Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at hc
  | true =>
    rw [hok] at h hc
    simp only [if_true] at h hc
    by_cases hn : n < (sigFns u).length
    · have hs : sigAt u n = mkSig u ((sigFns u).get ⟨n, hn⟩) := by unfold sigAt; rw [dif_pos hn]
      rw [hs] at h ⊢
      unfold invOkB at hok
      have hf := List.all_eq_true.mp hok ((sigFns u).get ⟨n, hn⟩) (List.get_mem _ _)
      simp only [Bool.or_eq_true, Bool.not_eq_true'] at hf
      rcases hf with hf | hf
      · have h' : (invTraeger u i).any (Sum.elim (writesAt u ((sigFns u).get ⟨n, hn⟩))
            (writesGAt u ((sigFns u).get ⟨n, hn⟩))) = true := h
        rw [hf] at h'
        cases h'
      · have hc' := List.all_eq_true.mp hf c hc
        have hw := List.all_eq_true.mp hc' (Sum.inl L) hL
        exact of_decide_eq_true hw
    · have hs : sigAt u n = dummySig u := by unfold sigAt; rw [dif_neg hn]
      rw [hs] at h
      simp only [List.any_eq_true] at h
      obtain ⟨x, _, hx⟩ := h
      cases x <;> simp only [dummySig, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true] at hx

/-- A non-empty emptiness test means a non-empty list. -/
theorem notEmpty_ne_nil (l : List α) (h : (!l.isEmpty) = true) :
    l ≠ [] := by
  cases l with
  | nil => simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true] at h
  | cons _ _ => simp only [ne_eq, reduceCtorEq, not_false_eq_true]

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
  dataSpaces := u.spaces
  tableSpace := fun t => (tabAt u t).space
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
  passt_ok := fun f n h => (passtAt_ok u f n h).1
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
          exact ⟨by simp only [hp, Option.isSome_some], hc.1, t.val, hc.2, by simp only [t.isLt, ↓reduceDIte, Fin.eta]⟩
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

end Gabbro.Grammatik.Parser.UebersetzeAllg
