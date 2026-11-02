module

public import Grammatik.Kern.Syntax.Zucker
public import Grammatik.Parser.Elab.Uebersetze
public import Grammatik.Parser.Elab.Generic.Signatures

@[expose] public section



namespace Gabbro.Grammatik.Parser.UebersetzeAllg

open Gabbro.Grammatik.Parser.Uebersetze

/-! ## Declaration data looked up from `UProg` -/

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
