module
public import Grammatik.Parser.Elab.UebersetzeAllg.TableCapabilities
@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.Uebersetze

/-- Successful source space resolution names an actual entry in the same declaration list. -/
theorem uDataSpace_sound (spaces : List String) (name : String) (index : Nat)
    (accepted : uDataSpace spaces name = .ok index) : spaces[index]? = some name := by
  unfold uDataSpace at accepted
  split at accepted
  · rename_i found number lookup
    cases accepted
    have member := List.mem_of_find?_eq_some lookup
    have named := List.find?_some lookup
    have same : found = name := strEq_klingt named
    subst found
    exact List.mem_zipIdx_iff_getElem?.mp member
  · cases accepted

/-- Named normal and nonzero spaces keep their exact registered positions; unknown or absent
    normal spaces are refused. These are witnesses, not an executed measurement. -/
theorem uDataSpace_registered_zeuge :
    uDataSpace ["normal", "custom"] "normal" = .ok 0 ∧
    uDataSpace ["normal", "custom"] "custom" = .ok 1 ∧
    uDataSpace ["normal", "custom"] "unknown" = .error "unknown data space: unknown" ∧
    uDataSpace [] "normal" = .error "unknown data space: normal" := ⟨rfl, rfl, rfl, rfl⟩

/-- Successful sequencing retains every accepted source parameter row. -/
private theorem parameterRows_origin {α β : Type} (produce : α → Except String β)
    {sources : List α} {rows : List β} (accepted : uSeq (sources.map produce) = .ok rows) :
    ∀ row ∈ rows, ∃ source ∈ sources, produce source = .ok row := by
  induction sources generalizing rows with
  | nil =>
    cases accepted
    simp
  | cons source sources ih =>
    cases first : produce source with
    | error error => simp [List.map_cons, uSeq, first] at accepted
    | ok row =>
      cases rest : uSeq (sources.map produce) with
      | error error => simp [List.map_cons, uSeq, first, rest] at accepted
      | ok tail =>
        have same : row :: tail = rows := by
          simpa only [List.map_cons, first, uSeq, rest, Except.ok.injEq] using accepted
        subst rows
        intro output member
        rcases List.mem_cons.mp member with same | member
        · subst output; exact ⟨source, List.mem_cons_self .., first⟩
        · obtain ⟨original, member, produced⟩ := ih rest output member
          exact ⟨original, List.mem_cons_of_mem _ member, produced⟩

/-- The function-head projection keeps every row in order, including its exact pointer type. -/
private theorem parameterRows_coherent (rows : List (String × Ty × UParamArt))
    (coherent : ∀ row ∈ rows, ∀ cap, row.2.2 = .ptr cap → row.2.1 = .ptr cap) :
    ∀ j cap, (rows.map (·.2.2))[j]? = some (.ptr cap) →
      (((rows.map (·.1)).zip (rows.map (·.2.1)))[j]?).map (·.2) = some (.ptr cap) := by
  induction rows with
  | nil => intro j cap kind; simp at kind
  | cons row rows ih =>
    intro j cap kind
    cases j with
    | zero =>
      have exactType := coherent row (List.mem_cons_self ..) cap (by simpa using kind)
      simpa only [List.map_cons, List.zip_cons_cons, List.getElem?_cons_zero,
        Option.map_some] using congrArg some exactType
    | succ j =>
      exact ih (fun row member => coherent row (List.mem_cons_of_mem _ member)) j cap
        (by simpa using kind)

variable (consts : List (String × Int)) (alias : List (String × (Int × Int)))
    (tabs : List UTab) (locks : List ULock) (globs : List UGlob) (whys : List UWhy)
    (sums : List USum) (devs zeiger : List String) (zb : Nat) (spaces : List String)
    (named : List (String × Ty)) (eigner : List String)

private theorem producedRows_coherent {sources : List (String × STyp)}
    {rows : List (String × Ty × UParamArt)}
    (accepted : uSeq (sources.map (uParam alias tabs sums whys zeiger zb spaces named eigner)) =
      .ok rows) :
    ∀ j cap, (rows.map (·.2.2))[j]? = some (.ptr cap) →
      (((rows.map (·.1)).zip (rows.map (·.2.1)))[j]?).map (·.2) = some (.ptr cap) := by
  apply parameterRows_coherent rows
  intro row member cap kind
  obtain ⟨source, _, produced⟩ := parameterRows_origin _ accepted row member
  exact uParam_pointer_coherent alias tabs sums whys zeiger zb spaces named eigner produced cap kind

/-- A successful canonical head producer retains pointer kinds and types at the same position. -/
theorem elabKopf_pointer_coherent {sig : FnSig} {kopf : UFnKopf} {writes : List String}
    (accepted : elabKopf consts alias tabs locks globs whys sums sig devs zeiger zb spaces named eigner =
      .ok (kopf, writes)) :
    ∀ j cap, kopf.kinds[j]? = some (.ptr cap) →
      ((kopf.names.zip kopf.types)[j]?).map (·.2) = some (.ptr cap) := by
  unfold elabKopf at accepted
  repeat' split at accepted
  all_goals cases accepted
  all_goals exact producedRows_coherent alias tabs whys sums zeiger zb spaces named eigner (by assumption)

/-- A successful source function satisfies the actual pointer gate; no well-typedness premise
    is added at its consumers. The canonical producer supplies both metadata equalities. -/
theorem elabUFunktion_checkedPointerParam
    (koepfe : List UFnKopf) (sig : FnSig) (body : SAnw) (annahmen : List String)
    (regs : List UReg) (zustaende : List UZustand)
    (specs : List (String × List String × SExpr)) (arrKonst : List (String × USide))
    (valueScope : UTypeScope) {fn : UFn}
    (accepted : elabUFunktion consts alias tabs locks globs koepfe sig body annahmen whys sums
      devs regs zustaende zeiger zb specs arrKonst spaces valueScope eigner = .ok fn)
    (j : Nat) (cap : DataCapTy) (kind : fn.kinds[j]? = some (.ptr cap)) :
    ∃ certificate, checkedPointerParam fn j cap = .ok certificate := by
  unfold elabUFunktion at accepted
  split at accepted
  · cases accepted
  · rename_i kopf writes head
    have coherent := elabKopf_pointer_coherent consts alias tabs locks globs whys sums devs zeiger
      zb spaces valueScope.types eigner head
    repeat' split at accepted
    all_goals cases accepted
    all_goals exact checkedPointerParam_complete _ j cap kind (coherent j cap kind)

end Gabbro.Grammatik.Parser.UebersetzeAllg
