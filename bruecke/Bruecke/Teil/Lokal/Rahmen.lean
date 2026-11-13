module
public import Bruecke.Teil.Lokal.Ruf
public import Bruecke.Teil.Abschluss
public import Bruecke.Anweisung.Lokal.Rahmen
public import Bruecke.Anweisung.Lokal.Glob
@[expose] public section

/-! Partial frames in every binding scope; only actual carried callees need shape duties. -/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

/-- A lowered body statement writes a carrier the function declares, or calls a function it
    finds by name whose declared writes are its own -- in every scope. -/
theorem stmt_statisch_teilB {loopMode : Bool} (S : Getragen u C) (c : Fin u.fns.length) (hc : C c) {Γ : Ctx} {fn : UFn}
    (hΓ : Γ = fn.params.map (·.2)) (st : UStmt)
    (hmem : st ∈ (fnAt u c).body) {Λ Λ' : List (Res (declOf u))}
    {g : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ'}
    (h : lowStmtL (l := loopMode) u c Γ fn Λ st = .ok ⟨Λ', g⟩) {bst : Gabbro.Body.Stmt}
    (hb : stmtBody u fn st = some bst) :
    (∃ cn idx fld ve, bst = .assign cn idx fld ve ∧ cn ∈ (fnAt u c).puts) ∨
    (∃ n ve, bst = .assignGlobal n ve ∧ n ∈ (fnAt u c).gputs) ∨
    (∃ cname ps es pre gf, bst = .call cname ps es pre ∧ fnSuch u cname = some gf ∧
      ∀ w ∈ writesU gf, w ∈ writesU (fnAt u c)) := by
  cases st
  case assign b fname ix v =>
    rw [lowStmtL_assign S.tab c Γ fn Λ b fname ix v] at h
    have pointerWrite {space num j : Nat} {read : Bool} {owner : Option Nat}
        (pv : Var Γ (.ptr ⟨space, ⟨read, true, owner⟩, .table num⟩))
        (hj : paramPos fn.params b = .ok j)
        (hpv : lowVar Γ j (.ptr ⟨space, ⟨read, true, owner⟩, .table num⟩) = .ok pv)
        (hlt : num < u.tabs.length) (hw : writesAt u (fnAt u c) ⟨num, hlt⟩ = true) :
        ∃ cn idx fld ve, bst = .assign cn idx fld ve ∧ cn ∈ (fnAt u c).puts := by
      have hparam : (fn.params[j]?).map (·.2) =
          some (.ptr ⟨space, ⟨read, true, owner⟩, .table num⟩) := by
        simpa only [hΓ, List.getElem?_map] using (lowVar_typ Γ j _ pv hpv)
      have hpt := ptrTab_of_type fn b j num read true hj hparam hlt
      simp only [stmtBody, hpt] at hb
      cases hsv : sideExprG u fn v with
      | none => rw [hsv] at hb; cases hb
      | some ve =>
        rw [hsv] at hb
        cases hb
        exact ⟨_, _, _, _, rfl, any_mem hw⟩
    cases stored : lowAssignDurchL (l := loopMode) u c Γ fn Λ b fname ix v with
    | error error => simp only [stored, Except.map] at h <;> cases h
    | ok statement =>
      simp only [stored, Except.map] at h
      cases h
      have h := stored
      unfold lowAssignDurchL at h
      split at h
      · cases h
      · rename_i j hj
        split at h
        · rename_i space read num _
          split at h
          · rename_i hlt
            split at h
            · cases h
            · rename_i fh _
              split at h
              · cases h
              · rename_i pv hpv
                split at h
                · cases h
                · split at h
                  · cases h
                  · split at h
                    · split at h
                      · rename_i hw
                        exact .inl (pointerWrite pv hj hpv hlt hw)
                      · cases h
                    · cases h
          · cases h
        · rename_i space read owner num _
          split at h
          · rename_i hlt
            split at h
            · cases h
            · rename_i fh _
              split at h
              · cases h
              · rename_i m _
                split at h
                · cases h
                · rename_i pv hpv
                  split at h
                  · cases h
                  · split at h
                    · cases h
                    · split at h
                      · split at h
                        · split at h
                          · rename_i hw
                            exact .inl (pointerWrite pv hj hpv hlt hw)
                          · cases h
                        · cases h
                      · cases h
          · cases h
        · cases h
  case assignTab b fname ix v =>
    rw [lowStmtL_assignTab S.tab c Γ fn Λ b fname ix v] at h
    cases stored : lowAssignTabL (l := loopMode) u c Γ fn Λ b fname ix v with
    | error error => simp only [stored, Except.map] at h <;> cases h
    | ok statement =>
      simp only [stored, Except.map] at h
      cases h
      have h := stored
      simp only [lowAssignTabL] at h
      split at h
      · cases h
      · rename_i t ht
        repeat' split at h
        all_goals try cases h
        rename_i hw
        left
        simp only [stmtBody] at hb
        cases hsv : sideExprG u fn v with
        | none => rw [hsv] at hb; cases hb
        | some ve =>
          rw [hsv] at hb
          cases hb
          have hn := tabIdx_name _ _ _ ht
          have hw' : writesAt u (fnAt u c) t = true := hw
          unfold writesAt at hw'
          rw [show (tabAt u t).name = b from hn] at hw'
          exact ⟨_, _, _, _, rfl, any_mem hw'⟩
  case assignGlob n v =>
    simp only [lowStmtL] at h
    cases hs : lowAssignGlobL (l := loopMode) u c Γ fn Λ n v with
    | error err => simp only [hs, Except.map] at h; cases h
    | ok st =>
      simp only [hs, Except.map] at h
      cases h
      have hw := lowAssignGlob_writes c hs S.statics
      simp only [stmtBody] at hb
      cases he : sideExprG u fn v with
      | none => rw [he] at hb; cases hb
      | some e =>
        rw [he] at hb
        cases hb
        exact .inr (.inl ⟨n, e, rfl, hw⟩)
  case call cname args =>
    have h' : lowCallL (l := loopMode) u c Γ fn Λ cname args = .ok ⟨Λ', g⟩ := h
    unfold lowCallL at h'
    split at h'
    · cases h'
    · rename_i k hk
      obtain ⟨hcallee, _, hWr⟩ := lowRufKopf_ok hk
      right
      right
      have hfs : fnSuch u cname = some (fnAt u k.callee) := fnIdx_find _ _ _ hcallee
      simp only [stmtBody, hfs] at hb
      cases hes : argsExpr u fn args with
      | none => rw [hes] at hb; cases hb
      | some es =>
        rw [hes] at hb
        cases hb
        refine ⟨_, _, _, _, _, rfl, hfs, fun w hw => ?_⟩
        rcases List.mem_append.mp hw with hw | hw
        · obtain ⟨t, rfl⟩ := S.schreibt k.callee (callee_getragen_teil S hc hmem hfs) w hw
          have h1 : writesAt u (fnAt u k.callee) t = true := by
            unfold writesAt
            exact List.any_eq_true.mpr ⟨_, hw, beq_self_eq_true _⟩
          have h2 := hWr t h1
          exact List.mem_append_left _ (any_mem h2)
        · rcases List.mem_append.mp hw with hw | hw
          · obtain ⟨g, rfl⟩ := S.gschreibt k.callee (callee_getragen_teil S hc hmem hfs) w hw
            have h1 : writesGAt u (fnAt u k.callee) g = true := by
              unfold writesGAt
              exact List.any_eq_true.mpr ⟨_, hw, beq_self_eq_true _⟩
            have h2 := lowRufKopf_gwrites hk g h1
            exact writesU_global (any_mem h2)
          · exact List.mem_append_right _ (List.mem_append_right _ hw)
  all_goals simp [stmtBody] at hb

end Gabbro.Bruecke
