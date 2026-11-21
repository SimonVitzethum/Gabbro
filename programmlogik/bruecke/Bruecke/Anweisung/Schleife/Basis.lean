module
public import Bruecke.Anweisung.Lokal.BoolScope
public import Bruecke.Anweisung.Lokal.Speichern
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- Control is interpreted by the innermost canonical loop. -/
def controlU (leave : Bool) (x : String) : UStmt :=
  if leave then .leave x else .next x

def controlStmtB (leave : Bool) : Gabbro.Body.Stmt :=
  if leave then .leave else .exit

def loopIndices (u : UProg) (t : Fin u.tabs.length) : List Int :=
  (alleIndizes ((declOf u).count t)).map (·.n)

/-- The number of passes of a traversal of `t`: the reading stores it, never the index list. -/
def loopZahl (u : UProg) (t : Fin u.tabs.length) : Nat := ((declOf u).count t).toNat

theorem filterMap_eq_map_of_mem {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ (l : List α), (∀ x ∈ l, f x = some (g x)) → l.filterMap f = l.map g
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.filterMap_cons, h x List.mem_cons_self, List.map_cons,
      filterMap_eq_map_of_mem f g xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- The traversal's index list is the counted one. -/
theorem loopIndices_zahl (u : UProg) (t : Fin u.tabs.length) :
    loopIndices u t = Gabbro.Body.zaehlIndizes (loopZahl u t) := by
  unfold loopIndices loopZahl Gabbro.Body.zaehlIndizes alleIndizes
  rw [List.map_filterMap]
  refine filterMap_eq_map_of_mem _ _ _ (fun k hk => ?_)
  have hk' := List.mem_range.mp hk
  have hle : ((k : Nat) : Int) ≤ (declOf u).count t - 1 := by omega
  simp [hle]

theorem Sicht.index {u : UProg} {ft fn : UFn} (h : Sicht u ft fn)
    (x : String) (num : Nat) (count : Int) :
    Sicht u (ft.mitIndex x num count) (fn.mitIndex x num count) := by
  change Sicht u (ft.mitBindung x (0, count - 1)) (fn.mitBindung x (0, count - 1))
  exact h.bind x (0, count - 1) (0, count - 1)

theorem UmfangB.index {Γ : Ctx} {fn : UFn} {ns : BodyNames} (h : UmfangB Γ fn ns)
    {x : String} (hx : NameFrisch (protectedNames fn.params fn.kinds) x) (num : Nat) (count : Int) :
    UmfangB (.index count :: Γ) (fn.mitIndex x num count) (ns.push x) := by
  have hb := h.bind hx (0, count - 1)
  refine ⟨hb.ctx, ?_, hb.namen, hb.length, hb.vorrat, hb.pointer⟩
  refine ⟨?_, ?_, hb.art.2.2⟩
  · intro j t wr hj
    cases j with
    | zero => cases hj
    | succ j =>
      have hj' : fn.kinds[j]? = some (.ptr (.table t (true, wr))) := hj
      obtain ⟨wr', hwr⟩ := h.art.1 j t wr hj'
      exact ⟨wr', hwr⟩
  · intro kind hk
    rcases List.mem_cons.mp hk with rfl | hk
    · rfl
    · exact h.art.2.1 _ hk

theorem PositionalLRel.pushIndex {D : Deklaration} {Γ : Ctx} {fn : UFn} {ns : BodyNames}
    {ρ : Env D Γ} {β : Gabbro.Body.Binding} (h : PositionalLRel fn ns.active 0 ρ β)
    (x : String) (hn : ns.Valid) (num : Nat) (count : Int) (v : Wert D (.index count)) :
    PositionalLRel (fn.mitIndex x num count) (ns.push x).active 0 (.cons v ρ)
      (Gabbro.Body.bindLocal β (ns.fresh x) (.int v.n)) := by
  have hh := h.push x (ns.fresh x) (0, count - 1) (BodyNames.fresh_not_active hn x) v
  exact ⟨hh.length, hh.distinct, hh.values⟩

theorem PositionalLRel.tailIndex {D : Deklaration} {Γ : Ctx} {fn : UFn} {ids : List String}
    {id x : String} {num : Nat} {count : Int} {ρ : Env D (.index count :: Γ)}
    {β : Gabbro.Body.Binding}
    (h : PositionalLRel (fn.mitIndex x num count) (id :: ids) 0 ρ β) :
    PositionalLRel fn ids 0 ρ.tail β := by
  have hh : PositionalLRel (fn.mitBindung x (0, count - 1)) (id :: ids) 0 ρ β :=
    ⟨h.length, h.distinct, h.values⟩
  exact hh.tail

end Gabbro.Bruecke
