module

public import Core.Ast.Aggregate.Carrier.Effects.Group
import Init.Omega

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

private theorem foundName {functions : List Funktion} {name : Identifier}
    {f : Funktion} (found : Funktion.finde functions name = some f) : f.name = name :=
  Subtype.ext (beq_iff_eq.mp (List.find?_some (p := fun (f : Funktion) => f.name.val == name.val) found))

private theorem hull_sound (functions : List Funktion) (effect : CarrierEffect) (fuel : Nat) :
    ∀ visited pending, effect ∈ Funktion.effectHull functions fuel visited pending →
      ∃ name ∈ pending, ∃ source origin declared,
        Funktion.finde functions name = some source ∧
        EffectContractPath functions source origin ∧ origin.effects = some declared ∧ effect ∈ declared := by
  induction fuel with
  | zero =>
    intro visited pending found
    cases pending <;> exact (List.not_mem_nil found).elim
  | succ fuel ih =>
    intro visited pending found
    cases pending with
    | nil => exact (List.not_mem_nil found).elim
    | cons name rest =>
      by_cases visitedName : visited.contains name.val = true
      · simp only [Funktion.effectHull, visitedName, if_true] at found
        obtain ⟨n, present, path⟩ := ih _ _ found
        exact ⟨n, List.mem_cons_of_mem _ present, path⟩
      · simp only [Funktion.effectHull, visitedName, Bool.false_eq_true, if_false] at found
        cases lookup : Funktion.finde functions name with
        | none =>
          rw [lookup] at found
          obtain ⟨n, present, path⟩ := ih _ _ found
          exact ⟨n, List.mem_cons_of_mem _ present, path⟩
        | some source =>
          rw [lookup] at found
          cases declared : source.effects with
          | some effects =>
            rw [declared] at found
            rcases List.mem_append.mp found with direct | later
            · exact ⟨name, List.mem_cons_self, source, source, effects, lookup, .here, declared, direct⟩
            · obtain ⟨n, present, path⟩ := ih _ _ later
              exact ⟨n, List.mem_cons_of_mem _ present, path⟩
          | none =>
            rw [declared] at found
            obtain ⟨n, present, middle, origin, effects, lookupMiddle, path, contract, member⟩ := ih _ _ found
            rcases List.mem_append.mp present with fromCall | later
            · obtain ⟨site, edge, rfl⟩ := List.mem_map.mp fromCall
              exact ⟨name, List.mem_cons_self, source, origin, effects, lookup,
                .call declared site edge lookupMiddle path, contract, member⟩
            · exact ⟨n, List.mem_cons_of_mem _ later, middle, origin, effects,
                lookupMiddle, path, contract, member⟩

/-- If the traversal has not emitted an effect, every visited contract excludes it and
    every traversable outgoing edge leads to a visited or queued name. -/
private def ClosedFor (functions : List Funktion) (effect : CarrierEffect)
    (visited : List (List Char)) (pending : List Identifier) : Prop :=
  ∀ name f, Funktion.finde functions name = some f → name.val ∈ visited →
    (∀ declared, f.effects = some declared → effect ∉ declared) ∧
    (f.effects = none → ∀ site ∈ f.ruft, site.name.val ∈ visited ∨ site.name ∈ pending)

private theorem closed_transfer {functions effect visited pending seen queue}
    (closed : ClosedFor functions effect visited pending) (retain : visited ⊆ seen)
    (carry : ∀ name ∈ pending, name.val ∈ seen ∨ name ∈ queue)
    (new : ∀ name f, Funktion.finde functions name = some f → name.val ∈ seen → name.val ∉ visited →
      (∀ declared, f.effects = some declared → effect ∉ declared) ∧
      (f.effects = none → ∀ site ∈ f.ruft, site.name.val ∈ seen ∨ site.name ∈ queue)) :
    ClosedFor functions effect seen queue := by
  intro name f lookup included
  by_cases old : name.val ∈ visited
  · obtain ⟨excludes, edges⟩ := closed name f lookup old
    refine ⟨excludes, fun missing site edge => ?_⟩
    rcases edges missing site edge with past | future
    · exact Or.inl (retain past)
    · exact carry site.name future
  · exact new name f lookup included old

private def callCount (functions : List Funktion) : Nat :=
  (functions.map fun f => f.ruft.length).sum

private theorem callCount_append (left right : List Funktion) :
    callCount (left ++ right) = callCount left + callCount right := by
  simp only [callCount, List.map_append, List.sum_append]

private theorem callCount_fold (functions : List Funktion) (start : Nat) :
    functions.foldl (fun n f => n + f.ruft.length) start = start + callCount functions := by
  induction functions generalizing start with
  | nil => simp only [List.foldl_nil, callCount, List.map_nil, List.sum_nil, Nat.add_zero]
  | cons f fs ih =>
    rw [List.foldl_cons, ih]
    simp only [callCount, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- One unit of fuel pays for each queued name. Each registered function's call sites
    are also paid for once, when that function is first visited. -/
private theorem hull_closed (functions : List Funktion) (effect : CarrierEffect) (fuel : Nat) :
    ∀ (visited : List (List Char)) (pending : List Identifier) (unused : List Funktion),
      (∀ f ∈ functions, f.name.val ∉ visited → f ∈ unused) →
      pending.length + callCount unused ≤ fuel →
      ClosedFor functions effect visited pending →
      effect ∉ Funktion.effectHull functions fuel visited pending →
      ∃ seen, ClosedFor functions effect seen [] ∧
        ∀ name : Identifier, name.val ∈ visited ∨ name ∈ pending → name.val ∈ seen := by
  induction fuel with
  | zero =>
    intro visited pending unused fresh budget closed absent
    cases pending with
    | nil => exact ⟨visited, closed, fun _ h => h.resolve_right List.not_mem_nil⟩
    | cons name rest =>
      simp only [List.length_cons] at budget
      omega
  | succ fuel ih =>
    intro visited pending unused fresh budget closed absent
    cases pending with
    | nil => exact ⟨visited, closed, fun _ h => h.resolve_right List.not_mem_nil⟩
    | cons name rest =>
      simp only [List.length_cons] at budget
      by_cases old : name.val ∈ visited
      · have contained : visited.contains name.val = true := List.contains_iff_mem.mpr old
        simp only [Funktion.effectHull, contained, if_true] at absent
        have carry (n : Identifier) (h : n ∈ name :: rest) : n.val ∈ visited ∨ n ∈ rest := by
          rcases List.mem_cons.mp h with rfl | later
          · exact Or.inl old
          · exact Or.inr later
        have smaller : rest.length + callCount unused ≤ fuel := by omega
        obtain ⟨seen, done, included⟩ := ih visited rest unused fresh smaller
          (closed_transfer closed (fun _ h => h) carry (fun _ _ _ h no => (no h).elim)) absent
        exact ⟨seen, done, fun n h => included n (h.elim Or.inl (carry n))⟩
      · have contained : visited.contains name.val ≠ true := fun h => old (List.contains_iff_mem.mp h)
        simp only [Funktion.effectHull, contained, Bool.false_eq_true, if_false] at absent
        let seen := name.val :: visited
        have carry {queue : List Identifier} (keep : rest ⊆ queue) (n : Identifier)
            (h : n ∈ name :: rest) : n.val ∈ seen ∨ n ∈ queue := by
          rcases List.mem_cons.mp h with rfl | later
          · exact Or.inl List.mem_cons_self
          · exact Or.inr (keep later)
        have extend {queue : List Identifier} (keep : rest ⊆ queue)
            (processed : ∀ f, Funktion.finde functions name = some f →
              (∀ declared, f.effects = some declared → effect ∉ declared) ∧
              (f.effects = none → ∀ site ∈ f.ruft, site.name.val ∈ seen ∨ site.name ∈ queue)) :
            ClosedFor functions effect seen queue := by
          refine closed_transfer closed (fun {_} h => List.mem_cons_of_mem _ h) (carry keep) ?_
          intro n f found hn notOld
          have same : n = name := Subtype.ext ((List.mem_cons.mp hn).resolve_right notOld)
          subst n
          exact processed f found
        have restore {queue : List Identifier} (keep : rest ⊆ queue)
            (result : ∃ final, ClosedFor functions effect final [] ∧
              ∀ n : Identifier, n.val ∈ seen ∨ n ∈ queue → n.val ∈ final) :
            ∃ final, ClosedFor functions effect final [] ∧
              ∀ n : Identifier, n.val ∈ visited ∨ n ∈ name :: rest → n.val ∈ final := by
          obtain ⟨final, done, included⟩ := result
          exact ⟨final, done, fun n h => included n (h.elim
            (fun past => Or.inl (List.mem_cons_of_mem _ past)) (carry keep n))⟩
        cases lookup : Funktion.finde functions name with
        | none =>
          rw [lookup] at absent
          have smaller : rest.length + callCount unused ≤ fuel := by omega
          apply restore (fun {_} h => h)
          exact ih seen rest unused (fun f h notSeen => fresh f h (fun hv => notSeen (List.mem_cons_of_mem _ hv)))
            smaller (extend (fun {_} h => h) fun f found => by rw [lookup] at found; cases found) absent
        | some f =>
          rw [lookup] at absent
          have inUnused := fresh f (List.mem_of_find?_eq_some lookup) (by rwa [foundName lookup])
          obtain ⟨before, after, splitUnused⟩ := List.append_of_mem inUnused
          let remaining := before ++ after
          have weight : callCount unused = callCount remaining + f.ruft.length := by
            rw [splitUnused, callCount_append, show callCount (f :: after) =
              f.ruft.length + callCount after from rfl, callCount_append]
            omega
          have stillUnused (g : Funktion) (inTable : g ∈ functions) (notSeen : g.name.val ∉ seen) :
              g ∈ remaining := by
            have inOld := fresh g inTable (fun h => notSeen (List.mem_cons_of_mem _ h))
            rw [splitUnused, List.mem_append, List.mem_cons] at inOld
            exact List.mem_append.mpr (inOld.elim Or.inl fun h =>
              Or.inr (h.resolve_left fun same => notSeen (List.mem_cons.mpr (Or.inl
                (by rw [same, foundName lookup])))))
          cases contract : f.effects with
          | some declared =>
            rw [contract] at absent
            have smaller : rest.length + callCount remaining ≤ fuel := by omega
            apply restore (fun {_} h => h)
            apply ih seen rest remaining stillUnused smaller
            · apply extend (fun {_} h => h)
              intro g found
              have eq := Option.some.inj (lookup.symm.trans found)
              subst g
              refine ⟨fun d dEq member => absent (List.mem_append_left _ ?_), ?_⟩
              · exact Option.some.inj (contract.symm.trans dEq) ▸ member
              · intro missing
                rw [contract] at missing
                cases missing
            · exact fun h => absent (List.mem_append_right _ h)
          | none =>
            rw [contract] at absent
            let queue := f.ruft.map Rufstelle.name ++ rest
            have smaller : queue.length + callCount remaining ≤ fuel := by
              simp only [queue, List.length_append, List.length_map]
              omega
            apply restore (fun {_} h => List.mem_append_right _ h)
            apply ih seen queue remaining stillUnused smaller _ absent
            apply extend (fun {_} h => List.mem_append_right _ h)
            intro g found
            have eq := Option.some.inj (lookup.symm.trans found)
            subst g
            refine ⟨?_, fun _ site member => Or.inr (List.mem_append_left _ (List.mem_map.mpr ⟨site, member, rfl⟩))⟩
            intro d dEq
            rw [contract] at dEq
            cases dEq

private theorem closed_excludes (path : EffectContractPath functions source origin)
    {effect : CarrierEffect} {seen : List (List Char)} (closed : ClosedFor functions effect seen [])
    (lookup : Funktion.finde functions source.name = some source)
    (included : source.name.val ∈ seen) (contract : origin.effects = some declared) : effect ∉ declared := by
  induction path with
  | here => exact (closed _ _ lookup included).1 _ contract
  | call missing site edge found _ ih =>
    have seenNext := ((closed _ _ lookup included).2 missing site edge).resolve_right List.not_mem_nil
    rw [← foundName found] at seenNext
    exact ih (foundName found ▸ found) seenNext contract

theorem effectGroup_inferred : EffectGroupInferredAussage := by
  intro functions target _ lookup effect
  cases declared : target.effects with
  | some effects =>
    change effect ∈ (match target.effects with | some effects => effects | none => _) ↔ _
    rw [declared]
    constructor
    · intro present
      exact ⟨target, effects, .here, declared, present⟩
    · rintro ⟨origin, contract, path, eq, present⟩
      cases path with
      | here => exact Option.some.inj (eq.symm.trans declared) ▸ present
      | call missing _ _ _ _ => rw [declared] at missing; cases missing
  | none =>
    have fuelEq := callCount_fold functions 1
    simp only [Funktion.requiredEffects, declared, fuelEq]
    constructor
    · intro member
      obtain ⟨name, nameIn, source, origin, contract, found, path, eq, present⟩ := hull_sound _ _ _ _ _ member
      cases List.mem_singleton.mp nameIn
      cases Option.some.inj (lookup.symm.trans found)
      exact ⟨origin, contract, path, eq, present⟩
    · rintro ⟨origin, contract, path, eq, present⟩
      by_contra absent
      have fresh (f : Funktion) (member : f ∈ functions) (_ : f.name.val ∉ []) : f ∈ functions := member
      have empty : ClosedFor functions effect [] [target.name] := by
        intro name f found included
        exact (List.not_mem_nil included).elim
      obtain ⟨seen, closed, included⟩ := hull_closed functions effect (1 + callCount functions) [] [target.name]
        functions fresh (Nat.le_refl _) empty absent
      exact (closed_excludes path closed lookup (included _ (Or.inr List.mem_cons_self)) eq) present

end Gabbro.Core.Ast.Semantik
