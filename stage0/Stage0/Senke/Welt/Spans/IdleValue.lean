module

public import Stage0.Senke.Welt.Spans.IdleLayout

@[expose] public section

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik

variable {D : Deklaration}

mutual
/-- The logical idle extension is a renumbering of the stored value.
    The exact bytes and reference validity survive it. -/
theorem idleValue (L : Lay D) : ∀ (τ : Ty) (v : Wert D τ),
    encodeWords L.withIdle (tyR τ) (valR τ v) = encodeWords L τ v ∧
      (ValueValid L.withIdle (tyR τ) (valR τ v) ↔ ValueValid L τ v)
  | .arr τ n, v => by
    have elements := fun i => idleValue L τ (v i)
    constructor
    · simp only [tyR, Ty.mapNumbers, valR, Val.relocate, encodeWords]
      split
      · rfl
      · exact congrArg _ (funext fun i => (elements i).1)
    · exact ⟨fun valid i => (elements i).2.mp (valid i), fun valid i => (elements i).2.mpr (valid i)⟩
  | .prod name fields, v => by
    have fieldsOk := idleProduct L fields v
    constructor
    · cases fields with
      | nil => rfl
      | cons τ rest =>
        simpa only [tyR, Ty.mapNumbers, Ty.mapFields, valR, Val.relocate, encodeWords,
          List.cons_ne_nil, ite_false]
          using fieldsOk.1
    · exact fieldsOk.2
  | .sum cs, v => by
    obtain ⟨tag, offset, payload, valid⟩ := idleCase L cs v
    constructor
    · simp only [tyR, Ty.mapNumbers, encodeWords, sumFits_mapNumbers, Ty.mapCases_length]
      split
      · simp only [sumN, tag, offset]
      · rw [tag, payload]
        simp only [sumPayloadWords_mapCases]
    · exact valid
  | .opt _, v => by
    constructor
    · cases v <;> simp only [tyR, Ty.mapNumbers, valR, Val.relocate, encodeWords]
    · rfl
  | .ptr ⟨_, _, .table _⟩, _
  | .int .., _ | .bool, _ | .why .., _ | .fl .., _
  | .fnptr .., _ | .ref .., _ | .str .., _ => by
    constructor
    · simp only [tyR, Ty.mapNumbers, valR, Val.relocate, encodeWords, Lay.withIdle, Option.elim]
      all_goals try rfl
    · rfl
  | .never, v => nomatch v
termination_by structural τ => τ

theorem idleProduct (L : Lay D) : ∀ (fields : List Ty) (v : ProdVal D.Fn D.passt fields),
    let mapped := Ty.mapFields (· + 1) id fields
    let value := ProdVal.relocate (· + 1) id (fun _ p => ⟨some p.1, p.2⟩) fields v
    encodeProductFields L.withIdle mapped value = encodeProductFields L fields v ∧
      (ProdValid L.withIdle mapped value ↔ ProdValid L fields v)
  | [], _ => ⟨rfl, Iff.rfl⟩
  | τ :: rest, v => by
    have head := idleValue L τ v.1
    have tail := idleProduct L rest v.2
    constructor
    · simp only [Ty.mapFields, ProdVal.relocate, encodeProductFields, ProdVal.hd, ProdVal.tl]
      have headWords := head.1
      simp only [tyR, valR] at headWords
      rw [headWords, tail.1]
    · exact and_congr head.2 tail.2
termination_by structural fields => fields

theorem idleCase (L : Lay D) : ∀ (cs : List (Option Ty)) (v : Wert D (.sum cs)),
    let mapped := Ty.mapCases (· + 1) id cs
    let value := valR (D := D) (.sum cs) v
    value.1.val = v.1.val ∧
      sumOff (D := D.mitRuhe) (mapped.get value.1)
          (Fall.toNutzlast _ _ _ _ value.2) =
        sumOff (D := D) (cs.get v.1) (Fall.toNutzlast _ _ _ _ v.2) ∧
      encodeSumPayload L.withIdle mapped value.1 value.2 = encodeSumPayload L cs v.1 v.2 ∧
      (SumValid L.withIdle mapped value.1 value.2 ↔ SumValid L cs v.1 v.2)
  | [], ⟨i, _⟩ => i.elim0
  | none :: _, ⟨⟨0, _⟩, _⟩ => ⟨rfl, rfl, rfl, Iff.rfl⟩
  | some τ :: _, ⟨⟨0, _⟩, payload⟩ => by
    have offset :
        sumOff (D := D.mitRuhe) (some (tyR τ)) (valR τ payload) =
          sumOff (D := D) (some τ) payload := by
      cases τ <;> rfl
    exact ⟨rfl, offset, (idleValue L τ payload).1, (idleValue L τ payload).2⟩
  | none :: cs, ⟨⟨i + 1, bound⟩, payload⟩
  | some _ :: cs, ⟨⟨i + 1, bound⟩, payload⟩ => by
    obtain ⟨tag, offset, words, valid⟩ :=
      idleCase L cs ⟨⟨i, Nat.lt_of_succ_lt_succ bound⟩, payload⟩
    exact ⟨congrArg Nat.succ tag, offset, words, valid⟩
termination_by structural cs => cs
end

/-- Scalar ABI arguments keep their exact word and validity after renumbering. -/
theorem Enc.withIdle_iff (L : Lay D) (word : Runner.W) :
    ∀ (τ : Ty) (v : Wert D τ), Enc L.withIdle (tyR τ) (valR τ v) word ↔ Enc L τ v word
  | .arr τ 0, _ => Iff.rfl
  | .arr τ 1, v => Enc.withIdle_iff L word τ (v ⟨0, by decide⟩)
  | .arr τ (_ + 2), _ => Iff.rfl
  | .sum cases, v => by
    have ⟨tag, offset, _, _⟩ := idleCase L cases v
    simp only [tyR, Ty.mapNumbers, Enc, sumFits_mapNumbers, sumN, tag, offset]
  | .ptr ⟨_, _, .table _⟩, _
  | .int .., _ | .bool, _ | .opt .., _ | .why .., _ | .fl .., _
  | .fnptr .., _ | .ref .., _ | .str .., _ | .prod .., _ => Iff.rfl
  | .never, v => nomatch v
termination_by structural τ => τ

/-- The stack encoding is unchanged for an environment in the idle extension. -/
theorem encodeEnv_withIdle (L : Lay D) {Γ : Ctx} (env : Env D Γ) :
    encodeEnv L.withIdle (envR env) = encodeEnv L env := by
  induction env with
  | nil => rfl
  | @cons τ _ value env ih =>
    simp only [envR, encodeEnv, ih, (idleValue L τ value).1]

theorem ValueAt.withIdle {L : Lay D} {m : Runner.Mem} {fp : Runner.W} {base : Nat}
    {τ : Ty} {v : Wert D τ} (stored : ValueAt L m fp base τ v) :
    ValueAt L.withIdle m fp base (tyR τ) (valR τ v) := by
  obtain ⟨words, valid⟩ := idleValue L τ v
  exact ⟨valid.mpr stored.1, words.symm ▸ stored.2⟩

theorem ValueAt.ofWithIdle {L : Lay D} {m : Runner.Mem} {fp : Runner.W} {base : Nat}
    {τ : Ty} {v : Wert D τ} (stored : ValueAt L.withIdle m fp base (tyR τ) (valR τ v)) :
    ValueAt L m fp base τ v := by
  obtain ⟨words, valid⟩ := idleValue L τ v
  exact ⟨valid.mp stored.1, words ▸ stored.2⟩

/-- Variables in the extended environment use the same canonical frame offsets. -/
theorem EnvAt.withIdle {L : Lay D} {m : Runner.Mem} {fp : Runner.W} {reserved : Nat}
    {Γ : Ctx} {env : Env D Γ} (stored : EnvAt L m fp env reserved) :
    EnvAt L.withIdle m fp (envR env) reserved := by
  induction env with
  | nil => intro _ var; exact nomatch var
  | @cons τ Γ head tail ih =>
    intro ty var
    cases var with
    | here =>
      have cell := (stored τ .here).withIdle
      rw [← vslot_varR (Var.here (τ := τ) (Γ := Γ)) reserved] at cell
      exact cell
    | there var =>
      exact ih (fun σ x => stored σ (.there x)) ty var

/-- Both machines give the same representation to every allocated world
    cell, including any worlds reached after entry. -/
theorem WeltAt.withIdle_iff {L : Lay D} {m : Runner.Mem} {world : World D}
    {requireWrites : Bool} :
    WeltAt m L.withIdle (worldR world) requireWrites ↔ WeltAt m L world requireWrites := by
  constructor
  · intro stored
    refine ⟨?_, ?_, stored.2.2⟩
    · intro t field i bound
      have cell := stored.1 t field i bound
      rw [Lay.withIdle_elem] at cell
      exact cell.ofWithIdle
    · intro g
      exact (stored.2.1 g).ofWithIdle
  · intro stored
    refine ⟨?_, ?_, stored.2.2⟩
    · intro t field i bound
      rw [Lay.withIdle_elem]
      exact (stored.1 t field i bound).withIdle
    · intro g
      exact (stored.2.1 g).withIdle

/-- Loading bytes for the ordinary source memory also loads the same
    memory of the goal machine, including all nested pointer values. -/
theorem WeltAt.withIdle {L : Lay D} {m : Runner.Mem} {s : Speicher D}
    (stored : WeltAt m L (s.welt [])) :
    WeltAt m L.withIdle ((speicherR s).welt []) := by
  exact WeltAt.withIdle_iff.mpr stored

end Gabbro.Stage0.Senke
