module

public import Core.Ast.Aggregate.Runtime
public import Core.Beobachtung.Fluss.Beschriftung.Aggregat
public import Core.Beobachtung.Fluss.Beschriftung.AufgabenBeweise

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung Katalog

/-- The number of locals `tupleLocals` actually pushes is exactly `behalteneTupel`, for
    every shape of `bind`, including a too-short one. -/
theorem tupleLocals_laenge : (types : List (Ty .value)) →
    (value : Wert (tupleType types)) → (bind : List Bool) →
    (tupleLocals types value bind).length = behalteneTupel types bind
  | [], _, _ => rfl
  | _ :: _, _, [] => rfl
  | head :: tail, (vhead, vtail), false :: more =>
      tupleLocals_laenge tail vtail more
  | head :: tail, (vhead, vtail), true :: more =>
      congrArg Nat.succ (tupleLocals_laenge tail vtail more)

/-- `liesTupel` depends only on the `types.length` consecutive temporaries it reads. -/
theorem liesTupel_cong : (types : List (Ty .value)) →
    ∀ (slot : Nat) (temp₁ temp₂ : Nat → Option Dynamisch),
      (∀ k, k < types.length → temp₁ (slot + k) = temp₂ (slot + k)) →
      liesTupel temp₁ slot types = liesTupel temp₂ slot types
  | [], _, _, _, _ => rfl
  | head :: tail, slot, temp₁, temp₂, h => by
      have h0 : temp₁ slot = temp₂ slot := by
        simpa only [Nat.add_zero] using h 0 (Nat.zero_lt_succ _)
      have htail : ∀ k, k < tail.length → temp₁ (slot + 1 + k) = temp₂ (slot + 1 + k) := by
        intro k hk
        have hk' : k + 1 < (head :: tail).length := by
          simp only [List.length_cons]
          omega
        have got := h (k + 1) hk'
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using got
      simp only [liesTupel, h0, liesTupel_cong tail (slot + 1) temp₁ temp₂ htail]

/-- `liesRecord` depends only on the temporaries named in `sources`. -/
theorem liesRecord_cong : (types : List (Ty .value)) →
    ∀ (sources : List Nat) (temp₁ temp₂ : Nat → Option Dynamisch),
      (∀ slot ∈ sources, temp₁ slot = temp₂ slot) →
      liesRecord temp₁ types sources = liesRecord temp₂ types sources
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, _ => rfl
  | _ :: _, [], _, _, _ => rfl
  | head :: tail, slot :: sources, temp₁, temp₂, h => by
      have h0 : temp₁ slot = temp₂ slot := h slot (List.mem_cons_self ..)
      have hrest : liesRecord temp₁ tail sources = liesRecord temp₂ tail sources :=
        liesRecord_cong tail sources temp₁ temp₂
          (fun s hs => h s (List.mem_cons_of_mem _ hs))
      simp only [liesRecord, h0, hrest]

/-- Masking an appended block: the tail is compared at `l₀`, the whole stack at `l₁`, and
    the old tail entries are public at `l₁` only from position `n` on. -/
theorem maskiere_anhaengen {l₀ l₁ : Nat → Etikett} :
    ∀ (n : Nat) (vs : List (Option Dynamisch)) (xs ys : List (Option Dynamisch)),
      (∀ j, oeffentlich (l₁ (n + j)) = true → oeffentlich (l₀ j) = true) →
      maskiereLokal l₀ 0 xs = maskiereLokal l₀ 0 ys →
      vs.length = n →
      maskiereLokal l₁ 0 (vs ++ xs) = maskiereLokal l₁ 0 (vs ++ ys)
  | 0, vs, xs, ys, hL, e, hlen => by
      have hvn : vs = [] := by
        cases vs with
        | nil => rfl
        | cons v vs' =>
            simp only [List.length_cons] at hlen
            omega
      subst vs
      simpa only [List.nil_append, Nat.zero_add] using
        (maskiereLokal_gleich_mono (fun i hi => hL i (by simpa only [Nat.zero_add] using hi))
          0 xs ys e)
  | n + 1, vs, xs, ys, hL, e, hlen => by
      cases vs with
      | nil =>
          simp only [List.length_nil] at hlen
          omega
      | cons v vs' =>
          simp only [List.length_cons] at hlen
          have ih := maskiere_anhaengen (l₀ := l₀) (l₁ := fun i => l₁ (i + 1))
            n vs' xs ys
            (fun j hj => by
              have hz : (n + j) + 1 = n + 1 + j := by omega
              exact hL j (by simpa only [hz] using hj))
            e (by omega)
          have tailEq : maskiereLokal l₁ 1 (vs' ++ xs) = maskiereLokal l₁ 1 (vs' ++ ys) := by
            simpa only [Nat.zero_add, maskiere_verschoben] using ih
          rw [List.cons_append, List.cons_append]
          simp only [maskiereLokal, Nat.zero_add, tailEq]

/-- The view after `baueArray`: it writes one temporary, so the shared write rule applies. -/
theorem baueArraySicht : BaueArraySichtAussage := by
  intro β pc ziel element count regel
  refine Befehl.sichtErhaltend_schreibform ?_ regel
  refine ⟨(fun r => do
    let values ← Vector.ofFnM (n := count) fun i =>
      (r.temp (ziel + i.val)).bind (wertAls element)
    pure ⟨.array element count, values⟩), ?_, ?_⟩
  · intro r live
    rfl
  · intro r₁ r₂ hRead
    have hFn : (fun i : Fin count => (r₁.temp (ziel + i.val)).bind (wertAls element)) =
        (fun i : Fin count => (r₂.temp (ziel + i.val)).bind (wertAls element)) := by
      funext i
      have hmem : Komp.temp (ziel + i.val) ∈ tempBereich ziel count := by
        simp only [tempBereich]
        exact List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩
      have hk := hRead (.temp (ziel + i.val)) hmem
      change r₁.temp (ziel + i.val) = r₂.temp (ziel + i.val) at hk
      rw [hk]
    change (do
      let values ← Vector.ofFnM (n := count) fun i =>
        (r₁.temp (ziel + i.val)).bind (wertAls element)
      pure (⟨.array element count, values⟩ : Dynamisch)) =
      (do
      let values ← Vector.ofFnM (n := count) fun i =>
        (r₂.temp (ziel + i.val)).bind (wertAls element)
      pure (⟨.array element count, values⟩ : Dynamisch))
    rw [hFn]

/-- The view after `baueTupel`: same shape, the payload comes from `liesTupel`. -/
theorem baueTupelSicht : BaueTupelSichtAussage := by
  intro β pc ziel types regel
  refine Befehl.sichtErhaltend_schreibform ?_ regel
  refine ⟨(fun r => (liesTupel r.temp ziel types).map fun values =>
    ⟨tupleType types, values⟩), ?_, ?_⟩
  · intro r live
    rfl
  · intro r₁ r₂ hRead
    have hpoint : ∀ k, k < types.length → r₁.temp (ziel + k) = r₂.temp (ziel + k) := by
      intro k hk
      have hmem : Komp.temp (ziel + k) ∈ tempBereich ziel types.length := by
        simp only [tempBereich]
        exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
      have got := hRead (.temp (ziel + k)) hmem
      change r₁.temp (ziel + k) = r₂.temp (ziel + k) at got
      exact got
    change (liesTupel r₁.temp ziel types).map
        (fun values => (⟨tupleType types, values⟩ : Dynamisch)) =
      (liesTupel r₂.temp ziel types).map
        (fun values => (⟨tupleType types, values⟩ : Dynamisch))
    rw [liesTupel_cong types ziel r₁.temp r₂.temp hpoint]

/-- The view after `baueRecord`: the payload comes from `liesRecord` over the sources. -/
theorem baueRecordSicht : BaueRecordSichtAussage := by
  intro β pc ziel name labels types sources regel
  refine Befehl.sichtErhaltend_schreibform ?_ regel
  refine ⟨(fun r => (liesRecord r.temp types sources).map fun record =>
    ⟨recordValueType name labels types, record⟩), ?_, ?_⟩
  · intro r live
    rfl
  · intro r₁ r₂ hRead
    have hpoint : ∀ slot ∈ sources, r₁.temp slot = r₂.temp slot := by
      intro slot hs
      have hmem : Komp.temp slot ∈ sources.map Komp.temp :=
        List.mem_map.mpr ⟨slot, hs, rfl⟩
      have got := hRead (.temp slot) hmem
      change r₁.temp slot = r₂.temp slot at got
      exact got
    change (liesRecord r₁.temp types sources).map
        (fun record => (⟨recordValueType name labels types, record⟩ : Dynamisch)) =
      (liesRecord r₂.temp types sources).map
        (fun record => (⟨recordValueType name labels types, record⟩ : Dynamisch))
    rw [liesRecord_cong types sources r₁.temp r₂.temp hpoint]

/-- The view after `bindeTupel`: the pushed block is computed from `source`, which is
    public, so both frames push the very same locals in front of their old ones. -/
theorem sicht_bindeTupel (β : Beschriftung) (r : Rahmen) (live : Nat → Bool)
    (source : Nat) (types : List (Ty .value)) (bind : List Bool) :
    ((Befehl.bindeTupel source types bind).auswerten r live).sicht β =
      { r.sicht β with
        pc := r.pc + 1
        temp := fun s => if oeffentlich (β.temp (r.pc + 1) s) = true then r.temp s else none
        lokale := maskiereLokal (β.lokal (r.pc + 1)) 0
          (((((r.temp source).bind (wertAls (tupleType types))).map fun product =>
              tupleLocals types product bind).getD []).reverse ++ r.lokale) } :=
  rfl

theorem bindeTupelSicht : BindeTupelSichtAussage := by
  intro β pc quelle types bind hT hQ hL hL2 r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have hTe : (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₁.temp s else none) =
      (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₂.temp s else none) := by
    funext s
    by_cases hp : oeffentlich (β.temp (r₁.pc + 1) s) = true
    · simp only [hp, if_true]
      exact tempPub s (hT s hp)
    · simp only [if_neg hp]
  let vs₁ := (((r₁.temp quelle).bind (wertAls (tupleType types))).map fun product =>
    tupleLocals types product bind).getD []
  let vs₂ := (((r₂.temp quelle).bind (wertAls (tupleType types))).map fun product =>
    tupleLocals types product bind).getD []
  have vsEq : vs₁ = vs₂ := by
    dsimp only [vs₁, vs₂]
    rw [tempPub quelle hQ]
  have hLe : maskiereLokal (β.lokal (r₁.pc + 1)) 0 (vs₁.reverse ++ r₁.lokale) =
      maskiereLokal (β.lokal (r₁.pc + 1)) 0 (vs₂.reverse ++ r₂.lokale) := by
    rw [← vsEq]
    have hlen : vs₁.length = 0 ∨ vs₁.length = behalteneTupel types bind := by
      dsimp only [vs₁]
      cases hopt : (r₁.temp quelle).bind (wertAls (tupleType types)) with
      | none =>
          left
          rfl
      | some product =>
          right
          exact tupleLocals_laenge types product bind
    cases hlen with
    | inl h0 =>
        have hnil : vs₁ = [] := by
          cases hcase : vs₁ with
          | nil => rfl
          | cons v vs' =>
              rw [hcase] at h0
              cases h0
        rw [hnil]
        change maskiereLokal (β.lokal (r₁.pc + 1)) 0 r₁.lokale =
          maskiereLokal (β.lokal (r₁.pc + 1)) 0 r₂.lokale
        exact maskiereLokal_gleich_mono (fun i hi => hL i hi) 0 r₁.lokale r₂.lokale lokEq
    | inr hn =>
        apply maskiere_anhaengen (l₀ := β.lokal r₁.pc) (l₁ := β.lokal (r₁.pc + 1))
          vs₁.length vs₁.reverse r₁.lokale r₂.lokale
        · intro j hj
          have hz : vs₁.length + j = j + behalteneTupel types bind := by
            rw [hn]
            omega
          rw [hz] at hj
          exact hL2 j hj
        · exact lokEq
        · simp only [List.length_reverse]
  rw [sicht_bindeTupel, sicht_bindeTupel, h, pcEq, hTe, hLe]

/-- The view after `setzeRecordFeld`: one local is overwritten from a public source. -/
theorem sicht_setzeRecordFeld (β : Beschriftung) (r : Rahmen) (live : Nat → Bool)
    (source indexLocal : Nat) (name : List Char) (labels : List Identifier)
    (types : List (Ty .value)) (index : Fin types.length) :
    ((Befehl.setzeRecordFeld source indexLocal name labels types index).auswerten r live).sicht β =
      { r.sicht β with
        pc := r.pc + 1
        temp := fun s => if oeffentlich (β.temp (r.pc + 1) s) = true then r.temp s else none
        lokale := maskiereLokal (β.lokal (r.pc + 1)) 0
          (r.lokale.set indexLocal (do
            let old ← r.lokale[indexLocal]?.join.bind
              (wertAls (recordValueType name labels types))
            let value ← (r.temp source).bind (wertAls (types.get index))
            pure ⟨recordValueType name labels types, tupleSet types index value old⟩)) } :=
  rfl

theorem setzeRecordFeldSicht : SetzeRecordFeldSichtAussage := by
  intro β pc source indexLocal name labels types index hT hL hIndex hLok r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have hTe : (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₁.temp s else none) =
      (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₂.temp s else none) := by
    funext s
    by_cases hp : oeffentlich (β.temp (r₁.pc + 1) s) = true
    · simp only [hp, if_true]
      exact tempPub s (hT s hp)
    · simp only [if_neg hp]
  let upd₁ : Option Dynamisch := do
    let old ← r₁.lokale[indexLocal]?.join.bind (wertAls (recordValueType name labels types))
    let value ← (r₁.temp source).bind (wertAls (types.get index))
    pure ⟨recordValueType name labels types, tupleSet types index value old⟩
  let upd₂ : Option Dynamisch := do
    let old ← r₂.lokale[indexLocal]?.join.bind (wertAls (recordValueType name labels types))
    let value ← (r₂.temp source).bind (wertAls (types.get index))
    pure ⟨recordValueType name labels types, tupleSet types index value old⟩
  have hV : oeffentlich (β.lokal (r₁.pc + 1) indexLocal) = true → upd₁ = upd₂ := by
    intro hi
    have hJoin : r₁.lokale[indexLocal]?.join = r₂.lokale[indexLocal]?.join :=
      maskiereLokal_eintrag 0 r₁.lokale r₂.lokale indexLocal lokEq (by
        simpa only [Nat.zero_add] using hLok hi)
    have hTemp : r₁.temp source = r₂.temp source := tempPub source (hIndex hi)
    change (do
      let old ← r₁.lokale[indexLocal]?.join.bind (wertAls (recordValueType name labels types))
      let value ← (r₁.temp source).bind (wertAls (types.get index))
      pure (⟨recordValueType name labels types, tupleSet types index value old⟩ : Dynamisch)) =
      (do
      let old ← r₂.lokale[indexLocal]?.join.bind (wertAls (recordValueType name labels types))
      let value ← (r₂.temp source).bind (wertAls (types.get index))
      pure (⟨recordValueType name labels types, tupleSet types index value old⟩ : Dynamisch))
    rw [hJoin, hTemp]
  have hLe := maskiere_set (l₀ := β.lokal r₁.pc) (l₁ := β.lokal (r₁.pc + 1))
    (index := indexLocal) (xs := r₁.lokale) (ys := r₂.lokale)
    (v₁ := upd₁) (v₂ := upd₂)
    (fun j hj hjpub => hL j hj hjpub) hV lokEq
  rw [sicht_setzeRecordFeld, sicht_setzeRecordFeld, h, pcEq, hTe, hLe]

end Gabbro.Core.Ast.Semantik
