/- Connected lowering witnesses on the actual emitted images and table cells. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Probe
public section

namespace Gabbro.Stage0.Senke.ConsumeProbe
open Gabbro.Grammatik Runner.IR Runner.Mem

/-- A statement about every variant follows from the four closed cases. -/
private theorem each (P : Fin 4 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (k : Fin 4) : P k :=
  match k with
  | ⟨0, _⟩ => h0 | ⟨1, _⟩ => h1 | ⟨2, _⟩ => h2 | ⟨3, _⟩ => h3

set_option hygiene false in
local macro "by_kind" : tactic =>
  `(tactic| (revert kind; refine each _ ?_ ?_ ?_ ?_ <;> decide +kernel))
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem layout_in : LayIn layout := by
  refine ⟨?_, (fun g => nomatch g), by decide⟩
  intro t f k hk
  cases t
  cases f
  change (k : Int) < 2 at hk
  change 8192 ≤ 8192 + 8 * k ∧ 8192 + 8 * k + 8 ≤ 8208
  omega

theorem layout_dis : LayDis layout := by
  refine ⟨?_, ?_, ?_⟩
  · intro c c' hc hc' hne
    cases c with
    | glob g => nomatch g
    | elem t f k =>
      cases t
      cases f
      cases c' with
      | glob g => nomatch g
      | elem t' f' k' =>
        cases t'
        cases f'
        have hk : k ≠ k' := fun h => hne (by subst k'; rfl)
        change 8192 + 8 * k + 8 ≤ 8192 + 8 * k' ∨
          8192 + 8 * k' + 8 ≤ 8192 + 8 * k
        omega
  · intro c c' hc hc' he
    cases c with
    | glob g => nomatch g
    | elem t f k =>
      cases t
      cases f
      cases c' with
      | glob g => nomatch g
      | elem t' f' k' =>
        cases t'
        cases f'
        change 8192 + 8 * k = 8192 + 8 * k' at he
        have hk : k = k' := by omega
        subst k'
        rfl
  · intro c hc
    cases c with
    | glob g => nomatch g
    | elem t f k =>
      cases t
      cases f
      change (8192 + 8 * k) % 8 = 8192 % 8
      omega

theorem code_at (kind : Fin 4) : CodeAt (memory kind) 16384 (code kind) := by
  have all : (List.finRange (code kind).length).all (fun k => decide
      ((memory kind).rd8 (16384 + BitVec.ofNat 64 (16 * k.val)) = some (BitVec.ofNat 8 (code kind)[k.val].o) ∧
       (memory kind).rd32 (16384 + BitVec.ofNat 64 (16 * k.val) + 4) = some (II.f (code kind)[k.val].a) ∧
       (memory kind).rd32 (16384 + BitVec.ofNat 64 (16 * k.val) + 8) = some (II.f (code kind)[k.val].b) ∧
       (memory kind).rd32 (16384 + BitVec.ofNat 64 (16 * k.val) + 12) = some (II.f (code kind)[k.val].c))) = true := by
    by_kind
  intro k hk
  have h := of_decide_eq_true (List.all_eq_true.mp all ⟨k, hk⟩ (by simp))
  simpa only [BitVec.zero_add] using (show InsAt (memory kind)
    (16384 + BitVec.ofNat 64 (16 * k)) (code kind)[k].o (II.f (code kind)[k].a)
      (II.f (code kind)[k].b) (II.f (code kind)[k].c) from ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩)

theorem functions_at (kind : Fin 4) :
    PCode (memory kind) (fun _ => 2048) (fun _ => functionCode) 4096 64 := by
  intro f
  refine ⟨?_, by unfold CodeFar; decide⟩
  have all : (List.finRange functionCode.length).all (fun k => decide
      ((memory kind).rd8 (2048 + BitVec.ofNat 64 (16 * k.val)) = some (BitVec.ofNat 8 functionCode[k.val].o) ∧
       (memory kind).rd32 (2048 + BitVec.ofNat 64 (16 * k.val) + 4) = some (II.f functionCode[k.val].a) ∧
       (memory kind).rd32 (2048 + BitVec.ofNat 64 (16 * k.val) + 8) = some (II.f functionCode[k.val].b) ∧
       (memory kind).rd32 (2048 + BitVec.ofNat 64 (16 * k.val) + 12) = some (II.f functionCode[k.val].c))) = true := by
    by_kind
  intro k hk
  have h := of_decide_eq_true (List.all_eq_true.mp all ⟨k, hk⟩ (by simp))
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem frame (kind : Fin 4) : FrameOK (memory kind) 4096 64 :=
  ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩

theorem pre [Kern] (kind : Fin 4) :
    PreS layout (memory kind) 16384 4096 64 8 (code kind) (Env.nil : Env D []) (reserved := controlReserved) := by
  refine ⟨by decide, by decide, frame kind, code_at kind, ?_, ?_, trivial, wstab_true _ _⟩
  · unfold CodeFar
    by_kind
  · intro _ x; nomatch x

theorem world_at [Kern] (kind : Fin 4) : WeltAt (memory kind) layout initial := by
  refine ⟨?_, (fun g => nomatch g), fun _ _ _ => rfl⟩
  intro t f k hk
  cases t
  cases f
  change (k : Int) < 2 at hk
  have casesK : k = 0 ∨ k = 1 := by omega
  rcases casesK with rfl | rfl
  · exact ValueAt.ofCellWord (w := 1) (by decide) (by by_kind) rfl
  · exact ValueAt.ofCellWord (w := 1) (by decide) (by by_kind) rfl

theorem within [Kern] : WIn layout 4096 64 64 :=
  ⟨layout_in, layout_dis, by decide, by decide, by decide⟩

theorem sync (kind : Fin 4) : SyncOK (memory kind) layout 4096 64 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    (fun l => nomatch l), by decide, (fun l => nomatch l),
    (fun l => nomatch l), (fun l => nomatch l)⟩

theorem surroundings [Kern] (kind : Fin 4) :
    Umf layout (fun _ => 2048) (fun _ => functionCode) 0 (memory kind) 4096 64 64 :=
  ⟨functions_at kind, by by_kind, by decide, sync kind, by decide⟩

theorem head (kind : Fin 4) :
    Kopf layout () (memory kind) 4096 64 0 0 (Env.nil : Env D []) program initial :=
  ⟨by by_kind, by by_kind,
    (fun _ x => nomatch x), by decide, trivial⟩

local instance [Kern] : TorOK layout oracle where
  ans a := nomatch a
  puf a := nomatch a
  ref_answer a := nomatch a
  area a := nomatch a

local instance : SichtOK oracle := ⟨fun _ _ => rfl⟩

theorem functions_spec [Kern] :
    FunSpec layout (fun _ => 2048) (fun _ => functionCode) calls 0 8 := by
  refine ⟨rfl, ?_⟩
  intro f m fp K Ks rp cfp σ ρ hc hW hK hF hC _ _ _ _ _ _
  exact stop_ok (hC f).1 (hC f).2 hF (by have := hW.ks; omega) hK (by decide)

/-- All four witnesses use the actual statement compiler and source frame. -/
theorem lowering_zeuge (kind : Fin 4) :
    loweredVariant kind = some (code kind, top kind) ∧ 0 < (code kind).length ∧
      top kind + 8 ≤ 64 ∧ 16 * (code kind).length < 2 ^ 31 := by
  by_kind

/-- Jointly inhabit the general theorem, including its ABI, world, code and
    call-contract premises. The emitted image, not a detached candidate, runs. -/
theorem consumeTraverse_case_zeuge [Kern] (kind : Fin 4) :
    loweredVariant kind = some (code kind, top kind) ∧
    PreS layout (memory kind) 16384 4096 64 8 (code kind) (Env.nil : Env D []) controlReserved ∧
    WeltAt (memory kind) layout initial ∧
    Sim layout program () initial .nil 0 0 4096 4 64 [3] ⟨16384, 4096⟩ (memory kind)
      (16384 + BitVec.ofNat 64 (16 * (code kind).length))
      (16384 + BitVec.ofNat 64 (16 * (code kind).length))
      (16384 + BitVec.ofNat 64 (16 * (code kind).length))
      (execStmt oracle 1 calls (variant kind) initial .nil) controlReserved := by
  have emitted := (lowering_zeuge kind).1
  refine ⟨emitted, pre kind, world_at kind, ?_⟩
  have run := lowS_ok (O := oracle) (passes := 1) (P := program) (f := ())
    (σ0 := initial) (ρ0 := Env.nil) (lo := 4) (pr := [3]) (ex := (0, 0))
    (cens := post.1) (tens := post.2) (reserved := controlReserved)
    functions_spec (by intro f; decide) rfl (by decide +kernel)
    (variant kind) (code kind) (top kind) emitted (lowering_zeuge kind).2.2.1
    (lowering_zeuge kind).2.2.2 within (memory kind) 16384 initial .nil (pre kind)
    (by decide) (by decide) (surroundings kind) (head kind) (world_at kind)
    (by intro j hj; have eq : j = 3 := by simpa using hj; subst j; decide)
  simpa using run

/-- The selected sequence is zero, one, none for the real predecessor 0→1;
    this same statement has its complete image simulation jointly witnessed. -/
theorem edge_selection_zeuge [Kern] :
    (verbrauchSel () member edge initial .nil).2.1 = some zero ∧
    (verbrauchSel () member edge afterFirst .nil).2.1 = some one ∧
    (verbrauchSel () member edge afterSecond .nil).2 = (none, false) ∧
    lowered true = some (code 0, top 0) ∧
    Sim layout program () initial .nil 0 0 4096 4 64 [3] ⟨16384, 4096⟩ (memory 0)
      (16384 + BitVec.ofNat 64 (16 * (code 0).length))
      (16384 + BitVec.ofNat 64 (16 * (code 0).length))
      (16384 + BitVec.ofNat 64 (16 * (code 0).length))
      (execStmt oracle 1 calls (statement true) initial .nil) controlReserved :=
  ⟨rfl, rfl, rfl, (lowering_zeuge 0).1, (consumeTraverse_case_zeuge 0).2.2.2⟩

/-- The normal emitted image clears both table cells and keeps the sentinel. -/
theorem normal_run_zeuge [Kern] :
    ∃ m', Star ⟨16384, 4096⟩ (memory 0)
      ⟨16384 + BitVec.ofNat 64 (16 * (code 0).length), 4096⟩ m' ∧
      m'.rd64 8192 = some 0 ∧ m'.rd64 8200 = some 0 ∧
      m'.rd64 (slot 4096 3) = some 77 := by
  have run := (consumeTraverse_case_zeuge 0).2.2.2
  change Reach layout 4096 4 64 [3] ⟨16384, 4096⟩ (memory 0)
    (16384 + BitVec.ofNat 64 (16 * (code 0).length)) finished .nil controlReserved at run
  obtain ⟨m', path, frame, env, represented, kept⟩ := run
  obtain ⟨w0, read0, enc0⟩ := ValueAt.word (D.typ () ()) _
    (wordCompatB_sound _ (by decide)) (represented.1 () () 0 (by decide))
  obtain ⟨w1, read1, enc1⟩ := ValueAt.word (D.typ () ()) _
    (wordCompatB_sound _ (by decide)) (represented.1 () () 1 (by decide))
  have zero0 : w0 = 0 := enc0
  have zero1 : w1 = 0 := enc1
  rw [slot_zero] at read0 read1
  exact ⟨m', path, by simpa only [zero0] using read0,
    by simpa only [zero1] using read1, (kept 3 (by simp)).trans (by decide +kernel)⟩

/-- False membership exits the emitted scan without changing either cell. -/
theorem false_membership_zeuge [Kern] :
    ∃ m', Star ⟨16384, 4096⟩ (memory 1)
      ⟨16384 + BitVec.ofNat 64 (16 * (code 1).length), 4096⟩ m' ∧
      m'.rd64 8192 = some 1 ∧ m'.rd64 8200 = some 1 := by
  have run := (consumeTraverse_case_zeuge 1).2.2.2
  change Reach layout 4096 4 64 [3] ⟨16384, 4096⟩ (memory 1)
    (16384 + BitVec.ofNat 64 (16 * (code 1).length)) initial .nil controlReserved at run
  obtain ⟨m', path, frame, env, represented, kept⟩ := run
  obtain ⟨w0, read0, enc0⟩ := ValueAt.word (D.typ () ()) _
    (wordCompatB_sound _ (by decide)) (represented.1 () () 0 (by decide))
  obtain ⟨w1, read1, enc1⟩ := ValueAt.word (D.typ () ()) _
    (wordCompatB_sound _ (by decide)) (represented.1 () () 1 (by decide))
  have one0 : w0 = 1 := enc0
  have one1 : w1 = 1 := enc1
  rw [slot_zero] at read0 read1
  exact ⟨m', path, by simpa only [one0] using read0, by simpa only [one1] using read1⟩

/-- A nonfalling measure reaches the emitted logical stop code. -/
theorem unchanged_measure_zeuge [Kern] : Stops ⟨16384, 4096⟩ (memory 2) 104 :=
  (consumeTraverse_case_zeuge 2).2.2.2

theorem invariant_stop_zeuge [Kern] : Stops ⟨16384, 4096⟩ (memory 3) 104 :=
  (consumeTraverse_case_zeuge 3).2.2.2

/-- The reservation is derived from the real source function, including nesting. -/
theorem reservation_zeuge :
    (functionFrame program ()).counterDepth = 1 ∧ controlReserved = 4 ∧
    counterPair controlReserved (counterDepthB body) = (6, 7) ∧
    frei [] controlReserved = 8 := by decide +kernel

theorem nested_reservation_zeuge :
    let nested : Block D (vertragVon D ()) true [.index 2] [] [] :=
      .cons (.forever () .tru .nil) .nil
    counterDepthS (.consumeTraverse () member edge .tru 2 mass nested :
      Stmt D (vertragVon D ()) false [] [] []) = 2 := rfl

/-- Scoped returns retain the existing refusal with a correctly reserved frame. -/
theorem consumeTraverse_refused_zeuge :
    lowS 1 (fun _ => 2048) layout (functionFrame program ()) post [3] (0, 0)
      (.consumeTraverse () member edge .tru 2 mass
        (.cons (.retScoped .empty { scopes := [], genau := .refl [] }) .nil) :
        Stmt D (vertragVon D ()) false [] [] []) controlReserved = none := rfl

end Gabbro.Stage0.Senke.ConsumeProbe
