/- Subject: Joint witnesses on a real two-cell provider region, beyond the source count zero. -/
import Stage0.Senke.BildLese
import Grammatik.Bausteine.Arena.Unbounded.GRegion

namespace Gabbro.Stage0.Senke.ReferenceProbe
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
variable [Kern]

abbrev D := GRegion.rD
abbrev Γ : Ctx := [.ref 0, .ref 0]

def layout : Lay D where
  regionCells _ := 2
  col _ _ := 8192
  ga g := nomatch g
  lo := 8192
  hi := 8208
  tor _ := some ⟨39, regsIn 0, []⟩
  byte _ := none

def world : World D where
  slots _ k _ := ⟨if k = 0 then 11 else 22, by split <;> decide, by split <;> decide⟩
  globs g := nomatch g
  spur := []

def env : Env D Γ := .cons (Val.vonZelle 0) (.cons (Val.vonZelle 1) .nil)
def first : Expr D Γ [] (.ref 0) := .var .here
def second : Expr D Γ [] (.ref 0) := .var (.there .here)
def read (r : Expr D Γ [] (.ref 0)) : Expr D Γ [] (.int 0 255) :=
  .slotRef r () rfl rfl () (fun _ h => nomatch h)
def checks : Expr D Γ [] .bool :=
  .and (.refEq first first) (.and (.not (.refEq first second))
    (.and (.eq (read first) (.lit 11)) (.eq (read second) (.lit 22))))

def assignment : Stmt D (vertragVon D ()) false Γ [] [] :=
  .assignSlotRef second () rfl rfl () (.widen (by decide) (by decide) (.lit 73)) rfl
    (fun _ h => nomatch h)

def readCode : List II := ((lowE layout checks 6).getD ([], 0)).1
def readTop : Nat := ((lowE layout checks 6).getD ([], 0)).2
def writeCode : List II := ((lowS (fun _ => 0) layout 4 ([], 0) [] (0, 0) assignment).getD ([], 0)).1
def writeTop : Nat := ((lowS (fun _ => 0) layout 4 ([], 0) [] (0, 0) assignment).getD ([], 0)).2

/-- A real code segment, a frame containing provider references 1 and 0, and two region cells. -/
def memory (code : List II) : Runner.Mem where
  b a := if a.toNat < (code.flatMap encII).length then ((code.flatMap encII)[a.toNat]?).getD 0
    else if a.toNat = 4128 then 1 else if a.toNat = 8192 then 11 else if a.toNat = 8200 then 22 else 0
  rd _ := true
  wr _ := true

theorem layout_in : LayIn layout := by
  refine ⟨fun t f k hk => ?_, (fun g => nomatch g), by decide⟩
  change (k : Int) < 0 + 2 at hk
  change 8192 ≤ 8192 + 8 * k ∧ 8192 + 8 * k + 8 ≤ 8208
  omega

theorem layout_dis : LayDis layout := by
  constructor
  · intro c c' hc hc' he
    cases c with
    | glob g => nomatch g
    | elem t f k =>
      cases c' with
      | glob g => nomatch g
      | elem t' f' k' =>
        cases t; cases t'; cases f; cases f'
        change 8192 + 8 * k = 8192 + 8 * k' at he
        have : k = k' := by omega
        subst k'
        rfl
  · intro c hc
    cases c with
    | glob g => nomatch g
    | elem t f k => change (8192 + 8 * k) % 8 = 8192 % 8; omega

theorem region_zeuge : D.count () = 0 ∧ layout.count () = 2 ∧ LayIn layout ∧ LayDis layout :=
  ⟨rfl, rfl, layout_in, layout_dis⟩

theorem lowering_zeuge : lowE layout checks 6 = some (readCode, readTop) ∧
    lowS (fun _ => 0) layout 4 ([], 0) [] (0, 0) assignment = some (writeCode, writeTop) ∧
    readCode ≠ [] ∧ writeCode ≠ [] ∧ readTop ≤ 64 ∧ writeTop ≤ 64 := by decide +kernel

theorem semantics_zeuge : eval world checks world env = true ∧
    ∀ O passes R, ∃ σ', execStmt O passes R assignment world env = .ok σ' env ∧
      (σ'.slots () 1 ()).n = 73 ∧ (σ'.slots () 0 ()).n = 11 := by
  refine ⟨by rfl, fun O passes R => ?_⟩
  exact ⟨_, rfl, rfl, rfl⟩

theorem bytes (code : List II) (hsize : (code.flatMap encII).length < 2 ^ 64) :
    BytesAt (memory code) 0 (code.flatMap encII) := by
  intro i hi
  refine ⟨rfl, rfl, ?_⟩
  simp only [memory, Nat.zero_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), hi, ↓reduceIte,
    List.getElem?_eq_getElem hi, Option.getD_some]

theorem encoded_zeuge : Enc layout (.ref 0) (Val.vonZelle 0) 0 ∧
    Enc layout (.ref 0) (Val.vonZelle 1) 1 ∧
    ¬ Enc layout (.ref 0) (Val.vonZelle 2) 2 ∧
    ¬ Enc layout (.ref 0) (Val.vonZelle (2 ^ 64)) 0 := by
  refine ⟨⟨rfl, by decide, (), rfl, rfl, by decide⟩,
    ⟨rfl, by decide, (), rfl, rfl, by decide⟩, ?_, ?_⟩
  · intro h
    have := enc_ref_cell h (t := ()) rfl
    change (2 : Int) < 2 at this
    omega
  · intro h
    have := h.2.1
    exact (Nat.lt_irrefl (2 ^ 64)) this

/-- Code below 4096 cannot change the provider data or frame variables in this fixture. -/
theorem memory_data (code : List II) (hc : (code.flatMap encII).length ≤ 4096)
    {a : Nat} (ha : 4096 ≤ a) (ha' : a + 8 ≤ 2 ^ 64) :
    (memory code).rd64 (BitVec.ofNat 64 a) = (memory []).rd64 (BitVec.ofNat 64 a) := by
  apply rd64_keep (m := memory []) (m' := memory code) rfl
  intro j hj
  have he : (BitVec.ofNat 64 a + BitVec.ofNat 64 j).toNat = a + j := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  simp only [memory, he, List.flatMap_nil, List.length_nil, Nat.not_lt_zero, ↓reduceIte]
  rw [if_neg (by omega)]

theorem env_memory (code : List II) (hc : (code.flatMap encII).length ≤ 4096) :
    EnvAt layout (memory code) 4096 env := by
  intro τ x
  cases x with
  | here =>
    refine ⟨0, ?_, encoded_zeuge.1⟩
    change (memory code).rd64 (BitVec.ofNat 64 4136) = some 0
    rw [memory_data code hc (by decide) (by decide)]
    decide +kernel
  | there x =>
    cases x with
    | here =>
      refine ⟨1, ?_, encoded_zeuge.2.1⟩
      change (memory code).rd64 (BitVec.ofNat 64 4128) = some 1
      rw [memory_data code hc (by decide) (by decide)]
      decide +kernel
    | there x => nomatch x

theorem world_memory (code : List II) (hc : (code.flatMap encII).length ≤ 4096) :
    WeltAt (memory code) layout world := by
  refine ⟨fun t f k hk => ?_, (fun g => nomatch g), fun _ _ _ => rfl⟩
  change (k : Int) < 2 at hk
  have : k = 0 ∨ k = 1 := by omega
  rcases this with rfl | rfl
  · refine ⟨11, ?_, rfl⟩
    change (memory code).rd64 (BitVec.ofNat 64 8192) = some 11
    rw [memory_data code hc (by decide) (by decide)]
    decide +kernel
  · refine ⟨22, ?_, rfl⟩
    change (memory code).rd64 (BitVec.ofNat 64 8200) = some 22
    rw [memory_data code hc (by decide) (by decide)]
    decide +kernel

theorem pre (code : List II) (hc : (code.flatMap encII).length ≤ 4096)
    (ho : code.all (fun i => decide (i.o < 256)) = true) :
    PreS layout (memory code) 0 4096 64 6 code env := by
  refine ⟨by decide, by decide, ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
    ?_, ?_, env_memory code hc, trivial, wstab_true _ _⟩
  · exact codeAt_bytes code 0 ho (bytes code (by omega))
  · have hn : (code.flatMap encII).length = 16 * code.length := by
      exact flatMap_enc_len code
    unfold CodeFar
    simp only [show (0 : Runner.W).toNat = 0 by decide,
      show (4096 : Runner.W).toNat = 4096 by decide, Nat.zero_add]
    omega

/-- The equality and reads run in an inhabited world with all simulation premises supplied. -/
theorem read_simulation_zeuge :
    lowE layout checks 6 = some (readCode, readTop) ∧
    Pre layout (memory readCode) 0 4096 64 6 readCode env (fun m => WeltAt m layout world) ∧
    Ok (memory readCode) 0 4096 64 6 readCode (Enc layout .bool true) := by
  have hc : (readCode.flatMap encII).length ≤ 4096 := by decide +kernel
  have hp := PreS.welt (pre readCode hc (by decide +kernel)) (Nat.le_refl _) (world_memory readCode hc) layout_in (by decide)
  refine ⟨lowering_zeuge.1, hp, ?_⟩
  have h := lowE_ok world world (fun _ h => h) checks 6 readCode readTop lowering_zeuge.1
    (by decide +kernel) (memory readCode) 0 env hp
  exact h

def value : Expr D Γ [] (.int 0 255) := .widen (by decide) (by decide) (.lit 73)
def valueCode : List II := [ci 1 6 73 0]
def addressCode : List II := [ci 2 7 4 0, ci 1 8 8 0, ci 5 7 7 8, ci 1 8 8192 0, ci 3 7 7 8]
def after : World D := world.storeSlot () 1 () ⟨73, by decide, by decide⟩

/-- The write's actual store runs, preserving both reference variables and the neighboring cell. -/
theorem write_simulation_zeuge :
    lowS (fun _ => 0) layout 4 ([], 0) [] (0, 0) assignment = some (writeCode, writeTop) ∧
    PreS layout (memory writeCode) 0 4096 64 6 writeCode env ∧
    ∃ m', Star ⟨0, 4096⟩ (memory writeCode)
        ⟨0 + BitVec.ofNat 64 (16 * writeCode.length), 4096⟩ m' ∧
      AgreeW layout 4096 6 64 (memory writeCode) m' ∧ EnvAt layout m' 4096 env ∧
      WeltAt m' layout after ∧ m'.rd64 8192 = some 11 ∧ m'.rd64 8200 = some 73 := by
  have hc : (writeCode.flatMap encII).length ≤ 4096 := by decide +kernel
  have hp := pre writeCode hc (by decide +kernel)
  have hw := world_memory writeCode hc
  have hW : WIn layout 4096 64 64 :=
    ⟨layout_in, layout_dis, by decide, by decide, by decide⟩
  have hcode : writeCode = valueCode ++ addressCode ++ [stC 6] := by decide +kernel
  refine ⟨lowering_zeuge.2.1, hp, ?_⟩
  have hp' : PreS layout (memory writeCode) 0 4096 64 6
      (valueCode ++ addressCode ++ [stC 6]) env := by rw [← hcode]; exact hp
  obtain ⟨m', hs, ha, he, hw'⟩ := store_ok (σ := world) (σ' := after) hp' hW hw (by decide)
    (fun m pc hp => lowE_ok world world (fun _ h => h) value 6 valueCode 7
      (by decide +kernel) (by decide) m pc env hp)
    (fun m pc hp => (slotRefA_ok (t := ()) (n := 0) rfl
      (cr := ([ci 2 7 4 0], 8)) (top := 9) (by decide +kernel) (by decide)
      (fun m pc hp => lowE_ok world world (fun _ h => h) second 7 [ci 2 7 4 0] 8
        (by decide +kernel) (by decide) m pc env hp) hp).mono (fun _ h => h.1))
    (by decide) (fun m w hm henc => weltAt_slot hm layout_in layout_dis (by decide) henc)
  refine ⟨m', ?_, ha, he, hw', ?_, ?_⟩
  · simpa only [← hcode] using hs
  · obtain ⟨w, hr, he⟩ := hw'.1 () () 0 (by decide)
    have he' : w = 11 := he
    rw [he', show BitVec.ofNat 64 (layout.elem () () 0) = (8192 : Runner.W) by decide] at hr
    exact hr
  · obtain ⟨w, hr, he⟩ := hw'.1 () () 1 (by decide)
    have he' : w = 73 := he
    rw [he', show BitVec.ofNat 64 (layout.elem () () 1) = (8200 : Runner.W) by decide] at hr
    exact hr

/-- Runner fixtures supply the region and reference words explicitly, before the lowered G fragment.
    This bootstrap is test setup, not an implementation of G's provider call. -/
def runnerImage (writing : Bool) : List Runner.B :=
  let base := Runner.Prog.IMG
  let L := { layout with col := fun _ _ => base + 8192, lo := base + 8192, hi := base + 8208 }
  let setupCode := [ci 1 4 1 0, ci 1 5 0 0, ci 1 7 (base + 8192) 0, ci 1 6 11 0, ci 16 7 6 0,
    ci 1 7 (base + 8200) 0, ci 1 6 22 0, ci 16 7 6 0]
  let body := if writing then
      ((lowS (fun _ => 0) L 4 ([], 0) [] (0, 0) assignment).getD ([], 0)).1 ++
        ((lowE L (read second) 6).getD ([], 0)).1
    else ((lowE L checks 6).getD ([], 0)).1
  let code := setupCode ++ body ++ [ci 1 10 231 0, ci 2 11 6 0, ci 1 12 0 0, ci 1 13 0 0,
    ci 1 14 0 0, ci 1 15 0 0, ci 1 16 0 0, ci 23 17 10 0]
  let bs := Runner.Prog.leN 8 (base + 4096) ++ Runner.Prog.leN 8 0 ++ code.flatMap encII
  bs ++ List.replicate (9000 - bs.length) 0

/-- Static images have no supplied region; raw provider words are not accepted as regions. -/
theorem refused_zeuge : chkC (some (.ref 0)) 5 = none ∧
    lowEnd (fun _ => 0) layout 4 ([], 0) [] (0, 0) GRegion.rumpf = none := by decide +kernel

end Gabbro.Stage0.Senke.ReferenceProbe
