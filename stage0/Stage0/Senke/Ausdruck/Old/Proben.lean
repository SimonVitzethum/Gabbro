/- Jointly inhabited entry/exit snapshot fixtures and explicit fragment refusals. -/
module
public import Stage0.Senke.Ausdruck.Old.Sound
public import Stage0.Senke.Ausdruck.Old.Distinct
public import Stage0.Senke.Ausdruck.Old.EnvironmentProbe
public import Stage0.Senke.Ausdruck.FnptrProben
public import Stage0.Senke.Ausdruck.Quant.Proben
@[expose] public section


namespace Gabbro.Stage0.Senke.OldProbe
open Gabbro.Grammatik Runner.IR Runner.Mem
open FnptrProben (D)
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

def layout : Lay D := FnptrProben.refLayout

def entry := FnptrProben.world

def exitWorld : World D := { entry with globs := fun _ => ⟨1, by decide⟩ }

def expr : Expr D [] [] (.fnptr 0) := .oldG () (by intro w h; cases h)

def frameLayout : FrameLayout := ⟨[], none, 0, 1, 0⟩

def readCode : List II := [ci 2 5 4 0]
def captureCode : List II := [ci 1 4 2048 0, ci 15 4 4 0]

/-- The exit global is 80; the saved entry word is 64. The code lies outside the frame. -/
def memory (code : List II) : Runner.Mem where
  b a := if a.toNat = 2048 then 80 else if a.toNat = 1056 then 64
    else if (2048 < a.toNat ∧ a.toNat < 2056) ∨ (1056 < a.toNat ∧ a.toNat < 1064) then 0
    else ((code.flatMap encII)[a.toNat]?).getD 0
  rd _ := true
  wr _ := true

theorem frame (c : List II) : FrameOK (memory c) 1024 16 :=
  ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩

theorem lay : LayIn layout := by
  refine ⟨(fun t => nomatch t), ?_, by decide⟩
  intro g
  cases g
  decide +kernel

theorem world [Kern] (c : List II) : WeltAt (memory c) layout exitWorld := by
  refine ⟨(fun t => nomatch t), ?_, fun _ _ _ => rfl⟩
  intro g
  cases g
  refine ValueAt.ofCellWord (w := 80) (by decide) ?_ rfl
  change (memory c).rd64 2048 = some 80
  simp [Runner.Mem.rd64, Runner.Mem.all, Runner.Mem.le, memory]

theorem read_at : CodeAt (memory readCode) 0 readCode := by
  intro k hk
  have : k = 0 := by simp only [readCode, List.length_singleton] at hk; omega
  subst k
  change InsAt (memory readCode) 0 2 (II.f 5) (II.f 4) (II.f 0)
  constructor <;> decide +kernel

theorem capture_at : CodeAt (memory captureCode) 0 captureCode := by
  intro k hk
  have : k = 0 ∨ k = 1 := by simp only [captureCode, List.length_cons, List.length_nil] at hk; omega
  rcases this with rfl | rfl
  · change InsAt (memory captureCode) 0 1 (II.f 4) (II.f 2048) (II.f 0)
    constructor <;> decide +kernel
  · change InsAt (memory captureCode) 16 15 (II.f 4) (II.f 4) (II.f 0)
    constructor <;> decide +kernel

theorem read_pre [Kern] : PreS layout (memory readCode) 0 1024 16 5 readCode (Env.nil : Env D []) 1 := by
  refine ⟨by decide, by decide, frame _, read_at, ?_, (fun _ x => nomatch x), trivial, wstab_true _ _⟩
  unfold CodeFar
  decide +kernel

theorem saved : EntrySnapshots.At layout entry (memory readCode) 1024 (oldCells expr) 4 := by
  exact ⟨ValueAt.of_enc (w := 64) (by decide) (by decide +kernel) rfl, trivial⟩

/-- A real entry word differing from the exit global satisfies every simulation premise. -/
theorem lowEns_ok_zeuge [Kern] :
    lowEns layout frameLayout expr 5 = some (readCode, 6) ∧
    PreS layout (memory readCode) 0 1024 16 5 readCode (Env.nil : Env D []) 1 ∧
    EntrySnapshots.At layout entry (memory readCode) 1024 (oldCells expr) 4 ∧
    eval entry expr exitWorld .nil ≠ eval exitWorld expr exitWorld .nil ∧
    ValueOk layout (memory readCode) 0 1024 16 5 readCode (.fnptr 0) (eval entry expr exitWorld .nil) := by
  refine ⟨rfl, read_pre, saved, ?_, ?_⟩
  · intro h
    have hh := congrArg (fun v : Wert D (.fnptr 0) => v.1.val) h
    change (0 : Nat) = 1 at hh
    omega
  · exact lowEns_ok frameLayout entry exitWorld (fun _ h => h) lay expr 5 readCode 6 rfl (by decide)
      (memory readCode) 0 .nil (PreS.welt read_pre (Nat.le_refl _) (world readCode) lay (by decide)) saved rfl

/-- Complete entry capture is the shared checked world-span execution. -/
theorem capture_ok_zeuge [Kern] :
    EntrySnapshots.capture layout [.glob ()] 4 = some captureCode ∧
    ∃ m', Star ⟨0, 1024⟩ (memory captureCode) ⟨32, 1024⟩ m' ∧
      EntrySnapshots.At layout exitWorld m' 1024 [.glob ()] 4 := by
  refine ⟨by decide +kernel, ?_⟩
  obtain ⟨m', run, _, saved⟩ := EntrySnapshots.capture_world_ok
    (L := layout) (cells := [.glob ()]) (base := 4) (code := captureCode)
    (m := memory captureCode) (pc := 0) (fp := 1024) (K := 16)
    (by decide +kernel) (frame _) (by decide) (by decide)
    capture_at (by unfold CodeFar; decide +kernel) (world captureCode) lay (by decide)
  exact ⟨m', run, saved⟩

def tableLayout : Lay QuantProbe.D where
  col _ _ := 2048
  ga g := nomatch g
  lo := 2048
  hi := 2080
  tor _ := none
  byte _ := none

def slotExpr : Expr QuantProbe.D [] [] (.opt 4) :=
  .oldS QuantProbe.tab QuantProbe.field (QuantProbe.index 1 (by decide)) QuantProbe.access

theorem oldS_literal_zeuge : lowEns tableLayout frameLayout slotExpr 5 = some (readCode, 6) := rfl

theorem oldS_parameter_refused_zeuge :
    lowEns tableLayout frameLayout (Expr.oldS (Γ := [.index 4]) QuantProbe.tab QuantProbe.field
      (.var .here) QuantProbe.access) 6 = none := rfl

theorem multiple_occurrences_zeuge :
    EntrySnapshots.capture layout [.glob (), .glob ()] 4 =
      some [ci 1 4 2048 0, ci 15 4 4 0, ci 1 5 2048 0, ci 15 5 5 0] := by decide +kernel

theorem distinct_occurrences_zeuge :
    EntrySnapshots.capture tableLayout
      [.elem QuantProbe.tab QuantProbe.field 0, .elem QuantProbe.tab QuantProbe.field 1] 4 =
      some [ci 1 4 2048 0, ci 15 4 4 0, ci 1 5 2056 0, ci 15 5 5 0] := by decide +kernel

theorem lowEns_top_zeuge : lowEns layout frameLayout expr 5 = some (readCode, 6) ∧ 5 < 6 :=
  ⟨rfl, by decide⟩

theorem entryIndex_ok_zeuge :
    entryIndex (QuantProbe.index 1 (by decide)) = some 1 ∧
    intValue (eval QuantProbe.initial (QuantProbe.index 1 (by decide)) QuantProbe.initial .nil) = some 1 :=
  ⟨rfl, rfl⟩

/-- A nonzero computed old index exercises every closed arithmetic index constructor. -/
def computedIndex : Expr QuantProbe.D [] [] (.index 4) :=
  .widen (by decide) (by decide)
    (.add (.sub (.mul (.lit 2) (.lit 2)) (.lit 2)) (.neg (.lit 1)))

theorem computed_snapshot_zeuge :
    entryIndex computedIndex = some 1 ∧
    intValue (eval QuantProbe.initial computedIndex QuantProbe.initial .nil) = some 1 ∧
    oldCells (Expr.oldS QuantProbe.tab QuantProbe.field computedIndex QuantProbe.access) =
      [.elem QuantProbe.tab QuantProbe.field 1] ∧
    lowEns tableLayout frameLayout
      (Expr.oldS QuantProbe.tab QuantProbe.field computedIndex QuantProbe.access) 5 =
        some (readCode, 6) ∧
    EntrySnapshots.capture tableLayout [.elem QuantProbe.tab QuantProbe.field 1] 4 =
      some [ci 1 4 2056 0, ci 15 4 4 0] :=
  ⟨rfl, rfl, rfl, rfl, by decide +kernel⟩

end Gabbro.Stage0.Senke.OldProbe
