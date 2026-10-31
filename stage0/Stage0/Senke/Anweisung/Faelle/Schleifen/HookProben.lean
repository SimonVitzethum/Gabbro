/- Joint source fixtures for the actual forever lowering, including ABI and nested counters. -/
import Stage0.Senke.Anweisung.Faelle.Schleifen.Proben
import Stage0.Senke.Anweisung.Faelle.Schleifen.Counted
import Stage0.Senke.Anweisung.Faelle.Schleifen.CounterRun

namespace Gabbro.Stage0.Senke.ForeverHookProbe
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def u : UProg := {
  tabs := [], locks := [], axs := [], annahmen := ["tick"]
  globs := [{ name := "count", ty := .int 0 100, init := 0, var := true }]
  fns := [
    { name := "main", params := [], kinds := [], res := some (0, 100), held := [], puts := [], gives := [], gputs := ["count"], body := [], ret := .val (.lit 0) },
    { name := "worker", params := [("parameter", .int 0 100)], kinds := [.int], res := some (0, 100), held := [], puts := [], gives := [], gputs := ["count"], body := [], ret := .val (.lit 0) },
    { name := "callee", params := [("parameter", .int 0 100)], kinds := [.int], res := some (0, 100), held := [], puts := [], gives := [], gputs := ["count"], body := [], ret := .val (.lit 0) }]
}
abbrev D := declOf u
abbrev mainFn : D.Fn := ⟨0, by decide⟩
abbrev worker : D.Fn := ⟨1, by decide⟩
abbrev callee : D.Fn := ⟨2, by decide⟩
abbrev progress : D.Annahme := some ⟨0, by decide⟩
abbrev locals : Ctx := [.int 73 73, .int 41 41, .int 0 100]

theorem fit (f g : D.Fn) : RufPasst D (vertragVon D f) (D.sigNr (D.sig g)) [] := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  have hf' : f = 0 ∨ f = 1 ∨ f = 2 := by change f < 3 at hf; omega
  have hg' : g = 0 ∨ g = 1 ∨ g = 2 := by change g < 3 at hg; omega
  rcases hf' with rfl | rfl | rfl <;> rcases hg' with rfl | rfl | rfl <;>
    exact {
      hw := fun t => Fin.elim0 t
      hg := fun g _ => by
        have hz : g = ⟨0, by decide⟩ := by
          apply Fin.ext
          have h := g.isLt
          change g.val < 1 at h
          change g.val = 0
          omega
        subst g
        decide +revert
      hk := ⟨[], List.Perm.nil, List.Sublist.refl []⟩
      hh := fun l => Fin.elim0 l }


abbrev count : D.Glob := ⟨0, by decide⟩

def readCount {Γ : Ctx} : Expr D Γ [] (.int 0 100) := .glob count (by intro w h; cases h)

def calleeBody : Endblock D (vertragVon D callee) false [.int 0 100] [] :=
  .cons (.ite (.eq readCount (.lit 0))
    (.cons (.assignGlob count (.widen (by decide) (by decide) (.lit 1)) (by decide) (by intro w h; cases h)) .nil)
    (.cons (.ite (.eq readCount (.lit 1))
      (.cons (.assignGlob count (.widen (by decide) (by decide) (.lit 2)) (by decide) (by intro w h; cases h)) .nil)
      (.cons (.ite (.eq readCount (.lit 2))
        (.cons (.assignGlob count (.widen (by decide) (by decide) (.lit 3)) (by decide) (by intro w h; cases h)) .nil)
        (.cons (.assignGlob count (.widen (by decide) (by decide) (.lit 4)) (by decide) (by intro w h; cases h)) .nil)) .nil)) .nil))
    (.ret (.val (.var .here)) (.refl []))

def retN {Γ : Ctx} (n : Int) (hl : 0 ≤ n) (hh : n ≤ 100) :
    Endblock D (vertragVon D worker) true Γ [] :=
  .ret (.val (.widen hl hh (.lit n))) (.refl [])

/-- The callee result, both lexical sentinels and the parameter are checked together. -/
def inner (mode : Nat) : Block D (vertragVon D worker) true locals [] [] :=
  .bindCall callee (.cons (.var (.there (.there .here))) .nil) rfl (fit worker callee) rfl
    (.check (.and (.eq (.var .here) (.lit 17))
      (.and (.eq (.var (.there .here)) (.lit 73))
        (.and (.eq (.var (.there (.there .here))) (.lit 41))
          (.eq (.var (.there (.there (.there .here)))) (.lit 17)))))
      (retN 97 (by decide) (by decide)) (.cons (if mode = 8 then .ite (.or (.eq readCount (.lit 2)) (.eq readCount (.lit 4)))
        (.cons (.leave rfl) .nil) .nil
        else if mode = 6 then .ite (.eq readCount (.lit 2))
        (.cons (.leave rfl) .nil) .nil else .leave rfl) .nil))

def outer (mode : Nat) : Block D (vertragVon D worker) true locals [] [] :=
  .cons (.forever progress .tru (inner mode))
    (.check (.and (.eq (.var .here) (.lit 73))
      (.and (.eq (.var (.there .here)) (.lit 41))
        (.eq (.var (.there (.there .here))) (.lit 17))))
      (retN 98 (by decide) (by decide))
      (.cons (if mode = 8 then .ite (.eq readCount (.lit 4))
        (.cons (.ret (.val readCount) (.refl [])) .nil) .nil
        else if mode = 5 then .ite (.eq readCount (.lit 2))
        (.cons (.ret (.val readCount) (.refl [])) .nil) .nil
        else if mode = 6 then .ret (.val readCount) (.refl [])
        else if mode = 1 then .next rfl else if mode = 2 then .leave rfl
        else if mode = 3 then .ret (.val (.widen (by decide) (by decide) (.lit 43))) (.refl [])
        else .ite .tru .nil .nil) .nil))

def workerBody (mode : Nat) : Endblock D (vertragVon D worker) false [.int 0 100] [] :=
  .bind (.lit 41) (.bind (.lit 73)
    (.cons (.forever progress (if mode = 4 then .fls else if mode = 7 then .eq readCount (.lit 0) else .tru) (outer mode))
      (.ret (.val (.var (.there (.there .here)))) (.refl []))))

def mainBody : Endblock D (vertragVon D mainFn) false [] [] :=
  .bindCall worker (.cons (.widen (by decide) (by decide) (.lit 17)) .nil)
    rfl (fit mainFn worker) rfl (.ret (.val (.var .here)) (.refl []))

def program (mode : Nat) : Programm D where
  invariante _ := .tru
  requires _ := .tru
  ensures := Fin.cases .tru
    (Fin.cases (.eq (.var (.there .here)) (.lit 17))
      (Fin.cases (.eq (.var (.there .here)) (.lit 17)) (fun i => Fin.elim0 i)))
  rumpf := Fin.cases mainBody
    (Fin.cases (workerBody mode)
      (Fin.cases calleeBody (fun i => Fin.elim0 i)))

def image (budget mode : Nat) : Except String (List Runner.B) := do
  let b ← bild budget (program mode) (layU u (fun _ => none))
    [mainFn, worker, callee] Fin.val (fun f => if f.val = 0 then "main" else if f.val = 1 then "worker" else "callee") mainFn [] 512
  pure b.bytes

def expected (budget mode : Nat) : Int :=
  if budget = 0 then 111 else if mode = 4 then 104
  else if mode = 8 ∧ budget ≥ 2 then 4
  else if mode = 7 ∧ budget ≥ 2 then 104
  else if (mode = 5 ∨ mode = 6) ∧ budget ≥ 2 then 2
  else if mode = 2 then 17 else if mode = 3 then 43 else 111

def world : World D where
  slots t := Fin.elim0 t
  globs g := by
    have hg : g = count := by apply Fin.ext; have := g.isLt; change g.val < 1 at this; change g.val = 0; omega
    subst g
    exact ⟨0, by decide, by decide⟩
  spur := []

def oracle : Orakel D where
  wirkt a := Fin.elim0 a
  regLies r := Fin.elim0 r
  regSchreib r := Fin.elim0 r
  sichtbar _ _ := true

/-- Evaluate the same complete source program, retaining the canonical call and loop semantics. -/
def sourceOutcome (budget mode : Nat) : Int :=
  match rufAt (program mode) oracle budget 5 mainFn world Env.nil with
  | .ok _ v => v.n
  | .hardware (.fortschritt _) => 111
  | .logik .schleife => 104
  | _ => -1

/-- Source outcomes include callee writes, repeated invariant checks, nested
    counters, exhausted fuel, leave and return. Exhaustion uses the same code
    at zero and positive fuel; distinct traces need not have distinct exits. -/
theorem hook_outcomes_zeuge :
    (List.range 3).all (fun budget => (List.range 9).all
      (fun mode => decide (sourceOutcome budget mode = expected budget mode))) = true := by
  decide +kernel

/-- All joint fixtures use the complete image producer and the actual source hook. -/
theorem hook_images_zeuge :
    (List.range 3).all (fun budget => (List.range 9).all (fun mode => (image budget mode).isOk)) = true := by
  decide +kernel

/-- Joint successful witnesses expose actual callee effects. Mode 8 performs
    two outer passes with two inner passes each; mode 7 initially satisfies its
    invariant and fails it on re-entry. ABI sentinel checks execute in each body. -/
theorem hook_effects_zeuge :
    sourceOutcome 1 5 = 111 ∧ sourceOutcome 2 5 = 2 ∧
    sourceOutcome 1 6 = 111 ∧ sourceOutcome 2 6 = 2 ∧
    sourceOutcome 1 8 = 111 ∧ sourceOutcome 2 8 = 4 ∧
    sourceOutcome 1 7 = 111 ∧ sourceOutcome 2 7 = 104 ∧
    (image 2 8).isOk = true := by
  decide +kernel

/-- The generic literal theorem on the existing indirect-call image: the
    first real instruction materializes address 8192 in caller slot four. -/
theorem lowE_lit_counted_zeuge [Runner.IR.Kern] :
    Counted 1 ⟨2048, 4096⟩ FnptrProben.callMem ⟨2064, 4096⟩
      (Runner.Mem.write FnptrProben.callMem (Runner.IR.slot 4096 4) 8 8192) := by
  have code : CodeAt FnptrProben.callMem 2048 [ci 1 4 8192 0] := by
    intro k hk
    have zero : k = 0 := by simpa using hk
    subst k
    simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero]
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  exact lowE_lit_counted (L := FnptrProben.callLayout) (Γ := []) (Λ := [])
    (reserved := 0) (d := 4) (top := 5) (K := 256) (n := 8192)
    (by decide +kernel) code FnptrProben.call_frame (by decide) (by decide)

/-- Two binary nodes share the same recursive certificate and the actual
    accepted lowering. This exercises child composition beyond a literal. -/
theorem exprCost_zeuge :
    let e : Expr FnptrProben.D [] [] (.int 27 27) :=
      .add (.add (.lit 7) (.lit 9)) (.lit 11)
    (∃ P, Nonempty (ExprCost FnptrProben.callLayout 0 e 4 5 P)) ∧
    lowE FnptrProben.callLayout e 4 = some
      ([ci 1 4 7 0, ci 1 5 9 0, ci 3 4 4 5, ci 1 5 11 0, ci 3 4 4 5], 6) := by
  constructor
  · exact ⟨_, ⟨ExprCost.add (ExprCost.add .literal .literal) .literal⟩⟩
  · rfl

def compositeCode : List II :=
  [ci 1 4 7 0, ci 1 5 9 0, ci 3 4 4 5, ci 1 5 11 0, ci 3 4 4 5]

def compositeMem : Runner.Mem := {
  b := fun a => ((compositeCode.flatMap encII)[a.toNat - 2048]?).getD 0
  rd := fun _ => true
  wr := fun _ => true }

/-- All preconditions hold jointly on an actual emitted two-node expression;
    exact execution is obtained from certificate soundness, not evaluation. -/
theorem exprCost_execution_zeuge [Runner.IR.Kern] :
    ∃ m', Counted 5 ⟨2048, 4096⟩ compositeMem ⟨2128, 4096⟩ m' ∧
      Agree 4096 4 256 compositeMem m' ∧
      ∃ w, m'.rd64 (slot 4096 4) = some w ∧
        (∃ wa wb, (∃ x y, x = BitVec.ofInt 64 7 ∧ y = BitVec.ofInt 64 9 ∧ wa = x + y) ∧
          wb = BitVec.ofInt 64 11 ∧ w = wa + wb) := by
  have code : CodeAt compositeMem 2048 compositeCode := by
    have all : (List.finRange compositeCode.length).all (fun k => decide
      (compositeMem.rd8 (2048 + BitVec.ofNat 64 (16 * k.val)) = some (BitVec.ofNat 8 compositeCode[k.val].o) ∧
       compositeMem.rd32 (2048 + BitVec.ofNat 64 (16 * k.val) + 4) = some (II.f compositeCode[k.val].a) ∧
       compositeMem.rd32 (2048 + BitVec.ofNat 64 (16 * k.val) + 8) = some (II.f compositeCode[k.val].b) ∧
       compositeMem.rd32 (2048 + BitVec.ofNat 64 (16 * k.val) + 12) = some (II.f compositeCode[k.val].c))) = true := by
      decide +kernel
    intro k hk
    have h := of_decide_eq_true (List.all_eq_true.mp all ⟨k, hk⟩ (by simp))
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  have pre : PreS FnptrProben.callLayout compositeMem 2048 4096 256 4 compositeCode
      (Env.nil : Env FnptrProben.D []) := by
    refine ⟨by decide, by decide, ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
      code, ?_, ?_, trivial, wstab_true _ _⟩
    · unfold CodeFar; decide +kernel
    · intro _ x; nomatch x
  exact (ExprCost.add (ExprCost.add .literal .literal) .literal).sound
    (L := FnptrProben.callLayout) (Γ := []) (Λ := []) (reserved := 0) (top := 6)
    (e := .add (.add (.lit 7) (.lit 9)) (.lit 11)) (by rfl) (by decide) pre

/-- An actual accepted lexical block gets its count from the expression
    certificate and the empty continuation, with all frame/world premises
    jointly satisfied on the existing executable call image. -/
theorem countedBlockBind_case_zeuge [Runner.IR.Kern] :
    CountedReach 1 FnptrProben.callLayout 4096 4 256 [] ⟨2048, 4096⟩
      FnptrProben.callMem 2064 FnptrProben.world
      (Env.cons (D := FnptrProben.D) (τ := .int 8192 8192)
        ⟨8192, by decide, by decide⟩ Env.nil) 0 := by
  have pre : PreS FnptrProben.callLayout FnptrProben.callMem 2048 4096 256 4
      [ci 1 4 8192 0] (Env.nil : Env FnptrProben.D []) := by
    refine ⟨by decide, by decide, FnptrProben.call_frame, ?_, ?_, ?_, trivial, wstab_true _ _⟩
    · intro k hk
      have : k = 0 := by simpa using hk
      subst k
      simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero]
      exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    · unfold CodeFar; decide +kernel
    · intro _ x; nomatch x
  exact countedBlockBind_case (V := vertragVon FnptrProben.D 2)
    (l := false) (Λ := []) (Λ' := []) (e := .lit 8192) (rest := .nil)
    (passes := 1) (A := FnptrProben.addresses) (ens := ([], 4))
    (ex := (0, 0)) (top := 5) (Ks := 128) (nr := 0)
    (lo := 4) (pr := []) (reserved := 0) (Γ := []) (ρ := Env.nil)
    (v := ⟨8192, by decide, by decide⟩) .literal rfl (by decide)
    FnptrProben.call_win (by decide) (by simp) pre FnptrProben.call_world
    (fun cr tr lower m pc hp hw => by
      simp only [lowB, Option.some.injEq, Prod.mk.injEq] at lower
      obtain ⟨rfl, rfl⟩ := lower
      simpa using countedBlockNil_case (lo := 4) (pr := []) hp.env hw)

/-- A real caller, a one-instruction callee and a real return. -/
def countedCallCode : List II :=
  [ci 20 4 8 0, ci 1 0 0 0, ci 1 4 7 0, ci 21 0 0 0]

def countedCallMem : Runner.Mem := {
  b := fun a => if a = 1056 then 32 else
    ((countedCallCode.flatMap encII)[a.toNat]?).getD 0
  rd := fun _ => true
  wr := fun _ => true }

def countedCallSavedPC := Runner.Mem.write countedCallMem 1088 8 16
def countedCallEntered := Runner.Mem.write countedCallSavedPC 1096 8 1024
def countedCallReturned := Runner.Mem.write countedCallEntered 1120 8 7

/-- The generic call rule includes the callee's actual constant instruction.
    All code, target, save and return-memory premises hold jointly. -/
theorem countedCall_zeuge [Runner.IR.Kern] :
    Counted 3 ⟨0, 1024⟩ countedCallMem ⟨16, 1024⟩ countedCallReturned := by
  have body : Counted 1 ⟨32, 1088⟩ countedCallEntered
      ⟨48, 1088⟩ countedCallReturned := by
    apply const_step_counted (K := 16) (j := 4) (k := 7)
    · intro k hk
      have : k = 0 := by simpa using hk
      subst k
      simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero]
      exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩
    · decide
    · decide
    · decide
  exact countedCall (a := 4) (k := 8) (c := 0) (ra := 0) (rb := 0) (rc := 0)
    (m1 := countedCallSavedPC) (m2 := countedCallEntered) (u := ⟨48, 1088⟩)
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by decide +kernel) rfl rfl body
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by decide +kernel) (by decide +kernel)

theorem returning_pre_zeuge [Runner.IR.Kern] : PreS FnptrProben.callLayout countedCallEntered 32 1088 16 4
      [ci 1 4 7 0] (Env.nil : Env FnptrProben.D []) := by
    refine ⟨by decide, by decide, ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
      ?_, ?_, (fun _ x => nomatch x), trivial, wstab_true _ _⟩
    · intro k hk
      have : k = 0 := by simpa using hk
      subst k
      simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero]
      exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    · unfold CodeFar; decide +kernel

/-- Accepted source lowering, recursive cost certificate, ABI preservation and
    the real return are instantiated jointly on the executable callee image. -/
theorem returning_zeuge [Runner.IR.Kern] :
    ∃ m', Counted 2 ⟨32, 1088⟩ countedCallEntered ⟨16, 1024⟩ m' ∧
      Agree 1088 4 16 countedCallEntered m' ∧
      ∃ w, m'.rd64 (slot 1088 4) = some w ∧ w = BitVec.ofInt 64 7 := by
  have pre := returning_pre_zeuge
  exact ExprCost.returning (L := FnptrProben.callLayout) (reserved := 0)
    (Γ := []) (Λ := []) (e := .lit 7) (top := 5) .literal rfl
    (by decide) (by decide) (by decide) pre
    (by
      intro k hk
      have : k = 0 := by simpa using hk
      subst k
      simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero]
      exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩)
    (by unfold CodeFar; decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Full real call whose callee evidence comes from accepted source lowering,
    including return-code and ABI preservation, rather than an assumed body run. -/
theorem source_counted_call_zeuge [Runner.IR.Kern] :
    ∃ m', Counted 3 ⟨0, 1024⟩ countedCallMem ⟨16, 1024⟩ m' ∧
      ∃ w, m'.rd64 (slot 1088 4) = some w ∧ w = BitVec.ofInt 64 7 := by
  obtain ⟨m', body, _, value⟩ := returning_zeuge
  have enter : Counted 1 ⟨0, 1024⟩ countedCallMem ⟨32, 1088⟩ countedCallEntered := by
    have code : InsAt countedCallMem 0 20 4 8 0 :=
      ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    exact .next (run_step code (by decide)
      (run_call code (by decide +kernel) (m1 := countedCallSavedPC) rfl rfl)) (.refl _ _)
  exact ⟨m', enter.trans body, value⟩

/-- Declaration, source certificate and the actual call ABI hold jointly. -/
theorem declared_call_zeuge [Runner.IR.Kern] :
    ∃ n m', n ≤ 3 ∧ Counted n ⟨0, 1024⟩ countedCallMem ⟨16, 1024⟩ m' ∧
      Agree 1088 4 16 countedCallEntered m' ∧
      ∃ w, m'.rd64 (slot 1088 4) = some w ∧ w = BitVec.ofInt 64 7 := by
  have certificate : CalleeCostCertificate FnptrProben.callLayout (fun _ => 2) 2
      0 (show Expr FnptrProben.D [] [] (.int 7 7) from .lit 7) 4
      (fun w => w = BitVec.ofInt 64 7) := ⟨1, .literal, by decide⟩
  exact certificate.call (t := ⟨0, 1024⟩) (a := 4) (k := 8) (c := 0)
    (m1 := countedCallSavedPC) (m2 := countedCallEntered) (target := 32)
    (top := 5) (K := 16)
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by decide +kernel) rfl rfl rfl (by decide) (by decide) (by decide)
    returning_pre_zeuge
    (by
      intro k hk
      have : k = 0 := by simpa using hk
      subst k
      simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero]
      exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩)
    (by unfold CodeFar; decide +kernel) (by decide +kernel) (by decide +kernel)

/-- A concrete positive-budget header executes one real instruction. This is
    a joint witness for counting/erasure/composition, not a loop cost bound. -/
theorem counted_header_zeuge [Runner.IR.Kern] :
    Counted 1 ⟨2016, 4096⟩ (CounterCallProbe.loaded ⟨1, by decide⟩)
      ⟨2032, 4096⟩ (CounterCallProbe.loaded ⟨1, by decide⟩) := by
  obtain ⟨test, _, count, _⟩ := CounterCallProbe.counter_facts ⟨0, by decide⟩
  have h := counter_fuel_step 0 (by decide)
  exact .next (counter_positive (t := ⟨2016, 4096⟩) test count h.1) (.refl _ _)

end Gabbro.Stage0.Senke.ForeverHookProbe
