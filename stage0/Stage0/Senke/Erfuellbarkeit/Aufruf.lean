/-
  Subject: Satisfiability of the Stage-0 call premises (stream E4): `FunSpec`, the caller's code and frame premises
           and the world placement hold jointly, and an indirect call runs to its result.
-/
module
public import Stage0.Senke.Erfuellbarkeit.Fixture
@[expose] public section


namespace Gabbro.Stage0.Senke.Erfuellbarkeit
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option maxRecDepth 10000

/-- Finite executable checks are expanded through the canonical enumeration. -/
theorem allFin {n : Nat} {Q : Fin n → Prop} [DecidablePred Q]
    (h : (List.finRange n).all (fun i => decide (Q i)) = true) : ∀ i, Q i :=
  fun i => of_decide_eq_true (List.all_eq_true.mp h i (by simp))

local instance (m : Runner.Mem) (pc : Runner.W) (o : Nat) (a b c : BitVec 32) :
    Decidable (InsAt m pc o a b c) :=
  if h : m.rd8 pc = some (BitVec.ofNat 8 o) ∧ m.rd32 (pc + 4) = some a ∧
      m.rd32 (pc + 8) = some b ∧ m.rd32 (pc + 12) = some c then
    .isTrue ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  else .isFalse (fun h' => h ⟨h'.op, h'.f1, h'.f2, h'.f3⟩)

def tiny : Programm D where
  invariante i := nomatch i
  requires _ := .tru
  ensures _ := .tru
  rumpf f := .ret (.val (if f.val = 0 then .widen (by decide) (by decide) (.lit 21)
    else .widen (by decide) (by decide) (.lit 22))) List.Perm.nil

def addresses (f : D.Fn) : Nat := 64 + 512 * f.val

def callLayout : Lay D := { layout 8192 with fa := addresses, sb := 4096, st := 2048 }

def target (f : D.Fn) : List II := ((lowFun 1 tiny addresses callLayout f).getD ([], 0)).1

def pointer : Expr D [] [] (.fnptr 0) := .glob () (by intro w h; cases h)

def indirect : List II := [ci 1 4 8192 0, ci 15 4 4 0] ++ callTailN 0 0 4 true

def caller : List II := indirect ++ receiveC (D.sigNr 0) 4

/-- Code segments followed by writable zero memory; the world and depth words are initialized below. -/
def callMem : Runner.Mem :=
  let segments := [(64, (target 0).flatMap encII), (576, (target 1).flatMap encII),
    (1088, (target 2).flatMap encII), (2048, caller.flatMap encII)]
  let base : Runner.Mem := {
    b := fun a => match segments.find? (fun s => s.1 ≤ a.toNat && a.toNat < s.1 + s.2.length) with
      | some s => (s.2[a.toNat - s.1]?).getD 0
      | none => 0
    rd := fun _ => true
    wr := fun _ => true }
  write (write base 8192 8 64) 4112 8 3

theorem target_lower : ∀ f : Fin 3, lowFun 1 tiny addresses callLayout f = some (target f, 13) := by
  exact @allFin 3 (fun f => lowFun 1 tiny addresses callLayout f = some (target f, 13))
    (fun _ => inferInstance) (by decide +kernel)

theorem targets_code : PCode callMem addresses target 4096 256 := by
  have h : (List.finRange 3).all (fun f => (List.finRange (target f).length).all (fun k =>
      decide (InsAt callMem (BitVec.ofNat 64 (addresses f) + BitVec.ofNat 64 (16 * k.val))
        (target f)[k.val].o (II.f (target f)[k.val].a) (II.f (target f)[k.val].b) (II.f (target f)[k.val].c)))) = true := by
    decide +kernel
  have hf : ∀ f : Fin 3, CodeFar (BitVec.ofNat 64 (addresses f)) (target f).length 4096 256 := by
    unfold CodeFar
    apply allFin
    decide +kernel
  change ∀ f : Fin 3, CodeAt callMem (BitVec.ofNat 64 (addresses f)) (target f) ∧
    CodeFar (BitVec.ofNat 64 (addresses f)) (target f).length 4096 256
  refine fun f => ⟨fun k hk => ?_, hf f⟩
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h f (by simp)) ⟨k, hk⟩ (by simp))

theorem caller_code : CodeAt callMem 2048 caller := by
  have h : ∀ k : Fin caller.length, InsAt callMem (2048 + BitVec.ofNat 64 (16 * k.val))
      caller[k.val].o (II.f caller[k.val].a) (II.f caller[k.val].b) (II.f caller[k.val].c) := by
    apply allFin
    decide +kernel
  exact fun k hk => h ⟨k, hk⟩

theorem call_frame : FrameOK callMem 4096 256 := ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩

theorem call_pre [Kern] : PreS callLayout callMem 2048 4096 256 4 caller (Env.nil : Env D []) := by
  refine ⟨by decide, by decide, call_frame, caller_code, ?_, ?_, trivial, wstab_true _ _⟩
  · unfold CodeFar; decide +kernel
  · intro _ x; nomatch x

theorem call_world [Kern] : WeltAt callMem callLayout world := by
  refine ⟨(fun t => nomatch t), (fun g => ?_), (fun _ _ _ => rfl)⟩
  cases g
  exact ValueAt.ofCellWord (w := 64) (by decide) (by decide +kernel) rfl

theorem call_win : WIn callLayout 4096 128 256 := by
  refine ⟨⟨(fun t => nomatch t), fun g => by cases g; exact ⟨by decide, by decide⟩, by decide⟩, ?_, by decide, by decide, by decide⟩
  refine ⟨?_, ?_, ?_⟩
  · intro c c' hc hc' h
    cases c with
    | elem t => nomatch t
    | glob g =>
      cases c' with
      | elem t => nomatch t
      | glob g' => cases g; cases g'; exact absurd rfl h
  · intro c c' hc hc' h
    cases c with
    | elem t => nomatch t
    | glob g =>
      cases c' with
      | elem t => nomatch t
      | glob g' => cases g; cases g'; rfl
  · intro c hc
    cases c with
    | elem t => nomatch t
    | glob _ => rfl

theorem call_sync : TicketSync callMem callLayout 4096 128 [] :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    (fun l => nomatch l), by decide, (fun l => nomatch l), (fun l => nomatch l), (fun l => nomatch l)⟩

theorem call_umf [Kern] : Umf callLayout addresses target 2 callMem 4096 128 256 [] :=
  ⟨targets_code, by decide +kernel, by decide, call_sync, by decide⟩

theorem call_head : Kopf callLayout 2 callMem 4096 256 0 0 (Env.nil : Env D []) tiny world :=
  ⟨by decide +kernel, by decide +kernel, (fun _ x => nomatch x), by decide, trivial⟩

local instance [Kern] : TorOK callLayout O where
  ans a := nomatch a
  puf a := nomatch a
  ref_answer a := nomatch a
  area a := nomatch a

local instance : SichtOK O := ⟨fun _ _ => rfl⟩

theorem addresses_bound (f : D.Fn) : addresses f < 2 ^ 31 := by
  have h := f.isLt
  dsimp only [addresses]
  omega

theorem target_bound : ∀ f : Fin 3, 16 * (target f).length < 2 ^ 31 := by
  apply allFin
  decide +kernel

theorem call_spec [Kern] : FunSpec callLayout addresses target (rufAt tiny O 1 2) 2 39 := by
  exact lowFun_spec (P := tiny) (O := O) (passes := 1) (L := 13) rfl
    (fun f => ⟨13, target_lower f, Nat.le_refl _⟩)
    addresses_bound
    (fun f => target_bound f) 2 (by decide)

private theorem aufruf_lauf [Kern] :
    FunSpec callLayout addresses target (rufAt tiny O 1 2) 2 39 ∧
    lowInd callLayout pointer .nil = some (indirect, 9) ∧
    PreS callLayout callMem 2048 4096 256 4 indirect (Env.nil : Env D []) ∧
    Umf callLayout addresses target 2 callMem 4096 128 256 [] ∧
    WIn callLayout 4096 128 256 ∧ WeltAt callMem callLayout world ∧
    ∃ m', Star ⟨2048, 4096⟩ callMem ⟨2144, 4096⟩ m' ∧ AgreeW callLayout 4096 4 256 callMem m' ∧
      ResultAt callLayout m' (slot 4096 4) (FB + contextWords (D.params 2)) (D.erg 2)
        (⟨21, by decide, by decide⟩ : Zahl 0 100) ∧
      WeltAt m' callLayout world := by
  refine ⟨call_spec, rfl, call_pre.left, call_umf, call_win, call_world, ?_⟩
  have h := lowInd_ok (same := rfl) (reserved := 0) call_spec (A := addresses)
    addresses_bound
    pointer .nil world world (c := indirect) (top := 9) (by rfl) (by decide)
    call_pre.left call_umf call_win call_world HeldIn.nil
  obtain ⟨m', steps, changed, ⟨result, _, _⟩, world'⟩ := h
  exact ⟨m', steps, changed, result, world'⟩

/-- **Satisfiability of the Stage-0 call premises** (stream E4): for a program of three functions, a function
    specification `FunSpec`, the caller's code and frame premises (`PreS`, `Umf`, `WIn`) and the world placement
    `WeltAt` hold jointly, and the indirect call through a global pointer runs to the callee's result 21. -/
theorem senke_aufruf_erfuellbar [Kern] :
    ∃ (L : Lay D) (A : D.Fn → Nat) (C : D.Fn → List II)
      (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (m : Runner.Mem) (σ : World D),
      FunSpec L A C R 2 39 ∧ PreS L m 2048 4096 256 4 indirect (Env.nil : Env D []) ∧
      Umf L A C 2 m 4096 128 256 [] ∧ WIn L 4096 128 256 ∧ WeltAt m L σ ∧
      ∃ m', Star ⟨2048, 4096⟩ m ⟨2144, 4096⟩ m' ∧
        ResultAt L m' (slot 4096 4) (FB + contextWords (D.params 2)) (D.erg 2)
          (⟨21, by decide, by decide⟩ : Zahl 0 100) := by
  obtain ⟨spec, _, pre, umf, win, placed, m', steps, _, result, _⟩ := aufruf_lauf
  exact ⟨callLayout, addresses, target, rufAt tiny O 1 2, callMem, world, spec, pre, umf, win, placed,
    m', steps, result⟩

end Gabbro.Stage0.Senke.Erfuellbarkeit
