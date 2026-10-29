/-
  Subject: Joint, successful witnesses of the indirect-call simulation premises.
-/
import Stage0.Senke.Ausdruck.FnptrProben

namespace Gabbro.Stage0.Senke.FnptrProben
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

def caller : List II := indirect ++ [ci 2 4 6 0]

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

theorem call_world : WeltAt callMem callLayout world := by
  refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
  cases g
  decide +kernel

theorem call_win : WIn callLayout 4096 128 256 := by
  refine ⟨⟨(fun t => nomatch t), fun _ => ⟨by change 8192 ≤ 8192; decide, by change 8192 + 8 ≤ 8200; decide⟩, by decide⟩, ?_, by decide, by decide, by decide⟩
  constructor
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

theorem call_sync : SyncOK callMem callLayout 4096 128 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    (fun l => nomatch l), by decide, (fun l => nomatch l), (fun l => nomatch l), (fun l => nomatch l)⟩

theorem call_umf [Kern] : Umf callLayout addresses target 2 callMem 4096 128 256 :=
  ⟨targets_code, by decide +kernel, by decide, call_sync, by decide⟩

theorem call_head : Kopf callLayout 2 callMem 4096 256 0 0 (Env.nil : Env D []) tiny world :=
  ⟨by decide +kernel, by decide +kernel, (fun _ x => nomatch x), by decide, fun _ h => nomatch h⟩

local instance [Kern] : TorOK callLayout O where
  ans a := nomatch a
  puf a := nomatch a

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

/-- The pointer, callee specification, code, world and frame premises hold together, and the call returns 21. -/
theorem lowInd_ok_zeuge [Kern] :
    FunSpec callLayout addresses target (rufAt tiny O 1 2) 2 39 ∧
    lowInd callLayout pointer .nil = some (indirect, 9) ∧
    PreS callLayout callMem 2048 4096 256 4 indirect (Env.nil : Env D []) ∧
    Umf callLayout addresses target 2 callMem 4096 128 256 ∧
    WIn callLayout 4096 128 256 ∧ WeltAt callMem callLayout world ∧
    ∃ m', Star ⟨2048, 4096⟩ callMem ⟨2144, 4096⟩ m' ∧ AgreeW callLayout 4096 4 256 callMem m' ∧
      (∃ w, m'.rd64 (slot 4096 6) = some w ∧ Enc callLayout (.int 0 100) (⟨21, by decide, by decide⟩ : Zahl 0 100) w) ∧
      WeltAt m' callLayout world := by
  refine ⟨call_spec, rfl, call_pre.left, call_umf, call_win, call_world, ?_⟩
  have h := lowInd_ok call_spec (A := addresses)
    addresses_bound
    pointer .nil world world (c := indirect) (top := 9) (by rfl) (by decide)
    call_pre.left call_umf call_win call_world
  exact h

/-- The statement instance uses the same jointly inhabited code, environment and callee premises. -/
theorem indStmt_ok_zeuge [Kern] :
    Sim callLayout tiny 2 world Env.nil 0 0 4096 4 256 [] ⟨2048, 4096⟩ callMem 2144 2144 2144
      (execStmt O 1 (rufAt tiny O 1 2) (Stmt.callInd (l := false) pointer .nil (fit 2) rfl) world Env.nil) := by
  exact indStmt_ok (O := O) (passes := 1) (P := tiny) (f := 2) (σ0 := world) (ρ0 := Env.nil)
    (ex := (0, 0)) call_spec addresses_bound pointer .nil (fit 2) rfl (c := indirect) (top := 9)
    rfl (by decide) call_win call_pre.left (by decide) call_umf call_world (fun _ h => nomatch h)

/-- A concrete successful result binder: slot 4 becomes 21, and its continuation reaches the end. -/
theorem indBind_ok_zeuge [Kern] :
    Sim (l := false) callLayout tiny 2 world Env.nil 0 0 4096 4 256 [] ⟨2048, 4096⟩ callMem 2160 2160 2160
      (.ok world (Env.cons (τ := .int 0 100) (⟨21, by decide, by decide⟩ : Zahl 0 100) Env.nil)) := by
  have h := indBind_ok (τ := .int 0 100) (f := 2) (fp := 4096) (rp := 0) (cfp := 0) (ρ0 := Env.nil)
    (lo := 4) (K := 256) (Ks := 128) (pr := []) (cc := indirect) (cr := []) (tc := 9)
    call_spec addresses_bound pointer .nil rfl rfl world Env.nil rfl (by decide) call_pre
    call_win rfl (by decide) call_umf call_head call_world (fun _ h => nomatch h)
    (fun σ v => Ausgang.ok (V := vertragVon D 2) (l := false) σ (Env.cons v Env.nil)) .logik .hardware
    (fun t m out => Sim callLayout tiny 2 world Env.nil 0 0 4096 4 256 [] t m 2160 2160 2160 out)
    (Sim.prefix (by decide)) (fun _ _ _ h => h) (fun _ _ _ h => h)
    (fun m' σ' v hp' _ _ hw' =>
      ⟨m', Star.refl _ _, AgreeW.refl _ _ _ _ _, hp'.env, hw', Keeps.refl _ _ _⟩)
  exact h

/-- An unrepresentable address is refused instead of being truncated to an immediate. -/
theorem fnref_address_refused_zeuge :
    lowE { refLayout with fa := fun _ => 2 ^ 31 }
      (Expr.fnref (D := D) (Γ := []) (Λ := []) 0 0 (by decide)) 3 = none := by
  simp only [lowE_eqs]
  decide +kernel

end Gabbro.Stage0.Senke.FnptrProben
