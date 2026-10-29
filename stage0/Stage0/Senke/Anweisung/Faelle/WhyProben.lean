/-
  Subject: Joint witnesses of normal and reason call premises, including false ensures on reason paths.
-/
import Stage0.Senke.Ausdruck.FnptrAufrufProben
import Stage0.Senke.Anweisung.Faelle.CallElse

namespace Gabbro.Stage0.Senke.WhyProbe
open Gabbro.Grammatik Runner.IR Runner.Mem
open FnptrProben (allFin)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

local instance (m : Runner.Mem) (pc : Runner.W) (o : Nat) (a b c : BitVec 32) :
    Decidable (InsAt m pc o a b c) :=
  if h : m.rd8 pc = some (BitVec.ofNat 8 o) ∧ m.rd32 (pc + 4) = some a ∧
      m.rd32 (pc + 8) = some b ∧ m.rd32 (pc + 12) = some c then
    .isTrue ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  else .isFalse (fun h' => h ⟨h'.op, h'.f1, h'.f2, h'.f3⟩)

def D : Deklaration := { FnptrProben.D with
  sigNr := fun _ => { FnptrProben.D.sigNr 0 with gruende := 3 }
  passt_ok := fun _ _ _ => SigPasst.refl _ _ }

instance (n : Nat) : OfNat D.Fn n := inferInstanceAs (OfNat (Fin 3) n)

def P : Programm D where
  invariante i := nomatch i
  requires _ := .tru
  ensures f := if f.val < 2 then .fls else .tru
  rumpf f := if h : f.val < 2 then .retWhy ⟨f.val + 1, by change f.val + 1 < 3; omega⟩ List.Perm.nil
    else .ret (.val (.widen (by decide) (by decide) (.lit 42))) List.Perm.nil

def O : Orakel D where
  wirkt a := nomatch a
  regLies r := nomatch r
  regSchreib r := nomatch r
  sichtbar _ _ := true

def world : World D where
  slots t := nomatch t
  globs _ := ⟨0, by decide⟩
  spur := []

def addresses (f : D.Fn) : Nat := 64 + 512 * f.val

def callLayout : Lay D where
  col t := nomatch t
  ga _ := 8192
  lo := 8192
  hi := 8200
  tor a := nomatch a
  byte t := nomatch t
  sye := 8200
  fa := addresses
  sb := 4096
  st := 2048

def target (f : D.Fn) : List II := ((lowFun P addresses callLayout f).getD ([], 0)).1

def caller (f : D.Fn) : List II :=
  elseC 9 4 (callC addresses f 4 []) [ci 1 5 11 0] [ci 1 5 22 0]

def callMem (f : D.Fn) : Runner.Mem :=
  let segments := [(64, (target 0).flatMap encII), (576, (target 1).flatMap encII),
    (1088, (target 2).flatMap encII), (2048, (caller f).flatMap encII)]
  let base : Runner.Mem := {
    b := fun a => match segments.find? (fun s => s.1 ≤ a.toNat && a.toNat < s.1 + s.2.length) with
      | some s => (s.2[a.toNat - s.1]?).getD 0
      | none => 0
    rd := fun _ => true
    wr := fun _ => true }
  write (write base 8192 8 64) 4112 8 3

theorem target_lower : ∀ f : Fin 3, lowFun P addresses callLayout f = some (target f, 13) := by
  exact @allFin 3 (fun f => lowFun P addresses callLayout f = some (target f, 13))
    (fun _ => inferInstance) (by first | decide +kernel | (revert g; apply allFin; decide +kernel))

theorem targets_code (g : D.Fn) : PCode (callMem g) addresses target 4096 256 := by
  have h : (List.finRange 3).all (fun f => (List.finRange (target f).length).all (fun k =>
      decide (InsAt (callMem g) (BitVec.ofNat 64 (addresses f) + BitVec.ofNat 64 (16 * k.val))
        (target f)[k.val].o (II.f (target f)[k.val].a) (II.f (target f)[k.val].b) (II.f (target f)[k.val].c)))) = true := by
    first | decide +kernel | (revert g; apply allFin; decide +kernel)
  have hf : ∀ f : Fin 3, CodeFar (BitVec.ofNat 64 (addresses f)) (target f).length 4096 256 := by
    unfold CodeFar
    apply allFin
    first | decide +kernel | (revert g; apply allFin; decide +kernel)
  change ∀ f : Fin 3, CodeAt (callMem g) (BitVec.ofNat 64 (addresses f)) (target f) ∧
    CodeFar (BitVec.ofNat 64 (addresses f)) (target f).length 4096 256
  refine fun f => ⟨fun k hk => ?_, hf f⟩
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h f (by simp)) ⟨k, hk⟩ (by simp))

theorem caller_code (g : D.Fn) : CodeAt (callMem g) 2048 (caller g) := by
  have h : ∀ k : Fin (caller g).length, InsAt (callMem g) (2048 + BitVec.ofNat 64 (16 * k.val))
      (caller g)[k.val].o (II.f (caller g)[k.val].a) (II.f (caller g)[k.val].b) (II.f (caller g)[k.val].c) := by
    apply allFin
    first | decide +kernel | (revert g; apply allFin; decide +kernel)
  exact fun k hk => h ⟨k, hk⟩

theorem call_frame (g : D.Fn) : FrameOK (callMem g) 4096 256 := ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩

theorem call_pre [Kern] (g : D.Fn) : PreS callLayout (callMem g) 2048 4096 256 4 (caller g) (Env.nil : Env D []) := by
  refine ⟨by decide, by decide, call_frame g, caller_code g, ?_, ?_, trivial, wstab_true _ _⟩
  · unfold CodeFar; first | decide +kernel | (revert g; apply allFin; decide +kernel)
  · intro _ x; nomatch x

theorem call_world (g : D.Fn) : WeltAt (callMem g) callLayout world := by
  refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
  cases g
  first | decide +kernel | (revert g; apply allFin; decide +kernel)

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

theorem call_sync (g : D.Fn) : SyncOK (callMem g) callLayout 4096 128 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    (fun l => nomatch l), by decide, (fun l => nomatch l), (fun l => nomatch l), (fun l => nomatch l)⟩

theorem call_umf [Kern] (g : D.Fn) : Umf callLayout addresses target 2 (callMem g) 4096 128 256 :=
  ⟨targets_code g, by first | decide +kernel | (revert g; apply allFin; decide +kernel), by decide, call_sync g, by decide⟩

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
  first | decide +kernel | (revert g; apply allFin; decide +kernel)

theorem call_spec [Kern] : FunSpec callLayout addresses target (rufAt P O 1 2) 2 39 := by
  exact lowFun_spec (P := P) (O := O) (passes := 1) (L := 13) rfl
    (fun f => ⟨13, target_lower f, Nat.le_refl _⟩)
    addresses_bound
    (fun f => target_bound f) 2 (by decide)


/-- Both reason callees and the successful callee are live, and G bypasses false ensures on reasons. -/
theorem outcomes_zeuge :
    (match rufAt P O 1 2 0 world .nil with | .why _ r => r.val | _ => 99) = 1 ∧
    (match rufAt P O 1 2 1 world .nil with | .why _ r => r.val | _ => 99) = 2 ∧
    (match rufAt P O 1 2 2 world .nil with | .ok _ v => v.n | _ => -1) = 42 := by
  decide +kernel

/-- The selected continuation has the encoded binding and the resulting world. -/
def Arrived [Kern] (g : D.Fn) : Prop :=
  match rufAt P O 1 2 g world .nil with
  | .ok σ v => ∃ m', Star ⟨2048, 4096⟩ (callMem g) ⟨2144, 4096⟩ m' ∧
      PreS callLayout m' 2144 4096 256 5 [ci 1 5 11 0]
        (Env.cons (τ := .int 0 100) v .nil) ∧ WeltAt m' callLayout σ
  | .why σ r => ∃ m', Star ⟨2048, 4096⟩ (callMem g) ⟨2176, 4096⟩ m' ∧
      PreS callLayout m' 2176 4096 256 5 [ci 1 5 22 0]
        (Env.cons (τ := .why 3) r .nil) ∧ WeltAt m' callLayout σ
  | _ => False

/-- All premises of the shared call simulation hold jointly for each of three distinct outcomes. -/
theorem callElse_ok_zeuge [Kern] (g : D.Fn) :
    FunSpec callLayout addresses target (rufAt P O 1 2) 2 39 ∧
    lowA callLayout (Γ := []) (Λ := []) (Args.nil : Args D [] [] (D.params g)) 6 = some ([], 6) ∧
    PreS callLayout (callMem g) 2048 4096 256 4 (caller g) (Env.nil : Env D []) ∧
    Umf callLayout addresses target 2 (callMem g) 4096 128 256 ∧
    WIn callLayout 4096 128 256 ∧ WeltAt (callMem g) callLayout world ∧ Arrived g := by
  refine ⟨call_spec, rfl, call_pre g, call_umf g, call_win, call_world g, ?_⟩
  have hn : (match rufAt P O 1 2 g world .nil with | .logik _ | .hardware _ => false | _ => true) = true := by
    revert g
    apply allFin
    decide +kernel
  have h := callElse_ok (g := g) (ca := []) (ta := 8) call_spec (addresses_bound g)
    (Args.nil : Args D [] [] (D.params g)) rfl world rfl (by change 49 ≤ 128; decide) (call_pre g)
    (by change 144 < 2 ^ 31; decide) (call_umf g) call_win (call_world g)
  rcases h with ⟨σ, v, m', hr, st, _, hp, hw⟩ | ⟨σ, r, m', hr, st, _, hp, hw⟩ |
    ⟨e, hr, _⟩ | ⟨e, hr, _⟩
  all_goals simp only [evalArgs] at hr
  · unfold Arrived
    rw [hr]
    exact ⟨m', st, hp, hw⟩
  · unfold Arrived
    rw [hr]
    exact ⟨m', st, hp, hw⟩
  · rw [hr] at hn; cases hn
  · rw [hr] at hn; cases hn

end Gabbro.Stage0.Senke.WhyProbe
