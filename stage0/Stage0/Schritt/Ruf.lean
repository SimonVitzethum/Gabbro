/-
  File:      stage0/Stage0/Schritt/Ruf.lean
  Subject:   The executable step, part 6: calls (direct and through a pointer, plain and bound) and returns (a
             value or a reason, from the three head positions, into a caller that waits or does not).
             A return from the last frame does not step: the thread has ended.
-/
import Stage0.Schritt.Grund

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration} (P : Programm D) (O : Orakel D) (passes : Nat)

/-! ## Calls -/

/-- `g(args);` at the head of a `dann` block. -/
def zugRufDann (M : RufMaschineG D) (f : Faden) {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)} (ρ : Env D Γ)
    (g : D.Fn) (args : Args D Γ Λ (D.params g))
    (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ (nach D g Λ) Λ'')
    (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
    (hk : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.call g args hp hr) rest) k⟩) :
    Option (Zug P O passes M f) :=
  if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
    some ⟨_, .rufDann M f l Γ Λ Λ Λ'' g args hp hr rest k ρ hk (heldIn_of hΛ) _ rfl _ rfl _
      (lese_neu M f Λ args.orte)⟩
  else none

/-- `g(args);` at the head of an end block. -/
def zugRufEnde (M : RufMaschineG D) (f : Faden) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (g : D.Fn) (args : Args D Γ Λ (D.params g))
    (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ (nach D g Λ))
    (hk : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.cons (.call g args hp hr) rest)⟩) :
    Option (Zug P O passes M f) :=
  if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
    some ⟨_, .ruf M f l Γ Λ g args hp hr rest ρ hk (heldIn_of hΛ) _ rfl _ rfl _ (lese_neu M f Λ args.orte)⟩
  else none

/-- `p(args);` through a pointer, at the head of a `dann` block. -/
def zugRufIndDann (M : RufMaschineG D) (f : Faden) {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)} (ρ : Env D Γ)
    (n : Nat) (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0)
    (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ (nachSig D (D.sigNr n) Λ) Λ'')
    (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
    (hk : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.callInd p args hp hr) rest) k⟩) :
    Option (Zug P O passes M f) :=
  if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
    let s0 := (M.weltVon f).lese Λ (p.orte ++ args.orte)
    match hv : eval s0 p s0 ρ with
    | ⟨g, hg⟩ =>
      some ⟨_, .dannCallInd M f l Γ Λ Λ Λ'' n p args hp hr rest k ρ hk (heldIn_of hΛ) s0 rfl g hg hv _ rfl _
        (lese_neu M f Λ (p.orte ++ args.orte))⟩
  else none

/-- `p(args);` through a pointer, at the head of an end block. -/
def zugRufIndEnde (M : RufMaschineG D) (f : Faden) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (n : Nat) (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0)
    (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ (nachSig D (D.sigNr n) Λ))
    (hk : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.cons (.callInd p args hp hr) rest)⟩) :
    Option (Zug P O passes M f) :=
  if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
    let s0 := (M.weltVon f).lese Λ (p.orte ++ args.orte)
    match hv : eval s0 p s0 ρ with
    | ⟨g, hg⟩ =>
      some ⟨_, .rufCallInd M f l Γ Λ n p args hp hr rest ρ hk (heldIn_of hΛ) s0 rfl g hg hv _ rfl _
        (lese_neu M f Λ (p.orte ++ args.orte))⟩
  else none

/-- `let x = g(args);` -- the caller waits for the value. -/
def zugBindRuf (M : RufMaschineG D) (f : Faden) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (ρ : Env D Γ) (g : D.Fn) (args : Args D Γ Λ (D.params g)) (he : D.erg g = some τ)
    (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) (nach D g Λ) Λ')
    (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
    (hk : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.bindCall g args he hp hr rest) k⟩) :
    Option (Zug P O passes M f) :=
  if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
    some ⟨_, .dannBindCall M f l Γ Λ Λ' Λ' τ g args he hp hr rest k ρ hk (heldIn_of hΛ) _ rfl _ rfl _
      (lese_neu M f Λ args.orte)⟩
  else none

/-- `let x = p(args);` through a pointer. -/
def zugBindRufInd (M : RufMaschineG D) (f : Faden) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (ρ : Env D Γ) (n : Nat) (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (he : (D.sigNr n).erg = some τ)
    (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0)
    (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) (nachSig D (D.sigNr n) Λ) Λ')
    (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
    (hk : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.bindCallInd p args he hp hr rest) k⟩) :
    Option (Zug P O passes M f) :=
  if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
    let s0 := (M.weltVon f).lese Λ (p.orte ++ args.orte)
    match hv : eval s0 p s0 ρ with
    | ⟨g, hg⟩ =>
      some ⟨_, .dannBindCallInd M f l Γ Λ Λ' Λ' τ n p args he hp hr rest k ρ hk (heldIn_of hΛ) s0 rfl g hg hv _
        rfl _ (lese_neu M f Λ (p.orte ++ args.orte))⟩
  else none

/-- `let x = g(args) else (e) { … }` -- the caller waits for a value or a reason. -/
def zugBindRufSonst (M : RufMaschineG D) (f : Faden) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (ρ : Env D Γ) (g : D.Fn) (args : Args D Γ Λ (D.params g)) (he : D.erg g = some τ)
    (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.signatur g) Λ) (hr : 0 < D.gruende g)
    (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l (.why (D.gruende g) :: Γ) (nach D g Λ))
    (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) (nach D g Λ) Λ')
    (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
    (hk : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.bindCallElse g args he hp hr err rest) k⟩) :
    Option (Zug P O passes M f) :=
  if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
    some ⟨_, .dannBindCallElse M f l Γ Λ Λ' Λ' τ g args he hp hr err rest k ρ hk (heldIn_of hΛ) _ rfl _ rfl _
      (lese_neu M f Λ args.orte)⟩
  else none

end Gabbro.Stage0
