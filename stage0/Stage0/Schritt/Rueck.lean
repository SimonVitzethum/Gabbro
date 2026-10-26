/-
  File:      stage0/Stage0/Schritt/Rueck.lean
  Subject:   The executable step, part 7: returns. A `return e` (or `return R::C`) at the head pops into the caller:
             a caller that does not wait goes on (`rueck`, `rueckCons`, `dannRet`), a caller waiting in
             `let x = g(…)` binds the value (`rueckBind`, `rueckConsBind`, `dannRetBind`), a caller waiting in
             `let … else` runs its `else` with the reason (`rueckGrund`, `rueckConsGrund`, `dannRetGrund`).
             The last frame does not pop: the thread has ended.
-/
import Stage0.Schritt.Grund

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration} (P : Programm D) (O : Orakel D) (passes : Nat)

/-- `return e` as the whole end block. -/
def zugRueckEnde (M : RufMaschineG D) (f : Faden) {lr : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (e : ErgExpr D Γ Λ (vertragVon D (M.faeden f).kopf.f).erg)
    (hperm : Λ.Perm (vertragVon D (M.faeden f).kopf.f).ende)
    (hk : (M.faeden f).kopf.rest = ⟨lr, Γ, Λ, ρ, .ende (.ret e hperm)⟩) : Option (Zug P O passes M f) :=
  if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
    let s1 := (M.weltVon f).lese Λ e.orte
    match hpop : (M.faeden f).stapel with
    | [] => none
    | caller :: rst =>
      if hnw : caller.wartend = false then
        some ⟨_, .rueck M f caller rst hpop Γ Λ e hperm ρ hk _ rfl _ rfl _ rfl (heldIn_of hΛ) s1 rfl _ rfl _
          (lese_neu M f Λ e.orte) hnw⟩
      else
        match hc : caller.rest with
        | ⟨l, Γc, Λc, ρc, .wartet (τ := τ) restb k⟩ =>
          if he : D.erg (M.faeden f).kopf.f = some τ then
            some ⟨_, .rueckBind M f caller rst hpop l Γc Λc _ τ restb k ρc (Or.inl hc) Γ Λ e hperm ρ hk _ rfl _ rfl
              _ rfl (heldIn_of hΛ) s1 rfl _ rfl he _ (lese_neu M f Λ e.orte)⟩
          else none
        | ⟨l, Γc, Λc, ρc, .wartetSonst (τ := τ) n err restb k⟩ =>
          if he : D.erg (M.faeden f).kopf.f = some τ then
            some ⟨_, .rueckBind M f caller rst hpop l Γc Λc _ τ restb k ρc (Or.inr ⟨n, err, hc⟩) Γ Λ e hperm ρ hk _
              rfl _ rfl _ rfl (heldIn_of hΛ) s1 rfl _ rfl he _ (lese_neu M f Λ e.orte)⟩
          else none
        | _ => none
  else none

/-- `return e` at the head of an end block. -/
def zugRueckConsEnde (M : RufMaschineG D) (f : Faden) {lr : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (e : ErgExpr D Γ Λ (vertragVon D (M.faeden f).kopf.f).erg)
    (hperm : Λ.Perm (vertragVon D (M.faeden f).kopf.f).ende)
    (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) lr Γ Λ)
    (hk : (M.faeden f).kopf.rest = ⟨lr, Γ, Λ, ρ, .ende (.cons (.ret e hperm) rest)⟩) :
    Option (Zug P O passes M f) :=
  if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
    let s1 := (M.weltVon f).lese Λ e.orte
    match hpop : (M.faeden f).stapel with
    | [] => none
    | caller :: rst =>
      if hnw : caller.wartend = false then
        some ⟨_, .rueckCons M f caller rst hpop Γ Λ e hperm rest ρ hk _ rfl _ rfl _ rfl (heldIn_of hΛ) s1 rfl _ rfl _
          (lese_neu M f Λ e.orte) hnw⟩
      else
        match hc : caller.rest with
        | ⟨l, Γc, Λc, ρc, .wartet (τ := τ) restb k⟩ =>
          if he : D.erg (M.faeden f).kopf.f = some τ then
            some ⟨_, .rueckConsBind M f lr Γ Λ e hperm rest ρ hk caller rst hpop l Γc Λc _ τ restb k ρc (Or.inl hc)
              (heldIn_of hΛ) s1 rfl _ rfl _ rfl _ rfl _ rfl he _ (lese_neu M f Λ e.orte)⟩
          else none
        | ⟨l, Γc, Λc, ρc, .wartetSonst (τ := τ) n err restb k⟩ =>
          if he : D.erg (M.faeden f).kopf.f = some τ then
            some ⟨_, .rueckConsBind M f lr Γ Λ e hperm rest ρ hk caller rst hpop l Γc Λc _ τ restb k ρc
              (Or.inr ⟨n, err, hc⟩) (heldIn_of hΛ) s1 rfl _ rfl _ rfl _ rfl _ rfl he _ (lese_neu M f Λ e.orte)⟩
          else none
        | _ => none
  else none

/-- `return e` at the head of a `dann` block. -/
def zugRetDann (M : RufMaschineG D) (f : Faden) {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)} (ρ : Env D Γ)
    (e : ErgExpr D Γ Λ (vertragVon D (M.faeden f).kopf.f).erg)
    (hperm : Λ.Perm (vertragVon D (M.faeden f).kopf.f).ende)
    (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
    (hk : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.ret e hperm) rest) k⟩) :
    Option (Zug P O passes M f) :=
  if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
    let s1 := (M.weltVon f).lese Λ e.orte
    match hpop : (M.faeden f).stapel with
    | [] => none
    | caller :: rst =>
      if hnw : caller.wartend = false then
        some ⟨_, .dannRet M f l Γ Λ Λ'' e hperm rest k ρ hk caller rst hpop (heldIn_of hΛ) s1 rfl _ rfl _ rfl _ rfl _
          rfl _ (lese_neu M f Λ e.orte) hnw⟩
      else
        match hc : caller.rest with
        | ⟨lc, Γc, Λc, ρc, .wartet (τ := τ) restb kc⟩ =>
          if he : D.erg (M.faeden f).kopf.f = some τ then
            some ⟨_, .dannRetBind M f l Γ Λ Λ'' e hperm rest k ρ hk caller rst hpop lc Γc Λc _ τ restb kc ρc
              (Or.inl hc) (heldIn_of hΛ) s1 rfl _ rfl _ rfl _ rfl _ rfl he _ (lese_neu M f Λ e.orte)⟩
          else none
        | ⟨lc, Γc, Λc, ρc, .wartetSonst (τ := τ) n err restb kc⟩ =>
          if he : D.erg (M.faeden f).kopf.f = some τ then
            some ⟨_, .dannRetBind M f l Γ Λ Λ'' e hperm rest k ρ hk caller rst hpop lc Γc Λc _ τ restb kc ρc
              (Or.inr ⟨n, err, hc⟩) (heldIn_of hΛ) s1 rfl _ rfl _ rfl _ rfl _ rfl he _ (lese_neu M f Λ e.orte)⟩
          else none
        | _ => none
  else none

/-! ## Reasons -/

/-- The caller of a `return R::C` waits in `let … else` with the callee's reason count. -/
def zugGrundAusAux (M : RufMaschineG D) (f : Faden) (caller : RufRahmenG D) :
    (x : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ) →
    caller.rest = x → Option (Σ' (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty) (n : Nat)
      (err : Endblock D (vertragVon D caller.f) l (.why n :: Γ) Λ)
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ') (k : GRest D (vertragVon D caller.f) l Γ Λ')
      (ρc : Env D Γ), caller.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩ ∧
        D.gruende (M.faeden f).kopf.f = n)
  | ⟨l, Γ, Λ, ρc, .wartetSonst (Λ' := Λ') (τ := τ) n err restb k⟩, hc =>
    if hn : D.gruende (M.faeden f).kopf.f = n then some ⟨l, Γ, Λ, Λ', τ, n, err, restb, k, ρc, hc, hn⟩ else none
  | _, _ => none

def zugGrundAus (M : RufMaschineG D) (f : Faden) (caller : RufRahmenG D) : Option (Σ' (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty) (n : Nat)
      (err : Endblock D (vertragVon D caller.f) l (.why n :: Γ) Λ)
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ') (k : GRest D (vertragVon D caller.f) l Γ Λ')
      (ρc : Env D Γ), caller.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩ ∧
        D.gruende (M.faeden f).kopf.f = n) :=
  zugGrundAusAux M f caller caller.rest rfl

/-- `return R::C` as the whole end block. -/
def zugGrundEnde (M : RufMaschineG D) (f : Faden) {lk : Bool} {Γk : Ctx} {Λk : List (Res D)} (ρ : Env D Γk)
    (r : Fin (vertragVon D (M.faeden f).kopf.f).gruende)
    (hperm : Λk.Perm (vertragVon D (M.faeden f).kopf.f).ende)
    (hk : (M.faeden f).kopf.rest = ⟨lk, Γk, Λk, ρ, .ende (.retWhy r hperm)⟩) : Option (Zug P O passes M f) :=
  if hΛ : heldInB Λk (offen (M.faeden f).spur) = true then
    match hpop : (M.faeden f).stapel with
    | [] => none
    | caller :: rst =>
      match zugGrundAus M f caller with
      | some ⟨l, Γ, Λ, Λ', τ, n, err, restb, k, ρc, hc, hn⟩ =>
        some ⟨_, .rueckGrund M f r hperm ρ hk caller rst hpop l Γ Λ Λ' τ n err restb k ρc hc (heldIn_of hΛ) _ rfl _ rfl
          _ rfl _ rfl hn⟩
      | none => none
  else none

/-- `return R::C` at the head of an end block. -/
def zugGrundConsEnde (M : RufMaschineG D) (f : Faden) {lk : Bool} {Γk : Ctx} {Λk : List (Res D)} (ρ : Env D Γk)
    (r : Fin (vertragVon D (M.faeden f).kopf.f).gruende)
    (hperm : Λk.Perm (vertragVon D (M.faeden f).kopf.f).ende)
    (restk : Endblock D (vertragVon D (M.faeden f).kopf.f) lk Γk Λk)
    (hk : (M.faeden f).kopf.rest = ⟨lk, Γk, Λk, ρ, .ende (.cons (.retWhy r hperm) restk)⟩) :
    Option (Zug P O passes M f) :=
  if hΛ : heldInB Λk (offen (M.faeden f).spur) = true then
    match hpop : (M.faeden f).stapel with
    | [] => none
    | caller :: rst =>
      match zugGrundAus M f caller with
      | some ⟨l, Γ, Λ, Λ', τ, n, err, restb, k, ρc, hc, hn⟩ =>
        some ⟨_, .rueckConsGrund M f r hperm restk ρ hk caller rst hpop l Γ Λ Λ' τ n err restb k ρc hc (heldIn_of hΛ)
          _ rfl _ rfl _ rfl _ rfl hn⟩
      | none => none
  else none

/-- `return R::C` at the head of a `dann` block. -/
def zugGrundDann (M : RufMaschineG D) (f : Faden) {lk : Bool} {Γk : Ctx} {Λk Λk'' : List (Res D)} (ρ : Env D Γk)
    (r : Fin (vertragVon D (M.faeden f).kopf.f).gruende)
    (hperm : Λk.Perm (vertragVon D (M.faeden f).kopf.f).ende)
    (restk : Block D (vertragVon D (M.faeden f).kopf.f) lk Γk Λk Λk'')
    (kk : GRest D (vertragVon D (M.faeden f).kopf.f) lk Γk Λk'')
    (hk : (M.faeden f).kopf.rest = ⟨lk, Γk, Λk, ρ, .dann (.cons (.retWhy r hperm) restk) kk⟩) :
    Option (Zug P O passes M f) :=
  if hΛ : heldInB Λk (offen (M.faeden f).spur) = true then
    match hpop : (M.faeden f).stapel with
    | [] => none
    | caller :: rst =>
      match zugGrundAus M f caller with
      | some ⟨l, Γ, Λ, Λ', τ, n, err, restb, k, ρc, hc, hn⟩ =>
        some ⟨_, .dannRetGrund M f r hperm restk kk ρ hk caller rst hpop l Γ Λ Λ' τ n err restb k ρc hc
          (heldIn_of hΛ) _ rfl _ rfl _ rfl _ rfl hn⟩
      | none => none
  else none

end Gabbro.Stage0
