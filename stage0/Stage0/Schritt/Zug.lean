/-
  File:      stage0/Stage0/Schritt/Zug.lean
  Subject:   **The executable step of the thread machine.** `zug` looks at the head residue of thread `f` and takes
             the one rule of `RufSchrittG` that applies, returning the successor WITH that rule: every step stage 0
             takes is a step of the model's thread machine (`zug_schritt`). `none` means the thread does not step
             now: it has ended (a return from its last frame), it waits for a lock another thread holds, or the
             machine stops (a failed invariant, a broken device promise, a foreign call without an answer, a form
             the machine has no rule for).
-/
import Stage0.Schritt.Dann
import Stage0.Schritt.Abbruch
import Stage0.Schritt.Rest
import Stage0.Schritt.Ruf
import Stage0.Schritt.Rueck
import Stage0.Schritt.Geraet

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration} (P : Programm D) (O : Orakel D) (passes : Nat)

/-- A head residue `.ende e`. -/
def zugEnde (hO : OrakelSpurTreu O)
    (ow : ∀ a : D.Ax, World D → Env D (D.aparams a) → List (Schreib D)) (hsw : OrakelSchreibt O ow) (M : RufMaschineG D) (f : Faden) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (ρ : Env D Γ) (e : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
    (hk : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .ende e⟩) : Option (Zug P O passes M f) :=
  match e, hk with
  | .ret x hperm, hk => zugRueckEnde P O passes M f ρ x hperm hk
  | .retWhy r hperm, hk => zugGrundEnde P O passes M f ρ r hperm hk
  | .cons (.ret x hperm) rest, hk => zugRueckConsEnde P O passes M f ρ x hperm rest hk
  | .cons (.retWhy r hperm) rest, hk => zugGrundConsEnde P O passes M f ρ r hperm rest hk
  | .cons (.call g args hp hr) rest, hk => zugRufEnde P O passes M f ρ g args hp hr rest hk
  | .cons (.callInd (n := n) p args hp hr) rest, hk => zugRufIndEnde P O passes M f ρ n p args hp hr rest hk
  | .cons s rest, hk =>
    if hent : GEntfaltbar s = true then some ⟨_, .endeEntf M f l Γ Λ _ s rest ρ hent hk, [], rfl⟩
    else zugBlattEnde P O passes hO ow hsw M f ρ s rest hk
  | .bind x rest, hk => zugEndeBind P O passes M f ρ x rest hk
  | .bindAxiom a args he hw hg hd hgd rest, hk => zugEndeAx P O passes hO ow hsw M f ρ a args he hw hg hd hgd rest hk
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, hk =>
    zugEndeAxSonst P O passes hO ow hsw M f ρ a args he hr hw hg hd hgd err rest hk
  | e, hk =>
    if hl : l = false then
      if hent : EndEntfaltbar e = true then some ⟨_, .endeForm M f l Γ Λ e ρ hl hent hk, [], rfl⟩ else none
    else none

/-- A head residue `.dann b k`. -/
def zugDannVoll (hO : OrakelSpurTreu O)
    (ow : ∀ a : D.Ax, World D → Env D (D.aparams a) → List (Schreib D)) (hsw : OrakelSchreibt O ow) (M : RufMaschineG D) (f : Faden) (aktiv : List Faden)
    (hruhe : ∀ g, g ∉ aktiv → offen (M.faeden g).spur = []) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (ρ : Env D Γ) (b : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
    (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
    (hk : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann b k⟩) : Option (Zug P O passes M f) :=
  match b, hk with
  | .cons (.ret x hperm) rest, hk => zugRetDann P O passes M f ρ x hperm rest k hk
  | .cons (.retWhy r hperm) rest, hk => zugGrundDann P O passes M f ρ r hperm rest k hk
  | .cons (.call g args hp hr) rest, hk => zugRufDann P O passes M f ρ g args hp hr rest k hk
  | .cons (.callInd (n := n) p args hp hr) rest, hk => zugRufIndDann P O passes M f ρ n p args hp hr rest k hk
  | .cons (.leave h) rest, hk => by cases h; exact zugLeave P O passes M f ρ rfl rest k hk
  | .cons (.next h) rest, hk => by cases h; exact zugNext P O passes M f ρ rfl rest k hk
  | .cons s rest, hk =>
    if s.istBlatt = true then zugBlattDann P O passes hO ow hsw M f ρ s rest k hk
    else zugDannCons P O passes M f aktiv hruhe ρ s rest k hk
  | .bindCall g args he hp hr rest, hk => zugBindRuf P O passes M f ρ g args he hp hr rest k hk
  | .bindCallInd (n := n) p args he hp hr rest, hk => zugBindRufInd P O passes M f ρ n p args he hp hr rest k hk
  | .bindCallElse g args he hp hr err rest, hk => zugBindRufSonst P O passes M f ρ g args he hp hr err rest k hk
  | .bindAxiom .., hk | .bindAxiomElse .., hk | .regRead .., hk | .regReadElse .., hk | .awaits .., hk
  | .exchange .., hk | .float .., hk | .floatLit .., hk | .floatOf .., hk | .floatNarrow .., hk =>
    zugDannGeraet P O passes hO ow hsw M f ρ _ k hk
  | b, hk => zugDann P O passes M f aktiv hruhe ρ b k hk

/-- **The step of thread `f`**: the successor with its rule, or `none`. `aktiv` are the threads that have run; every
    other thread holds no lock (`hruhe`). -/
def zug (hO : OrakelSpurTreu O)
    (ow : ∀ a : D.Ax, World D → Env D (D.aparams a) → List (Schreib D)) (hsw : OrakelSchreibt O ow) (M : RufMaschineG D) (f : Faden) (aktiv : List Faden)
    (hruhe : ∀ g, g ∉ aktiv → offen (M.faeden g).spur = []) : Option (Zug P O passes M f) :=
  match hk : (M.faeden f).kopf.rest with
  | ⟨_, _, _, ρ, .ende e⟩ => zugEnde P O passes hO ow hsw M f ρ e hk
  | ⟨_, _, _, ρ, .dann b k⟩ => zugDannVoll P O passes hO ow hsw M f aktiv hruhe ρ b k hk
  | ⟨_, _, _, ρ, r⟩ => zugRest P O passes M f ρ r hk

/-- **Every step stage 0 takes is a step of the thread machine.** -/
theorem zug_schritt {hO : OrakelSpurTreu O} {ow : ∀ a : D.Ax, World D → Env D (D.aparams a) → List (Schreib D)}
    {hsw : OrakelSchreibt O ow} {M : RufMaschineG D} {f : Faden} {aktiv : List Faden}
    {hruhe : ∀ g, g ∉ aktiv → offen (M.faeden g).spur = []} {z : Zug P O passes M f}
    (_ : zug P O passes hO ow hsw M f aktiv hruhe = some z) : RufSchrittG P O passes M f z.M' :=
  z.schritt

end Gabbro.Stage0
