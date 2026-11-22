module
public import Bruecke.Zertifikat.Aufrufe
import all Grammatik.Speichermodell.Atomar.AtomarSem.Teil1
import all Grammatik.Kern.Semantik.Semantik.T2.Teil1
@[expose] public section

/-!
# Exact weakest-precondition rules for further forms

Scoped returns, `exchange`, fallible foreign calls and calls through a function pointer, read off
`execStmtHA`/`execBlockHA`/`execEndHA`. Each rule is an equivalence; a callee's or an oracle's
outcome stays symbolic and is split on by the proof support.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.WP

variable {D : Deklaration} {V : Vertrag D}

section HA

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (A : AUmwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {l : Bool} {Γ : Ctx}

theorem wpSA_retScoped {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (c : RueckRessourcen D V Λ)
    (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpSA S O U A passes R (.retScoped e c) Q σ ρ ↔
      if scopesInvH S c.scopes (leseA A σ Λ e.orte) = true then
        Q (.zurueck (c.scopes.foldl World.gibt (leseA A σ Λ e.orte))
          (evalErg (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ))
      else Q (.logik .schleife) := by
  unfold wpSA
  simp only [execStmtHA]
  split <;> rfl

theorem wpSA_retWhyScoped {Λ : List (Res D)} (r : Fin V.gruende) (c : RueckRessourcen D V Λ)
    (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpSA S O U A passes R (.retWhyScoped r c) Q σ ρ ↔
      if scopesInvH S c.scopes σ = true then Q (.why (c.scopes.foldl World.gibt σ) r)
      else Q (.logik .schleife) := by
  unfold wpSA
  simp only [execStmtHA]
  split <;> rfl

theorem wpEA_retScoped {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (c : RueckRessourcen D V Λ)
    (Q : EndAusgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpEA S O U A passes R (.retScoped e c) Q σ ρ ↔
      if scopesInvH S c.scopes (leseA A σ Λ e.orte) = true then
        Q (.zurueck (c.scopes.foldl World.gibt (leseA A σ Λ e.orte))
          (evalErg (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ))
      else Q (.logik .schleife) := by
  unfold wpEA
  simp only [execEndHA]
  split <;> rfl

theorem wpEA_retWhyScoped {Λ : List (Res D)} (r : Fin V.gruende) (c : RueckRessourcen D V Λ)
    (Q : EndAusgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpEA S O U A passes R (.retWhyScoped r c) Q σ ρ ↔
      if scopesInvH S c.scopes σ = true then Q (.why (c.scopes.foldl World.gibt σ) r)
      else Q (.logik .schleife) := by
  unfold wpEA
  simp only [execEndHA]
  split <;> rfl

theorem wpBA_exchange {Λ Λ' : List (Res D)} (g : D.Glob) (neu : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g))
    (hw : V.gschreibt g = true) (hL : gdarf D g Λ) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
    (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpBA S O U A passes R (.exchange g neu hw hL rest) Q σ ρ ↔
      wpBA S O U A passes R rest (fun o => Q o.schrumpf)
        ((leseA A σ Λ (.inr g :: neu.orte)).schreibGlob g Λ
          (eval (leseA A σ Λ (.inr g :: neu.orte)) neu (leseA A σ Λ (.inr g :: neu.orte))
            (.cons ((leseA A σ Λ (.inr g :: neu.orte)).globs g) ρ)))
        (.cons ((leseA A σ Λ (.inr g :: neu.orte)).globs g) ρ) := by
  unfold wpBA
  simp only [execBlockHA]

theorem wpEA_exchange {Λ : List (Res D)} (g : D.Glob) (neu : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g))
    (hw : V.gschreibt g = true) (hL : gdarf D g Λ) (rest : Endblock D V l (D.gtyp g :: Γ) Λ)
    (Q : EndAusgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpEA S O U A passes R (.exchange g neu hw hL rest) Q σ ρ ↔
      wpEA S O U A passes R rest (fun o => Q o.schrumpf)
        ((leseA A σ Λ (.inr g :: neu.orte)).schreibGlob g Λ
          (eval (leseA A σ Λ (.inr g :: neu.orte)) neu (leseA A σ Λ (.inr g :: neu.orte))
            (.cons ((leseA A σ Λ (.inr g :: neu.orte)).globs g) ρ)))
        (.cons ((leseA A σ Λ (.inr g :: neu.orte)).globs g) ρ) := by
  unfold wpEA
  simp only [execEndHA]

theorem wpEA_awaits {Λ : List (Res D)} (g : D.Glob) (payload : List D.Glob) (hp : payload = D.nutzlast g)
    (hL : gdarf D g Λ) (ha : D.atomar g = true) (rest : Endblock D V l (D.gtyp g :: Γ) Λ)
    (Q : EndAusgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpEA S O U A passes R (.awaits g payload hp hL ha rest) Q σ ρ ↔
      if O.sichtbar g (leseA A (σ.fragt (.inr (.inr g))) Λ [.inr g]) = true then
        wpEA S O U A passes R rest (fun o => Q o.schrumpf) (leseA A (σ.fragt (.inr (.inr g))) Λ [.inr g])
          (.cons ((leseA A (σ.fragt (.inr (.inr g))) Λ [.inr g]).globs g) ρ)
      else Q (.hardware (.sichtbarkeit D.a10)) := by
  unfold wpEA
  simp only [execEndHA]
  split <;> rfl

theorem wpBA_awaits {Λ Λ' : List (Res D)} (g : D.Glob) (payload : List D.Glob) (hp : payload = D.nutzlast g)
    (hL : gdarf D g Λ) (ha : D.atomar g = true) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
    (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpBA S O U A passes R (.awaits g payload hp hL ha rest) Q σ ρ ↔
      if O.sichtbar g (leseA A (σ.fragt (.inr (.inr g))) Λ [.inr g]) = true then
        wpBA S O U A passes R rest (fun o => Q o.schrumpf) (leseA A (σ.fragt (.inr (.inr g))) Λ [.inr g])
          (.cons ((leseA A (σ.fragt (.inr (.inr g))) Λ [.inr g]).globs g) ρ)
      else Q (.hardware (.sichtbarkeit D.a10)) := by
  unfold wpBA
  simp only [execBlockHA]
  split <;> rfl

/-- What follows a fallible foreign binding at the end of a body, by the oracle's answer. -/
def axSonstEA {a : D.Ax} {τ : Ty} {Λ' : List (Res D)} (he : D.aerg a = some τ)
    (err : Endblock D V l (.why (D.agruende a) :: Γ) Λ') (rest : Endblock D V l (τ :: Γ) Λ')
    (Q : EndAusgang V l Γ → Prop) (ρ : Env D Γ) :
    World D × Option (ErgVal D (D.aerg a) ⊕ Fin (D.agruende a)) → Prop
  | (σ', Option.some (Sum.inl v)) => wpEA S O U A passes R rest (fun o => Q o.schrumpf) σ' (.cons (ergWert he v) ρ)
  | (σ', Option.some (Sum.inr r)) => wpEA S O U A passes R err (fun o => Q o.schrumpf) σ' (.cons r ρ)
  | (_, Option.none) => Q (.hardware (.annahme a))

theorem wpEA_bindAxiomElse {Λ : List (Res D)} {τ : Ty} (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (he : D.aerg a = some τ) (hr : 0 < D.agruende a) (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ) (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (err : Endblock D V l (.why (D.agruende a) :: Γ) Λ) (rest : Endblock D V l (τ :: Γ) Λ)
    (Q : EndAusgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpEA S O U A passes R (.bindAxiomElse a args he hr hw hg hd hgd err rest) Q σ ρ ↔
      axSonstEA S O U A passes R he err rest Q ρ (axiomAntwortSonst O a (leseA A σ Λ args.orte)
        (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)) := by
  unfold wpEA
  simp only [execEndHA]
  rcases axiomAntwortSonst O a (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)
    with ⟨σ', _ | _ | _⟩ <;> rfl

/-- What follows a fallible foreign binding in a block, by the oracle's answer. -/
def axSonstBA {a : D.Ax} {τ : Ty} {Λ' Λ'' : List (Res D)} (he : D.aerg a = some τ)
    (err : Endblock D V l (.why (D.agruende a) :: Γ) Λ') (rest : Block D V l (τ :: Γ) Λ' Λ'')
    (Q : Ausgang V l Γ → Prop) (ρ : Env D Γ) :
    World D × Option (ErgVal D (D.aerg a) ⊕ Fin (D.agruende a)) → Prop
  | (σ', Option.some (Sum.inl v)) => wpBA S O U A passes R rest (fun o => Q o.schrumpf) σ' (.cons (ergWert he v) ρ)
  | (σ', Option.some (Sum.inr r)) =>
      wpEA S O U A passes R err (fun o => Q o.schrumpf.zuAusgang) σ' (.cons r ρ)
  | (_, Option.none) => Q (.hardware (.annahme a))

theorem wpBA_bindAxiomElse {Λ Λ' : List (Res D)} {τ : Ty} (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (he : D.aerg a = some τ) (hr : 0 < D.agruende a) (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ) (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (err : Endblock D V l (.why (D.agruende a) :: Γ) Λ) (rest : Block D V l (τ :: Γ) Λ Λ')
    (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpBA S O U A passes R (.bindAxiomElse a args he hr hw hg hd hgd err rest) Q σ ρ ↔
      axSonstBA S O U A passes R he err rest Q ρ (axiomAntwortSonst O a (leseA A σ Λ args.orte)
        (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)) := by
  unfold wpBA
  simp only [execBlockHA]
  rcases axiomAntwortSonst O a (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)
    with ⟨σ', _ | _ | _⟩ <;> rfl

/-- What follows an indirect call at the end of a body, by the callee's outcome. -/
def indRufEA {n : Nat} {τ : Ty} {Λ' : List (Res D)} {f : D.Fn} (hf : D.passt f n = true)
    (he : (D.sigNr n).erg = some τ) (hr : (D.sigNr n).gruende = 0) (rest : Endblock D V l (τ :: Γ) Λ')
    (Q : EndAusgang V l Γ → Prop) (ρ : Env D Γ) : RufAusgang f → Prop
  | .ok σ' v => wpEA S O U A passes R rest (fun o => Q o.schrumpf) σ' (.cons (ergWert (ergSig hf he) v) ρ)
  | .why _ r => keinGrundSig hf hr r
  | .logik e => Q (.logik e)
  | .hardware e => Q (.hardware e)

/-- An indirect call at the end of a body, by the pointer's value. -/
def indZielEA {n : Nat} {τ : Ty} {Λ Λ' : List (Res D)} (args : Args D Γ Λ (D.sigNr n).params)
    (he : (D.sigNr n).erg = some τ) (hr : (D.sigNr n).gruende = 0) (rest : Endblock D V l (τ :: Γ) Λ')
    (Q : EndAusgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) : Wert D (.fnptr n) → Prop
  | ⟨f, hf⟩ => indRufEA S O U A passes R hf he hr rest Q ρ (R f σ (umsig hf (evalArgs σ args σ ρ)))

theorem wpEA_bindCallInd {Λ : List (Res D)} {n : Nat} {τ : Ty} (p : Expr D Γ Λ (.fnptr n))
    (args : Args D Γ Λ (D.sigNr n).params) (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ)
    (hr : (D.sigNr n).gruende = 0) (rest : Endblock D V l (τ :: Γ) (nachSig D (D.sigNr n) Λ))
    (Q : EndAusgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpEA S O U A passes R (.bindCallInd p args he hp hr rest) Q σ ρ ↔
      indZielEA S O U A passes R args he hr rest Q (leseA A σ Λ (p.orte ++ args.orte)) ρ
        (eval (leseA A σ Λ (p.orte ++ args.orte)) p (leseA A σ Λ (p.orte ++ args.orte)) ρ) := by
  unfold wpEA
  simp only [execEndHA]
  rcases eval (leseA A σ Λ (p.orte ++ args.orte)) p (leseA A σ Λ (p.orte ++ args.orte)) ρ with ⟨f, hf⟩
  simp only [indZielEA]
  cases R f _ _ with
  | why _ r => exact keinGrundSig hf hr r
  | _ => rfl

end HA

/-- **The three kinds of a fallible oracle's answer**, each with the equation that names it. -/
theorem antwortSonst_faelle {D : Deklaration} {α β : Type} {G : World D × Option (α ⊕ β) → Prop}
    (x : World D × Option (α ⊕ β))
    (hja : ∀ σ' v, x = (σ', Option.some (Sum.inl v)) → G (σ', Option.some (Sum.inl v)))
    (hgrund : ∀ σ' r, x = (σ', Option.some (Sum.inr r)) → G (σ', Option.some (Sum.inr r)))
    (hnein : ∀ σ', x = (σ', Option.none) → G (σ', Option.none)) : G x := by
  rcases x with ⟨σ', _ | v | r⟩
  · exact hnein σ' rfl
  · exact hja σ' v rfl
  · exact hgrund σ' r rfl

end Gabbro.Bruecke
