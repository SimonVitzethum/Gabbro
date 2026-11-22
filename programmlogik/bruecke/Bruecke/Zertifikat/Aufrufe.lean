module
public import Bruecke.Zertifikat.Regeln
public import Bruecke.Zertifikat.Programm
public import Bruecke.Zertifikat.Vertrag
import all Grammatik.Speichermodell.Atomar.AtomarSem.Teil1
@[expose] public section

/-!
# Exact weakest-precondition rules for calls and branches at the end of a body

The model's calculus (`Logik/WP/HA/Kern.lean`) states the call rule for blocks (`wpBA_bindCall`).
These are the same rules for end blocks (`Endblock.bindCall`, `Endblock.bindCallElse`), for the
fallible call in a block (`Block.bindCallElse`), and the branch of an end block (`Endblock.ite`),
read off `execEndHA`/`execBlockHA`. Each is an equivalence over the callee's outcome, which stays
the handler's `R f σ args`: what the callee returns is not assumed, it is split on.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.WP Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {D : Deklaration} {V : Vertrag D}

section HA

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (A : AUmwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {l : Bool} {Γ : Ctx}

/-- What remains of an end block after the call's outcome. -/
def bindRufEA {Λ' : List (Res D)} {τ : Ty} {f : D.Fn} (he : D.erg f = some τ) (hr : D.gruende f = 0)
    (rest : Endblock D V l (τ :: Γ) Λ') (Q : EndAusgang V l Γ → Prop) (ρ : Env D Γ) : RufAusgang f → Prop
  | .ok σ' v => wpEA S O U A passes R rest (fun o => Q o.schrumpf) σ' (.cons (ergWert he v) ρ)
  | .why _ r => keinGrund hr r
  | .logik e => Q (.logik e)
  | .hardware e => Q (.hardware e)

theorem wpEA_bindCall {Λ : List (Res D)} {τ : Ty} (f : D.Fn) (args : Args D Γ Λ (D.params f))
    (he : D.erg f = some τ) (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0)
    (rest : Endblock D V l (τ :: Γ) (nach D f Λ)) (Q : EndAusgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpEA S O U A passes R (.bindCall f args he hp hr rest) Q σ ρ ↔
      bindRufEA S O U A passes R he hr rest Q ρ
        (R f (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)) := by
  unfold wpEA
  simp only [execEndHA]
  cases R f (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) with
  | ok σ' v => rfl
  | why _ r => exact (Fin.cast hr r).elim0
  | logik e => rfl
  | hardware e => rfl

/-- What remains of an end block after a fallible call's outcome. -/
def bindRufSonstEA {Λ' : List (Res D)} {τ : Ty} {f : D.Fn} (he : D.erg f = some τ)
    (err : Endblock D V l (.why (D.gruende f) :: Γ) Λ') (rest : Endblock D V l (τ :: Γ) Λ')
    (Q : EndAusgang V l Γ → Prop) (ρ : Env D Γ) : RufAusgang f → Prop
  | .ok σ' v => wpEA S O U A passes R rest (fun o => Q o.schrumpf) σ' (.cons (ergWert he v) ρ)
  | .why σ' r => wpEA S O U A passes R err (fun o => Q o.schrumpf) σ' (.cons r ρ)
  | .logik e => Q (.logik e)
  | .hardware e => Q (.hardware e)

theorem wpEA_bindCallElse {Λ : List (Res D)} {τ : Ty} (f : D.Fn) (args : Args D Γ Λ (D.params f))
    (he : D.erg f = some τ) (hp : RufPasst D V (D.signatur f) Λ) (hr : 0 < D.gruende f)
    (err : Endblock D V l (.why (D.gruende f) :: Γ) (nach D f Λ)) (rest : Endblock D V l (τ :: Γ) (nach D f Λ))
    (Q : EndAusgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpEA S O U A passes R (.bindCallElse f args he hp hr err rest) Q σ ρ ↔
      bindRufSonstEA S O U A passes R he err rest Q ρ
        (R f (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)) := by
  unfold wpEA
  simp only [execEndHA]
  cases R f (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) <;> rfl

/-- What remains of a block after a fallible call's outcome. -/
def bindRufSonstBA {Λ' Λ'' : List (Res D)} {τ : Ty} {f : D.Fn} (he : D.erg f = some τ)
    (err : Endblock D V l (.why (D.gruende f) :: Γ) Λ') (rest : Block D V l (τ :: Γ) Λ' Λ'')
    (Q : Ausgang V l Γ → Prop) (ρ : Env D Γ) : RufAusgang f → Prop
  | .ok σ' v => wpBA S O U A passes R rest (fun o => Q o.schrumpf) σ' (.cons (ergWert he v) ρ)
  | .why σ' r => wpEA S O U A passes R err (fun o => Q o.schrumpf.zuAusgang) σ' (.cons r ρ)
  | .logik e => Q (.logik e)
  | .hardware e => Q (.hardware e)

theorem wpBA_bindCallElse {Λ Λ' : List (Res D)} {τ : Ty} (f : D.Fn) (args : Args D Γ Λ (D.params f))
    (he : D.erg f = some τ) (hp : RufPasst D V (D.signatur f) Λ) (hr : 0 < D.gruende f)
    (err : Endblock D V l (.why (D.gruende f) :: Γ) (nach D f Λ)) (rest : Block D V l (τ :: Γ) (nach D f Λ) Λ')
    (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpBA S O U A passes R (.bindCallElse f args he hp hr err rest) Q σ ρ ↔
      bindRufSonstBA S O U A passes R he err rest Q ρ
        (R f (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)) := by
  unfold wpBA
  simp only [execBlockHA]
  cases R f (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) <;> rfl

theorem wpEA_ite {Λ : List (Res D)} (c : Expr D Γ Λ .bool) (t e : Endblock D V l Γ Λ) (Q : EndAusgang V l Γ → Prop)
    (σ : World D) (ρ : Env D Γ) :
    wpEA S O U A passes R (.ite c t e) Q σ ρ ↔
      if wahr? (eval (leseA A σ Λ c.orte) c (leseA A σ Λ c.orte) ρ) then
        wpEA S O U A passes R t Q (leseA A σ Λ c.orte) ρ
      else wpEA S O U A passes R e Q (leseA A σ Λ c.orte) ρ := by
  unfold wpEA
  simp only [execEndHA]
  rw [apply_ite Q]

/-- What follows a foreign call statement, by the oracle's answer. -/
def axRufSA (a : D.Ax) {β : Type} (Q : Ausgang V l Γ → Prop) (ρ : Env D Γ) : World D × Option β → Prop
  | (σ', Option.some _) => Q (.ok σ' ρ)
  | (_, Option.none) => Q (.hardware (.annahme a))

theorem wpSA_axiomCall {Λ : List (Res D)} (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ) (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpSA S O U A passes R (.axiomCall a args h hw hg hd hgd) Q σ ρ ↔
      axRufSA a Q ρ (axiomAntwort O a (leseA A σ Λ args.orte)
        (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)) := by
  unfold wpSA
  simp only [execStmtHA]
  rcases axiomAntwort O a (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)
    with ⟨σ', _ | _⟩ <;> rfl

/-- What follows a foreign call binding in a block, by the oracle's answer. -/
def axBindBA {a : D.Ax} {τ : Ty} {Λ' Λ'' : List (Res D)} (he : D.aerg a = some τ)
    (rest : Block D V l (τ :: Γ) Λ' Λ'') (Q : Ausgang V l Γ → Prop) (ρ : Env D Γ) :
    World D × Option (ErgVal D (D.aerg a)) → Prop
  | (σ', Option.some v) => wpBA S O U A passes R rest (fun o => Q o.schrumpf) σ' (.cons (ergWert he v) ρ)
  | (_, Option.none) => Q (.hardware (.annahme a))

theorem wpBA_bindAxiom {Λ Λ' : List (Res D)} {τ : Ty} (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (he : D.aerg a = some τ) (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ) (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Block D V l (τ :: Γ) Λ Λ') (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpBA S O U A passes R (.bindAxiom a args he hw hg hd hgd rest) Q σ ρ ↔
      axBindBA S O U A passes R he rest Q ρ (axiomAntwort O a (leseA A σ Λ args.orte)
        (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)) := by
  unfold wpBA
  simp only [execBlockHA]
  rcases axiomAntwort O a (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)
    with ⟨σ', _ | _⟩ <;> rfl

/-- What follows a foreign call binding at the end of a body, by the oracle's answer. -/
def axBindEA {a : D.Ax} {τ : Ty} {Λ' : List (Res D)} (he : D.aerg a = some τ)
    (rest : Endblock D V l (τ :: Γ) Λ') (Q : EndAusgang V l Γ → Prop) (ρ : Env D Γ) :
    World D × Option (ErgVal D (D.aerg a)) → Prop
  | (σ', Option.some v) => wpEA S O U A passes R rest (fun o => Q o.schrumpf) σ' (.cons (ergWert he v) ρ)
  | (_, Option.none) => Q (.hardware (.annahme a))

theorem wpEA_bindAxiom {Λ : List (Res D)} {τ : Ty} (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (he : D.aerg a = some τ) (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ) (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Endblock D V l (τ :: Γ) Λ) (Q : EndAusgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpEA S O U A passes R (.bindAxiom a args he hw hg hd hgd rest) Q σ ρ ↔
      axBindEA S O U A passes R he rest Q ρ (axiomAntwort O a (leseA A σ Λ args.orte)
        (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)) := by
  unfold wpEA
  simp only [execEndHA]
  rcases axiomAntwort O a (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)
    with ⟨σ', _ | _⟩ <;> rfl

end HA


/-! ## Splitting on the callee's outcome -/

/-- **The two kinds of an oracle's answer**, each with the equation that names it. -/
theorem antwort_faelle {D : Deklaration} {β : Type} {G : World D × Option β → Prop} (x : World D × Option β)
    (hja : ∀ σ' v, x = (σ', Option.some v) → G (σ', Option.some v))
    (hnein : ∀ σ', x = (σ', Option.none) → G (σ', Option.none)) : G x := by
  rcases x with ⟨σ', _ | v⟩
  · exact hnein σ' rfl
  · exact hja σ' v rfl

/-- **The four outcomes of a call**, each with the equation that names it. -/
theorem ruf_faelle {D : Deklaration} {f : D.Fn} {G : RufAusgang f → Prop} (x : RufAusgang f)
    (hok : ∀ σ' v, x = .ok σ' v → G (.ok σ' v)) (hwhy : ∀ σ' r, x = .why σ' r → G (.why σ' r))
    (hlog : ∀ e, x = .logik e → G (.logik e)) (hhw : ∀ e, x = .hardware e → G (.hardware e)) : G x := by
  cases x with
  | ok σ' v => exact hok σ' v rfl
  | why σ' r => exact hwhy σ' r rfl
  | logik e => exact hlog e rfl
  | hardware e => exact hhw e rfl

/-- **A branch on a condition the kernel does not decide**: both branches, each under its condition. -/
theorem ite_faelle {α : Sort _} {G : α → Prop} (c : Prop) [Decidable c] (a b : α) (ha : c → G a) (hb : ¬c → G b) :
    G (if c then a else b) := by
  by_cases h : c
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h

/-- The gated call at a function of the program: its precondition is that of its own lowering. -/
theorem torRuf_von {u : UProg} {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (h : lowerAllg u = .ok (P, fs)) (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (g : Fin u.fns.length) (σ : World (declOf u)) (ρ : Env (declOf u) ((declOf u).params g)) :
    torRuf P R g σ ρ =
      if wahr? (eval σ (if (fnAt u g).needs = [] then Expr.tru else (lowerAtPair u g (lower_ok h g)).2.2) σ ρ) = true
      then R g σ ρ else RufAusgang.logik (Logik.vorbedingung g) := by
  unfold torRuf
  rw [requires_eq h g]

/-- The gated call at any reading `X` of the callee's precondition. -/
theorem torRuf_gleich {D : Deklaration} {P : Programm D} {g : D.Fn} {X : Expr D (D.params g) _ .bool}
    (hreq : P.requires g = X) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D (D.params g)) :
    torRuf P R g σ ρ = if wahr? (eval σ X σ ρ) = true then R g σ ρ else RufAusgang.logik (Logik.vorbedingung g) := by
  unfold torRuf
  rw [hreq]

/-- A handler without `logik` outcomes never answers `logik`. -/
theorem logik_ohne {D : Deklaration} {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    (hR : OhneLogik R) {g : D.Fn} {σ : World D} {ρ : Env D (D.params g)} {e : Logik D}
    (hx : R g σ ρ = .logik e) {G : Prop} : G :=
  absurd hx (hR g σ ρ e)

/-- A handler that never blames a caller: its `logik` outcome is no precondition stop. -/
theorem logik_nicht_vor {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    (hR : OhneVorbedingung R) {g : D.Fn} {σ : World D} {ρ : Env D (D.params g)} {e : Logik D}
    (hx : R g σ ρ = .logik e) : ∀ g' : D.Fn, (EndAusgang.logik e : EndAusgang V l Γ) ≠ .logik (.vorbedingung g') :=
  fun g' h => hR g σ ρ e hx g' (by cases h; rfl)

theorem rueckPost_logik {D : Deklaration} (P : Programm D) (f : D.Fn) (σ : World D) (ρ : Env D (D.params f))
    (e : Logik D) : RueckPost P f σ ρ (.logik e) ↔ True :=
  ⟨fun _ => trivial, fun _ => ⟨fun _ _ h => (by cases h), fun _ _ h => (by cases h)⟩⟩

theorem rueckPost_hardware {D : Deklaration} (P : Programm D) (f : D.Fn) (σ : World D) (ρ : Env D (D.params f))
    (e : Hardware D) : RueckPost P f σ ρ (.hardware e) ↔ True :=
  ⟨fun _ => trivial, fun _ => ⟨fun _ _ h => (by cases h), fun _ _ h => (by cases h)⟩⟩

end Gabbro.Bruecke
