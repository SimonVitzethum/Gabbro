import Grammatik.Logik.WP.HA.Pflicht

/-!
# The certificate: every logic duty of a program, each by name

GabbroV proves no logic: it turns a Gabbro program into a Lean certificate that states ALL the logic the program's
user owes and ALL the hardware it assumes; the user proves the logic. This file fixes what a complete certificate lists,
so that nothing is lumped and nothing is missing:

* per function `f`, at every budget, three duties (`PflichtRueck`, `PflichtKeineVor`, `PflichtKeinHalt`) -- the returns
  meet `ensures` and the owed invariants, a reason exit meets the owed invariants, no precondition stop under the gated
  call meaning, no `logik` stop under a call meaning without `logik`;
* per lock `L`, that its invariant reads only its protected carriers (`SperrLokalAn`) and holds at the declared
  initial memory (`SperrAmStart`);
* per foreign body `a`, that its declared `ensures` reads only its declared write carriers (`AxLokalAn`);
* per declared start, that its `requires` holds at the initial memory with its declared arguments (`StartAmStart`).

`LogikPflichten E` collects them; `logikPflichten_iff` proves that they are EXACTLY premise (b) of the goal theorem
(`NutzerPflichtA E`). The hardware assumptions stay what the goal theorem names (`HardwareAnnahmen O E.Q`: the frame of
every foreign body, register locality, and every gate's declared contract `E.Q a`); the certificate prints each gate's
contract with its name.
-/

namespace Gabbro.Grammatik.WP

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

variable {D : Deklaration}

/-- Duty 1 of a function: from `requires`, a return meets `ensures` and the owed invariants, a reason exit meets the
    owed invariants -- in every environment of the obligation's classes. -/
def PflichtRueck (P : Programm D) (passes : Nat) (Q : AxEns D) (S : SperrInv D) (T : D.Tab ⊕ D.Glob → Prop)
    (f : D.Fn) : Prop :=
  ∀ O' : Orakel D, RahmenO O' → RegLokal O' → AxVertragO Q O' →
    ∀ U : Umwelt D, HavocOk S U → ∀ A : AUmwelt D, HavocA T A →
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
      RespektiertRahmen P R → OhneVorbedingung R →
      ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ →
        wpEA (V := vertragVon D f) S O' U A passes R (P.rumpf f) (RueckPost P f σ ρ) σ ρ

/-- Duty 2 of a function: under the gated call meaning the body ends in no precondition stop (the caller duty). -/
def PflichtKeineVor (P : Programm D) (passes : Nat) (Q : AxEns D) (S : SperrInv D) (T : D.Tab ⊕ D.Glob → Prop)
    (f : D.Fn) : Prop :=
  ∀ O' : Orakel D, RahmenO O' → RegLokal O' → AxVertragO Q O' →
    ∀ U : Umwelt D, HavocOk S U → ∀ A : AUmwelt D, HavocA T A →
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
      RespektiertRahmen P R → OhneVorbedingung R →
      ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ →
        wpEA (V := vertragVon D f) S O' U A passes (torRuf P R) (P.rumpf f)
          (fun eo => ∀ g, eo ≠ .logik (.vorbedingung g)) σ ρ

/-- Duty 3 of a function: under a call meaning without `logik` the body ends in no `logik` stop at all. -/
def PflichtKeinHalt (P : Programm D) (passes : Nat) (Q : AxEns D) (S : SperrInv D) (T : D.Tab ⊕ D.Glob → Prop)
    (f : D.Fn) : Prop :=
  ∀ O' : Orakel D, RahmenO O' → RegLokal O' → AxVertragO Q O' →
    ∀ U : Umwelt D, HavocOk S U → ∀ A : AUmwelt D, HavocA T A →
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
      RespektiertRahmen P R → OhneLogik R →
      ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ →
        wpEA (V := vertragVon D f) S O' U A passes R (P.rumpf f) (fun eo => ∀ e, eo ≠ .logik e) σ ρ

/-- The three duties are `PflichtWP`. -/
theorem pflichtWP_iff_drei {P : Programm D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
    {T : D.Tab ⊕ D.Glob → Prop} {f : D.Fn} :
    PflichtWP P passes Q S T f ↔
      PflichtRueck P passes Q S T f ∧ PflichtKeineVor P passes Q S T f ∧ PflichtKeinHalt P passes Q S T f := by
  constructor
  · intro h
    exact ⟨fun O' h1 h2 h3 U hU A hA R hR hOV σ ρ hreq => (h.1 O' h1 h2 h3 U hU A hA R hR hOV σ ρ hreq).1,
      fun O' h1 h2 h3 U hU A hA R hR hOV σ ρ hreq => (h.1 O' h1 h2 h3 U hU A hA R hR hOV σ ρ hreq).2, h.2⟩
  · intro ⟨h1, h2, h3⟩
    exact ⟨fun O' a b c U hU A hA R hR hOV σ ρ hreq =>
      ⟨h1 O' a b c U hU A hA R hR hOV σ ρ hreq, h2 O' a b c U hU A hA R hR hOV σ ρ hreq⟩, h3⟩

/-- A lock's invariant reads only its protected carriers. -/
def SperrLokalAn (S : SperrInv D) (L : D.Lock) : Prop :=
  ∀ s s' : Speicher D, (∀ c ∈ S.orte L, TraegerGleich s s' c) → S.inv L s = S.inv L s'

/-- A foreign body's declared `ensures` reads only its declared write carriers. -/
def AxLokalAn (Q : AxEns D) (a : D.Ax) : Prop :=
  ∀ (σ σ' : World D) (v : ErgVal D (D.aerg a)),
    (∀ t, D.aschreibt a t = true → σ.slots t = σ'.slots t) →
    (∀ g, D.agschreibt a g = true → σ.globs g = σ'.globs g) → Q a σ v = Q a σ' v

/-- A lock's invariant holds at the declared initial memory. -/
def SperrAmStart (E : Einheit D) (L : D.Lock) : Prop := E.S.inv L E.sp0 = true

/-- A declared start's `requires` holds at the initial memory with its declared arguments. -/
def StartAmStart (E : Einheit D) (a : Σ w : D.Fn, Env D (D.params w)) : Prop :=
  ReqAmEintritt E.P a.1 (E.sp0.welt []) a.2

/-- **Every logic duty of a unit, each by name.** -/
structure LogikPflichten [DecidableEq D.Fn] (E : Einheit D) : Prop where
  rueck : ∀ f passes, PflichtRueck E.P passes E.Q E.S (GeteiltA E.P E.ws) f
  keineVor : ∀ f passes, PflichtKeineVor E.P passes E.Q E.S (GeteiltA E.P E.ws) f
  keinHalt : ∀ f passes, PflichtKeinHalt E.P passes E.Q E.S (GeteiltA E.P E.ws) f
  sperrLokal : ∀ L, SperrLokalAn E.S L
  axLokal : ∀ a, AxLokalAn E.Q a
  sperrStart : ∀ L, SperrAmStart E L
  startReq : ∀ a ∈ E.starts ++ E.gestartet, StartAmStart E a

/-- **The named duties are exactly premise (b) of the goal theorem**: nothing is missing, nothing is added. -/
theorem logikPflichten_iff [DecidableEq D.Fn] (E : Einheit D) : LogikPflichten E ↔ NutzerPflichtA E := by
  rw [nutzerPflichtA_iff]
  constructor
  · intro h
    exact ⟨fun passes f => pflichtWP_iff_drei.2 ⟨h.rueck f passes, h.keineVor f passes, h.keinHalt f passes⟩,
      fun L => h.sperrLokal L, fun a => h.axLokal a, ⟨h.sperrStart, h.startReq⟩⟩
  · intro ⟨h, hS, hQ, hStart⟩
    exact ⟨fun f passes => (pflichtWP_iff_drei.1 (h passes f)).1, fun f passes => (pflichtWP_iff_drei.1 (h passes f)).2.1,
      fun f passes => (pflichtWP_iff_drei.1 (h passes f)).2.2, hS, hQ, hStart.sperren, hStart.req⟩

end Gabbro.Grammatik.WP
