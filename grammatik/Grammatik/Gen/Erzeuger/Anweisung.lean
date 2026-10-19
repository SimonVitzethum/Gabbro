/-
  File:      Grammatik/Gen/Erzeuger/Anweisung.lean
  Subject:   The CLAUSES of the statement generator, one per constructor of `Stmt`. A clause is a `Sz` (the statements
             of exact size `k`, each with the resources held after it): it reads the expressions of the sizes below
             `k` from `E`, the blocks of the context at hand from `Bs`, and the blocks of other contexts from the
             oracle `O`. Every proof argument of a rule is DECIDED (`Sz.wenn`), so a generated statement carries
             the rule's own premise as a proof.
-/
import Grammatik.Gen.Erzeuger.Hilfen

namespace Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D] [Zahlen] {V : Vertrag D}

section Klauseln

variable (O : Orakel V) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (E : Sz (SE D Γ Λ)) (Bs : Sz (SB D V l Γ Λ))

def sAssignSlot : Sz (SS D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.tab) fun t => Sz.bind (Sz.wahl (Aufz.feld t)) fun f =>
    Sz.bind (tyS E (.index (D.count t))) fun i => Sz.bind (tyS E (D.typ t f)) fun e =>
      Sz.wenn (V.schreibt t = true) fun hw => Sz.wenn (darf D t Λ) fun hL =>
        Sz.pure ⟨Λ, .assignSlot t f i e hw hL⟩)

def sAssignThru : Sz (SS D V l Γ Λ) :=
  Sz.knoten (Sz.bind (ptrTS E) fun ⟨n, q⟩ => Sz.bind (Sz.wahl Aufz.tab) fun t =>
    Sz.wenn (D.tabNr n = some t) fun ht => Sz.bind (Sz.wahl (Aufz.feld t)) fun f =>
      Sz.bind (tyS E (.index (D.count t))) fun i => Sz.bind (tyS E (D.typ t f)) fun e =>
        Sz.wenn (V.schreibt t = true) fun hw => Sz.wenn (darf D t Λ) fun hL =>
          Sz.pure ⟨Λ, .assignThru q t ht f i e hw hL⟩)

def sAssignGlob : Sz (SS D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.glob) fun g => Sz.bind (tyS E (D.gtyp g)) fun e =>
    Sz.wenn (V.gschreibt g = true) fun hw => Sz.wenn (gdarf D g Λ) fun hL => Sz.pure ⟨Λ, .assignGlob g e hw hL⟩)

def sPutBytes : Sz (SS D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.tab) fun t => Sz.bind (Sz.wahl (Aufz.feld t)) fun f =>
    Sz.wenn (D.typ t f = .int 0 255) fun hf => Sz.bind nS fun n =>
      Sz.bind (intS E) fun ⟨lo, hi, i⟩ => Sz.wenn (0 ≤ lo) fun hlo => Sz.wenn (hi + (n : Int) ≤ D.count t) fun hhi =>
        Sz.bind (tyS E (.int 0 (256 ^ n - 1))) fun e =>
          Sz.wenn (V.schreibt t = true) fun hw => Sz.wenn (darf D t Λ) fun hL =>
            Sz.pure ⟨Λ, .putBytes t f hf n i hlo hhi e hw hL⟩)

def sAssignVar : Sz (SS D V l Γ Λ) :=
  Sz.knoten (Sz.bind (varS Γ) fun p => Sz.bind (tyS E p.1) fun e => Sz.pure ⟨Λ, .assignVar p.2 e⟩)

def sShift : Sz (SS D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.tab) fun t => Sz.bind (Sz.wahl (Aufz.feld t)) fun f =>
    mitTypInt (D.typ t f) fun {lo hi} hτ => Sz.bind (tyS E (.index (D.count t))) fun i =>
      Sz.bind zS fun von => Sz.bind zS fun nach =>
        Sz.wenn (lo ≤ nach ∧ nach ≤ hi) fun hn => Sz.wenn (D.erlaubt t f von nach = true) fun he =>
          Sz.wenn (V.schreibt t = true) fun hw => Sz.wenn (darf D t Λ) fun hL =>
            Sz.pure ⟨Λ, .shift t f hτ i von nach hn he hw hL⟩)

def sIte : Sz (SS D V l Γ Λ) :=
  Sz.knoten (Sz.bind (tyS E .bool) fun c => Sz.bind Bs fun p =>
    Sz.bind (fun j => ofTy (Bs j) p.1) fun e => Sz.pure ⟨p.1, .ite c p.2 e⟩)

def sOnOption : Sz (SS D V l Γ Λ) :=
  Sz.knoten (Sz.bindS (fun i => (optS E i).filter fun p => Zahlen.bindOk (Ty.index p.1))
    (fun n m => O.bl l (.index n :: Γ) Λ m) fun _ o p =>
    Sz.bind (fun j => ofTy (Bs j) p.1) fun a => Sz.pure ⟨p.1, .onOption o p.2 a⟩)

def sOnTag : Sz (SS D V l Γ Λ) :=
  Sz.knoten (Sz.bindS (sumS E) (fun cs _ => armsS O l Γ Λ cs) fun _ v arms => Sz.pure ⟨arms.1, .onTag v arms.2⟩)

def sOnWhy : Sz (SS D V l Γ Λ) :=
  Sz.knoten (Sz.bindS (whyS E) (fun n _ => grundArmsS O l Γ Λ n) fun _ r arms => Sz.pure ⟨arms.1, .onWhy r arms.2⟩)

def sCall : Sz (SS D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.fn) fun f =>
    Sz.wenn (RufPasst D V (D.signatur f) Λ) fun hp => Sz.wenn (D.gruende f = 0) fun hr =>
      Sz.bind (argsS E (D.params f)) fun args => Sz.pure ⟨nach D f Λ, .call f args hp hr⟩)

def sCallInd : Sz (SS D V l Γ Λ) :=
  Sz.knoten (Sz.bind (fnptrS E) fun ⟨n, p⟩ =>
    Sz.wenn (RufPasst D V (D.sigNr n) Λ) fun hp => Sz.wenn ((D.sigNr n).gruende = 0) fun hr =>
      Sz.bind (argsS E (D.sigNr n).params) fun args => Sz.pure ⟨nachSig D (D.sigNr n) Λ, .callInd p args hp hr⟩)

def sLocks : Sz (SS D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.lock) fun L =>
    Sz.wenn (∀ M, Res.held M ∈ Λ → D.rang M < D.rang L) fun hr =>
      Sz.bindR (Sz.pure ()) (fun m j => ofTy (O.bl l Γ (.held L :: Λ) m j) (.held L :: Λ)) fun _ body =>
        Sz.pure ⟨Λ, .locks L hr body⟩)

def sBreaking : Sz (SS D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.inv) fun i => Sz.bind Bs fun p => Sz.pure ⟨p.1, .breaking i p.2⟩)

def sTraverse : Sz (SS D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.tab) fun t =>
    Sz.bindR (tyS E .bool) (fun m j => ofTy (O.bl true (.index (D.count t) :: Γ) Λ m j) Λ) fun inv body =>
      Sz.pure ⟨Λ, .traverse t inv body⟩)

def sRetry : Sz (SS D V l Γ Λ) :=
  Sz.knoten (Sz.bind nS fun n =>
    Sz.bindR (tyS E .bool) (fun m j => ofTy (O.bl true Γ Λ m j) Λ) fun bis body =>
      Sz.bind (fun j => ofTy (Bs j) Λ) fun ueb => Sz.pure ⟨Λ, .retry n bis body ueb⟩)

def sForever : Sz (SS D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.annahme) fun a =>
    Sz.bindR (tyS E .bool) (fun m j => ofTy (O.bl true Γ Λ m j) Λ) fun inv body =>
      Sz.pure ⟨Λ, .forever a inv body⟩)

def sAxiomCall : Sz (SS D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.ax) fun a =>
    Sz.wenn (D.aerg a = none) fun h =>
    Sz.wenn (∀ t, D.aschreibt a t = true → V.schreibt t = true) fun hw =>
    Sz.wenn (∀ g, D.agschreibt a g = true → V.gschreibt g = true) fun hg =>
    Sz.wenn (∀ t, D.aschreibt a t = true → darf D t Λ) fun hd =>
    Sz.wenn (∀ g, D.agschreibt a g = true → gdarf D g Λ) fun hgd =>
      Sz.bind (argsS E (D.aparams a)) fun args => Sz.pure ⟨Λ, .axiomCall a args h hw hg hd hgd⟩)

def sRegWrite : Sz (SS D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.reg) fun r =>
    Sz.wenn ((D.rklasse r).schreibbar = true) fun hk =>
      Sz.bind (tyS E (D.rtyp r)) fun e => Sz.pure ⟨Λ, .regWrite r hk e⟩)

def sTransition : Sz (SS D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.reg) fun r => Sz.bind (Sz.wahl Aufz.reg) fun m' =>
    Sz.wenn ((D.rklasse r).schreibbar = true) fun hk => Sz.wenn (D.spiegel r = some m') fun hm =>
      Sz.wenn ((D.rklasse m').lesbar = true) fun hl => Sz.bind zW fun maske => Sz.bind zW fun bits =>
        Sz.pure ⟨Λ, .transition r hk m' hm hl maske bits⟩)

def sPublish : Sz (SS D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.glob) fun g =>
    Sz.wenn (V.gschreibt g = true) fun hw => Sz.wenn (gdarf D g Λ) fun hL =>
      Sz.bind (tyS E (D.gtyp g)) fun e => Sz.pure ⟨Λ, .publish g e (D.nutzlast g) rfl hw hL⟩)

def sAdvances : Sz (SS D V l Γ Λ) :=
  Sz.blatt (Λ.flatMap fun r => match r with
    | .marke mk a => if h : Res.marke mk a ∈ Λ then if hs : a + 1 < D.stufen mk then
        [⟨Λ.erase (.marke mk a) ++ [.marke mk (a + 1)], .advances mk a h hs⟩] else [] else []
    | .held _ => [])

def sRetires : Sz (SS D V l Γ Λ) :=
  Sz.blatt (Λ.flatMap fun r => match r with
    | .marke mk s => if h : Res.marke mk s ∈ Λ then
        Aufz.annahme.map fun a => ⟨Λ.erase (.marke mk s), .retires mk s h a⟩ else []
    | .held _ => [])

def sRet : Sz (SS D V l Γ Λ) :=
  Sz.knoten (Sz.bind (ergS E V.erg) fun e => Sz.wenn (Λ.Perm V.ende) fun hΛ => Sz.pure ⟨Λ, .ret e hΛ⟩)

def sRetWhy : Sz (SS D V l Γ Λ) :=
  Sz.blatt ((List.finRange V.gruende).flatMap fun r => if hΛ : Λ.Perm V.ende then [⟨Λ, .retWhy r hΛ⟩] else [])

def sLeave : Sz (SS D V l Γ Λ) := Sz.blatt (if h : l = true then [⟨Λ, .leave h⟩] else [])

def sNext : Sz (SS D V l Γ Λ) := Sz.blatt (if h : l = true then [⟨Λ, .next h⟩] else [])

end Klauseln

/-- **The statements of exact size `k`**. -/
def stmtS {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (O : Orakel V) (E : Sz (SE D Γ Λ)) (Bs : Sz (SB D V l Γ Λ)) :
    Sz (SS D V l Γ Λ) :=
  Sz.alle [sAssignSlot E, sAssignThru E, sAssignGlob E, sPutBytes E, sAssignVar E, sShift E, sIte E Bs,
    sOnOption O E Bs, sOnTag O E, sOnWhy O E, sCall E, sCallInd E, sLocks O, sBreaking Bs, sTraverse O E,
    sRetry O E Bs, sForever O E, sAxiomCall E, sRegWrite E, sTransition, sPublish E, sAdvances, sRetires, sRet E,
    sRetWhy, sLeave, sNext]

end Gabbro.Grammatik.Gen
