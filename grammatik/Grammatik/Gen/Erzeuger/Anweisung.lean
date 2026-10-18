/-
  File:      Grammatik/Gen/Erzeuger/Anweisung.lean
  Subject:   The clauses of the STATEMENT generator, one per constructor of `Stmt`. A clause takes the fuel `m`
             (the expressions are `genExpr m`), the recursion record `R` (the statements, blocks and end blocks
             of the fuel below) and the context, and returns the statements it builds with the resources held
             after them. Every proof argument is DECIDED (`if h : P then ... else []`), so a generated
             statement carries the rule's own premise as a proof.
-/
import Grammatik.Gen.Erzeuger.Hilfen

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D] {V : Vertrag D}

section Klauseln

variable (m : Nat) (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D))

def sAssignSlot : List (SS D V l Γ Λ) :=
  Aufz.tab.flatMap fun t => (Aufz.feld t).flatMap fun f =>
    (ofTy (genExpr m Γ Λ) (.index (D.count t))).flatMap fun i =>
      (ofTy (genExpr m Γ Λ) (D.typ t f)).flatMap fun e =>
        if hw : V.schreibt t = true then if hL : darf D t Λ then [⟨Λ, .assignSlot t f i e hw hL⟩] else [] else []

def sAssignThru : List (SS D V l Γ Λ) :=
  mitPtrT (genExpr m Γ Λ) fun {n} q => Aufz.tab.flatMap fun t => if ht : D.tabNr n = some t then
    (Aufz.feld t).flatMap fun f => (ofTy (genExpr m Γ Λ) (.index (D.count t))).flatMap fun i =>
      (ofTy (genExpr m Γ Λ) (D.typ t f)).flatMap fun e =>
        if hw : V.schreibt t = true then if hL : darf D t Λ then
          [⟨Λ, .assignThru q t ht f i e hw hL⟩] else [] else []
    else []

def sAssignGlob : List (SS D V l Γ Λ) :=
  Aufz.glob.flatMap fun g => (ofTy (genExpr m Γ Λ) (D.gtyp g)).flatMap fun e =>
    if hw : V.gschreibt g = true then if hL : gdarf D g Λ then [⟨Λ, .assignGlob g e hw hL⟩] else [] else []

def sPutBytes : List (SS D V l Γ Λ) :=
  Aufz.tab.flatMap fun t => (Aufz.feld t).flatMap fun f =>
    if hf : D.typ t f = .int 0 255 then (List.range (m + 1)).flatMap fun (n : Nat) =>
      mitIntR (genExpr m Γ Λ) fun {lo hi} i => if hlo : 0 ≤ lo then if hhi : hi + (n : Int) ≤ D.count t then
        (ofTy (genExpr m Γ Λ) (.int 0 (256 ^ n - 1))).flatMap fun e =>
          if hw : V.schreibt t = true then if hL : darf D t Λ then
            [⟨Λ, .putBytes t f hf n i hlo hhi e hw hL⟩] else [] else []
        else [] else []
    else []

def sAssignVar : List (SS D V l Γ Λ) :=
  (genVar Γ).flatMap fun p => (ofTy (genExpr m Γ Λ) p.1).map fun e => ⟨Λ, .assignVar p.2 e⟩

def sShift : List (SS D V l Γ Λ) :=
  Aufz.tab.flatMap fun t => (Aufz.feld t).flatMap fun f =>
    mitTypInt (D.typ t f) fun {lo hi} hτ =>
      (ofTy (genExpr m Γ Λ) (.index (D.count t))).flatMap fun i =>
        (ints m).flatMap fun von => (ints m).flatMap fun nach =>
          if hn : lo ≤ nach ∧ nach ≤ hi then if he : D.erlaubt t f von nach = true then
            if hw : V.schreibt t = true then if hL : darf D t Λ then
              [⟨Λ, .shift t f hτ i von nach hn he hw hL⟩] else [] else [] else [] else []

def sIte : List (SS D V l Γ Λ) :=
  (ofTy (genExpr m Γ Λ) .bool).flatMap fun c => (R.bl l Γ Λ).flatMap fun p =>
    (ofTy (R.bl l Γ Λ) p.1).map fun e => ⟨p.1, .ite c p.2 e⟩

def sOnOption : List (SS D V l Γ Λ) :=
  mitOptR (genExpr m Γ Λ) fun {n} o => (R.bl l (.index n :: Γ) Λ).flatMap fun p =>
    (ofTy (R.bl l Γ Λ) p.1).map fun a => ⟨p.1, .onOption o p.2 a⟩

def sOnTag : List (SS D V l Γ Λ) :=
  mitSumR (genExpr m Γ Λ) fun {cs} v => (genArms R l Γ Λ cs).map fun p => ⟨p.1, .onTag v p.2⟩

def sOnWhy : List (SS D V l Γ Λ) :=
  mitWhyR (genExpr m Γ Λ) fun {n} r => (genGrundArms R l Γ Λ n).map fun p => ⟨p.1, .onWhy r p.2⟩

def sCall : List (SS D V l Γ Λ) :=
  Aufz.fn.flatMap fun f => (genArgs (genExpr m Γ Λ) (D.params f)).flatMap fun args =>
    if hp : RufPasst D V (D.signatur f) Λ then if hr : D.gruende f = 0 then
      [⟨nach D f Λ, .call f args hp hr⟩] else [] else []

def sCallInd : List (SS D V l Γ Λ) :=
  mitFnptrR (genExpr m Γ Λ) fun {n} p => (genArgs (genExpr m Γ Λ) (D.sigNr n).params).flatMap fun args =>
    if hp : RufPasst D V (D.sigNr n) Λ then if hr : (D.sigNr n).gruende = 0 then
      [⟨nachSig D (D.sigNr n) Λ, .callInd p args hp hr⟩] else [] else []

def sLocks : List (SS D V l Γ Λ) :=
  Aufz.lock.flatMap fun L =>
    if hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L then
      (ofTy (R.bl l Γ (.held L :: Λ)) (.held L :: Λ)).map fun body => ⟨Λ, .locks L hr body⟩
    else []

def sBreaking : List (SS D V l Γ Λ) :=
  Aufz.inv.flatMap fun i => (R.bl l Γ Λ).map fun p => ⟨p.1, .breaking i p.2⟩

def sTraverse : List (SS D V l Γ Λ) :=
  Aufz.tab.flatMap fun t => (ofTy (genExpr m Γ Λ) .bool).flatMap fun inv =>
    (ofTy (R.bl true (.index (D.count t) :: Γ) Λ) Λ).map fun body => ⟨Λ, .traverse t inv body⟩

def sRetry : List (SS D V l Γ Λ) :=
  (List.range (m + 1)).flatMap fun (n : Nat) => (ofTy (genExpr m Γ Λ) .bool).flatMap fun bis =>
    (ofTy (R.bl true Γ Λ) Λ).flatMap fun body => (ofTy (R.bl l Γ Λ) Λ).map fun ueb =>
      ⟨Λ, .retry n bis body ueb⟩

def sForever : List (SS D V l Γ Λ) :=
  Aufz.annahme.flatMap fun a => (ofTy (genExpr m Γ Λ) .bool).flatMap fun inv =>
    (ofTy (R.bl true Γ Λ) Λ).map fun body => ⟨Λ, .forever a inv body⟩

def sAxiomCall : List (SS D V l Γ Λ) :=
  Aufz.ax.flatMap fun a => (genArgs (genExpr m Γ Λ) (D.aparams a)).flatMap fun args =>
    if h : D.aerg a = none then
      if hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true then
      if hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true then
      if hd : ∀ t, D.aschreibt a t = true → darf D t Λ then
      if hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ then
        [⟨Λ, .axiomCall a args h hw hg hd hgd⟩] else [] else [] else [] else []
    else []

def sRegWrite : List (SS D V l Γ Λ) :=
  Aufz.reg.flatMap fun r => (ofTy (genExpr m Γ Λ) (D.rtyp r)).flatMap fun e =>
    if hk : (D.rklasse r).schreibbar = true then [⟨Λ, .regWrite r hk e⟩] else []

def sTransition : List (SS D V l Γ Λ) :=
  Aufz.reg.flatMap fun r => Aufz.reg.flatMap fun m' =>
    if hk : (D.rklasse r).schreibbar = true then if hm : D.spiegel r = some m' then
      if hl : (D.rklasse m').lesbar = true then
        (ints m).flatMap fun maske => (ints m).map fun bits =>
          ⟨Λ, .transition r hk m' hm hl maske bits⟩
      else [] else [] else []

def sPublish : List (SS D V l Γ Λ) :=
  Aufz.glob.flatMap fun g => (ofTy (genExpr m Γ Λ) (D.gtyp g)).flatMap fun e =>
    if hw : V.gschreibt g = true then if hL : gdarf D g Λ then
      [⟨Λ, .publish g e (D.nutzlast g) rfl hw hL⟩] else [] else []

def sAdvances : List (SS D V l Γ Λ) :=
  Λ.flatMap fun r => match r with
    | .marke mk a => if h : Res.marke mk a ∈ Λ then if hs : a + 1 < D.stufen mk then
        [⟨Λ.erase (.marke mk a) ++ [.marke mk (a + 1)], .advances mk a h hs⟩] else [] else []
    | .held _ => []

def sRetires : List (SS D V l Γ Λ) :=
  Λ.flatMap fun r => match r with
    | .marke mk s => if h : Res.marke mk s ∈ Λ then
        Aufz.annahme.map fun a => ⟨Λ.erase (.marke mk s), .retires mk s h a⟩ else []
    | .held _ => []

def sRet : List (SS D V l Γ Λ) :=
  (genErg (genExpr m Γ Λ) V.erg).flatMap fun e =>
    if hΛ : Λ.Perm V.ende then [⟨Λ, .ret e hΛ⟩] else []

def sRetWhy : List (SS D V l Γ Λ) :=
  (List.finRange V.gruende).flatMap fun r => if hΛ : Λ.Perm V.ende then [⟨Λ, .retWhy r hΛ⟩] else []

def sLeave : List (SS D V l Γ Λ) := if h : l = true then [⟨Λ, .leave h⟩] else []

def sNext : List (SS D V l Γ Λ) := if h : l = true then [⟨Λ, .next h⟩] else []

/-- The statements of fuel `m + 1`. -/
def stmtS : List (SS D V l Γ Λ) :=
  sAssignSlot m l Γ Λ ++ sAssignThru m l Γ Λ ++ sAssignGlob m l Γ Λ ++ sPutBytes m l Γ Λ ++ sAssignVar m l Γ Λ ++
  sShift m l Γ Λ ++ sIte m R l Γ Λ ++ sOnOption m R l Γ Λ ++ sOnTag m R l Γ Λ ++ sOnWhy m R l Γ Λ ++
  sCall m l Γ Λ ++ sCallInd m l Γ Λ ++ sLocks R l Γ Λ ++ sBreaking R l Γ Λ ++ sTraverse m R l Γ Λ ++
  sRetry m R l Γ Λ ++ sForever m R l Γ Λ ++ sAxiomCall m l Γ Λ ++ sRegWrite m l Γ Λ ++ sTransition m l Γ Λ ++
  sPublish m l Γ Λ ++ sAdvances l Γ Λ ++ sRetires l Γ Λ ++ sRet m l Γ Λ ++ sRetWhy l Γ Λ ++ sLeave l Γ Λ ++
  sNext l Γ Λ

end Klauseln

end Gabbro.Grammatik.Gen
