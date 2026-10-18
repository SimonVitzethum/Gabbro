/-
  File:      Grammatik/Gen/Erzeuger/Block.lean
  Subject:   The clauses of the BLOCK and END-BLOCK generators, one per constructor of `Block` and `Endblock`.
             Same frame as `Anweisung.lean`: every clause takes the fuel, the recursion record and the context.
-/
import Grammatik.Gen.Erzeuger.Anweisung

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D] {V : Vertrag D}

/-- The pairs of integers `-m .. m` squared. -/
def paare (m : Nat) : List (Int × Int) := (ints m).flatMap fun a => (ints m).map fun b => (a, b)

theorem mem_paare {m : Nat} {p : Int × Int} (h1 : p.1.natAbs ≤ m) (h2 : p.2.natAbs ≤ m) : p ∈ paare m := by
  unfold paare
  exact List.mem_flatMap.2 ⟨p.1, mem_ints h1, List.mem_map.2 ⟨p.2, mem_ints h2, rfl⟩⟩

/-- The four float operations. -/
def gleitOps : List GleitOp := [.add, .sub, .mul, .div]

theorem mem_gleitOps (op : GleitOp) : op ∈ gleitOps := by cases op <;> simp [gleitOps]

def bNil (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (SB D V l Γ Λ) := [⟨Λ, .nil⟩]

def bCons (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (SB D V l Γ Λ) :=
  (R.st l Γ Λ).flatMap fun s => (R.bl l Γ s.1).map fun r => ⟨r.1, .cons s.2 r.2⟩

def bBind (m : Nat) (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (SB D V l Γ Λ) :=
  (genExpr m Γ Λ).flatMap fun p => (R.bl l (p.1 :: Γ) Λ).map fun r => ⟨r.1, .bind p.2 r.2⟩

def bBindCall (m : Nat) (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (SB D V l Γ Λ) :=
  Aufz.fn.flatMap fun f => (genArgs (genExpr m Γ Λ) (D.params f)).flatMap fun args =>
    mitSome (D.erg f) fun {τ} he =>
      if hp : RufPasst D V (D.signatur f) Λ then if hr : D.gruende f = 0 then
        (R.bl l (τ :: Γ) (nach D f Λ)).map fun r => ⟨r.1, .bindCall f args he hp hr r.2⟩
      else [] else []

def bBindCallInd (m : Nat) (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (SB D V l Γ Λ) :=
  mitFnptrR (genExpr m Γ Λ) fun {n} p => (genArgs (genExpr m Γ Λ) (D.sigNr n).params).flatMap fun args =>
    mitSome (D.sigNr n).erg fun {τ} he =>
      if hp : RufPasst D V (D.sigNr n) Λ then if hr : (D.sigNr n).gruende = 0 then
        (R.bl l (τ :: Γ) (nachSig D (D.sigNr n) Λ)).map fun r => ⟨r.1, .bindCallInd p args he hp hr r.2⟩
      else [] else []

def bBindCallElse (m : Nat) (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (SB D V l Γ Λ) :=
  Aufz.fn.flatMap fun f => (genArgs (genExpr m Γ Λ) (D.params f)).flatMap fun args =>
    mitSome (D.erg f) fun {τ} he =>
      if hp : RufPasst D V (D.signatur f) Λ then if hr : 0 < D.gruende f then
        (R.en l (.why (D.gruende f) :: Γ) (nach D f Λ)).flatMap fun err =>
          (R.bl l (τ :: Γ) (nach D f Λ)).map fun r => ⟨r.1, .bindCallElse f args he hp hr err r.2⟩
      else [] else []

def bBindAxiom (m : Nat) (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (SB D V l Γ Λ) :=
  Aufz.ax.flatMap fun a => (genArgs (genExpr m Γ Λ) (D.aparams a)).flatMap fun args =>
    mitSome (D.aerg a) fun {τ} he =>
      if hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true then
      if hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true then
      if hd : ∀ t, D.aschreibt a t = true → darf D t Λ then
      if hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ then
        (R.bl l (τ :: Γ) Λ).map fun r => ⟨r.1, .bindAxiom a args he hw hg hd hgd r.2⟩
      else [] else [] else [] else []

def bBindAxiomElse (m : Nat) (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (SB D V l Γ Λ) :=
  Aufz.ax.flatMap fun a => (genArgs (genExpr m Γ Λ) (D.aparams a)).flatMap fun args =>
    mitSome (D.aerg a) fun {τ} he =>
      if hr : 0 < D.agruende a then
      if hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true then
      if hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true then
      if hd : ∀ t, D.aschreibt a t = true → darf D t Λ then
      if hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ then
        (R.en l (.why (D.agruende a) :: Γ) Λ).flatMap fun err =>
          (R.bl l (τ :: Γ) Λ).map fun r => ⟨r.1, .bindAxiomElse a args he hr hw hg hd hgd err r.2⟩
      else [] else [] else [] else [] else []

def bRegRead (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (SB D V l Γ Λ) :=
  Aufz.reg.flatMap fun r => if hk : (D.rklasse r).lesbar = true then
    (R.bl l (D.rtyp r :: Γ) Λ).map fun x => ⟨x.1, .regRead r hk x.2⟩ else []

def bRegReadElse (m : Nat) (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (SB D V l Γ Λ) :=
  Aufz.reg.flatMap fun r => if hk : (D.rklasse r).lesbar = true then
    (ofTy (genExpr m (D.rtyp r :: Γ) Λ) .bool).flatMap fun z => (R.en l Γ Λ).flatMap fun sonst =>
      (R.bl l (D.rtyp r :: Γ) Λ).map fun x => ⟨x.1, .regReadElse r hk z sonst x.2⟩
  else []

def bAwaits (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (SB D V l Γ Λ) :=
  Aufz.glob.flatMap fun g => if hL : gdarf D g Λ then
    (R.bl l (D.gtyp g :: Γ) Λ).map fun x => ⟨x.1, .awaits g (D.nutzlast g) rfl hL x.2⟩ else []

def bExchange (m : Nat) (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (SB D V l Γ Λ) :=
  Aufz.glob.flatMap fun g => (ofTy (genExpr m (D.gtyp g :: Γ) Λ) (D.gtyp g)).flatMap fun neu =>
    if hw : V.gschreibt g = true then if hL : gdarf D g Λ then
      (R.bl l (D.gtyp g :: Γ) Λ).map fun x => ⟨x.1, .exchange g neu hw hL x.2⟩ else [] else []

def bNarrow (m : Nat) (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (SB D V l Γ Λ) :=
  mitIntR (genExpr m Γ Λ) fun {_ _} e => (ints m).flatMap fun lo' => (ints m).flatMap fun hi' =>
    (R.en l Γ Λ).flatMap fun sonst =>
      (R.bl l (.int lo' hi' :: Γ) Λ).map fun x => ⟨x.1, .narrow e lo' hi' sonst x.2⟩

def bCheck (m : Nat) (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (SB D V l Γ Λ) :=
  (ofTy (genExpr m Γ Λ) .bool).flatMap fun c => (R.en l Γ Λ).flatMap fun sonst =>
    (R.bl l Γ Λ).map fun x => ⟨x.1, .check c sonst x.2⟩

def bFloat (m : Nat) (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (SB D V l Γ Λ) :=
  gleitOps.flatMap fun op => mitFl2R (genExpr m Γ Λ) fun {_ _ _ _} a b =>
    (paare m).flatMap fun lo => (paare m).flatMap fun hi =>
      (R.bl l (.fl lo hi :: Γ) Λ).map fun x => ⟨x.1, .float op a b lo hi x.2⟩

def bFloatLit (m : Nat) (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (SB D V l Γ Λ) :=
  (paare m).flatMap fun q => (paare m).flatMap fun lo => (paare m).flatMap fun hi =>
    (R.bl l (.fl lo hi :: Γ) Λ).map fun x => ⟨x.1, .floatLit q lo hi x.2⟩

def bFloatOf (m : Nat) (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (SB D V l Γ Λ) :=
  mitIntR (genExpr m Γ Λ) fun {_ _} e => (paare m).flatMap fun lo => (paare m).flatMap fun hi =>
    (R.bl l (.fl lo hi :: Γ) Λ).map fun x => ⟨x.1, .floatOf e lo hi x.2⟩

def bFloatNarrow (m : Nat) (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (SB D V l Γ Λ) :=
  mitFlR (genExpr m Γ Λ) fun {_ _} e => (paare m).flatMap fun lo => (paare m).flatMap fun hi =>
    (R.en l Γ Λ).flatMap fun sonst =>
      (R.bl l (.fl lo hi :: Γ) Λ).map fun x => ⟨x.1, .floatNarrow e lo hi sonst x.2⟩

/-- The blocks of fuel `m + 1`. -/
def blockS (m : Nat) (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (SB D V l Γ Λ) :=
  bNil l Γ Λ ++ bCons R l Γ Λ ++ bBind m R l Γ Λ ++ bBindCall m R l Γ Λ ++ bBindCallInd m R l Γ Λ ++
  bBindCallElse m R l Γ Λ ++ bBindAxiom m R l Γ Λ ++ bBindAxiomElse m R l Γ Λ ++ bRegRead R l Γ Λ ++
  bRegReadElse m R l Γ Λ ++ bAwaits R l Γ Λ ++ bExchange m R l Γ Λ ++ bNarrow m R l Γ Λ ++ bCheck m R l Γ Λ ++
  bFloat m R l Γ Λ ++ bFloatLit m R l Γ Λ ++ bFloatOf m R l Γ Λ ++ bFloatNarrow m R l Γ Λ

/-! ## End blocks -/

def eRet (m : Nat) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (Endblock D V l Γ Λ) :=
  (genErg (genExpr m Γ Λ) V.erg).flatMap fun e => if hΛ : Λ.Perm V.ende then [.ret e hΛ] else []

def eRetWhy (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (Endblock D V l Γ Λ) :=
  (List.finRange V.gruende).flatMap fun r => if hΛ : Λ.Perm V.ende then [.retWhy r hΛ] else []

def eLeave (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (Endblock D V l Γ Λ) :=
  if h : l = true then [.leave h] else []

def eNext (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (Endblock D V l Γ Λ) :=
  if h : l = true then [.next h] else []

def eCons (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (Endblock D V l Γ Λ) :=
  (R.st l Γ Λ).flatMap fun s => (R.en l Γ s.1).map fun r => .cons s.2 r

def eBind (m : Nat) (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (Endblock D V l Γ Λ) :=
  (genExpr m Γ Λ).flatMap fun p => (R.en l (p.1 :: Γ) Λ).map fun r => .bind p.2 r

def eBindAxiom (m : Nat) (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (Endblock D V l Γ Λ) :=
  Aufz.ax.flatMap fun a => (genArgs (genExpr m Γ Λ) (D.aparams a)).flatMap fun args =>
    mitSome (D.aerg a) fun {τ} he =>
      if hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true then
      if hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true then
      if hd : ∀ t, D.aschreibt a t = true → darf D t Λ then
      if hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ then
        (R.en l (τ :: Γ) Λ).map fun r => .bindAxiom a args he hw hg hd hgd r
      else [] else [] else [] else []

def eBindAxiomElse (m : Nat) (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (Endblock D V l Γ Λ) :=
  Aufz.ax.flatMap fun a => (genArgs (genExpr m Γ Λ) (D.aparams a)).flatMap fun args =>
    mitSome (D.aerg a) fun {τ} he =>
      if hr : 0 < D.agruende a then
      if hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true then
      if hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true then
      if hd : ∀ t, D.aschreibt a t = true → darf D t Λ then
      if hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ then
        (R.en l (.why (D.agruende a) :: Γ) Λ).flatMap fun err =>
          (R.en l (τ :: Γ) Λ).map fun r => .bindAxiomElse a args he hr hw hg hd hgd err r
      else [] else [] else [] else [] else []

/-- The end blocks of fuel `m + 1`. -/
def endS (m : Nat) (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (Endblock D V l Γ Λ) :=
  eRet m l Γ Λ ++ eRetWhy l Γ Λ ++ eLeave l Γ Λ ++ eNext l Γ Λ ++ eCons R l Γ Λ ++ eBind m R l Γ Λ ++
  eBindAxiom m R l Γ Λ ++ eBindAxiomElse m R l Γ Λ

/-- The generated statements, blocks and end blocks of every fuel. -/
def genRek (V : Vertrag D) : Nat → Rek V
  | 0 => ⟨fun _ _ _ => [], fun _ _ _ => [], fun _ _ _ => []⟩
  | m + 1 =>
    ⟨fun l Γ Λ => stmtS m (genRek V m) l Γ Λ, fun l Γ Λ => blockS m (genRek V m) l Γ Λ,
     fun l Γ Λ => endS m (genRek V m) l Γ Λ⟩

end Gabbro.Grammatik.Gen
