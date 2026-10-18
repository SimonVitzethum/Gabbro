/-
  File:      Grammatik/Gen/Erzeuger/Block.lean
  Subject:   The CLAUSES of the block and end-block generators, one per constructor of `Block` and `Endblock`. Same
             frame as `Anweisung.lean`: a clause is a `Sz` (the items of exact size `k`); the rest of a block after
             a `let` lives in a context of its own, drawn from the oracle with the budget the first part leaves
             (`Sz.bindR`, `Sz.bindS`: built once per size of the first part and key, shared by every first part).
-/
import Grammatik.Gen.Erzeuger.Anweisung

namespace Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D] [Zahlen] {V : Vertrag D}

/-- The four float operations. -/
def gleitOps : List GleitOp := [.add, .sub, .mul, .div]

theorem mem_gleitOps (op : GleitOp) : op ∈ gleitOps := by cases op <;> simp [gleitOps]

section Klauseln

variable (O : Orakel V) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (E : Sz (SE D Γ Λ)) (Ss : Sz (SS D V l Γ Λ))
  (Bs : Sz (SB D V l Γ Λ)) (Ns : Sz (Endblock D V l Γ Λ))

def bNil : Sz (SB D V l Γ Λ) := Sz.blatt [⟨Λ, .nil⟩]

def bCons : Sz (SB D V l Γ Λ) :=
  Sz.knoten (Sz.bindS Ss (fun Λ' m => O.bl l Γ Λ' m) fun _ s r => Sz.pure ⟨r.1, .cons s r.2⟩)

def bBind : Sz (SB D V l Γ Λ) :=
  Sz.knoten (Sz.bindS E (fun τ m => O.bl l (τ :: Γ) Λ m) fun _ e r => Sz.pure ⟨r.1, .bind e r.2⟩)

def bBindCall : Sz (SB D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.fn) fun f => mitSome (D.erg f) fun {τ} he =>
    Sz.wenn (RufPasst D V (D.signatur f) Λ) fun hp => Sz.wenn (D.gruende f = 0) fun hr =>
      Sz.bindR (argsS E (D.params f)) (fun m => O.bl l (τ :: Γ) (nach D f Λ) m) fun args r =>
        Sz.pure ⟨r.1, .bindCall f args he hp hr r.2⟩)

def bBindCallInd : Sz (SB D V l Γ Λ) :=
  Sz.knoten (Sz.bind (fnptrS E) fun ⟨n, p⟩ => mitSome (D.sigNr n).erg fun {τ} he =>
    Sz.wenn (RufPasst D V (D.sigNr n) Λ) fun hp => Sz.wenn ((D.sigNr n).gruende = 0) fun hr =>
      Sz.bindR (argsS E (D.sigNr n).params) (fun m => O.bl l (τ :: Γ) (nachSig D (D.sigNr n) Λ) m) fun args r =>
        Sz.pure ⟨r.1, .bindCallInd p args he hp hr r.2⟩)

def bBindCallElse : Sz (SB D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.fn) fun f => mitSome (D.erg f) fun {τ} he =>
    Sz.wenn (RufPasst D V (D.signatur f) Λ) fun hp => Sz.wenn (0 < D.gruende f) fun hr =>
      Sz.bindR (argsS E (D.params f)) (fun m => O.en l (.why (D.gruende f) :: Γ) (nach D f Λ) m) fun args err =>
        Sz.bindR (Sz.pure ()) (fun m => O.bl l (τ :: Γ) (nach D f Λ) m) fun _ r =>
          Sz.pure ⟨r.1, .bindCallElse f args he hp hr err r.2⟩)

def bBindAxiom : Sz (SB D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.ax) fun a => mitSome (D.aerg a) fun {τ} he =>
    Sz.wenn (∀ t, D.aschreibt a t = true → V.schreibt t = true) fun hw =>
    Sz.wenn (∀ g, D.agschreibt a g = true → V.gschreibt g = true) fun hg =>
    Sz.wenn (∀ t, D.aschreibt a t = true → darf D t Λ) fun hd =>
    Sz.wenn (∀ g, D.agschreibt a g = true → gdarf D g Λ) fun hgd =>
      Sz.bindR (argsS E (D.aparams a)) (fun m => O.bl l (τ :: Γ) Λ m) fun args r =>
        Sz.pure ⟨r.1, .bindAxiom a args he hw hg hd hgd r.2⟩)

def bBindAxiomElse : Sz (SB D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.ax) fun a => mitSome (D.aerg a) fun {τ} he =>
    Sz.wenn (0 < D.agruende a) fun hr =>
    Sz.wenn (∀ t, D.aschreibt a t = true → V.schreibt t = true) fun hw =>
    Sz.wenn (∀ g, D.agschreibt a g = true → V.gschreibt g = true) fun hg =>
    Sz.wenn (∀ t, D.aschreibt a t = true → darf D t Λ) fun hd =>
    Sz.wenn (∀ g, D.agschreibt a g = true → gdarf D g Λ) fun hgd =>
      Sz.bindR (argsS E (D.aparams a)) (fun m => O.en l (.why (D.agruende a) :: Γ) Λ m) fun args err =>
        Sz.bindR (Sz.pure ()) (fun m => O.bl l (τ :: Γ) Λ m) fun _ r =>
          Sz.pure ⟨r.1, .bindAxiomElse a args he hr hw hg hd hgd err r.2⟩)

def bRegRead : Sz (SB D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.reg) fun r => Sz.wenn ((D.rklasse r).lesbar = true) fun hk =>
    Sz.bindR (Sz.pure ()) (fun m => O.bl l (D.rtyp r :: Γ) Λ m) fun _ x => Sz.pure ⟨x.1, .regRead r hk x.2⟩)

def bRegReadElse : Sz (SB D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.reg) fun r => Sz.wenn ((D.rklasse r).lesbar = true) fun hk =>
    Sz.bindR (Sz.pure ()) (fun m => tyS (O.ex (D.rtyp r :: Γ) Λ m) .bool) fun _ z =>
      Sz.bind Ns fun sonst =>
        Sz.bindR (Sz.pure ()) (fun m => O.bl l (D.rtyp r :: Γ) Λ m) fun _ x =>
          Sz.pure ⟨x.1, .regReadElse r hk z sonst x.2⟩)

def bAwaits : Sz (SB D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.glob) fun g => Sz.wenn (gdarf D g Λ) fun hL =>
    Sz.bindR (Sz.pure ()) (fun m => O.bl l (D.gtyp g :: Γ) Λ m) fun _ x =>
      Sz.pure ⟨x.1, .awaits g (D.nutzlast g) rfl hL x.2⟩)

def bExchange : Sz (SB D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.glob) fun g =>
    Sz.wenn (V.gschreibt g = true) fun hw => Sz.wenn (gdarf D g Λ) fun hL =>
      Sz.bindR (Sz.pure ()) (fun m => tyS (O.ex (D.gtyp g :: Γ) Λ m) (D.gtyp g)) fun _ neu =>
        Sz.bindR (Sz.pure ()) (fun m => O.bl l (D.gtyp g :: Γ) Λ m) fun _ x =>
          Sz.pure ⟨x.1, .exchange g neu hw hL x.2⟩)

def bNarrow : Sz (SB D V l Γ Λ) :=
  Sz.knoten (Sz.bind (intS E) fun ⟨_, _, e⟩ => Sz.bind zS fun lo' => Sz.bind zS fun hi' =>
    Sz.bind Ns fun sonst =>
      Sz.bindR (Sz.pure ()) (fun m => O.bl l (.int lo' hi' :: Γ) Λ m) fun _ x =>
        Sz.pure ⟨x.1, .narrow e lo' hi' sonst x.2⟩)

def bCheck : Sz (SB D V l Γ Λ) :=
  Sz.knoten (Sz.bind (tyS E .bool) fun c => Sz.bind Ns fun sonst => Sz.bind Bs fun x =>
    Sz.pure ⟨x.1, .check c sonst x.2⟩)

def bFloat : Sz (SB D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl gleitOps) fun op => Sz.bind (flS E) fun ⟨_, _, a⟩ =>
    Sz.bind (flS E) fun ⟨_, _, b⟩ => Sz.bind paarS fun lo => Sz.bind paarS fun hi =>
      Sz.bindR (Sz.pure ()) (fun m => O.bl l (.fl lo hi :: Γ) Λ m) fun _ x =>
        Sz.pure ⟨x.1, .float op a b lo hi x.2⟩)

def bFloatLit : Sz (SB D V l Γ Λ) :=
  Sz.knoten (Sz.bind paarS fun q => Sz.bind paarS fun lo => Sz.bind paarS fun hi =>
    Sz.bindR (Sz.pure ()) (fun m => O.bl l (.fl lo hi :: Γ) Λ m) fun _ x =>
      Sz.pure ⟨x.1, .floatLit q lo hi x.2⟩)

def bFloatOf : Sz (SB D V l Γ Λ) :=
  Sz.knoten (Sz.bind (intS E) fun ⟨_, _, e⟩ => Sz.bind paarS fun lo => Sz.bind paarS fun hi =>
    Sz.bindR (Sz.pure ()) (fun m => O.bl l (.fl lo hi :: Γ) Λ m) fun _ x =>
      Sz.pure ⟨x.1, .floatOf e lo hi x.2⟩)

def bFloatNarrow : Sz (SB D V l Γ Λ) :=
  Sz.knoten (Sz.bind (flS E) fun ⟨_, _, e⟩ => Sz.bind paarS fun lo => Sz.bind paarS fun hi =>
    Sz.bind Ns fun sonst =>
      Sz.bindR (Sz.pure ()) (fun m => O.bl l (.fl lo hi :: Γ) Λ m) fun _ x =>
        Sz.pure ⟨x.1, .floatNarrow e lo hi sonst x.2⟩)

/-! ## End blocks -/

def eRet : Sz (Endblock D V l Γ Λ) :=
  Sz.knoten (Sz.bind (ergS E V.erg) fun e => Sz.wenn (Λ.Perm V.ende) fun hΛ => Sz.pure (.ret e hΛ))

def eRetWhy : Sz (Endblock D V l Γ Λ) :=
  Sz.blatt ((List.finRange V.gruende).flatMap fun r => if hΛ : Λ.Perm V.ende then [.retWhy r hΛ] else [])

def eLeave : Sz (Endblock D V l Γ Λ) := Sz.blatt (if h : l = true then [.leave h] else [])

def eNext : Sz (Endblock D V l Γ Λ) := Sz.blatt (if h : l = true then [.next h] else [])

def eCons : Sz (Endblock D V l Γ Λ) :=
  Sz.knoten (Sz.bindS Ss (fun Λ' m => O.en l Γ Λ' m) fun _ s r => Sz.pure (.cons s r))

def eBind : Sz (Endblock D V l Γ Λ) :=
  Sz.knoten (Sz.bindS E (fun τ m => O.en l (τ :: Γ) Λ m) fun _ e r => Sz.pure (.bind e r))

def eBindAxiom : Sz (Endblock D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.ax) fun a => mitSome (D.aerg a) fun {τ} he =>
    Sz.wenn (∀ t, D.aschreibt a t = true → V.schreibt t = true) fun hw =>
    Sz.wenn (∀ g, D.agschreibt a g = true → V.gschreibt g = true) fun hg =>
    Sz.wenn (∀ t, D.aschreibt a t = true → darf D t Λ) fun hd =>
    Sz.wenn (∀ g, D.agschreibt a g = true → gdarf D g Λ) fun hgd =>
      Sz.bindR (argsS E (D.aparams a)) (fun m => O.en l (τ :: Γ) Λ m) fun args r =>
        Sz.pure (.bindAxiom a args he hw hg hd hgd r))

def eBindAxiomElse : Sz (Endblock D V l Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.ax) fun a => mitSome (D.aerg a) fun {τ} he =>
    Sz.wenn (0 < D.agruende a) fun hr =>
    Sz.wenn (∀ t, D.aschreibt a t = true → V.schreibt t = true) fun hw =>
    Sz.wenn (∀ g, D.agschreibt a g = true → V.gschreibt g = true) fun hg =>
    Sz.wenn (∀ t, D.aschreibt a t = true → darf D t Λ) fun hd =>
    Sz.wenn (∀ g, D.agschreibt a g = true → gdarf D g Λ) fun hgd =>
      Sz.bindR (argsS E (D.aparams a)) (fun m => O.en l (.why (D.agruende a) :: Γ) Λ m) fun args err =>
        Sz.bindR (Sz.pure ()) (fun m => O.en l (τ :: Γ) Λ m) fun _ r =>
          Sz.pure (.bindAxiomElse a args he hr hw hg hd hgd err r))

end Klauseln

/-- **The blocks of exact size `k`**. -/
def blockS {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (O : Orakel V) (E : Sz (SE D Γ Λ)) (Ss : Sz (SS D V l Γ Λ))
    (Bs : Sz (SB D V l Γ Λ)) (Ns : Sz (Endblock D V l Γ Λ)) : Sz (SB D V l Γ Λ) :=
  Sz.alle [bNil, bCons O Ss, bBind O E, bBindCall O E, bBindCallInd O E, bBindCallElse O E, bBindAxiom O E,
    bBindAxiomElse O E, bRegRead O, bRegReadElse O Ns, bAwaits O, bExchange O, bNarrow O E Ns, bCheck E Bs Ns,
    bFloat O E, bFloatLit O, bFloatOf O E, bFloatNarrow O E Ns]

/-- **The end blocks of exact size `k`**. -/
def endS {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (O : Orakel V) (E : Sz (SE D Γ Λ)) (Ss : Sz (SS D V l Γ Λ)) :
    Sz (Endblock D V l Γ Λ) :=
  Sz.alle [eRet E, eRetWhy, eLeave, eNext, eCons O Ss, eBind O E, eBindAxiom O E, eBindAxiomElse O E]

end Gabbro.Grammatik.Gen
