import Grammatik.Bausteine.Arena.Ownership.Body.Judgment
import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T1

/-! **The ownership judgment of a running residue.** The call machine G keeps
what is left of an activation as a `GRest`: blocks in front of a
continuation, binder shrinks, lock release markers, the bounded loops with
their per-iteration shims, and the continuations behind `else` branches.
`OR A I out k c r` says: from a realised source context `c`, every way the
residue `r` runs keeps the ownership discipline of the body judgment, with
`k` the context a `leave`/`next` of the innermost loop shim exits to.
`OX A I out k r` is the half a `leave`/`next` needs: peeling outward through
`r` it reaches a loop shim whose loop context is `k` and whose continuation
is judged. A block that never falls through (`OB` into a context that no
environment realises) leaves only that half to its continuation. -/

namespace Gabbro.Grammatik.ArenaOwnership.Machine

open Source Body

variable {D : Deklaration}

mutual

/-- **A residue, run from a realised context.** -/
inductive OR (A : FreiForm D) (I : Interfaces A) {V : Vertrag D} (out : Flow.Output A V.erg) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → Context → Context → GRest D V l Γ Λ → Prop where
  | ende {l Γ Λ k c} (e : Endblock D V l Γ Λ) (h : OE A I out k c e) : OR A I out k c (.ende e)
  | dann {l Γ Λ Λ' k c c1} (b : Block D V l Γ Λ Λ') (r : GRest D V l Γ Λ') (hb : OB A I out k c b c1)
      (hr : OR A I out k c1 r) : OR A I out k c (.dann b r)
  /-- The block never falls through: its end context is realised by no environment. -/
  | dannDead {l Γ Λ Λ' k c c1} (b : Block D V l Γ Λ Λ') (r : GRest D V l Γ Λ') (hb : OB A I out k c b c1)
      (hu : c1.references.length ≠ Γ.length) (hx : OX A I out k r) : OR A I out k c (.dann b r)
  | schrumpf {l Γ Λ τ k c} (r : GRest D V l Γ Λ) (hk : k.references.length ≤ Γ.length)
      (hr : OR A I out k c.drop r) : OR A I out k c (.schrumpf (τ := τ) r)
  | frei {l Γ Λ k c} (L : D.Lock) (r : GRest D V l Γ Λ) (hr : OR A I out k c r) :
      OR A I out k c (.frei L r)
  /-- Behind an `else` branch: nothing falls through to it, exits peel through. -/
  | abbruch {l Γ Λ Λk k c} (r : GRest D V l Γ Λk) (hx : OX A I out k r) :
      OR A I out (Λ := Λ) k c (.abbruch r)
  | leer {l Γ Λ k c} : OR A I out (l := l) (Γ := Γ) (Λ := Λ) k c .leer
  | trav {l Γ Λ k c kk c1} (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D V true (.index (D.count t) :: Γ) Λ Λ) (ks : List (Wert D (.index (D.count t))))
      (r : GRest D V l Γ Λ) (hentry : Weaker kk c) (hinv : checkExpression A kk inv = true)
      (hb : OB A I out kk (kk.bind none) body c1) (hback : Weaker kk c1.drop)
      (hk : k.references.length ≤ Γ.length) (hr : OR A I out k kk r) :
      OR A I out k c (.trav t inv body ks r)
  | travRest {l Γ Λ kk c} (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D V true (.index (D.count t) :: Γ) Λ Λ) (ks : List (Wert D (.index (D.count t))))
      (r : GRest D V l Γ Λ) (hentry : Weaker kk c.drop) (hx : OX A I out kk (.travRest t inv body ks r)) :
      OR A I out kk c (.travRest t inv body ks r)
  | wieder {l Γ Λ k c kk c1} (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
      (ueber : Block D V l Γ Λ Λ) (r : GRest D V l Γ Λ) (hentry : Weaker kk c)
      (hbis : checkExpression A kk bis = true) (hb : OB A I out kk kk body c1) (hback : Weaker kk c1)
      (hu : OB A I out k kk ueber kk) (hk : k.references.length ≤ Γ.length) (hr : OR A I out k kk r) :
      OR A I out k c (.wieder n bis body ueber r)
  | wiederRest {l Γ Λ kk c} (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
      (ueber : Block D V l Γ Λ Λ) (r : GRest D V l Γ Λ) (hentry : Weaker kk c)
      (hx : OX A I out kk (.wiederRest n bis body ueber r)) :
      OR A I out kk c (.wiederRest n bis body ueber r)
  | ewig {l Γ Λ k c kk c1} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
      (r : GRest D V l Γ Λ) (hentry : Weaker kk c) (hinv : checkExpression A kk inv = true)
      (hb : OB A I out kk kk body c1) (hback : Weaker kk c1) (hk : k.references.length ≤ Γ.length)
      (hr : OR A I out k kk r) : OR A I out k c (.ewig a n inv body r)
  | ewigRest {l Γ Λ kk c} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
      (r : GRest D V l Γ Λ) (hentry : Weaker kk c) (hx : OX A I out kk (.ewigRest a n inv body r)) :
      OR A I out kk c (.ewigRest a n inv body r)

/-- **What a `leave`/`next` peeling outward through a residue needs.** -/
inductive OX (A : FreiForm D) (I : Interfaces A) {V : Vertrag D} (out : Flow.Output A V.erg) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → Context → GRest D V l Γ Λ → Prop where
  | dann {l Γ Λ Λ' k} (b : Block D V l Γ Λ Λ') (r : GRest D V l Γ Λ') (hx : OX A I out k r) :
      OX A I out k (.dann b r)
  | schrumpf {l Γ Λ τ k} (r : GRest D V l Γ Λ) (hk : k.references.length ≤ Γ.length) (hx : OX A I out k r) :
      OX A I out k (.schrumpf (τ := τ) r)
  | frei {l Γ Λ k} (L : D.Lock) (r : GRest D V l Γ Λ) (hx : OX A I out k r) : OX A I out k (.frei L r)
  | abbruch {l Γ Λ Λk k} (r : GRest D V l Γ Λk) (hx : OX A I out k r) : OX A I out (Λ := Λ) k (.abbruch r)
  | travRest {l Γ Λ k kk c1} (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D V true (.index (D.count t) :: Γ) Λ Λ) (ks : List (Wert D (.index (D.count t))))
      (r : GRest D V l Γ Λ) (hinv : checkExpression A kk inv = true)
      (hb : OB A I out kk (kk.bind none) body c1) (hback : Weaker kk c1.drop)
      (hlen : kk.references.length = Γ.length) (hk : k.references.length ≤ Γ.length) (hr : OR A I out k kk r) :
      OX A I out kk (.travRest t inv body ks r)
  | wiederRest {l Γ Λ k kk c1} (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
      (ueber : Block D V l Γ Λ Λ) (r : GRest D V l Γ Λ) (hbis : checkExpression A kk bis = true)
      (hb : OB A I out kk kk body c1) (hback : Weaker kk c1) (hu : OB A I out k kk ueber kk)
      (hlen : kk.references.length = Γ.length) (hk : k.references.length ≤ Γ.length) (hr : OR A I out k kk r) :
      OX A I out kk (.wiederRest n bis body ueber r)
  | ewigRest {l Γ Λ k kk c1} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
      (r : GRest D V l Γ Λ) (hinv : checkExpression A kk inv = true) (hb : OB A I out kk kk body c1)
      (hback : Weaker kk c1) (hlen : kk.references.length = Γ.length) (hk : k.references.length ≤ Γ.length)
      (hr : OR A I out k kk r) : OX A I out kk (.ewigRest a n inv body r)
  /-- No exit reaches these residues (no peel step has them behind an exit). -/
  | ende {l Γ Λ k} (e : Endblock D V l Γ Λ) : OX A I out k (.ende e)
  | leer {l Γ Λ k} : OX A I out (l := l) (Γ := Γ) (Λ := Λ) k .leer
  | trav {l Γ Λ k} (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D V true (.index (D.count t) :: Γ) Λ Λ) (ks : List (Wert D (.index (D.count t))))
      (r : GRest D V l Γ Λ) : OX A I out k (.trav t inv body ks r)
  | wieder {l Γ Λ k} (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
      (ueber : Block D V l Γ Λ Λ) (r : GRest D V l Γ Λ) : OX A I out k (.wieder n bis body ueber r)
  | ewig {l Γ Λ k} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
      (r : GRest D V l Γ Λ) : OX A I out k (.ewig a n inv body r)
  | wartet {l Γ Λ Λ' τ k} (rest : Block D V l (τ :: Γ) Λ Λ') (r : GRest D V l Γ Λ') :
      OX A I out k (.wartet rest r)
  | wartetSonst {l Γ Λ Λ' τ k} (n : Nat) (err : Endblock D V l (.why n :: Γ) Λ)
      (rest : Block D V l (τ :: Γ) Λ Λ') (r : GRest D V l Γ Λ') :
      OX A I out k (.wartetSonst n err rest r)

end

variable {A : FreiForm D} {I : Interfaces A} {V : Vertrag D} {out : Flow.Output A V.erg}

/-- A residue judged from a realised context carries its exit half. -/
theorem OR.exits : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {k c : Context} {r : GRest D V l Γ Λ},
    OR A I out k c r → OX A I out k r
  | _, _, _, _, _, _, .ende e _ => .ende e
  | _, _, _, _, _, _, .dann b r _ hr => .dann b r hr.exits
  | _, _, _, _, _, _, .dannDead b r _ _ hx => .dann b r hx
  | _, _, _, _, _, _, .schrumpf r hk hr => .schrumpf r hk hr.exits
  | _, _, _, _, _, _, .frei L r hr => .frei L r hr.exits
  | _, _, _, _, _, _, .abbruch r hx => .abbruch r hx
  | _, _, _, _, _, _, .leer => .leer
  | _, _, _, _, _, _, .trav t inv body ks r _ _ _ _ _ _ => .trav t inv body ks r
  | _, _, _, _, _, _, .travRest _ _ _ _ _ _ hx => hx
  | _, _, _, _, _, _, .wieder n bis body ueber r _ _ _ _ _ _ _ => .wieder n bis body ueber r
  | _, _, _, _, _, _, .wiederRest _ _ _ _ _ _ hx => hx
  | _, _, _, _, _, _, .ewig a n inv body r _ _ _ _ _ _ => .ewig a n inv body r
  | _, _, _, _, _, _, .ewigRest _ _ _ _ _ _ hx => hx

end Gabbro.Grammatik.ArenaOwnership.Machine
