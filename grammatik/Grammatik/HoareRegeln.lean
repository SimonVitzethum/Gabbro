/-
  File:      Grammatik/HoareRegeln.lean
  Subject:   SEQUENTIAL HOARE RULES OVER execBlock, blocks WITHOUT calls.

  `HTripel` is partial correctness over the actual sequential semantics:
  starting from any world/env where `Pre` holds, if the block ends normally
  (`.ok σ' ρ'`), then `Post` holds there. Contracts hold at their place
  with the actual values; pre/post are predicates over the actual world
  AND environment, never quantified over environments.

  `BlockOhneRuf` says a block performs no call: no `call`/`callInd` in any
  statement, no `bindCall`/`bindCallInd`/`bindCallElse` in any block spine,
  and nested blocks preserve the property. Lemma `ohneRuf_Runabhaengig`
  proves the meaning: on such blocks `execBlock` is independent of the
  call-meaning parameter `R`.
-/
import Grammatik.Semantik

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-! ## 1. Triples and call-freedom. -/

/-- Partial correctness over the actual sequential semantics: for every
    world and environment where `Pre` holds, if the block ends normally
    (`.ok σ' ρ'`), then `Post` holds at the outcome. -/
def HTripel (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (b : Block D V l Γ Λ Λ')
    (Pre : World D → Env D Γ → Prop) (Post : World D → Env D Γ → Prop) : Prop :=
  ∀ σ ρ, Pre σ ρ →
    ∀ σ' ρ', execBlock O passes R b σ ρ = Ausgang.ok σ' ρ' → Post σ' ρ'

/-- Statement-level triple over `execStmt`. -/
def STTripel (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (s : Stmt D V l Γ Λ Λ')
    (Pre : World D → Env D Γ → Prop) (Post : World D → Env D Γ → Prop) : Prop :=
  ∀ σ ρ, Pre σ ρ →
    ∀ σ' ρ', execStmt O passes R s σ ρ = Ausgang.ok σ' ρ' → Post σ' ρ'

/- A statement performs no call: `call`/`callInd` are excluded; nested
    blocks (branches, lock bodies, loops, breaking) must preserve the
    property. Oracle/hardware leaves (`axiomCall`, registers, transitions,
    publish/awaits) stay allowed: they are not calls. -/
mutual

inductive StmtOhneRuf : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    Stmt D V l Γ Λ Λ' → Prop where
  | assignSlot (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t)))
      (e : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ) :
      StmtOhneRuf (.assignSlot t f i e hw hL)
  | assignDurch (n : Nat) (p : Expr D Γ Λ (.ptr n true)) (t : D.Tab) (ht : D.tabNr n = some t)
      (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t))) (e : Expr D Γ Λ (D.typ t f))
      (hw : V.schreibt t = true) (hL : darf D t Λ) :
      StmtOhneRuf (.assignDurch p t ht f i e hw hL)
  | assignGlob (g : D.Glob) (e : Expr D Γ Λ (D.gtyp g)) (hw : V.gschreibt g = true)
      (hL : gdarf D g Λ) :
      StmtOhneRuf (.assignGlob g e hw hL)
  | schreibBytes (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) (n : Nat)
      (i : Expr D Γ Λ (.int lo hi)) (hlo : 0 ≤ lo) (hhi : hi + n ≤ D.count t)
      (e : Expr D Γ Λ (.int 0 (256 ^ n - 1))) (hw : V.schreibt t = true) (hL : darf D t Λ) :
      StmtOhneRuf (.schreibBytes t f hf n i hlo hhi e hw hL)
  | assignVar {τ : Ty} (x : Var Γ τ) (e : Expr D Γ Λ τ) :
      StmtOhneRuf (.assignVar (τ := τ) x e)
  | uebergang (t : D.Tab) (f : D.Feld t) (hτ : D.typ t f = .int lo hi)
      (i : Expr D Γ Λ (.index (D.count t))) (von nach : Int) (hn : lo ≤ nach ∧ nach ≤ hi)
      (he : D.erlaubt t f von nach = true) (hw : V.schreibt t = true) (hL : darf D t Λ) :
      StmtOhneRuf (.uebergang t f hτ i von nach hn he hw hL)
  | ite (c : Expr D Γ Λ .bool) (t e : Block D V l Γ Λ Λ')
      (ht : BlockOhneRuf t) (he : BlockOhneRuf e) :
      StmtOhneRuf (.ite c t e)
  | onOption (o : Expr D Γ Λ (.opt n)) (p : Block D V l (.index n :: Γ) Λ Λ')
      (a : Block D V l Γ Λ Λ') (hp : BlockOhneRuf p) (ha : BlockOhneRuf a) :
      StmtOhneRuf (.onOption o p a)
  | onTag (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
      (ha : ArmsOhneRuf arms) :
      StmtOhneRuf (.onTag v arms)
  | onGrund (r : Expr D Γ Λ (.grund n)) (arms : GrundArms D V l Γ Λ Λ' n)
      (ha : GrundArmsOhneRuf arms) :
      StmtOhneRuf (.onGrund r arms)
  | locks (L : D.Lock) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
      (body : Block D V l Γ (.held L :: Λ) (.held L :: Λ)) (hb : BlockOhneRuf body) :
      StmtOhneRuf (.locks L hr body)
  | breaking (i : D.Inv) (body : Block D V l Γ Λ Λ') (hb : BlockOhneRuf body) :
      StmtOhneRuf (.breaking i body)
  | traverse (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D V true (.index (D.count t) :: Γ) Λ Λ) (hb : BlockOhneRuf body) :
      StmtOhneRuf (.traverse t inv body)
  | retry (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
      (ueberlauf : Block D V l Γ Λ Λ)
      (hb : BlockOhneRuf body) (hu : BlockOhneRuf ueberlauf) :
      StmtOhneRuf (.retry n bis body ueberlauf)
  | forever (a : D.Annahme) (inv : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
      (hb : BlockOhneRuf body) :
      StmtOhneRuf (.forever a inv body)
  | axiomCall (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
      (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) :
      StmtOhneRuf (.axiomCall a args h hw hg hd hgd)
  | regSchreib (r : D.Reg) (hk : (D.rklasse r).schreibbar = true) (e : Expr D Γ Λ (D.rtyp r)) :
      StmtOhneRuf (.regSchreib r hk e)
  | transition (r : D.Reg) (hk : (D.rklasse r).schreibbar = true) (m : D.Reg)
      (hm : D.spiegel r = some m) (hl : (D.rklasse m).lesbar = true) (maske bits : Int) :
      StmtOhneRuf (.transition r hk m hm hl maske bits)
  | publish (g : D.Glob) (e : Expr D Γ Λ (D.gtyp g)) (payload : List D.Glob)
      (hp : payload = D.nutzlast g) (hw : V.gschreibt g = true) (hL : gdarf D g Λ) :
      StmtOhneRuf (.publish g e payload hp hw hL)
  | advances (m : D.Marke) (a : Nat) (h : Res.marke m a ∈ Λ) (hs : a + 1 < D.stufen m) :
      StmtOhneRuf (.advances m a h hs)
  | retires (m : D.Marke) (s : Nat) (h : Res.marke m s ∈ Λ) (a : D.Annahme) :
      StmtOhneRuf (.retires m s h a)
  | ret (e : ErgExpr D Γ Λ V.erg) (hΛ : List.Perm Λ V.ende) :
      StmtOhneRuf (.ret e hΛ)
  | retGrund (r : Fin V.gruende) (hΛ : List.Perm Λ V.ende) :
      StmtOhneRuf (.retGrund r hΛ)
  | leave (h : l = true) :
      StmtOhneRuf (.leave h)
  | next (h : l = true) :
      StmtOhneRuf (.next h)

inductive BlockOhneRuf : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    Block D V l Γ Λ Λ' → Prop where
  | nil : BlockOhneRuf .nil
  | cons (s : Stmt D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'')
      (hs : StmtOhneRuf s) (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.cons s rest)
  | bind (e : Expr D Γ Λ τ) (rest : Block D V l (τ :: Γ) Λ Λ')
      (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.bind e rest)
  | regLies (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.regLies r hk rest)
  | regLiesElse (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock D V l Γ Λ)
      (rest : Block D V l (D.rtyp r :: Γ) Λ Λ')
      (he : EndOhneRuf sonst) (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.regLiesElse r hk zusage sonst rest)
  | awaits (g : D.Glob) (payload : List D.Glob) (hp : payload = D.nutzlast g)
      (hL : gdarf D g Λ)
      (rest : Block D V l (D.gtyp g :: Γ) Λ Λ') (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.awaits g payload hp hL rest)
  | exchange (g : D.Glob) (neu : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g))
      (hw : V.gschreibt g = true) (hL : gdarf D g Λ)
      (rest : Block D V l (D.gtyp g :: Γ) Λ Λ') (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.exchange g neu hw hL rest)
  | narrow (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int) (sonst : Endblock D V l Γ Λ)
      (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
      (he : EndOhneRuf sonst) (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.narrow e lo' hi' sonst rest)
  | pruefung (c : Expr D Γ Λ .bool) (sonst : Endblock D V l Γ Λ)
      (rest : Block D V l Γ Λ Λ')
      (he : EndOhneRuf sonst) (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.pruefung c sonst rest)
  | gleit (op : GleitOp) (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2))
      (lo hi : Int × Int)
      (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.gleit op a b lo hi rest)
  | gleitLit (q : Int × Int) (lo hi : Int × Int)
      (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.gleitLit q lo hi rest)
  | gleitVon (e : Expr D Γ Λ (.int l1 h1)) (lo hi : Int × Int)
      (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.gleitVon e lo hi rest)
  | gleitNarrow (e : Expr D Γ Λ (.fl l1 h1)) (lo hi : Int × Int)
      (sonst : Endblock D V l Γ Λ)
      (rest : Block D V l (.fl lo hi :: Γ) Λ Λ')
      (he : EndOhneRuf sonst) (hr : BlockOhneRuf rest) :
      BlockOhneRuf (.gleitNarrow e lo hi sonst rest)

inductive EndOhneRuf : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} →
    Endblock D V l Γ Λ → Prop where
  | ret (e : ErgExpr D Γ Λ V.erg) (hΛ : List.Perm Λ V.ende) :
      EndOhneRuf (.ret e hΛ)
  | retGrund (r : Fin V.gruende) (hΛ : List.Perm Λ V.ende) :
      EndOhneRuf (.retGrund r hΛ)
  | leave (h : l = true) :
      EndOhneRuf (.leave h)
  | next (h : l = true) :
      EndOhneRuf (.next h)
  | cons (s : Stmt D V l Γ Λ Λ') (rest : Endblock D V l Γ Λ')
      (hs : StmtOhneRuf s) (hr : EndOhneRuf rest) :
      EndOhneRuf (.cons s rest)
  | bind (e : Expr D Γ Λ τ) (rest : Endblock D V l (τ :: Γ) Λ)
      (hr : EndOhneRuf rest) :
      EndOhneRuf (.bind e rest)

inductive ArmsOhneRuf : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    {cs : List (Option (Int × Int))} → Arms D V l Γ Λ Λ' cs → Prop where
  | nil : ArmsOhneRuf .nil
  | cons (b : Block D V l (ArmCtx Γ c) Λ Λ') (rest : Arms D V l Γ Λ Λ' cs)
      (hb : BlockOhneRuf b) (hr : ArmsOhneRuf rest) :
      ArmsOhneRuf (.cons b rest)

inductive GrundArmsOhneRuf : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    {n : Nat} → GrundArms D V l Γ Λ Λ' n → Prop where
  | nil : GrundArmsOhneRuf .nil
  | cons (b : Block D V l Γ Λ Λ') (rest : GrundArms D V l Γ Λ Λ' n)
      (hb : BlockOhneRuf b) (hr : GrundArmsOhneRuf rest) :
      GrundArmsOhneRuf (.cons (l := l) (Γ := Γ) b rest)
end

/-! ## 2. The standard rules. -/

/-- Skip: the empty block preserves every assertion. -/
theorem hoare_skip (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (Pst : World D → Env D Γ → Prop) :
    HTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R .nil Pst Pst := by
  intro σ ρ hPre σ' ρ' hrun
  simp only [execBlock] at hrun
  cases hrun
  exact hPre

/-- Assignment to a local variable, backward (substitution) form: from a
    pre saying `Pst` will hold after the update, conclude `Pst` after. -/
theorem hoare_assignVar (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {τ : Ty} (x : Var Γ τ) (e : Expr D Γ Λ τ)
    (Pst : World D → Env D Γ → Prop) :
    STTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R (.assignVar x e)
      (fun σ ρ => Pst (σ.lese Λ e.orte) (ρ.set x (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)))
      (fun σ' ρ' => Pst σ' ρ') := by
  intro σ ρ hPre σ' ρ' hrun
  have hrun' : execStmt O passes R (.assignVar (V := V) (l := l) x e) σ ρ =
      Ausgang.ok σ' ρ' := hrun
  simp only [execStmt] at hrun'
  cases hrun'
  exact hPre

/-- Assignment to a local variable, forward form: after the update the
    environment equals the old one with `x` set to the old value of `e`. -/
theorem hoare_assignVar_fwd (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {τ : Ty} (x : Var Γ τ) (e : Expr D Γ Λ τ)
    (Pre : World D → Env D Γ → Prop) :
    STTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R (.assignVar x e) Pre
      (fun σ' ρ' => ∃ σ ρ, Pre σ ρ ∧
        σ' = σ.lese Λ e.orte ∧
        ρ' = ρ.set x (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) := by
  intro σ ρ hPre σ' ρ' hrun
  have hrun' : execStmt O passes R (.assignVar (V := V) (l := l) x e) σ ρ =
      Ausgang.ok σ' ρ' := hrun
  simp only [execStmt] at hrun'
  cases hrun'
  exact ⟨σ, ρ, hPre, rfl, rfl⟩

/-- Sequence: the statement ends normally in the mid assertion, the rest
    carries it to the post. `execBlock (.cons s rest)` performs no guard
    read between `s` and `rest`, so one mid assertion fits both sides. -/
theorem hoare_seq (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (s : Stmt D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'')
    (Pre Mid Pst : World D → Env D Γ → Prop)
    (hs : STTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R s Pre Mid)
    (hrest : HTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ') O passes R rest Mid Pst) :
    HTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R (.cons s rest) Pre Pst := by
  intro σ ρ hPre σ' ρ' hrun
  simp only [execBlock] at hrun
  cases hstep : execStmt O passes R s σ ρ with
  | ok σ1 ρ1 =>
      have hmid : Mid σ1 ρ1 := hs σ ρ hPre σ1 ρ1 hstep
      have hcont : execBlock O passes R rest σ1 ρ1 = Ausgang.ok σ' ρ' := by
        rw [hstep] at hrun
        exact hrun
      exact hrest σ1 ρ1 hmid σ' ρ' hcont
  | zurueck σ1 v => rw [hstep] at hrun; exact absurd hrun (by simp)
  | grund σ1 r => rw [hstep] at hrun; exact absurd hrun (by simp)
  | leave h σ1 ρ1 => rw [hstep] at hrun; exact absurd hrun (by simp)
  | next h σ1 ρ1 => rw [hstep] at hrun; exact absurd hrun (by simp)
  | logik e => rw [hstep] at hrun; exact absurd hrun (by simp)
  | hardware e => rw [hstep] at hrun; exact absurd hrun (by simp)

/-- If-then-else: both branches satisfy the same triple. The branch
    condition reads its carriers first (`σ.lese`), so the branch
    hypotheses ask for the pre at the read world plus the actual
    condition value there. -/
theorem hoare_ite (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (c : Expr D Γ Λ .bool) (t e : Block D V l Γ Λ Λ')
    (Pre Pst : World D → Env D Γ → Prop)
    (ht : HTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R t
      (fun σ ρ => (∃ σ₀ ρ₀, Pre σ₀ ρ₀ ∧ σ = σ₀.lese Λ c.orte ∧ ρ = ρ₀) ∧
        wahr? (eval σ c σ ρ) = true) Pst)
    (he : HTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R e
      (fun σ ρ => (∃ σ₀ ρ₀, Pre σ₀ ρ₀ ∧ σ = σ₀.lese Λ c.orte ∧ ρ = ρ₀) ∧
        wahr? (eval σ c σ ρ) = false) Pst) :
    STTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R (.ite c t e)
      Pre Pst := by
  intro σ ρ hPre σ' ρ' hrun
  have hsplit : (let σr := σ.lese Λ c.orte
      if wahr? (eval σr c σr ρ) then execBlock O passes R t σr ρ
      else execBlock O passes R e σr ρ) = Ausgang.ok σ' ρ' := hrun
  cases hc : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) with
  | true =>
      have hmem : execBlock O passes R t (σ.lese Λ c.orte) ρ = Ausgang.ok σ' ρ' := by
        have := hsplit
        simp only [hc] at this
        exact this
      exact ht _ _ ⟨⟨σ, ρ, hPre, rfl, rfl⟩, hc⟩ _ _ hmem
  | false =>
      have hmem : execBlock O passes R e (σ.lese Λ c.orte) ρ = Ausgang.ok σ' ρ' := by
        have := hsplit
        simp only [hc] at this
        exact this
      exact he _ _ ⟨⟨σ, ρ, hPre, rfl, rfl⟩, hc⟩ _ _ hmem

/-- Consequence: strengthen the pre, weaken the post. -/
theorem hoare_konsequenz (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (b : Block D V l Γ Λ Λ')
    (Pre Pre' Pst Pst' : World D → Env D Γ → Prop)
    (h : HTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R b Pre' Pst')
    (hPre : ∀ σ ρ, Pre σ ρ → Pre' σ ρ)
    (hPst : ∀ σ ρ, Pst' σ ρ → Pst σ ρ) :
    HTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R b Pre Pst := by
  intro σ ρ hPR σ' ρ' hrun
  exact hPst σ' ρ' (h σ ρ (hPre σ ρ hPR) σ' ρ' hrun)

/-- Statement consequence: strengthen the pre, weaken the post. -/
theorem hoare_konsequenz_stmt (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (s : Stmt D V l Γ Λ Λ')
    (Pre Pre' Pst Pst' : World D → Env D Γ → Prop)
    (h : STTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R s Pre' Pst')
    (hPre : ∀ σ ρ, Pre σ ρ → Pre' σ ρ)
    (hPst : ∀ σ ρ, Pst' σ ρ → Pst σ ρ) :
    STTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R s Pre Pst := by
  intro σ ρ hPR σ' ρ' hrun
  exact hPst σ' ρ' (h σ ρ (hPre σ ρ hPR) σ' ρ' hrun)

/-! ## 3. Call-freedom means independence from the call meaning.

    On `BlockOhneRuf` blocks the executor never consults `R`: every case
    equation that mentions `R` is a call constructor, and those are absent.
    The statement version needs the block-level fact for `ite` branches
    (and the arms/lock/loop bodies), hence the mutual shape. -/


theorem armsOhneRuf_RunabhaengigAux {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {c : Option (Int × Int)} {cs' : List (Option (Int × Int))}
    (b : Block D V l (ArmCtx Γ c) Λ Λ')
    (rest : Arms D V l Γ Λ Λ' cs')
    (hb : ∀ (σ : World D) (ρ : Env D _),
      execBlock O passes R₁ b σ ρ = execBlock O passes R₂ b σ ρ)
    (hr : ∀ (w : Wert D (.sum cs')) (σ : World D) (ρ : Env D Γ),
      execArms O passes R₁ rest w σ ρ = execArms O passes R₂ rest w σ ρ)
    (k : Nat) (hk : k < (c :: cs').length)
    (nutz : Nutzlast ((c :: cs').get ⟨k, hk⟩))
    (σ : World D) (ρ : Env D Γ) :
    execArms O passes R₁ (Arms.cons b rest) ⟨⟨k, hk⟩, nutz⟩ σ ρ =
    execArms O passes R₂ (Arms.cons b rest) ⟨⟨k, hk⟩, nutz⟩ σ ρ := by
  cases k with
  | zero =>
      simp only [execArms, hb]
  | succ n =>
      have hk' : n < cs'.length := Nat.lt_of_succ_lt_succ hk
      have heq : (c :: cs').get ⟨n + 1, hk⟩ = cs'.get ⟨n, hk'⟩ := by
        simp only [List.get_cons_succ]
      have htail := hr ⟨⟨n, hk'⟩, heq ▸ nutz⟩ σ ρ
      simp only [execArms]
      exact htail


theorem grundArmsOhneRuf_RunabhaengigAux
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (blockEq : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (b : Block D V l Γ Λ Λ') (h : BlockOhneRuf b)
      (σ : World D) (ρ : Env D Γ),
      execBlock O passes R₁ b σ ρ = execBlock O passes R₂ b σ ρ)
    (σ : World D) (ρ : Env D Γ)
    {n' : Nat}
    (rest : GrundArms D V l Γ Λ Λ' n') (hr : GrundArmsOhneRuf rest)
    (k : Nat) (hk : k < n' + 1)
    (b : Block D V l Γ Λ Λ') (hb : BlockOhneRuf b) :
    execGrund O passes R₁ (GrundArms.cons b rest) ⟨k, hk⟩ σ ρ =
    execGrund O passes R₂ (GrundArms.cons b rest) ⟨k, hk⟩ σ ρ := by
  exact Nat.rec (motive := fun k => ∀ (n' : Nat)
      (rest : GrundArms D V l Γ Λ Λ' n') (hr : GrundArmsOhneRuf rest)
      (hk : k < n' + 1) (b : Block D V l Γ Λ Λ') (hb : BlockOhneRuf b),
      execGrund O passes R₁ (GrundArms.cons b rest) ⟨k, hk⟩ σ ρ =
      execGrund O passes R₂ (GrundArms.cons b rest) ⟨k, hk⟩ σ ρ)
    (fun n' rest hr hk b hb => by
      have hbeq := blockEq b hb σ ρ
      simp only [execGrund, hbeq])
    (fun n ih n' rest hr hk b hb => by
      have hk' : n < n' := Nat.lt_of_succ_lt_succ hk
      have hbeq := blockEq b hb σ ρ
      have hstep : execGrund O passes R₁ (GrundArms.cons b rest) ⟨n + 1, hk⟩ σ ρ =
          execGrund O passes R₁ rest ⟨n, hk'⟩ σ ρ := by
        simp only [execGrund]
      have hstep2 : execGrund O passes R₂ (GrundArms.cons b rest) ⟨n + 1, hk⟩ σ ρ =
          execGrund O passes R₂ rest ⟨n, hk'⟩ σ ρ := by
        simp only [execGrund]
      rw [hstep, hstep2]
      cases hr with
      | nil =>
          simp at hk'
      | cons _ _ hbTail hrTail =>
          exact ih _ _ hrTail hk' _ hbTail)
    k n' rest hr hk b hb

theorem grundArmsOhneRuf_Runabhaengig_end
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (blockEq : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (b : Block D V l Γ Λ Λ') (h : BlockOhneRuf b)
      (σ : World D) (ρ : Env D Γ),
      execBlock O passes R₁ b σ ρ = execBlock O passes R₂ b σ ρ)
    {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n) (h : GrundArmsOhneRuf arms)
    (r : Fin n) (σ : World D) (ρ : Env D Γ) :
    execGrund O passes R₁ arms r σ ρ = execGrund O passes R₂ arms r σ ρ := by
  cases h with
  | nil => exact r.elim0
  | cons b rest hb hr =>
      subst_vars
      cases r with
      | mk k hk =>
          exact grundArmsOhneRuf_RunabhaengigAux O passes R₁ R₂ blockEq σ ρ
            rest hr k hk b hb



theorem traverseKey {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (blockEq : ∀ (σ : World D) (ρ : Env D _),
      execBlock O passes R₁ body σ ρ = execBlock O passes R₂ body σ ρ)
    (ks : List (Wert D (.index (D.count t)))) (σ' : World D) (ρ' : Env D Γ) :
    execStmt O passes R₁ (Stmt.traverse (V := V) (l := l) (Γ := Γ) (Λ := Λ) t inv body) σ' ρ' =
    execStmt O passes R₂ (Stmt.traverse (V := V) (l := l) (Γ := Γ) (Λ := Λ) t inv body) σ' ρ' := by
      have hb' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => blockEq σ ρ
      have key : ∀ (ks : List (Wert D (.index (D.count t)))) (σ' : World D) (ρ' : Env D Γ),
          traverseLauf (V := V) (l := l) (τ := .index (D.count t)) (Γ := Γ)
            (fun σ ρ => execBlock O passes R₁ body σ ρ)
            (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ)))
            ks σ' ρ' =
          traverseLauf (V := V) (l := l) (τ := .index (D.count t)) (Γ := Γ)
            (fun σ ρ => execBlock O passes R₂ body σ ρ)
            (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ)))
            ks σ' ρ' := by
        intro ks
        induction ks with
        | nil => intro σ' ρ'; simp only [traverseLauf]
        | cons k ks ih =>
            intro σ' ρ'
            simp only [traverseLauf]
            cases hsch : execBlock (l := true) (Γ := .index (D.count t) :: Γ) O passes R₁ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 (.cons k ρ') with
            | ok σ'' ρ'' =>
                have hsame : execBlock (l := true) (Γ := .index (D.count t) :: Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 (.cons k ρ') = Ausgang.ok σ'' ρ'' := by
                  rw [← hsch]; exact (hb' _ _).symm
                simp only [hsame, hsch, ih]
            | zurueck σ'' v =>
                have hsame : execBlock (l := true) (Γ := .index (D.count t) :: Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 (.cons k ρ') = Ausgang.zurueck σ'' v := by
                  rw [← hsch]; exact (hb' _ _).symm
                simp only [hsame, hsch]
            | grund σ'' r =>
                have hsame : execBlock (l := true) (Γ := .index (D.count t) :: Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 (.cons k ρ') = Ausgang.grund σ'' r := by
                  rw [← hsch]; exact (hb' _ _).symm
                simp only [hsame, hsch]
            | leave h σ'' ρ'' =>
                have hsame : execBlock (l := true) (Γ := .index (D.count t) :: Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 (.cons k ρ') = Ausgang.leave h σ'' ρ'' := by
                  rw [← hsch]; exact (hb' _ _).symm
                simp only [hsame, hsch]
            | next h σ'' ρ'' =>
                have hsame : execBlock (l := true) (Γ := .index (D.count t) :: Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 (.cons k ρ') = Ausgang.next h σ'' ρ'' := by
                  rw [← hsch]; exact (hb' _ _).symm
                simp only [hsame, hsch, ih]
            | logik e =>
                have hsame : execBlock (l := true) (Γ := .index (D.count t) :: Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 (.cons k ρ') = Ausgang.logik e := by
                  rw [← hsch]; exact (hb' _ _).symm
                simp only [hsame, hsch]
            | hardware e =>
                have hsame : execBlock (l := true) (Γ := .index (D.count t) :: Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 (.cons k ρ') = Ausgang.hardware e := by
                  rw [← hsch]; exact (hb' _ _).symm
                simp only [hsame, hsch]
      simp only [execStmt]
      exact key _ _ _
theorem retryKey {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueberlauf : Block D V l Γ Λ Λ)
    (blockEqB : ∀ (σ : World D) (ρ : Env D _),
      execBlock O passes R₁ body σ ρ = execBlock O passes R₂ body σ ρ)
    (blockEqU : ∀ (σ : World D) (ρ : Env D _),
      execBlock O passes R₁ ueberlauf σ ρ = execBlock O passes R₂ ueberlauf σ ρ)
    (σ' : World D) (ρ' : Env D Γ) :
    execStmt O passes R₁ (Stmt.retry (V := V) (l := l) (Γ := Γ) (Λ := Λ) n bis body ueberlauf) σ' ρ' =
    execStmt O passes R₂ (Stmt.retry (V := V) (l := l) (Γ := Γ) (Λ := Λ) n bis body ueberlauf) σ' ρ' := by
      have hb' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => blockEqB σ ρ
      have hu' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => blockEqU σ ρ
      have key : ∀ (m : Nat) (σ' : World D) (ρ' : Env D Γ),
          retryLauf (fun σ ρ => execBlock O passes R₁ body σ ρ)
            (fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ)))
            (fun σ ρ => execBlock O passes R₁ ueberlauf σ ρ) m σ' ρ' =
          retryLauf (fun σ ρ => execBlock O passes R₂ body σ ρ)
            (fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ)))
            (fun σ ρ => execBlock O passes R₂ ueberlauf σ ρ) m σ' ρ' := by
        intro m
        induction m with
        | zero => intro σ' ρ'; simp only [retryLauf, hu']
        | succ m ih =>
            intro σ' ρ'
            simp only [retryLauf]
            cases hsch : execBlock (l := true) (Γ := Γ) O passes R₁ body ((fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ))) σ' ρ').1 ρ' with
          | ok σ'' ρ'' =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ))) σ' ρ').1 ρ' = Ausgang.ok σ'' ρ'' := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch]
              cases hb2 : wahr? (eval (σ'.lese Λ bis.orte) bis (σ'.lese Λ bis.orte) ρ') with
              | true => simp only [hb2, if_true, ih, hu']
              | false =>
                  have hF : ¬(false = true) := by decide
                  simp only [hb2, if_neg hF]
                  rw [ih]
          | zurueck σ'' v =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ))) σ' ρ').1 ρ' = Ausgang.zurueck σ'' v := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch]
          | grund σ'' r =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ))) σ' ρ').1 ρ' = Ausgang.grund σ'' r := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch]
          | leave h σ'' ρ'' =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ))) σ' ρ').1 ρ' = Ausgang.leave h σ'' ρ'' := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch]
          | next h σ'' ρ'' =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ))) σ' ρ').1 ρ' = Ausgang.next h σ'' ρ'' := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch, ih]
          | logik e =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ))) σ' ρ').1 ρ' = Ausgang.logik e := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch]
          | hardware e =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ))) σ' ρ').1 ρ' = Ausgang.hardware e := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch]
      simp only [execStmt, key]
theorem foreverKey {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (a : D.Annahme) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ)
    (blockEq : ∀ (σ : World D) (ρ : Env D _),
      execBlock O passes R₁ body σ ρ = execBlock O passes R₂ body σ ρ)
    (σ' : World D) (ρ' : Env D Γ) :
    execStmt O passes R₁ (Stmt.forever (V := V) (l := l) (Γ := Γ) (Λ := Λ) a inv body) σ' ρ' =
    execStmt O passes R₂ (Stmt.forever (V := V) (l := l) (Γ := Γ) (Λ := Λ) a inv body) σ' ρ' := by
      have hb' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => blockEq σ ρ
      have key : ∀ (m : Nat) (σ' : World D) (ρ' : Env D Γ),
          foreverLauf (V := V) (l := l) (Γ := Γ) a (fun σ ρ => execBlock O passes R₁ body σ ρ)
            (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ)))
            m σ' ρ' =
          foreverLauf (V := V) (l := l) (Γ := Γ) a (fun σ ρ => execBlock O passes R₂ body σ ρ)
            (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ)))
            m σ' ρ' := by
        intro m
        induction m with
        | zero => intro σ' ρ'; rfl
        | succ m ih =>
            intro σ' ρ'
            simp only [foreverLauf]
            cases hsch : execBlock (l := true) (Γ := Γ) O passes R₁ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 ρ' with
          | ok σ'' ρ'' =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 ρ' = Ausgang.ok σ'' ρ'' := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch, ih]
          | zurueck σ'' v =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 ρ' = Ausgang.zurueck σ'' v := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch]
          | grund σ'' r =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 ρ' = Ausgang.grund σ'' r := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch]
          | leave h σ'' ρ'' =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 ρ' = Ausgang.leave h σ'' ρ'' := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch]
          | next h σ'' ρ'' =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 ρ' = Ausgang.next h σ'' ρ'' := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch, ih]
          | logik e =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 ρ' = Ausgang.logik e := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch]
          | hardware e =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 ρ' = Ausgang.hardware e := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch]
      simp only [execStmt, key]
theorem stmtOhneRuf_Runabhaengig {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (s : Stmt D V l Γ Λ Λ') (h : StmtOhneRuf s)
    (σ : World D) (ρ : Env D Γ) :
    execStmt O passes R₁ s σ ρ = execStmt O passes R₂ s σ ρ :=
  StmtOhneRuf.rec
    (motive_1 := fun s _ => ∀ (σ : World D) (ρ : Env D _),
      execStmt O passes R₁ s σ ρ = execStmt O passes R₂ s σ ρ)
    (motive_2 := fun b _ => ∀ (σ : World D) (ρ : Env D _),
      execBlock O passes R₁ b σ ρ = execBlock O passes R₂ b σ ρ)
    (motive_3 := fun b _ => ∀ (σ : World D) (ρ : Env D _),
      execEnd O passes R₁ b σ ρ = execEnd O passes R₂ b σ ρ)
    (motive_4 := fun arms _ => ∀ (v : Wert D _) (σ : World D) (ρ : Env D _),
      execArms O passes R₁ arms v σ ρ = execArms O passes R₂ arms v σ ρ)
    (motive_5 := fun arms _ => ∀ (r : Fin _) (σ : World D) (ρ : Env D _),
      execGrund O passes R₁ arms r σ ρ = execGrund O passes R₂ arms r σ ρ)
    (fun t f i e hw hL σ ρ => rfl)
    (fun n p t ht f i e hw hL σ ρ => rfl)
    (fun g e hw hL σ ρ => rfl)
    (fun t f hf n i hlo hhi e hw hL σ ρ => rfl)
    (fun x e σ ρ => rfl)
    (fun t f hτ i von nach hn he hw hL σ ρ => by
        simp only [execStmt]
)
    (fun c t e ht he iht ihe σ ρ => by
        have ht' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => iht σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execStmt, ht', he']
)
    (fun o p a hp ha ihp iha σ ρ => by
        have hp' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihp σ ρ
        have ha' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => iha σ ρ
        simp only [execStmt]
        split
        next _ => simp only [hp']
        next _ => simp only [ha']
)
    (fun v arms ha iha σ ρ => by
        -- `execArms` runs at the read world; keep the world explicit.
        show execStmt O passes R₁ (.onTag (V := V) v arms) σ ρ =
          execStmt O passes R₂ (.onTag (V := V) v arms) σ ρ
        simp only [execStmt]
        exact iha _ _ _
)
    (fun r arms ha iha σ ρ => by
        show execStmt O passes R₁ (.onGrund (V := V) r arms) σ ρ =
          execStmt O passes R₂ (.onGrund (V := V) r arms) σ ρ
        simp only [execStmt]
        exact iha _ _ _
)
    (fun L hr body hb ihb σ ρ => by
        have hb' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihb σ ρ
        simp only [execStmt, hb']
)
    (fun i body hb ihb σ ρ => by
        have hb' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihb σ ρ
        simp only [execStmt, hb']
)
    (fun t inv body hb ihb σ ρ => by
        exact traverseKey O passes R₁ R₂ t inv body (fun σ ρ => ihb σ ρ) (alleIndizes (D.count t)) σ ρ)
    (fun n bis body ueberlauf hb hu ihb ihu σ ρ => by
        exact retryKey O passes R₁ R₂ n bis body ueberlauf (fun σ ρ => ihb σ ρ) (fun σ ρ => ihu σ ρ) σ ρ)
    (fun a inv body hb ihb σ ρ => by
        exact foreverKey O passes R₁ R₂ a inv body (fun σ ρ => ihb σ ρ) σ ρ)
    (fun a args h hw hg hd hgd σ ρ => by
  simp only [execStmt]
)
    (fun r hk e σ ρ => rfl)
    (fun r hk m hm hl maske bits σ ρ => rfl)
    (fun g e payload hp hw hL σ ρ => rfl)
    (fun m a h hs σ ρ => rfl)
    (fun m s h a σ ρ => rfl)
    (fun e hΛ σ ρ => rfl)
    (fun r hΛ σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun σ ρ => rfl)
    (fun s rest hs hr ihs ihr σ ρ => by
        have hs' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihs σ ρ
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock, hs', hr']
)
    (fun e rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock, hr']
)
    (fun r hk rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hein : einpassen (D.rtyp r) (O.regLies r σ) with
        | none => simp only [hein]
        | some v =>
            simp only [hein]
            by_cases hzu : D.rzusage r v = true
            · simp only [hzu, if_pos hzu, hr']
            · simp only [if_neg hzu]
)
    (fun r hk zusage sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        cases hein : einpassen (D.rtyp r) (O.regLies r σ) with
        | none => simp only [hein]
        | some v =>
            simp only [hein]
            split
            next _ => simp only [hr']
            next _ => simp only [he']
)
    (fun g payload hp hL rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        by_cases hs : O.sichtbar g σ = true
        · simp only [hs, if_pos hs, hr']
        · simp only [if_neg hs]
)
    (fun g neu hw hL rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock, hr']
)
    (fun e lo' hi' sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        split
        next _ => simp only [hr']
        next _ => simp only [he']
)
    (fun c sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        split
        next _ => simp only [hr']
        next _ => simp only [he']
)
    (fun op a b lo hi rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi (gleitRechne op _ _) with
        | none => simp only [hg]
        | some v => simp only [hg, hr']
)
    (fun q lo hi rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi (bruch q) with
        | none => simp only [hg]
        | some v => simp only [hg, hr']
)
    (fun e lo hi rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi (Float.ofInt _) with
        | none => simp only [hg]
        | some v => simp only [hg, hr']
)
    (fun e lo hi sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi _ with
        | none => simp only [hg, he']
        | some v => simp only [hg, hr']

)
    (fun e hΛ σ ρ => rfl)
    (fun r hΛ σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun s rest hs hr ihs ihr σ ρ => by
        have hs' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihs σ ρ
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execEnd, hs']
        cases execStmt O passes R₂ s σ ρ with
        | ok σ1 ρ1 => simp only [hr']
        | zurueck σ1 v => rfl
        | grund σ1 r => rfl
        | leave h σ1 ρ1 => rfl
        | next h σ1 ρ1 => rfl
        | logik e => rfl
        | hardware e => rfl
)
    (fun e rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execEnd, hr']

)
    (fun v σ ρ => by
        subst_vars
        cases v with
        | mk idx nutz => exact idx.elim0
)
    (fun b rest hb hr ihb ihr v σ ρ => by
        subst_vars
        cases v with
        | mk idx nutz =>
            cases idx with
            | mk k hk =>
                exact armsOhneRuf_RunabhaengigAux O passes R₁ R₂ b rest
                  (fun σ ρ => ihb σ ρ)
                  (fun w σ ρ => ihr w σ ρ)
                  k hk nutz σ ρ)
    (fun r σ ρ => by exact r.elim0)
    (fun b rest hb hr ihb ihr r σ ρ => by
      cases r with
      | mk k hk =>
          cases k with
          | zero =>
              have hbeq := ihb σ ρ
              simp only [execGrund, hbeq]
          | succ n =>
              have hk' : n < _ := Nat.lt_of_succ_lt_succ hk
              have hstep : execGrund O passes R₁ (GrundArms.cons b rest) ⟨n + 1, hk⟩ σ ρ =
                  execGrund O passes R₁ rest ⟨n, hk'⟩ σ ρ := by
                simp only [execGrund]
              have hstep2 : execGrund O passes R₂ (GrundArms.cons b rest) ⟨n + 1, hk⟩ σ ρ =
                  execGrund O passes R₂ rest ⟨n, hk'⟩ σ ρ := by
                simp only [execGrund]
              rw [hstep, hstep2]
              exact ihr _ _ _)
    h σ ρ

theorem blockOhneRuf_Runabhaengig {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (b : Block D V l Γ Λ Λ') (h : BlockOhneRuf b)
    (σ : World D) (ρ : Env D Γ) :
    execBlock O passes R₁ b σ ρ = execBlock O passes R₂ b σ ρ :=
  BlockOhneRuf.rec
    (motive_1 := fun s _ => ∀ (σ : World D) (ρ : Env D _),
      execStmt O passes R₁ s σ ρ = execStmt O passes R₂ s σ ρ)
    (motive_2 := fun b _ => ∀ (σ : World D) (ρ : Env D _),
      execBlock O passes R₁ b σ ρ = execBlock O passes R₂ b σ ρ)
    (motive_3 := fun b _ => ∀ (σ : World D) (ρ : Env D _),
      execEnd O passes R₁ b σ ρ = execEnd O passes R₂ b σ ρ)
    (motive_4 := fun arms _ => ∀ (v : Wert D _) (σ : World D) (ρ : Env D _),
      execArms O passes R₁ arms v σ ρ = execArms O passes R₂ arms v σ ρ)
    (motive_5 := fun arms _ => ∀ (r : Fin _) (σ : World D) (ρ : Env D _),
      execGrund O passes R₁ arms r σ ρ = execGrund O passes R₂ arms r σ ρ)
    (fun t f i e hw hL σ ρ => rfl)
    (fun n p t ht f i e hw hL σ ρ => rfl)
    (fun g e hw hL σ ρ => rfl)
    (fun t f hf n i hlo hhi e hw hL σ ρ => rfl)
    (fun x e σ ρ => rfl)
    (fun t f hτ i von nach hn he hw hL σ ρ => by
        simp only [execStmt]
)
    (fun c t e ht he iht ihe σ ρ => by
        have ht' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => iht σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execStmt, ht', he']
)
    (fun o p a hp ha ihp iha σ ρ => by
        have hp' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihp σ ρ
        have ha' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => iha σ ρ
        simp only [execStmt]
        split
        next _ => simp only [hp']
        next _ => simp only [ha']
)
    (fun v arms ha iha σ ρ => by
        -- `execArms` runs at the read world; keep the world explicit.
        show execStmt O passes R₁ (.onTag (V := V) v arms) σ ρ =
          execStmt O passes R₂ (.onTag (V := V) v arms) σ ρ
        simp only [execStmt]
        exact iha _ _ _
)
    (fun r arms ha iha σ ρ => by
        show execStmt O passes R₁ (.onGrund (V := V) r arms) σ ρ =
          execStmt O passes R₂ (.onGrund (V := V) r arms) σ ρ
        simp only [execStmt]
        exact iha _ _ _
)
    (fun L hr body hb ihb σ ρ => by
        have hb' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihb σ ρ
        simp only [execStmt, hb']
)
    (fun i body hb ihb σ ρ => by
        have hb' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihb σ ρ
        simp only [execStmt, hb']
)
    (fun t inv body hb ihb σ ρ => by
        exact traverseKey O passes R₁ R₂ t inv body (fun σ ρ => ihb σ ρ) (alleIndizes (D.count t)) σ ρ)
    (fun n bis body ueberlauf hb hu ihb ihu σ ρ => by
        exact retryKey O passes R₁ R₂ n bis body ueberlauf (fun σ ρ => ihb σ ρ) (fun σ ρ => ihu σ ρ) σ ρ)
    (fun a inv body hb ihb σ ρ => by
        exact foreverKey O passes R₁ R₂ a inv body (fun σ ρ => ihb σ ρ) σ ρ)
    (fun a args h hw hg hd hgd σ ρ => by
  simp only [execStmt]
)
    (fun r hk e σ ρ => rfl)
    (fun r hk m hm hl maske bits σ ρ => rfl)
    (fun g e payload hp hw hL σ ρ => rfl)
    (fun m a h hs σ ρ => rfl)
    (fun m s h a σ ρ => rfl)
    (fun e hΛ σ ρ => rfl)
    (fun r hΛ σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun σ ρ => rfl)
    (fun s rest hs hr ihs ihr σ ρ => by
        have hs' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihs σ ρ
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock, hs', hr']
)
    (fun e rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock, hr']
)
    (fun r hk rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hein : einpassen (D.rtyp r) (O.regLies r σ) with
        | none => simp only [hein]
        | some v =>
            simp only [hein]
            by_cases hzu : D.rzusage r v = true
            · simp only [hzu, if_pos hzu, hr']
            · simp only [if_neg hzu]
)
    (fun r hk zusage sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        cases hein : einpassen (D.rtyp r) (O.regLies r σ) with
        | none => simp only [hein]
        | some v =>
            simp only [hein]
            split
            next _ => simp only [hr']
            next _ => simp only [he']
)
    (fun g payload hp hL rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        by_cases hs : O.sichtbar g σ = true
        · simp only [hs, if_pos hs, hr']
        · simp only [if_neg hs]
)
    (fun g neu hw hL rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock, hr']
)
    (fun e lo' hi' sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        split
        next _ => simp only [hr']
        next _ => simp only [he']
)
    (fun c sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        split
        next _ => simp only [hr']
        next _ => simp only [he']
)
    (fun op a b lo hi rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi (gleitRechne op _ _) with
        | none => simp only [hg]
        | some v => simp only [hg, hr']
)
    (fun q lo hi rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi (bruch q) with
        | none => simp only [hg]
        | some v => simp only [hg, hr']
)
    (fun e lo hi rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi (Float.ofInt _) with
        | none => simp only [hg]
        | some v => simp only [hg, hr']
)
    (fun e lo hi sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi _ with
        | none => simp only [hg, he']
        | some v => simp only [hg, hr']

)
    (fun e hΛ σ ρ => rfl)
    (fun r hΛ σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun s rest hs hr ihs ihr σ ρ => by
        have hs' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihs σ ρ
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execEnd, hs']
        cases execStmt O passes R₂ s σ ρ with
        | ok σ1 ρ1 => simp only [hr']
        | zurueck σ1 v => rfl
        | grund σ1 r => rfl
        | leave h σ1 ρ1 => rfl
        | next h σ1 ρ1 => rfl
        | logik e => rfl
        | hardware e => rfl
)
    (fun e rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execEnd, hr']

)
    (fun v σ ρ => by
        subst_vars
        cases v with
        | mk idx nutz => exact idx.elim0
)
    (fun b rest hb hr ihb ihr v σ ρ => by
        subst_vars
        cases v with
        | mk idx nutz =>
            cases idx with
            | mk k hk =>
                exact armsOhneRuf_RunabhaengigAux O passes R₁ R₂ b rest
                  (fun σ ρ => ihb σ ρ)
                  (fun w σ ρ => ihr w σ ρ)
                  k hk nutz σ ρ)
    (fun r σ ρ => by exact r.elim0)
    (fun b rest hb hr ihb ihr r σ ρ => by
      cases r with
      | mk k hk =>
          cases k with
          | zero =>
              have hbeq := ihb σ ρ
              simp only [execGrund, hbeq]
          | succ n =>
              have hk' : n < _ := Nat.lt_of_succ_lt_succ hk
              have hstep : execGrund O passes R₁ (GrundArms.cons b rest) ⟨n + 1, hk⟩ σ ρ =
                  execGrund O passes R₁ rest ⟨n, hk'⟩ σ ρ := by
                simp only [execGrund]
              have hstep2 : execGrund O passes R₂ (GrundArms.cons b rest) ⟨n + 1, hk⟩ σ ρ =
                  execGrund O passes R₂ rest ⟨n, hk'⟩ σ ρ := by
                simp only [execGrund]
              rw [hstep, hstep2]
              exact ihr _ _ _)
    h σ ρ

theorem endOhneRuf_Runabhaengig {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (b : Endblock D V l Γ Λ) (h : EndOhneRuf b)
    (σ : World D) (ρ : Env D Γ) :
    execEnd O passes R₁ b σ ρ = execEnd O passes R₂ b σ ρ :=
  EndOhneRuf.rec
    (motive_1 := fun s _ => ∀ (σ : World D) (ρ : Env D _),
      execStmt O passes R₁ s σ ρ = execStmt O passes R₂ s σ ρ)
    (motive_2 := fun b _ => ∀ (σ : World D) (ρ : Env D _),
      execBlock O passes R₁ b σ ρ = execBlock O passes R₂ b σ ρ)
    (motive_3 := fun b _ => ∀ (σ : World D) (ρ : Env D _),
      execEnd O passes R₁ b σ ρ = execEnd O passes R₂ b σ ρ)
    (motive_4 := fun arms _ => ∀ (v : Wert D _) (σ : World D) (ρ : Env D _),
      execArms O passes R₁ arms v σ ρ = execArms O passes R₂ arms v σ ρ)
    (motive_5 := fun arms _ => ∀ (r : Fin _) (σ : World D) (ρ : Env D _),
      execGrund O passes R₁ arms r σ ρ = execGrund O passes R₂ arms r σ ρ)
    (fun t f i e hw hL σ ρ => rfl)
    (fun n p t ht f i e hw hL σ ρ => rfl)
    (fun g e hw hL σ ρ => rfl)
    (fun t f hf n i hlo hhi e hw hL σ ρ => rfl)
    (fun x e σ ρ => rfl)
    (fun t f hτ i von nach hn he hw hL σ ρ => by
        simp only [execStmt]
)
    (fun c t e ht he iht ihe σ ρ => by
        have ht' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => iht σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execStmt, ht', he']
)
    (fun o p a hp ha ihp iha σ ρ => by
        have hp' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihp σ ρ
        have ha' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => iha σ ρ
        simp only [execStmt]
        split
        next _ => simp only [hp']
        next _ => simp only [ha']
)
    (fun v arms ha iha σ ρ => by
        -- `execArms` runs at the read world; keep the world explicit.
        show execStmt O passes R₁ (.onTag (V := V) v arms) σ ρ =
          execStmt O passes R₂ (.onTag (V := V) v arms) σ ρ
        simp only [execStmt]
        exact iha _ _ _
)
    (fun r arms ha iha σ ρ => by
        show execStmt O passes R₁ (.onGrund (V := V) r arms) σ ρ =
          execStmt O passes R₂ (.onGrund (V := V) r arms) σ ρ
        simp only [execStmt]
        exact iha _ _ _
)
    (fun L hr body hb ihb σ ρ => by
        have hb' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihb σ ρ
        simp only [execStmt, hb']
)
    (fun i body hb ihb σ ρ => by
        have hb' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihb σ ρ
        simp only [execStmt, hb']
)
    (fun t inv body hb ihb σ ρ => by
        exact traverseKey O passes R₁ R₂ t inv body (fun σ ρ => ihb σ ρ) (alleIndizes (D.count t)) σ ρ)
    (fun n bis body ueberlauf hb hu ihb ihu σ ρ => by
        exact retryKey O passes R₁ R₂ n bis body ueberlauf (fun σ ρ => ihb σ ρ) (fun σ ρ => ihu σ ρ) σ ρ)
    (fun a inv body hb ihb σ ρ => by
        exact foreverKey O passes R₁ R₂ a inv body (fun σ ρ => ihb σ ρ) σ ρ)
    (fun a args h hw hg hd hgd σ ρ => by
  simp only [execStmt]
)
    (fun r hk e σ ρ => rfl)
    (fun r hk m hm hl maske bits σ ρ => rfl)
    (fun g e payload hp hw hL σ ρ => rfl)
    (fun m a h hs σ ρ => rfl)
    (fun m s h a σ ρ => rfl)
    (fun e hΛ σ ρ => rfl)
    (fun r hΛ σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun σ ρ => rfl)
    (fun s rest hs hr ihs ihr σ ρ => by
        have hs' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihs σ ρ
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock, hs', hr']
)
    (fun e rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock, hr']
)
    (fun r hk rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hein : einpassen (D.rtyp r) (O.regLies r σ) with
        | none => simp only [hein]
        | some v =>
            simp only [hein]
            by_cases hzu : D.rzusage r v = true
            · simp only [hzu, if_pos hzu, hr']
            · simp only [if_neg hzu]
)
    (fun r hk zusage sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        cases hein : einpassen (D.rtyp r) (O.regLies r σ) with
        | none => simp only [hein]
        | some v =>
            simp only [hein]
            split
            next _ => simp only [hr']
            next _ => simp only [he']
)
    (fun g payload hp hL rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        by_cases hs : O.sichtbar g σ = true
        · simp only [hs, if_pos hs, hr']
        · simp only [if_neg hs]
)
    (fun g neu hw hL rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock, hr']
)
    (fun e lo' hi' sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        split
        next _ => simp only [hr']
        next _ => simp only [he']
)
    (fun c sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        split
        next _ => simp only [hr']
        next _ => simp only [he']
)
    (fun op a b lo hi rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi (gleitRechne op _ _) with
        | none => simp only [hg]
        | some v => simp only [hg, hr']
)
    (fun q lo hi rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi (bruch q) with
        | none => simp only [hg]
        | some v => simp only [hg, hr']
)
    (fun e lo hi rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi (Float.ofInt _) with
        | none => simp only [hg]
        | some v => simp only [hg, hr']
)
    (fun e lo hi sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi _ with
        | none => simp only [hg, he']
        | some v => simp only [hg, hr']

)
    (fun e hΛ σ ρ => rfl)
    (fun r hΛ σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun s rest hs hr ihs ihr σ ρ => by
        have hs' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihs σ ρ
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execEnd, hs']
        cases execStmt O passes R₂ s σ ρ with
        | ok σ1 ρ1 => simp only [hr']
        | zurueck σ1 v => rfl
        | grund σ1 r => rfl
        | leave h σ1 ρ1 => rfl
        | next h σ1 ρ1 => rfl
        | logik e => rfl
        | hardware e => rfl
)
    (fun e rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execEnd, hr']

)
    (fun v σ ρ => by
        subst_vars
        cases v with
        | mk idx nutz => exact idx.elim0
)
    (fun b rest hb hr ihb ihr v σ ρ => by
        subst_vars
        cases v with
        | mk idx nutz =>
            cases idx with
            | mk k hk =>
                exact armsOhneRuf_RunabhaengigAux O passes R₁ R₂ b rest
                  (fun σ ρ => ihb σ ρ)
                  (fun w σ ρ => ihr w σ ρ)
                  k hk nutz σ ρ)
    (fun r σ ρ => by exact r.elim0)
    (fun b rest hb hr ihb ihr r σ ρ => by
      cases r with
      | mk k hk =>
          cases k with
          | zero =>
              have hbeq := ihb σ ρ
              simp only [execGrund, hbeq]
          | succ n =>
              have hk' : n < _ := Nat.lt_of_succ_lt_succ hk
              have hstep : execGrund O passes R₁ (GrundArms.cons b rest) ⟨n + 1, hk⟩ σ ρ =
                  execGrund O passes R₁ rest ⟨n, hk'⟩ σ ρ := by
                simp only [execGrund]
              have hstep2 : execGrund O passes R₂ (GrundArms.cons b rest) ⟨n + 1, hk⟩ σ ρ =
                  execGrund O passes R₂ rest ⟨n, hk'⟩ σ ρ := by
                simp only [execGrund]
              rw [hstep, hstep2]
              exact ihr _ _ _)
    h σ ρ

theorem armsOhneRuf_Runabhaengig {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {cs : List (Option (Int × Int))}
    (arms : Arms D V l Γ Λ Λ' cs) (h : ArmsOhneRuf arms)
    (v : Wert D (.sum cs)) (σ : World D) (ρ : Env D Γ) :
    execArms O passes R₁ arms v σ ρ = execArms O passes R₂ arms v σ ρ :=
  ArmsOhneRuf.rec
    (motive_1 := fun s _ => ∀ (σ : World D) (ρ : Env D _),
      execStmt O passes R₁ s σ ρ = execStmt O passes R₂ s σ ρ)
    (motive_2 := fun b _ => ∀ (σ : World D) (ρ : Env D _),
      execBlock O passes R₁ b σ ρ = execBlock O passes R₂ b σ ρ)
    (motive_3 := fun b _ => ∀ (σ : World D) (ρ : Env D _),
      execEnd O passes R₁ b σ ρ = execEnd O passes R₂ b σ ρ)
    (motive_4 := fun arms _ => ∀ (v : Wert D _) (σ : World D) (ρ : Env D _),
      execArms O passes R₁ arms v σ ρ = execArms O passes R₂ arms v σ ρ)
    (motive_5 := fun arms _ => ∀ (r : Fin _) (σ : World D) (ρ : Env D _),
      execGrund O passes R₁ arms r σ ρ = execGrund O passes R₂ arms r σ ρ)
    (fun t f i e hw hL σ ρ => rfl)
    (fun n p t ht f i e hw hL σ ρ => rfl)
    (fun g e hw hL σ ρ => rfl)
    (fun t f hf n i hlo hhi e hw hL σ ρ => rfl)
    (fun x e σ ρ => rfl)
    (fun t f hτ i von nach hn he hw hL σ ρ => by
        simp only [execStmt]
)
    (fun c t e ht he iht ihe σ ρ => by
        have ht' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => iht σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execStmt, ht', he']
)
    (fun o p a hp ha ihp iha σ ρ => by
        have hp' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihp σ ρ
        have ha' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => iha σ ρ
        simp only [execStmt]
        split
        next _ => simp only [hp']
        next _ => simp only [ha']
)
    (fun v arms ha iha σ ρ => by
        -- `execArms` runs at the read world; keep the world explicit.
        show execStmt O passes R₁ (.onTag (V := V) v arms) σ ρ =
          execStmt O passes R₂ (.onTag (V := V) v arms) σ ρ
        simp only [execStmt]
        exact iha _ _ _
)
    (fun r arms ha iha σ ρ => by
        show execStmt O passes R₁ (.onGrund (V := V) r arms) σ ρ =
          execStmt O passes R₂ (.onGrund (V := V) r arms) σ ρ
        simp only [execStmt]
        exact iha _ _ _
)
    (fun L hr body hb ihb σ ρ => by
        have hb' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihb σ ρ
        simp only [execStmt, hb']
)
    (fun i body hb ihb σ ρ => by
        have hb' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihb σ ρ
        simp only [execStmt, hb']
)
    (fun t inv body hb ihb σ ρ => by
        exact traverseKey O passes R₁ R₂ t inv body (fun σ ρ => ihb σ ρ) (alleIndizes (D.count t)) σ ρ)
    (fun n bis body ueberlauf hb hu ihb ihu σ ρ => by
        exact retryKey O passes R₁ R₂ n bis body ueberlauf (fun σ ρ => ihb σ ρ) (fun σ ρ => ihu σ ρ) σ ρ)
    (fun a inv body hb ihb σ ρ => by
        exact foreverKey O passes R₁ R₂ a inv body (fun σ ρ => ihb σ ρ) σ ρ)
    (fun a args h hw hg hd hgd σ ρ => by
  simp only [execStmt]
)
    (fun r hk e σ ρ => rfl)
    (fun r hk m hm hl maske bits σ ρ => rfl)
    (fun g e payload hp hw hL σ ρ => rfl)
    (fun m a h hs σ ρ => rfl)
    (fun m s h a σ ρ => rfl)
    (fun e hΛ σ ρ => rfl)
    (fun r hΛ σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun σ ρ => rfl)
    (fun s rest hs hr ihs ihr σ ρ => by
        have hs' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihs σ ρ
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock, hs', hr']
)
    (fun e rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock, hr']
)
    (fun r hk rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hein : einpassen (D.rtyp r) (O.regLies r σ) with
        | none => simp only [hein]
        | some v =>
            simp only [hein]
            by_cases hzu : D.rzusage r v = true
            · simp only [hzu, if_pos hzu, hr']
            · simp only [if_neg hzu]
)
    (fun r hk zusage sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        cases hein : einpassen (D.rtyp r) (O.regLies r σ) with
        | none => simp only [hein]
        | some v =>
            simp only [hein]
            split
            next _ => simp only [hr']
            next _ => simp only [he']
)
    (fun g payload hp hL rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        by_cases hs : O.sichtbar g σ = true
        · simp only [hs, if_pos hs, hr']
        · simp only [if_neg hs]
)
    (fun g neu hw hL rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock, hr']
)
    (fun e lo' hi' sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        split
        next _ => simp only [hr']
        next _ => simp only [he']
)
    (fun c sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        split
        next _ => simp only [hr']
        next _ => simp only [he']
)
    (fun op a b lo hi rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi (gleitRechne op _ _) with
        | none => simp only [hg]
        | some v => simp only [hg, hr']
)
    (fun q lo hi rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi (bruch q) with
        | none => simp only [hg]
        | some v => simp only [hg, hr']
)
    (fun e lo hi rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi (Float.ofInt _) with
        | none => simp only [hg]
        | some v => simp only [hg, hr']
)
    (fun e lo hi sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi _ with
        | none => simp only [hg, he']
        | some v => simp only [hg, hr']

)
    (fun e hΛ σ ρ => rfl)
    (fun r hΛ σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun s rest hs hr ihs ihr σ ρ => by
        have hs' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihs σ ρ
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execEnd, hs']
        cases execStmt O passes R₂ s σ ρ with
        | ok σ1 ρ1 => simp only [hr']
        | zurueck σ1 v => rfl
        | grund σ1 r => rfl
        | leave h σ1 ρ1 => rfl
        | next h σ1 ρ1 => rfl
        | logik e => rfl
        | hardware e => rfl
)
    (fun e rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execEnd, hr']

)
    (fun v σ ρ => by
        subst_vars
        cases v with
        | mk idx nutz => exact idx.elim0
)
    (fun b rest hb hr ihb ihr v σ ρ => by
        subst_vars
        cases v with
        | mk idx nutz =>
            cases idx with
            | mk k hk =>
                exact armsOhneRuf_RunabhaengigAux O passes R₁ R₂ b rest
                  (fun σ ρ => ihb σ ρ)
                  (fun w σ ρ => ihr w σ ρ)
                  k hk nutz σ ρ)
    (fun r σ ρ => by exact r.elim0)
    (fun b rest hb hr ihb ihr r σ ρ => by
      cases r with
      | mk k hk =>
          cases k with
          | zero =>
              have hbeq := ihb σ ρ
              simp only [execGrund, hbeq]
          | succ n =>
              have hk' : n < _ := Nat.lt_of_succ_lt_succ hk
              have hstep : execGrund O passes R₁ (GrundArms.cons b rest) ⟨n + 1, hk⟩ σ ρ =
                  execGrund O passes R₁ rest ⟨n, hk'⟩ σ ρ := by
                simp only [execGrund]
              have hstep2 : execGrund O passes R₂ (GrundArms.cons b rest) ⟨n + 1, hk⟩ σ ρ =
                  execGrund O passes R₂ rest ⟨n, hk'⟩ σ ρ := by
                simp only [execGrund]
              rw [hstep, hstep2]
              exact ihr _ _ _)
    h v σ ρ



/-- Triples over call-free blocks hold for every call meaning: the block
    outcome is the same one the `R`-indexed proof assumed, so the same
    proof works. Both `hRfrei` (this block is call-free) and `h`
    (the triple for `R₁`) are used. -/
theorem hoare_Runabhaengig (O : Orakel D) (passes : Nat)
    (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (b : Block D V l Γ Λ Λ') (hRfrei : BlockOhneRuf b)
    (Pre Pst : World D → Env D Γ → Prop)
    (h : HTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R₁ b Pre Pst) :
    HTripel (V := V) (l := l) (Γ := Γ) (Λ := Λ) O passes R₂ b Pre Pst := by
  intro σ ρ hPre σ' ρ' hrun
  have hsame : execBlock O passes R₁ b σ ρ = Ausgang.ok σ' ρ' := by
    rw [blockOhneRuf_Runabhaengig O passes R₁ R₂ b hRfrei σ ρ]
    exact hrun
  exact h σ ρ hPre σ' ρ' hsame

end Gabbro.Grammatik

/-! ## Cuts (booked, not hidden)

    Proven: HTripel/STTripel with skip, assignment (backward + forward),
    sequence, if-then-else, consequence (block + statement), and R-independence
    for call-free blocks (stmt/block/end/arms via the mutual recursor, grund
    via Nat.rec in the Aux lemma). Loop rules (traverse/retry/forever) are NOT
    Hoare rules here: traverseKey/retryKey/foreverKey prove R-independence of
    the loop executors only. No while-rule, no frame rule: both need invariants
    over shared carriers, which is the interference fragment (out of scope).
-/

#print axioms Gabbro.Grammatik.hoare_skip
#print axioms Gabbro.Grammatik.hoare_assignVar
#print axioms Gabbro.Grammatik.hoare_seq
#print axioms Gabbro.Grammatik.hoare_ite
#print axioms Gabbro.Grammatik.hoare_konsequenz
#print axioms Gabbro.Grammatik.blockOhneRuf_Runabhaengig
#print axioms Gabbro.Grammatik.hoare_Runabhaengig