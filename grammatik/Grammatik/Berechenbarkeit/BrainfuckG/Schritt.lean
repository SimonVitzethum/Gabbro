import Grammatik.Berechenbarkeit.BrainfuckG.Nimm
import Grammatik.Berechenbarkeit.BrainfuckG.Lege

/-! Brainfuck on G, part 4: one source step as one G block. A Brainfuck state lives in G as two locals -- the head
byte on top, the program counter below it -- and four stacks in one arena: the tape left of the head, the tape
right of it, the remaining input and the output in reverse (`Darstellt`). `befehl op next` is the G block of one
instruction: `>` and `<` push the head on one tape stack and take the new head off the other, `+`/`-` are one
assignment, `,` takes from the input stack, `.` pushes on the output stack, and the brackets set the counter by a
test of the head. `befehl_schritt` shows that the block runs to exactly the represented successor state whenever
the arena has room for one cell; `befehl_voll` that a push without room runs the declared failure block. -/

namespace Gabbro.Grammatik.Berechenbarkeit.BrainfuckG

open Brainfuck ArenaKette Storage.GStack

variable {D : Deklaration} {A : FreiForm D} {V : Vertrag D} {l : Bool} {Γ0 : Ctx} {Λ : List (Res D)} {n : Nat}

/-- The locals of a Brainfuck run: the head byte on top, the program counter below it. -/
abbrev BCtx (n : Nat) (Γ0 : Ctx) : Ctx := ByteTy :: Ty.int 0 n :: Γ0

/-- A program counter as a G value. -/
def pcWert (p : Fin (n + 1)) : Wert D (Ty.int 0 n) := ⟨p.val, by omega, by have := p.isLt; omega⟩

def kopfV : Var (BCtx n Γ0) ByteTy := .here
def pcV : Var (BCtx n Γ0) (Ty.int 0 n) := .there .here

/-- A byte as a payload of the arena. -/
def ablage (hp : D.typ A.tab A.feld = ByteTy) (b : Brainfuck.Byte) : Wert D (D.typ A.tab A.feld) :=
  Wert.umTyp hp.symm (kodiere b)

/-- The four stacks of a state: left tape, right tape, remaining input, output in reverse. -/
def stapel (hp : D.typ A.tab A.feld = ByteTy) (s : State n) : Fin 4 → List (Wert D (D.typ A.tab A.feld)) :=
  fun k => match k with
    | ⟨0, _⟩ => s.left.map (ablage hp)
    | ⟨1, _⟩ => s.right.map (ablage hp)
    | ⟨2, _⟩ => s.remainingInput.map (ablage hp)
    | ⟨_ + 3, _⟩ => s.reversedOutput.map (ablage hp)

/-- **The representation of a Brainfuck state** in a G world and environment. -/
def Darstellt (L : LinkFeld A) (G : Fin 4 → LinkKopf A) (hp : D.typ A.tab A.feld = ByteTy) (ρ0 : Env D Γ0)
    (s : State n) (σ : World D) (ρ : Env D (BCtx n Γ0)) : Prop :=
  ρ = .cons (kodiere s.head) (.cons (pcWert s.pc) ρ0) ∧ MultiRep L G σ (stapel hp s) ∧ A.FreiOk σ

/-- The write and lock permissions the stack code needs, once for all four stacks. -/
structure Rechte (A : FreiForm D) (G : Fin 4 → LinkKopf A) (V : Vertrag D) (Λ : List (Res D)) : Prop where
  wT : V.schreibt A.tab = true
  lT : darf D A.tab Λ
  wF : V.gschreibt A.kopf = true
  lF : gdarf D A.kopf Λ
  wU : V.gschreibt A.zaehl = true
  lU : gdarf D A.zaehl Λ
  wH : ∀ k, V.gschreibt (G k).g = true
  lH : ∀ k, gdarf D (G k).g Λ

section Code

variable (L : LinkFeld A) (G : Fin 4 → LinkKopf A) (hp : D.typ A.tab A.feld = ByteTy) (r : Rechte A G V Λ)
variable (voll : Endblock D V l (BCtx n Γ0) Λ)

/-- `pc = j`. -/
def setzePc (j : Fin (n + 1)) : Stmt D V l (BCtx n Γ0) Λ Λ :=
  .assignVar pcV (.widen (by omega) (by have := j.isLt; omega) (.lit j.val))

/-- The head is zero. -/
def istNull : Expr D (BCtx n Γ0) Λ .bool := .eq (.var kopfV) (.lit 0)

/-- Push the head on stack `k`, as one statement. -/
def legeS (k : Fin 4) : Stmt D V l (BCtx n Γ0) Λ Λ :=
  .ite .tru (lege L G k hp kopfV r.wT r.lT r.wF r.lF r.wU r.lU (r.wH k) (r.lH k) voll) .nil

/-- Take the head off stack `k`. -/
def nimmS (k : Fin 4) : Stmt D V l (BCtx n Γ0) Λ Λ :=
  nimm L G k hp kopfV (r.wH k) (r.lH k) r.wT r.lT r.wF r.lF voll

/-- **The G block of one instruction**, with the successor counter `next`. -/
def befehl (op : Instruction n) (next : Fin (n + 1)) : Gabbro.Grammatik.Block D V l (BCtx n Γ0) Λ Λ :=
  match op with
  | .right => .cons (legeS L G hp r voll 0) (.cons (nimmS L G hp r voll 1) (.cons (setzePc next) .nil))
  | .left => .cons (legeS L G hp r voll 1) (.cons (nimmS L G hp r voll 0) (.cons (setzePc next) .nil))
  | .increment => .cons (.assignVar kopfV (plusEins kopfV)) (.cons (setzePc next) .nil)
  | .decrement => .cons (.assignVar kopfV (minusEins kopfV)) (.cons (setzePc next) .nil)
  | .input => .cons (nimmS L G hp r voll 2) (.cons (setzePc next) .nil)
  | .output => .cons (legeS L G hp r voll 3) (.cons (setzePc next) .nil)
  | .open exit => .cons (.ite istNull (.cons (setzePc exit) .nil) (.cons (setzePc next) .nil)) .nil
  | .close body => .cons (.ite istNull (.cons (setzePc next) .nil) (.cons (setzePc body) .nil)) .nil

end Code

section Execution

variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

theorem execBlock_cons_of_ok {Λ' Λ'' : List (Res D)} {Γ : Ctx} (s : Stmt D V l Γ Λ Λ')
    (rest : Gabbro.Grammatik.Block D V l Γ Λ' Λ'') {σ σ' : World D} {ρ ρ' : Env D Γ}
    (h : execStmt O passes R s σ ρ = .ok σ' ρ') :
    execBlock O passes R (.cons s rest) σ ρ = execBlock O passes R rest σ' ρ' := by
  simp only [execBlock, h]

theorem setzePc_exec (j : Fin (n + 1)) (σ : World D) (ρ : Env D (BCtx n Γ0)) :
    execStmt O passes R (setzePc (V := V) (l := l) (Λ := Λ) j) σ ρ =
      .ok (σ.lese Λ []) (ρ.set pcV (pcWert j)) := by
  simp only [setzePc, execStmt]
  congr 2

theorem istNull_eval (σ₀ σ : World D) (b : Brainfuck.Byte) (p : Wert D (Ty.int 0 n)) (ρ0 : Env D Γ0) :
    eval σ₀ (istNull (Λ := Λ)) σ (.cons (kodiere b) (.cons p ρ0)) = decide (b = 0) := by
  show decide ((b.val : Int) = 0) = decide (b = 0)
  by_cases hb : b = 0
  · subst hb; rfl
  · have : (b.val : Int) ≠ 0 := by
      intro h; apply hb; exact Fin.ext (by omega)
    simp only [hb, this, decide_false]

theorem stapel_lese {L : LinkFeld A} {G : Fin 4 → LinkKopf A} {hp} {ρ0 : Env D Γ0} {s : State n} {σ : World D}
    {ρ : Env D (BCtx n Γ0)} (h : Darstellt L G hp ρ0 s σ ρ) (o : List (D.Tab ⊕ D.Glob)) :
    Darstellt L G hp ρ0 s (σ.lese Λ o) ρ :=
  ⟨h.1, MultiRep.lese h.2.1 _ _, A.freiOk_gleich (σ := σ) rfl (fun _ => rfl) rfl h.2.2⟩

/-- The counter instructions and `+`/`-` never allocate. -/
theorem befehl_schritt_kopf (L : LinkFeld A) (G : Fin 4 → LinkKopf A) (hp : D.typ A.tab A.feld = ByteTy)
    (r : Rechte A G V Λ) (voll : Endblock D V l (BCtx n Γ0) Λ) (ρ0 : Env D Γ0)
    (op : Instruction n) (hop : op ≠ .right ∧ op ≠ .left ∧ op ≠ .input ∧ op ≠ .output)
    (next : Fin (n + 1)) (s : State n) (σ : World D) (ρ : Env D (BCtx n Γ0))
    (hd : Darstellt L G hp ρ0 s σ ρ) :
    ∃ σ' ρ', execBlock O passes R (befehl L G hp r voll op next) σ ρ = .ok σ' ρ' ∧
      Darstellt L G hp ρ0 (execute op next s) σ' ρ' := by
  obtain ⟨hρ, hm, hf⟩ := hd
  subst hρ
  cases op with
  | right => exact absurd rfl hop.1
  | left => exact absurd rfl hop.2.1
  | input => exact absurd rfl hop.2.2.1
  | output => exact absurd rfl hop.2.2.2
  | increment =>
      refine ⟨?w1, ?e1, ?ex1, ?rep1⟩
      case ex1 =>
        simp only [befehl, execBlock, execStmt]
        rw [plusEins_eval kopfV _ _ _ s.head rfl]
        simp only [setzePc_exec]
        rfl
      case rep1 =>
        exact ⟨rfl, MultiRep.lese (MultiRep.lese hm _ _) _ _,
          A.freiOk_gleich rfl (fun _ => rfl) rfl (A.freiOk_gleich (σ := σ) rfl (fun _ => rfl) rfl hf)⟩
  | decrement =>
      refine ⟨?w2, ?e2, ?ex2, ?rep2⟩
      case ex2 =>
        simp only [befehl, execBlock, execStmt]
        rw [minusEins_eval kopfV _ _ _ s.head rfl]
        simp only [setzePc_exec]
        rfl
      case rep2 =>
        exact ⟨rfl, MultiRep.lese (MultiRep.lese hm _ _) _ _,
          A.freiOk_gleich rfl (fun _ => rfl) rfl (A.freiOk_gleich (σ := σ) rfl (fun _ => rfl) rfl hf)⟩
  | «open» exit =>
      by_cases hb : s.head = 0
      · refine ⟨?w3, ?e3, ?ex3, ?rep3⟩
        case ex3 =>
          simp only [befehl, execBlock, execStmt, istNull_eval, wahr?, hb, decide_true, ite_true, setzePc_exec]
          rfl
        case rep3 =>
          refine ⟨by simp [execute, hb, Env.set, pcV], MultiRep.lese (MultiRep.lese hm _ _) _ _,
            A.freiOk_gleich rfl (fun _ => rfl) rfl (A.freiOk_gleich (σ := σ) rfl (fun _ => rfl) rfl hf)⟩
      · refine ⟨?w4, ?e4, ?ex4, ?rep4⟩
        case ex4 =>
          simp only [befehl, execBlock, execStmt, istNull_eval, wahr?, hb, decide_false, Bool.false_eq_true,
            ite_false, setzePc_exec]
          rfl
        case rep4 =>
          refine ⟨by simp [execute, hb, Env.set, pcV], MultiRep.lese (MultiRep.lese hm _ _) _ _,
            A.freiOk_gleich rfl (fun _ => rfl) rfl (A.freiOk_gleich (σ := σ) rfl (fun _ => rfl) rfl hf)⟩
  | close body =>
      by_cases hb : s.head = 0
      · refine ⟨?w5, ?e5, ?ex5, ?rep5⟩
        case ex5 =>
          simp only [befehl, execBlock, execStmt, istNull_eval, wahr?, hb, decide_true, ite_true, setzePc_exec]
          rfl
        case rep5 =>
          refine ⟨by simp [execute, hb, Env.set, pcV], MultiRep.lese (MultiRep.lese hm _ _) _ _,
            A.freiOk_gleich rfl (fun _ => rfl) rfl (A.freiOk_gleich (σ := σ) rfl (fun _ => rfl) rfl hf)⟩
      · refine ⟨?w6, ?e6, ?ex6, ?rep6⟩
        case ex6 =>
          simp only [befehl, execBlock, execStmt, istNull_eval, wahr?, hb, decide_false, Bool.false_eq_true,
            ite_false, setzePc_exec]
          rfl
        case rep6 =>
          refine ⟨by simp [execute, hb, Env.set, pcV], MultiRep.lese (MultiRep.lese hm _ _) _ _,
            A.freiOk_gleich rfl (fun _ => rfl) rfl (A.freiOk_gleich (σ := σ) rfl (fun _ => rfl) rfl hf)⟩


/-- `legeS` as a statement: with room, stack `k` grows by the head byte. -/
theorem legeS_exec (L : LinkFeld A) (G : Fin 4 → LinkKopf A) (hinj : Function.Injective fun k => (G k).g)
    (hp : D.typ A.tab A.feld = ByteTy) (r : Rechte A G V Λ) (voll : Endblock D V l (BCtx n Γ0) Λ) (k : Fin 4)
    (σ : World D) (ρ : Env D (BCtx n Γ0)) (vals : Fin 4 → List (Wert D (D.typ A.tab A.feld)))
    (hm : MultiRep L G σ vals) (hf : A.FreiOk σ)
    (hroom : A.kopfSt σ < D.count A.tab ∨ A.stand σ < D.count A.tab) :
    ∃ σ', execStmt O passes R (legeS L G hp r voll k) σ ρ = .ok σ' ρ ∧
      MultiRep L G σ' (Function.update vals k (Wert.umTyp hp.symm (ρ.get kopfV) :: vals k)) ∧ A.FreiOk σ' := by
  obtain ⟨σ', hexec, hm', hf'⟩ := lege_ok O passes R L G hinj k hp kopfV r.wT r.lT r.wF r.lF r.wU r.lU (r.wH k)
    (r.lH k) voll (σ.lese Λ []) ρ vals (MultiRep.lese hm _ _) (A.freiOk_gleich (σ := σ) rfl (fun _ => rfl) rfl hf)
    hroom
  refine ⟨σ', ?_, hm', hf'⟩
  simp only [legeS, execStmt, eval, wahr?, ite_true]
  exact hexec

/-- `nimmS` over a stack holding the bytes `bs`: the head becomes the first byte (or `0`), the stack its tail. -/
theorem nimmS_exec (L : LinkFeld A) (G : Fin 4 → LinkKopf A) (hinj : Function.Injective fun k => (G k).g)
    (hp : D.typ A.tab A.feld = ByteTy) (r : Rechte A G V Λ) (voll : Endblock D V l (BCtx n Γ0) Λ) (k : Fin 4)
    (σ : World D) (ρ : Env D (BCtx n Γ0)) (vals : Fin 4 → List (Wert D (D.typ A.tab A.feld)))
    (bs : List Brainfuck.Byte) (hk : vals k = bs.map (ablage hp))
    (hm : MultiRep L G σ vals) (hf : A.FreiOk σ) :
    ∃ σ', execStmt O passes R (nimmS L G hp r voll k) σ ρ = .ok σ' (ρ.set kopfV (kodiere (bs.headD 0))) ∧
      MultiRep L G σ' (Function.update vals k (bs.tail.map (ablage hp))) ∧ A.FreiOk σ' := by
  cases bs with
  | nil =>
      obtain ⟨σ', hexec, hm', hf'⟩ := nimm_leer O passes R L G k hp kopfV (r.wH k) (r.lH k) r.wT r.lT r.wF r.lF
        voll σ ρ vals hm hf hk
      refine ⟨σ', hexec, ?_, hf'⟩
      have he : Function.update vals k (vals k) = vals := Function.update_eq_self k vals
      rw [hk] at he
      have he' : Function.update vals k (List.map (ablage hp) ([] : List Brainfuck.Byte).tail) = vals := he
      rw [he']
      exact hm'
  | cons b tl =>
      obtain ⟨σ', hexec, hm', hf'⟩ := nimm_voll O passes R L G hinj k hp kopfV (r.wH k) (r.lH k) r.wT r.lT r.wF
        r.lF voll σ ρ vals (ablage hp b) (tl.map (ablage hp)) hm hf hk
      refine ⟨σ', ?_, hm', hf'⟩
      simp only [nimmS]
      rw [hexec]
      simp only [ablage, Wert.umTyp_hin_her, List.headD_cons]

/-- A statement that ends in an end block ends its block there. -/
theorem execBlock_cons_of_end {Λ' Λ'' : List (Res D)} {Γ : Ctx} (s : Stmt D V l Γ Λ Λ')
    (rest : Gabbro.Grammatik.Block D V l Γ Λ' Λ'') {σ : World D} {ρ : Env D Γ} (e : EndAusgang V l Γ)
    (h : execStmt O passes R s σ ρ = e.zuAusgang) :
    execBlock O passes R (.cons s rest) σ ρ = e.zuAusgang := by
  simp only [execBlock, h]
  cases e <;> rfl

/-- **One Brainfuck step is one run of its G block**: the block of an instruction runs normally to the representation
of the successor state; an instruction that pushes needs room for one cell. -/
theorem befehl_schritt (L : LinkFeld A) (G : Fin 4 → LinkKopf A) (hinj : Function.Injective fun k => (G k).g)
    (hp : D.typ A.tab A.feld = ByteTy) (r : Rechte A G V Λ) (voll : Endblock D V l (BCtx n Γ0) Λ)
    (ρ0 : Env D Γ0) (op : Instruction n) (next : Fin (n + 1)) (s : State n) (σ : World D)
    (ρ : Env D (BCtx n Γ0)) (hd : Darstellt L G hp ρ0 s σ ρ)
    (hroom : op = .right ∨ op = .left ∨ op = .output → A.kopfSt σ < D.count A.tab ∨ A.stand σ < D.count A.tab) :
    ∃ σ' ρ', execBlock O passes R (befehl L G hp r voll op next) σ ρ = .ok σ' ρ' ∧
      Darstellt L G hp ρ0 (execute op next s) σ' ρ' := by
  have hrest : ∀ op', op' ≠ Instruction.right ∧ op' ≠ .left ∧ op' ≠ .input ∧ op' ≠ .output → op' = op →
      ∃ σ' ρ', execBlock O passes R (befehl L G hp r voll op next) σ ρ = .ok σ' ρ' ∧
        Darstellt L G hp ρ0 (execute op next s) σ' ρ' := by
    intro op' hop he
    subst he
    exact befehl_schritt_kopf O passes R L G hp r voll ρ0 op' hop next s σ ρ hd
  obtain ⟨hρ, hm, hf⟩ := hd
  subst hρ
  cases op with
  | right =>
      obtain ⟨σ1, h1, hm1, hf1⟩ := legeS_exec O passes R L G hinj hp r voll 0 σ _ _ hm hf (hroom (.inl rfl))
      obtain ⟨σ2, h2, hm2, hf2⟩ := nimmS_exec O passes R L G hinj hp r voll 1 σ1 _ _ s.right rfl hm1 hf1
      refine ⟨σ2.lese Λ [], _, ?_, rfl, MultiRep.lese ?_ Λ [], A.freiOk_gleich (σ := σ2) rfl (fun _ => rfl) rfl hf2⟩
      · simp only [befehl]
        rw [execBlock_cons_of_ok O passes R _ _ h1, execBlock_cons_of_ok O passes R _ _ h2,
          execBlock_cons_of_ok O passes R _ _ (setzePc_exec O passes R next σ2 _)]
        rfl
      · convert hm2 using 1
        funext k
        rcases k with ⟨_ | _ | _ | _ | k, hk⟩ <;> first | rfl | omega
  | left =>
      obtain ⟨σ1, h1, hm1, hf1⟩ := legeS_exec O passes R L G hinj hp r voll 1 σ _ _ hm hf (hroom (.inr (.inl rfl)))
      obtain ⟨σ2, h2, hm2, hf2⟩ := nimmS_exec O passes R L G hinj hp r voll 0 σ1 _ _ s.left rfl hm1 hf1
      refine ⟨σ2.lese Λ [], _, ?_, rfl, MultiRep.lese ?_ Λ [], A.freiOk_gleich (σ := σ2) rfl (fun _ => rfl) rfl hf2⟩
      · simp only [befehl]
        rw [execBlock_cons_of_ok O passes R _ _ h1, execBlock_cons_of_ok O passes R _ _ h2,
          execBlock_cons_of_ok O passes R _ _ (setzePc_exec O passes R next σ2 _)]
        rfl
      · convert hm2 using 1
        funext k
        rcases k with ⟨_ | _ | _ | _ | k, hk⟩ <;> first | rfl | omega
  | input =>
      obtain ⟨σ2, h2, hm2, hf2⟩ := nimmS_exec O passes R L G hinj hp r voll 2 σ _ _ s.remainingInput rfl hm hf
      refine ⟨σ2.lese Λ [], _, ?_, rfl, MultiRep.lese ?_ Λ [], A.freiOk_gleich (σ := σ2) rfl (fun _ => rfl) rfl hf2⟩
      · simp only [befehl]
        rw [execBlock_cons_of_ok O passes R _ _ h2,
          execBlock_cons_of_ok O passes R _ _ (setzePc_exec O passes R next σ2 _)]
        rfl
      · convert hm2 using 1
        funext k
        rcases k with ⟨_ | _ | _ | _ | k, hk⟩ <;> first | rfl | omega
  | output =>
      obtain ⟨σ1, h1, hm1, hf1⟩ := legeS_exec O passes R L G hinj hp r voll 3 σ _ _ hm hf (hroom (.inr (.inr rfl)))
      refine ⟨σ1.lese Λ [], _, ?_, rfl, MultiRep.lese ?_ Λ [], A.freiOk_gleich (σ := σ1) rfl (fun _ => rfl) rfl hf1⟩
      · simp only [befehl]
        rw [execBlock_cons_of_ok O passes R _ _ h1,
          execBlock_cons_of_ok O passes R _ _ (setzePc_exec O passes R next σ1 _)]
        rfl
      · convert hm1 using 1
        funext k
        rcases k with ⟨_ | _ | _ | _ | k, hk⟩ <;> first | rfl | omega
  | increment => exact hrest .increment ⟨nofun, nofun, nofun, nofun⟩ rfl
  | decrement => exact hrest .decrement ⟨nofun, nofun, nofun, nofun⟩ rfl
  | «open» exit => exact hrest (.open exit) ⟨nofun, nofun, nofun, nofun⟩ rfl
  | close body => exact hrest (.close body) ⟨nofun, nofun, nofun, nofun⟩ rfl

/-- **Out of memory is the failure block**: an instruction that pushes (`>`, `<`, `.`) in a full arena with an
empty free list runs `voll`, never a normal step. -/
theorem befehl_voll (L : LinkFeld A) (G : Fin 4 → LinkKopf A) (hp : D.typ A.tab A.feld = ByteTy)
    (r : Rechte A G V Λ) (voll : Endblock D V l (BCtx n Γ0) Λ) (op : Instruction n)
    (hop : op = .right ∨ op = .left ∨ op = .output) (next : Fin (n + 1)) (σ : World D) (ρ : Env D (BCtx n Γ0))
    (hnone : A.kopfSt σ = D.count A.tab) (hfull : A.stand σ = D.count A.tab) :
    ∃ σf, execBlock O passes R (befehl L G hp r voll op next) σ ρ = (execEnd O passes R voll σf ρ).zuAusgang := by
  have hl : ∀ k, execStmt O passes R (legeS L G hp r voll k) σ ρ =
      (execEnd O passes R voll (((σ.lese Λ []).lese Λ (freeEmpty (Γ := BCtx n Γ0) A r.lF).orte).lese Λ
        [Sum.inr A.zaehl]) ρ).zuAusgang := by
    intro k
    simp only [legeS, execStmt, eval, wahr?, ite_true]
    exact lege_voll O passes R L G k hp kopfV r.wT r.lT r.wF r.lF r.wU r.lU (r.wH k) (r.lH k) voll _ ρ hnone hfull
  refine ⟨((σ.lese Λ []).lese Λ (freeEmpty (Γ := BCtx n Γ0) A r.lF).orte).lese Λ [Sum.inr A.zaehl], ?_⟩
  rcases hop with rfl | rfl | rfl
  · exact execBlock_cons_of_end O passes R _ _ _ (hl 0)
  · exact execBlock_cons_of_end O passes R _ _ _ (hl 1)
  · exact execBlock_cons_of_end O passes R _ _ _ (hl 3)

/-- **Every step has exactly one of two outcomes**: the represented successor state, or the failure block. -/
theorem befehl_genau (L : LinkFeld A) (G : Fin 4 → LinkKopf A) (hinj : Function.Injective fun k => (G k).g)
    (hp : D.typ A.tab A.feld = ByteTy) (r : Rechte A G V Λ) (voll : Endblock D V l (BCtx n Γ0) Λ)
    (ρ0 : Env D Γ0) (op : Instruction n) (next : Fin (n + 1)) (s : State n) (σ : World D)
    (ρ : Env D (BCtx n Γ0)) (hd : Darstellt L G hp ρ0 s σ ρ) :
    (∃ σ' ρ', execBlock O passes R (befehl L G hp r voll op next) σ ρ = .ok σ' ρ' ∧
      Darstellt L G hp ρ0 (execute op next s) σ' ρ') ∨
    ∃ σf, execBlock O passes R (befehl L G hp r voll op next) σ ρ = (execEnd O passes R voll σf ρ).zuAusgang := by
  by_cases hroom : A.kopfSt σ < D.count A.tab ∨ A.stand σ < D.count A.tab
  · exact .inl (befehl_schritt O passes R L G hinj hp r voll ρ0 op next s σ ρ hd (fun _ => hroom))
  · by_cases hop : op = .right ∨ op = .left ∨ op = .output
    · have h1 := A.kopfSt_le σ
      have h2 := A.stand_le σ
      exact .inr (befehl_voll O passes R L G hp r voll op hop next σ ρ (by omega) (by omega))
    · exact .inl (befehl_schritt O passes R L G hinj hp r voll ρ0 op next s σ ρ hd (fun h => absurd h hop))
end Execution

end Gabbro.Grammatik.Berechenbarkeit.BrainfuckG
