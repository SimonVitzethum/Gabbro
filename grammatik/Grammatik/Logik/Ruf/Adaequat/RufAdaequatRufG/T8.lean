/- Part 8 of 10 of `RufAdaequatRufG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatRufG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T7

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 10. The depth induction and TARGET 4 -/

/-- The fragment by nesting depth: at depth `n + 1` a callee `g` is admitted
    if its body is covered with callees admitted at depth `n`; at depth `0`
    no callee is admitted (the handler of depth `0` never returns). A fact
    about the concrete program's bodies, decidable for a finite program. -/
def Tief (P : Programm D) (A : D.Lock → Prop) : Nat → D.Fn → Prop
  | 0, _ => False
  | n + 1, g => EndR A (Tief P A n) (P.rumpf g)

/-- **The callee obligation holds for the body-running handler**, at every
    depth: the handler of depth `n + 1` runs a covered callee body with
    handler depth `n`, and `endRetR` (with the obligation of depth `n`, by
    induction) realises that run on the machine, popping into whatever
    caller frame `PopArt` names. -/
theorem rufOk_tief (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden)
    (A : D.Lock → Prop) : ∀ n, RufOk P O passes f A (rufRumpf P O passes n) (Tief P A n)
  | 0 => ⟨fun _ hC => (hC : False).elim, fun _ hC => (hC : False).elim⟩
  | n + 1 => by
      refine ⟨?_, ?_⟩
      · intro g hC σ1 σ' rhoG v hR M caller rst log hZ ziel hart hΛ hA
        exact endRetR P O passes f g caller rst rhoG σ1 A (rufRumpf P O passes n) (Tief P A n)
          ziel (fun _ => caller) (rufOk_tief P O passes f A n) (P.rumpf g) hC log σ1 rhoG
          (.zurueck σ' v) hart (by rw [rufRumpf_ok hR]; rfl) M hZ hΛ hA
      · intro g hC σ1 σ' rhoG r hR M caller rst log hZ zielG hart hΛ hA
        exact endRetR P O passes f g caller rst rhoG σ1 A (rufRumpf P O passes n) (Tief P A n)
          (fun _ => caller) zielG (rufOk_tief P O passes f A n) (P.rumpf g) hC log σ1 rhoG
          (.why σ' r) hart (by rw [rufRumpf_grund hR]; rfl) M hZ hΛ hA

/-- **TARGET 4 -- adequacy of the call machine G for bodies WITH calls.**
    Thread `f` of `M` runs a frame of `fn` above a caller frame, with residue
    `.ende b` for an end block `b` in the fragment extended by calls
    (`call` in block and `ende` position, `let x = g(…)`), whose callees are
    admitted at nesting depth `n` (`Tief P A n`: their bodies are in the
    fragment with callees at depth `n - 1`, and so on); its holdings `Λ` name
    exactly the locks its trace holds; no other thread holds a lock the run
    may take (`A`). If the sequential semantics, run with the handler
    `rufRumpf P O passes n` that executes each callee's BODY, started at the
    thread's current world, returns `v` in world `σ'`, then steps of thread
    `f` alone reach a machine `M'` that has popped the frame -- after
    running every call on the machine (push, callee steps, pop) and
    continuing each caller PAST its call -- and logged `rueck fn rho v s0 σ'`
    with THE SAME value `v`, on top of the old log extended by the calls'
    events; its shared memory is `σ'.speicher`, and other threads are
    untouched. -/
theorem rufG_adaequat_ruf (P : Programm D) (O : Orakel D) (passes : Nat) (n : Nat)
    (M : RufMaschineG D) (f : Faden) (fn : D.Fn) (rho : Env D (D.params fn))
    (s0 : World D) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (spur : List (Ereignis D)) (log : List (RufEreignisF D)) {Γ : Ctx}
    {Λ : List (Res D)} (ρ : Env D Γ) (b : Endblock D (vertragVon D fn) false Γ Λ)
    (A : D.Lock → Prop) (hb : EndR A (Tief P A n) b)
    (hM : M.faeden f = ⟨caller :: rst, ⟨fn, rho, s0, ⟨false, Γ, Λ, ρ, .ende b⟩⟩, spur, log⟩)
    (hnw : caller.wartend = false)
    (hΛ : HeldGenau Λ (offen spur))
    (hfrei : ∀ L, A L → RufFreiG M f L)
    (σ' : World D) (v : ErgVal D (vertragVon D fn).erg)
    (hexec : execEnd O passes (rufRumpf P O passes n) b (M.weltVon f) ρ = .zurueck σ' v) :
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      M'.faeden f = ⟨rst, caller, σ'.spur, RufEreignisF.rueck fn rho v s0 σ' :: (ext ++ log)⟩ ∧
      M'.speicher = σ'.speicher ∧
      (∀ g, g ≠ f → M'.faeden g = M.faeden g) := by
  have hsp : (M.weltVon f).spur = spur := by
    show (M.faeden f).spur = spur
    rw [hM]
  have hZ : ZustandG M f (caller :: rst) fn rho s0 log ρ (.ende b) (M.weltVon f) :=
    ⟨by rw [hsp]; exact hM, rfl⟩
  obtain ⟨M', ext, hl, hG, _⟩ := endRetR P O passes f fn caller rst rho s0 A
    (rufRumpf P O passes n) (Tief P A n) (fun _ => caller) (fun _ => caller)
    (rufOk_tief P O passes f A n) b hb log (M.weltVon f) ρ (.zurueck σ' v) (PopArt.wie hnw)
    (by rw [hexec]; rfl) M hZ (by rw [hsp]; exact heldB_of_genau _ hΛ) hfrei
  have hG' : GepopptG M' f caller rst fn rho s0 (ext ++ log) v σ' := hG
  exact ⟨M', ext, hl, hG'.1, hG'.2, rufLaufG_fremd hl⟩

/-! ### The old fragment embeds: a call-free body is covered at every depth -/

mutual

theorem stmtG_R {V : Vertrag D} {A : D.Lock → Prop} {C : D.Fn → Prop}
    (hV : ∀ c, V.boden = some c → ∀ L, A L → c ≤ D.rang L) :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'},
    StmtG A mr s → StmtR A C mr s
  | _, _, _, _, _, _, .blatt s h => .blatt s h
  | _, _, _, _, _, _, .ite c t e ht he => .ite c t e (blockG_R hV ht) (blockG_R hV he)
  | _, _, _, _, _, _, .onOption o p a hp ha => .onOption o p a (blockG_R hV hp) (blockG_R hV ha)
  | _, _, _, _, _, _, .onTag v arms ha => .onTag v arms (armsG_R hV ha)
  | _, _, _, _, _, _, .onWhy r arms ha => .onWhy r arms (grundG_R hV ha)
  | _, _, _, _, _, _, .breaking i body hb => .breaking i body (blockG_R hV hb)
  | _, _, _, _, _, _, .locks L hr body hA hb => .locks L hr body (fun c hc => hV c hc L hA) hA (blockG_R hV hb)
  | _, _, _, _, _, _, .ret e hΛ => .ret e hΛ

theorem blockG_R {V : Vertrag D} {A : D.Lock → Prop} {C : D.Fn → Prop}
    (hV : ∀ c, V.boden = some c → ∀ L, A L → c ≤ D.rang L) :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {b : Block D V l Γ Λ Λ'},
    BlockG A mr b → BlockR A C mr b
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, .cons s rest hs hr => .cons s rest (stmtG_R hV hs) (blockG_R hV hr)
  | _, _, _, _, _, _, .bind e rest hr => .bind e rest (blockG_R hV hr)
  | _, _, _, _, _, _, .regRead r hk rest hr => .regRead r hk rest (blockG_R hV hr)
  | _, _, _, _, _, _, .regReadElse r hk z sonst rest hs hr =>
      .regReadElse r hk z sonst rest (endG_R hV hs) (blockG_R hV hr)
  | _, _, _, _, _, _, .awaits g payload hp hL hat rest hr => .awaits g payload hp hL hat rest (blockG_R hV hr)
  | _, _, _, _, _, _, .exchange g neu hw hL rest hr => .exchange g neu hw hL rest (blockG_R hV hr)
  | _, _, _, _, _, _, .narrow e lo hi sonst rest hs hr =>
      .narrow e lo hi sonst rest (endG_R hV hs) (blockG_R hV hr)
  | _, _, _, _, _, _, .check c sonst rest hs hr =>
      .check c sonst rest (endG_R hV hs) (blockG_R hV hr)
  | _, _, _, _, _, _, .float op a b lo hi rest hr => .float op a b lo hi rest (blockG_R hV hr)
  | _, _, _, _, _, _, .floatLit q lo hi rest hr => .floatLit q lo hi rest (blockG_R hV hr)
  | _, _, _, _, _, _, .floatOf e lo hi rest hr => .floatOf e lo hi rest (blockG_R hV hr)
  | _, _, _, _, _, _, .floatNarrow e lo hi sonst rest hs hr =>
      .floatNarrow e lo hi sonst rest (endG_R hV hs) (blockG_R hV hr)

theorem endG_R {V : Vertrag D} {A : D.Lock → Prop} {C : D.Fn → Prop}
    (hV : ∀ c, V.boden = some c → ∀ L, A L → c ≤ D.rang L) :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {e : Endblock D V l Γ Λ},
    EndG A e → EndR A C e
  | _, _, _, _, .ret e hΛ => .ret e hΛ
  | _, _, _, _, .cons s rest hs hr => .cons s rest (stmtG_R hV hs) (endG_R hV hr)
  | _, _, _, _, .bind e rest hr => .bind e rest (endG_R hV hr)

theorem armsG_R {V : Vertrag D} {A : D.Lock → Prop} {C : D.Fn → Prop}
    (hV : ∀ c, V.boden = some c → ∀ L, A L → c ≤ D.rang L) :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    {arms : Arms D V l Γ Λ Λ' cs}, ArmsG A mr arms → ArmsR A C mr arms
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, .cons b rest hb hr => .cons b rest (blockG_R hV hb) (armsG_R hV hr)

theorem grundG_R {V : Vertrag D} {A : D.Lock → Prop} {C : D.Fn → Prop}
    (hV : ∀ c, V.boden = some c → ∀ L, A L → c ≤ D.rang L) :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    {arms : GrundArms D V l Γ Λ Λ' n}, GrundArmsG A mr arms → GrundArmsR A C mr arms
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, .cons b rest hb hr => .cons b rest (blockG_R hV hb) (grundG_R hV hr)

end
/-- A call-free covered body is covered by the extended fragment at every
    depth, when every lock it may take respects its function's floor (`hV`,
    vacuous without a floor); `rufG_adaequat_ruf` therefore contains `rufG_adaequat` for the
    body-running handler. -/
theorem endG_tief (P : Programm D) (A : D.Lock → Prop) (n : Nat) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)} {e : Endblock D V l Γ Λ} (h : EndG A e)
    (hV : ∀ c, V.boden = some c → ∀ L, A L → c ≤ D.rang L) :
    EndR A (Tief P A n) e :=
  endG_R hV h



/-! ## 11. Witnesses: callers that continue after the call, and loops

    `t4D` has one table `konto` (2 slots, one `.int 0 100` field, unguarded
    and unshared), no locks, and three functions over `Fin 3` with one
    signature (no parameters, returns `.int 0 100`, may write `konto`):

        fn 0 (the callee):   konto[0] := 5; return 3
        fn 1 (plain call):   g(); konto[1] := 7; return 9
        fn 2 (bind-call):    if true { let x = g(); konto[1] := x } else { }; return 9

    `fn 1` is exactly the shape the old `ruf` got wrong: the call stands at
    `ende` position and the caller has an observable statement AFTER it. -/

def t4Sig : Signatur Unit Empty Empty Empty where
  params := []
  erg := some (.int 0 100)
  gruende := 0
  haelt := []
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def t4D : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 3
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Fin 4
  sig := fun _ => 0
  sigNr := fun _ => t4Sig
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun _ h => absurd h (by decide)
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

/-- The callee, the plain caller, the bind caller. -/
def t4G : t4D.Fn := show Fin 4 from 0
def t4F : t4D.Fn := show Fin 4 from 1
def t4B : t4D.Fn := show Fin 4 from 2
def t4L : t4D.Fn := show Fin 4 from 3

theorem t4Darf : darf t4D () [] := fun _ h => absurd h List.not_mem_nil

def t4Idx0 : Expr t4D [] [] (.index (t4D.count ())) := .widen (by decide) (by decide) (.lit 0)
def t4Idx1 : Expr t4D [] [] (.index (t4D.count ())) := .widen (by decide) (by decide) (.lit 1)
def t4Idx1x : Expr t4D [.int 0 100] [] (.index (t4D.count ())) :=
  .widen (by decide) (by decide) (.lit 1)
def t4Lit (k : Int) (h0 : 0 ≤ k) (h1 : k ≤ 100) : Expr t4D [] [] (t4D.typ () ()) :=
  .widen h0 h1 (.lit k)

/-- The callee body: `konto[0] := 5; return 3`. -/
def t4GRumpf : Endblock t4D (vertragVon t4D t4G) false [] [] :=
  .cons (.assignSlot () () t4Idx0 (t4Lit 5 (by decide) (by decide)) rfl t4Darf)
    (.ret (.val (t4Lit 3 (by decide) (by decide))) List.Perm.nil)

/-- Every caller passes the callee's contract: it may write what the callee
    writes, and there are no locks or marks. -/
theorem t4Hp (fn : t4D.Fn) : RufPasst t4D (vertragVon t4D fn) (t4D.signatur t4G) [] where
  hw := fun _ _ => rfl
  hg := fun g _ => nomatch g
  hk := ⟨[], List.Perm.nil, List.Sublist.slnil⟩
  hh := fun L => nomatch L

/-- The plain caller: `g(); konto[1] := 7; return 9`. -/
def t4FRumpf : Endblock t4D (vertragVon t4D t4F) false [] [] :=
  .cons (.call t4G .nil (t4Hp t4F) rfl)
    (.cons (.assignSlot () () t4Idx1 (t4Lit 7 (by decide) (by decide)) rfl t4Darf)
      (.ret (.val (t4Lit 9 (by decide) (by decide))) List.Perm.nil))

/-- The bind block: `let x = g(); konto[1] := x`. -/
def t4BindBlock : Block t4D (vertragVon t4D t4B) false [] [] [] :=
  .bindCall t4G .nil rfl (t4Hp t4B) rfl
    (.cons (.assignSlot () () t4Idx1x (.var .here) rfl t4Darf) .nil)

/-- The bind caller: `if true { let x = g(); konto[1] := x } else { }; return 9`. -/
def t4BRumpf : Endblock t4D (vertragVon t4D t4B) false [] [] :=
  .cons (.ite .tru t4BindBlock .nil)
    (.ret (.val (t4Lit 9 (by decide) (by decide))) List.Perm.nil)

def t4Idx2 : Expr t4D [] [] (.index (t4D.count ())) := .widen (by decide) (by decide) (.lit 2)

/-- The loop caller:
    `traverse konto invariant true { g() };
     retry until false bounded 1 { konto[1] := 8 } on_exceeded { konto[2] := 6 };
     return 9` -- the callee runs once per index, the retry body once, then
    the overflow block. -/
def t4LRumpf : Endblock t4D (vertragVon t4D t4L) false [] [] :=
  .cons (.traverse () .tru (.cons (.call t4G .nil (t4Hp t4L) rfl) .nil))
    (.cons (.retry 1 .fls
        (.cons (.assignSlot () () t4Idx1 (t4Lit 8 (by decide) (by decide)) rfl t4Darf) .nil)
        (.cons (.assignSlot () () t4Idx2 (t4Lit 6 (by decide) (by decide)) rfl t4Darf) .nil))
      (.ret (.val (t4Lit 9 (by decide) (by decide))) List.Perm.nil))

def t4P : Programm t4D where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun (f : Fin 4) => match f with
    | 0 => t4GRumpf
    | 1 => t4FRumpf
    | 2 => t4BRumpf
    | 3 => t4LRumpf

def t4O : Orakel t4D where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

/-- Start memory: every slot reads `0`. -/
def t4Sp : Speicher t4D :=
  ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- The frame below the caller (any frame will do: it is only resumed). -/
def t4Unten : RufRahmenG t4D :=
  ⟨t4F, Env.nil, t4Sp.welt [], ⟨false, [], [], Env.nil,
    .ende (.ret (.val (t4Lit 9 (by decide) (by decide))) List.Perm.nil)⟩⟩

/-- A machine whose threads all run the frame of `fn` with body `b` above
    `t4Unten`, with empty trace and log. -/
def t4M (fn : t4D.Fn) (b : Endblock t4D (vertragVon t4D fn) false [] []) : RufMaschineG t4D :=
  ⟨t4Sp, fun _ => ⟨[t4Unten], ⟨fn, Env.nil, t4Sp.welt [], ⟨false, [], [], Env.nil, .ende b⟩⟩,
    [], []⟩, [], t4Sp.welt []⟩

/-- The callee body is covered with no further calls: depth 1 admits it. -/
theorem t4G_tief (A : t4D.Lock → Prop) : Tief t4P A 1 t4G :=
  show EndR A (Tief t4P A 0) t4GRumpf from EndR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) (EndR.ret _ _)

theorem t4FRumpf_R (A : t4D.Lock → Prop) : EndR A (Tief t4P A 1) t4FRumpf :=
  EndR.cons _ _ (StmtR.call _ t4G rfl (t4G_tief A))
    (EndR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) (EndR.ret _ _))

theorem t4BRumpf_R (A : t4D.Lock → Prop) : EndR A (Tief t4P A 1) t4BRumpf :=
  EndR.cons _ _
    (StmtR.ite _ _ _
      (BlockR.bindCall _ _ _ _ _ _ (t4G_tief A)
        (BlockR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) BlockR.nil))
      BlockR.nil)
    (EndR.ret _ _)

theorem t4LRumpf_R (A : t4D.Lock → Prop) : EndR A (Tief t4P A 1) t4LRumpf :=
  EndR.cons _ _
    (StmtR.traverse _ _ _ (BlockR.cons _ _ (StmtR.call _ t4G rfl (t4G_tief A)) BlockR.nil))
    (EndR.cons _ _
      (StmtR.retry _ _ _ _
        (BlockR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) BlockR.nil)
        (BlockR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) BlockR.nil))
      (EndR.ret _ _))

theorem t4_frei (fn : t4D.Fn) (b : Endblock t4D (vertragVon t4D fn) false [] []) :
    ∀ L : t4D.Lock, (fun _ => False) L → RufFreiG (t4M fn b) 0 L := fun L => nomatch L

theorem t4_held : HeldGenau ([] : List (Res t4D)) (offen ([] : List (Ereignis t4D))) :=
  fun L => nomatch L

/-- The sequential run of the plain caller with the body-running handler:
    the callee writes slot 0, the caller then writes slot 1 and returns 9. -/
theorem t4F_exec : ∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4F).erg),
    execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4FRumpf ((t4M t4F t4FRumpf).weltVon 0) Env.nil =
      .zurueck σ' v ∧
    (σ'.slots () 0 ()).n = 5 ∧ (σ'.slots () 1 ()).n = 7 ∧ (show Zahl 0 100 from v).n = 9 :=
  ⟨_, _, rfl, rfl, rfl, rfl⟩

/-- The sequential run of the bind caller: the callee writes slot 0 and
    returns 3, the caller binds it and writes it to slot 1, then returns 9. -/
theorem t4B_exec : ∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4B).erg),
    execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4BRumpf ((t4M t4B t4BRumpf).weltVon 0) Env.nil =
      .zurueck σ' v ∧
    (σ'.slots () 0 ()).n = 5 ∧ (σ'.slots () 1 ()).n = 3 ∧ (show Zahl 0 100 from v).n = 9 :=
  ⟨_, _, rfl, rfl, rfl, rfl⟩

/-- **Witness for `rufG_adaequat_ruf`** (plain call at `ende` position).
    Every premise is instantiated jointly on the non-degenerate program
    above at depth `1`: the caller's body calls a callee that WRITES the
    table, and after the call the caller writes a second slot and returns
    a value. The sequential semantics with the body-running handler ends
    with slot 0 moved `0 -> 5` (the callee), slot 1 moved `0 -> 7` (the
    caller, AFTER the call) and value `9`; the machine, by steps of thread 0
    alone, pops the caller's frame logging that same `9` and that same
    world, and its memory holds both moved slots. The old `ruf` rule could
    never reach the write to slot 1. -/
theorem rufG_adaequat_ruf_zeuge :
    ∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4F).erg),
      execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4FRumpf ((t4M t4F t4FRumpf).weltVon 0) Env.nil =
        .zurueck σ' v ∧
      (((t4M t4F t4FRumpf).weltVon 0).slots () 0 ()).n = 0 ∧
      (((t4M t4F t4FRumpf).weltVon 0).slots () 1 ()).n = 0 ∧
      (σ'.slots () 0 ()).n = 5 ∧ (σ'.slots () 1 ()).n = 7 ∧ (show Zahl 0 100 from v).n = 9 ∧
      ∃ (M' : RufMaschineG t4D) (ext : List (RufEreignisF t4D)),
        RufLaufG t4P t4O 0 0 (t4M t4F t4FRumpf) M' ∧
        M'.faeden 0 = ⟨[], t4Unten, σ'.spur,
          RufEreignisF.rueck t4F Env.nil v (t4Sp.welt []) σ' :: (ext ++ [])⟩ ∧
        M'.speicher = σ'.speicher ∧ (M'.speicher.slots () 0 ()).n = 5 ∧
        (M'.speicher.slots () 1 ()).n = 7 ∧
        (∀ g, g ≠ 0 → M'.faeden g = (t4M t4F t4FRumpf).faeden g) := by
  obtain ⟨σ', v, hex, h5, h7, h9⟩ := t4F_exec
  obtain ⟨M', ext, hl, hf, hsp, hfr⟩ := rufG_adaequat_ruf t4P t4O 0 1 (t4M t4F t4FRumpf) 0 t4F
    Env.nil (t4Sp.welt []) t4Unten [] [] [] Env.nil t4FRumpf (fun _ => False)
    (t4FRumpf_R _) rfl rfl t4_held (t4_frei t4F t4FRumpf) σ' v hex
  refine ⟨σ', v, hex, rfl, rfl, h5, h7, h9, M', ext, hl, hf, hsp, ?_, ?_, hfr⟩
  · rw [hsp]; exact h5
  · rw [hsp]; exact h7

/-- **Witness for `rufG_adaequat_ruf`** (bind-call in block position, under
    an `if`): the callee writes slot 0 and returns `3`; the caller binds
    `x = 3` and writes it to slot 1. The machine pops the caller's frame
    with the same value `9` and a memory holding `5` and `3` -- the bound
    value travelled through the machine's `rueckBind`. -/
theorem rufG_adaequat_ruf_zeuge_bind :
    ∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4B).erg),
      execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4BRumpf ((t4M t4B t4BRumpf).weltVon 0) Env.nil =
        .zurueck σ' v ∧
      (σ'.slots () 0 ()).n = 5 ∧ (σ'.slots () 1 ()).n = 3 ∧ (show Zahl 0 100 from v).n = 9 ∧
      ∃ (M' : RufMaschineG t4D) (ext : List (RufEreignisF t4D)),
        RufLaufG t4P t4O 0 0 (t4M t4B t4BRumpf) M' ∧
        M'.faeden 0 = ⟨[], t4Unten, σ'.spur,
          RufEreignisF.rueck t4B Env.nil v (t4Sp.welt []) σ' :: (ext ++ [])⟩ ∧
        (M'.speicher.slots () 0 ()).n = 5 ∧ (M'.speicher.slots () 1 ()).n = 3 := by
  obtain ⟨σ', v, hex, h5, h3, h9⟩ := t4B_exec
  obtain ⟨M', ext, hl, hf, hsp, _⟩ := rufG_adaequat_ruf t4P t4O 0 1 (t4M t4B t4BRumpf) 0 t4B
    Env.nil (t4Sp.welt []) t4Unten [] [] [] Env.nil t4BRumpf (fun _ => False)
    (t4BRumpf_R _) rfl rfl t4_held (t4_frei t4B t4BRumpf) σ' v hex
  refine ⟨σ', v, hex, h5, h3, h9, M', ext, hl, hf, ?_, ?_⟩
  · rw [hsp]; exact h5
  · rw [hsp]; exact h3


/-- The sequential run of the loop caller: three calls inside the
    `traverse` (slot 0 moved to 5), the `retry` body once (slot 1 to 8),
    its overflow block (slot 2 to 6), value 9. -/
theorem t4L_exec : ∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4L).erg),
    execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4LRumpf ((t4M t4L t4LRumpf).weltVon 0) Env.nil =
      .zurueck σ' v ∧
    (σ'.slots () 0 ()).n = 5 ∧ (σ'.slots () 1 ()).n = 8 ∧ (σ'.slots () 2 ()).n = 6 ∧
    (show Zahl 0 100 from v).n = 9 :=
  ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩

/-- **Witness for `rufG_adaequat_ruf` with loops**: a `traverse` whose body
    CALLS the writing callee (three iterations, the invariant read before
    each and after the last), then a bounded `retry` whose body runs once
    and whose overflow block runs at the bound. The machine pops the frame
    with the value `9` and the memory the sequential semantics computes:
    all three slots moved. -/
theorem rufG_adaequat_ruf_zeuge_schleife :
    ∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4L).erg),
      execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4LRumpf ((t4M t4L t4LRumpf).weltVon 0) Env.nil =
        .zurueck σ' v ∧ (show Zahl 0 100 from v).n = 9 ∧
      ∃ (M' : RufMaschineG t4D) (ext : List (RufEreignisF t4D)),
        RufLaufG t4P t4O 0 0 (t4M t4L t4LRumpf) M' ∧
        M'.faeden 0 = ⟨[], t4Unten, σ'.spur,
          RufEreignisF.rueck t4L Env.nil v (t4Sp.welt []) σ' :: (ext ++ [])⟩ ∧
        (M'.speicher.slots () 0 ()).n = 5 ∧ (M'.speicher.slots () 1 ()).n = 8 ∧
        (M'.speicher.slots () 2 ()).n = 6 := by
  obtain ⟨σ', v, hex, h5, h8, h6, h9⟩ := t4L_exec
  obtain ⟨M', ext, hl, hf, hsp, _⟩ := rufG_adaequat_ruf t4P t4O 0 1 (t4M t4L t4LRumpf) 0 t4L
    Env.nil (t4Sp.welt []) t4Unten [] [] [] Env.nil t4LRumpf (fun _ => False)
    (t4LRumpf_R _) rfl rfl t4_held (t4_frei t4L t4LRumpf) σ' v hex
  refine ⟨σ', v, hex, h9, M', ext, hl, hf, ?_, ?_, ?_⟩
  · rw [hsp]; exact h5
  · rw [hsp]; exact h8
  · rw [hsp]; exact h6


/-! ## 11b. Witnesses: a loop left by `leave` after writing, `next`, and both
    paths of `let … else`

    `t5D` is `t4D` with five functions over two signatures: `sig 0` (no
    reason, returns `.int 0 100`) and `sig 1` (ONE reason, returns
    `.int 0 100`). `sigNr n` has `n` reasons.

        fn 0 (G, sig 0):  konto[0] := 5; return 3
        fn 1 (E, sig 1):  konto[0] := 4; return reason 0          -- fails
        fn 2 (L, sig 0):  forever progress () invariant true {
                            konto[1] := 8; if true { leave } else { } };
                          traverse konto invariant true {
                            if true { next } else { }; konto[2] := 6 };
                          return 9
        fn 3 (B, sig 0):  if true {
                            let x = H() else { return 1 };
                            let y = E() else { konto[2] := x; return 5 }
                          } else { };
                          return 9
        fn 4 (H, sig 1):  konto[1] := 2; return 6

    `L` writes before its `leave` (the `if` layer is peeled), and every
    `next` skips the write after it. `B` takes the NORMAL path of the first
    `let … else` (`H` returns `6`) and the ERROR path of the second (`E`
    answers reason `0`, the else block writes the bound `x` and returns). -/

def t5Sig (g : Nat) : Signatur Unit Empty Empty Empty where
  params := []
  erg := some (.int 0 100)
  gruende := g
  haelt := []
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []


end Gabbro.Grammatik
