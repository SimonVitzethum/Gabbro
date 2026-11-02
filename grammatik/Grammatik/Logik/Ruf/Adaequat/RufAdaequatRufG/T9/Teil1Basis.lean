module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T8
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T8a

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

def t5D : Deklaration where
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
  Fn := Fin 5
  sig := fun f => if f.val = 1 ∨ f.val = 4 then 1 else 0
  sigNr := t5Sig
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

def t5G : t5D.Fn := show Fin 5 from 0
def t5E : t5D.Fn := show Fin 5 from 1
def t5L : t5D.Fn := show Fin 5 from 2
def t5B : t5D.Fn := show Fin 5 from 3
def t5H : t5D.Fn := show Fin 5 from 4

theorem t5Darf : darf t5D () [] := fun _ h => absurd h List.not_mem_nil

def t5Idx (Γ : Ctx) (k : Int) (h0 : 0 ≤ k) (h1 : k ≤ 2) :
    Expr t5D Γ [] (.index (t5D.count ())) :=
  .widen h0 (by show k ≤ 3 - 1; omega) (.lit k)
def t5Lit (Γ : Ctx) (k : Int) (h0 : 0 ≤ k) (h1 : k ≤ 100) : Expr t5D Γ [] (t5D.typ () ()) :=
  .widen h0 h1 (.lit k)

theorem t5Hp (fn g : t5D.Fn) : RufPasst t5D (vertragVon t5D fn) (t5D.signatur g) [] where
  hw := fun _ _ => rfl
  hg := fun g _ => nomatch g
  hk := ⟨[], List.Perm.nil, List.Sublist.slnil⟩
  hh := fun L => nomatch L

/-- `G`: `konto[0] := 5; return 3`. -/
def t5GRumpf : Endblock t5D (vertragVon t5D t5G) false [] [] :=
  .cons (.assignSlot () () (t5Idx [] 0 (by decide) (by decide)) (t5Lit [] 5 (by decide) (by decide))
      rfl t5Darf)
    (.ret (.val (t5Lit [] 3 (by decide) (by decide))) List.Perm.nil)

/-- `E`: `konto[0] := 4; return reason 0` -- the failing callee. -/
def t5ERumpf : Endblock t5D (vertragVon t5D t5E) false [] [] :=
  .cons (.assignSlot () () (t5Idx [] 0 (by decide) (by decide)) (t5Lit [] 4 (by decide) (by decide))
      rfl t5Darf)
    (.retWhy ⟨0, by decide⟩ List.Perm.nil)

/-- `H`: `konto[1] := 2; return 6` -- a callee WITH an error channel that
    returns normally. -/
def t5HRumpf : Endblock t5D (vertragVon t5D t5H) false [] [] :=
  .cons (.assignSlot () () (t5Idx [] 1 (by decide) (by decide)) (t5Lit [] 2 (by decide) (by decide))
      rfl t5Darf)
    (.ret (.val (t5Lit [] 6 (by decide) (by decide))) List.Perm.nil)

/-- The `forever` body: `konto[1] := 8; if true { leave } else { }`. -/
def t5ForeverBody : Block t5D (vertragVon t5D t5L) true [] [] [] :=
  .cons (.assignSlot () () (t5Idx [] 1 (by decide) (by decide)) (t5Lit [] 8 (by decide) (by decide))
      rfl t5Darf)
    (.cons (.ite .tru (.cons (.leave rfl) .nil) .nil) .nil)

/-- The `traverse` body: `if true { next } else { }; konto[2] := 6`. -/
def t5TravBody : Block t5D (vertragVon t5D t5L) true [.index (t5D.count ())] [] [] :=
  .cons (.ite .tru (.cons (.next rfl) .nil) .nil)
    (.cons (.assignSlot () () (t5Idx _ 2 (by decide) (by decide))
      (t5Lit _ 6 (by decide) (by decide)) rfl t5Darf) .nil)

/-- `L`: the loops, then `return 9`. -/
def t5LRumpf : Endblock t5D (vertragVon t5D t5L) false [] [] :=
  .cons (.forever () .tru t5ForeverBody)
    (.cons (.traverse () .tru t5TravBody)
      (.ret (.val (t5Lit [] 9 (by decide) (by decide))) List.Perm.nil))

/-- The else block of the call of `E`: `konto[2] := x; return 5`. -/
def t5ErrE : Endblock t5D (vertragVon t5D t5B) false [.why (t5D.gruende t5E), .int 0 100]
    (nach t5D t5E (nach t5D t5H [])) :=
  .cons (.assignSlot () () (t5Idx _ 2 (by decide) (by decide)) (.var (.there .here)) rfl t5Darf)
    (.ret (.val (t5Lit _ 5 (by decide) (by decide))) List.Perm.nil)

/-- The else block of the call of `H`: `return 1`. -/
def t5ErrH : Endblock t5D (vertragVon t5D t5B) false [.why (t5D.gruende t5H)]
    (nach t5D t5H []) :=
  .ret (.val (t5Lit _ 1 (by decide) (by decide))) List.Perm.nil

/-- `let x = H() else { return 1 }; let y = E() else { konto[2] := x; return 5 }`. -/
def t5BindBlock : Block t5D (vertragVon t5D t5B) false [] [] [] :=
  .bindCallElse t5H .nil rfl (t5Hp t5B t5H) (by decide) t5ErrH
    (.bindCallElse t5E .nil rfl (t5Hp t5B t5E) (by decide) t5ErrE .nil)

/-- `B`: `if true { … } else { }; return 9`. -/
def t5BRumpf : Endblock t5D (vertragVon t5D t5B) false [] [] :=
  .cons (.ite .tru t5BindBlock .nil)
    (.ret (.val (t5Lit [] 9 (by decide) (by decide))) List.Perm.nil)

def t5P : Programm t5D where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun (f : Fin 5) => match f with
    | 0 => t5GRumpf
    | 1 => t5ERumpf
    | 2 => t5LRumpf
    | 3 => t5BRumpf
    | 4 => t5HRumpf

def t5O : Orakel t5D where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

/-- Start memory: every slot reads `0`. -/
def t5Sp : Speicher t5D :=
  ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- The frame below the caller. -/
def t5Unten : RufRahmenG t5D :=
  ⟨t5G, Env.nil, t5Sp.welt [], ⟨false, [], [], Env.nil,
    .ende (.ret (.val (t5Lit [] 9 (by decide) (by decide))) List.Perm.nil)⟩⟩

def t5M (fn : t5D.Fn) (b : Endblock t5D (vertragVon t5D fn) false [] []) : RufMaschineG t5D :=
  ⟨t5Sp, fun _ => ⟨[t5Unten], ⟨fn, Env.nil, t5Sp.welt [], ⟨false, [], [], Env.nil, .ende b⟩⟩,
    [], []⟩, [], t5Sp.welt []⟩

theorem t5_frei (fn : t5D.Fn) (b : Endblock t5D (vertragVon t5D fn) false [] []) :
    ∀ L : t5D.Lock, (fun _ => False) L → RufFreiG (t5M fn b) 0 L := fun L => nomatch L

theorem t5_held : HeldGenau ([] : List (Res t5D)) (offen ([] : List (Ereignis t5D))) :=
  fun L => nomatch L

theorem t5H_tief (A : t5D.Lock → Prop) : Tief t5P A 1 t5H :=
  show EndR A (Tief t5P A 0) t5HRumpf from
    EndR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) (EndR.ret _ _)

theorem t5E_tief (A : t5D.Lock → Prop) : Tief t5P A 1 t5E :=
  show EndR A (Tief t5P A 0) t5ERumpf from
    EndR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) (EndR.retWhy (Γ := []) _ _)

theorem t5LRumpf_R (A : t5D.Lock → Prop) : EndR A (Tief t5P A 1) t5LRumpf :=
  EndR.cons _ _
    (StmtR.forever _ _ _
      (BlockR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _))
        (BlockR.cons _ _
          (StmtR.ite _ _ _ (BlockR.cons _ _ (StmtR.leave rfl) BlockR.nil) BlockR.nil)
          BlockR.nil)))
    (EndR.cons _ _
      (StmtR.traverse _ _ _
        (BlockR.cons _ _
          (StmtR.ite _ _ _ (BlockR.cons _ _ (StmtR.next rfl) BlockR.nil) BlockR.nil)
          (BlockR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) BlockR.nil)))
      (EndR.ret _ _))

theorem t5BRumpf_R (A : t5D.Lock → Prop) : EndR A (Tief t5P A 1) t5BRumpf :=
  EndR.cons _ _
    (StmtR.ite _ _ _
      (BlockR.bindCallElse _ _ _ _ _ _ _ (t5H_tief A) (EndR.ret _ _)
        (BlockR.bindCallElse _ _ _ _ _ _ _ (t5E_tief A)
          (EndR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) (EndR.ret _ _))
          BlockR.nil))
      BlockR.nil)
    (EndR.ret _ _)

/-- The sequential run of the loop body with one `forever` pass: the pass
    writes slot 1 and leaves; every `traverse` iteration takes `next`, so
    slot 2 stays `0`; value 9. -/
theorem t5L_exec : ∃ (σ' : World t5D) (v : ErgVal t5D (vertragVon t5D t5L).erg),
    execEnd t5O 1 (rufRumpf t5P t5O 1 1) t5LRumpf ((t5M t5L t5LRumpf).weltVon 0) Env.nil =
      .zurueck σ' v ∧
    (σ'.slots () 1 ()).n = 8 ∧ (σ'.slots () 2 ()).n = 0 ∧ (show Zahl 0 100 from v).n = 9 :=
  ⟨_, _, rfl, rfl, rfl, rfl⟩

/-- The sequential run of the bind-else caller: `H` writes slot 1 and
    returns 6 (normal path, `x = 6`); `E` writes slot 0 and answers reason 0
    (error path): the else block writes `x` to slot 2 and returns 5. -/
theorem t5B_exec : ∃ (σ' : World t5D) (v : ErgVal t5D (vertragVon t5D t5B).erg),
    execEnd t5O 0 (rufRumpf t5P t5O 0 1) t5BRumpf ((t5M t5B t5BRumpf).weltVon 0) Env.nil =
      .zurueck σ' v ∧
    (σ'.slots () 0 ()).n = 4 ∧ (σ'.slots () 1 ()).n = 2 ∧ (σ'.slots () 2 ()).n = 6 ∧
    (show Zahl 0 100 from v).n = 5 :=
  ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩


end Gabbro.Grammatik
