/- Part 9 of 10 of `RufAdaequatRufG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatRufG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T8

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
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
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

/-- **Witness for `rufG_adaequat_ruf` with `forever`, `leave` and `next`.**
    All premises jointly, on the loop program at depth 1 with one pass:
    the `forever` pass WRITES slot 1 (`0 -> 8`) and then leaves through an
    `if` (the machine peels the `if` layer and fires `dannLeaveEwig`);
    every `traverse` iteration exits by `next` through an `if` (peel,
    `dannNextTrav`), skipping the write behind it -- slot 2 stays `0`. The
    machine pops the frame with the sequential value `9` and memory. -/
theorem rufG_adaequat_ruf_zeuge_leave :
    ∃ (σ' : World t5D) (v : ErgVal t5D (vertragVon t5D t5L).erg),
      execEnd t5O 1 (rufRumpf t5P t5O 1 1) t5LRumpf ((t5M t5L t5LRumpf).weltVon 0) Env.nil =
        .zurueck σ' v ∧
      (((t5M t5L t5LRumpf).weltVon 0).slots () 1 ()).n = 0 ∧ (show Zahl 0 100 from v).n = 9 ∧
      ∃ (M' : RufMaschineG t5D) (ext : List (RufEreignisF t5D)),
        RufLaufG t5P t5O 1 0 (t5M t5L t5LRumpf) M' ∧
        M'.faeden 0 = ⟨[], t5Unten, σ'.spur,
          RufEreignisF.rueck t5L Env.nil v (t5Sp.welt []) σ' :: (ext ++ [])⟩ ∧
        (M'.speicher.slots () 1 ()).n = 8 ∧ (M'.speicher.slots () 2 ()).n = 0 ∧
        (∀ g, g ≠ 0 → M'.faeden g = (t5M t5L t5LRumpf).faeden g) := by
  obtain ⟨σ', v, hex, h8, h0, h9⟩ := t5L_exec
  obtain ⟨M', ext, hl, hf, hsp, hfr⟩ := rufG_adaequat_ruf t5P t5O 1 1 (t5M t5L t5LRumpf) 0 t5L
    Env.nil (t5Sp.welt []) t5Unten [] [] [] Env.nil t5LRumpf (fun _ => False)
    (t5LRumpf_R _) rfl rfl t5_held (t5_frei t5L t5LRumpf) σ' v hex
  refine ⟨σ', v, hex, rfl, h9, M', ext, hl, hf, ?_, ?_, hfr⟩
  · rw [hsp]; exact h8
  · rw [hsp]; exact h0

/-- **Witness for `rufG_adaequat_ruf` with both paths of `let … else`.**
    All premises jointly, on the bind-else program at depth 1: the first
    call returns normally (`H` writes slot 1, `x = 6`, machine `rueckBind`
    into `wartetSonst`), the second answers a reason (`E` writes slot 0,
    machine `rueckConsGrund` logs `grund` and resumes the caller's else
    block with the reason bound), the else block writes `x` to slot 2 and
    returns 5. The machine pops with `5` and all three slots moved. -/
theorem rufG_adaequat_ruf_zeuge_sonst :
    ∃ (σ' : World t5D) (v : ErgVal t5D (vertragVon t5D t5B).erg),
      execEnd t5O 0 (rufRumpf t5P t5O 0 1) t5BRumpf ((t5M t5B t5BRumpf).weltVon 0) Env.nil =
        .zurueck σ' v ∧ (show Zahl 0 100 from v).n = 5 ∧
      ∃ (M' : RufMaschineG t5D) (ext : List (RufEreignisF t5D)),
        RufLaufG t5P t5O 0 0 (t5M t5B t5BRumpf) M' ∧
        M'.faeden 0 = ⟨[], t5Unten, σ'.spur,
          RufEreignisF.rueck t5B Env.nil v (t5Sp.welt []) σ' :: (ext ++ [])⟩ ∧
        (M'.speicher.slots () 0 ()).n = 4 ∧ (M'.speicher.slots () 1 ()).n = 2 ∧
        (M'.speicher.slots () 2 ()).n = 6 := by
  obtain ⟨σ', v, hex, h4, h2, h6, h5⟩ := t5B_exec
  obtain ⟨M', ext, hl, hf, hsp, _⟩ := rufG_adaequat_ruf t5P t5O 0 1 (t5M t5B t5BRumpf) 0 t5B
    Env.nil (t5Sp.welt []) t5Unten [] [] [] Env.nil t5BRumpf (fun _ => False)
    (t5BRumpf_R _) rfl rfl t5_held (t5_frei t5B t5BRumpf) σ' v hex
  refine ⟨σ', v, hex, h5, M', ext, hl, hf, ?_, ?_, ?_⟩
  · rw [hsp]; exact h4
  · rw [hsp]; exact h2
  · rw [hsp]; exact h6

/-! ## 12. AGREEMENT (formerly a finding): a pop never restores a waiting caller

    Before the repair, `rueck`, `rueckCons` and `dannRet` popped the callee
    frame and restored the caller frame VERBATIM, also when the caller
    waited for a bound value (residue `wartet rest k`): the restored head
    `wartet …` has no rule, the thread was stuck for good (`wartet_steht`,
    `wartet_lauf` below), while the sequential semantics binds the value and
    continues. The three verbatim pops now demand a caller that does not
    wait (`hnw : caller.wartend = false`, `RufMaschineG.lean`); a waiting
    caller is resumed only by a binding pop. `rufG_nie_wartend` shows that
    no reachable head waits; `wartet_einig` checks it on the bind witness
    from its waiting state. -/

/-- At a head `wartet rest k` no step of `f` changes frame, stack or log (the
    bare lock steps that fired there were removed from G on 2026-09-13). -/
theorem wartet_steht {P : Programm D} {O : Orakel D} {passes : Nat}
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (z : RufFadenG D) (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (rest : Block D (vertragVon D z.kopf.f) l (τ :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hR : z.kopf.rest = ⟨l, Γ, Λ, ρ, .wartet rest k⟩) :
    ∃ sp, M'.faeden f = ⟨z.stapel, z.kopf, sp, z.log⟩ := by
  subst hz
  cases hs with
  | blatt _ _ _ _ _ _ _ hleaf hhead _ _ _ _ hstep => kopfweg
  | ruf _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rueck _ _ hpop _ _ _ _ _ hhead => kopfweg
  | endeEntf _ _ _ _ _ _ _ _ hhead => kopfweg
  | endeForm _ _ _ _ _ _ _ hhead => kopfweg
  | dannBlatt _ _ _ _ _ _ _ _ _ hleaf hhead _ _ _ _ hstep => kopfweg
  | dannLeer _ _ _ _ _ hhead => kopfweg
  | dannIteWahr _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannIteFalsch _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannOnOptionSome _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannOnOptionNone _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannOnTagSome _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ _ _ _ _ hw => kopfweg
  | dannOnTagNone _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ _ _ hw => kopfweg
  | dannOnGrund _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ _ hw => kopfweg
  | endeBind _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannBind _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannNarrowOk _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannNarrowElse _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannPruefWahr _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannPruefFalsch _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannBreaking _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannLocks _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | freiGib _ _ _ _ _ _ hhead => kopfweg
  | schrumpfVergiss _ _ _ _ _ _ _ hhead => kopfweg
  | dannTrav _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | travNext _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | travFort _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | travDone _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannRetry _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | wiederUeber _ _ _ _ _ _ _ _ hhead => kopfweg
  | wiederWeiter _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | wiederSchritt _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | wiederFort _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannForever _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | ewigWeiter _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | ewigFort _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rufDann _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannCallInd _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rufCallInd _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannBindCall _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannBindCallInd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannBindCallElse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rueckBind _ _ hpop _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannLeaveTrav _ _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep _ _ _ hs₁ hw => kopfweg
  | dannNextTrav _ _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannLeaveWieder _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannNextWieder _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannLeaveEwig _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannNextEwig _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | peelDannLeave _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelDannNext _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelSchrumpfLeave _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelSchrumpfNext _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelFreiLeave _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelFreiNext _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelAbbruchLeave _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelAbbruchNext _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannRet _ _ _ _ _ _ _ _ _ hhead _ _ hpop => kopfweg
  | rueckCons _ _ hpop _ _ _ _ _ _ hhead => kopfweg
  | dannRetBind _ _ _ _ _ _ _ _ _ hhead _ _ hpop => kopfweg
  | rueckConsBind _ _ _ _ _ _ _ hhead _ _ hpop => kopfweg
  | dannRegLies _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannRegLiesElseWahr _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hs₁ hw => kopfweg
  | dannRegLiesElseFalsch _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hs₁ hw => kopfweg
  | dannAwaits _ _ _ _ _ _ _ _ _ _ _ _ hhead _ _ hs₁ => kopfweg
  | dannExchange _ _ _ _ _ _ hw _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleitLit _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannGleitVon _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleitNarrowOk _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleitNarrowElse _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannBindAxiom _ _ _ _ _ _ _ _ hw _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannBindAxiomElseOk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannBindAxiomElseGrund _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | endeBindAxiomElseOk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | endeBindAxiomElseGrund _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | endeBindAxiom _ _ _ _ _ _ _ hw _ _ _ _ _ hhead _ hs₁ => kopfweg
  | rueckGrund _ _ _ hhead => kopfweg
  | rueckConsGrund _ _ _ _ hhead => kopfweg
  | dannRetGrund _ _ _ _ _ hhead => kopfweg

/-- A thread whose head waits stays so, and logs nothing, along any run. -/
theorem wartet_lauf {P : Programm D} {O : Orakel D} {passes : Nat} {f : Faden}
    {M M' : RufMaschineG D} (hl : RufLaufG P O passes f M M')
    (stapel : List (RufRahmenG D)) (kopf : RufRahmenG D) (log : List (RufEreignisF D))
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (rest : Block D (vertragVon D kopf.f) l (τ :: Γ) Λ Λ')
    (k : GRest D (vertragVon D kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hR : kopf.rest = ⟨l, Γ, Λ, ρ, .wartet rest k⟩) :
    ∀ sp0, M.faeden f = ⟨stapel, kopf, sp0, log⟩ →
      ∃ sp, M'.faeden f = ⟨stapel, kopf, sp, log⟩ := by
  induction hl with
  | refl => intro sp0 h; exact ⟨sp0, h⟩
  | schritt hs _ ih =>
    intro sp0 h
    obtain ⟨sp, e⟩ := wartet_steht hs _ h rest k ρ hR
    exact ih sp e

/-- The function an event belongs to. -/
def RufEreignisF.fnVon : RufEreignisF D → D.Fn
  | .eintritt f .. => f
  | .rueck f .. => f
  | .why f .. => f

/-- Runs of one thread keep the no-waiting-head invariant of every thread. -/
theorem rufLaufG_sauber {P : Programm D} {O : Orakel D} {passes : Nat} {f : Faden}
    {M M' : RufMaschineG D} (hl : RufLaufG P O passes f M M')
    (h : ∀ g, RufFadenSauberG (M.faeden g)) : ∀ g, RufFadenSauberG (M'.faeden g) := by
  induction hl with
  | refl => exact h
  | schritt hs _ ih => exact ih (rufSchrittG_sauber hs h)

/-- The witness machines satisfy the invariant: `ende` heads above `t4Unten`. -/
theorem t4M_sauber (fn : t4D.Fn) (b : Endblock t4D (vertragVon t4D fn) false [] []) :
    ∀ g, RufFadenSauberG ((t4M fn b).faeden g) := by
  intro g
  refine ⟨rfl, ?_⟩
  intro r hr
  simp only [t4M, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rfl

/-- The bind witness up to its waiting state: `endeEntf`, `dannIteWahr`,
    `dannBindCall` -- the caller frame of `t4B` now WAITS (`wartet`) below
    the callee frame of `t4G`. -/
theorem t4B_wartet :
    ∃ M3 : RufMaschineG t4D, RufLaufG t4P t4O 0 0 (t4M t4B t4BRumpf) M3 ∧
      ∃ caller : RufRahmenG t4D, (M3.faeden 0).stapel = [caller, t4Unten] ∧
        caller.f = t4B ∧ caller.wartend = true ∧ (M3.faeden 0).kopf.f = t4G := by
  have hZ0 : ZustandG (t4M t4B t4BRumpf) 0 [t4Unten] t4B Env.nil (t4Sp.welt []) []
      (Env.nil : Env t4D []) (.ende t4BRumpf) ((t4M t4B t4BRumpf).weltVon 0) := ⟨rfl, rfl⟩
  obtain ⟨M1, hs1, hZ1⟩ := w_endeEntf (P := t4P) (O := t4O) (passes := 0) hZ0.1
    (.ite .tru t4BindBlock .nil) (.ret (.val (t4Lit 9 (by decide) (by decide))) List.Perm.nil)
    Env.nil rfl rfl
  obtain ⟨M2, hs2, hZ2⟩ := w_iteWahr (P := t4P) (O := t4O) (passes := 0) hZ1.1
    .tru t4BindBlock .nil .nil
    (.ende (.ret (.val (t4Lit 9 (by decide) (by decide))) List.Perm.nil)) Env.nil rfl rfl
    (fun L => nomatch L)
  obtain ⟨M3, hs3, hZ3⟩ := w_bindCall (P := t4P) (O := t4O) (passes := 0) hZ2.1
    t4G .nil rfl (t4Hp t4B) rfl (.cons (.assignSlot () () t4Idx1x (.var .here) rfl t4Darf) .nil)
    (.dann .nil (.ende (.ret (.val (t4Lit 9 (by decide) (by decide))) List.Perm.nil))) Env.nil
    rfl (fun L => nomatch L)
  refine ⟨M3, RufLaufG.schritt hs1 (RufLaufG.schritt hs2 (RufLaufG.einzeln hs3)), _,
    by rw [hZ3.1], rfl, rfl, by rw [hZ3.1]⟩

/-- **AGREEMENT (formerly the finding `befund_wartet`).** On the bind
    witness, from the state in which the caller of `t4B` WAITS below the
    callee: no machine reachable by steps of the thread has a waiting head
    (the verbatim pops can no longer restore the waiting caller; the
    deadlock run is gone), and the sequential semantics returns `9`. -/
theorem wartet_einig :
    (∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4B).erg),
      execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4BRumpf ((t4M t4B t4BRumpf).weltVon 0) Env.nil =
        .zurueck σ' v ∧ (show Zahl 0 100 from v).n = 9) ∧
    ∃ M3 : RufMaschineG t4D, RufLaufG t4P t4O 0 0 (t4M t4B t4BRumpf) M3 ∧
      (∃ caller : RufRahmenG t4D, (M3.faeden 0).stapel = [caller, t4Unten] ∧
        caller.f = t4B ∧ caller.wartend = true) ∧
      ∀ M' : RufMaschineG t4D, RufLaufG t4P t4O 0 0 M3 M' →
        ∀ g, (M'.faeden g).kopf.wartend = false := by
  refine ⟨⟨_, _, rfl, rfl⟩, ?_⟩
  obtain ⟨M3, hl3, caller, hst, hf, hw, _⟩ := t4B_wartet
  refine ⟨M3, hl3, ⟨caller, hst, hf, hw⟩, ?_⟩
  intro M' hl g
  exact (rufLaufG_sauber (hl3.trans hl) (t4M_sauber t4B t4BRumpf) g).kopf_wartend


/-! ## 13. NOTE: the machine realises `rufRumpf`, not `rufAt`

    The program semantics `exec` calls through `rufAt`, which checks the
    callee's `requires` (and `ensures`, and the owed invariants) and READS
    their places. The machine checks no contract (booked in
    `RufMaschineG.lean`'s CUTS). So G agrees with `exec` only where every
    contract holds and reads nothing -- a design cut of G, not a defect of
    its steps, shown here on the plain witness with `requires false`. -/

/-- The plain witness program with every `requires` false. -/
def t4Pk : Programm t4D :=
  { t4P with requires := fun _ => .fls }

theorem befund_vertrag :
    execEnd t4O 0 (rufAt t4Pk t4O 0 2) t4FRumpf ((t4M t4F t4FRumpf).weltVon 0) Env.nil =
      .logik (.vorbedingung t4G) ∧
    ∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4F).erg),
      execEnd t4O 0 (rufRumpf t4Pk t4O 0 1) t4FRumpf ((t4M t4F t4FRumpf).weltVon 0) Env.nil =
        .zurueck σ' v ∧
      ∃ (M' : RufMaschineG t4D) (ext : List (RufEreignisF t4D)),
        RufLaufG t4Pk t4O 0 0 (t4M t4F t4FRumpf) M' ∧
        M'.faeden 0 = ⟨[], t4Unten, σ'.spur,
          RufEreignisF.rueck t4F Env.nil v (t4Sp.welt []) σ' :: (ext ++ [])⟩ := by
  refine ⟨rfl, ?_⟩
  have hex : ∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4F).erg),
      execEnd t4O 0 (rufRumpf t4Pk t4O 0 1) t4FRumpf ((t4M t4F t4FRumpf).weltVon 0) Env.nil =
        .zurueck σ' v := ⟨_, _, rfl⟩
  obtain ⟨σ', v, hex⟩ := hex
  have hG : Tief t4Pk (fun _ => False) 1 t4G :=
    show EndR (fun _ => False) (Tief t4Pk (fun _ => False) 0) t4GRumpf from
      EndR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) (EndR.ret _ _)
  have hb : EndR (fun _ => False) (Tief t4Pk (fun _ => False) 1) t4FRumpf :=
    EndR.cons _ _ (StmtR.call _ t4G rfl hG)
      (EndR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) (EndR.ret _ _))
  obtain ⟨M', ext, hl, hf, _, _⟩ := rufG_adaequat_ruf t4Pk t4O 0 1 (t4M t4F t4FRumpf) 0 t4F
    Env.nil (t4Sp.welt []) t4Unten [] [] [] Env.nil t4FRumpf (fun _ => False) hb rfl rfl t4_held
    (t4_frei t4F t4FRumpf) σ' v hex
  exact ⟨σ', v, hex, M', ext, hl, hf⟩



end Gabbro.Grammatik
