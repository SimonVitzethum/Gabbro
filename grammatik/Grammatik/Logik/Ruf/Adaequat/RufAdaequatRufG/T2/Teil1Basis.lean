module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T1

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

section Inv

variable {V : Vertrag D} {A : D.Lock → Prop} {C : D.Fn → Prop} {mr l : Bool} {Γ : Ctx}

theorem StmtR.ite_inv {Λ Λ' : List (Res D)} {c : Expr D Γ Λ .bool}
    {t e : Block D V l Γ Λ Λ'} (h : StmtR A C mr (.ite c t e)) :
    BlockR A C mr t ∧ BlockR A C mr e := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp only [Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | call _ _ hg _ => simp only [Stmt.rufZiel, reduceCtorEq] at hg
  | ite _ _ _ ht he => exact ⟨ht, he⟩

theorem StmtR.onOption_inv {Λ Λ' : List (Res D)} {n : Int} {o : Expr D Γ Λ (.opt n)}
    {p : Block D V l (.index n :: Γ) Λ Λ'} {a : Block D V l Γ Λ Λ'}
    (h : StmtR A C mr (.onOption o p a)) : BlockR A C mr p ∧ BlockR A C mr a := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp only [Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | call _ _ hg _ => simp only [Stmt.rufZiel, reduceCtorEq] at hg
  | onOption _ _ _ hp ha => exact ⟨hp, ha⟩

theorem StmtR.onTag_inv {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    {v : Expr D Γ Λ (.sum cs)} {arms : Arms D V l Γ Λ Λ' cs}
    (h : StmtR A C mr (.onTag v arms)) : ArmsR A C mr arms := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp only [Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | call _ _ hg _ => simp only [Stmt.rufZiel, reduceCtorEq] at hg
  | onTag _ _ ha => exact ha

theorem StmtR.onGrund_inv {Λ Λ' : List (Res D)} {n : Nat}
    {r : Expr D Γ Λ (.why n)} {arms : GrundArms D V l Γ Λ Λ' n}
    (h : StmtR A C mr (.onWhy r arms)) : GrundArmsR A C mr arms := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp only [Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | call _ _ hg _ => simp only [Stmt.rufZiel, reduceCtorEq] at hg
  | onWhy _ _ ha => exact ha

theorem StmtR.breaking_inv {Λ Λ' : List (Res D)} {i : D.Inv}
    {body : Block D V l Γ Λ Λ'} (h : StmtR A C mr (.breaking i body)) : BlockR A C mr body := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp only [Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | call _ _ hg _ => simp only [Stmt.rufZiel, reduceCtorEq] at hg
  | breaking _ _ hb => exact hb

theorem StmtR.locks_inv {Λ : List (Res D)} {L : D.Lock}
    {hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L}
    {body : Block D V l Γ (.held L :: Λ) (.held L :: Λ)}
    (h : StmtR A C mr (.locks L hr body)) :
    A L ∧ BlockR A C false body ∧ ∀ c, V.boden = some c → c ≤ D.rang L := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp only [Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | call _ _ hg _ => simp only [Stmt.rufZiel, reduceCtorEq] at hg
  | locks _ _ _ hbo hA hb => exact ⟨hA, hb, hbo⟩

theorem StmtR.ret_inv {Λ : List (Res D)} {e : ErgExpr D Γ Λ V.erg} {hΛ : Λ.Perm V.ende}
    (h : StmtR A C mr (.ret (l := l) e hΛ)) : mr = true := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp only [Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | call _ _ hg _ => simp only [Stmt.rufZiel, reduceCtorEq] at hg
  | ret _ _ => rfl

theorem BlockR.cons_inv {Λ Λ' Λ'' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Block D V l Γ Λ' Λ''} (h : BlockR A C mr (.cons s rest)) :
    StmtR A C mr s ∧ BlockR A C mr rest := by
  cases h with
  | cons _ _ hs hr => exact ⟨hs, hr⟩

theorem BlockR.bind_inv {Λ Λ' : List (Res D)} {τ : Ty} {e : Expr D Γ Λ τ}
    {rest : Block D V l (τ :: Γ) Λ Λ'} (h : BlockR A C mr (.bind e rest)) : BlockR A C mr rest := by
  cases h with
  | bind _ _ hr => exact hr

theorem BlockR.regLies_inv {Λ Λ' : List (Res D)} {r : D.Reg}
    {hk : (D.rklasse r).lesbar = true} {rest : Block D V l (D.rtyp r :: Γ) Λ Λ'}
    (h : BlockR A C mr (.regRead r hk rest)) : BlockR A C mr rest := by
  cases h with
  | regRead _ _ _ hr => exact hr

theorem BlockR.awaits_inv {Λ Λ' : List (Res D)} {g : D.Glob} {payload : List D.Glob}
    {hp : payload = D.nutzlast g} {hL : gdarf D g Λ} {hat : D.atomar g = true}
    {rest : Block D V l (D.gtyp g :: Γ) Λ Λ'}
    (h : BlockR A C mr (.awaits g payload hp hL hat rest)) : BlockR A C mr rest := by
  cases h with
  | awaits _ _ _ _ _ _ hr => exact hr

theorem BlockR.exchange_inv {Λ Λ' : List (Res D)} {g : D.Glob}
    {neu : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)} {hw : V.gschreibt g = true}
    {hL : gdarf D g Λ} {rest : Block D V l (D.gtyp g :: Γ) Λ Λ'}
    (h : BlockR A C mr (.exchange g neu hw hL rest)) : BlockR A C mr rest := by
  cases h with
  | exchange _ _ _ _ _ hr => exact hr

theorem BlockR.gleit_inv {Λ Λ' : List (Res D)} {l1 h1 l2 h2 : Int × Int} {op : GleitOp}
    {a : Expr D Γ Λ (.fl l1 h1)} {b : Expr D Γ Λ (.fl l2 h2)} {lo hi : Int × Int}
    {rest : Block D V l (.fl lo hi :: Γ) Λ Λ'}
    (h : BlockR A C mr (.float op a b lo hi rest)) : BlockR A C mr rest := by
  cases h with
  | float _ _ _ _ _ _ hr => exact hr

theorem BlockR.gleitLit_inv {Λ Λ' : List (Res D)} {q lo hi : Int × Int}
    {rest : Block D V l (.fl lo hi :: Γ) Λ Λ'}
    (h : BlockR A C mr (.floatLit q lo hi rest)) : BlockR A C mr rest := by
  cases h with
  | floatLit _ _ _ _ hr => exact hr

theorem BlockR.gleitVon_inv {Λ Λ' : List (Res D)} {l1 h1 : Int}
    {e : Expr D Γ Λ (.int l1 h1)} {lo hi : Int × Int}
    {rest : Block D V l (.fl lo hi :: Γ) Λ Λ'}
    (h : BlockR A C mr (.floatOf e lo hi rest)) : BlockR A C mr rest := by
  cases h with
  | floatOf _ _ _ _ hr => exact hr

theorem BlockR.regLiesElse_inv {Λ Λ' : List (Res D)} {r : D.Reg}
    {hk : (D.rklasse r).lesbar = true} {zusage : Expr D (D.rtyp r :: Γ) Λ .bool}
    {sonst : Endblock D V l Γ Λ} {rest : Block D V l (D.rtyp r :: Γ) Λ Λ'}
    (h : BlockR A C mr (.regReadElse r hk zusage sonst rest)) :
    mr = true ∧ BlockR A C true rest ∧ EndR A C sonst ∧ l = false := by
  cases h with
  | regReadElse _ _ _ _ _ hs hr => exact ⟨rfl, hr, hs, rfl⟩

theorem BlockR.narrow_inv {Λ Λ' : List (Res D)} {lo hi : Int}
    {e : Expr D Γ Λ (.int lo hi)} {lo' hi' : Int} {sonst : Endblock D V l Γ Λ}
    {rest : Block D V l (.int lo' hi' :: Γ) Λ Λ'}
    (h : BlockR A C mr (.narrow e lo' hi' sonst rest)) :
    mr = true ∧ BlockR A C true rest ∧ EndR A C sonst ∧ l = false := by
  cases h with
  | narrow _ _ _ _ _ hs hr => exact ⟨rfl, hr, hs, rfl⟩

theorem BlockR.pruefung_inv {Λ Λ' : List (Res D)} {c : Expr D Γ Λ .bool}
    {sonst : Endblock D V l Γ Λ} {rest : Block D V l Γ Λ Λ'}
    (h : BlockR A C mr (.check c sonst rest)) :
    mr = true ∧ BlockR A C true rest ∧ EndR A C sonst ∧ l = false := by
  cases h with
  | check _ _ _ hs hr => exact ⟨rfl, hr, hs, rfl⟩

theorem BlockR.gleitNarrow_inv {Λ Λ' : List (Res D)} {l1 h1 : Int × Int}
    {e : Expr D Γ Λ (.fl l1 h1)} {lo hi : Int × Int} {sonst : Endblock D V l Γ Λ}
    {rest : Block D V l (.fl lo hi :: Γ) Λ Λ'}
    (h : BlockR A C mr (.floatNarrow e lo hi sonst rest)) :
    mr = true ∧ BlockR A C true rest ∧ EndR A C sonst ∧ l = false := by
  cases h with
  | floatNarrow _ _ _ _ _ hs hr => exact ⟨rfl, hr, hs, rfl⟩

theorem ArmsR.cons_inv {Λ Λ' : List (Res D)} {c : Option Ty}
    {cs : List (Option Ty)} {b : Block D V l (ArmCtx Γ c) Λ Λ'}
    {rest : Arms D V l Γ Λ Λ' cs} (h : ArmsR A C mr (.cons b rest)) :
    BlockR A C mr b ∧ ArmsR A C mr rest := by
  cases h with
  | cons _ _ hb hr => exact ⟨hb, hr⟩

theorem GrundArmsR.cons_inv {Λ Λ' : List (Res D)} {n : Nat}
    {b : Block D V l Γ Λ Λ'} {rest : GrundArms D V l Γ Λ Λ' n}
    (h : GrundArmsR A C mr (.cons b rest)) : BlockR A C mr b ∧ GrundArmsR A C mr rest := by
  cases h with
  | cons _ _ hb hr => exact ⟨hb, hr⟩

theorem EndR.ret_inv {Λ : List (Res D)} {e : ErgExpr D Γ Λ V.erg} {hΛ : Λ.Perm V.ende}
    (h : EndR A C (.ret (l := l) e hΛ)) : l = false := by
  cases h with
  | ret _ _ => rfl

theorem EndR.cons_inv {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Endblock D V l Γ Λ'} (h : EndR A C (.cons s rest)) :
    StmtR A C true s ∧ EndR A C rest ∧ l = false := by
  cases h with
  | cons _ _ hs hr => exact ⟨hs, hr, rfl⟩

theorem EndR.bind_inv {Λ : List (Res D)} {τ : Ty} {e : Expr D Γ Λ τ}
    {rest : Endblock D V l (τ :: Γ) Λ} (h : EndR A C (.bind e rest)) : EndR A C rest := by
  cases h with
  | bind _ _ hr => exact hr

/-- A covered statement that is a call admits its callee. -/
theorem StmtR.call_inv' {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'} (h : StmtR A C mr s)
    (g : D.Fn) (hg : s.rufZiel = some g) : C g := by
  cases h with
  | blatt _ hb => cases hb <;> simp only [Stmt.rufZiel, reduceCtorEq] at hg
  | call s g' hg' hC =>
    rw [hg'] at hg
    cases hg
    exact hC
  | _ => simp only [Stmt.rufZiel, reduceCtorEq] at hg

theorem StmtR.call_inv {Λ : List (Res D)} {g : D.Fn} {args : Args D Γ Λ (D.params g)}
    {hp : RufPasst D V (D.signatur g) Λ} {hr : D.gruende g = 0}
    (h : StmtR A C mr (.call (l := l) g args hp hr)) : C g :=
  h.call_inv' g rfl

theorem BlockR.bindCall_inv {Λ Λ' : List (Res D)} {τ : Ty} {g : D.Fn}
    {args : Args D Γ Λ (D.params g)} {he : D.erg g = some τ}
    {hp : RufPasst D V (D.signatur g) Λ} {hr : D.gruende g = 0}
    {rest : Block D V l (τ :: Γ) (nach D g Λ) Λ'}
    (h : BlockR A C mr (.bindCall g args he hp hr rest)) : C g ∧ BlockR A C mr rest := by
  generalize hb : Block.bindCall g args he hp hr rest = b at h
  cases h with
  | bindCall g' args' he' hp' hr' rest' hC hrest =>
    cases hb
    exact ⟨hC, hrest⟩
  | _ => cases hb

theorem StmtR.traverse_inv {Λ : List (Res D)} {t : D.Tab} {inv : Expr D Γ Λ .bool}
    {body : Block D V true (.index (D.count t) :: Γ) Λ Λ}
    (h : StmtR A C mr (.traverse (l := l) t inv body)) : BlockR A C mr body := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp only [Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | call _ _ hg _ => simp only [Stmt.rufZiel, reduceCtorEq] at hg
  | traverse _ _ _ hb => exact hb

theorem StmtR.retry_inv {Λ : List (Res D)} {n : Nat} {bis : Expr D Γ Λ .bool}
    {body : Block D V true Γ Λ Λ} {ueber : Block D V l Γ Λ Λ}
    (h : StmtR A C mr (.retry n bis body ueber)) : BlockR A C mr body ∧ BlockR A C mr ueber := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp only [Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | call _ _ hg _ => simp only [Stmt.rufZiel, reduceCtorEq] at hg
  | retry _ _ _ _ hb hu => exact ⟨hb, hu⟩

theorem StmtR.forever_inv {Λ : List (Res D)} {a : D.Annahme} {inv : Expr D Γ Λ .bool}
    {body : Block D V true Γ Λ Λ}
    (h : StmtR A C mr (.forever (l := l) a inv body)) : BlockR A C mr body := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp only [Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | call _ _ hg _ => simp only [Stmt.rufZiel, reduceCtorEq] at hg
  | forever _ _ _ hb => exact hb

theorem StmtR.retGrund_inv {Λ : List (Res D)} {r : Fin V.gruende} {hΛ : Λ.Perm V.ende}
    (h : StmtR A C mr (.retWhy (l := l) (Γ := Γ) r hΛ)) : mr = true := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp only [Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | call _ _ hg _ => simp only [Stmt.rufZiel, reduceCtorEq] at hg
  | retWhy _ _ => rfl

theorem BlockR.bindCallElse_inv {Λ Λ' : List (Res D)} {τ : Ty} {g : D.Fn}
    {args : Args D Γ Λ (D.params g)} {he : D.erg g = some τ}
    {hp : RufPasst D V (D.signatur g) Λ} {hr : 0 < D.gruende g}
    {err : Endblock D V l (.why (D.gruende g) :: Γ) (nach D g Λ)}
    {rest : Block D V l (τ :: Γ) (nach D g Λ) Λ'}
    (h : BlockR A C mr (.bindCallElse g args he hp hr err rest)) :
    C g ∧ EndR A C err ∧ BlockR A C true rest ∧ mr = true ∧ l = false := by
  generalize hb : Block.bindCallElse g args he hp hr err rest = b at h
  cases h with
  | bindCallElse g' args' he' hp' hr' err' rest' hC herr hrest =>
    cases hb
    exact ⟨hC, herr, hrest, rfl, rfl⟩
  | _ => cases hb

/-- A covered end block stands at loop level `false`. -/
theorem EndR.l_false {Λ : List (Res D)} {e : Endblock D V l Γ Λ} (h : EndR A C e) :
    l = false := by
  cases h <;> rfl

end Inv
theorem EndR.gleitLit_inv {Λ : List (Res D)} {q lo hi : Int × Int}
    {rest : Endblock D V l (.fl lo hi :: Γ) Λ}
    (h : EndR A C (.floatLit q lo hi rest)) : EndR A C rest := by
  cases h with
  | floatLit _ _ _ _ hr => exact hr


theorem EndR.gleitVon_inv {Λ : List (Res D)} {l1 h1 : Int}
    {e : Expr D Γ Λ (.int l1 h1)} {lo hi : Int × Int}
    {rest : Endblock D V l (.fl lo hi :: Γ) Λ}
    (h : EndR A C (.floatOf e lo hi rest)) : EndR A C rest := by
  cases h with
  | floatOf _ _ _ _ hr => exact hr


theorem EndR.gleitNarrow_inv {Λ : List (Res D)} {l1 h1 : Int × Int}
    {e : Expr D Γ Λ (.fl l1 h1)} {lo hi : Int × Int} {sonst : Endblock D V l Γ Λ}
    {rest : Endblock D V l (.fl lo hi :: Γ) Λ}
    (h : EndR A C (.floatNarrow e lo hi sonst rest)) :
    EndR A C rest ∧ EndR A C sonst := by
  cases h with
  | floatNarrow _ _ _ _ _ hs hr => exact ⟨hr, hs⟩


theorem EndR.gleit_inv {Λ : List (Res D)} {l1 h1 l2 h2 : Int × Int} {op : GleitOp}
    {a : Expr D Γ Λ (.fl l1 h1)} {b : Expr D Γ Λ (.fl l2 h2)} {lo hi : Int × Int}
    {rest : Endblock D V l (.fl lo hi :: Γ) Λ}
    (h : EndR A C (.float op a b lo hi rest)) : EndR A C rest := by
  cases h with
  | float _ _ _ _ _ _ hr => exact hr


end Gabbro.Grammatik
