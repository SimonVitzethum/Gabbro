/-
  File:      Grammatik/Zielsatz/RuheLift/Fragment.lean
  Subject:   The call-free fragment of the adequacy proof (`StmtR`, `BlockR`, `EndR`, `ArmsR`, `GrundArmsR` with no
             admitted callee) is closed under the translation into `D.mitRuhe` (`ruS`, `ruB`, `ruEnd`, `ruArms`,
             `ruGArms`): a statement the machine of `P` runs by its own steps translates to a statement the machine of
             `P.mitRuhe` runs by its own steps. The leaves (`BlattG`) translate leaf by leaf (`blattG_ru`); the two
             leaves whose holdings after the statement the translation transports (`advances`, `retires`) go through
             `blattG_nachΛ`. Calls are outside the fragment: their admission `C g` is `False`.
-/
module
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuhe
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T1
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- A covered leaf stays covered when its holdings after the statement are transported. -/
theorem blattG_nachΛ {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂)
    {s : Stmt D V l Γ Λ Λ₁} (hs : BlattG s) : BlattG (Stmt.nachΛ h s) := by
  subst h
  exact hs

/-- **A covered leaf translates to a covered leaf.** -/
theorem blattG_ru {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    (h : BlattG s) : BlattG (ruS s) := by
  cases h with
  | advances m a h hs =>
      simp only [ruS]
      exact blattG_nachΛ _ (BlattG.advances _ _ _ _)
  | retires m s h a =>
      simp only [ruS]
      exact blattG_nachΛ _ (BlattG.retires _ _ _ _)
  | _ =>
      simp only [ruS]
      constructor

mutual

/-- **A call-free covered statement translates to a call-free covered statement** of `D.mitRuhe`, with the same
    admitted locks `A` and the same return mode `mr`. -/
theorem stmtR_ru {V : Vertrag D} {A : D.Lock → Prop} :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'},
    StmtR A (fun _ => False) mr s → StmtR (D := D.mitRuhe) A (fun _ => False) mr (ruS s)
  | _, _, _, _, _, _, .blatt s h => .blatt (ruS s) (blattG_ru h)
  | _, _, _, _, _, _, .ite c t e ht he => .ite (ruE c) (ruB t) (ruB e) (blockR_ru ht) (blockR_ru he)
  | _, _, _, _, _, _, .onOption o p a hp ha =>
      .onOption (ruE o) (ruB p) (ruB a) (blockR_ru hp) (blockR_ru ha)
  | _, _, _, _, _, _, .onTag v arms ha => .onTag (ruE v) (ruArms arms) (armsR_ru ha)
  | _, _, _, _, _, _, .onWhy r arms ha => .onWhy (ruE r) (ruGArms arms) (grundR_ru ha)
  | _, _, Γ, _, _, _, .breaking i body hb =>
      StmtR.breaking (D := D.mitRuhe) (V := vertragR V) (Γ := Γ.map tyR)
        i (ruB body) (blockR_ru hb)
  | _, _, Γ, _, _, _, .locks L hr body hbo hA hb =>
      StmtR.locks (D := D.mitRuhe) (V := vertragR V) (Γ := Γ.map tyR)
        L (fun M hM => hr M (held_mem_map.mp hM)) (ruB body) hbo hA (blockR_ru hb)
  | _, _, Γ, _, _, _, .ret e hΛ =>
      StmtR.ret (D := D.mitRuhe) (V := vertragR V) (Γ := Γ.map tyR)
        (ruErg e) ((hΛ.map resR).trans (by rw [ende_map]))
  | _, _, _, _, _, _, .call _ _ _ hC => (hC : False).elim
  | _, _, Γ, _, _, _, .traverse t inv body hb =>
      StmtR.traverse (D := D.mitRuhe) (V := vertragR V) (Γ := Γ.map tyR)
        t (ruE inv) (ruB body) (blockR_ru hb)
  | _, _, _, _, _, _, .retry n bis body ueber hb hu =>
      .retry n (ruE bis) (ruB body) (ruB ueber) (blockR_ru hb) (blockR_ru hu)
  | _, _, Γ, _, _, _, .forever a inv body hb =>
      StmtR.forever (D := D.mitRuhe) (V := vertragR V) (Γ := Γ.map tyR)
        a (ruE inv) (ruB body) (blockR_ru hb)
  | _, _, _, _, _, _, .leave h => .leave h
  | _, _, _, _, _, _, .next h => .next h
  | _, _, Γ, _, _, _, .retWhy r hΛ =>
      StmtR.retWhy (D := D.mitRuhe) (V := vertragR V) (Γ := Γ.map tyR)
        r ((hΛ.map resR).trans (by rw [ende_map]))

/-- A call-free covered block translates to a call-free covered block. -/
theorem blockR_ru {V : Vertrag D} {A : D.Lock → Prop} :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {b : Block D V l Γ Λ Λ'},
    BlockR A (fun _ => False) mr b → BlockR (D := D.mitRuhe) A (fun _ => False) mr (ruB b)
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, .cons s rest hs hr => .cons (ruS s) (ruB rest) (stmtR_ru hs) (blockR_ru hr)
  | _, _, _, _, _, _, .bind e rest hr => .bind (ruE e) (ruB rest) (blockR_ru hr)
  | _, _, _, _, _, _, .bindCall _ _ _ _ _ _ hC _ => (hC : False).elim
  | _, _, Γ, _, _, _, .regRead r hk rest hr =>
      BlockR.regRead (D := D.mitRuhe) (V := vertragR V) (Γ := Γ.map tyR)
        r hk (ruB rest) (blockR_ru hr)
  | _, _, _, _, _, _, .regReadElse r hk z sonst rest hs hr =>
      BlockR.regReadElse (D := D.mitRuhe) (V := vertragR V)
        r hk (ruE z) (ruEnd sonst) (ruB rest) (endR_ru hs) (blockR_ru hr)
  | _, _, Γ, _, _, _, .awaits g payload hp hL hat rest hr =>
      BlockR.awaits (D := D.mitRuhe) (V := vertragR V) (Γ := Γ.map tyR)
        g payload hp (gdarfR hL) hat (ruB rest) (blockR_ru hr)
  | _, _, Γ, _, _, _, .exchange g neu hw hL rest hr =>
      BlockR.exchange (D := D.mitRuhe) (V := vertragR V) (Γ := Γ.map tyR)
        g (ruE neu) hw (gdarfR hL) (ruB rest) (blockR_ru hr)
  | _, _, _, _, _, _, .narrow e lo hi sonst rest hs hr =>
      .narrow (ruE e) lo hi (ruEnd sonst) (ruB rest) (endR_ru hs) (blockR_ru hr)
  | _, _, _, _, _, _, .check c sonst rest hs hr =>
      .check (ruE c) (ruEnd sonst) (ruB rest) (endR_ru hs) (blockR_ru hr)
  | _, _, _, _, _, _, .float op a b lo hi rest hr =>
      .float op (ruE a) (ruE b) lo hi (ruB rest) (blockR_ru hr)
  | _, _, _, _, _, _, .floatLit q lo hi rest hr => .floatLit q lo hi (ruB rest) (blockR_ru hr)
  | _, _, _, _, _, _, .floatOf e lo hi rest hr => .floatOf (ruE e) lo hi (ruB rest) (blockR_ru hr)
  | _, _, _, _, _, _, .floatNarrow e lo hi sonst rest hs hr =>
      .floatNarrow (ruE e) lo hi (ruEnd sonst) (ruB rest) (endR_ru hs) (blockR_ru hr)
  | _, _, _, _, _, _, .bindCallElse _ _ _ _ _ _ _ hC _ _ => (hC : False).elim

/-- A call-free covered end block translates to a call-free covered end block. -/
theorem endR_ru {V : Vertrag D} {A : D.Lock → Prop} :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {e : Endblock D V l Γ Λ},
    EndR A (fun _ => False) e → EndR (D := D.mitRuhe) A (fun _ => False) (ruEnd e)
  | _, Γ, _, _, .ret e hΛ =>
      EndR.ret (D := D.mitRuhe) (V := vertragR V) (Γ := Γ.map tyR)
        (ruErg e) ((hΛ.map resR).trans (by rw [ende_map]))
  | _, _, _, _, .cons s rest hs hr => .cons (ruS s) (ruEnd rest) (stmtR_ru hs) (endR_ru hr)
  | _, _, _, _, .bind e rest hr => .bind (ruE e) (ruEnd rest) (endR_ru hr)
  | _, Γ, _, _, .retWhy r hΛ =>
      EndR.retWhy (D := D.mitRuhe) (V := vertragR V) (Γ := Γ.map tyR)
        r ((hΛ.map resR).trans (by rw [ende_map]))
  | _, _, _, _, .float op a b lo hi rest hr =>
      .float op (ruE a) (ruE b) lo hi (ruEnd rest) (endR_ru hr)
  | _, _, _, _, .floatLit q lo hi rest hr => .floatLit q lo hi (ruEnd rest) (endR_ru hr)
  | _, _, _, _, .floatOf e lo hi rest hr => .floatOf (ruE e) lo hi (ruEnd rest) (endR_ru hr)
  | _, _, _, _, .floatNarrow e lo hi sonst rest hs hr =>
      .floatNarrow (ruE e) lo hi (ruEnd sonst) (ruEnd rest) (endR_ru hs) (endR_ru hr)

/-- Call-free covered arms translate to call-free covered arms (the arm scope split as in `ruArms`). -/
theorem armsR_ru {V : Vertrag D} {A : D.Lock → Prop} :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    {arms : Arms D V l Γ Λ Λ' cs},
    ArmsR A (fun _ => False) mr arms → ArmsR (D := D.mitRuhe) A (fun _ => False) mr (ruArms arms)
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, .cons (c := none) b rest hb hr =>
      .cons (c := none) (ruB b) (ruArms rest) (blockR_ru hb) (armsR_ru hr)
  | _, _, _, _, _, _, _, .cons (c := some τ) b rest hb hr =>
      .cons (c := some (tyR τ)) (ruB b) (ruArms rest) (blockR_ru hb) (armsR_ru hr)

/-- Call-free covered reason arms translate to call-free covered reason arms. -/
theorem grundR_ru {V : Vertrag D} {A : D.Lock → Prop} :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} {arms : GrundArms D V l Γ Λ Λ' n},
    GrundArmsR A (fun _ => False) mr arms →
      GrundArmsR (D := D.mitRuhe) A (fun _ => False) mr (ruGArms arms)
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, .cons b rest hb hr => .cons (ruB b) (ruGArms rest) (blockR_ru hb) (grundR_ru hr)

end

end Gabbro.Grammatik
