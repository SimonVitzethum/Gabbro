import Grammatik.Berechenbarkeit.Storage.GStack.Push

/-! The concrete stack prefixes introduce no loop or recursive call. Existing
termination analysis still sees every supplied continuation and failure branch.
This is not a theorem that a caller's conditional controller eventually halts. -/

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.GStack

variable {D : Deklaration} {A : FreiForm D} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

theorem linkPush_termination (L : LinkFeld A) (G : LinkKopf A) (x : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwH : V.gschreibt G.g = true) (hLH : gdarf D G.g Λ)
    (rest : Gabbro.Grammatik.Block D V l Γ Λ Λ') (level forever : Bool) :
    befB level forever (Gabbro.Grammatik.Block.linkPush L G x hwT hLT hwH hLH rest) =
      befB level forever rest := rfl

theorem free_termination (A : FreiForm D) (x : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwF : V.gschreibt A.kopf = true) (hLF : gdarf D A.kopf Λ)
    (rest : Gabbro.Grammatik.Block D V l Γ Λ Λ') (level forever : Bool) :
    befB level forever (Gabbro.Grammatik.Block.freiVar A x hwT hLT hwF hLF rest) =
      befB level forever rest := rfl

theorem fresh_termination (A : FreiForm D) (value : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwU : V.gschreibt A.zaehl = true) (hLU : gdarf D A.zaehl Λ)
    (failure : Endblock D V l Γ Λ)
    (rest : Gabbro.Grammatik.Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (level forever : Bool) :
    befB level forever (Gabbro.Grammatik.Block.arenaAlloc A.toArenaForm value hwT hLT hwU hLU failure rest) =
      befE level forever failure ++ befB level forever rest := rfl

theorem reuse_termination (A : FreiForm D) (value : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwF : V.gschreibt A.kopf = true) (hLF : gdarf D A.kopf Λ)
    (failure : Endblock D V l Γ Λ)
    (rest : Gabbro.Grammatik.Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (level forever : Bool) :
    befB level forever (Gabbro.Grammatik.Block.freiNimm A value hwT hLT hwF hLF failure rest) =
      befE level forever failure ++ befB level forever rest := rfl

theorem popAndRelease_termination (L : LinkFeld A) (G : LinkKopf A)
    (hwH : V.gschreibt G.g = true) (hLH : gdarf D G.g Λ)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwF : V.gschreibt A.kopf = true) (hLF : gdarf D A.kopf Λ)
    (empty : Endblock D V l Γ Λ)
    (rest : Gabbro.Grammatik.Block D V l (D.typ A.tab A.feld :: Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (level forever : Bool) :
    befB level forever (Block.popAndRelease L G hwH hLH hwT hLT hwF hLF empty rest) =
      befE level forever empty ++ befB level forever rest := rfl

end Gabbro.Grammatik.Berechenbarkeit.Storage.GStack
