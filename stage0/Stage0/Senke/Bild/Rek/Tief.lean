/-
  File:      stage0/Stage0/Senke/Bild/Rek/Tief.lean
  Subject:   **The program-level discharge of the callee set** (package P4 of the closed calls of the image theorem,
             part 4). The image theorem with calls (`Emitted.bild_ziel_tief`) admits in `main`'s decomposed prefix
             the calls of callees in `Tief P Agl (depth - 1)`: their bodies are in the call fragment with callees
             admitted one level down. `Tief` is a fact about the bodies; this file derives it from a RANK of the
             functions: when every body is in the call fragment with callees of strictly smaller rank
             (`EndR Agl (rang · < rang g) (P.rumpf g)`), every function of rank below `n` is in `Tief P Agl n`
             (`tief_rang`). The fragment is monotone in its callee set (`endR_mono` and its mutual companions,
             `Zerlegung.mono`), so a decomposed prefix with callees of rank below the depth is one with callees in
             `Tief` (`zerlegung_tief_rang`).

             What supplies the premise: the rank and the fragment are facts about the program's bodies, decidable
             for a finite program; neither the checker (`Akzeptiert`) nor the compiler (`lowFun`) proves them --
             `lowFun` lowers recursive calls, and the checker admits them. A RECURSIVE callee (one that calls itself,
             directly or through others) has no rank and is in no `Tief` (`Tief P A 0 = False` at the bottom of its
             own call chain). Recursion is admitted by `TiefAlle` (`Rek/Alle.lean`), which has the vacuous bottom
             of the handler of depth `0`; `Tief ⊆ TiefAlle` (`tief_tiefAlle`), and the return to the caller is
             `Rek/RueckG.lean` and `Rek/RueckArt.lean`.
-/
module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T8
public import Stage0.Senke.Bild.Korrespondenz
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Runner.IR

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-! ## The call fragment is monotone in its callee set -/

mutual

theorem stmtR_mono {V : Vertrag D} {A : D.Lock → Prop} {C C' : D.Fn → Prop} (hC : ∀ g, C g → C' g) :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'},
    StmtR A C mr s → StmtR A C' mr s
  | _, _, _, _, _, _, .blatt s h => .blatt s h
  | _, _, _, _, _, _, .ite c t e ht he => .ite c t e (blockR_mono hC ht) (blockR_mono hC he)
  | _, _, _, _, _, _, .onOption o p a hp ha => .onOption o p a (blockR_mono hC hp) (blockR_mono hC ha)
  | _, _, _, _, _, _, .onTag v arms ha => .onTag v arms (armsR_mono hC ha)
  | _, _, _, _, _, _, .onWhy r arms ha => .onWhy r arms (grundR_mono hC ha)
  | _, _, _, _, _, _, .breaking i body hb => .breaking i body (blockR_mono hC hb)
  | _, _, _, _, _, _, .locks L hr body hbo hA hb => .locks L hr body hbo hA (blockR_mono hC hb)
  | _, _, _, _, _, _, .ret e hΛ => .ret e hΛ
  | _, _, _, _, _, _, .call s g hg hc => .call s g hg (hC g hc)
  | _, _, _, _, _, _, .traverse t inv body hb => .traverse t inv body (blockR_mono hC hb)
  | _, _, _, _, _, _, .retry n bis body ueber hb hu =>
      .retry n bis body ueber (blockR_mono hC hb) (blockR_mono hC hu)
  | _, _, _, _, _, _, .forever a inv body hb => .forever a inv body (blockR_mono hC hb)
  | _, _, _, _, _, _, .leave h => .leave h
  | _, _, _, _, _, _, .next h => .next h
  | _, _, Γ, _, _, _, .retWhy r hΛ => .retWhy (Γ := Γ) r hΛ

theorem blockR_mono {V : Vertrag D} {A : D.Lock → Prop} {C C' : D.Fn → Prop} (hC : ∀ g, C g → C' g) :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {b : Block D V l Γ Λ Λ'},
    BlockR A C mr b → BlockR A C' mr b
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, .cons s rest hs hr => .cons s rest (stmtR_mono hC hs) (blockR_mono hC hr)
  | _, _, _, _, _, _, .bind e rest hr => .bind e rest (blockR_mono hC hr)
  | _, _, _, _, _, _, .bindCall g args he hp hr rest hc hrest =>
      .bindCall g args he hp hr rest (hC g hc) (blockR_mono hC hrest)
  | _, _, _, _, _, _, .regRead r hk rest hr => .regRead r hk rest (blockR_mono hC hr)
  | _, _, _, _, _, _, .regReadElse r hk z sonst rest hs hr =>
      .regReadElse r hk z sonst rest (endR_mono hC hs) (blockR_mono hC hr)
  | _, _, _, _, _, _, .awaits g payload hp hL hat rest hr =>
      .awaits g payload hp hL hat rest (blockR_mono hC hr)
  | _, _, _, _, _, _, .exchange g neu hw hL rest hr => .exchange g neu hw hL rest (blockR_mono hC hr)
  | _, _, _, _, _, _, .narrow e lo hi sonst rest hs hr =>
      .narrow e lo hi sonst rest (endR_mono hC hs) (blockR_mono hC hr)
  | _, _, _, _, _, _, .check c sonst rest hs hr => .check c sonst rest (endR_mono hC hs) (blockR_mono hC hr)
  | _, _, _, _, _, _, .float op a b lo hi rest hr => .float op a b lo hi rest (blockR_mono hC hr)
  | _, _, _, _, _, _, .floatLit q lo hi rest hr => .floatLit q lo hi rest (blockR_mono hC hr)
  | _, _, _, _, _, _, .floatOf e lo hi rest hr => .floatOf e lo hi rest (blockR_mono hC hr)
  | _, _, _, _, _, _, .floatNarrow e lo hi sonst rest hs hr =>
      .floatNarrow e lo hi sonst rest (endR_mono hC hs) (blockR_mono hC hr)
  | _, _, _, _, _, _, .bindCallElse g args he hp hr err rest hc herr hrest =>
      .bindCallElse g args he hp hr err rest (hC g hc) (endR_mono hC herr) (blockR_mono hC hrest)

theorem endR_mono {V : Vertrag D} {A : D.Lock → Prop} {C C' : D.Fn → Prop} (hC : ∀ g, C g → C' g) :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {e : Endblock D V l Γ Λ},
    EndR A C e → EndR A C' e
  | _, _, _, _, .ret e hΛ => .ret e hΛ
  | _, _, _, _, .cons s rest hs hr => .cons s rest (stmtR_mono hC hs) (endR_mono hC hr)
  | _, _, _, _, .bind e rest hr => .bind e rest (endR_mono hC hr)
  | _, Γ, _, _, .retWhy r hΛ => .retWhy (Γ := Γ) r hΛ
  | _, _, _, _, .float op a b lo hi rest hr => .float op a b lo hi rest (endR_mono hC hr)
  | _, _, _, _, .floatLit q lo hi rest hr => .floatLit q lo hi rest (endR_mono hC hr)
  | _, _, _, _, .floatOf e lo hi rest hr => .floatOf e lo hi rest (endR_mono hC hr)
  | _, _, _, _, .floatNarrow e lo hi sonst rest hs hr =>
      .floatNarrow e lo hi sonst rest (endR_mono hC hs) (endR_mono hC hr)

theorem armsR_mono {V : Vertrag D} {A : D.Lock → Prop} {C C' : D.Fn → Prop} (hC : ∀ g, C g → C' g) :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    {arms : Arms D V l Γ Λ Λ' cs}, ArmsR A C mr arms → ArmsR A C' mr arms
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, .cons b rest hb hr => .cons b rest (blockR_mono hC hb) (armsR_mono hC hr)

theorem grundR_mono {V : Vertrag D} {A : D.Lock → Prop} {C C' : D.Fn → Prop} (hC : ∀ g, C g → C' g) :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    {arms : GrundArms D V l Γ Λ Λ' n}, GrundArmsR A C mr arms → GrundArmsR A C' mr arms
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, .cons b rest hb hr => .cons b rest (blockR_mono hC hb) (grundR_mono hC hr)

end

/-! ## `Tief` from a rank -/

/-- **Callees of lower rank are admitted at every larger depth**: if every body is in the call fragment with callees
    of strictly smaller rank, every function of rank below `n` is in `Tief P A n`. -/
theorem tief_rang (P : Programm D) (A : D.Lock → Prop) (rang : D.Fn → Nat)
    (h : ∀ g, EndR A (fun g' => rang g' < rang g) (P.rumpf g)) :
    ∀ (n : Nat) (g : D.Fn), rang g < n → Tief P A n g
  | 0, _, hg => absurd hg (Nat.not_lt_zero _)
  | n + 1, g, hg => by
    show EndR A (Tief P A n) (P.rumpf g)
    exact endR_mono (fun g' (hg' : rang g' < rang g) => tief_rang P A rang h n g' (by omega)) (h g)

variable [Kern]

/-- A decomposed prefix with callees `C` is one with every larger callee set. -/
theorem Zerlegung.mono {B : BodyFrame D} {Agl : D.Lock → Prop} {C C' : D.Fn → Prop} (hC : ∀ g, C g → C' g)
    {l : Bool} {Γ Γe : Ctx} {Λ Λe : List (Res D)} {eb : Endblock D (vertragVon D B.f) l Γ Λ}
    {ebe : Endblock D (vertragVon D B.f) l Γe Λe} {σ σe : World D} {ρ : Env D Γ} {ρe : Env D Γe}
    (h : Zerlegung B Agl C eb σ ρ ebe σe ρe) : Zerlegung B Agl C' eb σ ρ ebe σe ρe := by
  induction h with
  | halt eb σ ρ => exact Zerlegung.halt eb σ ρ
  | schritt s rest ebe σ σ1 σe ρ ρ1 ρe hs hex _ ih =>
    exact Zerlegung.schritt s rest ebe σ σ1 σe ρ ρ1 ρe (stmtR_mono hC hs) hex ih
  | bind e rest ebe σ σe ρ ρe _ ih => exact Zerlegung.bind e rest ebe σ σe ρ ρe ih

/-- **The program-level discharge**: a decomposed prefix whose callees have rank below `n` is one whose callees are
    admitted at depth `n` (`Tief P Agl n`), when every body is in the call fragment with callees of smaller rank. -/
theorem zerlegung_tief_rang {P : Programm D} {Agl : D.Lock → Prop} {rang : D.Fn → Nat}
    (h : ∀ g, EndR Agl (fun g' => rang g' < rang g) (P.rumpf g)) {n : Nat} {B : BodyFrame D}
    {l : Bool} {Γ Γe : Ctx} {Λ Λe : List (Res D)} {eb : Endblock D (vertragVon D B.f) l Γ Λ}
    {ebe : Endblock D (vertragVon D B.f) l Γe Λe} {σ σe : World D} {ρ : Env D Γ} {ρe : Env D Γe}
    (hk : Zerlegung B Agl (fun g => rang g < n) eb σ ρ ebe σe ρe) :
    Zerlegung B Agl (Tief P Agl n) eb σ ρ ebe σe ρe :=
  hk.mono (fun g (hg : rang g < n) => tief_rang P Agl rang h n g hg)

end Gabbro.Stage0.Senke.BildLauf
