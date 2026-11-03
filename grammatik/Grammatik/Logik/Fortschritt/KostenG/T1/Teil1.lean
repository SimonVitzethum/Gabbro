module
public import Grammatik.Logik.Fortschritt.KostenG.T1.Teil1a

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG
public import Grammatik.Logik.Ruf.Umkehr.RufUmkehrRufG

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 2. Which callees a body names -/

/- `rufeS Z ZS EW EW s`: every DIRECT callee named in `s` satisfies `Z`, and every
    indirect call in `s` goes through a signature `n` with `ZS n` (the syntax
    names the signature, not the callee; `ZS = fun _ => false` excludes
    indirect calls), and a `forever` stands in `s` only if `EW`. The
    bound needs to know, before a push, that the callee's cost was counted
    at a table the callee's own body fits under; this is the Bool that
    carries the admission of the callees down the residue. -/
mutual
def rufeS (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => rufeB Z ZS EW t && rufeB Z ZS EW e
  | .onOption _ p a => rufeB Z ZS EW p && rufeB Z ZS EW a
  | .onTag _ arms => rufeArms Z ZS EW arms
  | .onWhy _ arms => rufeGArms Z ZS EW arms
  | .call g _ _ _ => Z g
  | .callInd (n := n) _ _ _ _ => ZS n
  | .callIndElse (n := n) _ _ _ _ _ err => ZS n && rufeE Z ZS EW err
  | .locks _ _ body => rufeB Z ZS EW body
  | .breaking _ body => rufeB Z ZS EW body
  | .traverse _ _ body => rufeB Z ZS EW body
  | .consumeTraverse _ _ _ _ _ _ body => rufeB Z ZS EW body
  | .retry _ _ body ueber => rufeB Z ZS EW body && rufeB Z ZS EW ueber
  | .forever _ _ body => EW && rufeB Z ZS EW body
  | .assignSlot .. => true
  | .assignThru .. | .assignThruOwn .. | .assignSlotRef .. => true
  | .assignGlob .. => true
  | .putBytes .. => true
  | .assignVar .. => true
  | .shift .. => true
  | .axiomCall .. => true
  | .axiomCallElse _ _ _ _ _ _ _ _ err => rufeE Z ZS EW err
  | .regWrite .. => true
  | .transition .. => true
  | .publish .. => true
  | .advances .. => true
  | .retires .. => true
  | .ret .. => true
  | .retWhy .. => true
  | .retScoped .. => true
  | .retWhyScoped .. => true
  | .leave _ => true
  | .next _ => true

def rufeB (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => rufeS Z ZS EW s && rufeB Z ZS EW rest
  | .bind _ rest => rufeB Z ZS EW rest
  | .bindCall g _ _ _ _ rest => Z g && rufeB Z ZS EW rest
  | .bindCallInd (n := n) _ _ _ _ _ rest => ZS n && rufeB Z ZS EW rest
  | .bindCallIndElse (n := n) _ _ _ _ _ err rest => ZS n && rufeE Z ZS EW err && rufeB Z ZS EW rest
  | .bindCallElse g _ _ _ _ err rest => Z g && rufeE Z ZS EW err && rufeB Z ZS EW rest
  | .bindAxiom _ _ _ _ _ _ _ rest => rufeB Z ZS EW rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => rufeE Z ZS EW err && rufeB Z ZS EW rest
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => rufeB Z ZS EW rest
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => rufeE Z ZS EW err && rufeB Z ZS EW rest
  | .regRead _ _ rest => rufeB Z ZS EW rest
  | .regReadElse _ _ _ sonst rest => rufeE Z ZS EW sonst && rufeB Z ZS EW rest
  | .awaits _ _ _ _ _ rest => rufeB Z ZS EW rest
  | .exchange _ _ _ _ rest => rufeB Z ZS EW rest
  | .narrow _ _ _ sonst rest => rufeE Z ZS EW sonst && rufeB Z ZS EW rest
  | .narrowRequired _ _ _ rest => rufeB Z ZS EW rest
  | .check _ sonst rest => rufeE Z ZS EW sonst && rufeB Z ZS EW rest
  | .float _ _ _ _ _ rest => rufeB Z ZS EW rest
  | .floatLit _ _ _ rest => rufeB Z ZS EW rest
  | .floatOf _ _ _ rest => rufeB Z ZS EW rest
  | .floatNarrow _ _ _ sonst rest => rufeE Z ZS EW sonst && rufeB Z ZS EW rest

def rufeArms (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => rufeB Z ZS EW b && rufeArms Z ZS EW rest

def rufeGArms (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} : GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => rufeB Z ZS EW b && rufeGArms Z ZS EW rest

def rufeE (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retWhy .. => true
  | .retScoped .. => true
  | .retWhyScoped .. => true
  | .leave _ => true
  | .next _ => true
  | .cons s rest => rufeS Z ZS EW s && rufeE Z ZS EW rest
  | .bind _ rest => rufeE Z ZS EW rest
  | .bindCall g _ _ _ _ rest => Z g && rufeE Z ZS EW rest
  | .bindCallElse g _ _ _ _ err rest => Z g && rufeE Z ZS EW err && rufeE Z ZS EW rest
  | .bindAxiom _ _ _ _ _ _ _ rest => rufeE Z ZS EW rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => rufeE Z ZS EW err && rufeE Z ZS EW rest
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => rufeE Z ZS EW rest
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => rufeE Z ZS EW err && rufeE Z ZS EW rest
  | .regRead _ _ rest => rufeE Z ZS EW rest
  | .regReadElse _ _ _ sonst rest => rufeE Z ZS EW sonst && rufeE Z ZS EW rest
  | .awaits _ _ _ _ _ rest => rufeE Z ZS EW rest
  | .bindCallInd (n := n) _ _ _ _ _ rest => ZS n && rufeE Z ZS EW rest
  | .bindCallIndElse (n := n) _ _ _ _ _ err rest => ZS n && rufeE Z ZS EW err && rufeE Z ZS EW rest
  | .narrow _ _ _ sonst rest => rufeE Z ZS EW sonst && rufeE Z ZS EW rest
  | .narrowRequired _ _ _ rest => rufeE Z ZS EW rest
  | .exchange _ _ _ _ rest => rufeE Z ZS EW rest
  | .ite _ t e => rufeE Z ZS EW e && rufeE Z ZS EW t
end
/-- The callees of a residue: those of every block, end block and loop body
    still to run. -/
def rufeR (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Bool
  | .ende e => rufeE Z ZS EW e
  | .dann b k => rufeB Z ZS EW b && rufeR Z ZS EW k
  | .schrumpf k => rufeR Z ZS EW k
  | .frei _ k => rufeR Z ZS EW k
  | .trav _ _ body _ k => rufeB Z ZS EW body && rufeR Z ZS EW k
  | .travRest _ _ body _ k => rufeB Z ZS EW body && rufeR Z ZS EW k
  | .verbrauch _ _ _ _ _ _ body _ k => rufeB Z ZS EW body && rufeR Z ZS EW k
  | .verbrauchRest _ _ _ _ _ _ body _ _ k => rufeB Z ZS EW body && rufeR Z ZS EW k
  | .wieder _ _ body ueber k => rufeB Z ZS EW body && rufeB Z ZS EW ueber && rufeR Z ZS EW k
  | .wiederRest _ _ body ueber k => rufeB Z ZS EW body && rufeB Z ZS EW ueber && rufeR Z ZS EW k
  | .ewig _ _ _ body k => EW && rufeB Z ZS EW body && rufeR Z ZS EW k
  | .ewigRest _ _ _ body k => EW && rufeB Z ZS EW body && rufeR Z ZS EW k
  | .wartet rest k => rufeB Z ZS EW rest && rufeR Z ZS EW k
  | .wartetSonst _ err rest k => rufeE Z ZS EW err && rufeB Z ZS EW rest && rufeR Z ZS EW k
  | .abbruch k => rufeR Z ZS EW k
  | .zurueckgekehrt _ => true
  | .leer => true
  | .rueckBereit _ k => rufeR Z ZS EW k

/-! ## 3. The potential: `kosten` read as a function of the residue -/

/-- The steps a residue may still take: an end block or block costs what
    §1 says; a `schrumpf`/`frei` layer one step; a loop state its remaining
    iterations (list length, tries, budget) times one pass plus one; a
    `Rest` shim one more than the loop it resumes; a waiting caller its
    continuation (the callee's steps are counted in the callee's frame). -/
def potRest (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : GRest D V l Γ Λ → Nat
  | .ende e => kostenEnd c pa e
  | .dann b k => kostenBlock c pa b + potRest c pa k
  | .schrumpf k => 1 + potRest c pa k
  | .frei _ k => 1 + potRest c pa k
  | .trav _ inv body ks k =>
      1 + ks.length * (kostenBlock c pa body + kostenExpr inv + 2) + potRest c pa k
  | .travRest _ inv body ks k =>
      2 + ks.length * (kostenBlock c pa body + kostenExpr inv + 2) + potRest c pa k
  | .verbrauch _ member edge inv _ mass body rest k =>
      1 + rest * (kostenBlock c pa body + kostenExpr member + kostenExpr edge +
        kostenExpr inv + kostenExpr mass + 2) + potRest c pa k
  | .verbrauchRest _ member edge inv _ mass body rest _ k =>
      2 + rest * (kostenBlock c pa body + kostenExpr member + kostenExpr edge +
        kostenExpr inv + kostenExpr mass + 2) + potRest c pa k
  | .wieder n bis body ueber k =>
      1 + n * (kostenBlock c pa body + kostenExpr bis + 2) + (2 + kostenExpr bis + kostenBlock c pa ueber) +
        potRest c pa k
  | .wiederRest n bis body ueber k =>
      2 + n * (kostenBlock c pa body + kostenExpr bis + 2) + (2 + kostenExpr bis + kostenBlock c pa ueber) +
        potRest c pa k
  | .ewig _ n inv body k =>
      1 + n * (kostenBlock c pa body + kostenExpr inv + 2) + potRest c pa k
  | .ewigRest _ n inv body k =>
      2 + n * (kostenBlock c pa body + kostenExpr inv + 2) + potRest c pa k
  | .wartet rest k => kostenBlock c pa rest + 1 + potRest c pa k
  | .wartetSonst _ err rest k =>
      max (kostenSonst c pa err + 2 + potRest c pa k) (kostenBlock c pa rest + 1 + potRest c pa k)
  | .abbruch k => 1 + potRest c pa k
  | .zurueckgekehrt _ => 1
  | .leer => 1
  | .rueckBereit _ k => 1 + potRest c pa k

section Positiv

variable (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem kostenStmt_pos {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') :
    1 ≤ kostenStmt c pa s := by
  cases s <;> simp only [kostenStmt] <;> omega

theorem kostenBlock_pos {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') :
    1 ≤ kostenBlock c pa b := by
  cases b with
  | cons s rest => have := kostenStmt_pos c pa s; simp only [kostenBlock]; omega
  | _ => simp only [kostenBlock]; omega

theorem kostenEnd_pos {Λ : List (Res D)} (e : Endblock D V l Γ Λ) :
    1 ≤ kostenEnd c pa e := by
  cases e with
  | cons s rest => have := kostenStmt_pos c pa s; simp only [kostenEnd]; omega
  | _ => simp only [kostenEnd]; omega

theorem potRest_pos {Λ : List (Res D)} (r : GRest D V l Γ Λ) : 1 ≤ potRest c pa r := by
  cases r with
  | ende e => exact kostenEnd_pos c pa e
  | dann b k => have := kostenBlock_pos c pa b; simp only [potRest]; omega
  | wartet rest k => simp only [potRest]; omega
  | wartetSonst n err rest k => simp only [potRest]; omega
  | _ => simp only [potRest]; omega

end Positiv
end Gabbro.Grammatik
