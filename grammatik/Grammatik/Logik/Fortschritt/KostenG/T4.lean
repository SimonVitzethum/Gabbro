/- Part 4 of 5 of `KostenG` (split by instrumente/teile/lean-teilen.py; the umbrella `KostenG.lean` imports all parts). -/
import Grammatik.Logik.Fortschritt.KostenG.T3

namespace Gabbro.Grammatik

variable {D : Deklaration}

mutual
/-- **The correspondence, per statement form**: the Lean bound is at most
    the checker's number plus the remainder `zusatz`. -/
theorem spiegel_stmt (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → spiegelS s = true →
      kostenStmt c pa s ≤ kostenKS c s + zusatzS s
  | .ite b t e, h => by
      simp only [spiegelS, Bool.and_eq_true] at h
      have h1 := spiegel_block c pa t h.1
      have h2 := spiegel_block c pa e h.2
      simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .onOption o p a, h => by
      simp only [spiegelS, Bool.and_eq_true] at h
      have h1 := spiegel_block c pa p h.1
      have h2 := spiegel_block c pa a h.2
      simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .onTag v arms, h => by
      have h1 := spiegel_arms c pa arms h
      simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .onWhy r arms, h => by
      have h1 := spiegel_garms c pa arms h
      simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .locks _ _ body, h => by
      have h1 := spiegel_block c pa body h
      simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .breaking _ body, h => by
      have h1 := spiegel_block c pa body h
      simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .traverse t inv body, h => by
      have h1 := spiegel_block c pa body h
      have h2 : (D.count t).toNat * (kostenBlock c pa body + kostenExpr inv + 2) ≤
          (D.count t).toNat * kostenKB c body +
            (D.count t).toNat * (zusatzB body + kostenExpr inv + 2) := by
        rw [← Nat.mul_add]
        exact Nat.mul_le_mul_left _ (by omega)
      simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .callInd .., h => by simp [spiegelS] at h
  | .retry .., h => by simp [spiegelS] at h
  | .forever .., h => by simp [spiegelS] at h
  | .axiomCall .., h => by simp [spiegelS] at h
  | .transition .., h => by simp [spiegelS] at h
  | .advances .., h => by simp [spiegelS] at h
  | .retires .., h => by simp [spiegelS] at h
  | .assignSlot .., _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .assignThru .., _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .assignGlob .., _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .putBytes .., _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .assignVar .., _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .shift .., _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .call .., _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .regWrite .., _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .publish .., _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .ret .., _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .retWhy .., _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .leave _, _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .next _, _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega

theorem spiegel_block (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → spiegelB b = true →
      kostenBlock c pa b ≤ kostenKB c b + zusatzB b
  | .nil, _ => by simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .cons s rest, h => by
      simp only [spiegelB, Bool.and_eq_true] at h
      have h1 := spiegel_stmt c pa s h.1
      have h2 := spiegel_block c pa rest h.2
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .bind _ rest, h => by
      have h1 := spiegel_block c pa rest h
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .bindCall _ _ _ _ _ rest, h => by
      have h1 := spiegel_block c pa rest h
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .bindCallInd .., h => by simp [spiegelB] at h
  | .bindCallElse _ _ _ _ _ err rest, h => by
      simp only [spiegelB, Bool.and_eq_true] at h
      have h1 := spiegel_sonst c pa err h.1
      have h2 := spiegel_block c pa rest h.2
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .bindAxiom .., h => by simp [spiegelB] at h
  | .bindAxiomElse .., h => by simp [spiegelB] at h
  | .regRead _ _ rest, h => by
      have h1 := spiegel_block c pa rest h
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .regReadElse _ _ _ sonst rest, h => by
      simp only [spiegelB, Bool.and_eq_true] at h
      have h1 := spiegel_sonst c pa sonst h.1
      have h2 := spiegel_block c pa rest h.2
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .awaits _ _ _ _ rest, h => by
      have h1 := spiegel_block c pa rest h
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .exchange _ _ _ _ rest, h => by
      have h1 := spiegel_block c pa rest h
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .narrow _ _ _ sonst rest, h => by
      simp only [spiegelB, Bool.and_eq_true] at h
      have h1 := spiegel_sonst c pa sonst h.1
      have h2 := spiegel_block c pa rest h.2
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .check _ sonst rest, h => by
      simp only [spiegelB, Bool.and_eq_true] at h
      have h1 := spiegel_sonst c pa sonst h.1
      have h2 := spiegel_block c pa rest h.2
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .float _ _ _ _ _ rest, h => by
      have h1 := spiegel_block c pa rest h
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .floatLit _ _ _ rest, h => by
      have h1 := spiegel_block c pa rest h
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .floatOf _ _ _ rest, h => by
      have h1 := spiegel_block c pa rest h
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .floatNarrow _ _ _ sonst rest, h => by
      simp only [spiegelB, Bool.and_eq_true] at h
      have h1 := spiegel_sonst c pa sonst h.1
      have h2 := spiegel_block c pa rest h.2
      simp only [kostenBlock, kostenKB, zusatzB]; omega

theorem spiegel_arms (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} :
    (arms : Arms D V l Γ Λ Λ' cs) → spiegelArms arms = true →
      kostenArms c pa arms ≤ kostenKArms c arms + zusatzArms arms
  | .nil, _ => by simp only [kostenArms, kostenKArms, zusatzArms]; omega
  | .cons b rest, h => by
      simp only [spiegelArms, Bool.and_eq_true] at h
      have h1 := spiegel_block c pa b h.1
      have h2 := spiegel_arms c pa rest h.2
      simp only [kostenArms, kostenKArms, zusatzArms]; omega

theorem spiegel_garms (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} :
    (arms : GrundArms D V l Γ Λ Λ' n) → spiegelGArms arms = true →
      kostenGrundArms c pa arms ≤ kostenKGArms c arms + zusatzGArms arms
  | .nil, _ => by simp only [kostenGrundArms, kostenKGArms, zusatzGArms]; omega
  | .cons b rest, h => by
      simp only [spiegelGArms, Bool.and_eq_true] at h
      have h1 := spiegel_block c pa b h.1
      have h2 := spiegel_garms c pa rest h.2
      simp only [kostenGrundArms, kostenKGArms, zusatzGArms]; omega

theorem spiegel_end (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → spiegelE e = true →
      kostenEnd c pa e ≤ kostenKE c e + zusatzE e
  | .ret .., _ => by simp only [kostenEnd, kostenKE, zusatzE]; omega
  | .retWhy .., _ => by simp only [kostenEnd, kostenKE, zusatzE]; omega
  | .leave _, _ => by simp only [kostenEnd, kostenKE, zusatzE]; omega
  | .next _, _ => by simp only [kostenEnd, kostenKE, zusatzE]; omega
  | .cons s rest, h => by
      simp only [spiegelE, Bool.and_eq_true] at h
      have h1 := spiegel_stmt c pa s h.1
      have h2 := spiegel_end c pa rest h.2
      simp only [kostenEnd, kostenKE, zusatzE]; omega
  | .bind _ rest, h => by
      have h1 := spiegel_end c pa rest h
      simp only [kostenEnd, kostenKE, zusatzE]; omega
  | .bindCall _ _ _ _ _ rest, h => by
      have h1 := spiegel_sonst c pa rest h
      simp only [kostenEnd, kostenKE, zusatzE]; omega
  | .bindAxiom .., h => by simp [spiegelE] at h
  | .bindAxiomElse .., h => by simp [spiegelE] at h

theorem spiegel_sonst (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → spiegelE e = true →
      kostenSonst c pa e ≤ kostenKE c e + zusatzSonst e
  | .ret .., _ => by simp only [kostenSonst, kostenKE, zusatzSonst]; omega
  | .retWhy .., _ => by simp only [kostenSonst, kostenKE, zusatzSonst]; omega
  | .leave _, _ => by simp only [kostenSonst, kostenKE, zusatzSonst]; omega
  | .next _, _ => by simp only [kostenSonst, kostenKE, zusatzSonst]; omega
  | .cons s rest, h => by
      simp only [spiegelE, Bool.and_eq_true] at h
      have h1 := spiegel_stmt c pa s h.1
      have h2 := spiegel_sonst c pa rest h.2
      simp only [kostenSonst, kostenKE, zusatzSonst]; omega
  | .bind _ rest, h => by
      have h1 := spiegel_sonst c pa rest h
      simp only [kostenSonst, kostenKE, zusatzSonst]; omega
  | .bindCall _ _ _ _ _ rest, h => by
      have h1 := spiegel_sonst c pa rest h
      simp only [kostenSonst, kostenKE, zusatzSonst]; omega
  | .bindAxiom .., h => by simp [spiegelE] at h
  | .bindAxiomElse .., h => by simp [spiegelE] at h
end
/-- **TARGET 3 over a frame.** For a body in the mirrored forms, the own
    steps of its frame are at most the checker's number of the body plus
    the remainder -- with calls counting the callee's cost one depth down
    on both sides. -/
theorem frame_schritte_pruefer (P : Programm D) (O : Orakel D) (passes : Nat)
    (f : Faden) (g : D.Fn) (n : Nat) (hadm : rufTief P (n + 1) g = true)
    (hsp : spiegelE (P.rumpf g) = true)
    {rho : Env D (D.params g)} {s0 : World D} {k : Nat} {M1 M2 : RufMaschineG D}
    (hE : Eintritt P f g rho s0 k M1)
    (run : SegLauf P O passes M1 M2) (hA : aktivVor f k run) :
    segZaehle run f ≤ kostenKE (kostenTief P passes n) (P.rumpf g) + zusatzE (P.rumpf g) :=
  Nat.le_trans (frame_schritte_beschraenkt P O passes f g n hadm hE run hA)
    (spiegel_end (kostenTief P passes n) passes (P.rumpf g) hsp)

/-! ## 12. The admission depth of the adequacy theorems

    `Tief P A n` (RufAdaequatRufG.lean) and `TiefK P A n`
    (RufUmkehrRufG.lean) admit a callee at depth `n + 1` when its body is
    covered with callees admitted at depth `n`. Every function they admit
    is admitted by `rufTief` at the same depth, so every frame the
    adequacy theorems speak about has the step bound. -/

section Tiefe

variable {V : Vertrag D} {A : D.Lock → Prop} {C : D.Fn → Prop}

mutual
theorem rufeS_of_StmtR (Z : D.Fn → Bool) (hZ : ∀ g, C g → Z g = true) {mr l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'} :
    StmtR A C mr s → rufeS Z s = true
  | .blatt _ hb => by cases hb <;> rfl
  | .ite _ _ _ ht he => by
      simp only [rufeS, Bool.and_eq_true]
      exact ⟨rufeB_of_BlockR Z hZ ht, rufeB_of_BlockR Z hZ he⟩
  | .onOption _ _ _ hp ha => by
      simp only [rufeS, Bool.and_eq_true]
      exact ⟨rufeB_of_BlockR Z hZ hp, rufeB_of_BlockR Z hZ ha⟩
  | .onTag _ _ ha => by
      simp only [rufeS]; exact rufeArms_of_ArmsR Z hZ ha
  | .onWhy _ _ ha => by
      simp only [rufeS]; exact rufeGArms_of_GrundArmsR Z hZ ha
  | .breaking _ _ hb => by
      simp only [rufeS]; exact rufeB_of_BlockR Z hZ hb
  | .locks _ _ _ _ _ hb => by
      simp only [rufeS]; exact rufeB_of_BlockR Z hZ hb
  | .ret _ _ => rfl
  | .call s g hg hC => by
      cases s <;> simp only [Stmt.rufZiel, Option.some.injEq, reduceCtorEq] at hg
      subst hg
      exact hZ _ hC
  | .traverse _ _ _ hb => by
      simp only [rufeS]; exact rufeB_of_BlockR Z hZ hb
  | .retry _ _ _ _ hb hu => by
      simp only [rufeS, Bool.and_eq_true]
      exact ⟨rufeB_of_BlockR Z hZ hb, rufeB_of_BlockR Z hZ hu⟩
  | .forever _ _ _ hb => by
      simp only [rufeS]; exact rufeB_of_BlockR Z hZ hb
  | .leave _ => rfl
  | .next _ => rfl
  | .retWhy _ _ => rfl

theorem rufeB_of_BlockR (Z : D.Fn → Bool) (hZ : ∀ g, C g → Z g = true) {mr l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {b : Block D V l Γ Λ Λ'} :
    BlockR A C mr b → rufeB Z b = true
  | .nil => rfl
  | .cons _ _ hs hr => by
      simp only [rufeB, Bool.and_eq_true]
      exact ⟨rufeS_of_StmtR Z hZ hs, rufeB_of_BlockR Z hZ hr⟩
  | .bind _ _ hr => by simp only [rufeB]; exact rufeB_of_BlockR Z hZ hr
  | .bindCall _ _ _ _ _ _ hC hr => by
      simp only [rufeB, Bool.and_eq_true]
      exact ⟨hZ _ hC, rufeB_of_BlockR Z hZ hr⟩
  | .regRead _ _ _ hr => by simp only [rufeB]; exact rufeB_of_BlockR Z hZ hr
  | .regReadElse _ _ _ _ _ hs hr => by
      simp only [rufeB, Bool.and_eq_true]
      exact ⟨rufeE_of_EndR Z hZ hs, rufeB_of_BlockR Z hZ hr⟩
  | .awaits _ _ _ _ _ hr => by simp only [rufeB]; exact rufeB_of_BlockR Z hZ hr
  | .exchange _ _ _ _ _ hr => by simp only [rufeB]; exact rufeB_of_BlockR Z hZ hr
  | .narrow _ _ _ _ _ hs hr => by
      simp only [rufeB, Bool.and_eq_true]
      exact ⟨rufeE_of_EndR Z hZ hs, rufeB_of_BlockR Z hZ hr⟩
  | .check _ _ _ hs hr => by
      simp only [rufeB, Bool.and_eq_true]
      exact ⟨rufeE_of_EndR Z hZ hs, rufeB_of_BlockR Z hZ hr⟩
  | .float _ _ _ _ _ _ hr => by simp only [rufeB]; exact rufeB_of_BlockR Z hZ hr
  | .floatLit _ _ _ _ hr => by simp only [rufeB]; exact rufeB_of_BlockR Z hZ hr
  | .floatOf _ _ _ _ hr => by simp only [rufeB]; exact rufeB_of_BlockR Z hZ hr
  | .floatNarrow _ _ _ _ _ hs hr => by
      simp only [rufeB, Bool.and_eq_true]
      exact ⟨rufeE_of_EndR Z hZ hs, rufeB_of_BlockR Z hZ hr⟩
  | .bindCallElse _ _ _ _ _ _ _ hC herr hr => by
      simp only [rufeB, Bool.and_eq_true]
      exact ⟨⟨hZ _ hC, rufeE_of_EndR Z hZ herr⟩, rufeB_of_BlockR Z hZ hr⟩

theorem rufeE_of_EndR (Z : D.Fn → Bool) (hZ : ∀ g, C g → Z g = true) {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)} {e : Endblock D V l Γ Λ} :
    EndR A C e → rufeE Z e = true
  | .ret _ _ => rfl
  | .cons _ _ hs hr => by
      simp only [rufeE, Bool.and_eq_true]
      exact ⟨rufeS_of_StmtR Z hZ hs, rufeE_of_EndR Z hZ hr⟩
  | .bind _ _ hr => by simp only [rufeE]; exact rufeE_of_EndR Z hZ hr
  | .retWhy _ _ => rfl

theorem rufeArms_of_ArmsR (Z : D.Fn → Bool) (hZ : ∀ g, C g → Z g = true) {mr l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    {arms : Arms D V l Γ Λ Λ' cs} : ArmsR A C mr arms → rufeArms Z arms = true
  | .nil => rfl
  | .cons _ _ hb hr => by
      simp only [rufeArms, Bool.and_eq_true]
      exact ⟨rufeB_of_BlockR Z hZ hb, rufeArms_of_ArmsR Z hZ hr⟩

theorem rufeGArms_of_GrundArmsR (Z : D.Fn → Bool) (hZ : ∀ g, C g → Z g = true) {mr l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    {arms : GrundArms D V l Γ Λ Λ' n} : GrundArmsR A C mr arms → rufeGArms Z arms = true
  | .nil => rfl
  | .cons _ _ hb hr => by
      simp only [rufeGArms, Bool.and_eq_true]
      exact ⟨rufeB_of_BlockR Z hZ hb, rufeGArms_of_GrundArmsR Z hZ hr⟩
end

end Tiefe
/-- `Tief` admits no more than `rufTief`. -/
theorem tief_rufTief (P : Programm D) (A : D.Lock → Prop) :
    ∀ (n : Nat) (g : D.Fn), Tief P A n g → rufTief P n g = true
  | 0, _, h => (h : False).elim
  | n + 1, _, h => rufeE_of_EndR (rufTief P n) (fun g' hg' => tief_rufTief P A n g' hg') h

/-- `TiefK` admits no more than `rufTief`. -/
theorem tiefK_rufTief (P : Programm D) (A : D.Lock → Prop) :
    ∀ (n : Nat) (g : D.Fn), TiefK P A n g → rufTief P n g = true
  | 0, _, h => (h : False).elim
  | n + 1, _, h => rufeE_of_EndR (rufTief P n) (fun g' hg' => tiefK_rufTief P A n g' hg') h.1

/-- **The bound for the frames of the adequacy theorems**: a frame of a
    function admitted by `Tief` at depth `n + 1` takes at most
    `kostenTief P passes (n + 1) g` own steps. -/
theorem frame_schritte_beschraenkt_tief (P : Programm D) (O : Orakel D) (passes : Nat)
    (A : D.Lock → Prop) (f : Faden) (g : D.Fn) (n : Nat) (hT : Tief P A (n + 1) g)
    {rho : Env D (D.params g)} {s0 : World D} {k : Nat} {M1 M2 : RufMaschineG D}
    (hE : Eintritt P f g rho s0 k M1)
    (run : SegLauf P O passes M1 M2) (hA : aktivVor f k run) :
    segZaehle run f ≤ kostenTief P passes (n + 1) g :=
  frame_schritte_beschraenkt P O passes f g n (tief_rufTief P A (n + 1) g hT) hE run hA

/-! ## 13. Foreign edges: declared costs for `axiomCall`/`bindAxiom`

    A call counts the callee's DECLARED cost (`c g` in §1, the `call counts
    DECLARED costs` rule). A foreign edge -- `Stmt.axiomCall` (a syscall, an
    `extern fn`, `prim`, `asm`) and `Block.bindAxiom` -- had no such number:
    §1 counts `1 + args` for it, `spiegelS` excludes it, and `D.Ax` carries
    no cost field. This section closes that gap as an UPPER-BOUND layer,
    without touching §1:

    * `fa : D.Ax → Nat` is the declared cost table for foreign edges (the
      counterpart of `c : D.Fn → Nat`; cf. `beispiele/96`, where a `syscall`
      carries no `costs` clause by grammar -- here the table is a Lean
      parameter, not a grammar change).
    * `fremdStmt`/`fremdBlock`/`fremdArms`/`fremdGArms`/`fremdEnd` sum the
      declared foreign costs over the syntax, with the SAME combinators as
      §1 (maximum over branches, multiplication by the domain bound under
      `traverse`/`retry`/`forever`); plain calls contribute `0` here (their
      callee's cost, foreign or not, is counted at the callee's body through
      `kostenTiefF`).
    * `kostenStmtF`/`kostenBlockF`/`kostenEndF`/`kostenSonstF` add the §1
      cost and the foreign cost. `fremd_kein_null_stmt`/`fremd_kein_null_bind`:
      no zero slip -- a foreign edge costs at least one step even at
      declared `0` (the §1 dispatch step).
    * `kostenTiefF`/`kostenTiefF_ge`: the depth bound with foreign costs on
      top; `fremd_budget_erhalten`: budget preservation over foreign calls --
      every run admitted by `rufTief`, foreign steps included, fits under it
      (by transitivity through `frame_schritte_beschraenkt`).

    Docking at `Zielsatz.ZeitAb`/`FortschrittG` (Spec.lean): `ZeitAb` has
    exactly the shape of `frame_schritte_beschraenkt`, so `kostenTiefF` is a
    drop-in right-hand side with identical premises; `FortschrittG` needs no
    new stop kind -- a foreign edge fires as a `blatt` step
    (`Stmt.istBlatt`, Maschine.lean: `axiomCall` is not in the compound
    list), hence under `schrittArt` case (A), which lowers the potential by
    at least one for EVERY leaf.

    What stays booked (not faked): re-verifying the engine with a foreign
    table (`hS1`/`hS2` of `kinv_schritt` over `kostenTiefF`, i.e. the callee
    counting its own foreign costs at the call site) and reading `fa` off
    checker syntax (`costs` on `syscalldecl`, the lane-114 gap). -/

mutual
def fremdStmt (fa : D.Ax → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Nat
  | .ite _ t e => max (fremdBlock fa pa t) (fremdBlock fa pa e)
  | .onOption _ p a => max (fremdBlock fa pa p) (fremdBlock fa pa a)
  | .onTag _ arms => fremdArms fa pa arms
  | .onWhy _ arms => fremdGArms fa pa arms
  | .locks _ _ body => fremdBlock fa pa body
  | .breaking _ body => fremdBlock fa pa body
  | .traverse t _ body => (D.count t).toNat * fremdBlock fa pa body
  | .retry n _ body ueber => n * fremdBlock fa pa body + fremdBlock fa pa ueber
  | .forever _ _ body => pa * fremdBlock fa pa body
  | .axiomCall a _ _ _ _ _ _ => fa a
  | _ => 0

def fremdBlock (fa : D.Ax → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Nat
  | .nil => 0
  | .cons s rest => fremdStmt fa pa s + fremdBlock fa pa rest
  | .bind _ rest => fremdBlock fa pa rest
  | .bindCall _ _ _ _ _ rest => fremdBlock fa pa rest
  | .bindCallInd _ _ _ _ _ rest => fremdBlock fa pa rest
  | .bindCallElse _ _ _ _ _ err rest => fremdEnd fa pa err + fremdBlock fa pa rest
  | .bindAxiom a _ _ _ _ _ _ rest => fa a + fremdBlock fa pa rest
  | .bindAxiomElse a _ _ _ _ _ _ _ err rest => fa a + fremdEnd fa pa err + fremdBlock fa pa rest
  | .regRead _ _ rest => fremdBlock fa pa rest
  | .regReadElse _ _ _ sonst rest => fremdEnd fa pa sonst + fremdBlock fa pa rest
  | .awaits _ _ _ _ rest => fremdBlock fa pa rest
  | .exchange _ _ _ _ rest => fremdBlock fa pa rest
  | .narrow _ _ _ sonst rest => fremdEnd fa pa sonst + fremdBlock fa pa rest
  | .check _ sonst rest => fremdEnd fa pa sonst + fremdBlock fa pa rest
  | .float _ _ _ _ _ rest => fremdBlock fa pa rest
  | .floatLit _ _ _ rest => fremdBlock fa pa rest
  | .floatOf _ _ _ rest => fremdBlock fa pa rest
  | .floatNarrow _ _ _ sonst rest => fremdEnd fa pa sonst + fremdBlock fa pa rest

def fremdArms (fa : D.Ax → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} : Arms D V l Γ Λ Λ' cs → Nat
  | .nil => 0
  | .cons b rest => max (fremdBlock fa pa b) (fremdArms fa pa rest)

def fremdGArms (fa : D.Ax → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} : GrundArms D V l Γ Λ Λ' n → Nat
  | .nil => 0
  | .cons b rest => max (fremdBlock fa pa b) (fremdGArms fa pa rest)

def fremdEnd (fa : D.Ax → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : Endblock D V l Γ Λ → Nat
  | .ret .. => 0
  | .retWhy .. => 0
  | .leave _ => 0
  | .next _ => 0
  | .cons s rest => fremdStmt fa pa s + fremdEnd fa pa rest
  | .bind _ rest => fremdEnd fa pa rest
  | .bindCall _ _ _ _ _ rest => fremdEnd fa pa rest
  | .bindAxiom a _ _ _ _ _ _ rest => fa a + fremdEnd fa pa rest
  | .bindAxiomElse a _ _ _ _ _ _ _ err rest => fa a + fremdEnd fa pa err + fremdEnd fa pa rest
end
/-- The §1 cost plus the declared foreign cost, per statement form. -/
def kostenStmtF (fa : D.Ax → Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') : Nat :=
  kostenStmt c pa s + fremdStmt fa pa s

/-- The §1 cost plus the declared foreign cost, per block. -/
def kostenBlockF (fa : D.Ax → Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') : Nat :=
  kostenBlock c pa b + fremdBlock fa pa b

/-- The §1 cost plus the declared foreign cost, per end block. -/
def kostenEndF (fa : D.Ax → Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) : Nat :=
  kostenEnd c pa e + fremdEnd fa pa e

/-- The §1 cost plus the declared foreign cost, per `else` branch. -/
def kostenSonstF (fa : D.Ax → Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) : Nat :=
  kostenSonst c pa e + fremdEnd fa pa e

theorem kostenStmtF_ge (fa : D.Ax → Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') :
    kostenStmt c pa s ≤ kostenStmtF fa c pa s := by
  simp only [kostenStmtF]; omega

theorem kostenBlockF_ge (fa : D.Ax → Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') :
    kostenBlock c pa b ≤ kostenBlockF fa c pa b := by
  simp only [kostenBlockF]; omega

theorem kostenEndF_ge (fa : D.Ax → Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) :
    kostenEnd c pa e ≤ kostenEndF fa c pa e := by
  simp only [kostenEndF]; omega

theorem kostenSonstF_ge (fa : D.Ax → Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) :
    kostenSonst c pa e ≤ kostenSonstF fa c pa e := by
  simp only [kostenSonstF]; omega

/-- A foreign statement site counts exactly its declared cost. -/
theorem fremd_axiomCall (fa : D.Ax → Nat) (pa : Nat) (V : Vertrag D) {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)} (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (h : D.aerg a = none)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) :
    fremdStmt (V := V) fa pa (Stmt.axiomCall (V := V) (l := l) a args h hw hg hd hgd) = fa a := rfl

/-- A foreign bind site counts exactly its declared cost plus its continuation. -/
theorem fremd_bindAxiom (fa : D.Ax → Nat) (pa : Nat) (V : Vertrag D) {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (he : D.aerg a = some τ)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Block D V l (τ :: Γ) Λ Λ') :
    fremdBlock (V := V) fa pa (Block.bindAxiom (V := V) (l := l) a args he hw hg hd hgd rest)
      = fa a + fremdBlock fa pa rest := rfl

/-- No zero slip, statement site: a foreign call costs at least one step even
    at declared `0` (the §1 dispatch step). -/
theorem fremd_kein_null_stmt (fa : D.Ax → Nat) (c : D.Fn → Nat) (pa : Nat)
    (V : Vertrag D) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (a : D.Ax)
    (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) :
    1 ≤ kostenStmtF (V := V) fa c pa (Stmt.axiomCall (V := V) (l := l) a args h hw hg hd hgd) := by
  simp only [kostenStmtF, kostenStmt]; omega


