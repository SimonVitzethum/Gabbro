module
public import Grammatik.Logik.Fortschritt.KostenG.T4.Teil1Basis
import all Grammatik.Logik.Fortschritt.KostenG.T4.Teil1Basis

public import Grammatik.Logik.Fortschritt.KostenG.T3

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}
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
    StmtR A C mr s → rufeS Z (fun _ => false) true s = true
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
    BlockR A C mr b → rufeB Z (fun _ => false) true b = true
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
  | .awaits _ _ _ _ _ _ hr => by simp only [rufeB]; exact rufeB_of_BlockR Z hZ hr
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
    EndR A C e → rufeE Z (fun _ => false) true e = true
  | .ret _ _ => rfl
  | .cons _ _ hs hr => by
      simp only [rufeE, Bool.and_eq_true]
      exact ⟨rufeS_of_StmtR Z hZ hs, rufeE_of_EndR Z hZ hr⟩
  | .bind _ _ hr => by simp only [rufeE]; exact rufeE_of_EndR Z hZ hr
  | .retWhy _ _ => rfl

  | .float _ _ _ _ _ _ hr => by simp only [rufeE]; exact rufeE_of_EndR Z hZ hr
  | .floatLit _ _ _ _ hr => by simp only [rufeE]; exact rufeE_of_EndR Z hZ hr
  | .floatOf _ _ _ _ hr => by simp only [rufeE]; exact rufeE_of_EndR Z hZ hr
  | .floatNarrow _ _ _ _ _ hs hr => by
      simp only [rufeE, Bool.and_eq_true]
      exact ⟨rufeE_of_EndR Z hZ hs, rufeE_of_EndR Z hZ hr⟩

theorem rufeArms_of_ArmsR (Z : D.Fn → Bool) (hZ : ∀ g, C g → Z g = true) {mr l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    {arms : Arms D V l Γ Λ Λ' cs} : ArmsR A C mr arms → rufeArms Z (fun _ => false) true arms = true
  | .nil => rfl
  | .cons _ _ hb hr => by
      simp only [rufeArms, Bool.and_eq_true]
      exact ⟨rufeB_of_BlockR Z hZ hb, rufeArms_of_ArmsR Z hZ hr⟩

theorem rufeGArms_of_GrundArmsR (Z : D.Fn → Bool) (hZ : ∀ g, C g → Z g = true) {mr l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    {arms : GrundArms D V l Γ Λ Λ' n} : GrundArmsR A C mr arms → rufeGArms Z (fun _ => false) true arms = true
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

end Gabbro.Grammatik
