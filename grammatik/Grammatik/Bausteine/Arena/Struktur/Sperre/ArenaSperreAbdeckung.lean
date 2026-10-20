/-
  File:      Grammatik/ArenaSperreAbdeckung.lean
  Subject:   A LOOP-FREE RECOGNIZED BODY IS COVERED BY THE MACHINE'S FRAGMENT (PLAN-DYNAMIC.md section 8a.3, premise 2,
             finding 6 of 8a.2): `ErkE K a e` without a loop is `EndR A C e` -- the coverage the machine bridge
             `erkE_maschine` took as a SECOND premise now follows from the certificate.

  `EndR`/`BlockR` (RufAdaequatRufG) cover the statement forms the call machine realises by small steps: leaf stores, `ite`,
  `narrow`/`check` with a covered `else`, `return`/`return why`. Every move of the recognizer unfolds into exactly those
  (`narrow` for the guarded reads and allocations, `assignSlot`/`assignGlob` for the stores), and an `else` of the recognizer is a
  bare `return` (`Rein`). The loop moves (`forever`/`traverse`/`retry`) are NOT covered: `BlockR.narrow`/`check` need a block with
  `l = false` and a loop body has `l = true` -- so the theorem asks for `schleifenfrei`, a predicate that looks through the
  statement forms of the fragment and refuses a loop.
-/
import Grammatik.Bausteine.Arena.Struktur.Sperre.ArenaSperreBruecke

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette Gabbro.Grammatik.Zielsatz

variable {D : Deklaration}

set_option linter.unusedSimpArgs false

section Schleifenfrei
variable {V : Vertrag D}

mutual

/-- The statement is not a loop, and contains none through `ite` (only the forms of the recognized fragment are looked through;
    every other form counts as loop-free: `Erk`/`ErkE` build nothing else). -/
def Stmt.schleifenfrei {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => t.schleifenfrei && e.schleifenfrei
  | .traverse .. => false
  | .retry .. => false
  | .forever .. => false
  | _ => true

def Block.schleifenfrei {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Bool
  | .cons s rest => s.schleifenfrei && rest.schleifenfrei
  | .narrow _ _ _ sonst rest => sonst.schleifenfrei && rest.schleifenfrei
  | .check _ sonst rest => sonst.schleifenfrei && rest.schleifenfrei
  | .bind _ rest => rest.schleifenfrei
  | _ => true

def Endblock.schleifenfrei {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Endblock D V l Γ Λ → Bool
  | .cons s rest => s.schleifenfrei && rest.schleifenfrei
  | _ => true

end

/-- The predicate refuses a loop: a body with `forever`, `traverse` or `retry` is not `schleifenfrei` (the hypothesis of
    `erkE_endR` is not vacuous, and the planted counter-case is a real one). -/
theorem schleife_nicht_frei {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (an : D.Annahme) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (rest : Block D V l Γ Λ Λ) :
    (Block.cons (Stmt.forever an inv body) rest).schleifenfrei = false := by
  simp [Block.schleifenfrei, Stmt.schleifenfrei]

end Schleifenfrei

section Abdeckung
variable {V : Vertrag D} {A' : FreiForm D} {K : Dekl A'} {Alk : D.Lock → Prop} {C : D.Fn → Prop}

/-- A bare `else` is covered. -/
theorem endR_of_rein {Γ : Ctx} {Λ : List (Res D)} {voll : Endblock D V false Γ Λ} (h : Rein voll) : EndR Alk C voll := by
  cases h with
  | ret e hΛ => exact EndR.ret e hΛ
  | retWhy r hΛ => exact EndR.retWhy (Γ := Γ) r hΛ

theorem blockR_slot {Γ : Ctx} {Λ Λ' : List (Res D)} (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t))) (e : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ)
    {rest : Block D V false Γ Λ Λ'} (h : BlockR Alk C true rest) :
    BlockR Alk C true (Block.cons (Stmt.assignSlot t f i e hw hL) rest) :=
  BlockR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) h

theorem blockR_glob {Γ : Ctx} {Λ Λ' : List (Res D)} (g : D.Glob) (e : Expr D Γ Λ (D.gtyp g))
    (hw : V.gschreibt g = true) (hL : gdarf D g Λ) {rest : Block D V false Γ Λ Λ'} (h : BlockR Alk C true rest) :
    BlockR Alk C true (Block.cons (Stmt.assignGlob g e hw hL) rest) :=
  BlockR.cons _ _ (StmtR.blatt _ (BlattG.assignGlob _ _ _ _)) h

/-- **A loop-free recognized block is covered.** -/
theorem erk_blockR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a a' : Abs} {b : Block D V l Γ Λ Λ'}
    (h : Erk K a b a') : l = false → b.schleifenfrei = true → BlockR Alk C true b := by
  induction h with
  | nil => intro _ _; exact BlockR.nil
  | push d hd x hwT hLT hwG hLG rest hx h ih =>
    intro hl hs
    subst hl
    simp only [Block.linkPush, Block.schleifenfrei, Stmt.schleifenfrei, Bool.true_and] at hs
    exact blockR_slot _ _ _ _ _ _ (blockR_glob _ _ _ _ (ih rfl hs))
  | pop d hd hwG hLG hLT voll rest hv h ih =>
    intro hl hs
    subst hl
    simp only [Block.linkPop, Block.schleifenfrei, Stmt.schleifenfrei, Bool.true_and, Bool.and_eq_true] at hs
    exact BlockR.narrow _ _ _ _ _ (endR_of_rein hv) (blockR_glob _ _ _ _ (ih rfl hs.2))
  | unlink d hd p hwT hLT voll rest hp hv h ih =>
    intro hl hs
    subst hl
    simp only [Block.linkUnlink, Block.schleifenfrei, Stmt.schleifenfrei, Bool.true_and, Bool.and_eq_true] at hs
    exact BlockR.narrow _ _ _ _ _ (endR_of_rein hv) (blockR_slot _ _ _ _ _ _ (ih rfl hs.2))
  | kopf d hd hLG voll rest hv h ih =>
    intro hl hs
    subst hl
    simp only [Block.linkKopfBind, Block.schleifenfrei, Bool.and_eq_true] at hs
    exact BlockR.narrow _ _ _ _ _ (endR_of_rein hv) (ih rfl hs.2)
  | nach d hd p hLT voll rest hp hv h ih =>
    intro hl hs
    subst hl
    simp only [Block.linkNachBind, Block.schleifenfrei, Bool.and_eq_true] at hs
    exact BlockR.narrow _ _ _ _ _ (endR_of_rein hv) (ih rfl hs.2)
  | frisch v hwT hLT hwG hLG voll rest hv h ih =>
    intro hl hs
    subst hl
    simp only [Block.arenaAlloc, Block.arenaRumpf, Block.schleifenfrei, Stmt.schleifenfrei, Bool.true_and,
      Bool.and_eq_true] at hs
    exact BlockR.narrow _ _ _ _ _ (endR_of_rein hv) (blockR_slot _ _ _ _ _ _ (blockR_glob _ _ _ _ (ih rfl hs.2)))
  | nimm v hwT hLT hwK hLK voll rest hv h ih =>
    intro hl hs
    subst hl
    simp only [Block.freiNimm, Block.schleifenfrei, Stmt.schleifenfrei, Bool.true_and, Bool.and_eq_true] at hs
    exact BlockR.narrow _ _ _ _ _ (endR_of_rein hv)
      (blockR_glob _ _ _ _ (blockR_slot _ _ _ _ _ _ (ih rfl hs.2)))
  | frei x hwT hLT hwK hLK rest hx h ih =>
    intro hl hs
    subst hl
    simp only [Block.freiVar, Block.schleifenfrei, Stmt.schleifenfrei, Bool.true_and] at hs
    exact blockR_slot _ _ _ _ _ _ (blockR_glob _ _ _ _ (ih rfl hs))
  | wachs n hn hwK hLK voll rest hv h ih =>
    intro hl hs
    subst hl
    simp only [Block.dynGrowB, Block.schleifenfrei, Stmt.schleifenfrei, Bool.true_and, Bool.and_eq_true] at hs
    exact BlockR.narrow _ _ _ _ _ (endR_of_rein hv) (blockR_glob _ _ _ _ (ih rfl hs.2))
  | pruefe c voll rest hv h ih =>
    intro hl hs
    subst hl
    simp only [Block.schleifenfrei, Bool.and_eq_true] at hs
    exact BlockR.check _ _ _ (endR_of_rein hv) (ih rfl hs.2)
  | nutzlast i e hwT hLT rest h ih =>
    intro hl hs
    subst hl
    simp only [Block.schleifenfrei, Stmt.schleifenfrei, Bool.true_and] at hs
    exact blockR_slot _ _ _ _ _ _ (ih rfl hs)
  | ite c t e rest ht he h1 h2 h iht ihe ih =>
    intro hl hs
    subst hl
    simp only [Block.schleifenfrei, Stmt.schleifenfrei, Bool.and_eq_true] at hs
    exact BlockR.cons _ _ (StmtR.ite _ _ _ (iht rfl hs.1.1) (ihe rfl hs.1.2)) (ih rfl hs.2)
  | wurzelEin b hb x hwT hLT hwG hLG voll rest hx hv h ih =>
    intro hl hs
    subst hl
    simp only [Block.wurzelEin, Block.wurzelSetze, Block.schleifenfrei, Stmt.schleifenfrei, Bool.true_and,
      Bool.and_eq_true] at hs
    exact BlockR.check _ _ _ (endR_of_rein hv)
      (blockR_slot _ _ _ _ _ _ (blockR_slot _ _ _ _ _ _ (blockR_glob _ _ _ _ (ih rfl hs.2))))
  | wurzelKopf b hb hLG voll rest hv h ih =>
    intro hl hs
    subst hl
    simp only [Block.linkKopfBind, Block.schleifenfrei, Bool.and_eq_true] at hs
    exact BlockR.narrow _ _ _ _ _ (endR_of_rein hv) (ih rfl hs.2)
  | kind b hb C' hC p hLT voll rest hp hv h ih =>
    intro hl hs
    subst hl
    simp only [Block.linkNachBind, Block.schleifenfrei, Bool.and_eq_true] at hs
    exact BlockR.narrow _ _ _ _ _ (endR_of_rein hv) (ih rfl hs.2)
  | haengen b hb Cp Co hs' p i hwT hLT voll rest hp hi hv h ih =>
    intro hl hs
    subst hl
    simp only [Block.haengen, Block.blattEin, Block.schleifenfrei, Stmt.schleifenfrei, Bool.true_and,
      Bool.and_eq_true] at hs
    exact BlockR.check _ _ _ (endR_of_rein hv)
      (blockR_slot _ _ _ _ _ _ (blockR_slot _ _ _ _ _ _ (blockR_slot _ _ _ _ _ _ (ih rfl hs.2))))
  | abschneiden b hb C' hC p hwT hLT voll voll2 rest hp hv hv2 h ih =>
    intro hl hs
    subst hl
    simp only [Block.abschneiden, Block.schleifenfrei, Stmt.schleifenfrei, Bool.true_and, Bool.and_eq_true] at hs
    exact BlockR.narrow _ _ _ _ _ (endR_of_rein hv)
      (BlockR.check _ _ _ (endR_of_rein hv2) (blockR_slot _ _ _ _ _ _ (ih rfl hs.2.2)))
  | wurzelAus b hb hwG hLG hLT voll voll2 rest hv hv2 h ih =>
    intro hl hs
    subst hl
    simp only [Block.wurzelAus, Block.schleifenfrei, Stmt.schleifenfrei, Bool.true_and, Bool.and_eq_true] at hs
    exact BlockR.narrow _ _ _ _ _ (endR_of_rein hv)
      (BlockR.check _ _ _ (endR_of_rein hv2) (blockR_glob _ _ _ _ (ih rfl hs.2.2)))
  | forever an inv body rest hin hb hs' h ihb ih =>
    intro hl hs
    simp [Block.schleifenfrei, Stmt.schleifenfrei] at hs
  | traverse t inv body rest hin hb hs' h ihb ih =>
    intro hl hs
    simp [Block.schleifenfrei, Stmt.schleifenfrei] at hs
  | retry n bis body ueber rest hin hb hs' hu h3 h4 h ihb ihu ih =>
    intro hl hs
    simp [Block.schleifenfrei, Stmt.schleifenfrei] at hs

/-- **A loop-free recognized function body is covered** -- the premise `EndR` of `erkE_maschine`, from the certificate. -/
theorem erkE_endR {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {a : Abs} {e : Endblock D V l Γ Λ}
    (h : ErkE K a e) : l = false → e.schleifenfrei = true → EndR Alk C e := by
  induction h with
  | ret ex hΛ => intro hl _; subst hl; exact EndR.ret ex hΛ
  | retWhy r hΛ => intro hl _; subst hl; exact EndR.retWhy (Γ := Γ) r hΛ
  | nutzlast i e hwT hLT rest h ih =>
    intro hl hs
    subst hl
    simp only [Endblock.schleifenfrei, Stmt.schleifenfrei, Bool.true_and] at hs
    exact EndR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) (ih rfl hs)
  | ite c t e rest ht he h1 h2 h ihr =>
    intro hl hs
    subst hl
    simp only [Endblock.schleifenfrei, Stmt.schleifenfrei, Bool.and_eq_true] at hs
    exact EndR.cons _ _ (StmtR.ite _ _ _ (erk_blockR ht rfl hs.1.1) (erk_blockR he rfl hs.1.2)) (ihr rfl hs.2)
  | forever an inv body rest hin hb hs' h ih =>
    intro hl hs
    simp [Endblock.schleifenfrei, Stmt.schleifenfrei] at hs
  | traverse t inv body rest hin hb hs' h ih =>
    intro hl hs
    simp [Endblock.schleifenfrei, Stmt.schleifenfrei] at hs
  | retry n bis body ueber rest hin hb hs' hu h3 h4 h ih =>
    intro hl hs
    simp [Endblock.schleifenfrei, Stmt.schleifenfrei] at hs

/-- **The machine bridge with ONE certificate.** A loop-free recognized writer needs no separate coverage proof: `erkE_endR`
    derives `EndR` from the derivation, and `erkE_maschine` does the rest. -/
theorem erkE_maschine_erk (P : Programm D) (O : Orakel D) (passes n : Nat)
    (M : RufMaschineG D) (f : Faden) (fn : D.Fn) (rho : Env D (D.params fn))
    (s0 : World D) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (spur : List (Ereignis D)) (log : List (RufEreignisF D)) {Γ : Ctx}
    {Λ : List (Res D)} (ρ : Env D Γ) (b : Endblock D (vertragVon D fn) false Γ Λ)
    (hE : ErkE K Abs.leer b) (hs : b.schleifenfrei = true)
    (hM : M.faeden f = ⟨caller :: rst, ⟨fn, rho, s0, ⟨false, Γ, Λ, ρ, .ende b⟩⟩, spur, log⟩)
    (hnw : caller.wartend = false) (hΛ : HeldGenau Λ (offen spur))
    (hfrei : ∀ L, Alk L → RufFreiG M f L) (hOk : K.Ok (M.weltVon f))
    (σ' : World D) (v : ErgVal D (vertragVon D fn).erg)
    (hexec : execEnd O passes (rufRumpf P O passes n) b (M.weltVon f) ρ = .zurueck σ' v) :
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      M'.faeden f = ⟨rst, caller, σ'.spur, RufEreignisF.rueck fn rho v s0 σ' :: (ext ++ log)⟩ ∧
      M'.speicher = σ'.speicher ∧ (∀ g, g ≠ f → M'.faeden g = M.faeden g) ∧ K.Ok (M'.speicher.welt []) :=
  erkE_maschine K P O passes n M f fn rho s0 caller rst spur log ρ b Alk (erkE_endR hE rfl hs) hE hM hnw hΛ hfrei hOk
    σ' v hexec

end Abdeckung

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.erk_blockR
#print axioms Gabbro.Grammatik.erkE_endR
#print axioms Gabbro.Grammatik.erkE_maschine_erk
