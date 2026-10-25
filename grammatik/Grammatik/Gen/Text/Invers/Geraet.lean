/-
  File:      Grammatik/Gen/Text/Invers/Geraet.lean
  Subject:   REGISTERS AND ATOMICS READ BACK (Tier 2.1, step 2c): `d.r{k}` through the one device handle `d`
             (`uRegOrt`), the register write and read, `g = e publishes { .. }` and `let x = g awaits { .. }` with
             exactly the declared payload.
-/
import Grammatik.Gen.Text.Invers.Ruf
import Grammatik.Gen.Text.Invers.Nutzlast

namespace Gabbro.Grammatik.Gen.Text

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

variable {z : Spez} {V : Vertrag z.deklaration}

theorem namenGleich_map : ∀ (ws : List String), uNamenGleich (ws.map String.toList) ws = true
  | [] => rfl
  | w :: ws => by simp [uNamenGleich, namenGleich_map ws]

theorem flatten_kopf (a : String) (l : List String) :
    ∃ tail, (((a :: l).map fun n => [nameTok n]).intersperse [Token.zeichen ","]).flatten = nameTok a :: tail := by
  cases l with
  | nil => exact ⟨[], by simp⟩
  | cons b l => exact ⟨_, by simp [List.intersperse_cons_cons]; rfl⟩

theorem nicht_nothing (k : Nat) (tail : List Token) :
    strEq (String.ofList (render (nameTok (nGlob k) :: tail))) "nothing" = false := by
  unfold strEq
  rw [String.toList_ofList]
  simp only [render, spell_nameTok, nGlob_toList]
  simp

/-- The payload of `publishes`: the declared statics, by name. -/
theorem nutzNamen_ok (gs : List z.deklaration.Glob) :
    uNutzNamen (nutzText z gs) = (gs.map fun g => nGlob (gN z g)).map String.toList := by
  cases gs with
  | nil => simp [nutzText, uNutzNamen]; decide
  | cons g gs =>
    have hw := woerter_namen ((g :: gs).map fun g => nGlob (gN z g)) (by
      intro w hw
      simp only [List.mem_map] at hw
      obtain ⟨h, _, rfl⟩ := hw
      exact nGlob_wort _)
    have hm : (g :: gs).map (fun g => [nameTok (nGlob (gN z g))]) =
        ((g :: gs).map fun g => nGlob (gN z g)).map (fun n => [nameTok n]) := by simp [List.map_map]
    obtain ⟨tail, ht⟩ := flatten_kopf (nGlob (gN z g)) (gs.map fun g => nGlob (gN z g))
    have ht' : (((g :: gs).map fun g => [nameTok (nGlob (gN z g))]).intersperse [Token.zeichen ","]).flatten =
        nameTok (nGlob (gN z g)) :: tail := by rw [hm]; simpa using ht
    show uNutzNamen (if (g :: gs).isEmpty then "nothing" else renderText
      ((((g :: gs).map fun g => [nameTok (nGlob (gN z g))]).intersperse [Token.zeichen ","]).flatten)) = _
    simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, uNutzNamen, renderText]
    rw [ht', nicht_nothing]
    simp only [Bool.false_eq_true, ite_false, String.toList_ofList]
    rw [← ht', hm, hw]

/-- The payload of `awaits` (braces around nothing are the empty text). -/
theorem nutzNamenA_ok (gs : List z.deklaration.Glob) :
    uNutzNamen (nutzTextA z gs) = (gs.map fun g => nGlob (gN z g)).map String.toList := by
  unfold nutzTextA
  cases gs with
  | nil => simp [uNutzNamen, uWoerter, strEq_eq]
  | cons g gs => simpa using nutzNamen_ok (g :: gs)

/-- The register place `d.r{k}`. -/
theorem regOrt_ok {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (r : z.deklaration.Reg) :
    ∃ g, uRegOrt ctx (regOrt z r) = some (.ok g) ∧ g.dev = "Dev" ∧ g.name = nReg (rN z r) ∧ g.pruefung = none ∧
      some g.art = artErg (z.deklaration.rtyp r) ∧ (g.bool = true ↔ z.deklaration.rtyp r = .bool) := by
  obtain ⟨g, hf, hd, hn, hp, ha, hb⟩ := H.reg r
  have hnames : (ctx.names.any fun x => strEq x "d") = false := by
    rw [List.any_eq_false]
    intro n hm
    rcases H.namen n hm with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · simp [strEq_kopf (nVar_toList k) (show "d".toList = 'd' :: [] from rfl) (by decide)]
    · simp [strEq_kopf (nZeiger_toList k) (show "d".toList = 'd' :: [] from rfl) (by decide)]
  refine ⟨g, ?_, hd, hn, hp, ha, hb⟩
  simp only [regOrt, uRegOrt, hnames, Bool.false_eq_true, ite_false, H.griff r]
  simp only [hf]

/-- `d.r = e;` -/
theorem anw1_regWrite {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (tabs : List UTab) (koepfe : List UFnKopf) (r : z.deklaration.Reg) (w : SExpr) :
    (z.deklaration.rtyp r = .bool → ∀ b, uBool ctx w = .ok b →
      uAnw1 ctx tabs koepfe (.set (regOrt z r) "=" w) = .ok (.regWriteB "Dev" (nReg (rN z r)) b)) ∧
    (z.deklaration.rtyp r ≠ .bool → ∀ u, uWertBody ctx w = .ok u →
      uAnw1 ctx tabs koepfe (.set (regOrt z r) "=" w) = .ok (.regWrite "Dev" (nReg (rN z r)) u)) := by
  obtain ⟨g, hg, hd, hn, _, _, hb⟩ := regOrt_ok H r
  have hs : strEq "=" "=" = true := by decide
  refine ⟨fun ht b hw => ?_, fun ht u hw => ?_⟩
  · simp only [uAnw1, hg, hs, Bool.not_true, Bool.false_eq_true, ite_false, hb.2 ht, ite_true, hw, hd, hn]
  · have : g.bool = false := by cases h : g.bool <;> simp_all
    simp only [uAnw1, hg, hs, Bool.not_true, Bool.false_eq_true, ite_false, this, hw, hd, hn]

/-- `let x = d.r;` -/
theorem bindWert_regRead {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (tabs : List UTab) (koepfe : List UFnKopf) (r : z.deklaration.Reg) (x : String)
    (a : UParamArt) (ha : artErg (z.deklaration.rtyp r) = some a) :
    ∃ ty, uBindWert ctx tabs koepfe false x none (regOrt z r) =
      .ok (.regRead x "Dev" (nReg (rN z r)), ctxMit ctx x a ty 0 [] ctx.loops) := by
  obtain ⟨g, hg, hd, hn, hp, hart, _⟩ := regOrt_ok H r
  rw [ha] at hart
  simp only [Option.some.injEq] at hart
  refine ⟨g.ty, ?_⟩
  simp only [uBindWert, hg, Bool.or_false, Option.isSome_none, Bool.false_eq_true, ite_false, hp, hd, hn, hart,
    mitLokal_eq ctx H.muts]

/-- `g = e publishes { .. };` at an atomic, with its declared payload. -/
theorem anw1_publish {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (tabs : List UTab) (koepfe : List UFnKopf) (g : z.deklaration.Glob)
    (ha : z.deklaration.atomar g = true) (w : SExpr) :
    (z.deklaration.gtyp g = .bool → ∀ b, uBool ctx w = .ok b →
      uAnw1 ctx tabs koepfe (.emit (.variable (nGlob (gN z g))) w (nutzText z (z.deklaration.nutzlast g))) =
        .ok (.storeAtomB (nGlob (gN z g)) b)) ∧
    (z.deklaration.gtyp g ≠ .bool → ∀ u, uWertBody ctx w = .ok u →
      uAnw1 ctx tabs koepfe (.emit (.variable (nGlob (gN z g))) w (nutzText z (z.deklaration.nutzlast g))) =
        .ok (.storeAtom (nGlob (gN z g)) u)) := by
  obtain ⟨gl, hf, hb, _, hat, hn, hwt⟩ := H.glob g
  have hgl : uNamenGleich (uNutzNamen (nutzText z (z.deklaration.nutzlast g))) gl.nutzlast = true := by
    rw [nutzNamen_ok, hn]; exact namenGleich_map _
  refine ⟨fun ht b hw => ?_, fun ht u hw => ?_⟩
  · have : gl.ty = .bool := hb.2 ht
    simp only [uAnw1, uAtomSchreib, hf, hat, ha, Bool.not_true, Bool.false_eq_true, ite_false, hgl, this, hw]
  · cases h : gl.ty with
    | bool => exact absurd (hb.1 h) ht
    | int _ _ => simp only [uAnw1, uAtomSchreib, hf, hat, ha, Bool.not_true, Bool.false_eq_true, ite_false, hgl, h, hw]
    | wert τ => exact absurd h (hwt τ)

theorem reihe_emit (tabs : List UTab) (koepfe : List UFnKopf) (f : Nat) (ctx : UCtx) (ziel w : SExpr) (p : String)
    (rest : List SAnw) (st : UStmt) (xs : List UStmt) (cE : UCtx) (h1 : uAnw1 ctx tabs koepfe (.emit ziel w p) = .ok st)
    (h2 : uAnwReihe tabs koepfe f ctx rest = .ok (xs, cE)) :
    uAnwReihe tabs koepfe (f + 1) ctx (.emit ziel w p :: rest) = .ok (st :: xs, cE) := by
  rw [uAnwReihe] <;> first | (simp only [h1, h2]) | (intros; simp_all)

/-- `let x = g awaits { .. };` at an atomic, with its declared payload. -/
theorem reihe_await {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (tabs : List UTab) (koepfe : List UFnKopf) (f : Nat) (g : z.deklaration.Glob)
    (ha : z.deklaration.atomar g = true) (x : String) (a : UParamArt) (hart : artErg (z.deklaration.gtyp g) = some a)
    (rest : List SAnw) :
    ∃ ty, ∀ xs cE, uAnwReihe tabs koepfe f (ctxMit ctx x a ty 0 [] ctx.loops) rest = .ok (xs, cE) →
      uAnwReihe tabs koepfe (f + 1) ctx
        (.await x (.variable (nGlob (gN z g))) (nutzTextA z (z.deklaration.nutzlast g)) :: rest) =
        .ok (.awaitBind x (nGlob (gN z g)) :: xs, cE) := by
  obtain ⟨gl, hf, hb, _, hat, hn, hwt⟩ := H.glob g
  have hgl : uNamenGleich (uNutzNamen (nutzTextA z (z.deklaration.nutzlast g))) gl.nutzlast = true := by
    rw [nutzNamenA_ok, hn]; exact namenGleich_map _
  cases h : gl.ty with
  | bool =>
    have ht := hb.1 h
    rw [ht] at hart; simp only [artErg, Option.some.injEq] at hart; subst hart
    refine ⟨.bool, fun xs cE hr => ?_⟩
    rw [uAnwReihe]
    simp only [hf, hat, ha, Bool.not_true, Bool.false_eq_true, ite_false, hgl, h, H.muts, List.filter_nil]
    simp only [uMitLokal, ctxMit] at hr ⊢
    simp only [hr]
  | wert τ => exact absurd h (hwt τ)
  | int lo hi =>
    have ht : z.deklaration.gtyp g ≠ .bool := fun e => by rw [← hb] at e; rw [h] at e; cases e
    refine ⟨.int lo hi, fun xs cE hr => ?_⟩
    have : a = .int := by
      cases hg : z.deklaration.gtyp g with
      | bool => exact absurd hg ht
      | int _ _ => rw [hg] at hart; simp [artErg] at hart; exact hart.symm
      | _ => rw [hg] at hart; simp [artErg] at hart
    subst this
    rw [uAnwReihe]
    simp only [hf, hat, ha, Bool.not_true, Bool.false_eq_true, ite_false, hgl, h, H.muts, List.filter_nil]
    simp only [uMitLokal, ctxMit] at hr ⊢
    simp only [hr]

end Gabbro.Grammatik.Gen.Text