/-
  File:      stage0/Stage0/Schnell/Sim/SD.lean
  Subject:   The simulation of the normal form, rules 31 .. 40 of `RufSchrittG` (`Schnell/Sim.lean`): a step of
             `normal ww M` under the fast oracle is a step of `M` under the machine's oracle, to the same normal form.
-/
import Stage0.Schnell.Werkzeug

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration} {P : Programm D} {OF OM : Orakel D} {passes : Nat} {ww : World D}

theorem sim_wiederUeber {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (bis : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ Λ)
      (ueber : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ)
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .wieder 0 bis body ueber k⟩) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann (.cons (.ite bis .nil ueber) .nil) k⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann (.cons (.ite bis .nil ueber) .nil) k⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  refine ⟨_, RufSchrittG.wiederUeber M f l Γ Λ bis body ueber k ρ hhead, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_wiederWeiter {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (n : Nat) (bis : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ Λ)
      (ueber : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ)
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .wieder (n + 1) bis body ueber k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ bis.orte)
      (hw : wahr? (eval σ₁ bis σ₁ ρ) = true)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, k⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, k⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  refine ⟨_, RufSchrittG.wiederWeiter M f l Γ Λ n bis body ueber k ρ hhead ((M.weltVon f).lese Λ bis.orte) (rfl) ?_ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_wiederSchritt {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (n : Nat) (bis : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ Λ)
      (ueber : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ)
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .wieder (n + 1) bis body ueber k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ bis.orte)
      (hw : wahr? (eval σ₁ bis σ₁ ρ) = false)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨true, Γ, Λ, ρ,
              .dann body (.wiederRest n bis body ueber k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨true, Γ, Λ, ρ,
              .dann body (.wiederRest n bis body ueber k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  refine ⟨_, RufSchrittG.wiederSchritt M f l Γ Λ n bis body ueber k ρ hhead ((M.weltVon f).lese Λ bis.orte) (rfl) ?_ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_wiederFort {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (n : Nat) (bis : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ Λ)
      (ueber : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ)
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨true, Γ, Λ, ρ, .wiederRest n bis body ueber k⟩) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .wieder n bis body ueber k⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .wieder n bis body ueber k⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  refine ⟨_, RufSchrittG.wiederFort M f l Γ Λ n bis body ueber k ρ hhead, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannForever {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (a : D.Annahme) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ Λ)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ'')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.forever a inv body) rest) k⟩) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .ewig a passes inv body (.dann rest k)⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .ewig a passes inv body (.dann rest k)⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  refine ⟨_, RufSchrittG.dannForever M f l Γ Λ Λ' Λ'' a inv body rest k ρ hhead, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_ewigWeiter {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ Λ)
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ewig a (n + 1) inv body k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = ((normal ww M).weltVon f).lese Λ inv.orte)
      (hw : wahr? (eval σ₁ inv σ₁ ρ) = true)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ ((normal ww M).faeden f).spur)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur)) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨true, Γ, Λ, ρ,
              .dann body (.ewigRest a n inv body k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨true, Γ, Λ, ρ,
              .dann body (.ewigRest a n inv body k)⟩⟩,
            σ₁.spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs₁
  refine ⟨_, RufSchrittG.ewigWeiter M f l Γ Λ a n inv body k ρ hhead ((M.weltVon f).lese Λ inv.orte) (rfl) ?_ neu ?_ ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_ewigFort {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ Λ)
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨true, Γ, Λ, ρ, .ewigRest a n inv body k⟩) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .ewig a n inv body k⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .ewig a n inv body k⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  refine ⟨_, RufSchrittG.ewigFort M f l Γ Λ a n inv body k ρ hhead, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_rufDann {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (g : D.Fn) (args : Args D Γ Λ (D.params g))
      (hp : RufPasst D (vertragVon D ((normal ww M).faeden f).kopf.f) (D.signatur g) Λ)
      (hr : D.gruende g = 0)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ (nach D g Λ) Λ'')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.call g args hp hr) rest) k⟩)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur))
      (s0 : World D)
      (hs0 : s0 = ((normal ww M).weltVon f).lese Λ args.orte)
      (rho : Env D (D.params g))
      (hrho : rho = evalArgs s0 args s0 ρ)
      (neu : List (Ereignis D))
      (hneu : s0.spur = neu ++ ((normal ww M).faeden f).spur) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
              ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩ :: ((normal ww M).faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, .ende (P.rumpf g)⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
              ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩ :: ((normal ww M).faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, .ende (P.rumpf g)⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs0
  refine ⟨_, RufSchrittG.rufDann M f l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead ?_ ((M.weltVon f).lese Λ args.orte) (rfl) rho ?_ neu ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannCallInd {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (n : Nat) (p : Expr D Γ Λ (.fnptr n))
      (args : Args D Γ Λ (D.sigNr n).params)
      (hp : RufPasst D (vertragVon D ((normal ww M).faeden f).kopf.f) (D.sigNr n) Λ)
      (hr : (D.sigNr n).gruende = 0)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ (nachSig D (D.sigNr n) Λ) Λ'')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.callInd p args hp hr) rest) k⟩)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur))
      (s0 : World D)
      (hs0 : s0 = ((normal ww M).weltVon f).lese Λ (p.orte ++ args.orte))
      (g : D.Fn) (hg : D.passt g n = true)
      (hv : eval s0 p s0 ρ = ⟨g, hg⟩)
      (rho : Env D (D.params g))
      (hrho : rho = umsig hg (evalArgs s0 args s0 ρ))
      (neu : List (Ereignis D))
      (hneu : s0.spur = neu ++ ((normal ww M).faeden f).spur) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
              ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .dann rest k⟩⟩ ::
              ((normal ww M).faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, .ende (P.rumpf g)⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
              ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .dann rest k⟩⟩ ::
              ((normal ww M).faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, .ende (P.rumpf g)⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs0
  refine ⟨_, RufSchrittG.dannCallInd M f l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead ?_ ((M.weltVon f).lese Λ (p.orte ++ args.orte)) (rfl) g hg ?_ rho ?_ neu ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_rufCallInd {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (n : Nat) (p : Expr D Γ Λ (.fnptr n))
      (args : Args D Γ Λ (D.sigNr n).params)
      (hp : RufPasst D (vertragVon D ((normal ww M).faeden f).kopf.f) (D.sigNr n) Λ)
      (hr : (D.sigNr n).gruende = 0)
      (rest : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ
        (nachSig D (D.sigNr n) Λ))
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ende (.cons (.callInd p args hp hr) rest)⟩)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur))
      (s0 : World D)
      (hs0 : s0 = ((normal ww M).weltVon f).lese Λ (p.orte ++ args.orte))
      (g : D.Fn) (hg : D.passt g n = true)
      (hv : eval s0 p s0 ρ = ⟨g, hg⟩)
      (rho : Env D (D.params g))
      (hrho : rho = umsig hg (evalArgs s0 args s0 ρ))
      (neu : List (Ereignis D))
      (hneu : s0.spur = neu ++ ((normal ww M).faeden f).spur) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
              ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .ende rest⟩⟩ ::
              ((normal ww M).faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, .ende (P.rumpf g)⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
              ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .ende rest⟩⟩ ::
              ((normal ww M).faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, .ende (P.rumpf g)⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs0
  refine ⟨_, RufSchrittG.rufCallInd M f l Γ Λ n p args hp hr rest ρ hhead ?_ ((M.weltVon f).lese Λ (p.orte ++ args.orte)) (rfl) g hg ?_ rho ?_ neu ?_, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

end Gabbro.Stage0
