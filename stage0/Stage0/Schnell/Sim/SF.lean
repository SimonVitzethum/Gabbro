/-
  File:      stage0/Stage0/Schnell/Sim/SF.lean
  Subject:   The simulation of the normal form, rules 51 .. 60 of `RufSchrittG` (`Schnell/Sim.lean`): a step of
             `normal ww M` under the fast oracle is a step of `M` under the machine's oracle, to the same normal form.
-/
import Stage0.Schnell.Werkzeug

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration} {P : Programm D} {OF OM : Orakel D} {passes : Nat} {ww : World D}

theorem sim_peelDannLeave {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D)) {Λ1 Λ2 : List (Res D)}
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ Λ1)
      (b : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ1 Λ2)
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ2)
      (ρ : Env D Γ)
      (hleave : true = true)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨true, Γ, Λ, ρ,
         .dann (.cons ((.leave hleave) : Stmt D (vertragVon D ((normal ww M).faeden f).kopf.f)
            true Γ Λ Λ) rest) (.dann b k)⟩) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨true, Γ, Λ2, ρ,
              .dann (.cons ((.leave hleave) : Stmt D
                (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ2 Λ2) .nil) k⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨true, Γ, Λ2, ρ,
              .dann (.cons ((.leave hleave) : Stmt D
                (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ2 Λ2) .nil) k⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  refine ⟨_, RufSchrittG.peelDannLeave M f l Γ Λ rest b k ρ hleave hhead, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_peelDannNext {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D)) {Λ1 Λ2 : List (Res D)}
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ Λ1)
      (b : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ1 Λ2)
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ2)
      (ρ : Env D Γ)
      (hnext : true = true)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨true, Γ, Λ, ρ,
         .dann (.cons ((.next hnext) : Stmt D (vertragVon D ((normal ww M).faeden f).kopf.f)
            true Γ Λ Λ) rest) (.dann b k)⟩) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨true, Γ, Λ2, ρ,
              .dann (.cons ((.next hnext) : Stmt D
                (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ2 Λ2) .nil) k⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨true, Γ, Λ2, ρ,
              .dann (.cons ((.next hnext) : Stmt D
                (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ2 Λ2) .nil) k⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  refine ⟨_, RufSchrittG.peelDannNext M f l Γ Λ rest b k ρ hnext hhead, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_peelSchrumpfLeave {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (τ : Ty) {Λ1 : List (Res D)}
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true (τ :: Γ) Λ Λ1)
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ1)
      (ρ : Env D (τ :: Γ))
      (hleave : true = true)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨true, τ :: Γ, Λ, ρ,
         .dann (.cons ((.leave hleave) : Stmt D (vertragVon D ((normal ww M).faeden f).kopf.f)
            true (τ :: Γ) Λ Λ) rest) (.schrumpf k)⟩) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨true, Γ, Λ1, ρ.tail,
              .dann (.cons ((.leave hleave) : Stmt D
                (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ1 Λ1) .nil) k⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨true, Γ, Λ1, ρ.tail,
              .dann (.cons ((.leave hleave) : Stmt D
                (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ1 Λ1) .nil) k⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  refine ⟨_, RufSchrittG.peelSchrumpfLeave M f l Γ Λ τ rest k ρ hleave hhead, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_peelSchrumpfNext {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (τ : Ty) {Λ1 : List (Res D)}
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true (τ :: Γ) Λ Λ1)
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ1)
      (ρ : Env D (τ :: Γ))
      (hnext : true = true)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨true, τ :: Γ, Λ, ρ,
         .dann (.cons ((.next hnext) : Stmt D (vertragVon D ((normal ww M).faeden f).kopf.f)
            true (τ :: Γ) Λ Λ) rest) (.schrumpf k)⟩) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨true, Γ, Λ1, ρ.tail,
              .dann (.cons ((.next hnext) : Stmt D
                (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ1 Λ1) .nil) k⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨true, Γ, Λ1, ρ.tail,
              .dann (.cons ((.next hnext) : Stmt D
                (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ1 Λ1) .nil) k⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  refine ⟨_, RufSchrittG.peelSchrumpfNext M f l Γ Λ τ rest k ρ hnext hhead, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_peelFreiLeave {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (L : D.Lock) {Λ1 : List (Res D)}
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ (Res.held L :: Λ1))
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ1)
      (ρ : Env D Γ)
      (hleave : true = true)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨true, Γ, Λ, ρ,
         .dann (.cons ((.leave hleave) : Stmt D (vertragVon D ((normal ww M).faeden f).kopf.f)
            true Γ Λ Λ) rest) (.frei L k)⟩) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨true, Γ, Λ1, ρ,
              .dann (.cons ((.leave hleave) : Stmt D
                (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ1 Λ1) .nil) k⟩⟩,
            Ereignis.gibt L :: ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f [Ereignis.gibt L], (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨true, Γ, Λ1, ρ,
              .dann (.cons ((.leave hleave) : Stmt D
                (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ1 Λ1) .nil) k⟩⟩,
            Ereignis.gibt L :: ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f [Ereignis.gibt L], (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  refine ⟨_, RufSchrittG.peelFreiLeave M f l Γ Λ L rest k ρ hleave hhead, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_peelFreiNext {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (L : D.Lock) {Λ1 : List (Res D)}
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ (Res.held L :: Λ1))
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ1)
      (ρ : Env D Γ)
      (hnext : true = true)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨true, Γ, Λ, ρ,
         .dann (.cons ((.next hnext) : Stmt D (vertragVon D ((normal ww M).faeden f).kopf.f)
            true Γ Λ Λ) rest) (.frei L k)⟩) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨true, Γ, Λ1, ρ,
              .dann (.cons ((.next hnext) : Stmt D
                (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ1 Λ1) .nil) k⟩⟩,
            Ereignis.gibt L :: ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f [Ereignis.gibt L], (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨true, Γ, Λ1, ρ,
              .dann (.cons ((.next hnext) : Stmt D
                (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ1 Λ1) .nil) k⟩⟩,
            Ereignis.gibt L :: ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f [Ereignis.gibt L], (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  refine ⟨_, RufSchrittG.peelFreiNext M f l Γ Λ L rest k ρ hnext hhead, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_peelAbbruchLeave {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (Γ : Ctx) (Λ Λ1 Λk : List (Res D))
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ Λ1)
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λk)
      (ρ : Env D Γ)
      (hleave : true = true)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨true, Γ, Λ, ρ,
         .dann (.cons ((.leave hleave) : Stmt D (vertragVon D ((normal ww M).faeden f).kopf.f)
            true Γ Λ Λ) rest) (.abbruch k)⟩) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨true, Γ, Λk, ρ,
              .dann (.cons ((.leave hleave) : Stmt D
                (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λk Λk) .nil) k⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨true, Γ, Λk, ρ,
              .dann (.cons ((.leave hleave) : Stmt D
                (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λk Λk) .nil) k⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  refine ⟨_, RufSchrittG.peelAbbruchLeave M f Γ Λ Λ1 Λk rest k ρ hleave hhead, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_peelAbbruchNext {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (Γ : Ctx) (Λ Λ1 Λk : List (Res D))
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λ Λ1)
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λk)
      (ρ : Env D Γ)
      (hnext : true = true)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨true, Γ, Λ, ρ,
         .dann (.cons ((.next hnext) : Stmt D (vertragVon D ((normal ww M).faeden f).kopf.f)
            true Γ Λ Λ) rest) (.abbruch k)⟩) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨true, Γ, Λk, ρ,
              .dann (.cons ((.next hnext) : Stmt D
                (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λk Λk) .nil) k⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨(normal ww M).speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨((normal ww M).faeden f).stapel,
            ⟨((normal ww M).faeden f).kopf.f, ((normal ww M).faeden f).kopf.rho, ((normal ww M).faeden f).kopf.s0,
             ⟨true, Γ, Λk, ρ,
              .dann (.cons ((.next hnext) : Stmt D
                (vertragVon D ((normal ww M).faeden f).kopf.f) true Γ Λk Λk) .nil) k⟩⟩,
            ((normal ww M).faeden f).spur, ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf, (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  refine ⟨_, RufSchrittG.peelAbbruchNext M f Γ Λ Λ1 Λk rest k ρ hnext hhead, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_dannRet {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (l : Bool) (Γ : Ctx) (Λ Λ'' : List (Res D))
      (e : ErgExpr D Γ Λ (vertragVon D ((normal ww M).faeden f).kopf.f).erg)
      (hperm : Λ.Perm (vertragVon D ((normal ww M).faeden f).kopf.f).ende)
      (rest : Block D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ Λ'')
      (k : GRest D (vertragVon D ((normal ww M).faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : ((normal ww M).faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.ret e hperm) rest) k⟩)
      (caller : RufRahmenG D) (rst : List (RufRahmenG D))
      (hpop : ((normal ww M).faeden f).stapel = caller :: rst)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur))
      (s1 : World D)
      (hs1 : s1 = ((normal ww M).weltVon f).lese Λ e.orte)
      (g : D.Fn) (hfg : ((normal ww M).faeden f).kopf.f = g)
      (rho : Env D (D.params g)) (hrho : ((normal ww M).faeden f).kopf.rho = hfg ▸ rho)
      (s0 : World D) (hs0 : ((normal ww M).faeden f).kopf.s0 = s0)
      (v : ErgVal D (D.erg g))
      (hv : v = hfg ▸ evalErg s1 e s1 ρ)
      (neu : List (Ereignis D))
      (hneu : s1.spur = neu ++ ((normal ww M).faeden f).spur)
      (hnw : caller.wartend = false) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨s1.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨rst, caller, s1.spur,
            (RufEreignisF.rueck g rho v s0 s1) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨s1.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨rst, caller, s1.spur,
            (RufEreignisF.rueck g rho v s0 s1) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs1
  subst hs0
  obtain ⟨cM, rM, hM, hc, hr⟩ : ∃ cM rM, (M.faeden f).stapel = cM :: rM ∧ caller = cM.ohne ww ∧
      rst = rM.map (RufRahmenG.ohne ww) := by
    cases hs : (M.faeden f).stapel with
    | nil => simp [normal, fadenNormal, hs] at hpop
    | cons cM rM =>
      simp only [normal, fadenNormal, hs, List.map_cons, List.cons.injEq] at hpop
      exact ⟨cM, rM, rfl, hpop.1.symm, hpop.2.symm⟩
  subst hc hr
  subst hfg
  have hE : evalErg (((normal ww M).weltVon f).lese Λ e.orte) e (((normal ww M).weltVon f).lese Λ e.orte) ρ = evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ :=
    Paar.evalErg (sF := kompakt (M.faeden f).spur) (sM := (M.faeden f).spur) (by paar) (by paar) e ρ
  refine ⟨_, RufSchrittG.dannRet M f l Γ Λ Λ'' e hperm rest k ρ hhead cM rM hM ?_ ((M.weltVon f).lese Λ e.orte) (rfl) _ rfl rho hrho ((M.faeden f).kopf.s0) (rfl) v (hv.trans hE) neu ?_ hnw, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

theorem sim_rueckCons {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    (caller : RufRahmenG D) (rst : List (RufRahmenG D))
      (hpop : ((normal ww M).faeden f).stapel = caller :: rst) {lr : Bool}
      (Γ : Ctx) (Λ : List (Res D))
      (e : ErgExpr D Γ Λ (vertragVon D ((normal ww M).faeden f).kopf.f).erg)
      (hperm : Λ.Perm (vertragVon D ((normal ww M).faeden f).kopf.f).ende)
      (rest : Endblock D (vertragVon D ((normal ww M).faeden f).kopf.f) lr Γ Λ)
      (ρ : Env D Γ)
      (hkopf_ : ((normal ww M).faeden f).kopf.rest =
        ⟨lr, Γ, Λ, ρ, .ende (.cons (.ret e hperm) rest)⟩)
      (g : D.Fn) (hfg : ((normal ww M).faeden f).kopf.f = g)
      (rho : Env D (D.params g)) (hrho : ((normal ww M).faeden f).kopf.rho = hfg ▸ rho)
      (s0 : World D) (hs0 : ((normal ww M).faeden f).kopf.s0 = s0)
      (hΛ : HeldIn Λ (offen ((normal ww M).faeden f).spur))
      (s1 : World D)
      (hs1 : s1 = ((normal ww M).weltVon f).lese Λ e.orte)
      (v : ErgVal D (D.erg g))
      (hv : v = hfg ▸ evalErg s1 e s1 ρ)
      (neu : List (Ereignis D))
      (hneu : s1.spur = neu ++ ((normal ww M).faeden f).spur)
      (hnw : caller.wartend = false) :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww (⟨s1.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨rst, caller, s1.spur,
            (RufEreignisF.rueck g rho v s0 s1) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩ : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl (((⟨s1.speicher,
         rufUpdateG (normal ww M).faeden f
           ⟨rst, caller, s1.spur,
            (RufEreignisF.rueck g rho v s0 s1) :: ((normal ww M).faeden f).log⟩,
         (normal ww M).lauf ++ rufEigenG f neu,
         (normal ww M).start⟩ : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
  subst hs0
  subst hs1
  obtain ⟨cM, rM, hM, hc, hr⟩ : ∃ cM rM, (M.faeden f).stapel = cM :: rM ∧ caller = cM.ohne ww ∧
      rst = rM.map (RufRahmenG.ohne ww) := by
    cases hs : (M.faeden f).stapel with
    | nil => simp [normal, fadenNormal, hs] at hpop
    | cons cM rM =>
      simp only [normal, fadenNormal, hs, List.map_cons, List.cons.injEq] at hpop
      exact ⟨cM, rM, rfl, hpop.1.symm, hpop.2.symm⟩
  subst hc hr
  subst hfg
  have hE : evalErg (((normal ww M).weltVon f).lese Λ e.orte) e (((normal ww M).weltVon f).lese Λ e.orte) ρ = evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ :=
    Paar.evalErg (sF := kompakt (M.faeden f).spur) (sM := (M.faeden f).spur) (by paar) (by paar) e ρ
  refine ⟨_, RufSchrittG.rueckCons M f cM rM hM Γ Λ e hperm rest ρ hkopf_ _ rfl rho hrho ((M.faeden f).kopf.s0) (rfl) ?_ ((M.weltVon f).lese Λ e.orte) (rfl) v (hv.trans hE) neu ?_ hnw, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
  all_goals try sim_ziel

end Gabbro.Stage0
