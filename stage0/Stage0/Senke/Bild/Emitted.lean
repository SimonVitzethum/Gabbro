/-
  File:      stage0/Stage0/Senke/Bild/Emitted.lean
  Subject:   The start of the emitted image (image theorem, piece T2, one thread).
             * `BildLage.funSpec`: every function of a laid-out image keeps its call protocol at every depth (the
               `FunSpec` that `bild_ok` builds through `start_ok`, named).
             * `Emitted.sp0`, `Emitted.einheit`: the memory the image starts with (that of the canonical initial
               world) and the judged unit of an image whose only start is `main` (`Emitted.goal_checker_main`).
             * `Emitted.rahmen`: the frame of `main`'s body in the image; `zerlegung_rahmen`: a decomposed prefix
               depends on such a frame only through its oracle, pass budget, depth, program and function.
             * `Emitted.bild_anfang` (T2): for a unit without declared and run-time roots, from the loaded payload the
               image runs to the start of the code of `main`'s body, where `RandIR` of the whole body holds at the
               canonical initial world and `main`'s environment `output.args`, in a frame `Emitted.rahmen` that
               satisfies `BodyFrame.Ok`. The machine-G side of the start is `randG_start` (`Bild/StartG.lean`).
-/
module
public import Stage0.CompilerPruefer
public import Stage0.Senke.Bild.Anfang
public import Stage0.Senke.Bild.StartG
public import Stage0.Senke.Bild.Ziel
@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Stage0.Senke
  Gabbro.Stage0.Senke.BildLauf Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

/-! ## The call protocol of a laid-out image -/

/-- **`FunSpec` of a laid-out image**: every function keeps its call protocol at every depth `k`, as `rufAt k`. -/
theorem Senke.BildLage.funSpec [Kern] {D : Deklaration} {P : Programm D} {O : Orakel D} {Yb : Lay D}
    [TorOK Yb O] [SichtOK O] {passes : Nat} {fs : List D.Fn} {pos : D.Fn → Nat} {main : D.Fn}
    {roots : List D.Fn} {K Ks : Nat} {A : D.Fn → Nat} {cs : List (List II × Nat)} {body : List II}
    {n fp0 : Nat} {sp : List (Nat × Nat)} {ρ : Env D (D.params main)} {rootArgs : List (List Runner.W)}
    {tail : List Runner.B} (h : BildLage passes P fs pos main roots K Ks Yb A cs body n fp0 sp ρ rootArgs)
    {m : Runner.Mem}
    (hm : BytesAt m codeBase ((spawnC (startScratch main) sp ++ startC A main n 231 true ++ rootsC A n roots ++
      body).flatMap encII ++ ((startStackBytes Ks (FB + FB) (encodeEnv Yb ρ :: rootArgs)).getD [] ++ tail)))
    (k : Nat) (hk : k < 2 ^ 64) :
    FunSpec Yb A (fun g => ((cs[pos g]?).map (·.1)).getD []) (rufAt P O passes k) (BitVec.ofNat 64 k)
      ((k + 1) * maxTop cs) := by
  obtain ⟨c1, c2, _, _, _⟩ := h.code hm
  have hfit := h.hfit
  exact lowFun_spec h.hfa c1 (fun g => by have := (c2 g).2; dsimp only at this ⊢; omega)
    (fun g => by have := (c2 g).2; dsimp only at this ⊢; omega) k hk

variable {src : String} {K : Nat} {options : Profil.Options}

/-! ## The frame and the unit of the image -/

/-- The memory the image starts with: that of the canonical initial world (the judged unit's `sp0`). -/
abbrev Emitted.sp0 (output : Emitted src K options) : Speicher (declOf output.compiled.unit) :=
  (Senke.initialWorld output.compiled.unit output.initialValid).speicher

/-- The judged unit of an image whose only start is `main` (`Emitted.goal_checker_main`), over the image's memory. -/
abbrev Emitted.einheit (output : Emitted src K options) (Q : AxEns (declOf output.compiled.unit)) :
    Einheit (declOf output.compiled.unit) :=
  OldSource.einheitDer output.compiled.unit output.compiled.program Q output.sp0 output.compiled.main
    output.args [] [] []

/-- **The frame of `main`'s body in the image**: at depth `depth` (callees `rufAt (depth - 1)`), `main`'s frame at
    slot `FB` of the first stack, the caller frame `fp0`, the entry world the requires read leaves. The codes `C`, the
    call capacity `Lm`, the return pc `rp` and the ensures code `ens` are the image's (`Emitted.bild_anfang`). -/
abbrev Emitted.rahmen (output : Emitted src K options) (O : Orakel (declOf output.compiled.unit))
    (C : (declOf output.compiled.unit).Fn → List II) (Lm : Nat) (rp : Runner.W) (ens : List II × Nat) :
    BodyFrame (declOf output.compiled.unit) :=
  rumpfRahmen output.image.Y O output.image.passes output.compiled.program output.image.A C Lm
    (output.image.depth - 1) output.compiled.main (slot (BitVec.ofNat 64 output.image.fp0) (BitVec.ofNat 64 FB))
    (output.image.Ks - FB) (output.image.Ks - FB) rp (BitVec.ofNat 64 output.image.fp0)
    ((Senke.initialWorld output.compiled.unit output.initialValid).lese
      (Signatur.anfang (declOf output.compiled.unit) ((declOf output.compiled.unit).signatur output.compiled.main))
      (output.compiled.program.requires output.compiled.main).orte) output.args [] ens

/-- The frame in which the decomposed prefix is stated: `Zerlegung` reads only the oracle, the pass budget, the call
    handler and the function of a frame (`zerlegung_rahmen`), which this frame shares with every `Emitted.rahmen`. -/
abbrev Emitted.zRahmen (output : Emitted src K options) (O : Orakel (declOf output.compiled.unit)) :
    BodyFrame (declOf output.compiled.unit) :=
  output.rahmen O (fun _ => []) 0 0 ([], 0)

/-- `Zerlegung` depends on a `rumpfRahmen` only through its oracle, pass budget, depth, program and function. -/
theorem zerlegung_rahmen {D : Deklaration} {Y Y' : Lay D} {O : Orakel D} {passes : Nat} {P : Programm D}
    {A A' : D.Fn → Nat} {C C' : D.Fn → List II} {Lm Lm' k : Nat} {f : D.Fn} {fp fp' : Runner.W}
    {K1 K1' Ks Ks' : Nat} {rp rp' cfp cfp' : Runner.W} {σ0 σ0' : World D} {ρ0 ρ0' : Env D (D.params f)}
    {H H' : List D.Lock} {ens ens' : List II × Nat} {Agl : D.Lock → Prop} {Cg : D.Fn → Prop} {l : Bool}
    {Γ Γe : Ctx} {Λ Λe : List (Res D)} {eb : Endblock D (vertragVon D f) l Γ Λ}
    {ebe : Endblock D (vertragVon D f) l Γe Λe} {σ σe : World D} {ρ : Env D Γ} {ρe : Env D Γe}
    :
    Zerlegung (rumpfRahmen Y O passes P A C Lm k f fp K1 Ks rp cfp σ0 ρ0 H ens) Agl Cg eb σ ρ ebe σe ρe →
    Zerlegung (rumpfRahmen Y' O passes P A' C' Lm' k f fp' K1' Ks' rp' cfp' σ0' ρ0' H' ens') Agl Cg
      eb σ ρ ebe σe ρe
  | .halt eb σ ρ => Zerlegung.halt (B := (rumpfRahmen Y' O passes P A' C' Lm' k f fp' K1' Ks' rp' cfp' σ0' ρ0' H' ens')) eb σ ρ
  | .schritt s rest ebe σ σ1 σe ρ ρ1 ρe hs hex hk =>
      Zerlegung.schritt (B := (rumpfRahmen Y' O passes P A' C' Lm' k f fp' K1' Ks' rp' cfp' σ0' ρ0' H' ens')) s rest ebe σ σ1 σe ρ ρ1 ρe hs hex (zerlegung_rahmen hk)
  | .bind e rest ebe σ σe ρ ρe hk =>
      Zerlegung.bind (B := (rumpfRahmen Y' O passes P A' C' Lm' k f fp' K1' Ks' rp' cfp' σ0' ρ0' H' ens'))
        e rest ebe σ σe ρ ρe (zerlegung_rahmen hk)

/-! ## T2 on the emitted image -/

theorem Emitted.funktionen_voll (output : Emitted src K options) (g : (declOf output.compiled.unit).Fn) :
    (List.finRange output.compiled.unit.fns.length)[g.val]? = some g := by
  simp only [List.finRange, List.getElem?_ofFn, g.isLt, ↓reduceDIte]
  congr 1

/-- **T2, the start of the emitted image**: for a unit without declared and run-time roots, from the loaded payload
    the image runs to the start of the code of `main`'s body, where `RandIR` of the whole body holds at the canonical
    initial world and `output.args`, in a frame `Emitted.rahmen` that satisfies `BodyFrame.Ok`. -/
theorem Emitted.bild_anfang [Kern] (output : Emitted src K options) (hr : output.compiled.unit.roots = [])
    (hg : output.compiled.unit.gestartet = []) (O : Orakel (declOf output.compiled.unit))
    [TorOK output.image.Y O] [SichtOK O] {m : Runner.Mem}
    (loaded : BytesAt m Runner.Prog.IMG output.bytes)
    (hreq : ReqAmEintritt output.compiled.program output.compiled.main
      (Senke.initialWorld output.compiled.unit output.initialValid) output.args) :
    ∃ (C : (declOf output.compiled.unit).Fn → List II) (Lm : Nat) (ens : List II × Nat) (rp pc : Runner.W)
      (mR : Runner.Mem),
      Star ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 output.image.fp0⟩ m
        ⟨pc, slot (BitVec.ofNat 64 output.image.fp0) (BitVec.ofNat 64 FB)⟩ mR ∧
      (output.rahmen O C Lm rp ens).Ok ∧
      (output.rahmen O C Lm rp ens).RandIR (output.compiled.program.rumpf output.compiled.main) pc mR
        (Senke.initialWorld output.compiled.unit output.initialValid) output.args := by
  have hst : output.starts = [] := output.starts_leer hr hg
  have hb := output.emission
  rw [show output.startPlan.starts (Senke.initialWorld output.compiled.unit output.initialValid) = [] from hst]
    at hb
  obtain ⟨world, _, sync, _, made, _, _, startup, _⟩ :=
    bild_initialized_loaded_u output.initialValid hb output.funktionen_voll loaded
  obtain ⟨cs, body, sp, h, code, _, args, rootArgs⟩ := bild_lage hb output.funktionen_voll
    (fun base bound => layU_in output.compiled.unit output.tor base bound)
    (fun base => layU_dis output.compiled.unit output.tor base)
    (fun base => by simp only [layU]; omega) (fun base => layU_sync output.compiled.unit output.tor base)
  have startup' : BytesAt m codeBase (output.image.code.flatMap encII ++
      ((startStackBytes output.image.Ks (FB + FB) (output.image.args :: output.image.rootArgs)).getD [] ++ [])) := by
    simpa only [made, Option.getD_some, List.append_nil] using startup
  rw [code, args, rootArgs] at startup'
  obtain ⟨ens, rp, pc, mR, run, ok, rand⟩ := BildLauf.bild_anfang (O := O) h startup'
    (fun τ x => Senke.mainEnv_valid output.image.Y _ output.args output.pointers τ x) world
    (by simpa only [Nat.mul_zero, Nat.add_zero] using sync 0 (Nat.zero_le _)) hreq
  exact ⟨_, _, ens, rp, pc, mR, run, ok, rand⟩

end Gabbro.Stage0
