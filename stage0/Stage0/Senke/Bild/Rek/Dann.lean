/-
  File:      stage0/Stage0/Senke/Bild/Rek/Dann.lean
  Subject:   **Calls in block position, machine G: the descent** (package P5 of the closed calls of the image theorem,
             part 6). The decomposed prefix of the image theorem steps over whole statements of an end block; a call
             INSIDE a block (a branch of `if`, a loop body, the success block of `let … else`) runs on machine G at a
             residue `.dann b k`: `rufDann` for a plain call, `dannBindCall` for `let x = g(…)`, `dannBindCallElse`
             for `let x = g(…) else { … }`. `RandDannGL` is the block-position boundary up to read events (the
             analogue of `RandGL` for `.ende eb`). The descent lemmas take the push step from it to the callee's
             first body boundary, EXACT at the machine's world (`RandG` with the entry world as the current world: the
             form the callee obligation `RufOk` starts from), with the caller frame waiting as the step leaves it
             (`.dann rest k`, `.wartet rest k`, `.wartetSonst n err rest k`); `randGL_von_eintritt` turns it into the
             boundary up to read events against the image handler's body world `rufWelt`.
-/
module
public import Stage0.Senke.Bild.Rek.RueckArt
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-! ## The block-position boundary -/

/-- **Machine G at a block-position boundary, up to read events**: thread `thr` runs the frame of `f` with the residue
    `.dann b k` at a world `σm ≈ σ`, with the environment `ρ`, holding the locks of `Λ` above the floor of `f`, and no
    other thread holds a lock of `Agl`. -/
def RandDannGL (thr : Faden) (stapel : List (RufRahmenG D)) (f : D.Fn) (rho : Env D (D.params f)) (s0 : World D)
    (Agl : D.Lock → Prop) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D (vertragVon D f) l Γ Λ Λ')
    (k : GRest D (vertragVon D f) l Γ Λ') (M : RufMaschineG D) (σ : World D) (ρ : Env D Γ) : Prop :=
  ∃ σm : World D, WeltGleich σ σm ∧ (∃ log, ZustandG M thr stapel f rho s0 log ρ (.dann b k) σm) ∧
    HeldB (vertragVon D f).boden Λ (offen σm.spur) ∧ FreiA Agl M thr

/-! ## The common half of every descent -/

/-- **The callee's exact entry is its first boundary up to read events** against the image handler's body world. -/
theorem randGL_von_eintritt {thr : Faden} {stapel' : List (RufRahmenG D)} {Agl : D.Lock → Prop} {Γ : Ctx}
    {Λ : List (Res D)} {P : Programm D} {g : D.Fn} {args : Args D Γ Λ (D.params g)} {M1 : RufMaschineG D}
    {σ σm : World D} {ρ : Env D Γ} (hw1 : WeltGleich (σ.lese Λ args.orte) σm)
    (hE : RandG thr stapel' g (rufEnv g σ Λ args ρ) σm Agl (P.rumpf g) M1 σm (rufEnv g σ Λ args ρ)) :
    RandGL thr stapel' g (rufEnv g σ Λ args ρ) σm Agl (P.rumpf g) M1 (rufWelt P g σ Λ args)
      (rufEnv g σ Λ args ρ) :=
  ⟨σm, (rufWelt_gleich P g σ Λ args).trans hw1, hE⟩

/-- **A push is the callee's exact entry**: after one step of `thr` that pushes a caller frame (any waiting form, the
    stack `stapel'`) and starts the callee `g` at the read world `σm0.lese Λ args.orte` with the argument values there,
    machine G stands at the callee's first body boundary at that world, with the callee's parameters `rufEnv` of the
    sequential world `σ ≈ σm0`. -/
theorem randG_eintritt_von {P : Programm D} {O : Orakel D} {passes : Nat} {thr : Faden}
    {stapel' : List (RufRahmenG D)} {f : D.Fn} {Agl : D.Lock → Prop} {Γ : Ctx} {Λ : List (Res D)} {g : D.Fn}
    {args : Args D Γ Λ (D.params g)} (hp : RufPasst D (vertragVon D f) (D.signatur g) Λ)
    {M M1 : RufMaschineG D} {σ σm0 : World D} {ρ : Env D Γ} {log : List (RufEreignisF D)}
    (hw : WeltGleich σ σm0) (hΛ : HeldB (vertragVon D f).boden Λ (offen σm0.spur)) (hA : FreiA Agl M thr)
    (hs : RufSchrittG P O passes M thr M1)
    (hZ1 : ZustandG M1 thr stapel' g (evalArgs (σm0.lese Λ args.orte) args (σm0.lese Λ args.orte) ρ)
      (σm0.lese Λ args.orte) log (evalArgs (σm0.lese Λ args.orte) args (σm0.lese Λ args.orte) ρ)
      (.ende (P.rumpf g)) (σm0.lese Λ args.orte)) :
    RufLaufG P O passes thr M M1 ∧ WeltGleich (σ.lese Λ args.orte) (σm0.lese Λ args.orte) ∧
      RandG thr stapel' g (rufEnv g σ Λ args ρ) (σm0.lese Λ args.orte) Agl (P.rumpf g) M1
        (σm0.lese Λ args.orte) (rufEnv g σ Λ args ρ) := by
  have hw1 : WeltGleich (σ.lese Λ args.orte) (σm0.lese Λ args.orte) := hw.lese Λ args.orte
  have hargs : evalArgs (σm0.lese Λ args.orte) args (σm0.lese Λ args.orte) ρ = rufEnv g σ Λ args ρ :=
    (hw1.werte args ρ).symm
  rw [hargs] at hZ1
  have hl : RufLaufG P O passes thr M M1 := RufLaufG.einzeln hs
  exact ⟨hl, hw1, ⟨_, hZ1⟩, heldB_eintritt hp hΛ args.orte Λ, hA.lauf hl⟩

/-! ## The descents -/

/-- **Into the callee of a plain call in a block** (`rufDann`): the caller waits at `.dann rest k`. -/
theorem randDannGL_ruf_eintritt {P : Programm D} {O : Orakel D} {passes : Nat} {thr : Faden}
    {stapel : List (RufRahmenG D)} {f : D.Fn} {rho : Env D (D.params f)} {s0 : World D} {Agl : D.Lock → Prop}
    {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)} {g : D.Fn} {args : Args D Γ Λ (D.params g)}
    {hp : RufPasst D (vertragVon D f) (D.signatur g) Λ} {hr : D.gruende g = 0}
    {rest : Block D (vertragVon D f) l Γ (nach D g Λ) Λ''} {k : GRest D (vertragVon D f) l Γ Λ''}
    {M : RufMaschineG D} {σ : World D} {ρ : Env D Γ}
    (h : RandDannGL thr stapel f rho s0 Agl (.cons (.call g args hp hr) rest) k M σ ρ) :
    ∃ (M1 : RufMaschineG D) (σm : World D), RufLaufG P O passes thr M M1 ∧ WeltGleich (σ.lese Λ args.orte) σm ∧
      RandG thr (⟨f, rho, s0, ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩ :: stapel) g (rufEnv g σ Λ args ρ) σm Agl
        (P.rumpf g) M1 σm (rufEnv g σ Λ args ρ) := by
  obtain ⟨σm0, hw, ⟨log, hZ⟩, hΛ, hA⟩ := h
  have hW := hZ.welt
  obtain ⟨M1, hs1, hZ1⟩ := w_rufDann (P := P) (O := O) (passes := passes) hZ.1 g args hp hr rest k ρ rfl
    hΛ.heldIn
  rw [hW] at hZ1
  exact ⟨M1, σm0.lese Λ args.orte, randG_eintritt_von hp hw hΛ hA hs1 hZ1⟩

/-- **Into the callee of `let x = g(…)` in a block** (`dannBindCall`): the caller waits at `.wartet rest k`. -/
theorem randDannGL_bindCall_eintritt {P : Programm D} {O : Orakel D} {passes : Nat} {thr : Faden}
    {stapel : List (RufRahmenG D)} {f : D.Fn} {rho : Env D (D.params f)} {s0 : World D} {Agl : D.Lock → Prop}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} {g : D.Fn} {args : Args D Γ Λ (D.params g)}
    {he : D.erg g = some τ} {hp : RufPasst D (vertragVon D f) (D.signatur g) Λ} {hr : D.gruende g = 0}
    {rest : Block D (vertragVon D f) l (τ :: Γ) (nach D g Λ) Λ'} {k : GRest D (vertragVon D f) l Γ Λ'}
    {M : RufMaschineG D} {σ : World D} {ρ : Env D Γ}
    (h : RandDannGL thr stapel f rho s0 Agl (.bindCall g args he hp hr rest) k M σ ρ) :
    ∃ (M1 : RufMaschineG D) (σm : World D), RufLaufG P O passes thr M M1 ∧ WeltGleich (σ.lese Λ args.orte) σm ∧
      RandG thr (⟨f, rho, s0, ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩ :: stapel) g (rufEnv g σ Λ args ρ) σm Agl
        (P.rumpf g) M1 σm (rufEnv g σ Λ args ρ) := by
  obtain ⟨σm0, hw, ⟨log, hZ⟩, hΛ, hA⟩ := h
  have hW := hZ.welt
  obtain ⟨M1, hs1, hZ1⟩ := w_bindCall (P := P) (O := O) (passes := passes) hZ.1 g args he hp hr rest k ρ rfl
    hΛ.heldIn
  rw [hW] at hZ1
  exact ⟨M1, σm0.lese Λ args.orte, randG_eintritt_von hp hw hΛ hA hs1 hZ1⟩

/-- **Into the callee of `let x = g(…) else { … }` in a block** (`dannBindCallElse`): the caller waits at
    `.wartetSonst n err rest k`, keeping its else block for the reason exit. -/
theorem randDannGL_bindCallElse_eintritt {P : Programm D} {O : Orakel D} {passes : Nat} {thr : Faden}
    {stapel : List (RufRahmenG D)} {f : D.Fn} {rho : Env D (D.params f)} {s0 : World D} {Agl : D.Lock → Prop}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} {g : D.Fn} {args : Args D Γ Λ (D.params g)}
    {he : D.erg g = some τ} {hp : RufPasst D (vertragVon D f) (D.signatur g) Λ} {hr : 0 < D.gruende g}
    {err : Endblock D (vertragVon D f) l (.why (D.gruende g) :: Γ) (nach D g Λ)}
    {rest : Block D (vertragVon D f) l (τ :: Γ) (nach D g Λ) Λ'} {k : GRest D (vertragVon D f) l Γ Λ'}
    {M : RufMaschineG D} {σ : World D} {ρ : Env D Γ}
    (h : RandDannGL thr stapel f rho s0 Agl (.bindCallElse g args he hp hr err rest) k M σ ρ) :
    ∃ (M1 : RufMaschineG D) (σm : World D), RufLaufG P O passes thr M M1 ∧ WeltGleich (σ.lese Λ args.orte) σm ∧
      RandG thr (⟨f, rho, s0, ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩ :: stapel) g
        (rufEnv g σ Λ args ρ) σm Agl (P.rumpf g) M1 σm (rufEnv g σ Λ args ρ) := by
  obtain ⟨σm0, hw, ⟨log, hZ⟩, hΛ, hA⟩ := h
  have hW := hZ.welt
  obtain ⟨M1, hs1, hZ1⟩ := w_bindCallElse (P := P) (O := O) (passes := passes) hZ.1 g args he hp hr err rest k ρ
    rfl hΛ.heldIn
  rw [hW] at hZ1
  exact ⟨M1, σm0.lese Λ args.orte, randG_eintritt_von hp hw hΛ hA hs1 hZ1⟩

#print axioms randDannGL_bindCallElse_eintritt

end Gabbro.Stage0.Senke.BildLauf
