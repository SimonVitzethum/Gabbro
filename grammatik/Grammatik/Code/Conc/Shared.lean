import Grammatik.Code.Conc.Await
import Grammatik.Code.Conc.Present

/-
  File:      Grammatik/Code/Conc/Shared.lean
  Subject:   TRACK L, PHASE L3 -- THE INTERFACE OF THE SHARED ATOMICS (`Sees.shared`) and the weak `await`
             refined against it: a load of a shared atomic returns ANY value of the cell's type.

  Machine GX lets the presented memory differ from the machine's at the shared atomics `Tg` in an arbitrary way (it
  over-approximates the weak memory W). Its IR counterpart is the interface `Sees.shared lay`: an atomic load of the
  cell of a shared global answers any value of the cell's type; every other cell answers what the memory holds. The SC
  interface is inside it (`sees_sc_shared`), and so is any interface of the weak model that answers the memory's
  value outside the shared cells; `step_mono`/`reach_mono` (`Model/Weak.lean`) carry a refinement against `Sees.shared`
  down to those.

  `await_ok_shared`: for a SHARED global the lowered `await` refines G's `await` on the presented world `σ[g := xg]`
  for EVERY `xg` and with the memory representing the ACTUAL world `σ` -- the `Rep` of `Lower/Rep.lean` leaves the
  cell free, so no `RepX` of a second kind is needed.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag Orakel Ausgang EndAusgang RufAusgang
  ErgVal ErgExpr execStmt execBlock execEnd eval evalErg Zahl gdarf)

variable {D : Deklaration} {V : Vertrag D}

/-- **The interface of machine GX.** A load of the cell of a shared global answers any value of the cell's type; any
    other load answers what the memory holds. -/
def Sees.shared (lay : Layout D) : Sees := fun m b o t _ x =>
  (∃ g, lay.shared g = true ∧ b = lay.ggblk g ∧ o = 0 ∧ t = memTy (D.gtyp g) ∧ x.ty = t) ∨ m.load b o t = some x

/-- The SC interface is inside the GX interface. -/
theorem sees_sc_shared (lay : Layout D) :
    ∀ m b o t ord x, Sees.sc m b o t ord x → Sees.shared lay m b o t ord x :=
  fun _ _ _ _ _ _ h => Or.inr h

/-- A shared global's cell answers the image of any value. -/
theorem sees_shared_at (lay : Layout D) (m : Mem) (g : D.Glob) (hg : lay.shared g = true) (ord : Order)
    (xg : Wert D (D.gtyp g)) (hs : supp (D.gtyp g) = true) :
    Sees.shared lay m (lay.ggblk g) 0 (memTy (D.gtyp g)) ord (encM lay (D.gtyp g) xg) :=
  Or.inl ⟨g, hg, rfl, rfl, rfl, encM_ty lay xg hs⟩

/-- Presenting any value at a shared global keeps the memory's representation: the cell is free. -/
theorem rep_storeGlob_shared {lay : Layout D} {σ : World D} {m : Mem} (g : D.Glob) (hg : lay.shared g = true)
    (xg : Wert D (D.gtyp g)) (hR : Rep lay σ m) : Rep lay (σ.storeGlob g xg) m := by
  refine rep_agree (σ := σ) (σ' := σ.storeGlob g xg) (fun t k f => rfl) (fun g' hg' => ?_) hR
  have hne : g' ≠ g := fun e => by rw [e, hg] at hg'; exact Bool.noConfusion hg'
  simp [World.storeGlob, hne]

/-- **`await` of a shared atomic refines G's `await` on every presented world.** The memory represents the actual
    world `σ`; the thread reads the world `σ[g := xg]` for any `xg`, which the GX interface answers. -/
theorem await_ok_shared (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D)
    (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (g : D.Glob) (payload : List D.Glob)
    (hp : payload = D.nutzlast g) (hgd : gdarf D g Λ)
    (rest : Gabbro.Grammatik.Block D V l (D.gtyp g :: Γ) Λ Λ')
    (IH : ∀ a, BOk lay (a :: cenv) lv O passes R rest)
    (lb k : Lbl) (st st' : St) (blks : List Block)
    (h : lowerAwait lay cenv lv g rest lb k st = some (blks, st'))
    (hg : lay.shared g = true)
    (M : Modl) (fn : Nat) (hM : InM M fn blks) (hk : KOk M fn k) (hlv : LvOk M fn lv)
    (hFn : FnOk lay M) (hCall : CallRef lay M (Sees.shared lay) R)
    (σ : World D) (xg : Wert D (D.gtyp g)) (ρ : Env D Γ) (m : Mem) (rs : Regs) (ks : List Frame)
    (dst : Option Reg) (hR : Rep lay σ m) (hE : EnvRep lay rs m cenv ρ) (hW : WfL lay m)
    (hc : ∀ x ∈ cenv, x < st.r) :
    PresentedAt g σ (σ.storeGlob g xg) ∧
    OutOk lay cenv lv M (Sees.shared lay) fn lb k st.r st'.r m rs ks dst
      (execBlock O passes R (Gabbro.Grammatik.Block.awaits g payload hp hgd rest) (σ.storeGlob g xg) ρ) :=
  await_ok_gx lay hL cenv lv O passes R g payload hp hgd rest IH lb k st st' blks h M (Sees.shared lay) fn hM hk hlv
    hFn hCall σ xg ρ m rs ks dst (rep_storeGlob_shared g hg xg hR) hE hW hc
    (sees_shared_at lay m g hg .acq xg (atomicG_supp (lowerAwait_atomic h)))

end Gabbro.Code.Lower
