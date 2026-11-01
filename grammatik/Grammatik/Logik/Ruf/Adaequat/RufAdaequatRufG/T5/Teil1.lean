/- Part 5 of 10 of `RufAdaequatRufG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatRufG.lean` imports all parts). -/
module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T4
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

section SimOk

variable (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (fn : D.Fn)
  (stapel : List (RufRahmenG D)) (rho : Env D (D.params fn)) (s0 : World D)
  (A : D.Lock → Prop) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  (C : D.Fn → Prop)

/-- Block simulation, normal completion: `dann b k` at `σ, ρ` runs (steps of
    `f` only) to `k` at the world and environment `execBlock` returns; the
    log grows by the events of the calls made on the way (`ext`). -/
def SimOkBR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D fn) l Γ Λ Λ') : Prop :=
  ∀ (log : List (RufEreignisF D)) (σ σ' : World D) (ρ ρ' : Env D Γ),
    execBlock O passes R b σ ρ = .ok σ' ρ' →
  ∀ (M : RufMaschineG D) (k : GRest D (vertragVon D fn) l Γ Λ'),
    ZustandG M f stapel fn rho s0 log ρ (.dann b k) σ → HeldB (vertragVon D fn).boden Λ (offen σ.spur) →
    FreiA A M f →
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' k σ' ∧ offen σ'.spur = offen σ.spur

/-- Statement simulation, normal completion: `dann (s; rest) k` runs to
    `dann rest k`. -/
def SimOkSR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D fn) l Γ Λ Λ') : Prop :=
  ∀ (log : List (RufEreignisF D)) (σ σ' : World D) (ρ ρ' : Env D Γ),
    execStmt O passes R s σ ρ = .ok σ' ρ' →
  ∀ (M : RufMaschineG D) {Λ'' : List (Res D)}
    (rest : Block D (vertragVon D fn) l Γ Λ' Λ'') (k : GRest D (vertragVon D fn) l Γ Λ''),
    ZustandG M f stapel fn rho s0 log ρ (.dann (.cons s rest) k) σ →
    HeldB (vertragVon D fn).boden Λ (offen σ.spur) → FreiA A M f →
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' (.dann rest k) σ' ∧
      offen σ'.spur = offen σ.spur

/-- Block simulation, abrupt exit: `dann b k` at `σ, ρ`, inside a loop
    (`hl`), runs to the exit statement of the kind `execBlock` exits with,
    standing directly above `k` (every scaffolding layer the block built on
    the way is peeled, a `frei` layer releasing its lock), at the world and
    environment of the exit. -/
def SimAbbBR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D fn) l Γ Λ Λ') : Prop :=
  ∀ (hl : l = true) (log : List (RufEreignisF D)) (σ σ' : World D) (ρ ρ' : Env D Γ) (w : Bool),
    (execBlock O passes R b σ ρ).abb? = some (w, σ', ρ') →
  ∀ (M : RufMaschineG D) (k : GRest D (vertragVon D fn) l Γ Λ'),
    ZustandG M f stapel fn rho s0 log ρ (.dann b k) σ → HeldB (vertragVon D fn).boden Λ (offen σ.spur) →
    FreiA A M f →
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)) (Λx : List (Res D))
      (r : Block D (vertragVon D fn) l Γ Λx Λ'), RufLaufG P O passes f M M' ∧
      ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' (.dann (.cons (abbS hl w) r) k) σ' ∧
      offen σ'.spur = offen σ.spur

/-- Statement simulation, abrupt exit: `dann (s; rest) k` runs to the exit
    statement directly above `k` (the `dann rest` layer is peeled too). -/
def SimAbbSR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D fn) l Γ Λ Λ') : Prop :=
  ∀ (hl : l = true) (log : List (RufEreignisF D)) (σ σ' : World D) (ρ ρ' : Env D Γ) (w : Bool),
    (execStmt O passes R s σ ρ).abb? = some (w, σ', ρ') →
  ∀ (M : RufMaschineG D) {Λ'' : List (Res D)}
    (rest : Block D (vertragVon D fn) l Γ Λ' Λ'') (k : GRest D (vertragVon D fn) l Γ Λ''),
    ZustandG M f stapel fn rho s0 log ρ (.dann (.cons s rest) k) σ →
    HeldB (vertragVon D fn).boden Λ (offen σ.spur) → FreiA A M f →
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)) (Λx : List (Res D))
      (r : Block D (vertragVon D fn) l Γ Λx Λ''), RufLaufG P O passes f M M' ∧
      ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' (.dann (.cons (abbS hl w) r) k) σ' ∧
      offen σ'.spur = offen σ.spur

/-- A covered leaf: one `dannBlatt` step. -/
theorem blattOkR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D (vertragVon D fn) l Γ Λ Λ'} (h : BlattG s) :
    SimOkSR P O passes f fn stapel rho s0 A R s := by
  intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ _
  have hW := hZ.welt
  have herw := h.erw O passes R σ σ' ρ ρ' hex
  obtain ⟨M', hs, hZ'⟩ := w_dannBlatt (P := P) (O := O) (passes := passes) hZ.1 s rest k ρ
    h.istBlatt rfl hΛ.heldIn σ' ρ' (by rw [hW, ← h.exec_R O passes R]; exact hex) (by rw [hW]; exact herw)
  exact ⟨M', [], RufLaufG.einzeln hs, hZ', herw.offen⟩

/-- A covered leaf never exits abruptly. -/
theorem blattAbbR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D (vertragVon D fn) l Γ Λ Λ'} (h : BlattG s) :
    SimAbbSR P O passes f fn stapel rho s0 A R s := by
  intro _ log σ σ' ρ ρ' w hex
  rw [abb_none_of (h.ohneAbbruch O passes R σ ρ)] at hex
  cases hex

/-- A `schrumpf` layer after a sub-block: one `schrumpfVergiss` step. -/
theorem schrumpfOkR {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    {M : RufMaschineG D} {log : List (RufEreignisF D)} {k : GRest D (vertragVon D fn) l Γ Λ}
    {v : Wert D τ} {ρ : Env D Γ} {σ : World D}
    (hZ : ZustandG M f stapel fn rho s0 log (.cons v ρ) (.schrumpf k) σ) :
    ∃ M', RufSchrittG P O passes M f M' ∧ ZustandG M' f stapel fn rho s0 log ρ k σ := by
  have hW := hZ.welt
  obtain ⟨M', hs, hZ'⟩ := w_schrumpf (P := P) (O := O) (passes := passes) hZ.1 k v ρ rfl
  rw [hW] at hZ'
  exact ⟨M', hs, hZ'⟩

/-- An abrupt exit above a `dann` layer: one peel. -/
theorem peelDannR {l : Bool} {Γ : Ctx} {Λ Λ1 Λ2 : List (Res D)} {M : RufMaschineG D}
    {log : List (RufEreignisF D)} (hl : l = true) {w : Bool}
    {r : Block D (vertragVon D fn) l Γ Λ Λ1}
    {b : Block D (vertragVon D fn) l Γ Λ1 Λ2} {k : GRest D (vertragVon D fn) l Γ Λ2}
    {ρ : Env D Γ} {σ : World D}
    (hZ : ZustandG M f stapel fn rho s0 log ρ (.dann (.cons (abbS hl w) r) (.dann b k)) σ) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f stapel fn rho s0 log ρ (.dann (.cons (abbS hl w) .nil) k) σ := by
  subst hl
  have hW := hZ.welt
  obtain ⟨M', hs, hZ'⟩ := w_peelDann (P := P) (O := O) (passes := passes) hZ.1 w r b k ρ rfl
  rw [hW] at hZ'
  exact ⟨M', hs, hZ'⟩

/-- An abrupt exit above a `schrumpf` layer: one peel, the binding dropped. -/
theorem peelSchrumpfR {l : Bool} {Γ : Ctx} {Λ Λ1 : List (Res D)} {τ : Ty} {M : RufMaschineG D}
    {log : List (RufEreignisF D)} (hl : l = true) {w : Bool}
    {r : Block D (vertragVon D fn) l (τ :: Γ) Λ Λ1}
    {k : GRest D (vertragVon D fn) l Γ Λ1} {ρ : Env D (τ :: Γ)} {σ : World D}
    (hZ : ZustandG M f stapel fn rho s0 log ρ (.dann (.cons (abbS hl w) r) (.schrumpf k)) σ) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f stapel fn rho s0 log ρ.tail (.dann (.cons (abbS hl w) .nil) k) σ := by
  subst hl
  have hW := hZ.welt
  cases ρ with
  | cons v ρt =>
    obtain ⟨M', hs, hZ'⟩ := w_peelSchrumpf (P := P) (O := O) (passes := passes) hZ.1 w r k v ρt rfl
    rw [hW] at hZ'
    exact ⟨M', hs, hZ'⟩

/-- An abrupt exit above a `frei` layer: one peel, the lock released. -/
theorem peelFreiR {l : Bool} {Γ : Ctx} {Λ Λ1 : List (Res D)} {M : RufMaschineG D}
    {log : List (RufEreignisF D)} (hl : l = true) {w : Bool} {L : D.Lock}
    {r : Block D (vertragVon D fn) l Γ Λ (Res.held L :: Λ1)}
    {k : GRest D (vertragVon D fn) l Γ Λ1} {ρ : Env D Γ} {σ : World D}
    (hZ : ZustandG M f stapel fn rho s0 log ρ (.dann (.cons (abbS hl w) r) (.frei L k)) σ) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f stapel fn rho s0 log ρ (.dann (.cons (abbS hl w) .nil) k) (σ.gibt L) := by
  subst hl
  have hW := hZ.welt
  obtain ⟨M', hs, hZ'⟩ := w_peelFrei (P := P) (O := O) (passes := passes) hZ.1 w L r k ρ rfl
  rw [hW] at hZ'
  exact ⟨M', hs, hZ'⟩

/-- **The loop of a `traverse`, normal completion.** From `trav t inv body ks
    k` the machine runs to `k` exactly as `traverseLauf` over `ks` ends
    normally: one invariant read (`travNext`) before each iteration, the
    body by its simulation -- normal completion (`travFort`), `next`
    (`dannNextTrav`, the next index) or `leave` (`dannLeaveTrav`, the
    invariant read, the loop left) -- and one read after the last
    iteration (`travDone`). -/
theorem travOkR {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D fn) true (.index (D.count t) :: Γ) Λ Λ)
    (hbody : SimOkBR P O passes f fn stapel rho s0 A R body)
    (hbodyA : SimAbbBR P O passes f fn stapel rho s0 A R body)
    (k : GRest D (vertragVon D fn) l Γ Λ) :
    ∀ (ks : List (Wert D (.index (D.count t)))) (log : List (RufEreignisF D))
      (σ σ' : World D) (ρ ρ' : Env D Γ),
      traverseLauf (l := l) (fun σ ρ => execBlock O passes R body σ ρ)
        (fun σ ρ => ((σ.lese Λ inv.orte), wahr? (eval (σ.lese Λ inv.orte) inv
          (σ.lese Λ inv.orte) ρ))) ks σ ρ = .ok σ' ρ' →
      ∀ (M : RufMaschineG D), ZustandG M f stapel fn rho s0 log ρ (.trav t inv body ks k) σ →
        HeldB (vertragVon D fn).boden Λ (offen σ.spur) → FreiA A M f →
        ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
          ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' k σ' ∧ offen σ'.spur = offen σ.spur
  | [], log, σ, σ', ρ, ρ', hex, M, hZ, _, _ => by
      have hW := hZ.welt
      simp only [traverseLauf] at hex
      split at hex
      · rename_i hw
        simp only [Ausgang.ok.injEq] at hex
        obtain ⟨rfl, rfl⟩ := hex
        obtain ⟨M1, hs1, hZ1⟩ := w_travDone (P := P) (O := O) (passes := passes) hZ.1
          t inv body k ρ rfl (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact ⟨M1, [], RufLaufG.einzeln hs1, hZ1, (Erw.lese _ _ _).offen⟩
      · cases hex
  | i :: is, log, σ, σ', ρ, ρ', hex, M, hZ, hΛ, hA => by
      have hW := hZ.welt
      simp only [traverseLauf] at hex
      split at hex
      · cases hex
      · rename_i hw
        have hw' : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true := by
          simpa using hw
        obtain ⟨M1, hs1, hZ1⟩ := w_travNext (P := P) (O := O) (passes := passes) hZ.1
          t inv body i is k ρ rfl (by rw [hW]; exact hw')
        rw [hW] at hZ1
        have hA1 := hA.lauf (RufLaufG.einzeln hs1)
        have hΛ1 := heldB_lese inv.orte hΛ (Λ₀ := Λ)
        -- the loop continues at `trav … is k`
        have weiter : ∀ (M3 : RufMaschineG D) (e3 : List (RufEreignisF D)) (σ2 : World D)
            (ρt : Env D Γ), RufLaufG P O passes f M M3 →
            ZustandG M3 f stapel fn rho s0 (e3 ++ log) ρt (.trav t inv body is k) σ2 →
            offen σ2.spur = offen σ.spur →
            traverseLauf (l := l) (fun σ ρ => execBlock O passes R body σ ρ)
              (fun σ ρ => ((σ.lese Λ inv.orte), wahr? (eval (σ.lese Λ inv.orte) inv
                (σ.lese Λ inv.orte) ρ))) is σ2 ρt = .ok σ' ρ' →
            ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
              ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' k σ' ∧
              offen σ'.spur = offen σ.spur := by
          intro M3 e3 σ2 ρt hl3 hZ3 ho3 hex3
          have hΛ3 : HeldB (vertragVon D fn).boden Λ (offen σ2.spur) := by rw [ho3]; exact hΛ
          obtain ⟨M4, e4, hr4, hZ4, ho4⟩ := travOkR t inv body hbody hbodyA k is _ σ2 σ' ρt ρ'
            hex3 M3 hZ3 hΛ3 (hA.lauf hl3)
          exact ⟨M4, e4 ++ e3, hl3.trans hr4, by rw [List.append_assoc]; exact hZ4,
            by rw [ho4, ho3]⟩
        split at hex
        · rename_i σ2 ρ2 hb2
          obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := hbody log _ _ _ _ hb2 M1 _ hZ1 hΛ1 hA1
          cases ρ2 with
          | cons i2 ρt =>
            have hW2 := hZ2.welt
            obtain ⟨M3, hs3, hZ3⟩ := w_travFort (P := P) (O := O) (passes := passes) hZ2.1
              t inv body is k i2 ρt rfl
            rw [hW2] at hZ3
            exact weiter M3 e2 σ2 ρt (RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)))
              hZ3 (by rw [ho2, (Erw.lese _ _ _).offen]) hex
        · rename_i h2 σ2 ρ2 hb2
          obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := hbodyA rfl log _ _ _ _ false
            (by rw [hb2]; rfl) M1 _ hZ1 hΛ1 hA1
          cases ρ2 with
          | cons i2 ρt =>
            have hW2 := hZ2.welt
            obtain ⟨M3, hs3, hZ3⟩ := w_nextTrav (P := P) (O := O) (passes := passes) hZ2.1
              t inv body is k r i2 ρt rfl (show HeldIn _ (offen σ2.spur) from (heldB_block r (by rw [ho2]; exact hΛ1)).heldIn)
            rw [hW2] at hZ3
            exact weiter M3 e2 σ2 ρt (RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)))
              hZ3 (by rw [ho2, (Erw.lese _ _ _).offen]) hex
        · rename_i h2 σ2 ρ2 hb2
          split at hex
          · rename_i hw2
            simp only [Ausgang.ok.injEq] at hex
            obtain ⟨rfl, rfl⟩ := hex
            obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := hbodyA rfl log _ _ _ _ true
              (by rw [hb2]; rfl) M1 _ hZ1 hΛ1 hA1
            cases ρ2 with
            | cons i2 ρt =>
              have hW2 := hZ2.welt
              obtain ⟨M3, hs3, hZ3⟩ := w_leaveTrav (P := P) (O := O) (passes := passes) hZ2.1
                t inv body is k r i2 ρt rfl (by rw [hW2]; simpa [Env.tail] using hw2) (show HeldIn _ (offen σ2.spur) from (heldB_block r (by rw [ho2]; exact hΛ1)).heldIn)
              rw [hW2] at hZ3
              exact ⟨M3, e2, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
                by rw [(Erw.lese _ _ _).offen, ho2, (Erw.lese _ _ _).offen]⟩
          · cases hex
        all_goals cases hex

/-- **The loop of a `retry`, normal completion.** From `wieder n bis body
    ueber k` the machine runs to `k` exactly as `retryLauf` with bound `n`
    ends normally: at bound `0` the check `if bis {} else { overflow }`
    (`wiederUeber`, then the `if` and the overflow block), a read
    of `bis` before each try (`wiederWeiter` on `true`, `wiederSchritt`
    into the body on `false`), the body to its normal end (`wiederFort`),
    to `next` (`dannNextWieder`, the next try) or to `leave`
    (`dannLeaveWieder`, the loop left). -/
theorem retryOkR {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (bis : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D fn) true Γ Λ Λ) (ueber : Block D (vertragVon D fn) l Γ Λ Λ)
    (hbody : SimOkBR P O passes f fn stapel rho s0 A R body)
    (hbodyA : SimAbbBR P O passes f fn stapel rho s0 A R body)
    (hueber : SimOkBR P O passes f fn stapel rho s0 A R ueber)
    (k : GRest D (vertragVon D fn) l Γ Λ) :
    ∀ (n : Nat) (log : List (RufEreignisF D)) (σ σ' : World D) (ρ ρ' : Env D Γ),
      retryLauf (fun σ ρ => execBlock O passes R body σ ρ)
        (fun σ ρ => ((σ.lese Λ bis.orte), wahr? (eval (σ.lese Λ bis.orte) bis
          (σ.lese Λ bis.orte) ρ)))
        (fun σ ρ => execBlock O passes R ueber σ ρ) n σ ρ = .ok σ' ρ' →
      ∀ (M : RufMaschineG D), ZustandG M f stapel fn rho s0 log ρ (.wieder n bis body ueber k) σ →
        HeldB (vertragVon D fn).boden Λ (offen σ.spur) → FreiA A M f →
        ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
          ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' k σ' ∧ offen σ'.spur = offen σ.spur
  | 0, log, σ, σ', ρ, ρ', hex, M, hZ, hΛ, hA => by
      have hW := hZ.welt
      simp only [retryLauf] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_wiederUeber (P := P) (O := O) (passes := passes) hZ.1
        bis body ueber k ρ rfl
      rw [hW] at hZ1
      have hW1 := hZ1.welt
      have hA1 := hA.lauf (RufLaufG.einzeln hs1)
      split at hex
      · rename_i hw
        simp only [Ausgang.ok.injEq] at hex
        obtain ⟨rfl, rfl⟩ := hex
        obtain ⟨M2, hs2, hZ2⟩ := w_iteWahr (P := P) (O := O) (passes := passes) hZ1.1
          bis .nil ueber .nil k ρ rfl (by rw [hW1]; simpa using hw)
        rw [hW1] at hZ2
        obtain ⟨M3, hs3, hZ3⟩ := w_dannLeer (P := P) (O := O) (passes := passes) hZ2.1 _ ρ rfl
        rw [hZ2.welt] at hZ3
        obtain ⟨M4, hs4, hZ4⟩ := w_dannLeer (P := P) (O := O) (passes := passes) hZ3.1 _ ρ rfl
        rw [hZ3.welt] at hZ4
        exact ⟨M4, [], RufLaufG.schritt hs1 (RufLaufG.schritt hs2 (RufLaufG.schritt hs3
          (RufLaufG.einzeln hs4))), hZ4, (Erw.lese _ _ _).offen⟩
      · rename_i hw
        have hw' : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = false := by
          simpa using hw
        obtain ⟨M2, hs2, hZ2⟩ := w_iteFalsch (P := P) (O := O) (passes := passes) hZ1.1
          bis .nil ueber .nil k ρ rfl (by rw [hW1]; exact hw')
        rw [hW1] at hZ2
        obtain ⟨M3, e3, hr3, hZ3, ho3⟩ := hueber log _ _ _ _ hex M2 _ hZ2
          (heldB_lese bis.orte hΛ (Λ₀ := Λ)) (hA1.lauf (RufLaufG.einzeln hs2))
        obtain ⟨M4, hs4, hZ4⟩ := w_dannLeer (P := P) (O := O) (passes := passes) hZ3.1 k ρ' rfl
        rw [hZ3.welt] at hZ4
        exact ⟨M4, e3, RufLaufG.schritt hs1 (RufLaufG.schritt hs2 (hr3.trans (RufLaufG.einzeln hs4))),
          hZ4, by rw [ho3, (Erw.lese _ _ _).offen]⟩
  | n + 1, log, σ, σ', ρ, ρ', hex, M, hZ, hΛ, hA => by
      have hW := hZ.welt
      simp only [retryLauf] at hex
      split at hex
      · rename_i hw
        simp only [Ausgang.ok.injEq] at hex
        obtain ⟨rfl, rfl⟩ := hex
        obtain ⟨M1, hs1, hZ1⟩ := w_wiederWeiter (P := P) (O := O) (passes := passes) hZ.1
          n bis body ueber k ρ rfl (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact ⟨M1, [], RufLaufG.einzeln hs1, hZ1, (Erw.lese _ _ _).offen⟩
      · rename_i hw
        have hw' : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = false := by
          simpa using hw
        obtain ⟨M1, hs1, hZ1⟩ := w_wiederSchritt (P := P) (O := O) (passes := passes) hZ.1
          n bis body ueber k ρ rfl (by rw [hW]; exact hw')
        rw [hW] at hZ1
        have hA1 := hA.lauf (RufLaufG.einzeln hs1)
        have hΛ1 := heldB_lese bis.orte hΛ (Λ₀ := Λ)
        have weiter : ∀ (M3 : RufMaschineG D) (e3 : List (RufEreignisF D)) (σ2 : World D)
            (ρ2 : Env D Γ), RufLaufG P O passes f M M3 →
            ZustandG M3 f stapel fn rho s0 (e3 ++ log) ρ2 (.wieder n bis body ueber k) σ2 →
            offen σ2.spur = offen σ.spur →
            retryLauf (fun σ ρ => execBlock O passes R body σ ρ)
              (fun σ ρ => ((σ.lese Λ bis.orte), wahr? (eval (σ.lese Λ bis.orte) bis
                (σ.lese Λ bis.orte) ρ)))
              (fun σ ρ => execBlock O passes R ueber σ ρ) n σ2 ρ2 = .ok σ' ρ' →
            ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
              ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' k σ' ∧
              offen σ'.spur = offen σ.spur := by
          intro M3 e3 σ2 ρ2 hl3 hZ3 ho3 hex3
          have hΛ3 : HeldB (vertragVon D fn).boden Λ (offen σ2.spur) := by rw [ho3]; exact hΛ
          obtain ⟨M4, e4, hr4, hZ4, ho4⟩ := retryOkR bis body ueber hbody hbodyA hueber k n _ σ2
            σ' ρ2 ρ' hex3 M3 hZ3 hΛ3 (hA.lauf hl3)
          exact ⟨M4, e4 ++ e3, hl3.trans hr4, by rw [List.append_assoc]; exact hZ4,
            by rw [ho4, ho3]⟩
        split at hex
        · rename_i σ2 ρ2 hb2
          obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := hbody log _ _ _ _ hb2 M1 _ hZ1 hΛ1 hA1
          have hW2 := hZ2.welt
          obtain ⟨M3, hs3, hZ3⟩ := w_wiederFort (P := P) (O := O) (passes := passes) hZ2.1
            n bis body ueber k ρ2 rfl
          rw [hW2] at hZ3
          exact weiter M3 e2 σ2 ρ2 (RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)))
            hZ3 (by rw [ho2, (Erw.lese _ _ _).offen]) hex
        · rename_i h2 σ2 ρ2 hb2
          obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := hbodyA rfl log _ _ _ _ false
            (by rw [hb2]; rfl) M1 _ hZ1 hΛ1 hA1
          have hW2 := hZ2.welt
          obtain ⟨M3, hs3, hZ3⟩ := w_abbWieder (P := P) (O := O) (passes := passes) hZ2.1
            false n bis body ueber k r ρ2 rfl (show HeldIn _ (offen σ2.spur) from (heldB_block r (by rw [ho2]; exact hΛ1)).heldIn)
          rw [hW2] at hZ3
          exact weiter M3 e2 σ2 ρ2 (RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)))
            hZ3 (by rw [ho2, (Erw.lese _ _ _).offen]) hex
        · rename_i h2 σ2 ρ2 hb2
          simp only [Ausgang.ok.injEq] at hex
          obtain ⟨hσ, hρ⟩ := hex
          subst hσ hρ
          obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := hbodyA rfl log _ _ _ _ true
            (by rw [hb2]; rfl) M1 _ hZ1 hΛ1 hA1
          have hW2 := hZ2.welt
          obtain ⟨M3, hs3, hZ3⟩ := w_abbWieder (P := P) (O := O) (passes := passes) hZ2.1
            true n bis body ueber k r ρ2 rfl (show HeldIn _ (offen σ2.spur) from (heldB_block r (by rw [ho2]; exact hΛ1)).heldIn)
          rw [hW2] at hZ3
          exact ⟨M3, e2, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
            by rw [ho2, (Erw.lese _ _ _).offen]⟩
        all_goals cases hex

end SimOk
end Gabbro.Grammatik
