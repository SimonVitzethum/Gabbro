/-
  File:      stage0/Stage0/Senke/Bild/Gleich/RufAtZeuge.lean
  Subject:   Witnesses of package P2 (`rufAt` against `rufRumpf` up to read events) on the call fixture `t4` of
             `RufAdaequatRufG`, with two DIFFERENT start worlds (the start world and the start world after a read of
             `konto`) and the read-blind fixture oracle:
             * the short direction fires with all premises jointly (`rufAt_rufRumpf_zeuge`);
             * its error set is needed: with every `requires` false, `rufAt` fails a contract check
               (`rufAt_vertragMarke_zeuge`, on `t4Pk` of `befund_vertrag`);
             * the fixture's contracts are valid (`t4P_gueltig`), so the exact relation holds
               (`rufAt_rufRumpf_gueltig_zeuge`);
             * the one-unfolding duty holds for the plain caller at depth 2 (`vertragsfrei_t4F`), and the converse
               direction turns the body run's `ok` into an `ok` of `rufAt` with a `≈` world
               (`rufRumpf_ok_rufAt_zeuge`).
             Symbolic body steps and the general handler theorems; no kernel evaluation of a whole run.
-/
module
public import Stage0.Senke.Bild.Gleich.RufAtUmkehr
public import Stage0.Senke.Bild.Gleich.Zeuge
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T9.Teil2
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

/-- The start world after a read of `konto`: `≈` to the start world and different from it (`lesegleich_zeuge`). -/
abbrev zeugeWeltL : World t4D := zeugeWelt.lese [] [.inl ()]

/-- **Short direction, all premises jointly**: read-blind oracle, two different `≈` start worlds, the plain caller
    at depth 2 (one nested call). -/
theorem rufAt_rufRumpf_zeuge :
    RufLG VertragMarke (rufAt t4P t4O 0 2 t4F zeugeWelt Env.nil) (rufRumpf t4P t4O 0 2 t4F zeugeWeltL Env.nil) :=
  rufAt_rufRumpf_lg (P := t4P) (passes := 0) leseblind_t4O 2 t4F zeugeWelt zeugeWeltL Env.nil
    (weltGleich_lese _ _ _)

/-- **The error set is needed**: with every `requires` false, `rufAt` answers a contract mark at the callee. -/
theorem rufAt_vertragMarke_zeuge :
    rufAt t4Pk t4O 0 1 t4G zeugeWelt Env.nil = .logik (.vorbedingung t4G) ∧
      VertragMarke (.logik (.vorbedingung t4G) : Fehlermarke t4D) :=
  ⟨rfl, .vor t4G⟩

/-- The fixture's contracts are valid: every `requires` and `ensures` is `true`, and there is no invariant. -/
theorem t4P_gueltig : VertragGueltig t4P :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, (fun i => nomatch i)⟩

/-- With the fixture's trivial contracts and no invariants, a body return is a call return.
    The world and return value stay symbolic throughout the single handler step. -/
theorem rufAt_t4D_ok_of_body {P : Programm t4D} {n : Nat} {g : t4D.Fn} {σ σ' : World t4D}
    {v : ErgVal t4D (t4D.erg g)} (hq : P.requires g = .tru) (he : P.ensures g = .tru)
    (hb : execEnd (V := vertragVon t4D g) t4O 0 (rufAt P t4O 0 n) (P.rumpf g) σ Env.nil =
      .zurueck σ' v) : rufAt P t4O 0 (n + 1) g σ Env.nil = .ok σ' v := by
  have hi : t4D.invs = [] := rfl
  simp only [rufAt_succ_eq, rufSchritt, hq, he, Expr.orte, World.lese, World.merke,
    List.map_nil, List.nil_append, eval, wahr?, Bool.true_eq_false, ↓reduceIte, hb, hi,
    List.filter_nil, List.foldl_nil, List.find?_nil]

/-- The leaf callee returns for any handler and symbolic start world: one write and one return. -/
theorem t4G_body_kehrt (R : ∀ g : t4D.Fn, World t4D → Env t4D (t4D.params g) → RufAusgang g)
    (σ : World t4D) : ∃ (σ' : World t4D) (v : ErgVal t4D (t4D.erg t4G)),
      execEnd (V := vertragVon t4D t4G) t4O 0 R (t4P.rumpf t4G) σ Env.nil = .zurueck σ' v := by
  change ∃ σ' v, execEnd (V := vertragVon t4D t4G) t4O 0 R t4GRumpf σ Env.nil = .zurueck σ' v
  simp only [t4GRumpf, execEnd, execStmt]
  exact ⟨_, _, rfl⟩

/-- The image handler returns from the leaf callee, without reducing a concrete world. -/
theorem t4G_ruf_kehrt (σ : World t4D) : ∃ (σ' : World t4D) (v : ErgVal t4D (t4D.erg t4G)),
    rufAt t4P t4O 0 1 t4G σ Env.nil = .ok σ' v := by
  obtain ⟨σ', v, hb⟩ := t4G_body_kehrt (rufAt t4P t4O 0 0) σ
  exact ⟨σ', v, rufAt_t4D_ok_of_body rfl rfl hb⟩

/-- The plain caller returns whenever its handler returns from `g` in the start world. -/
theorem t4F_body_kehrt {R : ∀ g : t4D.Fn, World t4D → Env t4D (t4D.params g) → RufAusgang g}
    {σ σ1 : World t4D} {v1 : ErgVal t4D (t4D.erg t4G)} (hG : R t4G σ Env.nil = .ok σ1 v1) :
    ∃ (σ' : World t4D) (v : ErgVal t4D (t4D.erg t4F)),
      execEnd (V := vertragVon t4D t4F) t4O 0 R (t4P.rumpf t4F) σ Env.nil = .zurueck σ' v := by
  change ∃ σ' v, execEnd (V := vertragVon t4D t4F) t4O 0 R t4FRumpf σ Env.nil = .zurueck σ' v
  simp only [t4FRumpf, execEnd, execStmt, Args.orte, evalArgs, World.lese, World.merke,
    List.map_nil, List.nil_append, hG]
  exact ⟨_, _, rfl⟩

/-- **The exact relation under valid contracts**, on the two different start worlds. -/
theorem rufAt_rufRumpf_gueltig_zeuge :
    RufLG (fun _ => False) (rufAt t4P t4O 0 2 t4F zeugeWelt Env.nil)
      (rufRumpf t4P t4O 0 2 t4F zeugeWeltL Env.nil) :=
  rufAt_rufRumpf_gueltig (passes := 0) t4P_gueltig leseblind_t4O 2 t4F zeugeWelt zeugeWeltL Env.nil
    (weltGleich_lese _ _ _)

/-- **The one-unfolding duty at the plain caller**: `requires` holds, the body under `rufAt` at depth 1 returns
    (no `logik`), `ensures` is `true`, no invariant is owed -- so `rufAt` at depth 2 fails no contract check. -/
theorem vertragsfrei_t4F : Vertragsfrei t4P t4O 0 2 t4F zeugeWelt Env.nil := by
  obtain ⟨σ₂, v, hz⟩ : ∃ (σ₂ : World t4D) (v : ErgVal t4D (vertragVon t4D t4F).erg),
      execEnd (V := vertragVon t4D t4F) t4O 0 (rufAt t4P t4O 0 1) (t4P.rumpf t4F)
        (zeugeWelt.lese (Signatur.anfang t4D (t4D.signatur t4F)) (t4P.requires t4F).orte) Env.nil =
        .zurueck σ₂ v := by
    obtain ⟨σ1, v1, hG⟩ := t4G_ruf_kehrt zeugeWelt
    exact t4F_body_kehrt hG
  exact vertragsfrei_schritt (P := t4P) (O := t4O) (passes := 0) (n := 1) (g := t4F) (σ := zeugeWelt)
    (ρ := Env.nil) rfl
    (fun _ h => nomatch (h.symm.trans hz))
    (fun _ _ _ => rfl)
    (fun _ _ _ i => nomatch i)

/-- **Converse direction, all premises jointly**: the body run of machine G from the read world returns, and
    `rufAt` from the start world returns the same value in a `≈` world. -/
theorem rufRumpf_ok_rufAt_zeuge :
    ∃ (σ₂ : World t4D) (v : ErgVal t4D (t4D.erg t4F)),
      rufRumpf t4P t4O 0 2 t4F zeugeWeltL Env.nil = .ok σ₂ v ∧
      ∃ σ₁, rufAt t4P t4O 0 2 t4F zeugeWelt Env.nil = .ok σ₁ v ∧ WeltGleich σ₁ σ₂ := by
  obtain ⟨σ₂, v, h⟩ : ∃ (σ₂ : World t4D) (v : ErgVal t4D (t4D.erg t4F)),
      rufRumpf t4P t4O 0 2 t4F zeugeWeltL Env.nil = .ok σ₂ v := by
    obtain ⟨σG, vG, hG⟩ := t4G_ruf_kehrt zeugeWeltL
    obtain ⟨σF, vF, hF⟩ := t4F_body_kehrt hG
    have hRF : rufAt t4P t4O 0 2 t4F zeugeWeltL Env.nil = .ok σF vF :=
      rufAt_t4D_ok_of_body rfl rfl hF
    obtain ⟨σ₂, h₂, _⟩ := rufAt_ok_rufRumpf leseblind_t4O (WeltGleich.refl zeugeWeltL) hRF
    exact ⟨σ₂, vF, h₂⟩
  exact ⟨σ₂, v, h, rufRumpf_ok_rufAt leseblind_t4O vertragsfrei_t4F (weltGleich_lese _ _ _) h⟩

end Gabbro.Stage0.Senke.BildLauf
