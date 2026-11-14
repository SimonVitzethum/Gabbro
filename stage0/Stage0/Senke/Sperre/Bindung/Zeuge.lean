/- Small joint witnesses: admitted environments, nonempty scoped lock code,
   a real failed serving comparison, and the shared abstract simulation. -/
module
public import Stage0.Senke.Sperre.Bindung.Bild
public import Stage0.Senke.Sperre.Bindung.Schritt
public import Stage0.Senke.Sperre.Bindung.Simulation
public import Stage0.Senke.Sperre.Warten.Fixture
@[expose] public section

namespace Gabbro.Stage0.Senke.WaitBindingWitness
set_option maxRecDepth 100000
open Gabbro.Grammatik Gabbro.Grammatik.Parser Runner Runner.IR Runner.Mem

/-- Both selected source profiles pass the canonical admission gate. -/
def profile (environment : String) : List SItemTief :=
  [.profT false [.mode "environment" environment]]

def binding (environment : String) : ProfilBindung.ProfileBinding :=
  ProfilBindung.ProfileBinding.aus (profile environment)

def layout (environment : String) : Lay WartenProbe.D :=
  { WartenProbe.layout with lockWait := (Profil.imageEnvironment {} (binding environment)).lockWait }

/-- The two admitted source profiles select different implementations around
    the same nonempty body and the same lock address, with identical code size. -/
theorem profile_lock_zeuge :
    (Profil.prepareItems {} (profile "freestanding")).isOk = true ∧
    (Profil.prepareItems {} (profile "linux")).isOk = true ∧
    (Profil.prepareItems { environment := some .linux } (profile "freestanding")).isOk = false ∧
    ((locksCodeT (layout "freestanding") 8192 4 [ci 1 3 77 0] 0 0).all fun i => i.o != 23) = true ∧
    (nimmT (layout "linux") 8192 4)[26]? = some (ci 23 21 14 0) ∧
    (gibT (layout "linux") 8192 4)[15]? = some (ci 23 21 14 0) ∧
    (locksCodeT (layout "freestanding") 8192 4 [ci 1 3 77 0] 0 0).length = 87 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
  · exact locksCodeT_spin_no_syscall _ _ _ _ _ _ rfl rfl
  · exact (ticket_futex_syscalls _ _ _ rfl).1
  · exact (ticket_futex_syscalls _ _ _ rfl).2.1
  · rw [locksCodeT_len]; rfl

/-- The source spelling, CLI flag, conflict refusal and closed value decoder
    are all exercised, rather than only constructing a profile AST by hand. -/
theorem source_environment_zeuge :
    (parseProfEintraege 8 [.ident "environment", .ident "freestanding", .zeichen ";", .zeichen "}"]) =
      .ok ([.mode "environment" "freestanding"], [.zeichen "}"]) ∧
    (Profil.parseOptions ["--environment", "freestanding"] {}).toOption.map (·.environment) =
      some (some .freestanding) ∧
    (Profil.parseOptions ["--environment", "unknown"] {}).isOk = false ∧
    (Profil.prepareItems {} (profile "unknown")).isOk = false ∧
    (Profil.prepareItems {} [.profT false [.mode "environment" "linux", .mode "environment" "freestanding"]]).isOk = false := by
  decide

/-- Encoded memory for a contended freestanding lock, with a protected frame
    word and three actual ticket-lock words. -/
def memory : Mem where
  b a := if a.toNat = 4120 then 77
    else if a.toNat = 8192 then 1
    else if a.toNat = 8200 then 0
    else if a.toNat = 8208 then 0
    else (((nimmT (layout "freestanding") 8192 4).flatMap encII)[a.toNat]?).getD 0
  rd _ := true
  wr _ := true

/-- Joint witness of all machine-state premises of the two-instruction retry.
    This uses the runner's ordinary IR semantics and no futex response. -/
theorem nimmT_spin_retry_zeuge [Kern] :
    ∃ m f, LS memory m 4096 4 8192 f 1 0 0 ∧ f 2 = 1 ∧ f 5 = 0 ∧
      Star ⟨160, 4096⟩ m ⟨112, 4096⟩ m ∧ m.rd64 (slot 4096 3) = some 77 := by
  have E : LE memory 0 4096 4 8192 (nimmT (layout "freestanding") 8192 4) := by
    refine ⟨⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
      by decide, by decide, by decide, rfl, rfl, rfl, ?_, ?_⟩
    · apply codeAt_bytes (nimmT (layout "freestanding") 8192 4) 0 (by decide)
      intro i hi
      have length : ((nimmT (layout "freestanding") 8192 4).flatMap encII).length = 560 := by
        rw [flatMap_enc_len, nimmT_len]
      refine ⟨rfl, rfl, ?_⟩
      simp only [memory, Nat.zero_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
        ite_eq_right (show i ≠ 4120 by omega),
        ite_eq_right (show i ≠ 8192 by omega),
        ite_eq_right (show i ≠ 8200 by omega),
        ite_eq_right (show i ≠ 8208 by omega),
        List.getElem?_eq_getElem hi, Option.getD_some]
    · unfold CodeFar
      rw [nimmT_len]
      decide
  obtain ⟨f0, state0⟩ := ls_init E (o := 1) (c := 0) (w := 0)
    (by decide) (by decide) (by decide)
  obtain ⟨m, f, _, state, ticket, seen, compared⟩ :=
    nimmT_check E state0 (At.whole _)
  refine ⟨m, f, state, ticket, seen, ?_, ?_⟩
  · exact nimmT_spin_retry E state (At.whole _) rfl compared (by rw [ticket, seen]; decide)
  · rw [state.ag.rd_low (by decide) (by decide) (by decide)]
    decide

end Gabbro.Stage0.Senke.WaitBindingWitness
