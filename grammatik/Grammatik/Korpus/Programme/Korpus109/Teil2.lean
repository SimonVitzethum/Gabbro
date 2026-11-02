module

public import Grammatik.Zielsatz.Kern.Proben
public import Grammatik.Korpus.Programme.Korpus109.Teil1
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section

namespace Gabbro.Grammatik
namespace K109

/-- **`beispiele/109` as ONE declaration**: code `kP`, lock family `kSI`,
    no axiom, declared starts `distribute_a` and `distribute_b` (the two
    entry dispatch roots, no parameters), initial memory all zero. -/
def kE : Zielsatz.Einheit kD := ⟨kP, kSI, axWahr kD, [⟨kDistA, .nil⟩, ⟨kDistB, .nil⟩], kSp, [], []⟩

theorem korpus109_nutzer : Zielsatz.NutzerPflicht kE :=
  ⟨⟨fun passes f => ⟨kP_koerper_alle passes f, kP_inv_alle passes f,
      invGutGrund_ohneGrund (by cases f <;> rfl)⟩, fun _ _ _ _ => rfl, axEnsLokal_wahr, ptrVerfeinert_trivial (fun f _ _ => by cases f <;> rfl) (fun _ => rfl)⟩,
    ⟨fun _ => rfl, fun a ha => by
      simp only [kE, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> rfl⟩⟩

/-- No axiom, no register, no global: the oracle is empty. -/
def kO : Orakel kD where
  wirkt := fun a => (nomatch a)
  regLies := fun r => (nomatch r)
  regSchreib := fun r _ => (nomatch r)
  sichtbar := fun g => (nomatch g)

theorem kO_gut : GutO kO := fun a => (nomatch a)

theorem kO_lokal : RegLokal kO := ⟨(fun r _ _ _ => nomatch r), (fun g _ _ _ => nomatch g)⟩

theorem kO_hw : Zielsatz.HardwareAnnahmen kO kE.Q := ⟨kO_gut, kO_lokal, axVertragO_wahr kO⟩

theorem kE_akzeptiert : akzeptiert_pruefer.akzeptiert kE kFs [KLock.l, KLock.m] kCs = true :=
  (by show Akzeptiert kP kSI kFs [KLock.l, KLock.m] kCs [kDistA, kDistB] [] = true; exact kP_akzeptiert)

/-- **The goal theorem on `beispiele/109`**: for every oracle meeting (c), every
    budget, every runtime start meeting (d), and every reachable machine of
    `kP.mitRuhe`, the conclusion `Ziel` holds -- `gabbro_ziel` with the
    concrete checker. -/
theorem korpus109_ziel (O : Orakel kD) (hO : Zielsatz.HardwareAnnahmen O kE.Q) (passes : Nat)
    (sp : Speicher kD.mitRuhe)
    (init : Faden → Σ f : kD.mitRuhe.Fn, Env kD.mitRuhe (kD.mitRuhe.params f))
    (hL : Zielsatz.Laufzeit kE sp init) (M : RufMaschineG kD.mitRuhe)
    (hM : RufErreichbarG kE.P.mitRuhe O.mitRuhe passes (RufStartG kE.P.mitRuhe sp init) M) :
    Zielsatz.Ziel kE.P.mitRuhe kE.S.mitRuhe O.mitRuhe passes (RufStartG kE.P.mitRuhe sp init) M :=
  Zielsatz.gabbro_ziel_g akzeptiert_pruefer kD kE ⟨kFs, kFs_voll⟩ ⟨[KLock.l, KLock.m], kLocks_voll⟩ ⟨kCs, kCs_voll⟩
    kE_akzeptiert korpus109_nutzer O hO passes sp init hL M hM

/-- The index-`0` environment for the witness run. -/
def kRho0 : Env kD [Ty.index 4] := .cons ⟨0, by decide, by decide⟩ .nil

/-- **Witness for `korpus109_nutzer`** (rule 13): the premise group jointly
    with a non-degenerate run -- `write_a`'s body from the all-zero world
    returns with `T[0] = 1` while it started `0`: a reached run with a
    memory-changing step, on a table a function writes. -/
theorem korpus109_nutzer_zeuge
    (R : ∀ f : kD.Fn, World kD → Env kD (kD.params f) → RufAusgang f) :
    Zielsatz.NutzerPflicht kE ∧ ∃ (σ' : World kD) (v : ErgVal kD (kD.erg kWriteA)),
      execEndH kSI kO (fun _ σ => σ) 0 R kRumpfWriteA (kSp.welt []) kRho0 = .zurueck σ' v ∧
      (σ'.slots KTab.t 0 ()).n = 1 ∧ ((kSp.welt []).slots KTab.t 0 ()).n = 0 :=
  ⟨korpus109_nutzer, _, _, rfl, rfl, rfl⟩

/-
  CUTS: nothing is cut inside this file. The model covers the whole source
  file `beispiele/0109-lockfree-entry-roots.gab` except its `costs` effects
  (ignored form, like `reads`) and the `entry` register/stack hardware around
  the two dispatch roots (the roots themselves are the declared starts).
  What is NOT claimed: anything about the `.gab` source text (no exporter
  link yet -- lane 201), and no stage-(b) simulation certificate.
-/
#print axioms K109.kP_akzeptiert
#print axioms K109.korpus109_nutzer
#print axioms K109.korpus109_ziel
#print axioms K109.korpus109_nutzer_zeuge

end K109

end Gabbro.Grammatik
