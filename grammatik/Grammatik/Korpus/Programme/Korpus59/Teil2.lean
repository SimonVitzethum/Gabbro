module

public import Grammatik.Zielsatz.Kern.Proben
public import Grammatik.Korpus.Programme.Korpus59.Teil1
public import Grammatik.Korpus.Programme.Korpus59.Teil1a
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
namespace K59

theorem kP_inv : ∀ f : kD.Fn, InvGutS kP 0 (axWahr kD) kSI f :=
  fun _ => invGutS_ohne fun i _ => (nomatch i)

theorem kP_ohneEwig : ohneEwigB kP kFs = true := by decide

theorem kP_koerper_alle : ∀ (passes : Nat) (f : kD.Fn), KoerperGutS kP passes (axWahr kD) kSI f :=
  koerperGutS_alle kFs_voll kP_ohneEwig kP_koerper

theorem kP_inv_alle : ∀ (passes : Nat) (f : kD.Fn), InvGutS kP passes (axWahr kD) kSI f :=
  invGutS_alle kFs_voll kP_ohneEwig kP_inv

/-! ## 4. The program as one declaration, and every premise group -/

/-- The start memory: every slot zero. -/
def kSp : Speicher kD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- **`beispiele/59` as ONE declaration**: code `kP`, lock family `kSI`,
    no axiom, declared starts `takt_verteiler` and `ruf_verteiler` (the two
    entry dispatch roots, no parameters), initial memory all zero. -/
def kE : Zielsatz.Einheit kD where
  P := kP
  S := kSI
  Q := axWahr kD
  starts := [⟨kTaktVert, .nil⟩, ⟨kRufVert, .nil⟩]
  sp0 := kSp
  gestartet := []
  arenen := []
  akku := []
  pruefungen := []
  grants0 := []

theorem korpus59_nutzer : Zielsatz.NutzerPflicht kE :=
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

theorem kO_hw [RootNativeFloat.Hardware] : Zielsatz.HardwareAnnahmen kO kE.Q :=
  ⟨kO_gut, kO_lokal, axVertragO_wahr kO, inferInstance⟩

theorem kE_akzeptiert : akzeptiert_pruefer.akzeptiert kE kFs [KLock.takt, KLock.ring] kCs = true := by
  rw [akzeptiert_pruefer_eq]
  exact kP_akzeptiert

/-- **The goal theorem on `beispiele/59`**: for every oracle meeting (c), every
    budget, every runtime start meeting (d), and every reachable machine of
    `kP.mitRuhe`, the conclusion `Ziel` holds -- `gabbro_ziel` with the
    concrete checker. -/
theorem korpus59_ziel (O : Orakel kD) (hO : Zielsatz.HardwareAnnahmen O kE.Q) (passes : Nat)
    (sp : Speicher kD.mitRuhe)
    (init : Faden → Σ f : kD.mitRuhe.Fn, Env kD.mitRuhe (kD.mitRuhe.params f))
    (hL : Zielsatz.Laufzeit kE sp init) (M : RufMaschineG kD.mitRuhe)
    (hM : RufErreichbarG kE.P.mitRuhe O.mitRuhe passes (RufStartG kE.P.mitRuhe sp init) M) :
    Zielsatz.Ziel kE.P.mitRuhe kE.S.mitRuhe O.mitRuhe passes (RufStartG kE.P.mitRuhe sp init) M :=
  Zielsatz.gabbro_ziel_g akzeptiert_pruefer kD kE ⟨kFs, kFs_voll⟩ ⟨[KLock.takt, KLock.ring], kLocks_voll⟩ ⟨kCs, kCs_voll⟩
    kE_akzeptiert korpus59_nutzer O hO passes sp init hL M hM

/-- The index-`0` environment for the witness run. -/
def kRho0 : Env kD [Ty.index 64] := .cons ⟨0, by decide, by decide⟩ .nil

/-- **Witness for `korpus59_nutzer`** (rule 13): the premise group jointly
    with a non-degenerate run -- `zaehle`'s body from the all-zero world
    returns with `Takte[0] = 1` while it started `0`: a reached run with a
    memory-changing step, on a table a function writes. -/
theorem korpus59_nutzer_zeuge
    (R : ∀ f : kD.Fn, World kD → Env kD (kD.params f) → RufAusgang f) :
    Zielsatz.NutzerPflicht kE ∧ ∃ (σ' : World kD) (v : ErgVal kD (kD.erg kZaehle)),
      execEndH kSI kO (fun _ σ => σ) 0 R kRumpfZaehle (kSp.welt []) kRho0 = .zurueck σ' v ∧
      (σ'.slots KTab.takte 0 ()).n = 1 ∧ ((kSp.welt []).slots KTab.takte 0 ()).n = 0 :=
  ⟨korpus59_nutzer, _, _, rfl, rfl, rfl⟩

/-
  CUTS: the `deadline <= … arch x86_64 falsifier …` annotations of all four
  source functions are dropped (no `Expr` form; exporter refusal LG001
  `check_fn`, quoted in the header). Everything else of the source is
  modelled: tables, locks (including `masks irqs` as `D.maskiert`), bodies,
  Held sets, entry dispatch roots as starts. `costs`/`reads` are ignored
  form. What is NOT claimed: anything about the `.gab` source text (no
  exporter link yet -- lane 201), and no stage-(b) simulation certificate.
-/
#print axioms K59.kP_akzeptiert
#print axioms K59.korpus59_nutzer
#print axioms K59.korpus59_ziel
#print axioms K59.korpus59_nutzer_zeuge

end K59

end Gabbro.Grammatik
