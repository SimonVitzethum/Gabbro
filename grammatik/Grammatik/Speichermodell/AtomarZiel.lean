/-
  File:      Grammatik/Speichermodell/AtomarZiel.lean
  Subject:   THE LEGS WITH SHARED ATOMICS OVER MACHINE W, collected. Opus lane O25b, 2026-09-26.
             Standalone (NOT in `Spec.lean`).

  Pieces 1-7 of lane O25b proved, each on its own: every W step is a GX step whose presented
  memory agrees with G's outside the shared atomics `Tg` (`schwach_ist_gX`); the contract,
  invariant and start legs over GX, with the user obligation (b) quantified over every answer
  a shared atomic read may give (`ziel_ort_atomar_voll`, premise `KoerperGutSA` and its twins);
  race freedom, no wait cycle and no global deadlock over GA (`rennfreiGA`,
  `kein_warteZyklusGA`, `keine_verklemmungGA`).

  This file closes the chain from machine W's own start:

  * `gx_aus_w` -- every machine W reaches has a G-part that GX reaches;
  * `ZielAtomarW` -- the legs at such a machine: `SpurInv`, lock exclusivity, the seven contract
    and start legs of `Ziel`, no wait cycle, no global deadlock, and the weak-memory leg in GX
    form (every W step from here is a GX step, and presents G's memory outside `Tg`);
  * `ziel_atomar_w` -- THE THEOREM: under the named premises, every machine W reaches satisfies
    `ZielAtomarW`.

  What is NOT here (the remaining gap to a `Spec.lean` diff, report `messung/OPUS-O25B-ATOMICS.md`):
  the premises on `Tg` (`hTA`, `hTV`, `hTS`, `hTO`, `FussSX`) are hypotheses, not a checker Bool;
  the legs `InvRuheG`, `InvSichtG`, `SperrWechselG`, `SperrSichtG`, `KernHaltG`, `FortschrittG`
  and `ZeitAb` and the thread machine `ZielF` are not re-proved over GX.
-/
import Grammatik.Speichermodell.AtomarInv
import Grammatik.Speichermodell.AtomarZeuge

namespace Gabbro.Grammatik

open Speichermodell Zielsatz

variable {D : Deklaration}

section Ziel

variable {P : Programm D} {O : Orakel D} {passes : Nat} {ord : D.Glob → Ordnung}
  {S : SperrInv D} {fs : List D.Fn} {K : Faden → D.Fn → Bool} {Tg : D.Tab ⊕ D.Glob → Prop}
  {lok : D.Tab ⊕ D.Glob → Bool} {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}

/-- **Every machine W reaches has a G-part that GX reaches** (from `schwach_ist_gX`, step by
    step). -/
theorem gx_aus_w (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussSX P S lok Tg f) (hlokK : ∀ c, lok c = true → GetrenntK P K c)
    (hTA : ∀ c, Tg c → AtomarAusgenommen c) (hex : StartExklusiv init) {W : RufMaschineW D}
    (hr : RufErreichbarW P O passes ord (RufStartW (RufStartG P sp init)) W) :
    RufErreichbarGX P O passes Tg (RufStartG P sp init) W.g := by
  induction hr with
  | start => exact .start
  | schritt W W' u hr' hs ih =>
      obtain ⟨σ, M'', wahl, neu, h⟩ := hs
      exact .schritt _ _ _ ih
        (schwach_ist_gX hO hvoll hAbg hWurzel hFuss hlokK hTA hex hr' h).1

end Ziel

/-- **The legs at a machine W with shared atomics `Tg`.** -/
structure ZielAtomarW (P : Programm D) (S : SperrInv D) (O : Orakel D) (passes : Nat)
    (ord : D.Glob → Ordnung) (Tg : D.Tab ⊕ D.Glob → Prop) (M0 : RufMaschineG D)
    (W : RufMaschineW D) : Prop where
  /-- G's part is reached by GX: shared atomic reads answered by the weak memory. -/
  erreicht : RufErreichbarGX P O passes Tg M0 W.g
  -- memory safety of the trace, and lock exclusivity
  speicherSicher : SpurInv W.g
  exklusiv : Exklusiv W.g
  -- the weak memory adds no behaviour outside the shared atomics
  schwach : ∀ (W' : RufMaschineW D) (u : Faden) (σ : Speicher D) (M'' : RufMaschineG D)
      (wahl : D.Tab ⊕ D.Glob → NachrichtW D) (neu : D.Tab ⊕ D.Glob → Nat),
      SchrittW P O passes ord W u W' σ M'' wahl neu →
      RufSchrittGX P O passes Tg W.g u W'.g ∧ ∀ c, ¬ Tg c → TraegerGleich σ W.g.speicher c
  -- contracts where claimed, the invariants and the start legs
  vertrag : VertragAmOrtG P W.g
  sperrInv : SperrInvG S W.g
  invRueck : InvAmOrtG P W.g
  invGrund : Zielsatz.InvAmGrundG P W.g
  startEnde : StartEndeG P W.g
  keinStartGrund : KeinStartGrundG W.g
  keinLogikHalt : KeinLogikHaltG O passes W.g
  -- no deadlock
  keineVerklemmung : (∀ t, ¬ FertigG W.g t → WartetG W.g t) → ∀ t, FertigG W.g t
  keinZyklus : KeinWarteZyklus W.g

/-- **THE LEGS WITH SHARED ATOMICS, OVER MACHINE W.** A program whose footprints admit the
    shared atomics `Tg` unguarded (`FussSX`: every footprint carrier thread-local, guarded, or
    in `Tg`), where `Tg` holds only atomics (`hTA`) that no contract, invariant or lock
    invariant mentions (`hTV`, `hTS`, `hTO`), whose user obligation holds against EVERY answer
    a shared atomic read may give (`KoerperGutSA`, `InvGutSA`, `InvGutGrundA`): every machine
    W reaches -- racing atomics, views, messages -- satisfies `ZielAtomarW`. -/
theorem ziel_atomar_w (P : Programm D) (O : Orakel D) (passes : Nat) (ord : D.Glob → Ordnung)
    (Q : AxEns D) (S : SperrInv D) {fs : List D.Fn} (ls : List D.Lock) (K : Faden → D.Fn → Bool)
    (Tg : D.Tab ⊕ D.Glob → Prop) (lok : D.Tab ⊕ D.Glob → Bool) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hSt : StufenM P) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hls : ∀ L : D.Lock, L ∈ ls)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hTA : ∀ c, Tg c → AtomarAusgenommen c) (hTV : ∀ c, Tg c → VertragsFrei P c)
    (hTS : ∀ c, Tg c → ∀ f Λ, c ∉ stabilS P S lok f Λ)
    (hTO : ∀ c, Tg c → ∀ L, c ∉ S.orte L)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussSX P S lok Tg f) (hlokK : ∀ c, lok c = true → GetrenntK P K c)
    (hK : ∀ f : D.Fn, KoerperGutSA P passes Q S Tg f)
    (hI : ∀ f : D.Fn, InvGutSA P passes Q S Tg f)
    (hIG : ∀ f : D.Fn, InvGutGrundA P passes Q S Tg f) (hStart : StartGut P sp init)
    (hsp : ∀ L, S.inv L sp = true) (hex : StartExklusiv init) (hGrund : StartOhneGrund init)
    (hLeer : ∀ t, D.haelt (init t).1 = []) :
    ∀ W : RufMaschineW D, RufErreichbarW P O passes ord (RufStartW (RufStartG P sp init)) W →
      ZielAtomarW P S O passes ord Tg (RufStartG P sp init) W := by
  intro W hr
  have hX := gx_aus_w hO hvoll hAbg hWurzel hFS hlokK hTA hex hr
  have hA := gx_ga_lauf hTA hX
  have hV := ziel_ort_atomar_voll P O passes Q S K Tg lok sp init hO hRL hQ hlok hS hvoll hAbg
    hWurzel hTA hTV hTS hTO hFragS hFS hlokK hK hI hIG hStart hsp hex hGrund W.g hX
  exact
    { erreicht := hX
      speicherSicher := gaInv_spur hO sp init hA
      exklusiv := gaInv_exklusiv hO sp init hex hA
      schwach := fun W' u σ M'' wahl neu h =>
        schwach_ist_gX hO hvoll hAbg hWurzel hFS hlokK hTA hex hr h
      vertrag := hV.1
      sperrInv := hV.2.1
      invRueck := hV.2.2.2.1
      invGrund := hV.2.2.2.2.1
      startEnde := hV.2.2.2.2.2.1
      keinStartGrund := hV.2.2.2.2.2.2
      keinLogikHalt := hV.2.2.1
      keineVerklemmung := keine_verklemmungGA hO hSt sp init hLeer ls hls hA
      keinZyklus := kein_warteZyklusGA hO hSt sp init hLeer hA }

#print axioms Gabbro.Grammatik.gx_aus_w
#print axioms Gabbro.Grammatik.ziel_atomar_w

end Gabbro.Grammatik
