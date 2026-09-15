/-
  File:      Grammatik/CParser/Bruecke.lean
  Subject:   A2, PART 3: the bridge between the TEXT and the CERTIFICATE.

  The closing theorem's C side is `kProg K.zert` -- the unit the
  correspondence certificate elaborates to. This file says, once and
  generically, what it means for an emitted TEXT to BE that unit:

      A2 s c   :=   parseC s = some (kFuns c)

  and derives from it the equation the theorem needs,
  `cProgC s = kProg c`. A chain program discharges A2 by ONE kernel
  reduction (`CText104.lean`, `CText108.lean`); every theorem that spoke
  about `kProg zert` then speaks about the text.

  Nothing here is about a particular program, and nothing here changes
  `KorrespondenzAllg.lean` (another lane owns that file).
-/
import Grammatik.CParser.CParse
import Grammatik.KorrespondenzAllg
import Grammatik.Schlusssatz

namespace Gabbro.Grammatik.CParser

open Gabbro.Grammatik Parser.UebersetzeAllg Zielsatz

variable {D : Deklaration}

/-- The C functions a certificate elaborates to, as a LIST (the shape
    `parseC` returns): function `n` is row list `n`. -/
def kFuns (c : KCert D) : List CFun :=
  c.map fun k => { params := k.params, locals := k.locals, body := endCS k.rows }

/-- ... and that list IS the unit `kProg` builds. -/
theorem kProg_kFuns (c : KCert D) : kProg c = fun n => (kFuns c)[n]? := by
  funext n
  unfold kProg kFuns
  rw [List.getElem?_map]

/-- **A2 for one program**: the emitted TEXT `s` (its characters) parses,
    in Lean, to the very C unit the certificate `c` elaborates to. A
    proposition, not an assumption: a chain program proves it by kernel
    reduction. -/
def A2 (s : List Char) (c : KCert D) : Prop := parseC s = some (kFuns c)

/-- A2 gives the equation the closing theorem needs: the C unit read from
    the TEXT is the C unit the certificate elaborates to. -/
theorem a2_kProg {s : List Char} {c : KCert D} (h : A2 s c) : cProgC s = kProg c := by
  rw [kProg_kFuns]
  unfold cProgC
  rw [show parseC s = some (kFuns c) from h]
  rfl

/-- **A2 DISCHARGED, the hypothesis swap.** The closing theorem wants its
    binary hypothesis (A1) against `kProg K.zert`, the certificate's
    unit. With A2 proved, the SAME hypothesis may be stated against the
    unit read from the emitted TEXT -- and that is the whole point: A1
    then says "every run of the compiled binary is a run of the C
    semantics OF THE TEXT THE COMPILER WAS GIVEN", with no hand
    transcription between them. -/
theorem a2_hA1 {F : Type} {s : List Char} {c : KCert D} (hA2 : A2 s c)
    {L : CLayout} {orc : DevOrc} {XR : CCallR}
    {bin : F → CSt → List CVal → CSt → Option CVal → Prop} {tief : F → Nat} {fnum : F → Nat}
    (hA1 : ∀ f st vs st' rv, bin f st vs st' rv →
      CallAt L orc XR (cProgC s) (tief f) (fnum f) st vs st' rv) :
    ∀ f st vs st' rv, bin f st vs st' rv →
      CallAt L orc XR (kProg c) (tief f) (fnum f) st vs st' rv := by
  rw [← a2_kProg hA2]
  exact hA1

/-- **THE CLOSING THEOREM WITH A2 DISCHARGED.** Exactly `schlusssatz`
    (Schlusssatz.lean §4) -- every conclusion unchanged -- with ONE
    premise different: `hA1` speaks about the C unit of the emitted TEXT
    `s`, not about the certificate's elaboration. The two are the same
    unit, by `hA2`. (The conclusion is written out rather than
    abbreviated on purpose: if `schlusssatz` ever states something else,
    THIS FILE STOPS COMPILING instead of silently promising the old
    thing.) -/
theorem schlusssatz_text {src : String} (K : Kette src) {s : List Char} (hA2 : A2 s K.zert)
    (O : Orakel (declOf K.u)) (hH : HardwareAnnahmen O K.E.Q)
    (orc : DevOrc) (XR : CCallR) (hXR : XR.Funktional)
    (bin : (declOf K.u).Fn → CSt → List CVal → CSt → Option CVal → Prop)
    (tief : (declOf K.u).Fn → Nat)
    (hA1 : ∀ f st vs st' rv, bin f st vs st' rv →
      CallAt K.EL.lay orc XR (cProgC s) (tief f) (fnNr f) st vs st' rv)
    (sp : Speicher (declOf K.u).mitRuhe)
    (init : Faden → Σ f : (declOf K.u).mitRuhe.Fn,
      Env (declOf K.u).mitRuhe ((declOf K.u).mitRuhe.params f))
    (hA4 : EinFadenStart K.E sp init) :
    uebersetzeAllg src = .ok ⟨K.u, K.E.P, K.fs0⟩ ∧
    (akzeptiert_pruefer.akzeptiert K.E K.fs.1 K.ls.1 K.cs.1 = true ∧
      AkzeptiertSpec K.E.P K.E.S K.fs.1 K.E.ws ∧
      korrOk K.EL fnNr K.zert K.E.P K.fs.1 = true) ∧
    NutzerPflicht K.E ∧
    (∀ (passes n : Nat) (f : (declOf K.u).Fn) (k : KFun (declOf K.u)), K.zert[fnNr f]? = some k →
      ∀ (σ : World (declOf K.u)) (st : CSt) (ρG : Env (declOf K.u) ((declOf K.u).params f))
        (vs : List CVal) (ρ0 : CLok), corrW K.EL σ st → bindParams k.params vs = some ρ0 →
        EnvRel K.EL k.lay ρG ρ0 → (rufAt K.E.P O passes n f σ ρG).istFehler = false →
        (∃ st' rv, CallAt K.EL.lay orc XR (kProg K.zert) n (fnNr f) st vs st' rv) ∧
        ∀ st' rv, CallAt K.EL.lay orc XR (kProg K.zert) n (fnNr f) st vs st' rv →
          RufOut K.EL (rufAt K.E.P O passes n f σ ρG) st' rv) ∧
    (∀ (passes n : Nat) (f : (declOf K.u).Fn) (σ : World (declOf K.u))
        (ρG : Env (declOf K.u) ((declOf K.u).params f)) (e : Hardware (declOf K.u)),
      rufAt K.E.P O passes n f σ ρG ≠ .hardware e) ∧
    (∀ (passes n : Nat) (f : (declOf K.u).Fn) (σ : World (declOf K.u))
        (ρG : Env (declOf K.u) ((declOf K.u).params f)),
      (rufAt K.E.P O passes n f σ ρG).istFehler = true →
        ∃ e : Logik (declOf K.u), rufAt K.E.P O passes n f σ ρG = .logik e) ∧
    (∀ (passes n : Nat) (f : (declOf K.u).Fn) (σ : World (declOf K.u))
        (ρG : Env (declOf K.u) ((declOf K.u).params f)),
      (rufAt K.E.P O passes (n + 1) f σ ρG).istFehler = false →
        ReqAmEintritt K.E.P f σ ρG) ∧
    ((∀ passes n : Nat, RufRu (rufAt K.E.P O passes n) (rufAt K.E.P.mitRuhe O.mitRuhe passes n)) ∧
      (∀ (passes : Nat) (M : RufMaschineG (declOf K.u).mitRuhe),
        RufErreichbarG K.E.P.mitRuhe O.mitRuhe passes (RufStartG K.E.P.mitRuhe sp init) M →
          SpurInv M ∧
          ((VertragAmOrtG K.E.P.mitRuhe M ∧ SperrInvG K.E.S.mitRuhe M ∧
            KeinLogikHaltG O.mitRuhe passes M ∧
            ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
              AnPruefungG M t → ∃ M', RufSchrittG K.E.P.mitRuhe O.mitRuhe passes M t M') ∧
            InvAmOrtG K.E.P.mitRuhe M) ∧ StartEndeG K.E.P.mitRuhe M ∧ KeinStartGrundG M) ∧
      (∀ (passes : Nat) (sp' : Speicher (declOf K.u).mitRuhe)
        (init' : Faden → Σ f : (declOf K.u).mitRuhe.Fn,
          Env (declOf K.u).mitRuhe ((declOf K.u).mitRuhe.params f)),
        Laufzeit K.E sp' init' → ∀ M : RufMaschineG (declOf K.u).mitRuhe,
          RufErreichbarG K.E.P.mitRuhe O.mitRuhe passes (RufStartG K.E.P.mitRuhe sp' init') M →
            Ziel K.E.P.mitRuhe K.E.S.mitRuhe O.mitRuhe passes
              (RufStartG K.E.P.mitRuhe sp' init') M)) ∧
    (∀ (passes : Nat) (f : (declOf K.u).Fn) (k : KFun (declOf K.u)), K.zert[fnNr f]? = some k →
      ∀ (σ : World (declOf K.u)) (st : CSt) (ρG : Env (declOf K.u) ((declOf K.u).params f))
        (vs : List CVal) (ρ0 : CLok), corrW K.EL σ st → bindParams k.params vs = some ρ0 →
        EnvRel K.EL k.lay ρG ρ0 → (rufAt K.E.P O passes (tief f) f σ ρG).istFehler = false →
        ∀ st' rv, bin f st vs st' rv → RufOut K.EL (rufAt K.E.P O passes (tief f) f σ ρG) st' rv) :=
  schlusssatz K O hH orc XR hXR bin tief (a2_hA1 hA2 hA1) sp init hA4

#print axioms Gabbro.Grammatik.CParser.kProg_kFuns
#print axioms Gabbro.Grammatik.CParser.a2_kProg
#print axioms Gabbro.Grammatik.CParser.a2_hA1
#print axioms Gabbro.Grammatik.CParser.schlusssatz_text

end Gabbro.Grammatik.CParser
