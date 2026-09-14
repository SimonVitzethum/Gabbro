/-
  File:      Grammatik/ZielOrtStart.lean
  Subject:   WHAT A START FUNCTION OWES AT ITS END (SATZKARTE §15.6, §16.2).

  Machine G logs a return only when a frame POPS (`rueck g rho v s0 s1`),
  and a thread's start frame has no caller: it never pops. So `InvAmOrtG`
  (every logged return meets its owed invariants) and the `ensures` half of
  `VertragAmOrtG` said nothing about a start function -- an invariant owed
  at the return of a thread's start function was never checked.

  **The decision.** The completion of a start function IS a machine state:
  the thread's stack is empty and its head stands at a `return` (one of the
  three shapes a pop would fire on: `ret`, `ret` before the rest of an end
  block, `ret` before the rest of a block). No rule of G applies there (the
  returns need a caller, `kein_schritt_ruhig` for the bare shape); the
  thread is finished and stays so. The statement is therefore a property of
  every reachable machine, not of a log entry, and it needs no change of G:

  * `StartEndeG P M`: for every thread whose stack is empty and whose head
    stands at a `return e`, the start function's `ensures` AND every
    invariant it owes hold at the world that return reads
    (`(M.weltVon t).lese Λ e.orte`, exactly the world a pop would log), with
    the value `e` evaluates to there.

  Because it holds on EVERY reachable machine, it holds at the moment the
  thread finishes and at every later moment: the carriers read are stable
  for the finished frame (signature-guarded -- the finished thread holds
  those locks for good --, protected by a lock the frame names, or local),
  and the replay invariant keeps them. A start function that never returns
  owes nothing here (the premise never fires); no `never`/`diverges`
  annotation is needed. The obligation is the existing one: `KoerperGutS`
  (ensures) and `InvGutS` (owed invariants) of the start function, the same
  per-function sequential triples every function owes.

  `ziel_ort_ende` (generic in the local carriers) and
  `ziel_ort_mehrfaden_ende` (thread-local carriers): the flagship's
  conclusion AND `StartEndeG`.
-/
import Grammatik.ZielOrtMehrfaden

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The predicate -/

/-- The residue stands at a `return e` a pop would fire on: `ret` as the
    end block, `ret` before the rest of an end block, or `ret` before the
    rest of a block. -/
def RetKopf {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : ErgExpr D Γ Λ V.erg) (r : GRest D V l Γ Λ) : Prop :=
  ∃ hperm : Λ.Perm V.ende,
    r = .ende (.ret e hperm) ∨ (∃ rest, r = .ende (.cons (.ret e hperm) rest)) ∨
    (∃ (Λ'' : List (Res D)) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ''),
      r = .dann (.cons (.ret e hperm) rest) k)

/-- **The start function's completion**: at every thread whose stack is
    empty and whose head stands at `return e`, the start function's
    `ensures` and every invariant it owes hold at the world the return
    reads, with the returned value. -/
def StartEndeG (P : Programm D) (M : RufMaschineG D) : Prop :=
  ∀ (t : Faden), (M.faeden t).stapel = [] →
    ∀ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ)
      (r : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ)
      (e : ErgExpr D Γ Λ (vertragVon D (M.faeden t).kopf.f).erg),
      (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, r⟩ → RetKopf e r →
      EnsAmRueck P (M.faeden t).kopf.f (M.faeden t).kopf.s0 ((M.weltVon t).lese Λ e.orte)
          (M.faeden t).kopf.rho (evalErg ((M.weltVon t).lese Λ e.orte) e
            ((M.weltVon t).lese Λ e.orte) ρ) ∧
        InvAmRueck P (M.faeden t).kopf.f ((M.weltVon t).lese Λ e.orte)

/-! ## 2. From the replay -/

section Ende

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool}

/-- **A replayed head at a `return` meets `ensures` and its owed
    invariants at the machine world** -- whether or not a caller waits. -/
theorem kopfS_ret (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f) (hI : ∀ f, InvGutS P passes Q S f)
    (hFS : ∀ f, FussS P S lok f) {G : RufRahmenG D} {W : World D}
    (hG : KopfS P O passes Q S lok G W) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D G.f) l Γ Λ} (hr : G.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (e : ErgExpr D Γ Λ (vertragVon D G.f).erg) (hk : RetKopf e r) :
    EnsAmRueck P G.f G.s0 (W.lese Λ e.orte) G.rho (evalErg (W.lese Λ e.orte) e (W.lese Λ e.orte) ρ) ∧
      InvAmRueck P G.f (W.lese Λ e.orte) := by
  obtain ⟨hperm, h | ⟨rest, h⟩ | ⟨Λ'', rest, k, h⟩⟩ := hk <;> subst h
  · have hok := kopfS_okS hG hr
    exact ⟨popS_ens hO hRL hQ hS hsp hK hG hr e (erg_stabil (hFS _) e hok.2)
        (ens_stabil (hFS _) hperm) (fun O' R U σ => semH_rueck S O' U passes R e hperm σ ρ),
      popS_inv hO hRL hQ hS hsp hI hG hr e (fun i hi hs => inv_stabil (hFS _) hperm hi hs)
        (fun O' R U σ => semH_rueck S O' U passes R e hperm σ ρ)⟩
  · have hok := okS_ende_cons (kopfS_okS hG hr)
    exact ⟨popS_ens hO hRL hQ hS hsp hK hG hr e (erg_stabil (hFS _) e hok.2.1)
        (ens_stabil (hFS _) hperm) (fun O' R U σ => semH_rueckCons S O' U passes R e hperm rest σ ρ),
      popS_inv hO hRL hQ hS hsp hI hG hr e (fun i hi hs => inv_stabil (hFS _) hperm hi hs)
        (fun O' R U σ => semH_rueckCons S O' U passes R e hperm rest σ ρ)⟩
  · have hok := okS_dann_cons (kopfS_okS hG hr)
    exact ⟨popS_ens hO hRL hQ hS hsp hK hG hr e (erg_stabil (hFS _) e hok.2.1)
        (ens_stabil (hFS _) hperm) (fun O' R U σ => semH_dannRet S O' U passes R e hperm rest k σ ρ),
      popS_inv hO hRL hQ hS hsp hI hG hr e (fun i hi hs => inv_stabil (hFS _) hperm hi hs)
        (fun O' R U σ => semH_dannRet S O' U passes R e hperm rest k σ ρ)⟩

end Ende

/-! ## 3. The theorems -/

/-- **The flagship with the start functions' completion, generic in the
    local carriers.** The conclusion of `ziel_ort_sperre_invL` AND
    `StartEndeG`: at every finished thread (empty stack, head at a
    `return`) the start function's `ensures` and owed invariants hold. -/
theorem ziel_ort_ende (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (lok : D.Tab ⊕ D.Glob → Bool) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussS P S lok f) (hLok : LokOk P O passes lok sp init)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hI : ∀ f : D.Fn, InvGutS P passes Q S f) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      ((VertragAmOrtG P M ∧ SperrInvG S M ∧ KeinLogikHaltG O passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M') ∧
      InvAmOrtG P M) ∧ StartEndeG P M := by
  intro M hr
  refine ⟨ziel_ort_sperre_invL P O passes Q S lok sp init e0 hO hRL hQ hlok hS hFragS hFS hLok hK
    hStart hSstart hex hI M hr, ?_⟩
  have hZ := (zielInvS_erreichbarL P O passes Q S lok sp init e0 hO hRL hQ hlok hS hFragS hFS
    hLok hK hStart hSstart hex M hr).1
  intro t _ l Γ Λ ρ r e hr' hk
  exact kopfS_ret hO hRL hQ hS hSstart hK hI hFS (hZ.1 t).1 hr' e hk

/-- **THE FLAGSHIP (2026-09-14): several active threads with thread-local
    carriers, lock invariants, table invariants, and the start functions'
    completion.** The premises of `ziel_ort_mehrfaden`; the conclusion of
    `ziel_ort_mehrfaden` AND `StartEndeG`. -/
theorem ziel_ort_mehrfaden_ende (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (K : Faden → D.Fn → Bool)
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussS P S (lokK P K) f)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hI : ∀ f : D.Fn, InvGutS P passes Q S f) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      ((VertragAmOrtG P M ∧ SperrInvG S M ∧ KeinLogikHaltG O passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M') ∧
      InvAmOrtG P M) ∧ StartEndeG P M :=
  ziel_ort_ende P O passes Q S (lokK P K) sp init e0 hO hRL hQ hlok hS
    (programmImFragmentS_ok P S hvoll hFrag hFuss) hFuss
    (lokOk_mehr hO hvoll sp init K hAbg hWurzel) hK hStart hSstart hex hI

/-- **`ziel_ort_sperre_inv` with the start functions' completion** (the
    footprint check of the flagship, `fussSperreB`). -/
theorem ziel_ort_sperre_ende (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussSperreB P S fs = true)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hI : ∀ f : D.Fn, InvGutS P passes Q S f) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      ((VertragAmOrtG P M ∧ SperrInvG S M ∧ KeinLogikHaltG O passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M') ∧
      InvAmOrtG P M) ∧ StartEndeG P M :=
  have hFS : ∀ f, FussS P S (freiB fs) f := fussSperreB_ok hvoll hFuss
  ziel_ort_ende P O passes Q S (freiB fs) sp init e0 hO hRL hQ hlok hS
    (programmImFragmentS_ok P S hvoll hFrag hFS) hFS (lokOk_frei hO hvoll sp init) hK hStart
    hSstart hex hI

#print axioms Gabbro.Grammatik.kopfS_ret
#print axioms Gabbro.Grammatik.ziel_ort_ende
#print axioms Gabbro.Grammatik.ziel_ort_mehrfaden_ende
#print axioms Gabbro.Grammatik.ziel_ort_sperre_ende

end Gabbro.Grammatik
