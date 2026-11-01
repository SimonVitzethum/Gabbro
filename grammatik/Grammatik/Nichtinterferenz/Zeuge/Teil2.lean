module

public import Grammatik.Nichtinterferenz.Fluss
public import Grammatik.Nichtinterferenz.Zeuge.Teil1

@[expose] public section

namespace Gabbro.Grammatik
namespace NIZeuge

theorem lk_s1 (sp : Speicher nD) : RufSchrittG nP nO 0 (lkM0 sp) 0 (lkM1 sp) :=
  RufSchrittG.endeEntf (lkM0 sp) 0 false [] [] [] lkS lkRet .nil rfl rfl

/-- The read world of the condition. -/
def lkσ₁ (sp : Speicher nD) : World nD := ((lkM1 sp).weltVon 0).lese [] lkC.orte

/-- Run 1 (`tabA[0] = 0`): the true branch is taken. -/
def lkM2w (sp : Speicher nD) : RufMaschineG nD :=
  ⟨(lkM1 sp).speicher,
   rufUpdateG (lkM1 sp).faeden 0
     ⟨((lkM1 sp).faeden 0).stapel,
      ⟨((lkM1 sp).faeden 0).kopf.f, ((lkM1 sp).faeden 0).kopf.rho, ((lkM1 sp).faeden 0).kopf.s0,
       ⟨false, [], [], .nil, .dann (.cons lkW .nil) (.dann .nil (.ende lkRet))⟩⟩,
      (lkσ₁ sp).spur, ((lkM1 sp).faeden 0).log⟩,
   (lkM1 sp).lauf ++ rufEigenG 0 (lkσ₁ sp).spur, (lkM1 sp).start⟩

theorem lk_s2w : RufSchrittG nP nO 0 (lkM1 sp0) 0 (lkM2w sp0) :=
  RufSchrittG.dannIteWahr (lkM1 sp0) 0 false [] [] [] [] lkC (.cons lkW .nil) .nil .nil
    (.ende lkRet) .nil rfl (lkσ₁ sp0) rfl rfl (lkσ₁ sp0).spur rfl (fun _ h => nomatch h)

/-- The world after the write `tabB[0] = 1`. -/
def lkσ' : World nD := blattWelt lkW ((lkM2w sp0).weltVon 0) .nil

def lkM3w : RufMaschineG nD :=
  ⟨lkσ'.speicher,
   rufUpdateG (lkM2w sp0).faeden 0
     ⟨((lkM2w sp0).faeden 0).stapel,
      ⟨((lkM2w sp0).faeden 0).kopf.f, ((lkM2w sp0).faeden 0).kopf.rho,
       ((lkM2w sp0).faeden 0).kopf.s0,
       ⟨false, [], [], .nil, .dann .nil (.dann .nil (.ende lkRet))⟩⟩,
      lkσ'.spur, ((lkM2w sp0).faeden 0).log⟩,
   (lkM2w sp0).lauf ++ rufEigenG 0 [Ereignis.zugriff NTab.tabB true [] []], (lkM2w sp0).start⟩

theorem lk_s3w : RufSchrittG nP nO 0 (lkM2w sp0) 0 lkM3w :=
  RufSchrittG.dannBlatt (lkM2w sp0) 0 false [] [] [] [] lkW .nil (.dann .nil (.ende lkRet)) .nil
    rfl rfl (fun _ h => nomatch h) lkσ' .nil [Ereignis.zugriff NTab.tabB true [] []] rfl rfl
    (fun L => nomatch L)

/-- Run 2 (`tabA[0] = 1`): the (empty) false branch is taken. -/
def lkM2f (sp : Speicher nD) : RufMaschineG nD :=
  ⟨(lkM1 sp).speicher,
   rufUpdateG (lkM1 sp).faeden 0
     ⟨((lkM1 sp).faeden 0).stapel,
      ⟨((lkM1 sp).faeden 0).kopf.f, ((lkM1 sp).faeden 0).kopf.rho, ((lkM1 sp).faeden 0).kopf.s0,
       ⟨false, [], [], .nil, .dann .nil (.dann .nil (.ende lkRet))⟩⟩,
      (lkσ₁ sp).spur, ((lkM1 sp).faeden 0).log⟩,
   (lkM1 sp).lauf ++ rufEigenG 0 (lkσ₁ sp).spur, (lkM1 sp).start⟩

theorem lk_s2f : RufSchrittG nP nO 0 (lkM1 sp1) 0 (lkM2f sp1) :=
  RufSchrittG.dannIteFalsch (lkM1 sp1) 0 false [] [] [] [] lkC (.cons lkW .nil) .nil .nil
    (.ende lkRet) .nil rfl (lkσ₁ sp1) rfl rfl (lkσ₁ sp1).spur rfl (fun _ h => nomatch h)

def lkM3f : RufMaschineG nD :=
  ⟨(lkM2f sp1).speicher,
   rufUpdateG (lkM2f sp1).faeden 0
     ⟨((lkM2f sp1).faeden 0).stapel,
      ⟨((lkM2f sp1).faeden 0).kopf.f, ((lkM2f sp1).faeden 0).kopf.rho,
       ((lkM2f sp1).faeden 0).kopf.s0,
       ⟨false, [], [], .nil, .dann .nil (.ende lkRet)⟩⟩,
      ((lkM2f sp1).faeden 0).spur, ((lkM2f sp1).faeden 0).log⟩,
   (lkM2f sp1).lauf, (lkM2f sp1).start⟩

theorem lk_s3f : RufSchrittG nP nO 0 (lkM2f sp1) 0 lkM3f :=
  RufSchrittG.dannLeer (lkM2f sp1) 0 false [] [] (.dann .nil (.ende lkRet)) .nil rfl

def lkRun1 : Nat → RufMaschineG nD
  | 0 => lkM0 sp0
  | 1 => lkM1 sp0
  | 2 => lkM2w sp0
  | _ => lkM3w

def lkRun2 : Nat → RufMaschineG nD
  | 0 => lkM0 sp1
  | 1 => lkM1 sp1
  | 2 => lkM2f sp1
  | _ => lkM3f

theorem lkRun1_lauf : LaufG nP nO 0 (RufStartG nP sp0 init3) lkRun1 (fun _ => 0) 3 := by
  refine ⟨rfl, fun k hk => ?_⟩
  match k, hk with
  | 0, _ => exact lk_s1 sp0
  | 1, _ => exact lk_s2w
  | 2, _ => exact lk_s3w

theorem lkRun2_lauf : LaufG nP nO 0 (RufStartG nP sp1 init3) lkRun2 (fun _ => 0) 3 := by
  refine ⟨rfl, fun k hk => ?_⟩
  match k, hk with
  | 0, _ => exact lk_s1 sp1
  | 1, _ => exact lk_s2f
  | 2, _ => exact lk_s3f

theorem sp01_B : SpeicherGleich (sichtbarC nπ (etiketten (L3 .A) fdom3) NDom.B) sp0 sp1 := by
  intro c hc
  cases c with
  | inl t =>
      cases t with
      | tabA => exact absurd hc (by decide)
      | tabB => rfl
  | inr g => rfl

/-- **The leak violates noninterference (`n3_verletzt`).** Same program,
    same oracle, same schedule (thread 0 three times), start memories that
    agree on every carrier tenant B may see (they differ only in `tabA`):
    after three steps B sees `tabB[0] = 1` in one run and `0` in the other.
    Together with `n3_abgelehnt`: the premise `flussB` of
    `nichtinterferenz` is not decoration -- without it the conclusion
    fails. -/
theorem n3_verletzt :
    SpeicherGleich (sichtbarC nπ (etiketten (L3 .A) fdom3) NDom.B) sp0 sp1 ∧
    LaufG nP nO 0 (RufStartG nP sp0 init3) lkRun1 (fun _ => 0) 3 ∧
    LaufG nP nO 0 (RufStartG nP sp1 init3) lkRun2 (fun _ => 0) 3 ∧
    beob nπ (etiketten (L3 .A) fdom3) NDom.B (lkRun1 3) ≠
      beob nπ (etiketten (L3 .A) fdom3) NDom.B (lkRun2 3) ∧
    (∀ d, flussB nπ nP nFs nCs (L3 d) = false) := by
  refine ⟨sp01_B, lkRun1_lauf, lkRun2_lauf, fun h => ?_, n3_abgelehnt⟩
  have hg := ((beob_gleich_iff _ _ _ _ _).mp h).1 (.inl NTab.tabB) rfl
  have h1 : (lkRun1 3).speicher.slots NTab.tabB 0 () = (lkRun2 3).speicher.slots NTab.tabB 0 () :=
    congrFun (congrFun hg 0) ()
  have h2 := congrArg Zahl.n h1
  exact absurd h2 (by decide)

#print axioms Gabbro.Grammatik.NIZeuge.n1_ni
#print axioms Gabbro.Grammatik.NIZeuge.n1_zeuge
#print axioms Gabbro.Grammatik.NIZeuge.n2_abgelehnt
#print axioms Gabbro.Grammatik.NIZeuge.n3_verletzt

end NIZeuge

end Gabbro.Grammatik
