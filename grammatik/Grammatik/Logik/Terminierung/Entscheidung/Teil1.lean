module

public import Grammatik.Logik.Terminierung.Rekursion
public import Grammatik.Gen.Abdeckung.Satz.MerkmalZerlegt
public import Grammatik.Zielsatz.Faeden.Verbund.T1
public import Grammatik.Logik.Ruf.Maschine.BudgetMonoton
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

variable {D : Deklaration}

/-! ## 1. The gates read as feature sets -/

section Gate

variable (Z : D.Fn → Bool) (ZS : Nat → Bool) {V : Vertrag D}

mutual

theorem rufeS_mS : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ'),
    rufeS Z ZS true s = mS ⟨Z, ZS, fun _ => true⟩ s
  | _, _, _, _, .ite _ t e => by simp only [rufeS, mS, rufeB_mB t, rufeB_mB e]
  | _, _, _, _, .onOption _ p a => by simp only [rufeS, mS, rufeB_mB p, rufeB_mB a]
  | _, _, _, _, .onTag _ arms => by simp only [rufeS, mS, rufeArms_mArms arms]
  | _, _, _, _, .onWhy _ arms => by simp only [rufeS, mS, rufeGArms_mGArms arms]
  | _, _, _, _, .call .. => rfl
  | _, _, _, _, .callInd .. => rfl
  | _, _, _, _, .callIndElse (n := n) _ _ _ _ _ err => by simp only [rufeS, mS, rufeE_mE err]
  | _, _, _, _, .locks _ _ body => by simp only [rufeS, mS, rufeB_mB body, Bool.true_and]
  | _, _, _, _, .breaking _ body => by simp only [rufeS, mS, rufeB_mB body]
  | _, _, _, _, .traverse _ _ body => by simp only [rufeS, mS, rufeB_mB body]
  | _, _, _, _, .consumeTraverse _ _ _ _ _ _ body => by simp only [rufeS, mS, rufeB_mB body]
  | _, _, _, _, .retry _ _ body ueber => by simp only [rufeS, mS, rufeB_mB body, rufeB_mB ueber]
  | _, _, _, _, .forever _ _ body => by simp only [rufeS, mS, rufeB_mB body, Bool.true_and]
  | _, _, _, _, .assignSlot .. => rfl
  | _, _, _, _, .assignThru .. | _, _, _, _, .assignSlotRef .. => rfl
  | _, _, _, _, .assignGlob .. => rfl
  | _, _, _, _, .putBytes .. => rfl
  | _, _, _, _, .assignVar .. => rfl
  | _, _, _, _, .shift .. => rfl
  | _, _, _, _, .axiomCall .. => rfl
  | _, _, _, _, .axiomCallElse _ _ _ _ _ _ _ _ err => by simp only [rufeS, mS, rufeE_mE err]
  | _, _, _, _, .regWrite .. => rfl
  | _, _, _, _, .transition .. => rfl
  | _, _, _, _, .publish .. => rfl
  | _, _, _, _, .advances .. => rfl
  | _, _, _, _, .retires .. => rfl
  | _, _, _, _, .ret .. => rfl
  | _, _, _, _, .retWhy .. => rfl
  | _, _, _, _, .retScoped .. => rfl
  | _, _, _, _, .retWhyScoped .. => rfl
  | _, _, _, _, .leave _ => rfl
  | _, _, _, _, .next _ => rfl

theorem rufeB_mB : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ'),
    rufeB Z ZS true b = mB ⟨Z, ZS, fun _ => true⟩ b
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons s rest => by simp only [rufeB, mB, rufeS_mS s, rufeB_mB rest]
  | _, _, _, _, .bind _ rest => by simp only [rufeB, mB, rufeB_mB rest]
  | _, _, _, _, .bindCall _ _ _ _ _ rest => by simp only [rufeB, mB, rufeB_mB rest]
  | _, _, _, _, .bindCallInd _ _ _ _ _ rest => by simp only [rufeB, mB, rufeB_mB rest]
  | _, _, _, _, .bindCallIndElse _ _ _ _ _ err rest => by simp only [rufeB, mB, rufeE_mE err, rufeB_mB rest]
  | _, _, _, _, .bindCallElse _ _ _ _ _ err rest => by simp only [rufeB, mB, rufeE_mE err, rufeB_mB rest]
  | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ rest => by simp only [rufeB, mB, rufeB_mB rest]
  | _, _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by simp only [rufeB, mB, rufeE_mE err, rufeB_mB rest]
  | _, _, _, _, .bindAxiomOpt _ _ _ _ _ _ _ rest => by simp only [rufeB, mB, rufeB_mB rest]
  | _, _, _, _, .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => by simp only [rufeB, mB, rufeE_mE err, rufeB_mB rest]
  | _, _, _, _, .regRead _ _ rest => by simp only [rufeB, mB, rufeB_mB rest]
  | _, _, _, _, .regReadElse _ _ _ sonst rest => by simp only [rufeB, mB, rufeE_mE sonst, rufeB_mB rest]
  | _, _, _, _, .awaits _ _ _ _ _ rest => by simp only [rufeB, mB, rufeB_mB rest]
  | _, _, _, _, .exchange _ _ _ _ rest => by simp only [rufeB, mB, rufeB_mB rest]
  | _, _, _, _, .narrow _ _ _ sonst rest => by simp only [rufeB, mB, rufeE_mE sonst, rufeB_mB rest]
  | _, _, _, _, .narrowRequired _ _ _ rest => by simp only [rufeB, mB, rufeB_mB rest]
  | _, _, _, _, .check _ sonst rest => by simp only [rufeB, mB, rufeE_mE sonst, rufeB_mB rest]
  | _, _, _, _, .float _ _ _ _ _ rest => by simp only [rufeB, mB, rufeB_mB rest]
  | _, _, _, _, .floatLit _ _ _ rest => by simp only [rufeB, mB, rufeB_mB rest]
  | _, _, _, _, .floatOf _ _ _ rest => by simp only [rufeB, mB, rufeB_mB rest]
  | _, _, _, _, .floatNarrow _ _ _ sonst rest => by simp only [rufeB, mB, rufeE_mE sonst, rufeB_mB rest]

theorem rufeArms_mArms : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    (arms : Arms D V l Γ Λ Λ' cs), rufeArms Z ZS true arms = mArms ⟨Z, ZS, fun _ => true⟩ arms
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons b rest => by simp only [rufeArms, mArms, rufeB_mB b, rufeArms_mArms rest]

theorem rufeGArms_mGArms : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n), rufeGArms Z ZS true arms = mGArms ⟨Z, ZS, fun _ => true⟩ arms
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons b rest => by simp only [rufeGArms, mGArms, rufeB_mB b, rufeGArms_mGArms rest]

theorem rufeE_mE : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ),
    rufeE Z ZS true e = mE ⟨Z, ZS, fun _ => true⟩ e
  | _, _, _, .ret .. => rfl
  | _, _, _, .retWhy .. => rfl
  | _, _, _, .retScoped .. => rfl
  | _, _, _, .retWhyScoped .. => rfl
  | _, _, _, .leave _ => rfl
  | _, _, _, .next _ => rfl
  | _, _, _, .cons s rest => by simp only [rufeE, mE, rufeS_mS s, rufeE_mE rest]
  | _, _, _, .bind _ rest => by simp only [rufeE, mE, rufeE_mE rest]
  | _, _, _, .bindCall _ _ _ _ _ rest => by simp only [rufeE, mE, rufeE_mE rest]
  | _, _, _, .bindCallElse _ _ _ _ _ err rest => by simp only [rufeE, mE, rufeE_mE err, rufeE_mE rest]
  | _, _, _, .bindAxiom _ _ _ _ _ _ _ rest => by simp only [rufeE, mE, rufeE_mE rest]
  | _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by simp only [rufeE, mE, rufeE_mE err, rufeE_mE rest]
  | _, _, _, .bindAxiomOpt _ _ _ _ _ _ _ rest => by simp only [rufeE, mE, rufeE_mE rest]
  | _, _, _, .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => by simp only [rufeE, mE, rufeE_mE err, rufeE_mE rest]
  | _, _, _, .regRead _ _ rest => by simp only [rufeE, mE, rufeE_mE rest]
  | _, _, _, .regReadElse _ _ _ sonst rest => by simp only [rufeE, mE, rufeE_mE sonst, rufeE_mE rest]
  | _, _, _, .awaits _ _ _ _ _ rest => by simp only [rufeE, mE, rufeE_mE rest]
  | _, _, _, .bindCallInd _ _ _ _ _ rest => by simp only [rufeE, mE, rufeE_mE rest]
  | _, _, _, .bindCallIndElse _ _ _ _ _ err rest => by simp only [rufeE, mE, rufeE_mE err, rufeE_mE rest]
  | _, _, _, .narrow _ _ _ sonst rest => by simp only [rufeE, mE, rufeE_mE sonst, rufeE_mE rest]
  | _, _, _, .narrowRequired _ _ _ rest => by simp only [rufeE, mE, rufeE_mE rest]
  | _, _, _, .exchange _ _ _ _ rest => by simp only [rufeE, mE, rufeE_mE rest]
  | _, _, _, .ite _ t e => by simp only [rufeE, mE, rufeE_mE t, rufeE_mE e, Bool.and_comm]

end

/-- The `forever` gate is idle where the syntax holds no `forever`. -/
theorem befund_und_ewig (a b : Befund D) : (a ++ b).ewig = (a.ewig || b.ewig) := by rfl

mutual

theorem rufeS_ohneEwig : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (eb ie dl : Bool), (befS eb ie dl s).ewig = false → rufeS Z ZS false s = rufeS Z ZS true s
  | _, _, _, _, .ite _ t e, eb, ie, _, h => by
      simp only [befS, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeS, rufeB_ohneEwig t eb ie h.1, rufeB_ohneEwig e eb ie h.2]
  | _, _, _, _, .onOption _ p a, eb, ie, _, h => by
      simp only [befS, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeS, rufeB_ohneEwig p eb ie h.1, rufeB_ohneEwig a eb ie h.2]
  | _, _, _, _, .onTag _ arms, eb, ie, _, h => by
      simp only [befS] at h
      simp only [rufeS, rufeArms_ohneEwig arms eb ie h]
  | _, _, _, _, .onWhy _ arms, eb, ie, _, h => by
      simp only [befS] at h
      simp only [rufeS, rufeGArms_ohneEwig arms eb ie h]
  | _, _, _, _, .call .., _, _, _, _ => rfl
  | _, _, _, _, .callInd .., _, _, _, _ => rfl
  | _, _, _, _, .locks _ _ body, eb, ie, _, h => by
      simp only [befS] at h
      simp only [rufeS, rufeB_ohneEwig body eb ie h]
  | _, _, _, _, .breaking _ body, eb, ie, _, h => by
      simp only [befS] at h
      simp only [rufeS, rufeB_ohneEwig body eb ie h]
  | _, _, _, _, .traverse _ _ body, _, ie, _, h => by
      simp only [befS] at h
      simp only [rufeS, rufeB_ohneEwig body false ie h]
  | _, _, _, _, .consumeTraverse _ _ _ _ _ _ body, _, ie, _, h => by
      simp only [befS] at h
      simp only [rufeS, rufeB_ohneEwig body false ie h]
  | _, _, _, _, .retry _ _ body ueber, eb, ie, _, h => by
      simp only [befS, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeS, rufeB_ohneEwig body false ie h.1, rufeB_ohneEwig ueber eb ie h.2]
  | _, _, _, _, .forever _ _ _, _, _, _, h => by
      simp only [befS, befund_und_ewig, Bool.true_or, Bool.true_eq_false] at h
  | _, _, _, _, .assignSlot .., _, _, _, _ => rfl
  | _, _, _, _, .assignThru .., _, _, _, _ | _, _, _, _, .assignSlotRef .., _, _, _, _ => rfl
  | _, _, _, _, .assignGlob .., _, _, _, _ => rfl
  | _, _, _, _, .putBytes .., _, _, _, _ => rfl
  | _, _, _, _, .assignVar .., _, _, _, _ => rfl
  | _, _, _, _, .shift .., _, _, _, _ => rfl
  | _, _, _, _, .axiomCall .., _, _, _, _ => rfl
  | _, _, _, _, .axiomCallElse _ _ _ _ _ _ _ _ err, eb, ie, h => by
      simp only [befS] at h
      simp only [rufeS, rufeE_ohneEwig err eb ie h]
  | _, _, _, _, .regWrite .., _, _, _, _ => rfl
  | _, _, _, _, .transition .., _, _, _, _ => rfl
  | _, _, _, _, .publish .., _, _, _, _ => rfl
  | _, _, _, _, .advances .., _, _, _, _ => rfl
  | _, _, _, _, .retires .., _, _, _, _ => rfl
  | _, _, _, _, .ret .., _, _, _, _ => rfl
  | _, _, _, _, .retWhy .., _, _, _, _ => rfl
  | _, _, _, _, .retScoped .., _, _, _, _ => rfl
  | _, _, _, _, .retWhyScoped .., _, _, _, _ => rfl
  | _, _, _, _, .leave _, _, _, _, _ => rfl
  | _, _, _, _, .next _, _, _, _, _ => rfl

theorem rufeB_ohneEwig : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ')
    (eb ie : Bool), (befB eb ie b).ewig = false → rufeB Z ZS false b = rufeB Z ZS true b
  | _, _, _, _, .nil, _, _, _ => rfl
  | _, _, _, _, .cons s rest, eb, ie, h => by
      simp only [befB, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeB, rufeS_ohneEwig s eb ie _ h.1, rufeB_ohneEwig rest eb ie h.2]
  | _, _, _, _, .bind _ rest, eb, ie, h => by
      simp only [befB] at h
      simp only [rufeB, rufeB_ohneEwig rest eb ie h]
  | _, _, _, _, .bindCall _ _ _ _ _ rest, eb, ie, h => by
      simp only [befB, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeB, rufeB_ohneEwig rest eb ie h.2]
  | _, _, _, _, .bindCallInd _ _ _ _ _ rest, eb, ie, h => by
      simp only [befB, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeB, rufeB_ohneEwig rest eb ie h.2]
  | _, _, _, _, .bindCallIndElse _ _ _ _ _ err rest, eb, ie, h => by
      simp only [befB, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeB, rufeE_ohneEwig err eb ie h.1.2, rufeB_ohneEwig rest eb ie h.2]
  | _, _, _, _, .bindCallElse _ _ _ _ _ err rest, eb, ie, h => by
      simp only [befB, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeB, rufeE_ohneEwig err eb ie h.1.2, rufeB_ohneEwig rest eb ie h.2]
  | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ rest, eb, ie, h => by
      simp only [befB] at h
      simp only [rufeB, rufeB_ohneEwig rest eb ie h]
  | _, _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest, eb, ie, h => by
      simp only [befB, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeB, rufeE_ohneEwig err eb ie h.1, rufeB_ohneEwig rest eb ie h.2]
  | _, _, _, _, .bindAxiomOpt _ _ _ _ _ _ _ rest, eb, ie, h => by
      simp only [befB] at h
      simp only [rufeB, rufeB_ohneEwig rest eb ie h]
  | _, _, _, _, .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest, eb, ie, h => by
      simp only [befB, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeB, rufeE_ohneEwig err eb ie h.1, rufeB_ohneEwig rest eb ie h.2]
  | _, _, _, _, .regRead _ _ rest, eb, ie, h => by
      simp only [befB] at h
      simp only [rufeB, rufeB_ohneEwig rest eb ie h]
  | _, _, _, _, .regReadElse _ _ _ sonst rest, eb, ie, h => by
      simp only [befB, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeB, rufeE_ohneEwig sonst eb ie h.1, rufeB_ohneEwig rest eb ie h.2]
  | _, _, _, _, .awaits _ _ _ _ _ rest, eb, ie, h => by
      simp only [befB] at h
      simp only [rufeB, rufeB_ohneEwig rest eb ie h]
  | _, _, _, _, .exchange _ _ _ _ rest, eb, ie, h => by
      simp only [befB] at h
      simp only [rufeB, rufeB_ohneEwig rest eb ie h]
  | _, _, _, _, .narrow _ _ _ sonst rest, eb, ie, h => by
      simp only [befB, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeB, rufeE_ohneEwig sonst eb ie h.1, rufeB_ohneEwig rest eb ie h.2]
  | _, _, _, _, .narrowRequired _ _ _ rest, eb, ie, h => by
      simp only [befB] at h
      simp only [rufeB, rufeB_ohneEwig rest eb ie h]
  | _, _, _, _, .check _ sonst rest, eb, ie, h => by
      simp only [befB, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeB, rufeE_ohneEwig sonst eb ie h.1, rufeB_ohneEwig rest eb ie h.2]
  | _, _, _, _, .float _ _ _ _ _ rest, eb, ie, h => by
      simp only [befB] at h
      simp only [rufeB, rufeB_ohneEwig rest eb ie h]
  | _, _, _, _, .floatLit _ _ _ rest, eb, ie, h => by
      simp only [befB] at h
      simp only [rufeB, rufeB_ohneEwig rest eb ie h]
  | _, _, _, _, .floatOf _ _ _ rest, eb, ie, h => by
      simp only [befB] at h
      simp only [rufeB, rufeB_ohneEwig rest eb ie h]
  | _, _, _, _, .floatNarrow _ _ _ sonst rest, eb, ie, h => by
      simp only [befB, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeB, rufeE_ohneEwig sonst eb ie h.1, rufeB_ohneEwig rest eb ie h.2]

theorem rufeArms_ohneEwig : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    (arms : Arms D V l Γ Λ Λ' cs) (eb ie : Bool), (befArms eb ie arms).ewig = false →
      rufeArms Z ZS false arms = rufeArms Z ZS true arms
  | _, _, _, _, _, .nil, _, _, _ => rfl
  | _, _, _, _, _, .cons b rest, eb, ie, h => by
      simp only [befArms, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeArms, rufeB_ohneEwig b eb ie h.1, rufeArms_ohneEwig rest eb ie h.2]

theorem rufeGArms_ohneEwig : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n) (eb ie : Bool), (befGArms eb ie arms).ewig = false →
      rufeGArms Z ZS false arms = rufeGArms Z ZS true arms
  | _, _, _, _, _, .nil, _, _, _ => rfl
  | _, _, _, _, _, .cons b rest, eb, ie, h => by
      simp only [befGArms, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeGArms, rufeB_ohneEwig b eb ie h.1, rufeGArms_ohneEwig rest eb ie h.2]

theorem rufeE_ohneEwig : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ)
    (eb ie : Bool), (befE eb ie e).ewig = false → rufeE Z ZS false e = rufeE Z ZS true e
  | _, _, _, .ret .., _, _, _ => rfl
  | _, _, _, .retWhy .., _, _, _ => rfl
  | _, _, _, .retScoped .., _, _, _ => rfl
  | _, _, _, .retWhyScoped .., _, _, _ => rfl
  | _, _, _, .leave _, _, _, _ => rfl
  | _, _, _, .next _, _, _, _ => rfl
  | _, _, _, .cons s rest, eb, ie, h => by
      simp only [befE, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeE, rufeS_ohneEwig s eb ie _ h.1, rufeE_ohneEwig rest eb ie h.2]
  | _, _, _, .bind _ rest, eb, ie, h => by
      simp only [befE] at h
      simp only [rufeE, rufeE_ohneEwig rest eb ie h]
  | _, _, _, .bindCall _ _ _ _ _ rest, eb, ie, h => by
      simp only [befE, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeE, rufeE_ohneEwig rest eb ie h.2]
  | _, _, _, .bindCallElse _ _ _ _ _ err rest, eb, ie, h => by
      simp only [befE, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeE, rufeE_ohneEwig err eb ie h.1.2, rufeE_ohneEwig rest eb ie h.2]
  | _, _, _, .bindAxiom _ _ _ _ _ _ _ rest, eb, ie, h => by
      simp only [befE] at h
      simp only [rufeE, rufeE_ohneEwig rest eb ie h]
  | _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest, eb, ie, h => by
      simp only [befE, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeE, rufeE_ohneEwig err eb ie h.1, rufeE_ohneEwig rest eb ie h.2]
  | _, _, _, .bindAxiomOpt _ _ _ _ _ _ _ rest, eb, ie, h => by
      simp only [befE] at h
      simp only [rufeE, rufeE_ohneEwig rest eb ie h]
  | _, _, _, .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest, eb, ie, h => by
      simp only [befE, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeE, rufeE_ohneEwig err eb ie h.1, rufeE_ohneEwig rest eb ie h.2]
  | _, _, _, .regRead _ _ rest, eb, ie, h => by
      simp only [befE] at h
      simp only [rufeE, rufeE_ohneEwig rest eb ie h]
  | _, _, _, .regReadElse _ _ _ sonst rest, eb, ie, h => by
      simp only [befE, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeE, rufeE_ohneEwig sonst eb ie h.1, rufeE_ohneEwig rest eb ie h.2]
  | _, _, _, .awaits _ _ _ _ _ rest, eb, ie, h => by
      simp only [befE] at h
      simp only [rufeE, rufeE_ohneEwig rest eb ie h]
  | _, _, _, .bindCallInd _ _ _ _ _ rest, eb, ie, h => by
      simp only [befE, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeE, rufeE_ohneEwig rest eb ie h.2]
  | _, _, _, .narrow _ _ _ sonst rest, eb, ie, h => by
      simp only [befE, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeE, rufeE_ohneEwig sonst eb ie h.1, rufeE_ohneEwig rest eb ie h.2]
  | _, _, _, .narrowRequired _ _ _ rest, eb, ie, h => by
      simp only [befE] at h
      simp only [rufeE, rufeE_ohneEwig rest eb ie h]
  | _, _, _, .exchange _ _ _ _ rest, eb, ie, h => by
      simp only [befE] at h
      simp only [rufeE, rufeE_ohneEwig rest eb ie h]
  | _, _, _, .ite _ t e, eb, ie, h => by
      simp only [befE, befund_und_ewig, Bool.or_eq_false_iff] at h
      simp only [rufeE, rufeE_ohneEwig e eb ie h.1, rufeE_ohneEwig t eb ie h.2]

end

end Gate

end Gabbro.Grammatik
