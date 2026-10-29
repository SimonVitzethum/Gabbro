/- Nonempty witnesses for quantified expressions and bounded optional-index chains. -/
import Stage0.Senke.Bild
import Stage0.Senke.Welt.Anordnung

namespace Gabbro.Stage0.Senke.QuantProbe
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR

set_option maxRecDepth 100000

def u : UProg := {
  tabs := [{name := "Links", count := 4, cols := [("link", (0, 1))], opts := [("link", 0)]}]
  locks := []
  fns := [{name := "main", params := [], kinds := [], res := some (0, 100), held := [], puts := ["Links"], gives := [], body := [], ret := .val (.lit 0)}]
}
abbrev D := declOf u
abbrev tab : D.Tab := ⟨0, by decide⟩
abbrev field : D.Feld tab := ⟨0, by decide⟩
abbrev entry : D.Fn := ⟨0, by decide⟩

theorem access : darf D tab [] := by intro w hw; change w ∈ [] at hw; cases hw

def index (k : Nat) (hk : k < 4) : Expr D [] [] (.index 4) :=
  .widen (by omega) (by omega) (.lit k)

def reach (a b : Nat) (ha : a < 4) (hb : b < 4) : Expr D [] [] .bool :=
  .reaches tab field rfl (index a ha) (index b hb) access

/-- Every binder occurs in its body; the inner binder also reads the outer one. -/
def quantifiers : Expr D [] [] .bool :=
  .and (.forallSlots tab (.lt (.var .here) (.lit 4)) access)
    (.and (.not (.forallSlots tab (.eq (.var .here) (.lit 2)) access))
      (.and (.existsSlots tab (.eq (.var .here) (.lit 2)) access)
        (.and (.not (.existsSlots tab (.eq (.var .here) (.lit 4)) access))
          (.forallSlots tab (.existsSlots tab (.eq (.var .here) (.var (.there .here))) access) access))))

def checks : Expr D [] [] .bool :=
  .and quantifiers (.and (reach 0 2 (by decide) (by decide))
    (.and (reach 2 2 (by decide) (by decide))
      (.and (.not (reach 2 0 (by decide) (by decide)))
        (.and (.not (reach 3 0 (by decide) (by decide))) (reach 0 1 (by decide) (by decide))))))

def world (next : Int → Option (Zahl 0 3)) : World D where
  slots t k f := by
    obtain ⟨t, ht⟩ := t
    have hz : t = 0 := by change t < 1 at ht; omega
    subst t
    obtain ⟨f, hf⟩ := f
    have hz : f = 0 := by change f < 1 at hf; omega
    subst f
    exact next k
  globs g := Fin.elim0 g
  spur := []

def initial : World D := world (fun _ => none)

/-- 0 -> 1 -> 2 -> None; 3 -> 3 is a cycle that does not reach 0. -/
def linked : World D := world (fun k => if k = 0 then some ⟨1, by decide, by decide⟩
    else if k = 1 then some ⟨2, by decide, by decide⟩
    else if k = 3 then some ⟨3, by decide, by decide⟩ else none)

theorem quantifiers_zeuge : wahr? (eval initial quantifiers initial .nil) = true := by decide +kernel

theorem reaches_zeuge : wahr? (eval linked checks linked .nil) = true := by decide +kernel

def put (a b : Nat) (ha : a < 4) (hb : b < 4) : Stmt D (vertragVon D entry) false [] [] [] :=
  .assignSlot tab field (index a ha) (.some (index b hb)) (by decide) access

def body : Endblock D (vertragVon D entry) false [] [] :=
  .cons (put 0 1 (by decide) (by decide))
    (.cons (put 1 2 (by decide) (by decide))
      (.cons (put 3 3 (by decide) (by decide))
        (.cons (.assignSlot tab field (index 2 (by decide)) (.none 4) (by decide) access)
          (.ret (.val (.wenn checks (.widen (by decide) (by decide) (.lit 83))
            (.widen (by decide) (by decide) (.lit 0)))) (.refl [])))))

def program : Programm D where
  invariante _ := .tru
  requires _ := .tru
  ensures _ := .tru
  rumpf f := by
    obtain ⟨f, hf⟩ := f
    have hz : f = 0 := by change f < 1 at hf; omega
    subst f
    exact body

def image : Except String (List Runner.B) := do
  let b ← bild program (layU u (fun _ => none)) [entry] Fin.val (fun _ => "main") entry [] 1024
  pure b.bytes

theorem quant_image_zeuge : image.isOk = true := by decide +kernel

/-- Empty domains do not demand body code; counts and code ranges are checked before expansion. -/
theorem quant_refused_zeuge :
    quantL true 3 7 0 none = some ([ci 1 7 1 0], 8) ∧
    quantL false 3 7 (-1) none = some ([ci 1 7 0 0], 8) ∧
    quantL true 3 7 (2 ^ 31) (some ([], 11)) = none ∧
    quantL true 3 7 (2 ^ 29) (some ([], 11)) = none := by
  decide +kernel

/-- A column outside the instruction's signed immediate range is refused. -/
theorem reaches_refused_zeuge :
    let bad : Lay D := { layU u (fun _ => none) 65536 with col := fun _ _ => 2 ^ 31 }
    lowE bad (reach 0 2 (by decide) (by decide)) 3 = none := by
  decide +kernel

end Gabbro.Stage0.Senke.QuantProbe
