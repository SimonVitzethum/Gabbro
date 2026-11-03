module
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil1
@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.Uebersetze

/-- `tabNr` at a live number. -/
theorem tabNr_some (u : UProg) (num : Nat) (h : num < u.tabs.length) :
    (declOf u).tabNr num = some (⟨num, h⟩ : Fin u.tabs.length) := by
  show (if h' : num < u.tabs.length then
    (some ⟨num, h'⟩ : Option (Fin u.tabs.length)) else none) = _
  rw [dif_pos h]

/-- Resolve the intended table in its actual registered space. The certificate is checked
    against the same capTab used by G; neither a missing space nor a mismatched one is invented. -/
def checkedTableCap (u : UProg) (space num : Nat) (h : num < u.tabs.length) :
    Except String (PLift ((declOf u).capTab space num = some (⟨num, h⟩ : Fin u.tabs.length))) :=
  if resolved : (declOf u).capTab space num = some (⟨num, h⟩ : Fin u.tabs.length) then .ok ⟨resolved⟩
  else .error "pointer table space is not registered"

/-- Every returned certificate retains the table's actual space and its registration bound. -/
theorem checkedTableCap_registered (u : UProg) (space num : Nat) (h : num < u.tabs.length)
    (certificate : PLift ((declOf u).capTab space num = some (⟨num, h⟩ : Fin u.tabs.length))) :
    space = (tabAt u ⟨num, h⟩).space ∧ space < u.spaces.length :=
  (Deklaration.capTab_sound certificate.down).2

/-- All registered spaces are admitted, including nonzero ones. This transports the actual
    table identity and registration facts, rather than assuming a distinguished normal space. -/
theorem checkedTableCap_complete (u : UProg) (space num : Nat) (h : num < u.tabs.length)
    (same : space = (tabAt u ⟨num, h⟩).space) (registered : space < u.spaces.length) :
    ∃ certificate, checkedTableCap u space num h = .ok certificate := by
  have resolved : (declOf u).capTab space num = some (⟨num, h⟩ : Fin u.tabs.length) :=
    Deklaration.capTab_of (tabNr_some u num h) same registered
  exact ⟨⟨resolved⟩, by simp only [checkedTableCap, resolved, ↓reduceDIte]⟩

private def customSpaceFixture : UProg :=
  { tabs := [{name := "T", count := 1, cols := [("value", (0, 255))], space := 1}],
    locks := [], fns := [], spaces := ["normal", "custom"] }

/-- A genuine registered nonzero space jointly satisfies the generic acceptance premises. -/
theorem checkedTableCap_complete_zeuge :
    ∃ certificate, checkedTableCap customSpaceFixture 1 0 (by decide) = .ok certificate :=
  checkedTableCap_complete customSpaceFixture 1 0 (by decide) rfl (by decide)

/-- Neither an unregistered space nor a registered but foreign space supplies a capability. -/
theorem checkedTableCap_refused_zeuge :
    checkedTableCap {customSpaceFixture with spaces := []} 1 0 (by decide) =
      .error "pointer table space is not registered" ∧
    checkedTableCap customSpaceFixture 0 0 (by decide) =
      .error "pointer table space is not registered" := ⟨rfl, rfl⟩

end Gabbro.Grammatik.Parser.UebersetzeAllg
