import Grammatik.Speichermodell.Adressen.Layout
import Grammatik.Kern.Syntax.Koernung
import Grammatik.Zielsatz.Kern.Akzeptiert

/-! The open region in G, executed (PLAN-DYNAMIC 14). One open table `T` (`table T open`, one byte field) and one
provider item `neu : -> ref T else 1 reason` -- the program's memory provider, whose answer is the ONLY way a reference
comes into being. The body `let r = neu() else { return; }; r->x = 7; return;` runs in G:

* `zelle_geschrieben`: when the provider answers cell `K`, the run writes `7` into cell `K` of `T` and returns;
* `kein_statisches_limit`: for EVERY `K` -- no ceiling, `count T = 0` -- there is a provider answer that makes the same
  program write cell `K`;
* `oom_fehlerzweig`: when the provider refuses, the failure branch runs and no cell of `T` is written;
* `zelle_im_bereich`: the written cell lies in the extent of the open region (the address leg, `ImBereich`). -/

namespace Gabbro.Grammatik.GRegion

open Gabbro.Grammatik

/-- One OPEN table `T` (`count 0`: the count bounds nothing), one byte field; one function; one provider item that
    answers a reference into `T` or one reason (out of memory). -/
@[reducible] def rD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 0
  offen := fun _ => true
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 255
  erlaubt := fun _ _ _ _ => true
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun g => g.elim
  nutzlast := fun g => g.elim
  atomar := fun g => g.elim
  geteilt := fun _ => false
  ggeteilt := fun g => g.elim
  Lock := Empty
  decLock := inferInstance
  rang := fun L => L.elim
  maskiert := fun L => L.elim
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => m.elim
  braucht := fun _ => []
  gbraucht := fun g => g.elim
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => ⟨[], none, 0, [], fun _ => true, fun g => g.elim, [], [], none⟩
  eigner_nie_erzeugt := fun _ _ _ _ h => nomatch h
  Inv := Empty
  traeger := fun i => i.elim
  invs := []
  Ax := Unit
  aparams := fun _ => []
  aerg := fun _ => some (.ref 0)
  aschreibt := fun _ _ => false
  agschreibt := fun _ g => g.elim
  agruende := fun _ => 1
  Reg := Empty
  rtyp := fun r => r.elim
  rklasse := fun r => r.elim
  spiegel := fun r => r.elim
  rzusage := fun r => r.elim
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun _ h => nomatch h
  invarianten_gehalten := fun _ i => i.elim
  ggeteilt_bewacht := fun g => g.elim

abbrev rV : Vertrag rD := vertragVon rD ()

/-- After the provider's answer: `r->x = 7; return;` -/
def weiter : Endblock rD rV false [.ref 0] [] :=
  .cons (.assignSlotRef (.var .here) () rfl rfl () (.widen (by decide) (by decide) (.lit 7)) rfl
    (fun _ h => nomatch h)) (.ret .empty (List.Perm.refl _))

/-- `let r = neu() else { return; }; r->x = 7; return;` -/
def rumpf : Endblock rD rV false [] [] :=
  .bindAxiomElse () .nil rfl (by decide) (fun _ h => nomatch h) (fun g => g.elim) (fun _ h => nomatch h)
    (fun g => g.elim)
    (.ret .empty (List.Perm.refl _))
    weiter

/-- The provider answering cell `K` (the raw word `2 K`: tag 0, value `K`). -/
def oK (K : Nat) : Orakel rD :=
  ⟨fun _ σ _ => (σ, 2 * (K : Int)), fun r => r.elim, fun r => r.elim, fun g => g.elim, fun _ => none⟩

/-- The provider refusing (the raw word `1`: reason 0, out of memory). -/
def oVoll : Orakel rD :=
  ⟨fun _ σ _ => (σ, 1), fun r => r.elim, fun r => r.elim, fun g => g.elim, fun _ => none⟩

/-- A start world: every cell holds `0`. -/
def w0 : World rD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => g.elim, []⟩

/-- The provider's answer `2 K` decodes as cell `K`. -/
theorem antwort_K (K : Nat) :
    sonstPasst (D := rD) (fun _ => none) (some (.ref 0)) 1 (2 * (K : Int)) = some (Sum.inl (Val.vonZelle (F := rD.Fn) (passt := rD.passt) (n := 0) K)) := by
  have h1 : 2 * (K : Int) % ((1 : Nat) + 1 : Int) = 0 := by omega
  have h2 : 2 * (K : Int) / ((1 : Nat) + 1 : Int) = K := by omega
  simp only [sonstPasst, h1, if_true, h2, einpassenErg, einpassen, Int.natCast_nonneg, Int.toNat_natCast]
  rfl

/-- **The provider's cell is written.** -/
theorem zelle_geschrieben (K : Nat) (passes : Nat)
    (R : ∀ f : rD.Fn, World rD → Env rD (rD.params f) → RufAusgang f) :
    ∃ σ', execEnd (oK K) passes R rumpf w0 .nil = .zurueck σ' () ∧ (σ'.slots () (K : Int) ()).n = 7 := by
  have h : execEnd (oK K) passes R rumpf w0 .nil =
      (execEnd (oK K) passes R weiter (w0.lese [] []) (.cons (Val.vonZelle K) .nil)).schrumpf := by
    simp only [rumpf, execEnd, axiomAntwortSonst, oK, Args.orte, antwort_K]
    rfl
  rw [h]
  refine ⟨_, rfl, ?_⟩
  exact (congrArg Zahl.n (schreibSlot_slots_same (D := rD) _ () [] (K : Int) () _)).trans rfl

/-- **No static limit**: one program, and for every cell number `K` a provider answer under which it writes cell
    `K` -- although the table declares `count 0`. -/
theorem kein_statisches_limit (passes : Nat)
    (R : ∀ f : rD.Fn, World rD → Env rD (rD.params f) → RufAusgang f) :
    ∀ K : Nat, ∃ O σ', execEnd O passes R rumpf w0 .nil = .zurueck σ' () ∧ (σ'.slots () (K : Int) ()).n = 7 ∧
      ¬ (K : Int) < rD.count () := by
  intro K
  obtain ⟨σ', h, h7⟩ := zelle_geschrieben K passes R
  exact ⟨oK K, σ', h, h7, by simp⟩

/-- **Out of memory is the failure branch**: the provider refuses, the function returns through `else`, and no cell
    of `T` changes. -/
theorem oom_fehlerzweig (passes : Nat) (R : ∀ f : rD.Fn, World rD → Env rD (rD.params f) → RufAusgang f) :
    ∃ σ', execEnd oVoll passes R rumpf w0 .nil = .zurueck σ' () ∧ ∀ k f, σ'.slots () k f = w0.slots () k f := by
  refine ⟨_, rfl, fun _ _ => rfl⟩

/-- **The written cell lies in the extent of the open region**, whatever its number. -/
theorem zelle_im_bereich (K : Nat) : ImBereich rD () (K : Int) := ⟨by omega, .inl rfl⟩

/-- The whole program: its one function is `rumpf`. -/
def prog : Programm rD where
  invariante := fun i => i.elim
  requires := fun _ => Expr.tru
  ensures := fun _ => Expr.tru
  rumpf := fun _ => rumpf

/-- **The core checker accepts the program with the open region.** -/
theorem prog_akzeptiert :
    Akzeptiert prog ⟨fun L => L.elim, fun L => L.elim⟩ [()] [] [.inl ()] [()] = true := by decide +kernel

end Gabbro.Grammatik.GRegion
