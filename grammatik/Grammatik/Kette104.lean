/-
  File:      Grammatik/Kette104.lean
  Subject:   THE CLOSED CHAIN OF `beispiele/104-referenz.gab`, through the
             GENERIC closing theorem (`schlusssatz`, Schlusssatz.lean).

  CHAIN-INSTANCE beispiele/104-referenz.gab kette_104

  `schlusssatz_104` (Schlusssatz104.lean) stays as it is: one program, by
  hand. This file builds the value `kette_104 : Kette src104real` -- the
  REAL source text, comments and all (`src104real`, byte-identical to the
  file, measured 2026-09-15) -- and applies the generic theorem to it:
  * the program is the GENERIC pipeline's output (`uebersetzeAllg`,
    `declOf uExp104`), not `lowerProg`'s `gP`;
  * the checker's Bool on the unit (no declared start: 104 declares no
    `concurrent`), by `decide`;
  * the user's logic (`NutzerPflicht`): the two bodies against every
    frame-respecting handler, at every budget -- the same argument as
    `gP_einzahlen_R`, over the parser's declaration;
  * the emitter's layout (`EL4`) and the certificate `zert104`, pasted
    from `gabbro corr-lean beispiele/104-referenz.gab` (generic section,
    the EXPORTER'S map), checked by `korrOk` by `decide`.
  Witness (rule 13): `kette_104_zeuge` -- `einzahlen(k, 0, 7)` from the
  zero state through the generic theorem: the Gabbro call ends `ok` with
  the slot at `100`, and EVERY C run ends with the C cell at `100`.
-/
import Grammatik.Schlusssatz
import Grammatik.Schlusssatz104

namespace Gabbro.Grammatik.Kette104

open Gabbro.Grammatik Parser Parser.Uebersetze Parser.UebersetzeAllg Parser.UebersetzeAllg2 Zielsatz

set_option maxRecDepth 100000

/-! ## 1. Parse: the real source text, through the generic pipeline -/

abbrev D4 : Deklaration := declOf uExp104

theorem low_some : (lowerAllg uExp104).toOption.isSome = true := by decide

/-- The generically lowered program of 104. -/
def P4 : Programm D4 := ((lowerAllg uExp104).toOption.get low_some).1

def fs4 : List D4.Fn := ((lowerAllg uExp104).toOption.get low_some).2

theorem parse4 : parseTopTief tt104 = .ok items104 := rfl

/-- The lane-162 preprocessing leaves 104's elaboration unchanged. -/
theorem elab4 : elabU (pre108 items104) = .ok uExp104 := rfl

theorem low4 : lowerAllg uExp104 = .ok (P4, fs4) := except_ok_get low_some

/-- **PARSE FIDELITY** of the real text (comments included), through the
    generic stage lemma. Unfolding `uebersetzeAllg` HERE, at the concrete
    source, is what cost 70 GB (O13): `simp` looks at the discriminant
    `lex src104real` and the kernel runs the UTF-8 decoder over 2064
    bytes. `uebersetzeAllg_von_zeichen` does the unfolding once, at a
    VARIABLE character list, so nothing is decoded. -/
theorem uebersetzt4 : uebersetzeAllg src104real = .ok ⟨uExp104, P4, fs4⟩ :=
  uebersetzeAllg_von_zeichen lexL104real parse4 elab4 low4

/-! ## 2. The declaration's members, and the bodies as terms -/

def t4 : D4.Tab := ⟨0, by decide⟩
def f4 : D4.Feld t4 := ⟨0, by decide⟩
def ein4 : D4.Fn := ⟨0, by decide⟩
def lies4 : D4.Fn := ⟨1, by decide⟩
def m4 : D4.Lock := ⟨0, by decide⟩

theorem tab_eins (t : D4.Tab) : t = t4 := Fin.ext (by have h : t.val < 1 := t.isLt; show t.val = 0; omega)

theorem feld_eins (f : D4.Feld t4) : f = f4 := Fin.ext (by have h : f.val < 1 := f.isLt; show f.val = 0; omega)

theorem fn_zwei (f : D4.Fn) : f = ein4 ∨ f = lies4 := by
  have h : f.val < 2 := f.isLt
  rcases (by omega : f.val = 0 ∨ f.val = 1) with e | e
  · exact Or.inl (Fin.ext e)
  · exact Or.inr (Fin.ext e)

theorem ht4 : D4.tabNr 0 = some t4 := rfl

abbrev L4 : List (Res D4) := [Res.held (D := D4) m4]

theorem darf4 : darf D4 t4 L4 := by unfold darf; decide

theorem hp4 : RufPasst D4 (vertragVon D4 ein4) (D4.signatur lies4) L4 where
  hw := fun t _ => by rw [tab_eins t]; rfl
  hg := fun g => nomatch g
  hk := rufHk_ok uExp104 lies4 L4
  hh := fun L hL => by
    have e : L = m4 := Fin.ext (by have h : L.val < 1 := L.isLt; show L.val = 0; omega)
    subst e
    exact List.mem_singleton_self _
  hx := fun L _ hn => absurd (show L ∈ (D4.signatur lies4).haelt by
    have e : L = m4 := Fin.ext (by have h : L.val < 1 := L.isLt; show L.val = 0; omega)
    subst e
    exact List.mem_singleton_self _) hn
  hb := rufHb_ok uExp104 ein4 lies4

/-- `einzahlen`'s body, as the parser lowers it: the write through `k`, the
    call of `lies` on a fresh read-only pointer and `i`, the return. -/
def bodyEin4 : Endblock D4 (vertragVon D4 ein4) false (D4.params ein4) L4 :=
  .cons (Stmt.assignDurch (.var .hier) t4 ht4 f4 (.var (.dort .hier))
      (.weiter (by decide) (by decide) (.lit 100)) rfl darf4)
    (.cons (Stmt.call lies4 (.cons (.ptrOf t4 0 ht4 false) (.cons (.var (.dort .hier)) .nil))
      hp4 rfl) (.ret .keine (List.Perm.refl _)))

/-- `lies`' body: the return of the slot read through `k`. -/
def bodyLies4 : Endblock D4 (vertragVon D4 lies4) false (D4.params lies4) L4 :=
  .ret (.wert (Expr.weiter (lo' := 0) (hi' := 100) (by decide) (by decide)
    (Expr.durch (.var .hier) t4 ht4 f4 (.var (.dort .hier)) darf4))) (List.Perm.refl _)

def ensEin4 : Expr D4 (ErgCtx (D4.params ein4) (D4.erg ein4)) (vertragVon D4 ein4).ende .bool :=
  .le (Expr.altSlot t4 f4 (.var (.dort .hier)) darf4)
    (Expr.durch (.var .hier) t4 ht4 f4 (.var (.dort .hier)) darf4)

def ensLies4 : Expr D4 (ErgCtx (D4.params lies4) (D4.erg lies4)) (vertragVon D4 lies4).ende .bool :=
  .eq (.var .hier) (Expr.durch (.var (.dort .hier)) t4 ht4 f4 (.var (.dort (.dort .hier))) darf4)

/-- The lowered bodies and contracts ARE these terms (kernel-checked). -/
theorem rumpf_ein4 : P4.rumpf ein4 = bodyEin4 := rfl
theorem rumpf_lies4 : P4.rumpf lies4 = bodyLies4 := rfl
theorem ens_ein4 : P4.ensures ein4 = ensEin4 := rfl
theorem ens_lies4 : P4.ensures lies4 = ensLies4 := rfl
theorem req4 (f : D4.Fn) : P4.requires f = .wahr := rfl

/-! ## 3. The emitter's layout and the correspondence certificate -/

/-- The emitter's layout of `D4`: `Konto` is table block 0, `stand` field 0
    of `Konto_slot` at `uint32_t` -- the layout `refEL`/`gEL104` pin. -/
def EL4 : EmitLay D4 where
  lay := refLay
  tnr := fun _ => 0
  tnr_inj := fun t t' _ => (tab_eins t).trans (tab_eins t').symm
  trec := fun _ => kontoLay
  lay_tab := fun _ => rfl
  trec_wf := fun _ => by decide
  trec_count := fun t => by rw [tab_eins t]; rfl
  fnr := fun _ _ => 0
  fnr_lt := fun _ _ => by decide
  fnr_inj := fun t f f' _ => by
    have e := tab_eins t
    subst e
    exact (feld_eins f).trans (feld_eins f').symm
  fnr_fits := fun t f => by
    have e := tab_eins t
    subst e
    rw [feld_eins f]
    rfl
  gnr := fun g => nomatch g
  gnr_inj := fun g => nomatch g
  gty := fun g => nomatch g
  lay_glob := fun g => nomatch g
  gty_fits := fun g => nomatch g

/-- Pasted from `gabbro corr-lean beispiele/104-referenz.gab`, generic section
    (`-- pasteable as KCert`), 2026-09-15. -/
def zert104 : KCert D4 :=
  [{ params := [(0, .ptr), (1, .int false .w32), (2, .int false .w32)], locals := [], rows := [GRow.void 2, GRow.storeSlot 0 (.var 1) 2 4 0 (.int false .w32) (.lit 100), GRow.call 1 [.var 0, .var 1] none], vm := [0, 1, 2], pp := [], ks := [] },
   { params := [(0, .ptr), (1, .int false .w32)], locals := [], rows := [GRow.ret (some ((.int false .w32), (.ld (.slotA (.var 0) (.var 1) 2 4 0) (.int false .w32))))], vm := [0, 1], pp := [], ks := [] }]

def fsA : Aufzaehlung D4.Fn := ⟨[ein4, lies4], fun f => by
  rcases fn_zwei f with e | e <;> subst e <;> simp⟩

def lsA : Aufzaehlung D4.Lock := ⟨[m4], fun L => by
  have e : L = m4 := Fin.ext (by have h : L.val < 1 := L.isLt; show L.val = 0; omega)
  subst e; simp⟩

def csA : Aufzaehlung (D4.Tab ⊕ D4.Glob) := ⟨[.inl t4], fun c => by
  rcases c with t | g
  · rw [tab_eins t]; simp
  · exact nomatch g⟩

/-- **THE CORRESPONDENCE CERTIFICATE CHECKS** against the parsed program. -/
theorem zert104_ok : korrOk EL4 fnNr zert104 P4 fsA.1 = true := by decide

end Gabbro.Grammatik.Kette104
