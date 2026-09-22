/-
  File:      Grammatik/Kette108.lean
  Subject:   THE CLOSED CHAIN OF `beispiele/108-disjoint-start-locks.gab`,
             through the GENERIC closing theorem (`schlusssatz`,
             Schlusssatz.lean). The second corpus program with a closed chain,
             and the first whose chain nobody wrote a hand theorem for.

  CHAIN-INSTANCE beispiele/108-disjoint-start-locks.gab kette_108

  108: one table `T` (4 slots, one `u32` field), no lock, two readers
  `read_a` (returns `T.slots[0].v`) and `read_c` (returns `T.slots[1].v`),
  declared `concurrent { read_a, read_c }`. The chain:
  * parse: the real text (`src108`, byte-identical to the file, measured
    2026-09-15) through `uebersetzeAllg`;
  * the unit: the parsed code, no lock invariant, no axiom, the two DECLARED
    starts, the zero memory; the checker accepts it WITH both starts;
  * the user's logic: each body returns what it reads, `ensures` is `true`;
  * the certificate `zert108`: pasted from `gabbro corr-lean` (generic
    section) -- the named-table loads (`T_speicher.slots[0].v`) that the
    printer refused before 2026-09-15, checked by `korrOk`.
  Witness: `kette_108_zeuge` -- `read_a()` from a memory holding `42` in
  `T.slots[0].v`: the Gabbro call returns `42` and EVERY C run returns the
  C value `42`; and the declared concurrent start meets the goal theorem's
  runtime premise (d), so part 5's concurrent conclusion is not vacuous.
-/
import Grammatik.Schlusssatz
import Grammatik.Schlusssatz104

namespace Gabbro.Grammatik.Kette108

open Gabbro.Grammatik Parser Parser.Uebersetze Parser.UebersetzeAllg Parser.UebersetzeAllg2 Zielsatz

set_option maxRecDepth 100000

/-! ## 1. Parse -/

abbrev D8 : Deklaration := declOf uExp108

theorem low_some : (lowerAllg uExp108).toOption.isSome = true := by decide

def P8 : Programm D8 := ((lowerAllg uExp108).toOption.get low_some).1

def fs8 : List D8.Fn := ((lowerAllg uExp108).toOption.get low_some).2

theorem parse8 : parseTopTief toks108 = .ok items108 := rfl

theorem elab8 : elabU (pre108 items108) = .ok uExp108 := rfl

theorem low8 : lowerAllg uExp108 = .ok (P8, fs8) := except_ok_get low_some

/-- **PARSE FIDELITY** of the real text, through the generic stage lemma
    (`uebersetzeAllg_von_zeichen`) -- see the note at `uebersetzt4`: the
    unfolding happens at a variable character list, so the kernel never
    decodes the source `String` (O13). -/
theorem uebersetzt8 : uebersetzeAllg src108 = .ok ⟨uExp108, P8, fs8⟩ :=
  uebersetzeAllg_von_zeichen lexL108 parse8 elab8 low8

/-! ## 2. Members and bodies -/

def t8 : D8.Tab := ⟨0, by decide⟩
def f8 : D8.Feld t8 := ⟨0, by decide⟩
def a8 : D8.Fn := ⟨0, by decide⟩
def c8 : D8.Fn := ⟨1, by decide⟩

theorem tab_eins (t : D8.Tab) : t = t8 := Fin.ext (by have h : t.val < 1 := t.isLt; show t.val = 0; omega)

theorem feld_eins (f : D8.Feld t8) : f = f8 := Fin.ext (by have h : f.val < 1 := f.isLt; show f.val = 0; omega)

theorem fn_zwei (f : D8.Fn) : f = a8 ∨ f = c8 := by
  have h : f.val < 2 := f.isLt
  rcases (by omega : f.val = 0 ∨ f.val = 1) with e | e
  · exact Or.inl (Fin.ext e)
  · exact Or.inr (Fin.ext e)

theorem kein_lock (L : D8.Lock) : False := by have h : L.val < 0 := L.isLt; omega

theorem darf8 : darf D8 t8 [] := by unfold darf; decide

/-- `read_a`'s body: `return T.slots[0].v;`. -/
def bodyA8 : Endblock D8 (vertragVon D8 a8) false (D8.params a8) [] :=
  .ret (.wert (Expr.weiter (lo' := 0) (hi' := 4294967295) (by decide) (by decide)
    (Expr.slot t8 f8 (.weiter (by decide) (by decide) (.lit 0)) darf8))) (List.Perm.refl _)

/-- `read_c`'s body: `return T.slots[1].v;`. -/
def bodyC8 : Endblock D8 (vertragVon D8 c8) false (D8.params c8) [] :=
  .ret (.wert (Expr.weiter (lo' := 0) (hi' := 4294967295) (by decide) (by decide)
    (Expr.slot t8 f8 (.weiter (by decide) (by decide) (.lit 1)) darf8))) (List.Perm.refl _)

theorem rumpf_a8 : P8.rumpf a8 = bodyA8 := rfl
theorem rumpf_c8 : P8.rumpf c8 = bodyC8 := rfl
theorem ens8 (f : D8.Fn) : P8.ensures f = .wahr := by rcases fn_zwei f with e | e <;> subst e <;> rfl
theorem req8 (f : D8.Fn) : P8.requires f = .wahr := rfl

/-! ## 3. Layout, certificate, unit, checker -/

/-- `T` is table block 0: 4 records of one `uint32_t`. -/
def tLay : RecLay := natLay 4 [.int false .w32]

def lay8 : CLayout := fun b =>
  match b with
  | .tab 0 => some { lay := tLay, kind := .plain, base := 0 }
  | _ => none

def EL8 : EmitLay D8 where
  lay := lay8
  tnr := fun _ => 0
  tnr_inj := fun t t' _ => (tab_eins t).trans (tab_eins t').symm
  trec := fun _ => tLay
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

/-- Pasted from `gabbro corr-lean beispiele/108-disjoint-start-locks.gab`,
    generic section (`-- pasteable as KCert`), 2026-09-15. -/
def zert108 : KCert D8 :=
  [{ params := [], locals := [], rows := [GRow.ret (some ((.int false .w32), (.ld (.slotA (.addr (.tab 0)) (.lit 0) 4 4 0) (.int false .w32))))], vm := [], pp := [], ks := [] },
   { params := [], locals := [], rows := [GRow.ret (some ((.int false .w32), (.ld (.slotA (.addr (.tab 0)) (.lit 1) 4 4 0) (.int false .w32))))], vm := [], pp := [], ks := [] }]

def fsA : Aufzaehlung D8.Fn := ⟨[a8, c8], fun f => by
  rcases fn_zwei f with e | e <;> subst e <;> simp⟩

def lsA : Aufzaehlung D8.Lock := ⟨[], fun L => (kein_lock L).elim⟩

def csA : Aufzaehlung (D8.Tab ⊕ D8.Glob) := ⟨[.inl t8], fun c => by
  rcases c with t | g
  · rw [tab_eins t]; simp
  · exact nomatch g⟩

/-- **THE CORRESPONDENCE CERTIFICATE CHECKS** against the parsed program. -/
theorem zert108_ok : korrOk EL8 fnNr zert108 P8 fsA.1 = true := by decide

/-- The zero memory. -/
def sp8 : Speicher D8 where
  slots := fun t _ f => by
    have e := tab_eins t
    subst e
    rw [feld_eins f]
    exact (⟨0, by decide, by decide⟩ : Zahl 0 4294967295)
  globs := fun g => nomatch g

/-- **108 as the goal theorem's unit**: the parsed code, no lock (hence the
    empty family), no axiom, its two DECLARED starts, the zero memory. -/
def E8 : Einheit D8 where
  P := P8
  S := SperrInv.leer D8
  Q := axWahr D8
  starts := [⟨a8, .nil⟩, ⟨c8, .nil⟩]
  sp0 := sp8

/-- The checker accepts the unit WITH its two concurrent starts. -/
theorem akzeptiert8 : akzeptiert_pruefer.akzeptiert E8 fsA.1 lsA.1 csA.1 = true := by decide

/-! ## 4. The user's logic -/

theorem koerperV8 (f : D8.Fn) : KoerperGutV P8 0 f := by
  intro O' _ R _ _ σ ρ _
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · unfold EnsAmRueck
    rw [ens8 f]
    rfl
  · rcases fn_zwei f with e | e <;> subst e
    · rw [rumpf_a8] at hrun
      simp only [bodyA8, execEnd] at hrun
      cases hrun
    · rw [rumpf_c8] at hrun
      simp only [bodyC8, execEnd] at hrun
      cases hrun

theorem logikFrei8 : programmLogikFrei P8 fsA.1 = true := by decide

theorem ohneEwig8 : ohneEwigB P8 fsA.1 = true := by decide

theorem koerperS8 : ∀ f : D8.Fn, KoerperGutS P8 0 (axWahr D8) (SperrInv.leer D8) f := fun f =>
  koerperGutS_leer ⟨koerperGutRQ_of_R _ (koerperGutR_of_V (koerperV8 f)),
    programmLogikFrei_ok fsA.2 logikFrei8 0 _ f⟩

/-- **THE USER'S LOGIC on 108**: the bodies at every budget; the start
    obligation: no lock invariant, and each declared start's `requires`
    (`true`) at the zero memory. -/
theorem nutzer8 : NutzerPflicht E8 where
  logik := ⟨fun passes f => ⟨koerperGutS_alle fsA.2 ohneEwig8 koerperS8 passes f, invGutS_leer rfl f,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ r _ => by
        have h := r.isLt
        have h0 : D8.gruende f = 0 := sigGruende_zero uExp108 f
        omega⟩,
    fun _ _ _ _ => rfl, axEnsLokal_wahr⟩
  start := ⟨fun L => (kein_lock L).elim, fun _ _ => rfl⟩

/-! ## 5. The closed chain -/

/-- **THE CLOSED CHAIN OF `beispiele/108-disjoint-start-locks.gab`.** -/
def kette_108 : Kette src108 where
  u := uExp108
  E := E8
  fs0 := fs8
  uebersetzt := uebersetzt8
  fs := fsA
  ls := lsA
  cs := csA
  akzeptiert := akzeptiert8
  nutzer := nutzer8
  EL := EL8
  zert := zert108
  zertOk := zert108_ok

/-! ## 6. Witnesses (rule 13) -/

def O8 : Orakel D8 where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem hw8 : HardwareAnnahmen O8 E8.Q :=
  And.intro (fun a => nomatch a)
    (And.intro (And.intro (fun r => nomatch r) (fun g => nomatch g)) (axVertragO_wahr O8))

/-- A memory holding `42` in `T.slots[0].v`, `0` elsewhere. -/
def w42 : World D8 where
  slots := fun t k f => by
    have e := tab_eins t
    subst e
    rw [feld_eins f]
    exact if k = 0 then (⟨42, by decide, by decide⟩ : Zahl 0 4294967295) else ⟨0, by decide, by decide⟩
  globs := fun g => nomatch g
  spur := []

/-- The C state of that memory: `T_speicher.slots[0].v == 42`. -/
def st42 : CSt :=
  { mem := fun b o => match b, o with
      | .tab 0, 0 => .int 42
      | _, _ => .int 0,
    live := fun _ => true, obs := [] }

theorem corr42 : corrW EL8 w42 st42 := by
  refine ⟨?_, And.intro (fun g => nomatch g) (fun _ h => Bool.noConfusion h)⟩
  intro t _
  have e := tab_eins t
  subst e
  refine ⟨rfl, ?_⟩
  intro k f h0 h1
  rw [feld_eins f]
  have h1' : k < 4 := h1
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with e | e | e | e <;> subst e <;> rfl

def init8 : Faden → Σ f : D8.mitRuhe.Fn, Env D8.mitRuhe (D8.mitRuhe.params f) :=
  fun t => if t = 0 then ⟨some a8, envR .nil⟩ else ⟨none, .nil⟩

theorem start8 : EinFadenStart E8 (speicherR E8.sp0) init8 where
  lader := rfl
  ruhe := fun u hu => by unfold init8; rw [if_neg hu]
  treiber := Or.inr ⟨a8, .nil, rfl, rfl, rfl⟩

theorem env8 : EnvRel EL8 (zert108[0]'(by decide)).lay (Env.nil (D := D8)) (fun _ => .undef) := by
  exact ⟨(fun _ x => nomatch x), (fun q hq => absurd hq List.not_mem_nil), (fun q hq => absurd hq List.not_mem_nil)⟩

/-- **WITNESS of `schlusssatz` on 108**: every premise jointly (the chain,
    the oracle with the hardware assumptions, the C semantics as the
    binary's behaviour, the driver's start of `read_a`); through part 4,
    `read_a()` from a memory with `42` at `T.slots[0].v` returns `42` in
    Gabbro, the C call has a run, and EVERY C run returns the C value `42`. -/
theorem kette_108_zeuge :
    ∃ (σ' : World D8) (v : ErgVal D8 (D8.erg a8)),
      rufAt P8 O8 0 1 a8 w42 .nil = .ok σ' v ∧ (show Zahl 0 4294967295 from v).n = 42 ∧
      (∃ st' rv, CallAt EL8.lay tvOrc tvXR (kProg zert108) 1 0 st42 [] st' rv) ∧
      ∀ st' rv, CallAt EL8.lay tvOrc tvXR (kProg zert108) 1 0 st42 [] st' rv →
        rv = some (.int 42) := by
  have hR : rufAt P8 O8 0 1 a8 w42 .nil = .ok _ _ := rfl
  have hR' : rufAt kette_108.E.P O8 0 1 a8 w42 .nil = .ok _ _ := hR
  obtain ⟨hex, hall⟩ := (schlusssatz kette_108 O8 hw8 tvOrc tvXR tvXR_funktional
    (fun f => CallAt EL8.lay tvOrc tvXR (kProg zert108) 1 (fnNr f)) (fun _ => 1)
    (fun _ _ _ _ _ h => h) (speicherR E8.sp0) init8 start8).2.2.2.1 0 1 a8
    (zert108[0]'(by decide)) rfl w42 st42 .nil [] (fun _ => .undef) corr42 rfl env8
    (by rw [hR']; rfl)
  refine ⟨_, _, hR, rfl, hex, fun st' rv hC => ?_⟩
  have hO := hall st' rv hC
  rw [hR'] at hO
  obtain ⟨-, c, hc, hv⟩ := hO
  rw [hc, hv]
  rfl

/-- **The concurrent conclusion is not vacuous for 108**: the runtime's start
    of both declared starts (`initRuhe`) meets the goal theorem's premise
    (d), so part 5 gives every leg of `Ziel` on the machines of 108's
    declared concurrent run (here: at its start). -/
theorem kette_108_nebenlaeufig :
    Laufzeit E8 (speicherR E8.sp0) (initRuhe E8.starts) ∧
    Ziel E8.P.mitRuhe E8.S.mitRuhe O8.mitRuhe 0 (RufStartG E8.P.mitRuhe (speicherR E8.sp0)
      (initRuhe E8.starts)) (RufStartG E8.P.mitRuhe (speicherR E8.sp0) (initRuhe E8.starts)) := by
  have hL := laufzeit_initRuhe E8
  exact ⟨hL, (schlusssatz kette_108 O8 hw8 tvOrc tvXR tvXR_funktional
    (fun f => CallAt EL8.lay tvOrc tvXR (kProg zert108) 1 (fnNr f)) (fun _ => 1)
    (fun _ _ _ _ _ h => h) (speicherR E8.sp0) init8 start8).2.2.2.2.2.2.2.2.1.2.2 0 _ _ hL _ .start⟩

#print axioms Gabbro.Grammatik.Kette108.kette_108
#print axioms Gabbro.Grammatik.Kette108.kette_108_zeuge
#print axioms Gabbro.Grammatik.Kette108.kette_108_nebenlaeufig

end Gabbro.Grammatik.Kette108
