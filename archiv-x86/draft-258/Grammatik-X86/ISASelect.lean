/-
  File:      Grammatik/X86/ISASelect.lean
  Subject:   A decided peephole / instruction-selection pass over the unified
             instruction set: a straight-line program of pilot (plus shift and
             SETcc) rows is rewritten into a SHORTER unified program using the
             compact forms (`kompaktWahl`, `aluImmWahl`) and the integer-core
             LEA for `d := a + (b << k)`, with a proof that the selected
             program runs to a state that agrees with the original one.

  Reused, not redefined: `Instr`/`stepI`/`laufI`/`canonI`/`encodeI`
  (`ISA.lean`), `stepI_rahmen`/`progBytes`/`laufBytesI_layout`
  (`ISAExecution.lean`), `kompaktWahl`/`passtSx32`/`passtS8_32`/`disp8Of`/
  `dispWort8_eq_signExtend`/`effAddr8_eq_effAddr`/`effAddr0_eq_effAddr`/
  `aluWert`/`aluFlags`/`aluSchreibt` (`CompactForms.lean`), `aluImmWahl`
  (`CompactFormsWitnesses.lean`), `leaVal`/`core_lea64` (`IntegerCore.lean`),
  `shiftSchritt_weiter` (`ShiftCodec.lean`), the pilot step equations
  (`Ausfuehrung.lean`) and the flag read sets of `FlagDependencies.lean`
  (`stimmtUebberein`, `setccBytes_stabil`) for the one flag reader admitted.

  WHAT IS PRESERVED (`waehle_korrekt`). For the original program `p` and the
  selected program `q`, both run by `laufI` from the SAME state:
    * both refuse, or both succeed;
    * on success the final states agree on EVERY register outside the
      declared scratch list `S`, on ALL of memory (bytes and permissions),
      and -- when the caller declares the flags live at the end
      (`flEnde = true`) -- on all flags;
    * RIP is NOT compared: the selected program is shorter, so its final
      RIP is its own start plus its own byte length (`laufI_rip`). That
      is the layout statement: every program counter moves, and nothing
      in the admitted straight-line language reads RIP.
  Flags may differ only where the original's flags are DEAD: the LEA
  rewrite drops the flag writes of SHL/ADD, and the selector admits it only
  if every later flag READ (a SETcc) and the program end (if `flEnde`) is
  preceded by a flag-writing instruction of the selected program. The check
  is decided by the selector itself (`sel`, the flag bit `fl`), with the
  read set of SETcc taken from `FlagDependencies.stimmtUebberein`.

  Control flow is refused: no rule admits a pilot jump/branch/call/ret or a
  compact rel8 jump, so a program containing one is NOT selected
  (`gift_sprung`). A shorter encoding before a jump target would move the
  target; jumps keep their long form until a layout pass revalidates them.

  Contents:
    §1 agreement modulo scratch (`Gl`, `OptRel`), the read/write footprints
    §2 the frame lemmas of the kept rows
    §3 the effect lemmas of the three rewrites
    §4 the selection relation `Wahl` and the decided selector `sel`
    §5 correctness, byte shrink, canonicity and the byte-level corollary
-/
import Grammatik.X86.ISAExecution
import Grammatik.X86.CompactFormsWitnesses
import Grammatik.X86.FlagDependencies

namespace Gabbro.Grammatik.X86

/-! ## 1. Agreement modulo a difference set. -/

/-- Two states agree outside the difference set `D` on registers, on all of
    memory, and -- when `fl` -- on all flags. RIP is never compared. -/
def Gl (D : List Register) (fl : Bool) (s1 s2 : Zustand) : Prop :=
  (∀ r, r ∉ D → s1.register r = s2.register r) ∧ s1.speicher = s2.speicher ∧
    (fl = true → s1.flags = s2.flags)

/-- Lifting a relation to run outcomes: both refuse, or both succeed and
    the successors are related. -/
def OptRel (R : Zustand → Zustand → Prop) : Option Zustand → Option Zustand → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

theorem optRel_bind (R1 R2 : Zustand → Zustand → Prop) (o1 o2 : Option Zustand)
    (f g : Zustand → Option Zustand) (h : OptRel R1 o1 o2)
    (hfg : ∀ a b, R1 a b → OptRel R2 (f a) (g b)) :
    OptRel R2 (o1.bind f) (o2.bind g) := by
  cases o1 <;> cases o2 <;> simp only [OptRel] at h
  · trivial
  · exact hfg _ _ h

/-- The difference set with one register removed (it was overwritten with
    the same value on both sides). -/
def entferne (D : List Register) (d : Register) : List Register :=
  D.filter (fun r => r != d)

theorem nicht_in_entferne (D : List Register) (d r : Register)
    (h : r ∉ entferne D d) (hr : r ≠ d) : r ∉ D := by
  intro hm
  apply h
  simp only [entferne, List.mem_filter, bne_iff_ne, ne_eq]
  exact ⟨hm, hr⟩

theorem entferne_teil (D S : List Register) (d : Register)
    (h : ∀ r ∈ D, r ∈ S) : ∀ r ∈ entferne D d, r ∈ S := by
  intro r hr
  simp only [entferne, List.mem_filter] at hr
  exact h r hr.1

/-- Decided: no register of `rs` is in the difference set. -/
def frei (D rs : List Register) : Bool := rs.all (fun r => !D.contains r)

theorem frei_mem (D rs : List Register) (h : frei D rs = true) (r : Register)
    (hr : r ∈ rs) : r ∉ D := by
  simp only [frei, List.all_eq_true] at h
  have := h r hr
  simpa using this

theorem gl_reg (D : List Register) (fl : Bool) (s1 s2 : Zustand) (hg : Gl D fl s1 s2)
    (rs : List Register) (hf : frei D rs = true) (r : Register) (hr : r ∈ rs) :
    s1.register r = s2.register r :=
  hg.1 r (frei_mem D rs hf r hr)

/-- A register write of the SAME value on both sides removes the register
    from the difference set; the new flag bit is justified by `hf`. -/
theorem gl_schrittRegister (D : List Register) (fl : Bool) (s1 s2 : Zustand)
    (hg : Gl D fl s1 s2) (d : Register) (v : Wort) (n1 n2 : Adresse)
    (f1 f2 : Flags) (fl' : Bool) (hf : fl' = true → f1 = f2) :
    Gl (entferne D d) fl' (schrittRegister s1 n1 f1 d v)
      (schrittRegister s2 n2 f2 d v) := by
  refine ⟨fun r hr => ?_, hg.2.1, hf⟩
  show regSet s1.register d v r = regSet s2.register d v r
  by_cases hrd : r = d
  · subst hrd
    rw [regSet_gleich, regSet_gleich]
  · rw [regSet_fremd _ _ _ _ hrd, regSet_fremd _ _ _ _ hrd]
    exact hg.1 r (nicht_in_entferne D d r hr hrd)

/-! ### Footprints of the kept pilot rows. -/

/-- The pilot rows the selector may keep unchanged: the straight-line
    register, load and store forms (no stack, no control flow). -/
def behaltbar : Befehl → Bool
  | .movImm64 _ _ => true
  | .movReg64 _ _ => true
  | .addReg64 _ _ => true
  | .subReg64 _ _ => true
  | .xorReg64 _ _ => true
  | .cmpReg64 _ _ => true
  | .load64 _ _ _ => true
  | .store64 _ _ _ => true
  | _ => false

/-- Registers a kept pilot row reads. -/
def liestP : Befehl → List Register
  | .movReg64 _ src => [src]
  | .addReg64 d s => [d, s]
  | .subReg64 d s => [d, s]
  | .xorReg64 d s => [d, s]
  | .cmpReg64 l r => [l, r]
  | .load64 _ base _ => [base]
  | .store64 base src _ => [base, src]
  | _ => []

/-- The register a kept pilot row overwrites, if any. -/
def schreibtP : Befehl → Option Register
  | .movImm64 d _ => some d
  | .movReg64 d _ => some d
  | .addReg64 d _ => some d
  | .subReg64 d _ => some d
  | .xorReg64 d _ => some d
  | .load64 d _ _ => some d
  | _ => none

/-- Whether a kept pilot row writes the whole flag snapshot. -/
def setztFlags : Befehl → Bool
  | .addReg64 _ _ => true
  | .subReg64 _ _ => true
  | .xorReg64 _ _ => true
  | .cmpReg64 _ _ => true
  | _ => false

def nachD (D : List Register) (b : Befehl) : List Register :=
  match schreibtP b with
  | some d => entferne D d
  | none => D

def nachFl (fl : Bool) (b : Befehl) : Bool := fl || setztFlags b

theorem nachD_teil (D S : List Register) (b : Befehl) (h : ∀ r ∈ D, r ∈ S) :
    ∀ r ∈ nachD D b, r ∈ S := by
  unfold nachD
  split
  · exact entferne_teil D S _ h
  · exact h

/-! ## 2. Frame lemmas of the kept rows. -/

/-- FRAME (kept pilot rows): two states that agree outside `D` and on the
    registers the row reads step to states that agree outside `nachD D b`
    (the written register agrees again), refusing together. -/
theorem schritt_gl (b : Befehl) (hb : behaltbar b = true) (l : Nat)
    (D : List Register) (fl : Bool) (s1 s2 : Zustand) (hg : Gl D fl s1 s2)
    (hr : frei D (liestP b) = true) :
    OptRel (Gl (nachD D b) (nachFl fl b)) (schritt ⟨b, l⟩ s1) (schritt ⟨b, l⟩ s2) := by
  cases hl : laengeOk l with
  | false =>
    unfold schritt
    simp only [hl]
    trivial
  | true =>
    cases b with
    | movImm64 d v =>
      rw [schritt_movImm64 _ _ d v hl rfl, schritt_movImm64 _ _ d v hl rfl]
      exact gl_schrittRegister D fl s1 s2 hg d v _ _ _ _ _
        (fun h => hg.2.2 (by simpa [nachFl, setztFlags] using h))
    | movReg64 d src =>
      rw [schritt_movReg64 _ _ d src hl rfl, schritt_movReg64 _ _ d src hl rfl]
      have e := gl_reg D fl s1 s2 hg _ hr src (by simp [liestP])
      show Gl _ _ (schrittRegister _ _ _ d (s1.register src))
        (schrittRegister _ _ _ d (s2.register src))
      rw [e]
      exact gl_schrittRegister D fl s1 s2 hg d _ _ _ _ _ _
        (fun h => hg.2.2 (by simpa [nachFl, setztFlags] using h))
    | addReg64 d src =>
      rw [schritt_addReg64 _ _ d src hl rfl, schritt_addReg64 _ _ d src hl rfl]
      have e1 := gl_reg D fl s1 s2 hg _ hr d (by simp [liestP])
      have e2 := gl_reg D fl s1 s2 hg _ hr src (by simp [liestP])
      show Gl _ _ (schrittRegister _ _ _ d _) (schrittRegister _ _ _ d _)
      rw [e1, e2]
      exact gl_schrittRegister D fl s1 s2 hg d _ _ _ _ _ _ (fun _ => rfl)
    | subReg64 d src =>
      rw [schritt_subReg64 _ _ d src hl rfl, schritt_subReg64 _ _ d src hl rfl]
      have e1 := gl_reg D fl s1 s2 hg _ hr d (by simp [liestP])
      have e2 := gl_reg D fl s1 s2 hg _ hr src (by simp [liestP])
      show Gl _ _ (schrittRegister _ _ _ d _) (schrittRegister _ _ _ d _)
      rw [e1, e2]
      exact gl_schrittRegister D fl s1 s2 hg d _ _ _ _ _ _ (fun _ => rfl)
    | xorReg64 d src =>
      rw [schritt_xorReg64 _ _ d src hl rfl, schritt_xorReg64 _ _ d src hl rfl]
      have e1 := gl_reg D fl s1 s2 hg _ hr d (by simp [liestP])
      have e2 := gl_reg D fl s1 s2 hg _ hr src (by simp [liestP])
      show Gl _ _ (schrittRegister _ _ _ d _) (schrittRegister _ _ _ d _)
      rw [e1, e2]
      exact gl_schrittRegister D fl s1 s2 hg d _ _ _ _ _ _ (fun _ => rfl)
    | cmpReg64 lhs rhs =>
      rw [schritt_cmpReg64 _ _ lhs rhs hl rfl, schritt_cmpReg64 _ _ lhs rhs hl rfl]
      have e1 := gl_reg D fl s1 s2 hg _ hr lhs (by simp [liestP])
      have e2 := gl_reg D fl s1 s2 hg _ hr rhs (by simp [liestP])
      refine ⟨hg.1, hg.2.1, fun _ => ?_⟩
      show (sub64 (s1.register lhs) (s1.register rhs)).2 =
        (sub64 (s2.register lhs) (s2.register rhs)).2
      rw [e1, e2]
    | load64 d base disp =>
      have e := gl_reg D fl s1 s2 hg _ hr base (by simp [liestP])
      have ha : effAddr s1 base disp = effAddr s2 base disp := by
        unfold effAddr; rw [e]
      cases hrd : read64 s2.speicher (effAddr s2 base disp) with
      | none =>
        have hrd1 : read64 s1.speicher (effAddr s1 base disp) = none := by
          rw [ha, hg.2.1, hrd]
        rw [schritt_load64_verweigert _ _ d base disp hl rfl hrd1,
          schritt_load64_verweigert _ _ d base disp hl rfl hrd]
        trivial
      | some v =>
        have hrd1 : read64 s1.speicher (effAddr s1 base disp) = some v := by
          rw [ha, hg.2.1, hrd]
        rw [schritt_load64_erfolg _ _ d base disp v hl rfl hrd1,
          schritt_load64_erfolg _ _ d base disp v hl rfl hrd]
        exact gl_schrittRegister D fl s1 s2 hg d v _ _ _ _ _
          (fun h => hg.2.2 (by simpa [nachFl, setztFlags] using h))
    | store64 base src disp =>
      have e1 := gl_reg D fl s1 s2 hg _ hr base (by simp [liestP])
      have e2 := gl_reg D fl s1 s2 hg _ hr src (by simp [liestP])
      have ha : effAddr s1 base disp = effAddr s2 base disp := by
        unfold effAddr; rw [e1]
      cases hwr : write64 s2.speicher (effAddr s2 base disp) (s2.register src) with
      | none =>
        have hwr1 : write64 s1.speicher (effAddr s1 base disp) (s1.register src) =
            none := by rw [ha, hg.2.1, e2, hwr]
        rw [schritt_store64_verweigert _ _ base src disp hl rfl hwr1,
          schritt_store64_verweigert _ _ base src disp hl rfl hwr]
        trivial
      | some m =>
        have hwr1 : write64 s1.speicher (effAddr s1 base disp) (s1.register src) =
            some m := by rw [ha, hg.2.1, e2, hwr]
        rw [schritt_store64_erfolg _ _ base src disp m hl rfl hwr1,
          schritt_store64_erfolg _ _ base src disp m hl rfl hwr]
        exact ⟨hg.1, rfl, fun h => hg.2.2 (by simpa [nachFl, setztFlags] using h)⟩
    | jump32 _ => simp [behaltbar] at hb
    | jumpIf32 _ _ => simp [behaltbar] at hb
    | call32 _ => simp [behaltbar] at hb
    | push64 _ => simp [behaltbar] at hb
    | pop64 _ => simp [behaltbar] at hb
    | ret => simp [behaltbar] at hb

/-- FRAME (kept SETcc): with all flags agreeing (`fl = true`) and the
    destination outside `D`, SETcc steps agree outside `D` minus the
    destination. The selected low byte agrees by the REUSED
    `FlagDependencies.setccBytes_stabil`. -/
theorem setcc_gl (c : Bedingung) (dst : Register) (l : Nat) (D : List Register)
    (s1 s2 : Zustand) (hg : Gl D true s1 s2) (hd : dst ∉ D) :
    OptRel (Gl (entferne D dst) true) (setccSchrittBytes l s1 dst c)
      (setccSchrittBytes l s2 dst c) := by
  cases hl : laengeOk l with
  | false =>
    unfold setccSchrittBytes
    simp only [hl]
    trivial
  | true =>
    cases h1 : setccSchrittBytes l s1 dst c with
    | none => unfold setccSchrittBytes at h1; rw [hl] at h1; cases h1
    | some a =>
      cases h2 : setccSchrittBytes l s2 dst c with
      | none => unfold setccSchrittBytes at h2; rw [hl] at h2; cases h2
      | some b =>
        have hfl : s1.flags = s2.flags := hg.2.2 rfl
        have hv := setccBytes_stabil l s1 s2 a b dst c hl
          (fun n _ => by rw [hfl]) (hg.1 dst hd) h1 h2
        unfold setccSchrittBytes at h1 h2
        rw [hl] at h1 h2
        cases h1
        cases h2
        refine ⟨fun r hr => ?_, hg.2.1, fun _ => hfl⟩
        by_cases hrd : r = dst
        · subst hrd; exact hv
        · show regSet s1.register dst _ r = regSet s2.register dst _ r
          rw [regSet_fremd _ _ _ _ hrd, regSet_fremd _ _ _ _ hrd]
          exact hg.1 r (nicht_in_entferne D dst r hr hrd)

/-- FRAME (kept immediate shift): the evidence reads only the destination,
    so agreement there gives agreeing results; a nonzero masked count
    writes the flags (from agreeing inputs), a zero count leaves them. -/
theorem shift_gl (r : ShiftRichtung) (dst : Register) (k l : Nat)
    (D : List Register) (fl : Bool) (s1 s2 : Zustand) (hg : Gl D fl s1 s2)
    (hd : dst ∉ D) :
    OptRel (Gl (entferne D dst) (fl || (k % 64 != 0)))
      (shiftSchritt ⟨.imm r dst k, l⟩ s1) (shiftSchritt ⟨.imm r dst k, l⟩ s2) := by
  have he : s1.register dst = s2.register dst := hg.1 dst hd
  by_cases hl : (l == shiftLaenge (.imm r dst k)) = true
  · by_cases h0 : schiebeZaehler .b64 k = 0
    · have h0' : (schiebeZaehler .b64 (shiftZaehler (.imm r dst k) s1) == 0) = true := by
        simp [shiftZaehler, h0]
      have h0'' : (schiebeZaehler .b64 (shiftZaehler (.imm r dst k) s2) == 0) = true := by
        simp [shiftZaehler, h0]
      rw [shiftSchritt_null _ s1 hl h0', shiftSchritt_null _ s2 hl h0'']
      have hk : (k % 64 != 0) = false := by simpa [schiebeZaehler] using h0
      refine ⟨fun q hq => ?_, hg.2.1, fun h => hg.2.2 (by simpa [hk] using h)⟩
      by_cases hqd : q = dst
      · subst hqd; exact he
      · exact hg.1 q (nicht_in_entferne D dst q hq hqd)
    · have h1 : schiebeZaehler .b64 (shiftZaehler (.imm r dst k) s1) ≠ 0 := h0
      have h2 : schiebeZaehler .b64 (shiftZaehler (.imm r dst k) s2) ≠ 0 := h0
      rw [shiftSchritt_weiter _ s1 hl h1, shiftSchritt_weiter _ s2 hl h2]
      have hn : shiftNachweis (.imm r dst k) s1 = shiftNachweis (.imm r dst k) s2 := by
        simp only [shiftNachweis, he]
      show Gl _ _ (schrittRegister _ _ _ dst _) (schrittRegister _ _ _ dst _)
      rw [hn]
      exact gl_schrittRegister D fl s1 s2 hg dst _ _ _ _ _ _ (fun _ => rfl)
  · unfold shiftSchritt
    rw [if_neg hl, if_neg hl]
    trivial

/-! ## 3. Effect lemmas of the three rewrites. -/

/-- A state with its program counter forgotten. -/
def ohneRip (s : Zustand) : Zustand := { s with rip := 0 }

/-- `Gl` never looks at RIP. -/
theorem gl_ohneRip (D : List Register) (fl : Bool) (a b : Zustand) :
    Gl D fl a b ↔ Gl D fl a (ohneRip b) := Iff.rfl

/-- Replacing the right outcome by one that differs only in RIP keeps any
    RIP-blind relation. -/
theorem optRel_ohneRip (D : List Register) (fl : Bool) (o1 o2 o3 : Option Zustand)
    (h : OptRel (Gl D fl) o1 o2) (he : o2.map ohneRip = o3.map ohneRip) :
    OptRel (Gl D fl) o1 o3 := by
  cases o2 with
  | none =>
    cases o3 with
    | none => exact h
    | some c => cases he
  | some b =>
    cases o3 with
    | none => cases he
    | some c =>
      cases o1 with
      | none => exact absurd h id
      | some a =>
        have hbc : ohneRip b = ohneRip c := Option.some.inj he
        have hb : Gl D fl a (ohneRip b) := h
        rw [hbc] at hb
        exact hb

/-- The data-moving pilot rows with a compact analog (`kompaktWahl` is
    applied ONLY to these: its jump arms are never used, jumps keep their
    long form). -/
def kompaktDaten : Befehl → Option CompactBefehl
  | .movImm64 d v => kompaktWahl (.movImm64 d v)
  | .load64 d base disp => kompaktWahl (.load64 d base disp)
  | .store64 base src disp => kompaktWahl (.store64 base src disp)
  | _ => none

/-- REWRITE 1 (compact data forms): the selected compact row has the SAME
    effect as the pilot row, success and refusal included, up to RIP. -/
theorem kompakt_wirkung (b : Befehl) (cb : CompactBefehl)
    (h : kompaktDaten b = some cb) (s : Zustand) (l l' : Nat)
    (hl : laengeOk l = true) (hl' : laengeOk l' = true) :
    (schrittC ⟨cb, l'⟩ s).map ohneRip = (schritt ⟨b, l⟩ s).map ohneRip := by
  cases b with
  | movImm64 d v =>
    simp only [kompaktDaten, kompaktWahl] at h
    rw [schritt_movImm64 _ _ d v hl rfl]
    split at h
    · rename_i hzx
      cases h
      rw [schrittC_movImm32Zx _ _ d _ hl' rfl, of_decide_eq_true hzx]
      rfl
    · split at h
      · rename_i _ hsx
        cases h
        rw [schrittC_movImm32Sx _ _ d _ hl' rfl, of_decide_eq_true hsx]
        rfl
      · cases h
  | load64 d base disp =>
    simp only [kompaktDaten, kompaktWahl] at h
    split at h
    · rename_i hd0
      cases h
      obtain ⟨hdisp, _, _⟩ := of_decide_eq_true hd0
      subst hdisp
      have ha : effAddr0 s base = effAddr s base 0 := effAddr0_eq_effAddr s base
      cases hrd : read64 s.speicher (effAddr s base 0) with
      | none =>
        rw [schritt_load64_verweigert _ _ d base 0 hl rfl hrd]
        rw [← ha] at hrd
        rw [schrittC_load64Disp0_verweigert _ _ d base hl' rfl hrd]
      | some v =>
        rw [schritt_load64_erfolg _ _ d base 0 v hl rfl hrd]
        rw [← ha] at hrd
        rw [schrittC_load64Disp0_erfolg _ _ d base v hl' rfl hrd]
        rfl
    · split at h
      · rename_i _ hs8
        cases h
        have ha : effAddr8 s base (disp8Of disp) = effAddr s base disp := by
          rw [effAddr8_eq_effAddr, of_decide_eq_true hs8]
        cases hrd : read64 s.speicher (effAddr s base disp) with
        | none =>
          rw [schritt_load64_verweigert _ _ d base disp hl rfl hrd]
          rw [← ha] at hrd
          rw [schrittC_load64Disp8_verweigert _ _ d base _ hl' rfl hrd]
        | some v =>
          rw [schritt_load64_erfolg _ _ d base disp v hl rfl hrd]
          rw [← ha] at hrd
          rw [schrittC_load64Disp8_erfolg _ _ d base _ v hl' rfl hrd]
          rfl
      · cases h
  | store64 base src disp =>
    simp only [kompaktDaten, kompaktWahl] at h
    split at h
    · rename_i hd0
      cases h
      obtain ⟨hdisp, _, _⟩ := of_decide_eq_true hd0
      subst hdisp
      have ha : effAddr0 s base = effAddr s base 0 := effAddr0_eq_effAddr s base
      cases hwr : write64 s.speicher (effAddr s base 0) (s.register src) with
      | none =>
        rw [schritt_store64_verweigert _ _ base src 0 hl rfl hwr]
        rw [← ha] at hwr
        rw [schrittC_store64Disp0_verweigert _ _ base src hl' rfl hwr]
      | some m =>
        rw [schritt_store64_erfolg _ _ base src 0 m hl rfl hwr]
        rw [← ha] at hwr
        rw [schrittC_store64Disp0_erfolg _ _ base src m hl' rfl hwr]
        rfl
    · split at h
      · rename_i _ hs8
        cases h
        have ha : effAddr8 s base (disp8Of disp) = effAddr s base disp := by
          rw [effAddr8_eq_effAddr, of_decide_eq_true hs8]
        cases hwr : write64 s.speicher (effAddr s base disp) (s.register src) with
        | none =>
          rw [schritt_store64_verweigert _ _ base src disp hl rfl hwr]
          rw [← ha] at hwr
          rw [schrittC_store64Disp8_verweigert _ _ base src _ hl' rfl hwr]
        | some m =>
          rw [schritt_store64_erfolg _ _ base src disp m hl rfl hwr]
          rw [← ha] at hwr
          rw [schrittC_store64Disp8_erfolg _ _ base src _ m hl' rfl hwr]
          rfl
      · cases h
  | movReg64 _ _ => simp [kompaktDaten] at h
  | addReg64 _ _ => simp [kompaktDaten] at h
  | subReg64 _ _ => simp [kompaktDaten] at h
  | xorReg64 _ _ => simp [kompaktDaten] at h
  | cmpReg64 _ _ => simp [kompaktDaten] at h
  | jump32 _ => simp [kompaktDaten] at h
  | jumpIf32 _ _ => simp [kompaktDaten] at h
  | call32 _ => simp [kompaktDaten] at h
  | push64 _ => simp [kompaktDaten] at h
  | pop64 _ => simp [kompaktDaten] at h
  | ret => simp [kompaktDaten] at h

/-- The pilot register-register ALU rows, as (operation, destination,
    source) of the compact family's `AluOp` (AND/OR have no pilot row). -/
def aluVon : Befehl → Option (AluOp × Register × Register)
  | .addReg64 d t => some (.add, d, t)
  | .subReg64 d t => some (.sub, d, t)
  | .xorReg64 d t => some (.xor', d, t)
  | .cmpReg64 d t => some (.cmp, d, t)
  | _ => none

/-- The successor of one ALU operation with second operand `y`: the shape
    BOTH `schritt` (register source) and `schrittC` (immediate) produce. -/
def ergAlu (o : AluOp) (s : Zustand) (n : Adresse) (d : Register) (y : Wort) : Zustand :=
  if aluSchreibt o then
    schrittRegister s n (aluFlags o (s.register d) y) d (aluWert o (s.register d) y)
  else { s with rip := n, flags := aluFlags o (s.register d) y }

theorem schritt_aluVon (pb : Befehl) (o : AluOp) (d t : Register)
    (h : aluVon pb = some (o, d, t)) (l : Nat) (hl : laengeOk l = true) (s : Zustand) :
    schritt ⟨pb, l⟩ s = some (ergAlu o s (ripNach s.rip l) d (s.register t)) := by
  cases pb <;> simp only [aluVon, Option.some.injEq, Prod.mk.injEq,
    reduceCtorEq] at h
  · obtain ⟨rfl, rfl, rfl⟩ := h
    rw [schritt_addReg64 _ _ _ _ hl rfl]; rfl
  · obtain ⟨rfl, rfl, rfl⟩ := h
    rw [schritt_subReg64 _ _ _ _ hl rfl]; rfl
  · obtain ⟨rfl, rfl, rfl⟩ := h
    rw [schritt_xorReg64 _ _ _ _ hl rfl]; rfl
  · obtain ⟨rfl, rfl, rfl⟩ := h
    rw [schritt_cmpReg64 _ _ _ _ hl rfl]; rfl

/-- REWRITE 2 (ALU immediate): the REUSED selector `aluImmWahl` over a
    value that round-trips through a signed 32-bit immediate computes the
    ALU operation with that value as second operand. -/
theorem schrittC_aluImmWahl (o : AluOp) (d : Register) (v : Wort)
    (hv : passtSx32 v = true) (l : Nat) (hl : laengeOk l = true) (s : Zustand) :
    schrittC ⟨aluImmWahl o d (BitVec.ofNat 32 v.toNat), l⟩ s =
      some (ergAlu o s (ripNach s.rip l) d v) := by
  have hw : dispWort (BitVec.ofNat 32 v.toNat) = v := of_decide_eq_true hv
  unfold aluImmWahl
  split
  · rename_i h8
    have h8' : (disp8Of (BitVec.ofNat 32 v.toNat)).signExtend 32 =
        BitVec.ofNat 32 v.toNat := of_decide_eq_true h8
    have hd : dispWort8 (disp8Of (BitVec.ofNat 32 v.toNat)) = v := by
      rw [dispWort8_eq_signExtend, h8', hw]
    unfold schrittC
    rw [hl]
    simp only [hd]
    rfl
  · unfold schrittC
    rw [hl]
    simp only [hw]
    rfl

/-- Both sides run the same ALU operation on agreeing destinations: the
    destination (if written) agrees again and all flags agree. -/
theorem gl_ergAlu (D : List Register) (fl : Bool) (s1 s2 : Zustand) (hg : Gl D fl s1 s2)
    (o : AluOp) (d : Register) (y : Wort) (n1 n2 : Adresse)
    (hd : s1.register d = s2.register d) :
    Gl (if aluSchreibt o then entferne D d else D) true (ergAlu o s1 n1 d y)
      (ergAlu o s2 n2 d y) := by
  unfold ergAlu
  cases ha : aluSchreibt o
  · simp only [Bool.false_eq_true, if_false]
    refine ⟨hg.1, hg.2.1, fun _ => ?_⟩
    show aluFlags o (s1.register d) y = aluFlags o (s2.register d) y
    rw [hd]
  · simp only [if_true]
    rw [hd]
    exact gl_schrittRegister D fl s1 s2 hg d _ _ _ _ _ _ (fun _ => rfl)

/-- The difference set after the ALU rewrite: the scratch `t` now differs
    (the original loaded it, the selected program did not), the written
    destination agrees again. -/
def aluD (o : AluOp) (D : List Register) (t d : Register) : List Register :=
  if aluSchreibt o then entferne (t :: D) d else t :: D

/-- The scale of a shift count usable in an LEA (1, 2, 3; a zero count is
    not rewritten). -/
def skalaVon : Nat → Option Scale
  | 1 => some .s2
  | 2 => some .s4
  | 3 => some .s8
  | _ => none

theorem skalaVon_spec (k : Nat) (sc : Scale) (h : skalaVon k = some sc) :
    scaleShift sc = k ∧ schiebeZaehler .b64 k ≠ 0 ∧ k < 256 := by
  unfold skalaVon at h
  split at h <;> cases h <;> decide

/-! ## 4. The selection relation and the decided selector. -/

/-- The rewrite rules as a relation between an original and a selected
    straight-line program, threading the difference set `D` (registers
    that may differ; kept inside the scratch list `S`) and the flag bit
    `fl` (all flags agree). `fe` declares the flags live at the end. -/
inductive Wahl (S : List Register) (fe : Bool) :
    List Register → Bool → List Instr → List Instr → Prop
  /-- End of program: flags must agree if they are live there. -/
  | ende (D : List Register) (fl : Bool) (h : fe = true → fl = true) :
      Wahl S fe D fl [] []
  /-- `mov d, b; shl d, k; add d, a` becomes `lea d, [a + b * 2^k]`
      (flags dropped: the next flag reader must see a fresh writer). -/
  | lea (D : List Register) (fl : Bool) (d b a : Register) (k : Nat) (sc : Scale)
      (rest q : List Instr) (hk : skalaVon k = some sc) (hda : d ≠ a)
      (hb : b ≠ .rsp) (hf : frei D [a, b] = true)
      (hq : Wahl S fe (entferne D d) false rest q) :
      Wahl S fe D fl
        (.pilot (.movReg64 d b) :: .shift (.imm .shl d k) :: .pilot (.addReg64 d a) :: rest)
        (.core (.lea64 d a (some (b, sc)) 0) :: q)
  /-- `mov t, v; op d, t` with a scratch `t` becomes the compact
      immediate form (`aluImmWahl`); `t` joins the difference set. -/
  | alu (D : List Register) (fl : Bool) (t : Register) (v : Wort) (pb : Befehl)
      (o : AluOp) (d : Register) (rest q : List Instr)
      (ha : aluVon pb = some (o, d, t)) (htd : t ≠ d) (hS : t ∈ S)
      (hf : frei D [d] = true) (hv : passtSx32 v = true)
      (hq : Wahl S fe (aluD o D t d) true rest q) :
      Wahl S fe D fl (.pilot (.movImm64 t v) :: .pilot pb :: rest)
        (.compact (aluImmWahl o d (BitVec.ofNat 32 v.toNat)) :: q)
  /-- A data-moving pilot row becomes its compact form (`kompaktWahl`). -/
  | kompakt (D : List Register) (fl : Bool) (b : Befehl) (cb : CompactBefehl)
      (rest q : List Instr) (hk : kompaktDaten b = some cb)
      (hf : frei D (liestP b) = true) (hq : Wahl S fe (nachD D b) fl rest q) :
      Wahl S fe D fl (.pilot b :: rest) (.compact cb :: q)
  /-- A straight-line pilot row is kept. -/
  | behalte (D : List Register) (fl : Bool) (b : Befehl) (rest q : List Instr)
      (hb : behaltbar b = true) (hf : frei D (liestP b) = true)
      (hq : Wahl S fe (nachD D b) (nachFl fl b) rest q) :
      Wahl S fe D fl (.pilot b :: rest) (.pilot b :: q)
  /-- An immediate shift is kept. -/
  | schiebe (D : List Register) (fl : Bool) (r : ShiftRichtung) (dst : Register)
      (k : Nat) (rest q : List Instr) (hk : k < 256) (hf : frei D [dst] = true)
      (hq : Wahl S fe (entferne D dst) (fl || (k % 64 != 0)) rest q) :
      Wahl S fe D fl (.shift (.imm r dst k) :: rest) (.shift (.imm r dst k) :: q)
  /-- A SETcc is kept; it READS the flags, so they must agree here. -/
  | setcc (D : List Register) (c : Bedingung) (dst : Register) (rest q : List Instr)
      (hf : frei D [dst] = true) (hq : Wahl S fe (entferne D dst) true rest q) :
      Wahl S fe D true (.cond (.setcc c dst) :: rest) (.cond (.setcc c dst) :: q)

/-- Left-biased choice (the first rule that applies wins). -/
def oder : Option (List Instr) → Option (List Instr) → Option (List Instr)
  | some x, _ => some x
  | none, y => y

theorem oder_some (a b : Option (List Instr)) (q : List Instr) (h : oder a b = some q) :
    a = some q ∨ b = some q := by
  cases a with
  | none => exact Or.inr h
  | some x => exact Or.inl h

/-- THE DECIDED SELECTOR. Tries, at every position, the LEA rewrite, the
    ALU-immediate rewrite, the compact data rewrite, and finally keeping
    the row; a rewrite whose consequences fail later (a flag reader or a
    live-flags end after a dropped flag write, a read of a register that
    now differs) is abandoned for the next alternative. `none` is a
    refusal: the caller keeps the original program. Control flow has no
    rule, so a program with a jump is always refused. -/
def sel (S : List Register) (fe : Bool) :
    List Register → Bool → List Instr → Option (List Instr)
  | _, fl, [] => if fe = true ∧ fl = false then none else some []
  | D, fl, i :: rest =>
    oder
      (match i, rest with
        | .pilot (.movReg64 d b), .shift (.imm .shl d' k) :: .pilot (.addReg64 d'' a) :: rest3 =>
          match skalaVon k with
          | some sc =>
            if d' = d ∧ d'' = d ∧ d ≠ a ∧ b ≠ .rsp ∧ frei D [a, b] = true then
              (sel S fe (entferne D d) false rest3).map
                (Instr.core (.lea64 d a (some (b, sc)) 0) :: ·)
            else none
          | none => none
        | _, _ => none)
    (oder
      (match i, rest with
        | .pilot (.movImm64 t v), .pilot pb :: rest2 =>
          match aluVon pb with
          | some (o, d, t') =>
            if t' = t ∧ t ≠ d ∧ S.contains t = true ∧ frei D [d] = true ∧
                passtSx32 v = true then
              (sel S fe (aluD o D t d) true rest2).map
                (Instr.compact (aluImmWahl o d (BitVec.ofNat 32 v.toNat)) :: ·)
            else none
          | none => none
        | _, _ => none)
    (oder
      (match i with
        | .pilot b =>
          match kompaktDaten b with
          | some cb =>
            if frei D (liestP b) = true then
              (sel S fe (nachD D b) fl rest).map (Instr.compact cb :: ·)
            else none
          | none => none
        | _ => none)
      (match i with
        | .pilot b =>
          if behaltbar b = true ∧ frei D (liestP b) = true then
            (sel S fe (nachD D b) (nachFl fl b) rest).map (Instr.pilot b :: ·)
          else none
        | .shift (.imm r dst k) =>
          if k < 256 ∧ frei D [dst] = true then
            (sel S fe (entferne D dst) (fl || (k % 64 != 0)) rest).map
              (Instr.shift (.imm r dst k) :: ·)
          else none
        | .cond (.setcc c dst) =>
          if fl = true ∧ frei D [dst] = true then
            (sel S fe (entferne D dst) true rest).map (Instr.cond (.setcc c dst) :: ·)
          else none
        | _ => none)))

/-- The top-level selector: start with full agreement. -/
def waehle (S : List Register) (fe : Bool) (p : List Instr) : Option (List Instr) :=
  sel S fe [] true p

/-! ## 5. Correctness. -/

/-- The selector's answer is a derivation of the rule relation. -/
theorem sel_wahl (S : List Register) (fe : Bool) :
    ∀ (p : List Instr) (D : List Register) (fl : Bool) (q : List Instr),
      sel S fe D fl p = some q → Wahl S fe D fl p q
  | [], D, fl, q, h => by
    unfold sel at h
    split at h
    · cases h
    · rename_i hn
      cases h
      refine Wahl.ende D fl (fun hfe => ?_)
      cases hfl : fl
      · exact absurd ⟨hfe, hfl⟩ hn
      · rfl
  | i :: rest, D, fl, q, h => by
    unfold sel at h
    rcases oder_some _ _ _ h with hA | hBCE
    · split at hA
      · rename_i d b d' k d'' a rest3
        split at hA
        · rename_i sc hsk
          split at hA
          · rename_i hc
            obtain ⟨h1, h2, hda, hb, hf⟩ := hc
            subst d' d''
            obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hA
            exact Wahl.lea D fl d b a k sc rest3 q' hsk hda hb hf
              (sel_wahl S fe rest3 _ _ q' hq')
          · cases hA
        · cases hA
      · cases hA
    · rcases oder_some _ _ _ hBCE with hB | hCE
      · split at hB
        · rename_i t v pb rest2
          split at hB
          · rename_i o d t' hav
            split at hB
            · rename_i hc
              obtain ⟨h1, htd, hS, hf, hv⟩ := hc
              subst t'
              obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hB
              exact Wahl.alu D fl t v pb o d rest2 q' hav htd
                (List.contains_iff_mem.mp hS) hf hv (sel_wahl S fe rest2 _ _ q' hq')
            · cases hB
          · cases hB
        · cases hB
      · rcases oder_some _ _ _ hCE with hC | hE
        · split at hC
          · rename_i b
            split at hC
            · rename_i cb hk
              split at hC
              · rename_i hf
                obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hC
                exact Wahl.kompakt D fl b cb rest q' hk hf (sel_wahl S fe rest _ _ q' hq')
              · cases hC
            · cases hC
          · cases hC
        · split at hE
          · rename_i b
            split at hE
            · rename_i hc
              obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hE
              exact Wahl.behalte D fl b rest q' hc.1 hc.2 (sel_wahl S fe rest _ _ q' hq')
            · cases hE
          · rename_i r dst k
            split at hE
            · rename_i hc
              obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hE
              exact Wahl.schiebe D fl r dst k rest q' hc.1 hc.2
                (sel_wahl S fe rest _ _ q' hq')
            · cases hE
          · rename_i c dst
            split at hE
            · rename_i hc
              obtain ⟨hfl, hf⟩ := hc
              subst hfl
              obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hE
              exact Wahl.setcc D c dst rest q' hf (sel_wahl S fe rest _ _ q' hq')
            · cases hE
          · cases hE

/-- A run of `x :: xs` is one step, then the rest. -/
theorem laufI_cons (x : InstrDecoded) (xs : List InstrDecoded) (s : Zustand) :
    laufI (x :: xs) s = (stepI x s).bind (laufI xs) := by
  simp only [laufI]
  cases stepI x s <;> rfl

/-- The final agreement: registers outside the scratch list, all memory,
    and the flags if they are live at the end. -/
def EndGl (S : List Register) (fe : Bool) (s1 s2 : Zustand) : Prop :=
  (∀ r, r ∉ S → s1.register r = s2.register r) ∧ s1.speicher = s2.speicher ∧
    (fe = true → s1.flags = s2.flags)

theorem kompaktDaten_behaltbar (b : Befehl) (cb : CompactBefehl)
    (h : kompaktDaten b = some cb) : behaltbar b = true ∧ setztFlags b = false := by
  cases b <;> simp_all [kompaktDaten, behaltbar, setztFlags]

theorem aluVon_laenge (pb : Befehl) (o : AluOp) (d t : Register)
    (h : aluVon pb = some (o, d, t)) : canonI (.pilot pb) = ⟨.pilot pb, 3⟩ := by
  cases pb <;> simp [aluVon] at h <;> rfl

/-- SELECTION CORRECTNESS over a derivation: for every pair of states that
    agree outside a difference set inside the scratch list, the original
    and the selected program refuse together or end in states that agree
    outside the scratch list, on memory, and on the flags if live. -/
theorem wahl_korrekt (S : List Register) (fe : Bool) (D : List Register) (fl : Bool)
    (p q : List Instr) (hw : Wahl S fe D fl p q) :
    ∀ (s1 s2 : Zustand), (∀ r ∈ D, r ∈ S) → Gl D fl s1 s2 →
      OptRel (EndGl S fe) (laufI (p.map canonI) s1) (laufI (q.map canonI) s2) := by
  induction hw with
  | ende D fl hfl =>
    intro s1 s2 hDS hg
    refine ⟨fun r hr => hg.1 r (fun hm => hr (hDS r hm)), hg.2.1,
      fun hfe => hg.2.2 (hfl hfe)⟩
  | lea D fl d b a k sc rest q hk hda hb hf hq ih =>
    intro s1 s2 hDS hg
    obtain ⟨hsc, hk0, _⟩ := skalaVon_spec k sc hk
    have ea := gl_reg D fl s1 s2 hg _ hf a (by simp)
    have eb := gl_reg D fl s1 s2 hg _ hf b (by simp)
    simp only [List.map_cons, laufI_cons]
    -- the three original steps
    have h1 : stepI (canonI (.pilot (.movReg64 d b))) s1 =
        some (schrittRegister s1 (ripNach s1.rip 3) s1.flags d (s1.register b)) :=
      schritt_movReg64 ⟨.movReg64 d b, 3⟩ s1 d b rfl rfl
    rw [h1]
    simp only [Option.bind_some]
    generalize hA : schrittRegister s1 (ripNach s1.rip 3) s1.flags d (s1.register b) = sA
    rw [laufI_cons]
    have hlen : ((canonI (.shift (.imm .shl d k))).laenge ==
        shiftLaenge (.imm .shl d k)) = true := by
      simp [canonI, encodeI, encodeShift_laenge]
    have h2 := shiftSchritt_weiter ⟨.imm .shl d k, _⟩ sA hlen hk0
    rw [show stepI (canonI (.shift (.imm .shl d k))) sA =
      shiftSchritt ⟨.imm .shl d k, (canonI (.shift (.imm .shl d k))).laenge⟩ sA from rfl,
      h2]
    simp only [Option.bind_some]
    generalize hB : schrittRegister sA _ _ _ _ = sB
    rw [laufI_cons]
    have h3 : stepI (canonI (.pilot (.addReg64 d a))) sB =
        some (schrittRegister sB (ripNach sB.rip 3)
          (add64 (sB.register d) (sB.register a)).2 d
          (add64 (sB.register d) (sB.register a)).1) :=
      schritt_addReg64 ⟨.addReg64 d a, 3⟩ sB d a rfl rfl
    rw [h3]
    simp only [Option.bind_some]
    -- the one selected step
    have h4 : stepI (canonI (.core (.lea64 d a (some (b, sc)) 0))) s2 =
        some (schrittRegister s2 (ripNach s2.rip 8) s2.flags d
          (leaVal s2 a (some (b, sc)) 0)) :=
      core_lea64 ⟨.lea64 d a (some (b, sc)) 0, 8⟩ s2 d a _ 0 rfl rfl
    rw [h4]
    simp only [Option.bind_some]
    apply ih _ _ (entferne_teil D S d hDS)
    -- agreement after the block
    have hBd : sB.register d = shlB .b64 (s1.register b) k := by
      rw [← hB, ← hA]
      show regSet _ d _ d = _
      rw [regSet_gleich]
      show shlB .b64 (regSet s1.register d (s1.register b) d) k = _
      rw [regSet_gleich]
    have hBr : ∀ r, r ≠ d → sB.register r = s1.register r := by
      intro r hr
      rw [← hB, ← hA]
      show regSet (regSet s1.register d _) d _ r = _
      rw [regSet_fremd _ _ _ _ hr, regSet_fremd _ _ _ _ hr]
    have hBm : sB.speicher = s1.speicher := by rw [← hB, ← hA]; rfl
    refine ⟨fun r hr => ?_, by show sB.speicher = s2.speicher; rw [hBm]; exact hg.2.1,
      fun h => by cases h⟩
    by_cases hrd : r = d
    · subst hrd
      show regSet sB.register r _ r = regSet s2.register r _ r
      rw [regSet_gleich, regSet_gleich, hBd, hBr a (Ne.symm hda)]
      show shlB .b64 (s1.register b) k + s1.register a =
        s2.register a + shlB .b64 (s2.register b) (scaleShift sc) + dispWort 0
      rw [hsc, ea, eb, show dispWort (0 : BitVec 32) = 0#64 from by decide,
        BitVec.add_zero]
      exact BitVec.add_comm _ _
    · show regSet sB.register d _ r = regSet s2.register d _ r
      rw [regSet_fremd _ _ _ _ hrd, regSet_fremd _ _ _ _ hrd, hBr r hrd]
      exact hg.1 r (nicht_in_entferne D d r hr hrd)
  | alu D fl t v pb o d rest q ha htd hS hf hv hq ih =>
    intro s1 s2 hDS hg
    have ed := gl_reg D fl s1 s2 hg _ hf d (by simp)
    simp only [List.map_cons, laufI_cons]
    have h1 : stepI (canonI (.pilot (.movImm64 t v))) s1 =
        some (schrittRegister s1 (ripNach s1.rip 10) s1.flags t v) :=
      schritt_movImm64 ⟨.movImm64 t v, 10⟩ s1 t v rfl rfl
    rw [h1]
    simp only [Option.bind_some]
    generalize hA : schrittRegister s1 (ripNach s1.rip 10) s1.flags t v = sA
    rw [laufI_cons]
    rw [aluVon_laenge pb o d t ha]
    have h2 := schritt_aluVon pb o d t ha 3 rfl sA
    rw [show stepI ⟨.pilot pb, 3⟩ sA = schritt ⟨pb, 3⟩ sA from rfl, h2]
    simp only [Option.bind_some]
    have h3 := schrittC_aluImmWahl o d v hv
      (encodeI (.compact (aluImmWahl o d (BitVec.ofNat 32 v.toNat)))).length
      (laengeOk_encodeI _) s2
    rw [show stepI (canonI (.compact (aluImmWahl o d (BitVec.ofNat 32 v.toNat)))) s2 =
      schrittC ⟨aluImmWahl o d (BitVec.ofNat 32 v.toNat),
        (encodeI (.compact (aluImmWahl o d (BitVec.ofNat 32 v.toNat)))).length⟩ s2 from rfl,
      h3]
    simp only [Option.bind_some]
    have hAt : sA.register t = v := by rw [← hA]; exact regSet_gleich _ _ _
    have hAd : sA.register d = s2.register d := by
      rw [← hA]
      show regSet s1.register t v d = _
      rw [regSet_fremd _ _ _ _ (Ne.symm htd)]
      exact ed
    have hgA : Gl (t :: D) fl sA s2 := by
      refine ⟨fun r hr => ?_, by rw [← hA]; exact hg.2.1, fun h => by rw [← hA]; exact hg.2.2 h⟩
      have hrt : r ≠ t := fun e => hr (e ▸ List.mem_cons_self)
      rw [← hA]
      show regSet s1.register t v r = _
      rw [regSet_fremd _ _ _ _ hrt]
      exact hg.1 r (fun hm => hr (List.mem_cons_of_mem _ hm))
    rw [hAt]
    apply ih _ _ ?_ (gl_ergAlu (t :: D) fl sA s2 hgA o d v _ _ hAd)
    unfold aluD
    split
    · exact entferne_teil (t :: D) S d (fun r hr => by
        rcases List.mem_cons.mp hr with e | e
        · exact e ▸ hS
        · exact hDS r e)
    · intro r hr
      rcases List.mem_cons.mp hr with e | e
      · exact e ▸ hS
      · exact hDS r e
  | kompakt D fl b cb rest q hk hf hq ih =>
    intro s1 s2 hDS hg
    obtain ⟨hb, hfl⟩ := kompaktDaten_behaltbar b cb hk
    simp only [List.map_cons, laufI_cons]
    have hs := schritt_gl b hb (encode b).length D fl s1 s2 hg hf
    have hfl' : nachFl fl b = fl := by simp [nachFl, hfl]
    rw [hfl'] at hs
    have hw := kompakt_wirkung b cb hk s2 (encode b).length (encodeC cb).length
      (laengeOk_encodeI (.pilot b)) (laengeOk_encodeI (.compact cb))
    have hs' := optRel_ohneRip _ _ _ _ _ hs hw.symm
    apply optRel_bind _ _ _ _ _ _ hs'
    intro a c hac
    exact ih a c (nachD_teil D S b hDS) hac
  | behalte D fl b rest q hb hf hq ih =>
    intro s1 s2 hDS hg
    simp only [List.map_cons, laufI_cons]
    apply optRel_bind _ _ _ _ _ _ (schritt_gl b hb (encode b).length D fl s1 s2 hg hf)
    intro a c hac
    exact ih a c (nachD_teil D S b hDS) hac
  | schiebe D fl r dst k rest q hk hf hq ih =>
    intro s1 s2 hDS hg
    simp only [List.map_cons, laufI_cons]
    apply optRel_bind _ _ _ _ _ _
      (shift_gl r dst k _ D fl s1 s2 hg (frei_mem D [dst] hf dst (by simp)))
    intro a c hac
    exact ih a c (entferne_teil D S dst hDS) hac
  | setcc D c dst rest q hf hq ih =>
    intro s1 s2 hDS hg
    simp only [List.map_cons, laufI_cons]
    exact optRel_bind _ _ _ _ _ _
      (setcc_gl c dst (encodeI (.cond (.setcc c dst))).length D s1 s2 hg (frei_mem D [dst] hf dst (by simp)))
      (fun a c' hac => ih a c' (entferne_teil D S dst hDS) hac)

/-- MAIN THEOREM (selection correctness). If the decided selector accepts
    `p` with scratch list `S` and end-liveness `fe`, then from ANY state
    the original and the selected program refuse together, or both
    succeed with final states that agree on every register outside `S`,
    on all of memory, and -- if `fe` -- on all flags. -/
theorem waehle_korrekt (S : List Register) (fe : Bool) (p q : List Instr)
    (h : waehle S fe p = some q) (s : Zustand) :
    OptRel (EndGl S fe) (laufI (p.map canonI) s) (laufI (q.map canonI) s) :=
  wahl_korrekt S fe [] true p q (sel_wahl S fe p [] true q h) s s
    (fun _ h => by cases h) ⟨fun _ _ => rfl, rfl, fun _ => rfl⟩

/-! ## 6. Shape of the selected program: canonical, straight-line, shorter. -/

theorem progBytes_cons_laenge (i : Instr) (is : List Instr) :
    (progBytes (i :: is)).length = (encodeI i).length + (progBytes is).length := by
  simp [progBytes]

theorem aluImmWahl_kanonisch (o : AluOp) (d : Register) (imm : BitVec 32) :
    kanonischI (.compact (aluImmWahl o d imm)) = true ∧
      faelltDurchI (.compact (aluImmWahl o d imm)) = true ∧
      (encodeI (.compact (aluImmWahl o d imm))).length ≤ 7 := by
  unfold aluImmWahl
  split
  · refine ⟨rfl, rfl, ?_⟩
    rw [show (encodeI (.compact (.aluImm8 o d (disp8Of imm)))).length = 4 from rfl]
    decide
  · exact ⟨rfl, rfl, Nat.le_of_eq (show (encodeC (.aluImm32 o d imm)).length = 7 from rfl)⟩

theorem kompaktDaten_form (b : Befehl) (cb : CompactBefehl) (h : kompaktDaten b = some cb) :
    kanonischI (.compact cb) = true ∧ faelltDurchI (.compact cb) = true ∧
      (encodeC cb).length ≤ (encode b).length := by
  cases b with
  | movImm64 d v =>
    simp only [kompaktDaten, kompaktWahl] at h
    split at h
    · cases h
      refine ⟨rfl, rfl, ?_⟩
      simp only [encodeC, encode, leBytes32, leBytes64]
      split <;> simp
    · split at h
      · cases h
        exact ⟨rfl, rfl, by simp [encodeC, encode, leBytes32, leBytes64]⟩
      · cases h
  | load64 d base disp =>
    simp only [kompaktDaten, kompaktWahl] at h
    split at h
    · rename_i hd0
      cases h
      obtain ⟨_, h1, h2⟩ := of_decide_eq_true hd0
      refine ⟨by simp [kanonischI, h1, h2], rfl, ?_⟩
      simp only [encodeC, encode, leBytes32]
      split <;> simp
    · split at h
      · cases h
        refine ⟨rfl, rfl, ?_⟩
        simp only [encodeC, encode, leBytes32]
        split <;> simp
      · cases h
  | store64 base src disp =>
    simp only [kompaktDaten, kompaktWahl] at h
    split at h
    · rename_i hd0
      cases h
      obtain ⟨_, h1, h2⟩ := of_decide_eq_true hd0
      refine ⟨by simp [kanonischI, h1, h2], rfl, ?_⟩
      simp only [encodeC, encode, leBytes32]
      split <;> simp
    · split at h
      · cases h
        refine ⟨rfl, rfl, ?_⟩
        simp only [encodeC, encode, leBytes32]
        split <;> simp
      · cases h
  | _ => simp [kompaktDaten] at h

theorem behaltbar_form (b : Befehl) (hb : behaltbar b = true) :
    kanonischI (.pilot b) = true ∧ faelltDurchI (.pilot b) = true := by
  cases b <;> first | exact ⟨rfl, rfl⟩ | simp [behaltbar] at hb

/-- The selected program is canonical and straight-line, the original is
    straight-line, and the selected program is NOT LONGER in bytes. -/
theorem wahl_form (S : List Register) (fe : Bool) (D : List Register) (fl : Bool)
    (p q : List Instr) (hw : Wahl S fe D fl p q) :
    (∀ i ∈ q, kanonischI i = true ∧ faelltDurchI i = true) ∧
      (∀ i ∈ p, faelltDurchI i = true) ∧
      (progBytes q).length ≤ (progBytes p).length := by
  induction hw with
  | ende D fl hfl => exact ⟨by simp, by simp, by simp [progBytes]⟩
  | lea D fl d b a k sc rest q hk hda hb hf hq ih =>
    obtain ⟨ihq, ihp, ihl⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      rcases List.mem_cons.mp hi with e | e
      · subst e
        exact ⟨by simp [kanonischI, coreValid, leaIndexOk, hb], rfl⟩
      · exact ihq i e
    · intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with e | e | e | e
      · subst e; rfl
      · subst e; rfl
      · subst e; rfl
      · exact ihp i e
    · simp only [progBytes_cons_laenge]
      have : (encodeI (.core (.lea64 d a (some (b, sc)) 0))).length = 8 := by
        simp [encodeI, encodeCore_laenge, coreLen]
      have h1 : (encodeI (.pilot (.movReg64 d b))).length = 3 := rfl
      have h2 : (encodeI (.shift (.imm .shl d k))).length = 4 := rfl
      have h3 : (encodeI (.pilot (.addReg64 d a))).length = 3 := rfl
      omega
  | alu D fl t v pb o d rest q ha htd hS hf hv hq ih =>
    obtain ⟨ihq, ihp, ihl⟩ := ih
    obtain ⟨hk, hfd, hlen⟩ := aluImmWahl_kanonisch o d (BitVec.ofNat 32 v.toNat)
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      rcases List.mem_cons.mp hi with e | e
      · subst e; exact ⟨hk, hfd⟩
      · exact ihq i e
    · intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with e | e | e
      · subst e; rfl
      · subst e
        cases pb <;> first | rfl | simp [aluVon] at ha
      · exact ihp i e
    · simp only [progBytes_cons_laenge]
      have h1 : (encodeI (.pilot (.movImm64 t v))).length = 10 := by
        simp [encodeI, encode, leBytes64]
      have h2 : (encodeI (.pilot pb)).length = 3 := by
        have := aluVon_laenge pb o d t ha
        simp only [canonI, InstrDecoded.mk.injEq] at this
        exact this.2
      omega
  | kompakt D fl b cb rest q hk hf hq ih =>
    obtain ⟨ihq, ihp, ihl⟩ := ih
    obtain ⟨hkk, hfd, hlen⟩ := kompaktDaten_form b cb hk
    obtain ⟨hb, _⟩ := kompaktDaten_behaltbar b cb hk
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      rcases List.mem_cons.mp hi with e | e
      · subst e; exact ⟨hkk, hfd⟩
      · exact ihq i e
    · intro i hi
      rcases List.mem_cons.mp hi with e | e
      · subst e; exact (behaltbar_form b hb).2
      · exact ihp i e
    · simp only [progBytes_cons_laenge]
      show (encodeC cb).length + _ ≤ (encode b).length + _
      omega
  | behalte D fl b rest q hb hf hq ih =>
    obtain ⟨ihq, ihp, ihl⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      rcases List.mem_cons.mp hi with e | e
      · subst e; exact behaltbar_form b hb
      · exact ihq i e
    · intro i hi
      rcases List.mem_cons.mp hi with e | e
      · subst e; exact (behaltbar_form b hb).2
      · exact ihp i e
    · simp only [progBytes_cons_laenge]
      omega
  | schiebe D fl r dst k rest q hk hf hq ih =>
    obtain ⟨ihq, ihp, ihl⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      rcases List.mem_cons.mp hi with e | e
      · subst e; exact ⟨by simp [kanonischI, hk], rfl⟩
      · exact ihq i e
    · intro i hi
      rcases List.mem_cons.mp hi with e | e
      · subst e; rfl
      · exact ihp i e
    · simp only [progBytes_cons_laenge]
      omega
  | setcc D c dst rest q hf hq ih =>
    obtain ⟨ihq, ihp, ihl⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      rcases List.mem_cons.mp hi with e | e
      · subst e; exact ⟨rfl, rfl⟩
      · exact ihq i e
    · intro i hi
      rcases List.mem_cons.mp hi with e | e
      · subst e; rfl
      · exact ihp i e
    · simp only [progBytes_cons_laenge]
      omega

/-- RIP at the end of a straight-line run: the start plus the byte length
    of the program (each program has its OWN end address). -/
theorem laufI_rip (is : List Instr) (hf : ∀ i ∈ is, faelltDurchI i = true)
    (s s' : Zustand) (h : laufI (is.map canonI) s = some s') :
    s'.rip = ripNach s.rip (progBytes is).length := by
  induction is generalizing s with
  | nil =>
    simp only [List.map_nil, laufI, Option.some.injEq] at h
    subst h
    simp [progBytes, ripNach]
  | cons i rest ih =>
    simp only [List.map_cons, laufI_cons] at h
    cases hs : stepI (canonI i) s with
    | none => rw [hs] at h; cases h
    | some s1 =>
      rw [hs] at h
      simp only [Option.bind_some] at h
      have hr := (stepI_rahmen i _ s s1 hs).2 (hf i (by simp))
      rw [ih (fun j hj => hf j (by simp [hj])) s1 h, hr, progBytes_cons_laenge]
      unfold ripNach
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- SELECTION, COMPLETE STATEMENT. When the selector accepts `p`:
    the selected program `q` is canonical, straight-line and not longer in
    bytes; from any state both programs refuse together or both succeed,
    and then the final states agree outside the scratch list, on memory,
    on the flags if live, and each RIP is its own start plus its own byte
    length. -/
theorem waehle_lauf (S : List Register) (fe : Bool) (p q : List Instr)
    (h : waehle S fe p = some q) (s : Zustand) :
    (∀ i ∈ q, kanonischI i = true ∧ faelltDurchI i = true) ∧
      (progBytes q).length ≤ (progBytes p).length ∧
      ((laufI (p.map canonI) s = none ∧ laufI (q.map canonI) s = none) ∨
        ∃ s1 s2, laufI (p.map canonI) s = some s1 ∧ laufI (q.map canonI) s = some s2 ∧
          EndGl S fe s1 s2 ∧
          s1.rip = ripNach s.rip (progBytes p).length ∧
          s2.rip = ripNach s.rip (progBytes q).length) := by
  have hw := sel_wahl S fe p [] true q h
  obtain ⟨hq, hp, hl⟩ := wahl_form S fe [] true p q hw
  refine ⟨hq, hl, ?_⟩
  have hk := waehle_korrekt S fe p q h s
  cases h1 : laufI (p.map canonI) s with
  | none =>
    cases h2 : laufI (q.map canonI) s with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some s2 => rw [h1, h2] at hk; exact absurd hk id
  | some s1 =>
    cases h2 : laufI (q.map canonI) s with
    | none => rw [h1, h2] at hk; exact absurd hk id
    | some s2 =>
      rw [h1, h2] at hk
      exact Or.inr ⟨s1, s2, rfl, rfl, hk, laufI_rip p hp s s1 h1,
        laufI_rip q (fun i hi => (hq i hi).2) s s2 h2⟩

/-- BYTE-LEVEL COROLLARY: the selected program, laid out by `encodeI` at
    RIP in executable memory under W^X, runs from ACTUAL bytes exactly as
    `laufI` runs it (`laufBytesI_layout`, whose premises the selector
    discharges). -/
theorem waehle_bytes (S : List Register) (fe : Bool) (p q : List Instr)
    (h : waehle S fe p = some q) (s : Zustand) (hwx : WX s.speicher)
    (hcode : CodeAt s.speicher s.rip (progBytes q)) :
    laufBytesI q.length s = ausgangVon (laufI (q.map canonI) s) := by
  obtain ⟨hq, _, _⟩ := wahl_form S fe [] true p q (sel_wahl S fe p [] true q h)
  exact laufBytesI_layout q s (fun i hi => (hq i hi).1) (fun i hi => (hq i hi).2) hwx hcode

/- CUTS (what is NOT proved here):
   - STRAIGHT-LINE ONLY. No rule admits control flow; a program with a jump,
     branch, call, return or compact rel8 jump is refused (`sel` answers
     `none`), and so is any row outside the admitted input language
     (pilot register/load/store rows, immediate shifts, SETcc). Selection
     across basic blocks needs a layout pass that re-validates every jump
     target after the shrink (branch relaxation); none is done here, and
     `kompaktWahl`'s jump arms are never used.
   - RIP is excluded from the agreement: the selected program ends at its
     own start plus its own (shorter) byte length (`laufI_rip`). Nothing in
     the admitted language reads RIP; a RIP-relative or call/return row
     would break this and is not admitted.
   - Flag deadness is all-or-nothing: `fl` tracks whether ALL flags agree,
     and SETcc demands it even though it reads only the flags of
     `FlagDependencies.liestFlag`. A finer per-flag check is possible but
     not done. Flags at the end are compared only if the caller declares
     them live (`fe = true`).
   - The scratch list `S` is the caller's declaration that those registers
     are dead after the program; it is NOT checked against any code that
     follows the program. Inside the program, a later read of a register
     that differs is detected and the rewrite abandoned.
   - The decided selector is a backtracking search (first applicable rule,
     abandoned when a later check fails); it is correct for every input
     (`waehle_korrekt`) but neither optimal nor linear-time in the worst
     case. No completeness or cost claim is made.
   - The LEA rewrite needs a nonzero shift count 1..3 (scale 2/4/8); the
     ALU rewrite covers ADD/SUB/XOR/CMP only (AND/OR have no pilot
     register form, `CompactForms.aluPilotBefehl`). No rewrite uses
     MOVZX/MOVSX, TEST, NOT/NEG or the shift family beyond keeping it.
   - Agreement is sequential over one `Zustand`; no TSO, concurrency,
     timing or source-correspondence claim. The byte-level corollary is
     `laufBytesI_layout` for the selected program alone; comparing the two
     byte runs from their two differently-coded memories is done only on
     the witness (`ISASelectWitnesses.lean`).
-/

#print axioms optRel_bind
#print axioms nicht_in_entferne
#print axioms entferne_teil
#print axioms frei_mem
#print axioms gl_reg
#print axioms gl_schrittRegister
#print axioms nachD_teil
#print axioms schritt_gl
#print axioms setcc_gl
#print axioms shift_gl
#print axioms gl_ohneRip
#print axioms optRel_ohneRip
#print axioms kompakt_wirkung
#print axioms schritt_aluVon
#print axioms schrittC_aluImmWahl
#print axioms gl_ergAlu
#print axioms skalaVon_spec
#print axioms oder_some
#print axioms sel_wahl
#print axioms laufI_cons
#print axioms kompaktDaten_behaltbar
#print axioms aluVon_laenge
#print axioms wahl_korrekt
#print axioms waehle_korrekt
#print axioms progBytes_cons_laenge
#print axioms aluImmWahl_kanonisch
#print axioms kompaktDaten_form
#print axioms behaltbar_form
#print axioms wahl_form
#print axioms laufI_rip
#print axioms waehle_lauf
#print axioms waehle_bytes

end Gabbro.Grammatik.X86
