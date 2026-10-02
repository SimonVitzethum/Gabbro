/-
  File:      Grammatik/X86/ISARelax.lean
  Subject:   Branch relaxation and cross-block selection over the unified
             instruction set: a program with SYMBOLIC branch targets (labels
             are instruction indices) is laid out from encoded lengths, every
             jump is resolved to rel32 or rel8 by the bounded DESIGN-§2B
             relaxation (start all wide, at most `N` compression rounds,
             narrow a branch only if the WHOLE resulting layout validates),
             and the resolved byte image, laid out in executable memory, is
             proved to run under `laufBytesI` exactly as the labelled
             program's semantics (every jump goes to the address of its
             label). This DERIVES the trace premise that `laufBytesI_spur`
             assumes for programs with control flow (loops, branches).

  Reused, not redefined: `Instr`/`stepI`/`canonI`/`encodeI`/`kanonischI`
  (`ISA.lean`), `byteschrittI`/`laufBytesI`/`byteschrittI_kanonisch`/
  `progBytes`/`CodeAt`/`WX`/`stepI_rahmen`/`faelltDurchI`/`geholt_codeAt`/
  `codeAt_links`/`codeAt_rechts`/`codeAt_schutz`/`wx_schutz`/`ausgangVon`
  (`ISAExecution.lean`), the jump step equations `schritt_jump32`,
  `schritt_jumpIf32_*` (`Ausfuehrung.lean`) and `schrittC_jump8`,
  `schrittC_jumpIf8_*`, `rel8FromWort`/`passtRel8Wort` (`CompactForms.lean`),
  and the decided selector `sel`/`Wahl`/`wahl_korrekt`/`Gl`/`EndGl`/`OptRel`
  (`ISASelect.lean`). The pilot `jump32`/`jumpIf32` and compact
  `jump8`/`jumpIf8` are the ONLY jump encodings; no new instruction, step or
  decoder exists here.

  Contents:
    §1 labelled programs `LInstr`, encoded lengths, the layout `off`/`adrL`,
       resolution `aufloesen`, the decided validator `layoutOk`, the image
       `bild`;
    §2 bounded relaxation `relax` and `relax_ok` (the answer validates);
    §3 the labelled semantics `stepL`/`laufL` (jumps go to label addresses);
    §4 THE LAYOUT THEOREM WITH CONTROL FLOW `laufBytesL`: the byte run of
       the image IS the labelled run, outcome for outcome;
    §5 basic blocks, block semantics `laufB`, the flattening `flach` and the
       simulation `laufB_flach`;
    §6 per-block selection `waehleB` (`sel` on each block body, labels kept)
       and its agreement theorem `waehleB_korrekt`;
    §7 the combined statement `waehleB_relax_bytes`: select per block,
       flatten, relax, lay out; the byte run agrees with the ORIGINAL
       block program outside the scratch list, at the same block label.
  Witnesses and poison probes: `ISARelaxWitnesses.lean`.
-/
import Grammatik.X86.ISASelect

namespace Gabbro.Grammatik.X86

/-! ## 1. Labelled programs, layout, resolution, validation. -/

/-- A labelled instruction: an ordinary unified instruction (must fall
    through), or a jump whose target is a LABEL (an instruction index;
    the index equal to the program length is the program end). -/
inductive LInstr where
  | op (i : Instr)
  | jmp (ziel : Nat)
  | jcc (c : Bedingung) (ziel : Nat)
  deriving DecidableEq, Repr

/-- A labelled program. -/
abbrev LProg := List LInstr

/-- Encoded length of a labelled instruction at a chosen width
    (`kurz = true`: rel8, 2 bytes; otherwise rel32, 5 or 6 bytes). -/
def lenL (kurz : Bool) : LInstr → Nat
  | .op i => (encodeI i).length
  | .jmp _ => if kurz then 2 else 5
  | .jcc _ _ => if kurz then 2 else 6

/-- Encoded length of instruction `k` under the width vector `ws`
    (0 past the end). -/
def lenAt (ws : List Bool) (p : LProg) (k : Nat) : Nat :=
  match p[k]? with
  | some li => lenL (ws.getD k false) li
  | none => 0

/-- Byte offset of instruction `k` (and of label `k`): the sum of the
    encoded lengths before it. -/
def off (ws : List Bool) (p : LProg) (k : Nat) : Nat :=
  ((List.range k).map (lenAt ws p)).sum

theorem off_null (ws : List Bool) (p : LProg) : off ws p 0 = 0 := rfl

theorem off_succ (ws : List Bool) (p : LProg) (k : Nat) :
    off ws p (k + 1) = off ws p k + lenAt ws p k := by
  simp [off, List.range_succ]

/-- The address of label `k` when the program starts at `base`. -/
def adrL (base : Adresse) (ws : List Bool) (p : LProg) (k : Nat) : Adresse :=
  ripNach base (off ws p k)

/-- The displacement WORD from the end of instruction `k` (length `l`) to
    label `z`: recomputed from the layout, never reused across widths. -/
def dispW (ws : List Bool) (p : LProg) (k z l : Nat) : Wort :=
  BitVec.ofNat 64 (off ws p z) - BitVec.ofNat 64 (off ws p k + l)

/-- rel32 admission: the word round-trips through a sign-extended 32-bit
    displacement (the rel32 analogue of `CompactForms.passtRel8Wort`). -/
def passtRel32Wort (w : Wort) : Bool :=
  decide (dispWort (BitVec.ofNat 32 w.toNat) = w)

/-- Resolution of instruction `k`: ordinary instructions unchanged, jumps
    to the existing pilot rel32 or compact rel8 forms at the displacement
    the layout computes. -/
def aufloesen (ws : List Bool) (p : LProg) (k : Nat) : LInstr → Instr
  | .op i => i
  | .jmp z =>
    if ws.getD k false then .compact (.jump8 (rel8FromWort (dispW ws p k z 2)))
    else .pilot (.jump32 (BitVec.ofNat 32 (dispW ws p k z 5).toNat))
  | .jcc c z =>
    if ws.getD k false then .compact (.jumpIf8 c (rel8FromWort (dispW ws p k z 2)))
    else .pilot (.jumpIf32 c (BitVec.ofNat 32 (dispW ws p k z 6).toNat))

/-- Resolution by index (a dummy past the end, never reached). -/
def aufloesenAt (ws : List Bool) (p : LProg) (k : Nat) : Instr :=
  match p[k]? with
  | some li => aufloesen ws p k li
  | none => .pilot .ret

/-- The decided row check: ordinary rows are canonical and fall through;
    a jump's label lies inside the program (or at its end) and its
    displacement fits the chosen width. -/
def zeileOk (ws : List Bool) (p : LProg) (k : Nat) : LInstr → Bool
  | .op i => kanonischI i && faelltDurchI i
  | .jmp z => decide (z ≤ p.length) &&
      (if ws.getD k false then passtRel8Wort (dispW ws p k z 2)
       else passtRel32Wort (dispW ws p k z 5))
  | .jcc _ z => decide (z ≤ p.length) &&
      (if ws.getD k false then passtRel8Wort (dispW ws p k z 2)
       else passtRel32Wort (dispW ws p k z 6))

/-- THE LAYOUT VALIDATOR: every row passes `zeileOk` under `ws`. -/
def layoutOk (ws : List Bool) (p : LProg) : Bool :=
  (List.range p.length).all (fun k =>
    match p[k]? with
    | some li => zeileOk ws p k li
    | none => true)

theorem layoutOk_zeile (ws : List Bool) (p : LProg) (h : layoutOk ws p = true)
    (k : Nat) (li : LInstr) (hk : p[k]? = some li) : zeileOk ws p k li = true := by
  have hlt : k < p.length := by
    rcases Nat.lt_or_ge k p.length with h1 | h1
    · exact h1
    · rw [List.getElem?_eq_none h1] at hk; cases hk
  simp only [layoutOk, List.all_eq_true, List.mem_range] at h
  have := h k hlt
  rw [hk] at this
  exact this

/-- The resolved instruction list. -/
def aufgeloest (ws : List Bool) (p : LProg) : List Instr :=
  (List.range p.length).map (aufloesenAt ws p)

/-- The byte image: the resolved instructions back to back. -/
def bild (ws : List Bool) (p : LProg) : List Byte :=
  progBytes (aufgeloest ws p)

/-- A forged-image check: the given bytes are exactly the image of a
    validated layout. -/
def bildOk (ws : List Bool) (p : LProg) (bs : List Byte) : Bool :=
  layoutOk ws p && (bs == bild ws p)

theorem progBytes_append (xs ys : List Instr) :
    progBytes (xs ++ ys) = progBytes xs ++ progBytes ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [progBytes, ih]

theorem jump32_laenge (d : BitVec 32) : (encodeI (.pilot (.jump32 d))).length = 5 := by
  simp [encodeI, encode, length_leBytes32]

theorem jumpIf32_laenge (c : Bedingung) (d : BitVec 32) :
    (encodeI (.pilot (.jumpIf32 c d))).length = 6 := by
  simp [encodeI, encode, length_leBytes32]

/-- The resolved instruction has exactly the length the layout assumed. -/
theorem aufloesen_laenge (ws : List Bool) (p : LProg) (k : Nat) (li : LInstr) :
    (encodeI (aufloesen ws p k li)).length = lenL (ws.getD k false) li := by
  cases li with
  | op i => rfl
  | jmp z =>
    simp only [aufloesen, lenL]
    split
    · rfl
    · exact jump32_laenge _
  | jcc c z =>
    simp only [aufloesen, lenL]
    split
    · rfl
    · exact jumpIf32_laenge _ _

theorem aufloesenAt_laenge (ws : List Bool) (p : LProg) (k : Nat) (hk : k < p.length) :
    (encodeI (aufloesenAt ws p k)).length = lenAt ws p k := by
  unfold aufloesenAt lenAt
  rw [List.getElem?_eq_getElem hk]
  exact aufloesen_laenge ws p k _

/-- The layout offset IS the byte length of the image prefix. -/
theorem off_bild (ws : List Bool) (p : LProg) (k : Nat) (hk : k ≤ p.length) :
    off ws p k = (progBytes ((List.range k).map (aufloesenAt ws p))).length := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [off_succ, ih (by omega), List.range_succ, List.map_append, progBytes_append,
      List.length_append]
    simp only [List.map_cons, List.map_nil, progBytes, List.append_nil]
    rw [aufloesenAt_laenge ws p k (by omega)]

/-- PLACEMENT: if the image sits at `base`, the resolved instruction `k`
    sits at the address of label `k`. -/
theorem codeAt_zeile (m : Speicher) (base : Adresse) (ws : List Bool) (p : LProg)
    (h : CodeAt m base (bild ws p)) (k : Nat) (hk : k < p.length) :
    CodeAt m (adrL base ws p k) (encodeI (aufloesenAt ws p k)) := by
  have gen : ∀ n, k < n → n ≤ p.length →
      CodeAt m base (progBytes ((List.range n).map (aufloesenAt ws p))) →
      CodeAt m (adrL base ws p k) (encodeI (aufloesenAt ws p k)) := by
    intro n
    induction n with
    | zero => intro h0; omega
    | succ n ih =>
      intro hkn hn hc
      rw [List.range_succ, List.map_append, progBytes_append] at hc
      by_cases hkn' : k < n
      · exact ih hkn' (by omega) (codeAt_links _ _ _ _ hc)
      · have hke : k = n := by omega
        subst hke
        have hr := codeAt_rechts _ _ _ _ hc
        simp only [List.map_cons, List.map_nil, progBytes, List.append_nil] at hr
        unfold adrL
        rw [off_bild ws p k (by omega)]
        exact hr
  exact gen p.length hk (Nat.le_refl _) h

/-! ## 2. Bounded relaxation (DESIGN §2B). -/

/-- One compression attempt at index `k`: narrow it only if it is still
    wide AND the WHOLE layout with it narrowed validates. -/
def versuche (p : LProg) (ws : List Bool) (k : Nat) : List Bool :=
  if ws.getD k false = false ∧ layoutOk (ws.set k true) p = true then ws.set k true else ws

/-- One compression round over all indices, in order. -/
def runde (p : LProg) (ws : List Bool) : List Bool :=
  (List.range p.length).foldl (versuche p) ws

/-- At most `n` rounds; stops early at a fixpoint. -/
def relaxN (p : LProg) : Nat → List Bool → List Bool
  | 0, ws => ws
  | n + 1, ws =>
    let ws' := runde p ws
    if ws' = ws then ws else relaxN p n ws'

/-- The all-wide start. -/
def alleWeit (p : LProg) : List Bool := List.replicate p.length false

/-- BOUNDED RELAXATION: start all wide; refuse (`none`) if even the wide
    layout does not validate (a label outside the program, a rel32
    overflow, a non-canonical or control-flow `op` row); otherwise at most
    `fuel` compression rounds. -/
def relax (fuel : Nat) (p : LProg) : Option (List Bool) :=
  if layoutOk (alleWeit p) p = true then some (relaxN p fuel (alleWeit p)) else none

theorem versuche_ok (p : LProg) (ws : List Bool) (k : Nat) (h : layoutOk ws p = true) :
    layoutOk (versuche p ws k) p = true := by
  unfold versuche
  split
  · rename_i hc; exact hc.2
  · exact h

theorem runde_ok (p : LProg) (ws : List Bool) (h : layoutOk ws p = true) :
    layoutOk (runde p ws) p = true := by
  unfold runde
  generalize List.range p.length = ks
  induction ks generalizing ws with
  | nil => exact h
  | cons k ks ih => exact ih _ (versuche_ok p ws k h)

theorem relaxN_ok (p : LProg) (n : Nat) (ws : List Bool) (h : layoutOk ws p = true) :
    layoutOk (relaxN p n ws) p = true := by
  induction n generalizing ws with
  | zero => exact h
  | succ n ih =>
    simp only [relaxN]
    split
    · exact h
    · exact ih _ (runde_ok p ws h)

/-- RELAXATION SOUNDNESS: whatever the fuel, the answer validates. -/
theorem relax_ok (fuel : Nat) (p : LProg) (ws : List Bool)
    (h : relax fuel p = some ws) : layoutOk ws p = true := by
  unfold relax at h
  split at h
  · rename_i h0; cases h; exact relaxN_ok p fuel _ h0
  · cases h

/-- FUEL EXHAUSTED: with no rounds the answer is the validated all-wide
    layout. -/
theorem relax_null (p : LProg) (h : layoutOk (alleWeit p) p = true) :
    relax 0 p = some (alleWeit p) := by
  simp [relax, h, relaxN]

/-! ## 3. The labelled semantics: a jump goes to the address of its label. -/

/-- One labelled step at program counter `x.1` (a label), given the
    address map `adr` of labels. Ordinary rows run the unified `stepI`;
    a jump sets RIP to the address of its label; an untaken conditional
    jump continues at the next label. Past the end: no change. -/
def stepL (adr : Nat → Adresse) (p : LProg) (x : Nat × Zustand) : Option (Nat × Zustand) :=
  match p[x.1]? with
  | none => some x
  | some (.op i) => (stepI (canonI i) x.2).map (fun s' => (x.1 + 1, s'))
  | some (.jmp z) => some (z, { x.2 with rip := adr z })
  | some (.jcc c z) =>
    some (if bedingung c x.2.flags then (z, { x.2 with rip := adr z })
      else (x.1 + 1, { x.2 with rip := adr (x.1 + 1) }))

/-- Bounded labelled run: at most `n` steps; it STOPS at the program end
    (a label `≥ p.length`); `none` is a refusal. -/
def laufL (adr : Nat → Adresse) (p : LProg) : Nat → Nat × Zustand → Option (Nat × Zustand)
  | 0, x => some x
  | n + 1, x =>
    if x.1 < p.length then
      match stepL adr p x with
      | some y => laufL adr p n y
      | none => none
    else some x

/-- The number of machine steps the bounded labelled run executes
    (a refusing step counts). -/
def schritteL (adr : Nat → Adresse) (p : LProg) : Nat → Nat × Zustand → Nat
  | 0, _ => 0
  | n + 1, x =>
    if x.1 < p.length then
      match stepL adr p x with
      | some y => schritteL adr p n y + 1
      | none => 1
    else 0

/-- The resolved instructions the bounded labelled run executes, in order
    (the trace `laufBytesI_spur` speaks about). -/
def spurL (ws : List Bool) (adr : Nat → Adresse) (p : LProg) :
    Nat → Nat × Zustand → List Instr
  | 0, _ => []
  | n + 1, x =>
    if x.1 < p.length then
      aufloesenAt ws p x.1 ::
        (match stepL adr p x with
         | some y => spurL ws adr p n y
         | none => [])
    else []

/-- Runs compose (also across the program end, where the run stays). -/
theorem laufL_add (adr : Nat → Adresse) (p : LProg) (a b : Nat) (x : Nat × Zustand) :
    laufL adr p (a + b) x = (laufL adr p a x).bind (laufL adr p b) := by
  induction a generalizing x with
  | zero => simp [laufL]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [laufL]
    split
    · cases stepL adr p x with
      | none => rfl
      | some y => exact ih y
    · rename_i hx
      show some x = laufL adr p b x
      cases b with
      | zero => rfl
      | succ b => simp [laufL, hx]

/-! ## 4. The layout theorem with control flow. -/

theorem ripNach_ripNach (b : Adresse) (x y : Nat) :
    ripNach (ripNach b x) y = ripNach b (x + y) := by
  unfold ripNach
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem ripNach_null (a : Adresse) : ripNach a 0 = a := by
  unfold ripNach
  simp

/-- The one arithmetic fact of branch resolution: from the end of an
    instruction at offset `a` with length `l`, adding the displacement word
    to offset `c` lands at offset `c` (modular, no no-wrap premise). -/
theorem ziel_arith (base : Adresse) (a l c : Nat) :
    ripNach (ripNach base a) l + (BitVec.ofNat 64 c - BitVec.ofNat 64 (a + l)) =
      ripNach base c := by
  rw [ripNach_ripNach]
  unfold ripNach
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_sub]
  omega

theorem adrL_succ (base : Adresse) (ws : List Bool) (p : LProg) (k : Nat) :
    adrL base ws p (k + 1) = ripNach (adrL base ws p k) (lenAt ws p k) := by
  unfold adrL
  rw [off_succ, ripNach_ripNach]

/-- A rel8 jump resolved by the layout reaches the label address. -/
theorem ziel_kurz (base : Adresse) (ws : List Bool) (p : LProg) (k z : Nat)
    (h : passtRel8Wort (dispW ws p k z 2) = true) :
    ripNach (adrL base ws p k) 2 + dispWort8 (rel8FromWort (dispW ws p k z 2)) =
      adrL base ws p z := by
  rw [of_decide_eq_true h]
  exact ziel_arith base _ 2 _

/-- A rel32 jump resolved by the layout reaches the label address. -/
theorem ziel_weit (base : Adresse) (ws : List Bool) (p : LProg) (k z l : Nat)
    (h : passtRel32Wort (dispW ws p k z l) = true) :
    ripNach (adrL base ws p k) l + dispWort (BitVec.ofNat 32 (dispW ws p k z l).toNat) =
      adrL base ws p z := by
  rw [of_decide_eq_true h]
  exact ziel_arith base _ l _

/-- The layout invariant of a labelled state: RIP is the address of its
    label, memory is W^X, and the image still sits at `base`. -/
def InvL (base : Adresse) (ws : List Bool) (p : LProg) (x : Nat × Zustand) : Prop :=
  x.2.rip = adrL base ws p x.1 ∧ WX x.2.speicher ∧ CodeAt x.2.speicher base (bild ws p)

theorem invL_rip (base : Adresse) (ws : List Bool) (p : LProg) (s : Zustand) (pc z : Nat)
    (h : InvL base ws p (pc, s)) :
    InvL base ws p (z, { s with rip := adrL base ws p z }) :=
  ⟨rfl, h.2.1, h.2.2⟩

/-- ONE BYTE STEP OF A LAID-OUT LABELLED PROGRAM: at a label inside a
    validated program, under the layout invariant, the unified byte step
    from actual memory is the labelled step (successor or refusal), and the
    invariant is kept. -/
theorem byteschrittL (base : Adresse) (ws : List Bool) (p : LProg)
    (hok : layoutOk ws p = true) (pc : Nat) (s : Zustand) (hx : pc < p.length)
    (hinv : InvL base ws p (pc, s)) :
    byteschrittI s = ausgangVon ((stepL (adrL base ws p) p (pc, s)).map Prod.snd) ∧
      ∀ y, stepL (adrL base ws p) p (pc, s) = some y → InvL base ws p y := by
  have hli : p[pc]? = some p[pc] := List.getElem?_eq_getElem hx
  generalize hL : p[pc] = li at hli
  have hz := layoutOk_zeile ws p hok pc li hli
  have hcode := codeAt_zeile s.speicher base ws p hinv.2.2 pc hx
  rw [← hinv.1] at hcode
  have hJ : aufloesenAt ws p pc = aufloesen ws p pc li := by
    simp only [aufloesenAt, hli]
  rw [hJ] at hcode
  obtain ⟨suf, hw⟩ := geholt_codeAt s _ hcode (encodeI_len _).2
  have hlen : lenAt ws p pc = lenL (ws.getD pc false) li := by
    simp only [lenAt, hli]
  cases li with
  | op i =>
    simp only [zeileOk, Bool.and_eq_true] at hz
    have hb := (byteschrittI_kanonisch i hz.1 s suf hw).2
    simp only [stepL, hli]
    refine ⟨?_, ?_⟩
    · rw [hb]
      cases stepI (canonI i) s <;> rfl
    · intro y hy
      cases hs : stepI (canonI i) s with
      | none => rw [hs] at hy; cases hy
      | some s1 =>
        rw [hs] at hy
        cases hy
        obtain ⟨hschutz, hrip⟩ := stepI_rahmen i _ s s1 hs
        refine ⟨?_, wx_schutz _ _ hinv.2.1 hschutz,
          codeAt_schutz _ _ _ _ hinv.2.1 hschutz hinv.2.2⟩
        show s1.rip = adrL base ws p (pc + 1)
        rw [hrip hz.2, adrL_succ, hlen, ← hinv.1]
        rfl
  | jmp z =>
    simp only [zeileOk, Bool.and_eq_true] at hz
    refine ⟨?_, fun y hy => ?_⟩
    · simp only [stepL, hli, Option.map_some]
      cases hk : ws.getD pc false with
      | true =>
        simp only [hk, if_true] at hz
        have hJ' : aufloesen ws p pc (.jmp z) =
            .compact (.jump8 (rel8FromWort (dispW ws p pc z 2))) := by
          simp only [aufloesen, hk, if_true, Bool.false_eq_true, if_false]
        rw [hJ'] at hw
        rw [(byteschrittI_kanonisch _ rfl s suf hw).2]
        show ausgangVon (schrittC ⟨.jump8 _, 2⟩ s) = _
        rw [schrittC_jump8 _ s _ rfl rfl]
        show ByteAusgang.weiter _ = ByteAusgang.weiter _
        rw [hinv.1, ziel_kurz base ws p pc z hz.2]
      | false =>
        simp only [hk] at hz
        have hJ' : aufloesen ws p pc (.jmp z) =
            .pilot (.jump32 (BitVec.ofNat 32 (dispW ws p pc z 5).toNat)) := by
          simp only [aufloesen, hk, if_true, Bool.false_eq_true, if_false]
        rw [hJ'] at hw
        rw [(byteschrittI_kanonisch _ rfl s suf hw).2]
        have hc : canonI (.pilot (.jump32 (BitVec.ofNat 32 (dispW ws p pc z 5).toNat))) =
            ⟨.pilot (.jump32 (BitVec.ofNat 32 (dispW ws p pc z 5).toNat)), 5⟩ := by
          simp only [canonI, jump32_laenge]
        rw [hc]
        show ausgangVon (schritt ⟨.jump32 _, 5⟩ s) = _
        rw [schritt_jump32 _ s _ rfl rfl]
        show ByteAusgang.weiter _ = ByteAusgang.weiter _
        rw [hinv.1, ziel_weit base ws p pc z 5 hz.2]
    · simp only [stepL, hli, Option.some.injEq] at hy
      subst hy
      exact invL_rip base ws p s pc z hinv
  | jcc c z =>
    simp only [zeileOk, Bool.and_eq_true] at hz
    refine ⟨?_, fun y hy => ?_⟩
    · simp only [stepL, hli, Option.map_some]
      cases hk : ws.getD pc false with
      | true =>
        simp only [hk, if_true] at hz
        have hJ' : aufloesen ws p pc (.jcc c z) =
            .compact (.jumpIf8 c (rel8FromWort (dispW ws p pc z 2))) := by
          simp only [aufloesen, hk, if_true, Bool.false_eq_true, if_false]
        rw [hJ'] at hw
        rw [(byteschrittI_kanonisch _ rfl s suf hw).2]
        show ausgangVon (schrittC ⟨.jumpIf8 c _, 2⟩ s) = _
        cases hb : bedingung c s.flags with
        | true =>
          rw [schrittC_jumpIf8_genommen _ s c _ rfl rfl hb]
          simp only [if_true]
          show ByteAusgang.weiter _ = ByteAusgang.weiter _
          rw [hinv.1, ziel_kurz base ws p pc z hz.2]
        | false =>
          rw [schrittC_jumpIf8_nicht _ s c _ rfl rfl hb]
          simp only [Bool.false_eq_true, if_false]
          show ByteAusgang.weiter _ = ByteAusgang.weiter _
          rw [adrL_succ, hlen, ← hinv.1]
          simp only [lenL, hk, if_true, Bool.false_eq_true, if_false]
      | false =>
        simp only [hk] at hz
        have hJ' : aufloesen ws p pc (.jcc c z) =
            .pilot (.jumpIf32 c (BitVec.ofNat 32 (dispW ws p pc z 6).toNat)) := by
          simp only [aufloesen, hk, if_true, Bool.false_eq_true, if_false]
        rw [hJ'] at hw
        rw [(byteschrittI_kanonisch _ rfl s suf hw).2]
        have hc : canonI (.pilot (.jumpIf32 c (BitVec.ofNat 32 (dispW ws p pc z 6).toNat))) =
            ⟨.pilot (.jumpIf32 c (BitVec.ofNat 32 (dispW ws p pc z 6).toNat)), 6⟩ := by
          simp only [canonI, jumpIf32_laenge]
        rw [hc]
        show ausgangVon (schritt ⟨.jumpIf32 c _, 6⟩ s) = _
        cases hb : bedingung c s.flags with
        | true =>
          rw [schritt_jumpIf32_genommen _ s c _ rfl rfl hb]
          simp only [if_true]
          show ByteAusgang.weiter _ = ByteAusgang.weiter _
          rw [hinv.1, ziel_weit base ws p pc z 6 hz.2]
        | false =>
          rw [schritt_jumpIf32_nicht _ s c _ rfl rfl hb]
          simp only [Bool.false_eq_true, if_false]
          show ByteAusgang.weiter _ = ByteAusgang.weiter _
          rw [adrL_succ, hlen, ← hinv.1]
          simp only [lenL, hk, if_true, Bool.false_eq_true, if_false]
    · simp only [stepL, hli, Option.some.injEq] at hy
      subst hy
      split
      · exact invL_rip base ws p s pc z hinv
      · exact invL_rip base ws p s pc (pc + 1) hinv

/-- THE LAYOUT THEOREM WITH CONTROL FLOW. A validated labelled program
    (loops and branches allowed), laid out by `bild` at `base` in W^X
    memory and entered at the address of a label: the unified byte run of
    exactly as many steps as the bounded labelled run executes produces the
    labelled run's outcome -- the same successor state, or a refusal
    exactly when the labelled run refuses -- and the layout invariant holds
    at the end (RIP is the address of the reached label). -/
theorem laufBytesL (base : Adresse) (ws : List Bool) (p : LProg)
    (hok : layoutOk ws p = true) :
    ∀ (n : Nat) (x : Nat × Zustand), InvL base ws p x →
      laufBytesI (schritteL (adrL base ws p) p n x) x.2 =
          ausgangVon ((laufL (adrL base ws p) p n x).map Prod.snd) ∧
        ∀ y, laufL (adrL base ws p) p n x = some y → InvL base ws p y := by
  intro n
  induction n with
  | zero => intro x hx; exact ⟨rfl, fun y hy => by cases hy; exact hx⟩
  | succ n ih =>
    intro x hinv
    obtain ⟨pc, s⟩ := x
    by_cases hx : pc < p.length
    · obtain ⟨hb, hinv'⟩ := byteschrittL base ws p hok pc s hx hinv
      simp only [schritteL, laufL, hx, if_true]
      cases hs : stepL (adrL base ws p) p (pc, s) with
      | none =>
        rw [hs] at hb
        simp only [laufBytesI, hb, ausgangVon, Option.map_none]
        exact ⟨trivial, fun y hy => by cases hy⟩
      | some y =>
        rw [hs] at hb
        simp only [laufBytesI, hb, ausgangVon, Option.map_some]
        exact ih y (hinv' y hs)
    · simp only [schritteL, laufL, hx, if_false]
      exact ⟨rfl, fun y hy => by cases hy; exact hinv⟩

/-- THE TRACE PREMISE, DERIVED. The resolved instructions the labelled run
    executes satisfy `SpurAn` from the layout alone -- the premise that
    `laufBytesI_spur` (ISAExecution) ASSUMED for control flow. -/
theorem spurAn_layoutL (base : Adresse) (ws : List Bool) (p : LProg)
    (hok : layoutOk ws p = true) :
    ∀ (n : Nat) (x : Nat × Zustand), InvL base ws p x →
      SpurAn (spurL ws (adrL base ws p) p n x) x.2 := by
  intro n
  induction n with
  | zero => intro x _; trivial
  | succ n ih =>
    intro x hinv
    obtain ⟨pc, s⟩ := x
    by_cases hx : pc < p.length
    · simp only [spurL, hx, if_true]
      obtain ⟨hb, hinv'⟩ := byteschrittL base ws p hok pc s hx hinv
      have hli : p[pc]? = some p[pc] := List.getElem?_eq_getElem hx
      have hcode := codeAt_zeile s.speicher base ws p hinv.2.2 pc hx
      rw [← hinv.1] at hcode
      obtain ⟨suf, hw⟩ := geholt_codeAt s _ hcode (encodeI_len _).2
      have hk : kanonischI (aufloesenAt ws p pc) = true := by
        have hz := layoutOk_zeile ws p hok pc _ hli
        simp only [aufloesenAt, hli]
        revert hz
        cases p[pc] with
        | op i =>
          intro hz
          simp only [zeileOk, Bool.and_eq_true] at hz
          exact hz.1
        | jmp z => intro _; simp only [aufloesen]; split <;> rfl
        | jcc c z => intro _; simp only [aufloesen]; split <;> rfl
      have hb2 := (byteschrittI_kanonisch _ hk s suf hw).2
      refine ⟨hk, ⟨suf, hw⟩, fun s1 hs1 => ?_⟩
      rw [hb2, hs1] at hb
      cases hs : stepL (adrL base ws p) p (pc, s) with
      | none => rw [hs] at hb; cases hb
      | some y =>
        rw [hs] at hb
        simp only [ausgangVon, Option.map_some, ByteAusgang.weiter.injEq] at hb
        subst hb
        exact ih y (hinv' y hs)
    · simp only [spurL, hx, if_false]
      trivial

/-- ENTRY FORM: a validated program whose image sits at the current RIP in
    W^X memory, entered at label 0. -/
theorem laufBytesL_start (ws : List Bool) (p : LProg) (hok : layoutOk ws p = true)
    (s : Zustand) (hwx : WX s.speicher) (hcode : CodeAt s.speicher s.rip (bild ws p))
    (n : Nat) :
    laufBytesI (schritteL (adrL s.rip ws p) p n (0, s)) s =
        ausgangVon ((laufL (adrL s.rip ws p) p n (0, s)).map Prod.snd) ∧
      ∀ y, laufL (adrL s.rip ws p) p n (0, s) = some y →
        y.2.rip = adrL s.rip ws p y.1 :=
  have h := laufBytesL s.rip ws p hok n (0, s)
    ⟨by simp [adrL, off_null, ripNach_null], hwx, hcode⟩
  ⟨h.1, fun y hy => (h.2 y hy).1⟩

/-- RELAXED FORM: whatever the fuel, the relaxed layout runs as the
    labelled program. -/
theorem relax_laufBytes (fuel : Nat) (p : LProg) (ws : List Bool)
    (hr : relax fuel p = some ws) (s : Zustand) (hwx : WX s.speicher)
    (hcode : CodeAt s.speicher s.rip (bild ws p)) (n : Nat) :
    laufBytesI (schritteL (adrL s.rip ws p) p n (0, s)) s =
        ausgangVon ((laufL (adrL s.rip ws p) p n (0, s)).map Prod.snd) ∧
      ∀ y, laufL (adrL s.rip ws p) p n (0, s) = some y →
        y.2.rip = adrL s.rip ws p y.1 :=
  laufBytesL_start ws p (relax_ok fuel p ws hr) s hwx hcode n

end Gabbro.Grammatik.X86
