module
public import Core.Katalog.Start

@[expose] public section

namespace Gabbro.Core.Katalog

def AussenSicht.leer : AussenSicht :=
  ⟨fun _ => ⟨0, false, false, [], fun _ => 0⟩, fun _ _ => none, fun _ _ => none⟩

/-- Instantiate the complete outside envelope with an arbitrary public-history snapshot policy. -/
def Umgebung.referenz (k : Katalog) (cores : Nat) (sicht : Nat → AussenVerlauf → AussenSicht) : Umgebung where
  ziel := k.plattform.ziel
  systemAbi := k.plattform.systemAbi
  kernzahl := cores
  float := ⟨binary32.rechne, binary64.rechne⟩
  lade := Bild.lade
  translate := uebersetze k.plattform.ziel
  pages := SeitenSchritt k.plattform.ziel
  interrupt := unterbrechungen
  medium := fun r s e t => k.enthaelt .persistence ∧ persistenz r s e t
  politik :=
    ⟨sicht, fun i history q => atomar k.plattform (sicht i history) q, fun _ _ _ _ => none⟩

theorem Umgebung.referenz_hardware (k : Katalog) (cores : Nat) (sicht : Nat → AussenVerlauf → AussenSicht)
    (valid : KatalogWohlgeformt k) (positive : 0 < cores) : Hardware k (Umgebung.referenz k cores sicht) where
  katalog := valid
  ziel := rfl
  abi := rfl
  kerne := positive
  float :=
    ⟨fun q => binary32.antwortGleich_refl (binary32.rechne q),
      fun q => binary64.antwortGleich_refl (binary64.rechne q)⟩
  lader := fun b hb => b.lader_lade hb
  mmu := rfl
  pages := rfl
  interrupts := rfl
  persistence := fun _ _ _ _ => Iff.rfl
  antwort := fun _ _ _ _ => rfl
  dma := fun _ _ _ _ _ never => by cases never

def Umgebung.referenzLauf (k : Katalog) (cores : Nat) (sicht : Nat → AussenVerlauf → AussenSicht) : HwLauf where
  angebot i :=
    { core := some (i % cores)
      interrupt := fun c => decide (c < cores)
      interrupts := []
      delivery := fun e => decide (k.enthaelt (.endpoint e))
      medium := decide (k.enthaelt .persistence)
      crash := false
      cycles := i }
  politik := (Umgebung.referenz k cores sicht).politik

theorem Umgebung.referenz_fair (k : Katalog) (cores : Nat) (sicht : Nat → AussenVerlauf → AussenSicht)
    (valid : KatalogWohlgeformt k) (positive : 0 < cores) : FairLaeufe k (Umgebung.referenz k cores sicht) (Umgebung.referenzLauf k cores sicht) where
  hardware := Umgebung.referenz_hardware k cores sicht valid positive
  politik := rfl
  gueltig := by
    intro i
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      change some (i % cores) = some c at hc
      exact (Option.some.inj hc) ▸ Nat.mod_lt i positive
    · intro c hc
      simpa only [Umgebung.referenz, Umgebung.referenzLauf, decide_eq_true_eq] using hc
    · intro irq raised
      cases raised
    · intro e he
      simpa only [Umgebung.referenzLauf, decide_eq_true_eq] using he
    · intro h
      cases h with
      | inl selected => simpa only [Umgebung.referenzLauf, decide_eq_true_eq] using selected
      | inr crash => cases crash
  kerne := kerneSchreiten_reihum positive
  interrupts := fun _ hc cut => ⟨cut, Nat.le_refl cut, decide_eq_true hc⟩
  auslieferung := fun _ selected cut => ⟨cut, Nat.le_refl cut, decide_eq_true selected⟩
  medium := fun selected cut => ⟨cut, Nat.le_refl cut, decide_eq_true selected⟩
  cycles := fun _ _ le => le
  zeit := fun cut n => ⟨cut + n, Nat.le_add_right cut n, Nat.le_add_left n cut⟩

theorem katalog_kernzahl_erfuellbar (k : Katalog) (valid : KatalogWohlgeformt k)
    (cores : Nat) (positive : 0 < cores) :
    ∃ h run, h.kernzahl = cores ∧ Hardware k h ∧ FairLaeufe k h run :=
  let sicht : Nat → AussenVerlauf → AussenSicht := fun _ _ => AussenSicht.leer
  ⟨Umgebung.referenz k cores sicht, Umgebung.referenzLauf k cores sicht, rfl,
    Umgebung.referenz_hardware k cores sicht valid positive,
    Umgebung.referenz_fair k cores sicht valid positive⟩

/-- The catalogue existence conjunct of `Ziel.NichtLeer`. Its history contains no program. -/
theorem katalog_nichtLeer (k : Katalog) (valid : KatalogWohlgeformt k) :
    ∃ h run, Hardware k h ∧ FairLaeufe k h run := by
  obtain ⟨h, run, _, hw, fair⟩ := katalog_kernzahl_erfuellbar k valid 2 (by decide)
  exact ⟨h, run, hw, fair⟩

theorem plattform_erfuellbar (p : Plattform) :
    KatalogWohlgeformt p.katalog ∧ ∃ h run, Hardware p.katalog h ∧ FairLaeufe p.katalog h run :=
  ⟨p.katalog_wohlgeformt, katalog_nichtLeer p.katalog p.katalog_wohlgeformt⟩

theorem x86_64_erfuellbar :
    KatalogWohlgeformt Plattform.x86_64.katalog ∧
    ∃ h run, Hardware Plattform.x86_64.katalog h ∧ FairLaeufe Plattform.x86_64.katalog h run :=
  plattform_erfuellbar .x86_64

theorem aarch64_erfuellbar :
    KatalogWohlgeformt Plattform.aarch64.katalog ∧
    ∃ h run, Hardware Plattform.aarch64.katalog h ∧ FairLaeufe Plattform.aarch64.katalog h run :=
  plattform_erfuellbar .aarch64

theorem riscv64_erfuellbar :
    KatalogWohlgeformt Plattform.riscv64.katalog ∧
    ∃ h run, Hardware Plattform.riscv64.katalog h ∧ FairLaeufe Plattform.riscv64.katalog h run :=
  plattform_erfuellbar .riscv64

/-- An approved hosted read can succeed with an issued handle and arbitrary outside contents. -/
theorem hosted_lesen_erfuellbar (p : Plattform) (bytes : List UInt8) :
    ∃ s q a, q.endpoint = .hosted ∧ q.operation = .read ∧
      atomar p s q = .antwort a ∧ a.result = .ok (.data bytes) := by
  let handle : Handle := ⟨0, ⟨⟨.hosted, 0⟩, 0⟩, [.read]⟩
  let q : Frage := ⟨.hosted, handle, [], .read⟩
  let s : AussenSicht :=
    ⟨fun _ => ⟨0, true, true, bytes, fun _ => 0⟩,
      fun e i => if e = .hosted ∧ i = 0 then some handle else none, fun _ _ => none⟩
  exact ⟨s, q, ⟨handle.origin, [handle.origin], .ok (.data bytes)⟩, rfl, rfl, rfl, rfl⟩

/-- The same issued UART handle can get an answer or a permitted non-answer as the register changes. -/
theorem register_warten_erfuellbar (p : Plattform) :
    ∃ before after q a, q.endpoint = .uart ∧ q.operation = .waitRegister 0 1 ∧
      atomar p before q = .warten ∧ atomar p after q = .antwort a ∧ a.result = .ok (.register 1) := by
  let handle : Handle := ⟨0, ⟨⟨.uart, 0⟩, 0⟩, [.read]⟩
  let sight : Nat → AussenSicht := fun value =>
    ⟨fun _ => ⟨0, true, true, [], fun _ => value⟩,
      fun e i => if e = .uart ∧ i = 0 then some handle else none, fun _ _ => none⟩
  let q : Frage := ⟨.uart, handle, [], .waitRegister 0 1⟩
  refine ⟨sight 0, sight 1, q, ⟨handle.origin, [handle.origin], .ok (.register 1)⟩,
    rfl, rfl, ?_, ?_, rfl⟩ <;> cases p <;> rfl

end Gabbro.Core.Katalog
