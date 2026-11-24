module

public import Core.Beobachtung.Nichtinterferenz
public import Core.Annahme.HostedLauf

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme
open Annahme.Hosted

private theorem hoch_vereinigt : hoch ∪ hoch = hoch := by
  ext n
  simp only [Finset.mem_union, or_self]

private theorem hoch_verborgen : oeffentlich hoch = false := by
  apply decide_eq_false
  intro eq
  have mem : 0 ∈ hoch := Finset.mem_singleton_self _
  rw [eq] at mem
  exact Finset.notMem_empty _ mem

private theorem verdeckt (a : A) : sichtbar hoch a = none := by
  simp only [sichtbar, hoch_verborgen, Bool.false_eq_true, if_false]

private theorem frage_hoch (q : Frage) : einheit.etiketten.frage q = hoch := by
  change (q.zugriffe.map (fun _ => hoch)).foldl (· ∪ ·) hoch = hoch
  generalize q.zugriffe = xs
  induction xs with
  | nil => rfl
  | cons z rest ih => simpa only [List.map_cons, List.foldl_cons, hoch_vereinigt] using ih

private theorem sicht_gleich (s₁ s₂ : AussenSicht) :
    niedereAussensicht einheit.etiketten s₁ = niedereAussensicht einheit.etiketten s₂ := by
  apply Prod.ext
  · funext o
    change sichtbar (hoch ∪ hoch) (s₁.objects o) = sichtbar (hoch ∪ hoch) (s₂.objects o)
    simp only [hoch_vereinigt, verdeckt]
  · apply Prod.ext
    · funext e i
      change (s₁.channels e i).bind (fun h => sichtbar (hoch ∪ hoch) h) =
        (s₂.channels e i).bind (fun h => sichtbar (hoch ∪ hoch) h)
      cases s₁.channels e i <;> cases s₂.channels e i <;> simp only [Option.bind, hoch_vereinigt, verdeckt]
    · funext o name
      change (s₁.names o name).bind (fun h => sichtbar (hoch ∪ hoch ∪ hoch) h) =
        (s₂.names o name).bind (fun h => sichtbar (hoch ∪ hoch ∪ hoch) h)
      cases s₁.names o name <;> cases s₂.names o name <;> simp only [Option.bind, hoch_vereinigt, verdeckt]

private theorem politik_gleich (p₁ p₂ : AussenPolitik) :
    politikProjektion einheit.etiketten p₁ = politikProjektion einheit.etiketten p₂ := by
  apply Prod.ext
  · funext t h
    exact sicht_gleich _ _
  · apply Prod.ext
    · funext t h q
      simp only [politikProjektion, frage_hoch, verdeckt]
    · funext t h e phase
      change sichtbar hoch (p₁.dma t (niedrigerVerlauf einheit.etiketten h) e phase) =
        sichtbar hoch (p₂.dma t (niedrigerVerlauf einheit.etiketten h) e phase)
      simp only [verdeckt]

private theorem umgebung_gleich (b₁ b₂ : List UInt8) :
    GleicheNiedrigeUmgebung einheit (umgebung b₁) (umgebung b₂) := by
  unfold GleicheNiedrigeUmgebung umgebungsProjektion
  rw [politik_gleich (umgebung b₁).politik (umgebung b₂).politik] <;> rfl

private theorem hw_gleich (b₁ b₂ : List UInt8) :
    hwPolitikProjektion einheit (hardware b₁) = hwPolitikProjektion einheit (hardware b₂) :=
  Prod.ext rfl (politik_gleich _ _)

private theorem endet_nicht (vor nach : Zustand)
    (gleich : ∀ c, nach.status c = .ruht ∨ nach.status c = .laeuft) :
    ¬ ∃ c, (neuBeendet vor nach einheit.etiketten c).isSome = true := by
  rintro ⟨c, endet⟩
  rcases gleich c with h | h <;>
    cases status : vor.status c <;>
    rw [neuBeendet, status, h] at endet <;> exact Bool.false_ne_true endet

private theorem verborgen_frage (s : AussenStart) :
    aussenBeob einheit (.frage (gestellt s)) = [] := by
  simp only [aussenBeob, frage_hoch, verdeckt, Option.toList]

private theorem verborgen_antwort (s : AussenStart) (bytes : List UInt8) :
    aussenBeob einheit (.antwort (angekommen s bytes)) = [] := by
  simp only [aussenBeob, frage_hoch, verdeckt] <;> rfl

private theorem schritte_stumm {s : AussenStart} {bytes : List UInt8} {ρ : Lauf einheit}
    {g g' : SpeicherGraph Unit Unit}
    (z₀ : ρ.zeit.zustand 0 = some (startZustand s))
    (z₁ : ρ.zeit.zustand 1 = some (binde (startZustand s)))
    (z₂ : ρ.zeit.zustand 2 = some (fragend s g))
    (z₃ : ρ.zeit.zustand 3 = some (fertig s bytes g g'))
    (e₀ : ρ.zeit.spur 0 = some (.kontext kontext (), ⟨[], []⟩))
    (e₁ : ρ.zeit.spur 1 = some (.kontext kontext (), frageSpur s))
    (e₂ : ρ.zeit.spur 2 = some (.antwort (angekommen s bytes), antwortSpur s bytes))
    (still : ∀ t, ρ.zeit.spur (t + 3) = none) (p : Praediktor) (t : Nat) :
    schrittBeob ρ p t = [] := by
  match t with
  | 0 =>
    rw [schrittBeob, e₀, z₀, z₁]
    have kein := endet_nicht (startZustand s) (binde (startZustand s)) (fun _ => Or.inr rfl)
    simp only [kein, if_false] <;> rfl
  | 1 =>
    rw [schrittBeob, e₁, z₁, z₂]
    have kein := endet_nicht (binde (startZustand s)) (fragend s g) (fun _ => Or.inl rfl)
    simp only [frageSpur, List.flatMap_cons, List.flatMap_nil, verborgen_frage,
      kein, if_false, List.append_nil] <;> rfl
  | 2 =>
    rw [schrittBeob, e₂, z₂, z₃]
    have kein := endet_nicht (fragend s g) (fertig s bytes g g') (fun _ => Or.inl rfl)
    simp only [antwortSpur, List.flatMap_cons, List.flatMap_nil, verborgen_antwort,
      kein, if_false, List.append_nil] <;> rfl
  | t + 3 => simp only [schrittBeob, still]

private theorem beob_konstant {ρ : Lauf einheit} {s : AussenStart} (p : Praediktor)
    (anfang : ρ.zeit.zustand 0 = some (startZustand s)) (still : ∀ t, schrittBeob ρ p t = []) (t : Nat) :
    NiedrigeBeob einheit ρ p t = [.anfangsspeicher (fun _ => some ())] := by
  induction t with
  | zero =>
    change ((match ρ.zeit.zustand 0 with
      | none => [.ladefehler]
      | some z => [.anfangsspeicher (fun o => sichtbar (einheit.etiketten.ort o) (z.initial o))]) :
        List (NiedrigesEreignis Unit Unit Unit Unit)) = _
    rw [anfang] <;> rfl
  | succ t ih =>
    change NiedrigeBeob einheit ρ p t ++ schrittBeob ρ p t = _
    rw [ih, still, List.append_nil]

private theorem beob_aequiv {ρ₁ ρ₂ : Lauf einheit}
    (gleich : ∀ p t, NiedrigeBeob einheit ρ₁ p t = NiedrigeBeob einheit ρ₂ p t) :
    NiedrigAequiv einheit (NiedrigeBeob einheit ρ₁) (NiedrigeBeob einheit ρ₂) := by
  intro p
  have reflexiv (xs : List (NiedrigesEreignis Unit Unit Unit Unit)) :
      List.Forall₂ (EreignisAequiv einheit.fluss.freigabe) xs xs := by
    induction xs with
    | nil => exact .nil
    | cons x _ ih => exact .cons (.gleich x) ih
  refine ⟨fun t => ⟨t, ?_⟩, fun t => ⟨t, ?_⟩⟩
  · rw [← gleich p t, List.take_length]
    exact reflexiv _
  · rw [gleich p t, List.take_length]
    exact reflexiv _

/-- The whole NI comparison premise holds for an accepted program and two admitted runs.
    They issue the same high question, get different successful answers, and have related low traces. -/
theorem ni_erfuellbar :
    ∃ (E : Modell) (H₁ H₂ : Umgebung) (ρ₁ : Lauf E) (s₂ : AussenStart) (ρ₂ : Lauf E)
      (tq ta : Nat) (c : Kontext) (q : FrageEreignis) (a₁ a₂ : AntwortEreignis)
      (req resp₁ resp₂ : Spur),
      Akzeptiert E ∧ Hardware E.katalog H₁ ∧ Hardware E.katalog H₂ ∧
      Laeufe E H₁ ρ₁ ∧ GleicheNiedrigeUmgebung E H₁ H₂ ∧ E.ZulStart H₂ s₂ ∧
      NiedrigGleich E ρ₁.start s₂ ∧ Laeufe E H₂ ρ₂ ∧ ρ₂.start = s₂ ∧ GleichePolitik E ρ₁ ρ₂ ∧
      ρ₁.zeit.spur tq = some (.kontext c (), req) ∧ ρ₂.zeit.spur tq = some (.kontext c (), req) ∧
      req.aussen = [.frage q] ∧ oeffentlich (E.etiketten.frage q.question) = false ∧
      tq < ta ∧ ρ₁.zeit.spur ta = some (.antwort a₁, resp₁) ∧
      ρ₂.zeit.spur ta = some (.antwort a₂, resp₂) ∧ resp₁.aussen = [.antwort a₁] ∧
      resp₂.aussen = [.antwort a₂] ∧ a₁.zu q ∧ a₂.zu q ∧
      a₁.reply.result.isOk = true ∧ a₂.reply.result.isOk = true ∧ a₁.reply.result ≠ a₂.reply.result ∧
      NiedrigAequiv E (NiedrigeBeob E ρ₁) (NiedrigeBeob E ρ₂) := by
  obtain ⟨s, zul⟩ := zulStart_erfuellbar (erlaubt []) Sicherheit.Laufkonstruktion.bild_gueltig
  let b₁ : List UInt8 := []
  let b₂ : List UInt8 := [1]
  obtain ⟨ρ₁, _, _, lauf₁, start₁, hw₁, za₀, za₁, za₂, za₃, ea₀, ea₁, ea₂, still₁⟩ := konkreter_lauf zul b₁
  obtain ⟨ρ₂, _, _, lauf₂, start₂, hw₂, zb₀, zb₁, zb₂, zb₃, eb₀, eb₁, eb₂, still₂⟩ := konkreter_lauf zul b₂
  have politik : GleichePolitik einheit ρ₁ ρ₂ := by
    unfold GleichePolitik
    rw [hw₁, hw₂]
    exact hw_gleich _ _
  have anders : (ausgabe b₁).result ≠ (ausgabe b₂).result := by
    change (Except.ok (.data []) : Except AussenFehler AussenWert) ≠ Except.ok (.data [1])
    intro gleich
    cases gleich
  have trace : NiedrigAequiv einheit (NiedrigeBeob einheit ρ₁) (NiedrigeBeob einheit ρ₂) := by
    apply beob_aequiv
    intro p t
    exact (beob_konstant p za₀ (schritte_stumm za₀ za₁ za₂ za₃ ea₀ ea₁ ea₂ still₁ p) t).trans
      (beob_konstant p zb₀ (schritte_stumm zb₀ zb₁ zb₂ zb₃ eb₀ eb₁ eb₂ still₂ p) t).symm
  refine ⟨einheit, umgebung b₁, umgebung b₂, ρ₁, s, ρ₂, 1, 2, kontext, gestellt s,
    angekommen s b₁, angekommen s b₂, frageSpur s, antwortSpur s b₁, antwortSpur s b₂,
    akzeptiert, erlaubt b₁, erlaubt b₂, lauf₁, umgebung_gleich _ _, gleicher_start zul b₂, ?_,
    lauf₂, start₂, politik, ea₁, eb₁, rfl, ?_, Nat.lt_succ_self _, ea₂, eb₂, rfl, rfl,
    ⟨Nat.le_succ _, rfl, rfl, rfl⟩, ⟨Nat.le_succ _, rfl, rfl, rfl⟩, rfl, rfl, anders, trace⟩
  · rw [start₁]
    rfl
  · rw [frage_hoch]
    exact hoch_verborgen

end Gabbro.Core.Beobachtung
