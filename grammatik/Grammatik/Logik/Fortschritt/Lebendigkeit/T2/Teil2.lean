module

public import Grammatik.Logik.Fortschritt.Lebendigkeit.T1
public import Grammatik.Logik.Fortschritt.Lebendigkeit.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Kern
variable {P : Programm D} {O : Orakel D} {passes : Nat} (R : PlanLauf P O passes)
variable {ls : List D.Lock} {Ts : D.Lock → List Faden} {h k : D.Lock → Nat} {F : Nat}
section Beweis
variable (hO : GutO O) (hls : ∀ L : D.Lock, L ∈ ls)
  (hRang : ∀ n t, ∃ w, RangInvG w ((R.M n).faeden t))
  (hEx : ∀ n (f g : Faden), f ≠ g → ∀ L : D.Lock,
    L ∈ offen ((R.M n).faeden f).spur → L ∉ offen ((R.M n).faeden g).spur)
  (hFifo : FifoSperre R) (hFair : FairF R F) (hH : Haltezeit R h k)
  (hAkt : AbschnittAktiv R) (hAnw : Anwaerter R Ts)
include hO hls hRang hEx hFifo hFair hH hAkt hAnw in
/-- **THE WAITING BOUND, core form.** A thread standing at `locks L` at
    scheduler step `n0` takes `L` at a step `j < n0 + wartezeit L` and holds
    it after that step. -/
theorem wartezeit_kern (L : D.Lock) (t : Faden) (n0 : Nat) (hA : AnSperre (R.M n0) t L) :
    ∃ j, n0 ≤ j ∧ j < n0 + wartezeit ls Ts h k F L ∧ R.akt j = some t ∧
      L ∈ offen ((R.M (j + 1)).faeden t).spur := by
  obtain ⟨j, j1, j2, j3⟩ := gueltig R hO hls hRang hEx hFifo hFair hH hAkt hAnw ls.length L
    (hoeher_lt_len ls (hls L)) t n0 hA
  obtain ⟨j', j1', j2', j3', j4'⟩ := erster_schritt R ⟨j, j1, j2, j3⟩
  have hA' : AnSperre (R.M j') t L := anSperre_gleich (j4' j' j1' (Nat.le_refl j')) hA
  have e := (sperre_schritt hA' (R.schritt j' t j3')).2
  refine ⟨j', j1', j2', j3', ?_⟩
  rw [e]
  exact List.mem_cons_self

end Beweis

/-! ## 8. From the goal theorem's premises -/

/-- **A lock holder can step or stands at a `locks` head**, from progress
    (`fortschrittG_aus`, with `KeinLogikHaltG` -- a conjunct of `Ziel`) and
    `HardwareImAbschnitt`: a finished thread holds no lock (`fertig_leer`),
    a waiting one stands at `locks`, a hardware stop is excluded. -/
theorem abschnittAktiv_aus (hO : GutO O) (hSt : StufenM P) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hLeer : ∀ t, D.haelt (init t).1 = [])
    (hr0 : RufErreichbarG P O passes (RufStartG P sp init) (R.M 0))
    (hL : ∀ n, KeinLogikHaltG O passes (R.M n)) (hB : ∀ n t, BereichG (R.M n) t)
    (hAnt : ∀ g, ∀ x ∈ (P.rumpf g).ants, StelleOk D x)
    (hHw : Zielsatz.HardwareImAbschnitt R) :
    AbschnittAktiv R := by
  intro n u L hu
  have hr := R.erreichbar hr0 n
  have hND := startSpur_nodup_leer init hLeer
  rcases fortschrittG_aus hO hSt sp init hND hr (hL n) (hB n) hAnt u with
    hF | hW | hHalt | hHalt | hHalt | hHalt | hs
  · have e := fertig_leer (rangInvG_erreichbar hO hSt sp init hND hr u) (hLeer u) hF
    rw [e] at hu
    exact absurd hu List.not_mem_nil
  · exact Or.inr hW.1
  · exact absurd hHalt (hHw n u L hu _)
  · exact absurd hHalt (hHw n u L hu _)
  · exact absurd hHalt (hHw n u L hu _)
  · exact absurd hHalt (hHw n u L hu _)
  · exact Or.inl hs

/-- **THE WAITING BOUND (`wartezeit_schranke`).** On a scheduled run of
    machine G that starts at a reachable machine, under
    * the goal theorem's premises used here -- `GutO` (hardware), `StufenM`
      (checker), starts without signature locks (`AkzeptiertSpec.wurzeln`,
      idle roots), admissible answer sites (`AkzeptiertSpec.antworten`, W1),
      a complete lock list, and `KeinLogikHaltG` at every machine
      of the run (the conjunct `Ziel.keinLogikHalt`, which `gabbro_ziel`
      supplies at every reachable machine);
    * THE RUNTIME ASSUMPTION `LaufzeitAnnahme R F` (FIFO lock, fairness `F`);
    * the hold-time premise `Haltezeit R h k`;
    * `HardwareImAbschnitt R` (no hardware stop inside a critical section);
    * the contenders `Anwaerter R Ts`;
    a thread standing at `locks L` at scheduler step `n0` takes `L` at a step
    `j < n0 + wartezeit ls Ts h k F L` and holds it after that step. -/
theorem wartezeit_schranke (hO : GutO O) (hSt : StufenM P) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hLeer : ∀ t, D.haelt (init t).1 = [])
    (hls : ∀ L : D.Lock, L ∈ ls)
    (hr0 : RufErreichbarG P O passes (RufStartG P sp init) (R.M 0))
    (hL : ∀ n, KeinLogikHaltG O passes (R.M n)) (hB : ∀ n t, BereichG (R.M n) t)
    (hAnt : ∀ g, ∀ x ∈ (P.rumpf g).ants, StelleOk D x) (hLZ : LaufzeitAnnahme R F) (hH : Haltezeit R h k) (hHw : Zielsatz.HardwareImAbschnitt R)
    (hAnw : Anwaerter R Ts)
    (L : D.Lock) (t : Faden) (n0 : Nat) (hA : AnSperre (R.M n0) t L) :
    ∃ j, n0 ≤ j ∧ j < n0 + wartezeit ls Ts h k F L ∧ R.akt j = some t ∧
      L ∈ offen ((R.M (j + 1)).faeden t).spur := by
  have hND := startSpur_nodup_leer init hLeer
  have hRang : ∀ n t, ∃ w, RangInvG w ((R.M n).faeden t) :=
    fun n t => ⟨_, rangInvG_erreichbar hO hSt sp init hND (R.erreichbar hr0 n) t⟩
  have hEx : ∀ n (f g : Faden), f ≠ g → ∀ L : D.Lock,
      L ∈ offen ((R.M n).faeden f).spur → L ∉ offen ((R.M n).faeden g).spur :=
    fun n => exklusivG hO sp init (startExklusiv_ohne_haelt init hLeer) (R.erreichbar hr0 n)
  exact wartezeit_kern R hO hls hRang hEx hLZ.1 hLZ.2 hH
    (abschnittAktiv_aus R hO hSt sp init hLeer hr0 hL hB hAnt hHw) hAnw L t n0 hA

end Kern
