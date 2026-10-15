/-
  Sound reuse certificate for already validated canonical byte inputs (lane 430).

  A validation cache replays a previously checked decode outcome only on EXACT
  canonical byte input and context equality. No hash, no collision assumption:
  lookup compares the actual bytes and the actual context. This reuses the
  accepted `Codec.decode`, `Ausfuehrung.laengeOk` and `Bild.Profil` vocabulary
  and proves nothing about hardware, source correspondence or performance.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Codec
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Bild

namespace Gabbro.Grammatik.X86

namespace ValidCache

/- Own namespace for the lane-430 reuse certificate: every name below is
   `Gabbro.Grammatik.X86.ValidCache.*`, so nothing here can collide with
   sibling X86 modules (notably `TableLayout.eintragOk`). -/

/-- Validation context: the address-width profile plus the load bias the
    checked bytes were validated under. Nothing else is compared. -/
structure ValidKontext where
  profil : Profil
  bias : Nat
  deriving DecidableEq, Repr

/-- One cache entry: the exact validated byte window, its decoded outcome
    (instruction, consumed length, remaining suffix within the window) and
    the context it was validated under. -/
structure CacheEintrag where
  kontext : ValidKontext
  bytes : List Byte
  befehl : Befehl
  laenge : Nat
  rest : List Byte
  deriving DecidableEq, Repr

/-- A cache is a finite list of entries; lookup is linear and exact. -/
abbrev Cache := List CacheEintrag

/-- An entry is well validated: decoding its EXACT stored bytes reproduces
    the stored outcome, and the stored length is within 1..15. -/
def eintragOk (e : CacheEintrag) : Bool :=
  match decode e.bytes with
  | none => false
  | some (d, r) =>
    decide (d.befehl = e.befehl ∧ d.laenge = e.laenge ∧ r = e.rest) &&
    laengeOk e.laenge

/-- Exact match of one entry against a query context and query bytes. -/
def eintragPasst (e : CacheEintrag) (ctx : ValidKontext)
    (bs : List Byte) : Bool :=
  decide (e.kontext = ctx) && decide (e.bytes = bs)

/-- Cache lookup: the first entry with exactly equal context and bytes.
    Different bytes or a different context never hit. -/
def cacheFind : Cache → ValidKontext → List Byte → Option CacheEintrag
  | [], _, _ => none
  | e :: rest, ctx, bs =>
    if eintragPasst e ctx bs then some e else cacheFind rest ctx bs

/-- CACHE IDENTITY COMPLETENESS: a lookup hit returns a stored entry
    with exactly the queried context and the queried bytes. -/
theorem cacheFind_hit_gleich (c : Cache) (ctx : ValidKontext)
    (bs : List Byte) (e : CacheEintrag)
    (h : cacheFind c ctx bs = some e) :
    e ∈ c ∧ e.kontext = ctx ∧ e.bytes = bs := by
  induction c with
  | nil => simp [cacheFind] at h
  | cons f rest ih =>
    simp only [cacheFind] at h
    by_cases hc : eintragPasst f ctx bs = true
    · rw [if_pos hc] at h
      cases h
      simp only [eintragPasst, Bool.and_eq_true, decide_eq_true_eq] at hc
      exact ⟨List.mem_cons.mpr (Or.inl rfl), hc.1, hc.2⟩
    · rw [if_neg hc] at h
      obtain ⟨hmem, hctx, hbs⟩ := ih h
      exact ⟨List.mem_cons.mpr (Or.inr hmem), hctx, hbs⟩

/-- FAILURE ON DIFFERENT BYTES: if no stored entry carries the queried
    bytes, lookup refuses. -/
theorem cacheFind_verweigert_bei_fremden_bytes (c : Cache)
    (ctx : ValidKontext) (bs : List Byte)
    (h : ∀ e ∈ c, e.bytes ≠ bs) :
    cacheFind c ctx bs = none := by
  induction c with
  | nil => rfl
  | cons f rest ih =>
    simp only [cacheFind]
    have hne : f.bytes ≠ bs := h f (List.mem_cons.mpr (Or.inl rfl))
    have hnot : ¬ eintragPasst f ctx bs = true := by
      simp only [eintragPasst, Bool.and_eq_true, decide_eq_true_eq]
      intro hcon
      exact hne hcon.2
    rw [if_neg hnot]
    exact ih (fun e hm => h e (List.mem_cons.mpr (Or.inr hm)))

/-- FAILURE ON DIFFERENT CONTEXT: if no stored entry carries the queried
    context, lookup refuses, even on byte-identical input. -/
theorem cacheFind_verweigert_bei_fremdem_kontext (c : Cache)
    (ctx : ValidKontext) (bs : List Byte)
    (h : ∀ e ∈ c, e.kontext ≠ ctx) :
    cacheFind c ctx bs = none := by
  induction c with
  | nil => rfl
  | cons f rest ih =>
    simp only [cacheFind]
    have hne : f.kontext ≠ ctx := h f (List.mem_cons.mpr (Or.inl rfl))
    have hnot : ¬ eintragPasst f ctx bs = true := by
      simp only [eintragPasst, Bool.and_eq_true, decide_eq_true_eq]
      intro hcon
      exact hne hcon.1
    rw [if_neg hnot]
    exact ih (fun e hm => h e (List.mem_cons.mpr (Or.inr hm)))

/-- VALIDATED MEANS DECIDED: a well-validated entry reproduces its stored
    outcome when its exact bytes are decoded, and its length is valid. -/
theorem eintragOk_auspacken (e : CacheEintrag) (h : eintragOk e = true) :
    decode e.bytes = some (⟨e.befehl, e.laenge⟩, e.rest) ∧
      laengeOk e.laenge = true := by
  unfold eintragOk at h
  cases hde : decode e.bytes with
  | none =>
    rw [hde] at h
    simp at h
  | some pr =>
    obtain ⟨d, r⟩ := pr
    rw [hde] at h
    dsimp only at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hbef, hlen, hrest⟩, hok⟩ := h
    cases d with
    | mk b l =>
      dsimp only at hbef hlen
      subst hbef
      subst hlen
      subst hrest
      exact ⟨rfl, hok⟩

/-- SOUND REUSE: a lookup hit on a well-validated entry replays the stored
    decode outcome for the queried bytes, in the queried context. Reuse
    follows from actual input equality (`decode` is a function of the
    bytes); no hash and no collision assumption is used anywhere. -/
theorem treffer_wiederverwendung (c : Cache) (ctx : ValidKontext)
    (bs : List Byte) (e : CacheEintrag)
    (hhit : cacheFind c ctx bs = some e)
    (hval : eintragOk e = true) :
    decode bs = some (⟨e.befehl, e.laenge⟩, e.rest) ∧
      e.kontext = ctx ∧ laengeOk e.laenge = true := by
  obtain ⟨_, hctx, hbs⟩ := cacheFind_hit_gleich c ctx bs e hhit
  obtain ⟨hdec, hok⟩ := eintragOk_auspacken e hval
  subst hctx
  subst hbs
  exact ⟨hdec, rfl, hok⟩

/-- Witness context: profile 48, fixed bias. -/
def zeugenKontext : ValidKontext := ⟨.p48, 0⟩

/-- Witness entry: a validated `ret` over its one canonical byte. -/
def zeugenEintragRet : CacheEintrag :=
  ⟨zeugenKontext, [natByte 195], .ret, 1, []⟩

/-- The witness entry is well validated, by direct evaluation. -/
theorem zeugenEintragRet_ok : eintragOk zeugenEintragRet = true := by
  decide

/-- HIT WITNESS: the exact validated bytes hit the stored entry. -/
theorem zeugenTreffer :
    cacheFind [zeugenEintragRet] zeugenKontext [natByte 195] =
      some zeugenEintragRet := by
  decide

/-- MISS WITNESS (bytes): one forged byte refuses, with the entry present. -/
theorem zeugenMiss_bytes :
    cacheFind [zeugenEintragRet] zeugenKontext [natByte 194] = none := by
  decide

/-- A different bias is a different context, even on identical bytes. -/
def zeugenKontextAnderer : ValidKontext := ⟨.p48, 4096⟩

/-- MISS WITNESS (context): identical bytes under another bias refuse. -/
theorem zeugenMiss_kontext :
    cacheFind [zeugenEintragRet] zeugenKontextAnderer [natByte 195] =
      none := by
  decide

/-- JOINT REUSE WITNESS: the generic reuse theorem applied to the concrete
    validated entry replays the `ret` decode for the queried bytes. -/
theorem zeugenWiederverwendung_angewandt :
    decode [natByte 195] =
        some (⟨zeugenEintragRet.befehl, zeugenEintragRet.laenge⟩,
          zeugenEintragRet.rest) ∧
      zeugenEintragRet.kontext = zeugenKontext ∧
      laengeOk zeugenEintragRet.laenge = true :=
  treffer_wiederverwendung _ _ _ _ zeugenTreffer zeugenEintragRet_ok

/- CUTS:
    Proved here: cache identity completeness (`cacheFind_hit_gleich`: a hit
    returns a stored entry with exactly the queried context and bytes),
    failure on different bytes (`cacheFind_verweigert_bei_fremden_bytes`)
    and on different context (`cacheFind_verweigert_bei_fremdem_kontext`),
    validated-means-decided (`eintragOk_auspacken`), sound reuse from actual
    input equality (`treffer_wiederverwendung`), and concrete evaluated
    witnesses: a validated `ret` entry, an exact-bytes hit, a forged-byte
    miss, a same-bytes other-bias miss, and the generic reuse theorem
    applied to the concrete entry.
    NOT proved here, and not claimed:
    - No hash and no collision claim: lookup compares actual bytes and the
      actual context linearly; performance of any real cache is OPEN.
    - No semantic conclusion beyond decode replay: reuse replays the stored
      (`befehl`, `laenge`, `rest`) triple through the accepted decoder only.
      Correspondence of that triple to source, contracts, costs, locks,
      regions, control flow or any profile/region/control binding beyond
      the compared (profile, bias) pair is OPEN.
    - No whole-image or multi-instruction validation: entries cover single
      fetched windows; sequential/cache-evicting reasoning is OPEN.
    - No hardware, OS, loader, concurrency, TSO, timing or termination
      claim; no second decoder or IR is introduced.
-/

#print axioms cacheFind_hit_gleich
#print axioms cacheFind_verweigert_bei_fremden_bytes
#print axioms cacheFind_verweigert_bei_fremdem_kontext
#print axioms eintragOk_auspacken
#print axioms treffer_wiederverwendung
#print axioms zeugenEintragRet_ok
#print axioms zeugenTreffer
#print axioms zeugenMiss_bytes
#print axioms zeugenMiss_kontext
#print axioms zeugenWiederverwendung_angewandt

end ValidCache

end Gabbro.Grammatik.X86
