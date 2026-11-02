module

public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Round.Rundlauf.Teil1
public import Grammatik.Kern.Syntax.Profil.Teil1

@[expose] public section

/-!
  File:      Grammatik/Parser/Profil/Register.lean
  Subject:   **C14: the source-bound profile.** The `profile { .. }` and `requires profile { .. }` items
             of the ORIGINAL parsed tree, the registry of the `assume` declarations they reference, the
             closed decoder of the keyed modes, and the Bool that admits the whole binding (`bindungB`).

  Retains the one `Profil`/`Bibliothek` architecture of `Kern/Syntax/Profil`:
  * a keyed entry is decoded by a CLOSED decoder (`schluesselVon`/`wertVon`): an unknown key or an
    unsupported value is refused, there is no arbitrary `Nat` code and no missing-key `0`; every
    supported value is a positive code;
  * an `assume n` entry is a reference into the registry of the unit's `assume` declarations
    (`AnnahmeKennung`: name, machine, text, class); a reference to a name no declaration carries, or to
    a name two declarations carry with different content, is refused. Content equality is DECIDED over
    these finite records, never over arbitrary `Prop`s;
  * the keyed half becomes a `Profil D`/`Bibliothek D` of keyed entries (`modusProfil`,
    `modusBibliothek`), so `profil_modell` and `bindung_fuegt_nichts_hinzu` apply unchanged
    (`modusProfil_modell`, `bindung_fuegt_nichts_hinzu_bindung`).

  Free prose is never proved here: an `assume` constrains nothing in Lean (`erfuellt .frei = True` is the
  mode projection of the model, not evidence of hardware); the named hardware components are the ones of
  `HardwareAnnahmen` (`Zielsatz/Projekte/Profil.lean`).
-/

namespace Gabbro.Grammatik.Parser.ProfilBindung

open Gabbro.Grammatik

/-! ## The closed decoder of the keyed modes -/

/-- The five keys of a keyed mode entry, by their source spelling. Any other word is no key. -/
def schluesselVon (s : String) : Option ProfilSchluessel :=
  if strEq s "arch" then some .arch
  else if strEq s "rounding" then some .fpRundung
  else if strEq s "fp_contract" then some .fpKontraktion
  else if strEq s "memory_model" then some .speichermodell
  else if strEq s "interrupt_routing" then some .interruptRouting
  else none

/-- The value of a key by its source spelling. Only the modes the model and the emitted image have a
    meaning for are supported, each a positive code: `arch` x86_64 (1) / aarch64 (2), `rounding` nearest,
    `fp_contract` off (the float prelude binds `-ffp-contract=off`, `N218`), `memory_model` c11,
    `interrupt_routing` fest. Anything else is refused. -/
def wertVon (k : ProfilSchluessel) (v : String) : Option Nat :=
  match k with
  | .arch => if strEq v "x86_64" then some 1 else if strEq v "aarch64" then some 2 else none
  | .fpRundung => if strEq v "nearest" then some 1 else none
  | .fpKontraktion => if strEq v "off" then some 1 else none
  | .speichermodell => if strEq v "c11" then some 1 else none
  | .interruptRouting => if strEq v "fest" then some 1 else none

/-- The entry name a decoded key carries in the model profile. -/
def schluesselName : ProfilSchluessel → String
  | .arch => "arch"
  | .fpRundung => "rounding"
  | .fpKontraktion => "fp_contract"
  | .speichermodell => "memory_model"
  | .interruptRouting => "interrupt_routing"

/-- Distinct keys carry distinct entry names. -/
theorem schluesselName_inj {k k' : ProfilSchluessel} (h : schluesselName k = schluesselName k') :
    k = k' := by
  cases k <;> cases k' <;> first | rfl | (exfalso; simp [schluesselName] at h)

/-- The decoded pair of a keyed entry; an `assume` entry has none, an undecodable one has none. -/
def modusPaar : SProfEintrag → Option (ProfilSchluessel × Nat)
  | .mode k v => (schluesselVon k).bind fun key => (wertVon key v).map fun val => (key, val)
  | .assum _ => none

/-- An entry is decidable: an `assume` always, a keyed entry when it decodes. -/
def entscheidbar : SProfEintrag → Bool
  | .mode k v => (modusPaar (.mode k v)).isSome
  | .assum _ => true

/-- The decoded keyed pairs of a block. -/
def modi (es : List SProfEintrag) : List (ProfilSchluessel × Nat) := es.filterMap modusPaar

/-- The `assume` names of a block. -/
def annahmeNamen : List SProfEintrag → List String
  | [] => []
  | .assum n :: rest => n :: annahmeNamen rest
  | .mode _ _ :: rest => annahmeNamen rest

/-- Key agreement of decoded pairs: one key, one value. -/
def einig (ps : List (ProfilSchluessel × Nat)) : Bool :=
  ps.all fun a => ps.all fun b => decide (a.1 = b.1 → a.2 = b.2)

theorem einig_iff (ps : List (ProfilSchluessel × Nat)) :
    einig ps = true ↔ ∀ a ∈ ps, ∀ b ∈ ps, a.1 = b.1 → a.2 = b.2 := by
  simp only [einig, List.all_eq_true, decide_eq_true_eq]

/-- Equality of two keyed or `assume` entries is equality of their text, and implies equality. -/
theorem beqSProfEintrag_klingt : ∀ a b : SProfEintrag, beqSProfEintrag a b = true → a = b
  | .mode a b, .mode c d, h => by
      simp only [beqSProfEintrag, Bool.and_eq_true, strEq_eq] at h
      obtain ⟨h1, h2⟩ := h
      rw [h1, h2]
  | .assum a, .assum b, h => by
      simp only [beqSProfEintrag, strEq_eq] at h
      rw [h]
  | .mode _ _, .assum _, h => by simp only [beqSProfEintrag, Bool.false_eq_true] at h
  | .assum _, .mode _ _, h => by simp only [beqSProfEintrag, Bool.false_eq_true] at h

/-! ## The registry of the `assume` declarations -/

/-- One `assume` declaration with all it says: its name, the machine it is about, its statement text and its
    class (falsifier probe or trusted). Two records are the same assumption iff `gleich`. -/
structure AnnahmeKennung where
  name : String
  arch : Option String
  text : String
  klasse : SAnKlasse
  deriving Repr

/-- Content identity of two declarations (decided over the finite record). -/
def AnnahmeKennung.gleich (a b : AnnahmeKennung) : Bool :=
  strEq a.name b.name && beqOptWort a.arch b.arch && strEq a.text b.text && beqSAnKlasse a.klasse b.klasse

mutual
/-- The `assume` declarations of an item, modules opened, `pub` and gates transparent. -/
def annahmenI : SItemTief → List AnnahmeKennung
  | .modT _ b => annahmenL b
  | .pubT it => annahmenI it
  | .gateT it => annahmenI it
  | .assumT n a t k => [⟨n, a, t, k⟩]
  | _ => []
/-- The `assume` declarations of an item list, in order. -/
def annahmenL : List SItemTief → List AnnahmeKennung
  | [] => []
  | it :: rest => annahmenI it ++ annahmenL rest
end

/-- A reference `assume n` resolves: some declaration carries the name, and every declaration of that name
    has the same content as the first (`N219`, `N216`). -/
def aufgeloest (reg : List AnnahmeKennung) (n : String) : Bool :=
  match reg.filter (fun a => strEq a.name n) with
  | [] => false
  | a :: rest => rest.all (fun b => a.gleich b)

/-! ## The profile blocks of the tree -/

/-- One `profile { .. }` (`bedarf = false`) or `requires profile { .. }` (`bedarf = true`) block with the
    module path it stands in. -/
structure ProfilBlock where
  modul : List String
  bedarf : Bool
  eintraege : List SProfEintrag
  deriving Repr

mutual
/-- The profile blocks of an item, with the module path they stand in. -/
def bloeckeI (modul : List String) : SItemTief → List ProfilBlock
  | .modT n b => bloeckeL (modul ++ [n]) b
  | .pubT it => bloeckeI modul it
  | .gateT it => bloeckeI modul it
  | .profT bedarf es => [⟨modul, bedarf, es⟩]
  | _ => []
/-- The profile blocks of an item list, in order. -/
def bloeckeL (modul : List String) : List SItemTief → List ProfilBlock
  | [] => []
  | it :: rest => bloeckeI modul it ++ bloeckeL modul rest
end

/-- **The profile binding of a tree**: its profile blocks (at most one admitted), the requirement blocks of
    the linked libraries, and the registry of its `assume` declarations. -/
structure ProfileBinding where
  profile : List ProfilBlock
  bedarfe : List ProfilBlock
  register : List AnnahmeKennung
  deriving Repr

/-- The binding read off a parsed tree. -/
def ProfileBinding.aus (items : List SItemTief) : ProfileBinding :=
  let bs := bloeckeL [] items
  { profile := bs.filter (fun b => !b.bedarf)
    bedarfe := bs.filter (fun b => b.bedarf)
    register := annahmenL items }

/-- A block is sound: every keyed entry decodes, the decoded modes agree (`N215`), and every `assume`
    reference resolves (`N219`, `N216`). -/
def blockOk (reg : List AnnahmeKennung) (b : ProfilBlock) : Bool :=
  b.eintraege.all entscheidbar && einig (modi b.eintraege) &&
    (annahmeNamen b.eintraege).all (aufgeloest reg)

/-- A requirement entry stands in the profile with identical content (`N217`). -/
def gedeckt (p : ProfilBlock) (e : SProfEintrag) : Bool :=
  p.eintraege.any fun x => beqSProfEintrag x e

/-- Linking: with a profile every requirement of every library is covered by it; without one no library may
    require anything. -/
def deckungB (b : ProfileBinding) : Bool :=
  match b.profile with
  | [] => b.bedarfe.all (fun lib => lib.eintraege.isEmpty)
  | p :: _ => b.bedarfe.all (fun lib => lib.eintraege.all (gedeckt p))

/-- **The profile binding is admitted**: one profile at most (`N219`), sound blocks, linked requirements
    covered (`N217`). -/
def bindungB (b : ProfileBinding) : Bool :=
  decide (b.profile.length ≤ 1) && b.profile.all (blockOk b.register) &&
    b.bedarfe.all (blockOk b.register) && deckungB b

theorem bindungB_zerlegt {b : ProfileBinding} (h : bindungB b = true) :
    b.profile.length ≤ 1 ∧ (∀ p ∈ b.profile, blockOk b.register p = true) ∧
      (∀ p ∈ b.bedarfe, blockOk b.register p = true) ∧ deckungB b = true := by
  simp only [bindungB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- An admitted block has one value per key. -/
theorem blockOk_einig {reg : List AnnahmeKennung} {b : ProfilBlock} (h : blockOk reg b = true) :
    einig (modi b.eintraege) = true := by
  simp only [blockOk, Bool.and_eq_true] at h
  exact h.1.2

/-- An admitted block references only resolved assumptions. -/
theorem blockOk_aufgeloest {reg : List AnnahmeKennung} {b : ProfilBlock} (h : blockOk reg b = true) :
    ∀ n ∈ annahmeNamen b.eintraege, aufgeloest reg n = true := by
  simp only [blockOk, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2

/-- An admitted block has every keyed entry decoded: the closed decoder knows its key and value. -/
theorem blockOk_dekodiert {reg : List AnnahmeKennung} {b : ProfilBlock} (h : blockOk reg b = true)
    {k v : String} (hm : SProfEintrag.mode k v ∈ b.eintraege) :
    ∃ key val, schluesselVon k = some key ∧ wertVon key v = some val := by
  simp only [blockOk, Bool.and_eq_true, List.all_eq_true] at h
  have he := h.1.1 _ hm
  simp only [entscheidbar, modusPaar] at he
  cases hk : schluesselVon k with
  | none => simp [hk] at he
  | some key =>
      cases hv : wertVon key v with
      | none => simp [hk, hv] at he
      | some val => exact ⟨key, val, rfl, hv⟩

/-- With one profile `p`, every requirement entry of every admitted library stands in `p`. -/
theorem bindungB_gedeckt {b : ProfileBinding} (h : bindungB b = true) {p : ProfilBlock}
    (hp : b.profile = [p]) {lib : ProfilBlock} (hl : lib ∈ b.bedarfe) {e : SProfEintrag}
    (he : e ∈ lib.eintraege) : e ∈ p.eintraege := by
  have hd := (bindungB_zerlegt h).2.2.2
  have hd' : b.bedarfe.all (fun lib => lib.eintraege.all (gedeckt p)) = true := by
    unfold deckungB at hd
    rw [hp] at hd
    exact hd
  have hg := List.all_eq_true.mp hd' lib hl
  have hge := List.all_eq_true.mp hg e he
  simp only [gedeckt, List.any_eq_true] at hge
  obtain ⟨x, hx, hbeq⟩ := hge
  have hxe := beqSProfEintrag_klingt x e hbeq
  rw [hxe] at hx
  exact hx

/-- Without a profile, no library requires anything. -/
theorem bindungB_ohne_profil {b : ProfileBinding} (h : bindungB b = true) (hp : b.profile = [])
    {lib : ProfilBlock} (hl : lib ∈ b.bedarfe) : lib.eintraege = [] := by
  have hd := (bindungB_zerlegt h).2.2.2
  have hd' : b.bedarfe.all (fun lib => lib.eintraege.isEmpty) = true := by
    unfold deckungB at hd
    rw [hp] at hd
    exact hd
  exact List.isEmpty_iff.mp (List.all_eq_true.mp hd' lib hl)

/-! ## The model profile of the keyed half -/

/-- The model entry of a decoded keyed pair. -/
def modusEintrag (D : Deklaration) (p : ProfilSchluessel × Nat) : AnnahmeEintrag D :=
  .modus (schluesselName p.1) "ziel" p.1 p.2

/-- The model profile of decoded keyed pairs. -/
def modusProfil (D : Deklaration) (ps : List (ProfilSchluessel × Nat)) : Profil D :=
  ps.map (modusEintrag D)

/-- The model library of decoded keyed requirement pairs. -/
def modusBibliothek (D : Deklaration) (name : String) (ps : List (ProfilSchluessel × Nat)) :
    Bibliothek D :=
  ⟨name, ps.map fun p => Anforderung.modus (schluesselName p.1) "ziel" p.1 p.2⟩

/-- **Agreeing decoded modes are a good profile** (`Profil.gut`): key agreement, and same-named entries
    (same key, hence one name) carry one content. -/
theorem modusProfil_gut (D : Deklaration) {ps : List (ProfilSchluessel × Nat)}
    (h : einig ps = true) : Profil.gut (modusProfil D ps) := by
  have hE := (einig_iff ps).mp h
  constructor
  · intro a ha b hb k v w h1 h2
    have ha' : a ∈ ps.map (modusEintrag D) := ha
    have hb' : b ∈ ps.map (modusEintrag D) := hb
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb'
    obtain ⟨n1, c1, e1⟩ := h1
    obtain ⟨n2, c2, e2⟩ := h2
    simp only [modusEintrag, AnnahmeEintrag.modus.injEq] at e1 e2
    obtain ⟨_, _, hk1, hv1⟩ := e1
    obtain ⟨_, _, hk2, hv2⟩ := e2
    have hpq := hE p hp q hq (hk1.trans hk2.symm)
    exact hv1.symm.trans (hpq.trans hv2)
  · intro a ha b hb hname
    have ha' : a ∈ ps.map (modusEintrag D) := ha
    have hb' : b ∈ ps.map (modusEintrag D) := hb
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb'
    simp only [eintragName, modusEintrag] at hname
    have hk : p.1 = q.1 := schluesselName_inj hname
    have hv : p.2 = q.2 := hE p hp q hq hk
    show schluesselName p.1 = schluesselName q.1 ∧ "ziel" = "ziel" ∧ p.1 = q.1 ∧ p.2 = q.2
    exact ⟨by rw [hk], rfl, hk, hv⟩

/-- **The decoded modes of an admitted profile have a model** (`profil_modell`): a mode assignment under
    which every keyed entry holds. It proves no free prose and no hardware. -/
theorem modusProfil_modell (D : Deklaration) {ps : List (ProfilSchluessel × Nat)}
    (h : einig ps = true) : ∃ m : ModusBelegung, Profil.gilt (modusProfil D ps) m := by
  refine profil_modell (modusProfil D ps) (modusProfil_gut D h) ?_
  intro a ha
  have ha' : a ∈ ps.map (modusEintrag D) := ha
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha'
  exact ⟨p.1, p.2, schluesselName p.1, "ziel", rfl⟩

/-- **Covered keyed requirements bind** (`Profil.bindet`): a library whose decoded requirement pairs all
    stand among the profile's pairs is bound by the model profile. -/
theorem modusBibliothek_bindet (D : Deklaration) (name : String)
    {ps bs : List (ProfilSchluessel × Nat)} (h : ∀ q ∈ bs, q ∈ ps) :
    Profil.bindet (modusProfil D ps) (modusBibliothek D name bs) := by
  intro r hr
  have hr' : r ∈ bs.map fun p => Anforderung.modus (D := D) (schluesselName p.1) "ziel" p.1 p.2 := hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr'
  refine ⟨modusEintrag D q, ?_, rfl, ?_⟩
  · exact List.mem_map.mpr ⟨q, h q hq, rfl⟩
  · show schluesselName q.1 = schluesselName q.1 ∧ "ziel" = "ziel" ∧ q.1 = q.1 ∧ q.2 = q.2
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- A decoded pair of a covered entry is a decoded pair of the covering block. -/
theorem modi_mono {es fs : List SProfEintrag} (h : ∀ e ∈ es, e ∈ fs) :
    ∀ q ∈ modi es, q ∈ modi fs := by
  intro q hq
  obtain ⟨e, he, hq'⟩ := List.mem_filterMap.mp hq
  exact List.mem_filterMap.mpr ⟨e, h e he, hq'⟩

/-- **Linking adds nothing, for the source-bound profile**: if the binding is admitted with one profile `p`
    and a library `lib` in it, then every mode assignment under which the profile's decoded modes hold
    makes the library's decoded requirements hold. -/
theorem bindung_fuegt_nichts_hinzu_bindung (D : Deklaration) (name : String) {b : ProfileBinding}
    (h : bindungB b = true) {p : ProfilBlock} (hp : b.profile = [p]) {lib : ProfilBlock}
    (hl : lib ∈ b.bedarfe) (m : ModusBelegung)
    (hgilt : Profil.gilt (modusProfil D (modi p.eintraege)) m) :
    Bibliothek.gilt (modusBibliothek D name (modi lib.eintraege)) m := by
  have hsub : ∀ q ∈ modi lib.eintraege, q ∈ modi p.eintraege :=
    modi_mono (fun e he => bindungB_gedeckt h hp hl he)
  exact bindung_fuegt_nichts_hinzu (modusProfil D (modi p.eintraege))
    (modusBibliothek D name (modi lib.eintraege)) m hgilt
    (modusBibliothek_bindet D name hsub)

end Gabbro.Grammatik.Parser.ProfilBindung
