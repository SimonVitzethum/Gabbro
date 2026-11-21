module
public import Bruecke.Ausdruck.Readers
@[expose] public section

/-!
# A function table the kernel searches in logarithmic time

`fnSuch u n` is a linear search of `u.fns`; in a generated duty module the kernel evaluates it
for every call of the function, so the cost of each module grows with the unit. `Tabelle` is a
binary trie over the bits of a hash of the name: a search follows `tiefe` bits (natural-number
division by two, which the kernel computes on literals) and then scans one bucket.

`suche_bauen` is the whole correctness argument, generic and proved once: the trie built from a
list answers exactly as the first-match search of that list, for every name, duplicates included.
No ordering, no sortedness, no hash property is needed: the hash only spreads the buckets.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik.Parser.Uebersetze

/-- A cheap hash of a name; it only spreads the buckets, correctness never depends on it. -/
def namensHash (n : String) : Nat :=
  n.toList.foldl (fun h c => (h * 31 + c.toNat) % 1048576) 7

/-- A binary trie of named entries: buckets at depth 0, one bit per level. -/
inductive Tabelle (α : Type) where
  | leer
  | knoten (eimer : List (String × α)) (null eins : Tabelle α)
  deriving Repr

namespace Tabelle

variable {α : Type}

/-- Search at depth `d` along the key `k`; the bucket is searched by name, first match. -/
def sucheK : Nat → Tabelle α → Nat → String → Option α
  | _, .leer, _, _ => none
  | 0, .knoten e _ _, _, n => (e.find? (·.1 == n)).map (·.2)
  | d + 1, .knoten _ l r, k, n => if k % 2 = 0 then sucheK d l (k / 2) n else sucheK d r (k / 2) n

/-- Insert in front at depth `d` along the key `k` (an earlier entry of the same name is shadowed). -/
def einfuegenK : Nat → Tabelle α → Nat → String → α → Tabelle α
  | 0, .leer, _, n, a => .knoten [(n, a)] .leer .leer
  | 0, .knoten e l r, _, n, a => .knoten ((n, a) :: e) l r
  | d + 1, .leer, k, n, a =>
    if k % 2 = 0 then .knoten [] (einfuegenK d .leer (k / 2) n a) .leer
    else .knoten [] .leer (einfuegenK d .leer (k / 2) n a)
  | d + 1, .knoten e l r, k, n, a =>
    if k % 2 = 0 then .knoten e (einfuegenK d l (k / 2) n a) r
    else .knoten e l (einfuegenK d r (k / 2) n a)

/-- Whether two keys agree on their lowest `d` bits. -/
def gleich : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | d + 1, k, k' => k % 2 == k' % 2 && gleich d (k / 2) (k' / 2)

theorem gleich_self : ∀ (d k : Nat), gleich d k k = true
  | 0, _ => rfl
  | d + 1, k => by simp only [gleich, BEq.rfl, Bool.true_and]; exact gleich_self d (k / 2)

theorem sucheK_leer : ∀ (d k : Nat) (n : String), sucheK d (leer : Tabelle α) k n = none
  | 0, _, _ => rfl
  | _ + 1, _, _ => rfl

theorem sucheK_einfuegenK : ∀ (d : Nat) (t : Tabelle α) (k k' : Nat) (m n : String) (a : α),
    sucheK d (einfuegenK d t k m a) k' n =
      if gleich d k k' = true ∧ (m == n) = true then some a else sucheK d t k' n
  | 0, .leer, k, k', m, n, a => by
    by_cases h : (m == n) = true
    · simp [sucheK, einfuegenK, gleich, h]
    · simp [sucheK, einfuegenK, gleich, h]
  | 0, .knoten e l r, k, k', m, n, a => by
    by_cases h : (m == n) = true
    · simp [sucheK, einfuegenK, gleich, h]
    · simp [sucheK, einfuegenK, gleich, h]
  | d + 1, .leer, k, k', m, n, a => by
    have ih := sucheK_einfuegenK d (.leer : Tabelle α) (k / 2) (k' / 2) m n a
    rw [sucheK_leer] at ih
    by_cases hk : k % 2 = 0 <;> by_cases hk' : k' % 2 = 0
    · simp only [einfuegenK, hk, ite_true, sucheK, hk', ih, gleich]; simp [hk, hk']
    · have hne : (k % 2 == k' % 2) = false := by simp only [beq_eq_false_iff_ne]; omega
      simp only [einfuegenK, hk, ite_true, sucheK, hk', ite_false, sucheK_leer, gleich]; simp; intro h; exfalso; omega
    · have hne : (k % 2 == k' % 2) = false := by simp only [beq_eq_false_iff_ne]; omega
      simp only [einfuegenK, hk, ite_false, sucheK, hk', ite_true, sucheK_leer, gleich]; simp; intro h; exfalso; omega
    · have : k % 2 = k' % 2 := by omega
      simp only [einfuegenK, hk, ite_false, sucheK, hk', ih, gleich]; simp [this]
  | d + 1, .knoten e l r, k, k', m, n, a => by
    by_cases hk : k % 2 = 0 <;> by_cases hk' : k' % 2 = 0
    · have ih := sucheK_einfuegenK d l (k / 2) (k' / 2) m n a
      simp only [einfuegenK, hk, ite_true, sucheK, hk', ih, gleich]; simp [hk, hk']
    · have hne : (k % 2 == k' % 2) = false := by simp only [beq_eq_false_iff_ne]; omega
      simp only [einfuegenK, hk, ite_true, sucheK, hk', ite_false, gleich]; simp; intro h; exfalso; omega
    · have hne : (k % 2 == k' % 2) = false := by simp only [beq_eq_false_iff_ne]; omega
      simp only [einfuegenK, hk, ite_false, sucheK, hk', ite_true, gleich]; simp; intro h; exfalso; omega
    · have : k % 2 = k' % 2 := by omega
      have ih := sucheK_einfuegenK d r (k / 2) (k' / 2) m n a
      simp only [einfuegenK, hk, ite_false, sucheK, hk', ih, gleich]; simp [this]

/-- Search by name. -/
def suche (tiefe : Nat) (t : Tabelle α) (n : String) : Option α := sucheK tiefe t (namensHash n) n

/-- The trie of a list of keyed entries `(key, name, value)`; the first entry of a name wins. The
    keys are data: building computes no hash, so the kernel builds a large table with bit
    arithmetic only. That every key is the hash of its name is a separate, local fact. -/
def bauenK (tiefe : Nat) : List (Nat × String × α) → Tabelle α
  | [] => .leer
  | (k, n, a) :: rest => einfuegenK tiefe (bauenK tiefe rest) k n a

/-- **The trie answers as the first-match search of its list**, for every name, provided every
    key is the hash of its name. -/
theorem suche_bauenK (tiefe : Nat) : ∀ (ts : List (Nat × String × α)),
    (∀ p ∈ ts, p.1 = namensHash p.2.1) → ∀ n : String,
      suche tiefe (bauenK tiefe ts) n = (ts.find? (·.2.1 == n)).map (·.2.2)
  | [], _, n => sucheK_leer tiefe _ n
  | (k, m, a) :: rest, hk, n => by
    have hkm : k = namensHash m := hk _ List.mem_cons_self
    unfold suche at *
    simp only [bauenK]
    rw [sucheK_einfuegenK]
    by_cases h : (m == n) = true
    · have hmn : m = n := by simpa using h
      subst hmn hkm
      simp [gleich_self, List.find?_cons]
    · have ih := suche_bauenK tiefe rest (fun p hp => hk p (List.mem_cons_of_mem _ hp)) n
      unfold suche at ih
      simp only [h, and_false, ite_false, ih, List.find?_cons]
      simp [h]

end Tabelle

/-- The keyed entries of a list of functions: the hash of the name, the name, the function. -/
def tabellenSchluessel (fs : List UFn) : List (Nat × String × UFn) :=
  fs.map fun f => (namensHash f.name, f.name, f)

theorem tabellenSchluessel_append (xs ys : List UFn) :
    tabellenSchluessel (xs ++ ys) = tabellenSchluessel xs ++ tabellenSchluessel ys := List.map_append

/-- Appended keyed lists are the keyed list of the appended functions (assembly of the chunks). -/
theorem tabellenSchluessel_verbinde {a b : List (Nat × String × UFn)} {xs ys : List UFn}
    (ha : a = tabellenSchluessel xs) (hb : b = tabellenSchluessel ys) : a ++ b = tabellenSchluessel (xs ++ ys) := by
  rw [ha, hb, tabellenSchluessel_append]

/-- **The function table answers as the standard callee lookup** (the first function of the
    name, `instFnSuche`), for every list of functions and every name. -/
theorem funktionsTabelle_suche (tiefe : Nat) (fs : List UFn) (n : String) :
    Tabelle.suche tiefe (Tabelle.bauenK tiefe (tabellenSchluessel fs)) n = fs.find? (fun f => f.name == n) := by
  rw [Tabelle.suche_bauenK tiefe (tabellenSchluessel fs) (fun p hp => by
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hp
    rfl)]
  unfold tabellenSchluessel
  rw [List.find?_map]
  cases h : fs.find? (fun f => f.name == n) <;> simp [Function.comp_def, h]

#print axioms funktionsTabelle_suche

end Gabbro.Bruecke
