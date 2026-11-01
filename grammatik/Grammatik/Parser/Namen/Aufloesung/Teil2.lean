module

public import Grammatik.Parser.Elab.Uebersetze
public import Grammatik.Parser.Namen.Namensraum
public import Grammatik.Parser.Namen.Aufloesung.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser.Aufloesung
open Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Namensraum (Pfad Quelle Platz aufloeseK)
set_option maxRecDepth 100000

/-- A transition, resolved. -/
def trans (k : Kontext) (t : STrans) : STrans :=
  { t with
    schritte := t.schritte.map fun (a, b, c) => (aus k a, aus k b, aus k c)
    voraus := ausO k t.voraus
    wirkung := t.wirkung.map (effekt k) }

/-- A device member, resolved. -/
def gerTeil (k : Kontext) : SGerTeil → SGerTeil
  | .copy a b => .copy (aus k a) (aus k b)
  | .reg r => .reg { r with rtyp := typ k r.rtyp, addr := aus k r.addr, voraus := ausO k r.voraus }
  | .trans t => .trans (trans k t)
  | g => g

/-- A binding of a gate, resolved. -/
def bindung (k : Kontext) (b : SBind) : SBind :=
  { b with id := aus k b.id, codes := b.codes.map fun (e, n, g) => (e, ausO k n, g) }

/-- Where a gate rests, resolved: the assumption it names. -/
def herkunft (k : Kontext) : SHerkunft → SHerkunft
  | .assum n c => .assum (k.ref n) c
  | h => h

/-- **A `syscall` gate, resolved.** -/
def syscall (k : Kontext) (c : SSyscall) : SSyscall :=
  let k' := k.mit (c.params.map Prod.fst)
  { c with
    name := k.eigen c.name
    params := c.params.map fun (n, t) => (n, typ k t)
    res := typO k c.res
    fail := c.fail.map k.ref
    way := match c.way with
      | .lit abi arch b h => .lit abi arch (bindung k' b) (herkunft k h)
      | .via v => .via (k.ref v)
    gate := { pre := c.gate.pre.map (aus k'), post := c.gate.post.map (aus k'),
              uses := c.gate.uses.map (effekt k'), cost := ausO k' c.gate.cost } }

/-- **An item, resolved** in its module: its own key and every name it writes. Item kinds without a G
    form pass unchanged (the elaborator refuses them). -/
def item (k : Kontext) : SItemTief → SItemTief
  | .typeT fl n args ord t => .typeT fl (k.eigen n) (args.map (typ k)) ord (typO k t)
  | .constT n t v => .constT (k.eigen n) (typ k t) (konst k v)
  | .globT m n t v al s sh => .globT m (k.eigen n) (typ k t) (konst k v) (ausO k al) s sh
  | .fnT s b => .fnT (sig k s) (anw (k.mit (s.params.map Prod.fst)) b)
  | .protoT s => .protoT (sig k s)
  | .specT s p => .specT (sig k s) (aus (k.mit (s.params.map Prod.fst)) p)
  | .asmT s h => .asmT (sig k s) h
  | .tableT n v c b o sh ps => .tableT (k.eigen n) (v.map k.ref) (ausO k c) b o sh (ps.map (tabTeil k))
  | .lockT n ps rk h sh m i =>
    .lockT (k.eigen n) (ps.map (aus k)) (aus k rk) (ausO k h) (ausO k sh) m (ausO k i)
  | .atomT n t p o b => .atomT (k.eigen n) (typ k t) (p.map (·.map (aus k))) o b
  | .arenaT n lo hi mx t pb =>
    .arenaT (k.eigen n) (aus k lo) (aus k hi) (ausO k mx) (typ k t) (pb.map fun (ps, e) => (ps, aus k e))
  | .assumT n a s c => .assumT (k.eigen n) a s c
  | .whyT n cs ex => .whyT (k.eigen n) (cs.map fun (a, e, b) => (a, aus k e, b)) ex
  | .callT c => .callT (syscall k c)
  | .varT n => .varT (k.eigen n)
  | .goalT n o => .goalT n (o.map fun (abi, arch, bs) => (abi, arch, bs.map fun (v, b, h) =>
      (k.ref v, bindung k b, herkunft k h)))
  | .entryT e => .entryT { e with name := k.eigen e.name, vektor := ausO k e.vektor, ist := ausO k e.ist,
                                  dispatch := k.pfad e.dispatch }
  | .concT ps => .concT (ps.map fun (p, a) => (k.pfad p, a.map (aus k)))
  | .devT n ps sp ms =>
    .devT (k.eigen n) (ps.map fun (x, t) => (x, typ k t)) sp (ms.map (gerTeil (k.mit (ps.map Prod.fst))))
  | .groupT n ns is => .groupT (k.eigen n) (ns.map k.ref) (is.map (inv k))
  | .stateT n ts => .stateT (k.eigen n) (ts.map (trans k))
  | .pubT it => item k it
  | it => it

mutual
/-- The items of a unit, resolved and flat: module wrappers opened, `use` lines dropped. -/
def loeseI (q : Quelle) (von : Pfad) : SItemTief → List SItemTief
  | .modT p b => loeseL q (von ++ segmente p) b
  | .useT _ => []
  | .pubT it => loeseI q von it
  | it => [item ⟨q, von, []⟩ it]
def loeseL (q : Quelle) (von : Pfad) : List SItemTief → List SItemTief
  | [] => []
  | it :: rest => loeseI q von it ++ loeseL q von rest
end

/-- An item list of one name space: no `use`, no module. -/
def flach : List SItemTief → Bool
  | [] => true
  | .modT _ _ :: _ => false
  | .useT _ :: _ => false
  | .pubT (.modT _ _) :: _ => false
  | .pubT (.useT _) :: _ => false
  | _ :: rest => flach rest

/-- **A unit of one name space**: no `use` line, and at most one module wrapper around flat items. -/
def einfach : List SItemTief → Bool
  | [.modT _ b] => flach b
  | its => flach its

/-- **The resolution of a unit**: one name space as before (`uMembers`); else every name by the
    name-space rule and every item under its key. -/
def loese (items : List SItemTief) : List SItemTief :=
  if einfach items then Uebersetze.uMembers items else loeseL (quelle items) [] items

/-- **A unit of one name space is resolved as before.** -/
theorem loese_einfach {items : List SItemTief} (h : einfach items = true) :
    loese items = Uebersetze.uMembers items := by
  simp only [loese, h, ↓reduceIte]

/-- **A local stays what it is.** -/
theorem ref_lokal {k : Kontext} {s : String} (h : k.lok.any (strEq · s) = true) : k.ref s = s := by
  simp only [Kontext.ref, h, ↓reduceIte]

/-- **A name that resolves names its item's key.** -/
theorem ref_aufgeloest {k : Kontext} {s : String} {c : Pfad} (hl : k.lok.any (strEq · s) = false)
    (h : aufloeseK k.q ⟨none, []⟩ k.von (segmente s) = some c) :
    k.ref s = schluessel k.q.namen c := by
  simp only [Kontext.ref, hl, Bool.false_eq_true, ↓reduceIte, h]

/-- **A name of an item that is not visible from here is poisoned**: no item carries the text. -/
theorem ref_unsichtbar {k : Kontext} {s : String} (hl : k.lok.any (strEq · s) = false)
    (h : aufloeseK k.q ⟨none, []⟩ k.von (segmente s) = none)
    (hn : k.q.namen.any (fun q => strEq (letzter q) (letzter (segmente s))) = true) :
    k.ref s = gift s := by
  simp only [Kontext.ref, hl, Bool.false_eq_true, ↓reduceIte, h, hn]

/-- **An item whose short name no other item has keeps its short name.** -/
theorem schluessel_kurz {namen : List Pfad} {c : Pfad}
    (h : (namen.filter fun q => strEq (letzter q) (letzter c)).length = 1) :
    schluessel namen c = letzter c := by
  simp only [schluessel, h, BEq.rfl, ↓reduceIte]

end Gabbro.Grammatik.Parser.Aufloesung
