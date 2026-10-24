/-
  File:      Grammatik/Gen/Abdeckung/Erklaerung.lean
  Subject:   WHAT A DECLARATION CONTAINS, as the members of the model's register: `Spez.mitglieder` names every
             member of `Deklaration`, `Signatur`, `Regklasse`, `Ty`, `ArenaForm`, `DynForm` that the declaration of a
             specification exercises in a non-default way (a lock with a rank, a mask, an owner mark, an atomic with a
             payload, a state transition, a register of a class, a mirrored register, a foreign body with a channel,
             a function that holds a lock, ...). The proof fields are named when the declaration holds a NON-TRIVIAL
             instance of them (the filter of `eigner_nie_erzeugt` removes something, the guard of `geteilt_bewacht`
             is needed, `invarianten_gehalten` adds a lock).
-/
import Grammatik.Gen.Familie.Familie
import Grammatik.Gen.Abdeckung.Mitglieder

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik

variable (z : Spez)

/-- The effective held locks of signature `n` are not empty (declared or added for an invariant). -/
def Spez.haeltIrgendwo : Bool := (List.range z.sigs.length).any fun n => !(z.haelt n).isEmpty

/-- Some signature produces a mark that a table owns (the filter of `eigner_nie_erzeugt` has something to remove). -/
def Spez.eignerGefiltert : Bool :=
  z.sigs.any fun s => s.produziert.any fun p => z.tabs.any fun t => t.eigner == some p.1

/-- Some signature adds a lock for an invariant. -/
def Spez.invSperreHinzu : Bool :=
  (List.range z.sigs.length).any fun n => (z.haelt n).any fun L => !(z.sigRoh n).haelt.contains L.val

/-- Some table is shared (and guarded). -/
def Spez.teilt : Bool := z.tabs.any fun t => t.geteilt && (t.sperre.isSome || t.eigner.isSome)

/-- Some static is shared (and guarded or atomic). -/
def Spez.gteilt : Bool := z.globs.any fun g => g.geteilt && (g.sperre.isSome || g.marke.isSome || g.atomar)

/-- The table `t` and the static `g` form an arena (`ArenaForm`): the counter ranges over `0 .. count`. -/
def Spez.arenaPaare : List (Nat × Nat) :=
  (List.range z.tabs.length).flatMap fun t => (List.range z.globs.length).filterMap fun g =>
    if (z.tabs.getD t { count := 0, felder := [] }).count > 0 &&
        (z.globs.getD g ⟨.bool, false, none, none, [], false, false⟩).typ ==
          .int 0 (z.tabs.getD t { count := 0, felder := [] }).count then some (t, g) else none

/-- **The members a declaration exercises.** -/
def Spez.mitglieder : List String :=
  let wenn : Bool → List String → List String := fun b xs => if b then xs else []
  let tabs := !z.tabs.isEmpty
  let globs := !z.globs.isEmpty
  let regs := !z.regs.isEmpty
  let axs := !z.axs.isEmpty
  let sigs := z.sigs
  ["Deklaration.Fn", "Deklaration.sig", "Deklaration.sigNr", "Deklaration.Annahme", "Deklaration.a10",
   "Deklaration.decTab", "Deklaration.decFeld", "Deklaration.decGlob", "Deklaration.decLock", "Deklaration.decMarke"] ++
  wenn tabs ["Deklaration.Tab", "Deklaration.Feld", "Deklaration.count", "Deklaration.typ", "Deklaration.tabNr"] ++
  wenn (z.tabs.any fun t => t.felder.any fun f => !f.erlaubt.isEmpty) ["Deklaration.erlaubt"] ++
  wenn globs ["Deklaration.Glob", "Deklaration.gtyp"] ++
  wenn (z.globs.any fun g => !g.nutzlast.isEmpty) ["Deklaration.nutzlast"] ++
  wenn (z.globs.any fun g => g.atomar) ["Deklaration.atomar"] ++
  wenn z.teilt ["Deklaration.geteilt", "Deklaration.geteilt_bewacht"] ++
  wenn z.gteilt ["Deklaration.ggeteilt", "Deklaration.ggeteilt_bewacht"] ++
  wenn (!z.locks.isEmpty) ["Deklaration.Lock", "Deklaration.rang"] ++
  wenn (z.locks.any fun L => L.maskiert) ["Deklaration.maskiert"] ++
  wenn (!z.marken.isEmpty) ["Deklaration.Marke", "Deklaration.stufen"] ++
  wenn (z.tabs.any fun t => t.sperre.isSome || t.eigner.isSome) ["Deklaration.braucht"] ++
  wenn (z.globs.any fun g => g.sperre.isSome || g.marke.isSome) ["Deklaration.gbraucht"] ++
  wenn (z.tabs.any fun t => t.eigner.isSome) ["Deklaration.eigner"] ++
  wenn z.eignerGefiltert ["Deklaration.eigner_nie_erzeugt"] ++
  wenn (!z.invs.isEmpty) ["Deklaration.Inv", "Deklaration.traeger", "Deklaration.invs"] ++
  wenn z.invSperreHinzu ["Deklaration.invarianten_gehalten"] ++
  wenn axs ["Deklaration.Ax", "Deklaration.aparams", "Deklaration.aerg"] ++
  wenn (z.axs.any fun a => !a.schreibt.isEmpty) ["Deklaration.aschreibt"] ++
  wenn (z.axs.any fun a => !a.gschreibt.isEmpty) ["Deklaration.agschreibt"] ++
  wenn (z.axs.any fun a => a.gruende > 0) ["Deklaration.agruende"] ++
  wenn regs ["Deklaration.Reg", "Deklaration.rtyp", "Deklaration.rklasse", "Deklaration.rzusage"] ++
  wenn (z.regs.any fun r => r.spiegel.isSome) ["Deklaration.spiegel"] ++
  wenn (z.regs.any fun r => !r.traeger.isEmpty) ["Deklaration.rtraeger"] ++
  wenn (z.tabs.any fun t => t.geist) ["Deklaration.geist"] ++
  wenn (z.globs.any fun g => g.geist) ["Deklaration.ggeist"] ++
  -- Signatur
  wenn (sigs.any fun s => !s.params.isEmpty) ["Signatur.params"] ++
  wenn (sigs.any fun s => s.erg.isSome) ["Signatur.erg"] ++
  wenn (sigs.any fun s => s.gruende > 0) ["Signatur.gruende"] ++
  wenn z.haeltIrgendwo ["Signatur.haelt"] ++
  wenn (sigs.any fun s => !s.schreibt.isEmpty) ["Signatur.schreibt"] ++
  wenn (sigs.any fun s => !s.gschreibt.isEmpty) ["Signatur.gschreibt"] ++
  wenn (sigs.any fun s => !s.konsumiert.isEmpty) ["Signatur.konsumiert"] ++
  wenn (sigs.any fun s => !(z.produziert 0).isEmpty || !s.produziert.isEmpty) ["Signatur.produziert"] ++
  wenn (sigs.any fun s => s.boden.isSome) ["Signatur.boden"] ++
  -- Regklasse
  (z.regs.flatMap fun r => klasseM' r.klasse) ++
  -- Ty
  (z.typen.flatMap tyM) ++ wenn (z.axs.any fun a => a.erg == some .never) ["Ty.never"] ++
  -- ArenaForm, DynForm
  wenn (!z.arenaPaare.isEmpty)
    ["ArenaForm.tab", "ArenaForm.feld", "ArenaForm.zaehl", "ArenaForm.hz", "ArenaForm.hpos"] ++
  wenn (z.arenaPaare.any fun p => z.arenaPaare.any fun q => p.1 == q.1 && p.2 != q.2)
    ["DynForm.komm", "DynForm.hk", "DynForm.hzwei"]
where
  klasseM' : Regklasse → List String
    | .r => ["Regklasse.r"]
    | .w => ["Regklasse.w"]
    | .rw => ["Regklasse.rw"]
    | .w1c => ["Regklasse.w1c"]
    | .rc => ["Regklasse.rc"]

end Gabbro.Grammatik.Gen
