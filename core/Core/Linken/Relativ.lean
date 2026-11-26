module

public import Core.Linken.DeckungsZustand

@[expose] public section

namespace Gabbro.Core.Linken

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Annahme
open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

/-- Relocation keeps the function name. -/
theorem funktionZurueck_name (off : Nat) (f : Funktion) : (funktionZurueck off f).name = f.name :=
  rfl

/-- Relocation keeps the function parameters. -/
theorem funktionZurueck_parameter (off : Nat) (f : Funktion) :
    (funktionZurueck off f).parameter = f.parameter :=
  rfl

/-- Relocation keeps the function result. -/
theorem funktionZurueck_result (off : Nat) (f : Funktion) :
    (funktionZurueck off f).result = f.result :=
  rfl

/-- Relocation keeps the descent flag. -/
theorem funktionZurueck_misstAbstieg (off : Nat) (f : Funktion) :
    (funktionZurueck off f).misstAbstieg = f.misstAbstieg :=
  rfl

/-- Relocation keeps the outgoing calls. -/
theorem funktionZurueck_ruft (off : Nat) (f : Funktion) : (funktionZurueck off f).ruft = f.ruft :=
  rfl

/-- Relocation keeps the effect contract. -/
theorem funktionZurueck_effects (off : Nat) (f : Funktion) :
    (funktionZurueck off f).effects = f.effects :=
  rfl

/-- Relocation keeps the continuation function. -/
theorem fortsetzungZurueck_funktion (off : Nat) (k : Fortsetzung) :
    (fortsetzungZurueck off k).funktion = k.funktion :=
  rfl

/-- Relocation keeps the current function. -/
theorem funktionAktuell_proj (off : Nat) (r : Rahmen) :
    (frameZurueck off r).funktion = r.funktion :=
  rfl

/-- Relocation keeps the globals. -/
theorem globale_proj (off : Nat) (r : Rahmen) : (frameZurueck off r).globale = r.globale :=
  rfl

/-- Relocation keeps the arrival regions. -/
theorem arrivalRegions_proj (off : Nat) (r : Rahmen) :
    (frameZurueck off r).arrivalRegions = r.arrivalRegions :=
  rfl

/-- Relocation keeps the platform. -/
theorem platform_proj (off : Nat) (r : Rahmen) : (frameZurueck off r).platform = r.platform :=
  rfl

/-- Relocation keeps the environment choices. -/
theorem environment_proj (off : Nat) (r : Rahmen) :
    (frameZurueck off r).environment = r.environment :=
  rfl

/-- The relocated frame's functions are the relocated table. -/
theorem funktionen_proj (off : Nat) (r : Rahmen) :
    (frameZurueck off r).funktionen = r.funktionen.map (funktionZurueck off) :=
  rfl

/-- Lookup in the relocated table tracks lookup in the original one up to relocation. -/
theorem finde_abbild (off : Nat) (l : List Funktion) (name : Identifier) :
    Funktion.finde (l.map (funktionZurueck off)) name =
      (Funktion.finde l name).map (funktionZurueck off) := by
  simp only [Funktion.finde, List.find?_map]
  have h : (fun f => f.name.val == name.val) ∘ funktionZurueck off =
      (fun f => f.name.val == name.val) := by
    funext f
    simp only [Function.comp_apply]
    rw [funktionZurueck_name]
  rw [h]

/-- The relocated frame's continuations are the relocated stack. -/
theorem fortsetzungen_proj (off : Nat) (r : Rahmen) :
    (frameZurueck off r).fortsetzungen = r.fortsetzungen.map (fortsetzungZurueck off) :=
  rfl

/-- The effect hull reads only names, calls and contracts, so it survives the address shift. -/
theorem effectHull_map (off : Nat) (l : List Funktion) (fuel : Nat) (visited : List (List Char))
    (names : List Identifier) :
    Funktion.effectHull (l.map (funktionZurueck off)) fuel visited names =
      Funktion.effectHull l fuel visited names := by
  induction fuel generalizing visited names with
  | zero => rfl
  | succ fuel ih =>
    cases names with
    | nil => rfl
    |     cons name pending =>
      have hf : ∀ name, Funktion.finde (l.map (funktionZurueck off)) name =
          (Funktion.finde l name).map (funktionZurueck off) :=
        fun name => finde_abbild _ _ _
      simp only [Funktion.effectHull, hf]
      by_cases hc : visited.contains name.val = true
      · simp only [if_pos hc]
        exact ih _ _
      · simp only [if_neg hc]
        cases h : Funktion.finde l name with
        | none =>
          simp only [h, Option.map]
          exact ih _ _
        | some target =>
          simp only [h, Option.map]
          have heff : (funktionZurueck off target).effects = target.effects :=
            funktionZurueck_effects _ _
          have hruft : (funktionZurueck off target).ruft = target.ruft :=
            funktionZurueck_ruft _ _
          simp only [heff, hruft]
          cases he : target.effects with
          | none => exact ih _ _
          | some effects => rw [ih]

/-- The folding bound survives the address shift: only arities are counted. -/
theorem foldlBound_map (off : Nat) (l : List Funktion) :
    (l.map (funktionZurueck off)).foldl (fun n f => n + f.ruft.length) 1 =
      l.foldl (fun n f => n + f.ruft.length) 1 := by
  have key : ∀ (b : Nat) (l : List Funktion),
      (l.map (funktionZurueck off)).foldl (fun n f => n + f.ruft.length) b =
        l.foldl (fun n f => n + f.ruft.length) b := by
    intro b l
    induction l generalizing b with
    | nil => rfl
    | cons f rest ihrest =>
      simp only [List.map_cons, List.foldl_cons, funktionZurueck_ruft off f, ihrest]
  exact key _ _

/-- The required effects over the relocated table agree with the original ones. -/
theorem requiredEffects_map (off : Nat) (l : List Funktion) (t : Funktion) :
    Funktion.requiredEffects (l.map (funktionZurueck off)) t =
      Funktion.requiredEffects l t := by
  simp only [Funktion.requiredEffects]
  cases he : t.effects with
  | some effects => simp only [he]
  | none =>
    simp only [he]
    rw [foldlBound_map]
    exact effectHull_map _ _ _ _ _

/-- Required effects read only effects, calls and names, so relocating the argument agrees. -/
theorem requiredEffects_arg_map (off : Nat) (l : List Funktion) (t : Funktion) :
    Funktion.requiredEffects l (funktionZurueck off t) =
      Funktion.requiredEffects l t := by
  simp only [Funktion.requiredEffects, funktionZurueck_effects off t,
    funktionZurueck_name off t]

/-- A call fits the relocated table exactly when it fits the original one. -/
theorem passt_map (off : Nat) (l : List Funktion) (call : Rufstelle) :
    call.passt (l.map (funktionZurueck off)) = call.passt l := by
  have hf : ∀ name, Funktion.finde (l.map (funktionZurueck off)) name =
      (Funktion.finde l name).map (funktionZurueck off) :=
    fun name => finde_abbild _ _ _
  simp only [Rufstelle.passt, hf]
  cases h : Funktion.finde l call.name with
  | none => simp only [h, Option.map]
  | some target =>
    simp only [h, Option.map, funktionZurueck_parameter off target,
      funktionZurueck_result off target, requiredEffects_map, requiredEffects_arg_map]

/-- Reachability reads only names and calls, so it survives the address shift. -/
theorem erreichbar_map (off : Nat) (l : List Funktion) (fuel : Nat) (ziel name : Identifier) :
    Funktion.erreichbar (l.map (funktionZurueck off)) ziel fuel name =
      Funktion.erreichbar l ziel fuel name := by
  induction fuel generalizing name with
  | zero => rfl
  | succ fuel ih =>
    have hf : ∀ name, Funktion.finde (l.map (funktionZurueck off)) name =
        (Funktion.finde l name).map (funktionZurueck off) :=
      fun name => finde_abbild _ _ _
    simp only [Funktion.erreichbar, hf]
    cases h : Funktion.finde l name with
    | none => simp only [h, Option.map]
    | some target =>
      simp only [h, Option.map]
      have hruft : (funktionZurueck off target).ruft = target.ruft :=
        funktionZurueck_ruft _ _
      rw [hruft]
      have hrest : ∀ calls : List Rufstelle,
          calls.any (fun call => Funktion.erreichbar (l.map (funktionZurueck off)) ziel fuel call.name) =
          calls.any (fun call => Funktion.erreichbar l ziel fuel call.name) := by
        intro calls
        induction calls with
        | nil => rfl
        | cons call rest ihrest =>
          simp only [List.any_cons, ih, ihrest]
      rw [hrest]

/-- The recursion check survives the address shift. -/
theorem rekursiv_map (off : Nat) (l : List Funktion) (f : Funktion) :
    Funktion.rekursiv (l.map (funktionZurueck off)) (funktionZurueck off f) =
      Funktion.rekursiv l f := by
  have hlen : (l.map (funktionZurueck off)).length = l.length := by
    simp only [List.length_map]
  simp only [Funktion.rekursiv, funktionZurueck_ruft off f, funktionZurueck_name off f, hlen]
  have key : ∀ calls : List Rufstelle,
      calls.any
          (fun call => Funktion.erreichbar (l.map (funktionZurueck off)) f.name l.length call.name) =
        calls.any (fun call => Funktion.erreichbar l f.name l.length call.name) := by
    intro calls
    induction calls with
    | nil => rfl
    | cons call rest ihrest =>
      simp only [List.any_cons, erreichbar_map, ihrest]
  exact key f.ruft

/-- The recursion search over a fixed table tracks the original search up to relocation. -/
theorem findRekursiv_map (off : Nat) (T l : List Funktion) :
    (l.map (funktionZurueck off)).find?
        (fun f => !f.misstAbstieg && Funktion.rekursiv (T.map (funktionZurueck off)) f) =
      ((l.find? (fun f => !f.misstAbstieg && Funktion.rekursiv T f)).map
        (funktionZurueck off)) := by
  induction l with
  | nil => rfl
  | cons f rest ihrest =>
    simp only [List.find?_cons, List.map_cons]
    rw [funktionZurueck_misstAbstieg, rekursiv_map]
    cases hc : (!f.misstAbstieg && Funktion.rekursiv T f) with
    | true => simp only [hc, Option.map]
    | false => simp only [hc, ihrest]

/-- The outgoing calls of the relocated table are the outgoing calls of the original one. -/
theorem flatMap_ruft_map (off : Nat) (l : List Funktion) :
    (l.map (funktionZurueck off)).flatMap Funktion.ruft = l.flatMap Funktion.ruft := by
  induction l with
  | nil => rfl
  | cons f rest ihrest =>
    simp only [List.map_cons, List.flatMap_cons, funktionZurueck_ruft off f, ihrest]

/-- The failing-call search survives the address shift. -/
theorem findPasst_map (off : Nat) (l : List Funktion) :
    ((l.map (funktionZurueck off)).flatMap Funktion.ruft).find?
        (fun call => !(call.passt (l.map (funktionZurueck off)))) =
      (l.flatMap Funktion.ruft).find? (fun call => !(call.passt l)) := by
  rw [flatMap_ruft_map]
  have key : ∀ calls : List Rufstelle,
      calls.find? (fun call => !(call.passt (l.map (funktionZurueck off)))) =
        calls.find? (fun call => !(call.passt l)) := by
    intro calls
    induction calls with
    | nil => rfl
    | cons call rest ihrest =>
      simp only [List.find?_cons, passt_map, ihrest]
  exact key _

/-- Defined names survive the address shift, so the duplicate check agrees. -/
theorem nodupNamen_map (off : Nat) (l : List Funktion) :
    ((l.map (funktionZurueck off)).map fun f => f.name.val).Nodup =
      (l.map fun f => f.name.val).Nodup := by
  have h : (l.map (funktionZurueck off)).map (fun f => f.name.val) =
      l.map (fun f => f.name.val) := by
    simp only [List.map_map, Function.comp_def, funktionZurueck_name]
  rw [h]

/-- The stack guard reads only continuation functions, so it survives relocation. -/
theorem stackAny_map (off : Nat) (fs : List Fortsetzung) (name : Identifier) :
    (fs.map (fortsetzungZurueck off)).any
        (fun k => (k.funktion.map Subtype.val) == some name.val) =
      fs.any (fun k => (k.funktion.map Subtype.val) == some name.val) := by
  induction fs with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.map_cons, List.any_cons, fortsetzungZurueck_funktion, ih]

/-- Reading an integer slot survives relocation: only temporaries are read. -/
theorem zahl_proj (off : Nat) (r : Rahmen) (slot : Nat) :
    (frameZurueck off r).zahl slot = r.zahl slot := by
  simp only [Rahmen.zahl, frameZurueck_temp]

/-- Reading a raw integer survives relocation. -/
theorem ganz_proj (off : Nat) (r : Rahmen) (slot : Nat) :
    (frameZurueck off r).ganz slot = r.ganz slot := by
  simp only [Rahmen.ganz, zahl_proj]

/-- Reading a temporary survives relocation. -/
theorem temp_proj (off : Nat) (r : Rahmen) (slot : Nat) :
    (frameZurueck off r).temp slot = r.temp slot := by
  rw [frameZurueck_temp]

/-- Call arguments are read from temporaries, so they survive relocation. -/
theorem rufArgumente_proj (off : Nat) (r : Rahmen) (slot : Nat)
    (sources targets : List (Ty .value)) :
    (frameZurueck off r).rufArgumente slot sources targets =
      r.rufArgumente slot sources targets := by
  induction sources generalizing slot targets with
  | nil =>
    cases targets with
    | nil => rfl
    | cons _ _ => rfl
  | cons source sources ih =>
    cases targets with
    | nil => rfl
    | cons target targets =>
      simp only [Rahmen.rufArgumente, temp_proj]
      rw [ih]

/-- Entry arguments read temporaries, locals and arrival regions, so they survive relocation. -/
theorem eintrittArgumente_proj (off : Nat) (r : Rahmen) (types : List (Ty .value)) :
    (frameZurueck off r).eintrittArgumente types =
      (r.eintrittArgumente types).map (frameZurueck off) := by
  simp only [Rahmen.eintrittArgumente]
  rw [arrivalRegions_proj]
  by_cases h1 : types = []
  · subst h1
    simp only [ite_true, Option.map, frameZurueck]
  · simp only [if_neg h1, Option.map_if]
    split
    all_goals simp only [Option.map, frameZurueck]

/-- Writing a temporary commutes with relocation. -/
theorem schreibe_proj (off : Nat) (r : Rahmen) (hpc : off ≤ r.pc) (ziel : Nat)
    (value : Option Dynamisch) :
    frameZurueck off (Rahmen.schreibe r ziel value) =
      Rahmen.schreibe (frameZurueck off r) ziel value := by
  have h : (r.pc + 1) - off = (r.pc - off) + 1 := by omega
  simp only [Rahmen.schreibe, frameZurueck, h]

/-- A plain step forward commutes with relocation. -/
theorem weiter_proj (off : Nat) (r : Rahmen) (hpc : off ≤ r.pc) :
    frameZurueck off { r with pc := r.pc + 1 } =
      { (frameZurueck off r) with pc := (frameZurueck off r).pc + 1 } := by
  have h : (r.pc + 1) - off = (r.pc - off) + 1 := by omega
  simp only [frameZurueck, frameZurueck_pc, h]

/-- Halting commutes with relocation: only the stop reason changes. -/
theorem halt_proj (off : Nat) (r : Rahmen) (reason : Abschluss) :
    frameZurueck off (r.halt reason) = (frameZurueck off r).halt reason := by
  simp only [Rahmen.halt, frameZurueck]

/-- A forward jump commutes with relocation. -/
theorem vorwaerts_proj (off : Nat) (r : Rahmen) (hpc : off ≤ r.pc) (d : Nat) :
    frameZurueck off { r with pc := r.pc + d } =
      { (frameZurueck off r) with pc := (frameZurueck off r).pc + d } := by
  have h : (r.pc + d) - off = (r.pc - off) + d := by omega
  simp only [frameZurueck, frameZurueck_pc, h]

/-- A backward jump commutes with relocation, unconditionally. -/
theorem rueckwaerts_proj (off : Nat) (r : Rahmen) (d : Nat) :
    frameZurueck off { r with pc := r.pc - d } =
      { (frameZurueck off r) with pc := (frameZurueck off r).pc - d } := by
  have h : (r.pc - d) - off = (r.pc - off) - d := by omega
  simp only [frameZurueck, frameZurueck_pc, h]

/-- Updating a counter at an absolute key commutes with relocation. -/
theorem zaehlerSetzen_proj (off : Nat) (r : Rahmen) (k : Nat) (h : off ≤ k) (v : Option Nat) :
    frameZurueck off { r with zaehler := Function.update r.zaehler k v } =
      { (frameZurueck off r) with
        zaehler := Function.update (frameZurueck off r).zaehler (k - off) v } := by
  unfold frameZurueck
  congr 1
  funext j
  simp only [karteZurueck]
  by_cases hj : j = k - off
  · subst hj
    have h1 : (k - off) + off = k := by omega
    simp only [Function.update_self, h1, Function.update_self]
  · have h2 : j + off ≠ k := by omega
    simp only [karteZurueck, Function.update_of_ne hj, Function.update_of_ne h2]

/-- Updating a bound at an absolute key commutes with relocation. -/
theorem obergrenzenSetzen_proj (off : Nat) (r : Rahmen) (k : Nat) (h : off ≤ k)
    (v : Option Ganzzahl) :
    frameZurueck off { r with obergrenzen := Function.update r.obergrenzen k v } =
      { (frameZurueck off r) with
        obergrenzen := Function.update (frameZurueck off r).obergrenzen (k - off) v } := by
  unfold frameZurueck
  congr 1
  funext j
  simp only [karteZurueck]
  by_cases hj : j = k - off
  · subst hj
    have h1 : (k - off) + off = k := by omega
    simp only [Function.update_self, h1, Function.update_self]
  · have h2 : j + off ≠ k := by omega
    simp only [karteZurueck, Function.update_of_ne hj, Function.update_of_ne h2]

end Gabbro.Core.Linken
