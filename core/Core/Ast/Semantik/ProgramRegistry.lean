module

public import Core.Ast.Semantik.ProgramForms
public import Core.Ast.Semantik.ProgramObligations
public import Core.Ast.Semantik.Formen
public import Core.Ast.ProgramRegistry.BoundedWhile
public import Core.Ast.ProgramRegistry.ForRange
public import Core.Ast.ProgramRegistry.Constant
public import Core.Ast.ProgramRegistry.Function
public import Core.Ast.ProgramRegistry.Unit

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Waechter

def returnVoidEntry : RegistryEntry ``Stmt.retVoid (stmtSchema ``Stmt.retVoid) := by
  rw [stmtSchema,
    if_neg (differentLabels (a := "retVoid") (b := "letValue") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "retVoid") (b := "assignVar") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "retVoid") (b := "ret") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "retVoid") (b := "ite") (by intro same; simp only [String.reduceEq] at same)),
    if_pos rfl]
  exact returnVoidProofs

def mutableLocalEntry : RegistryEntry ``Stmt.letMutable (stmtSchema ``Stmt.letMutable) := by
  rw [stmtSchema,
    if_neg (differentLabels (a := "letMutable") (b := "letValue") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "letMutable") (b := "assignVar") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "letMutable") (b := "ret") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "letMutable") (b := "ite") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "letMutable") (b := "retVoid") (by intro same; simp only [String.reduceEq] at same)),
    if_pos rfl]
  exact mutableLocalProofs

def directCallEntry : RegistryEntry ``Stmt.directCall (stmtSchema ``Stmt.directCall) := by
  rw [stmtSchema,
    if_neg (differentLabels (a := "directCall") (b := "letValue") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "directCall") (b := "assignVar") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "directCall") (b := "ret") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "directCall") (b := "ite") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "directCall") (b := "retVoid") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "directCall") (b := "letMutable") (by intro same; simp only [String.reduceEq] at same)),
    if_pos rfl]
  exact directCallProofs

def bindDirectEntry : RegistryEntry ``Stmt.bindDirect (stmtSchema ``Stmt.bindDirect) := by
  rw [stmtSchema,
    if_neg (differentLabels (a := "bindDirect") (b := "letValue") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "bindDirect") (b := "assignVar") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "bindDirect") (b := "ret") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "bindDirect") (b := "ite") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "bindDirect") (b := "retVoid") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "bindDirect") (b := "letMutable") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "bindDirect") (b := "directCall") (by intro same; simp only [String.reduceEq] at same)),
    if_pos rfl]
  exact bindDirectProofs

end Gabbro.Core.Ast.Semantik
