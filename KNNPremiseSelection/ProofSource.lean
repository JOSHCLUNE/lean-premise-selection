import Lean
import KNNPremiseSelection.StatementFeatures

open Lean System

namespace String

/-- Check if a string is contained in another one. -/
partial def isSubstrOf (target str : String) : Bool :=
  loop "" 0
where
  loop (acc : String) (pos : String.Pos) : Bool :=
    if pos.byteIdx + target.endPos.byteIdx > str.endPos.byteIdx then
      false
    else if str.substrEq pos target 0 target.endPos.byteIdx then
      true
    else
      loop acc (str.next pos)

end String

/-- Find file path from module imported from Mathlib. -/
def pathFromMathlibImport (mod : Name) : MetaM (Option FilePath) := do
  let mathlibPath : System.FilePath := "." / "lake-packages" / "mathlib"
  SearchPath.findModuleWithExt [mathlibPath] "lean" mod

/-- Find file path of JSON with proof sources. -/
def proofSourcePath (mod : Name) : MetaM (Option FilePath) := do
  let mathlibPath : System.FilePath := "." / "data" / "proof_sources" / "mathlib"
  SearchPath.findModuleWithExt [mathlibPath] "json" mod

/-- Given a theorem name and a file path, extract the proof text. -/
def proofSource (thm : Name) (json : Json) : MetaM (Option String) := do
  if let Name.str _ thmStr := thm then
    match json.getObjVal? thmStr  with
    | Except.ok (Json.str s) => return some s
    | _ => return none
  return none

namespace KNNPremiseSelection

/-- Given a list of premises and proof text, get rid of the ones that do not
appear. We take into account `ToAdditive` name translations. -/
def filterUserPremises (premises : Multiset Name) (proofSource : String)
  : Multiset Name := Id.run <| do
  let appearsInProof (s : String) : Bool := s.isSubstrOf proofSource
  let mut result := Batteries.RBMap.empty
  for (p, c) in premises do
    let pLast := (Syntax.splitNameLit p.toString.toSubstring).reverse.head!.toString
    if appearsInProof pLast then
      result := result.insert p c
  return result

/-- Like `filterUserPremises` but simply checks that the premise appears
somewhere in the file, instead of looking for the proof source. -/
def filterUserPremisesFromFile
  (premises : Multiset Name) (referencePath : FilePath)
  : IO (Multiset Name) := do
  let appearsInFile (s : String) : IO Bool := do
    let args := #[s, referencePath.toString]
    let output ← IO.Process.output { cmd := "grep", args := args }
    if output.exitCode != 0 then
      return false
    if output.stdout.isEmpty then
      return false
    return true
  let mut result := Batteries.RBMap.empty
  for (p, c) in premises do
    if ← appearsInFile p.toString then
      result := result.insert p c
  return result

end KNNPremiseSelection
