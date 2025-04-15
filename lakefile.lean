import Lake
open Lake DSL

package leanPremiseSelection

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.18.0"

require «premise-selection» from git "https://github.com/hanwenzhu/premise-selection" @ "v4.18.0"

@[default_target]
lean_lib KNNPremiseSelection

@[default_target]
lean_lib Tests

@[default_target]
lean_exe Train where
  root := `Scripts.Train

@[default_target]
lean_exe Predict where
  root := `Scripts.Predict

@[default_target]
lean_exe KnnPredict where
  root := `Scripts.KnnPredict

-- def npmCmd : String := "npm"

-- target packageLock : FilePath := do
--   let widgetDir := __dir__ / "widget"
--   let packageFile ← inputFile <| widgetDir / "package.json"
--   let packageLockFile := widgetDir / "package-lock.json"
--   buildFileAfterDep packageLockFile packageFile fun _srcFile => do
--     proc {
--       cmd := npmCmd
--       args := #["install"]
--       cwd := some widgetDir
--     }

-- def tsxTarget (pkg : Package) (tsxName : String)
--     : IndexBuildM (BuildJob FilePath) := do
--   let widgetDir := __dir__ / "widget"
--   let jsFile := widgetDir / "dist" / s!"{tsxName}.js"
--   let deps : Array (BuildJob FilePath) := #[
--     ← inputFile <| widgetDir / "src" / s!"{tsxName}.tsx",
--     ← inputFile <| widgetDir / "rollup.config.js",
--     ← inputFile <| widgetDir / "tsconfig.json",
--     ← fetch (pkg.target ``packageLock)
--   ]
--   buildFileAfterDepArray jsFile deps fun _srcFile => do
--     proc {
--       cmd := npmCmd
--       args := #["run", "build", "--", "--tsxName", tsxName]
--       cwd := some widgetDir
--     }

-- @[default_target]
-- target widgetJs (pkg : Package) : FilePath := tsxTarget pkg "index"
