import Lean
namespace LspCli.ProjectProcess
/-- Remove Lake's build-package environment before invoking the target project's toolchain. -/
def environment : Array (String × Option String) :=
  #["ELAN_TOOLCHAIN", "LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LEAN", "LEAN_AR", "LEAN_GITHASH", "LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP", "LAKE_CACHE_DIR", "LD_LIBRARY_PATH"].map (·, none)

/-- An inherited Lake PATH may start with the CLI's compiler bin directory. Prefer the
    installed elan shim, which selects lean-toolchain from the child working directory. -/
def lake : IO String := do
  -- Preserve an explicitly supplied executable (including native test fixtures), while
  -- bypassing a toolchain bin directory injected by `lake env`.
  let mut selected := "lake"
  for dir in ((← IO.getEnv "PATH").getD "").splitOn ":" do
    let candidate := System.FilePath.mk dir / "lake"
    if ← candidate.pathExists then
      selected := candidate.toString
      break
  if !(selected.splitOn "/toolchains/").length > 1 then return selected
  let home ← IO.getEnv "ELAN_HOME"
  let home := home.getD (((← IO.getEnv "HOME").getD "/nonexistent") ++ "/.elan")
  let shim := System.FilePath.mk home / "bin" / "lake"
  if ← shim.pathExists then return shim.toString
  return "lake"
end LspCli.ProjectProcess
