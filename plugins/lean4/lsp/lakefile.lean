import Lake
open Lake DSL
package «lean4-skills-lsp»
lean_lib LspCli
@[default_target] lean_exe «lean4-skills-lsp» where
  root := `Main
lean_exe test where
  root := `Test
