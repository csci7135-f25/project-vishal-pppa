import Lake
open Lake DSL

package LeanJavaScripty where
  -- add package configuration options here

@[default_target]
lean_lib LeanJavaScripty where
  -- add library configuration options here

lean_lib Tests where
  globs := #[.submodules `Tests]

lean_exe llmtest where
  root := `Main
