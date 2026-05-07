import Lake
open Lake DSL

package «defeater» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «Defeater» where
  srcDir := "."

lean_exe «smoke» where
  root := `Smoke
