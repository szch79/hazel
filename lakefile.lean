import Lake

open Lake DSL

package hazel where
  version := v!"0.1.0"

@[default_target]
lean_lib Hazel

lean_lib HazelTest where
  globs := #[.submodules `HazelTest]
