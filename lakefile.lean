import Lake

open Lake DSL

package hazel where
  version := v!"0.1.0"
  testDriver := "hazelTest"

@[default_target]
lean_lib Hazel

lean_lib HazelTest where
  globs := #[
    .one `HazelTest.Do, .one `HazelTest.DocString, .one `HazelTest.Header,
    .one `HazelTest.Meta, .one `HazelTest.Pedantic, .one `HazelTest.Sampling,
    .one `HazelTest.Style, .one `HazelTest.Tactic
  ]

lean_lib HazelTestFixtures where
  globs := #[
    .submodules `HazelTest.ImportOrder,
    .submodules `HazelTest.ModuleDoc
  ]

lean_exe hazelTest where
  root := `HazelTest.Driver
  supportInterpreter := true
