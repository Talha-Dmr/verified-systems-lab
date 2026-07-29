import VerifiedCompiler

open VerifiedCompiler

def sample : Expr :=
  .sub
    (.mul
      (.add (.lit 2) (.lit 3))
      (.lit 4))
    (.lit 7)

def main : IO Unit := do
  IO.println s!"Source expression: {reprStr sample}"
  IO.println s!"Interpreter result: {sample.eval}"
  IO.println s!"Compiled code: {reprStr (Compiler.compile sample)}"
  IO.println s!"Machine result: {reprStr (Machine.run (Compiler.compile sample) [])}"
