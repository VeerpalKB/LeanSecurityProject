import Std
import backend.SecurityVerification

def main : IO Unit := do
  let result := verifyProperty "access_control"
  IO.println result.output

