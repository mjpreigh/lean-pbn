@[extern "add"]
opaque add : UInt32 → UInt32 → UInt32

def main : IO Unit := do
  IO.println (add 10 20)
