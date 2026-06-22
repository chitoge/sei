-- Smoke test: validates the rules_lean4 + remote-execution toolchain.
theorem smoke (a b : Nat) : a + b = b + a := Nat.add_comm a b
