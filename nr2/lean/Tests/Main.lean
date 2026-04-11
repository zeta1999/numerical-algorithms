import Tests.TestExact
import Tests.TestFloat

def runSuite (name : String) (tests : List (String × Bool)) : IO (Nat × Nat) := do
  IO.println s!"--- {name} ---"
  let mut passed := 0
  let mut total := 0
  for (tname, result) in tests do
    total := total + 1
    if result then
      passed := passed + 1
      IO.println s!"  ✓ {tname}"
    else
      IO.println s!"  ✗ {tname} FAILED"
  IO.println s!"  {passed}/{total} passed"
  return (passed, total)

def main : IO Unit := do
  IO.println "=== QR Decomposition Test Suite ==="
  IO.println ""

  let (ep, et) ← runSuite "Exact Arithmetic Tests (ℚ)" [
    ("identity_2x2", Tests.Exact.test_identity_2x2),
    ("simple_2x2", Tests.Exact.test_simple_2x2),
    ("solve_2x2", Tests.Exact.test_solve_2x2),
    ("solve_3x3", Tests.Exact.test_solve_3x3),
    ("singular", Tests.Exact.test_singular)
  ]

  IO.println ""

  let (fp, ft) ← runSuite "Floating-Point Tests" [
    ("identity", Tests.FloatTests.test_identity),
    ("2x2", Tests.FloatTests.test_2x2),
    ("solve_2x2", Tests.FloatTests.test_solve_2x2),
    ("3x3", Tests.FloatTests.test_3x3),
    ("hilbert_3x3", Tests.FloatTests.test_hilbert_3x3),
    ("4x4", Tests.FloatTests.test_4x4),
    ("singular", Tests.FloatTests.test_singular),
    ("determinant", Tests.FloatTests.test_determinant),
    ("cond_identity", Tests.FloatTests.test_cond_identity)
  ]

  IO.println ""
  let totalPassed := ep + fp
  let totalTests := et + ft
  IO.println s!"=== Total: {totalPassed}/{totalTests} passed ==="

  if totalPassed < totalTests then
    IO.Process.exit 1
  else
    IO.println "ALL TESTS PASSED"
