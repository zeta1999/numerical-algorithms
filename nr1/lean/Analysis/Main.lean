import Analysis.SensitivityUtils

/-!
# Sensitivity Analysis Driver
-/

open Fuzz Analysis in
def main : IO Unit := do
  IO.println "=== Numerical Sensitivity Analysis ==="
  IO.println "n,target_kappa,mean_actual_kappa,mean_forward_err,max_forward_err,mean_backward_err,max_backward_err"

  let mut state := initPrng 12345

  let sizes := #[5, 10, 20, 50]
  let kappas := #[1.0, 1e2, 1e4, 1e6, 1e8, 1e10, 1e12]
  let numTrials := 20

  for n in sizes do
    for targetKappa in kappas do
      let mut sumKappa := 0.0
      let mut sumFwd := 0.0
      let mut maxFwd := 0.0
      let mut sumBwd := 0.0
      let mut maxBwd := 0.0
      let mut validTrials := 0

      for _ in [:numTrials] do
        let (result, state') := runTrial state n targetKappa
        state := state'

        if result.forwardErr < (1.0 / 0.0 : Float) then
          validTrials := validTrials + 1
          sumKappa := sumKappa + result.actualKappa
          sumFwd := sumFwd + result.forwardErr
          if result.forwardErr > maxFwd then
            maxFwd := result.forwardErr
          sumBwd := sumBwd + result.backwardErr
          if result.backwardErr > maxBwd then
            maxBwd := result.backwardErr

      if validTrials > 0 then
        let vf := Float.ofNat validTrials
        IO.println s!"{n},{targetKappa},{sumKappa/vf},{sumFwd/vf},{maxFwd},{sumBwd/vf},{maxBwd}"
      else
        IO.println s!"{n},{targetKappa},inf,inf,inf,inf,inf"

  IO.println ""
  IO.println "=== Analysis Notes ==="
  IO.println "Theoretical bound: forward_error <= kappa(A) * machine_epsilon"
  IO.println "Machine epsilon (Float64): 2.22e-16"
  IO.println "With partial pivoting, growth factor is typically O(1) in practice."
