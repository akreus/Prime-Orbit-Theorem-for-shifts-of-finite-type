import Mathlib.Dynamics.SymbolicDynamics.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.LinearAlgebra.Matrix.Trace

variable {k : ℕ}

abbrev TransitionMatrix (k : ℕ) := Matrix (Fin k) (Fin k) Bool
abbrev FullShift (k : ℕ) := ℤ -> Fin k

def Shift (x : FullShift k) : FullShift k := fun n => x (n + 1)
def ShiftOfFiniteType (A : TransitionMatrix k) : Set (FullShift k) :=
  {x | ∀ n : ℤ, A (x n) (x (n + 1)) = true}
