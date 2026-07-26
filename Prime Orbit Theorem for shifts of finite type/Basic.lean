import Mathlib.Dynamics.SymbolicDynamics.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.LinearAlgebra.Matrix.Trace

/-
Might not even need SymbolicDynamics.Basic as we define SoFT to a higher
level of specificity (generality and lemmas in Mathlib not necessary)
 -/

variable {k : ℕ}

/- Defns for two-sided shift spaces -/
abbrev TransitionMatrix (k : ℕ) := Matrix (Fin k) (Fin k) Bool
abbrev FullShift (k : ℕ) := ℤ -> Fin k

def shift (x : FullShift k) : FullShift k := fun n => x (n + 1)
def ShiftOfFiniteType (A : TransitionMatrix k) : Set (FullShift k) :=
  {x | ∀ n : ℤ, A (x n) (x (n + 1)) = true}

/- Shift invariance of a SoFT -/
theorem shift_mapsTo (A : TransitionMatrix k) :
    Set.MapsTo shift (ShiftOfFiniteType A) (ShiftOfFiniteType A) := by
  exact Set.mapsTo_iff_subset_preimage.mpr fun ⦃a⦄ a_1 n ↦ a_1 (n + 1)

variable (A : TransitionMatrix k)

open Function

/- Fix_n -/
def Fix (n : ℕ) : Set (FullShift k) := ShiftOfFiniteType A ∩ ptsOfPeriod shift n
#check periodicOrbit shift /- τ -/
#check isPeriodicPt_iff_minimalPeriod_dvd /- minimalperiod | period -/

/- x lies in prime orbit of period n -/
def IsPrimeOrbitOf (n : ℕ) (x : FullShift k) : Prop := minimalPeriod shift x = n
