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
notation "σ" => shift

def ShiftOfFiniteType (A : TransitionMatrix k) : Set (FullShift k) :=
  {x | ∀ n : ℤ, A (x n) (x (n + 1)) = true}
notation "SoFT" => ShiftOfFiniteType

/- Shift invariance of a SoFT -/
theorem shift_mapsTo (A : TransitionMatrix k) :
    Set.MapsTo σ (SoFT A) (SoFT A) := by
  exact Set.mapsTo_iff_subset_preimage.mpr fun ⦃a⦄ a_1 n ↦ a_1 (n + 1)

variable (A : TransitionMatrix k)

open Function

/- Useful defns in Dynamics.PeriodicPts -/
#check periodicOrbit /- All prime orbits in the FullShift -/
#check isPeriodicPt_iff_minimalPeriod_dvd /- minimalperiod | period -/
#check periodicPts /- Set of all periodic points -/
#check ptsOfPeriod /- Set of periodic pts given a period (minimal or not) -/

/- Fix_n -/
def Fix (n : ℕ) : Set (FullShift k) := SoFT A ∩ ptsOfPeriod σ n

/- x lies in prime orbit of period n -/
def IsPrimeOrbitOf (n : ℕ) (x : FullShift k) : Prop := minimalPeriod σ x = n

/- Set of all prime orbits in SoFT. To be used for indexing sums later -/
noncomputable def primeOrbits : Set (Cycle (FullShift k)) :=
  (fun x => periodicOrbit σ x) '' (SoFT A  ∩ periodicPts σ)

def orbitPeriod (x : FullShift k) : ℕ := sorry
notation "λ" => orbitPeriod

def primeOrbitCount (n : ℕ) : ℕ := sorry
notation "π" => primeOrbitCount
