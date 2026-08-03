import Mathlib.Dynamics.SymbolicDynamics.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-
Might not even need SymbolicDynamics.Basic as we define SoFT to a higher
level of specificity (generality and lemmas in Mathlib not necessary)
 -/

open Function Matrix

variable {k : ℕ}

/- Defns for two-sided shift spaces -/
abbrev TransitionMatrix (k : ℕ) := Matrix (Fin k) (Fin k) Bool

/- So we can use it for Trace and Det -/
def TransitionMatrix.toRealMatrix (A : TransitionMatrix k) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => if A i j then 1 else 0

/- Set of all sequences -/
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

/- Useful defns in Dynamics.PeriodicPts -/
#check periodicOrbit /- σ → x → Cycle (FullShift k) -/
#check isPeriodicPt_iff_minimalPeriod_dvd /- minimalperiod | period -/
#check periodicPts /- Set of all periodic points -/
#check ptsOfPeriod /- Set of periodic pts given a period (minimal or not) -/

/- Fix_n -/
def Fix (n : ℕ) : Set (FullShift k) := SoFT A ∩ ptsOfPeriod σ n

/- x lies in prime orbit of period n -/
def IsPrimeOrbitOf (n : ℕ) (x : FullShift k) : Prop := minimalPeriod σ x = n

/- Set of all prime orbits in SoFT. To be used for indexing sums later -/
noncomputable
def primeOrbits : Set (Cycle (FullShift k)) :=
  (fun x => periodicOrbit σ x) '' (SoFT A  ∩ periodicPts σ)

/- Periodic orbit as a pair (x, n) with proofs -/
structure PeriodicOrbit where
  x : FullShift k
  n : ℕ
  hn : n > 0 -- if n=0 then IsPeriodicPt σ 0 x means x isn't periodic
  mem : x ∈ SoFT A
  periodic : IsPeriodicPt σ n x

def period (τ : PeriodicOrbit A) := τ.n
notation "λ" => period

noncomputable
def primePeriod (τ : PeriodicOrbit A) := minimalPeriod σ τ.x
notation "Λ" => primePeriod

/- orbit is prime if minimal period equals period -/
def PeriodicOrbit.IsPrime (τ : PeriodicOrbit A) : Prop :=
  period _ τ = primePeriod _ τ

/- def as in lem 3.2 then prove other defns backwards -/
noncomputable
def zeta (z : ℂ) : ℂ :=
  (det (1 - z • A.toRealMatrix.map ((↑) : ℝ → ℂ)))⁻¹

/- product definition as in def 3.1 -/
noncomputable
def zetaProd (z : ℂ) : ℂ :=
  ∏' τ : primeOrbits A, (1 - z ^ (τ : Cycle (FullShift k)).length)⁻¹

/- τ PeriodicOrbit, then τ.x has a primeOrbit-/
theorem periodicOrbits_mem_primeOrbits (τ : PeriodicOrbit A) :
    periodicOrbit σ τ.x ∈ primeOrbits A :=
  Set.mem_image_of_mem _ ⟨τ.mem, τ.n, τ.hn, τ.periodic⟩
/- e.g. (1,2,1,2,1,2) PeriodicOrbit with (1,2) ∈ primeOrbits-/

/- IsPrime then length of primeOrbit = τ.n -/
theorem periodicOrbit_length_eq_period {τ : PeriodicOrbit A} (hτ : τ.IsPrime) :
    (periodicOrbit σ τ.x).length = τ.n := by
  simp [PeriodicOrbit.IsPrime, period, primePeriod] at hτ
  simp [hτ]

/- power series of log(1-z) in ℂ -/
#check Complex.hasSum_taylorSeries_neg_log

/- may or may not need but its in : Mathlib.Analysis.SpecialFunctions.Log.Summable
#check Complex.hasProd_of_hasSum_log -/

/- lem 3.1 (Σz^n/n#Fixn = S => zetaprod z = S)) -/
theorem hasProd_zeta_of_hasSum (z : ℂ) (S : ℂ)
    (hS : HasSum (fun n : ℕ => z ^ n / n * (Nat.card (Fix A n) : ℂ)) S) :
    HasProd (fun τ : primeOrbits A => (1 - z ^ (τ : Cycle (FullShift k)).length)⁻¹)
    (Complex.exp S) := by
  sorry
