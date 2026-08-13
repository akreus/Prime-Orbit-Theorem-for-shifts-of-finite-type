import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Analytic.Basic

open Function Matrix Complex

variable {k : ℕ}

/- Defns for two-sided shift spaces -/
abbrev TransitionMatrix (k : ℕ) := Matrix (Fin k) (Fin k) Bool

/- So we can use it for Trace and Det -/
def TransitionMatrix.toRealMatrix (A : TransitionMatrix k) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => if A i j then 1 else 0

/- So we can use it for complex eigenvalues -/
def TransitionMatrix.toComplexMatrix (A : TransitionMatrix k) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => if A i j then 1 else 0

def TransitionMatrix.IsAperiodic (A : TransitionMatrix k) : Prop :=
  ∃ n : ℕ, ∀ i : Fin k, ∀ j : Fin k, ((A.toRealMatrix)^n) i j > 0

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

/- two points in same orbit are equivalent -/
def orbitRel : Setoid {x : FullShift k // x ∈ periodicPts σ} where
    r x y := ∃ k, σ^[k] x.1 = y.1
    iseqv := ⟨fun x => ⟨0, rfl⟩, by
  intro x y h
  obtain ⟨k, hk⟩ := h
  let n := minimalPeriod σ x.1
  let hn := minimalPeriod_pos_of_mem_periodicPts x.2
  let m := n * (k / n + 1)
  use n * (k / n + 1) - k
  rw [← hk, ← iterate_add_apply, Nat.sub_add_cancel]
  · exact isPeriodicPt_iff_minimalPeriod_dvd.mpr (Nat.dvd_mul_right n (k / n + 1))
  have h1 : n * (k / n) + k % n = k := Nat.div_add_mod k n
  have h2 : k % n < n := Nat.mod_lt k hn
  calc k = n * (k / n) + k % n := h1.symm
    _ ≤ n * (k / n) + n := by omega
    _ = n * (k / n + 1) := by ring
  , by
  intro x y z hxy hyz
  obtain ⟨i, hi⟩ := hxy
  obtain ⟨j ,hj⟩ := hyz
  use i + j
  rw [add_comm, iterate_add_apply, hi, hj]⟩

/- Periodic orbit in SoFT A as a pair (x, n) with proofs -/
structure PeriodicOrbit where
  x : Quotient orbitRel
  n : ℕ
  hn : n > 0 -- if n=0 then IsPeriodicPt σ 0 x means x isn't periodic
  mem : ∀ p ∈ x, p.1 ∈ SoFT A
  --periodic : IsPeriodicPt σ n x

noncomputable
def period (τ : PeriodicOrbit A) := τ.n * minimalPeriod σ τ.x
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

/- IsPrime then length of primeOrbit = λ τ -/
theorem periodicOrbit_length_eq_period {τ : PeriodicOrbit A} (hτ : τ.IsPrime) :
    (periodicOrbit σ τ.x).length = τ.n * minimalPeriod σ τ.x := by
  simp [PeriodicOrbit.IsPrime, period, primePeriod] at hτ
  simp [hτ]

/- power series of log(1-z) in ℂ -/
#check hasSum_taylorSeries_neg_log

/- RoC of ∑zⁿ/n·#Fixₙ less than 1 -/
lemma mod_lt_one_of_hasSum (z : ℂ) (S : ℂ)
    (hS : HasSum (fun n : ℕ => z ^ n / n * (Nat.card (Fix A n) : ℂ)) S) :
    ‖z‖ < 1 := by
  sorry

lemma period_div_primePeriod_ge_one (τ : PeriodicOrbit A) : 1 ≤ τ.n/(Λ A τ) := by
  sorry

/- bijection between τ' PeriodicOrbit and (τ,m) ∈ primeOrbit x ℕ≥1-/
noncomputable
def periodicOrbit_equiv_primeOrbit_ge_one :
    PeriodicOrbit A ≃ {(τ, m) : primeOrbits A × ℕ | 1 ≤ m} where
  toFun := fun τ' => ⟨(⟨periodicOrbit σ τ'.x, periodicOrbits_mem_primeOrbits A τ'⟩,
    τ'.n/(Λ A τ')), period_div_primePeriod_ge_one A τ'⟩
  invFun := fun ⟨(τ, m), hm⟩ =>
    let x :=
      ((Set.mem_image (fun x => periodicOrbit σ x) (SoFT A  ∩ periodicPts σ) τ).mp τ.2).choose
    let hx :=
      ((Set.mem_image (fun x => periodicOrbit σ x) (SoFT A  ∩ periodicPts σ) τ).mp τ.2).choose_spec.1
    {
      x := x
      n := m * minimalPeriod σ x
      hn := mul_pos hm (minimalPeriod_pos_of_mem_periodicPts hx.2)
      mem := hx.1
      periodic := isPeriodicPt_iff_minimalPeriod_dvd.mpr (dvd_mul_left (minimalPeriod σ x) m)
    }
  left_inv := sorry -- oversight: invFun chooses x, not necessarily the same x...
  right_inv := sorry

/- lem 3.1 (Σz^n/n#Fixn = S => zetaprod z = S)) -/
theorem hasProd_zeta_of_hasSum (z : ℂ) (S : ℂ)
    (hS : HasSum (fun n : ℕ => z ^ n / n * (Nat.card (Fix A n) : ℂ)) S) :
    HasProd (fun τ : primeOrbits A => (1 - z ^ (τ : Cycle (FullShift k)).length)⁻¹)
    (exp S) := by
  apply HasProd.congr_fun
    (f := fun τ : primeOrbits A => exp (-log (1 - z ^ (τ : Cycle (FullShift k)).length)))
  rotate_left
  · intro τ
    rw [exp_neg, exp_log]
    have hneτ : (τ : Cycle (FullShift k)).length ≠ 0 := by
      obtain ⟨x, ⟨_, hx_per⟩, hxeq⟩ := τ.2
      rw [← hxeq, periodicOrbit_length]
      exact (minimalPeriod_pos_of_mem_periodicPts hx_per).ne'
    rw [sub_ne_zero]
    intro heq
    have h1 : ‖z ^ (τ : Cycle (FullShift k)).length‖ = 1 := by rw [← heq]; norm_num
    rw [norm_pow] at h1
    have h2 : ‖z‖ ^ (τ : Cycle (FullShift k)).length < 1 :=
      pow_lt_one₀ (norm_nonneg z) (mod_lt_one_of_hasSum A z S hS) hneτ
    linarith
  sorry -- goal: HasProd (fun τ => exp (-log (1 - z^λ(τ)))) (exp S)

/- #Fixₙ = Tr(Aⁿ)
Rough proof:
  Prove bijection: x ∈ Fixₙ ↔ x₀,...,x_{n-1} s.t.
  A(x₀,x₁)=...=A(x_{n-2},x_{n-1})=A(x_{n-1},x₀)=1
  Then #Fixₙ=∑1 over x₀,...,x_{n-1} s.t. ...
  =∑ A(x₀,x₁)...A(x_{n-1},x₀) over all x₀,...,x_{n-1} ∈ Fin k
  =∑ Aⁿ(x₀,x₀) (inductively on n by defn of matrix mult)
  = Tr(Aⁿ)
-/

lemma fix_bijects_tuple (n : ℕ) [NeZero n] :
    Set.BijOn (fun x : FullShift k => (fun i : Fin n => x (i : ℤ))) (Fix A n)
      {v : Fin n → Fin k | ∀ i, A (v i) (v (i + 1)) = true} := by
  refine ⟨?_, ?_, ?_⟩
  · sorry
  · intro x hx y hy hxy
    sorry
  sorry

theorem card_fix_eq_trace (n : ℕ) :
    (Nat.card (Fix A n) : ℝ) = trace (A.toRealMatrix ^ n) := by
  sorry

/- lem3.2 (∑z^n/n#Fixn = 1/det(I-zA))-/
theorem zeta_eq_hasSum (z : ℂ) (S : ℂ)
    (hS : HasSum (fun n : ℕ => z ^ n / n * (Nat.card (Fix A n) : ℂ)) S) :
    zeta A z = exp S := by
  sorry

/- Cor: zeta = zetaProd for suff small z-/
theorem zeta_eq_zetaProd (z : ℂ) (S : ℂ)
    (hS : HasSum (fun n : ℕ => z ^ n / n * (Nat.card (Fix A n) : ℂ)) S) :
    zeta A z = zetaProd A z := by
  unfold zetaProd
  rw [(hasProd_zeta_of_hasSum A z S hS).tprod_eq]
  exact zeta_eq_hasSum A z S hS

/- use Perron-Frobenius as a black box result (not in Mathlib yet) -/
theorem exists_maximal_eigenval (hA : A.IsAperiodic) : -- have A nonneg for free
    ∃ β : ℝ, 0 < β ∧ Module.End.HasEigenvalue (A.toComplexMatrix.toLin') β ∧
      (∀ γ : ℂ, Module.End.HasEigenvalue (A.toComplexMatrix.toLin') γ → γ ≠ β → ‖γ‖ < β) := by
  sorry -- NEED TO ADD THE FACT THAT β IS A SIMPLE EIGENVALUE SOMEHOW

/- lem3.3 -/
theorem logDeriv_zeta_eq_sum_primeOrbits (z : ℂ) :
    deriv (zeta A) z / zeta A z =
      ∑' (τ : primeOrbits A), ∑' (m : ℕ),
        ((τ : Cycle (FullShift k)).length : ℂ) *
          z ^ ((m + 1) * (τ : Cycle (FullShift k)).length - 1) := by
  sorry

/- beta : maximal e-val of A -/
noncomputable
def beta (hA : A.IsAperiodic) : ℝ := (exists_maximal_eigenval A hA).choose

lemma beta_is_eigenval (hA : A.IsAperiodic) :
    Module.End.HasEigenvalue (A.toComplexMatrix.toLin') (beta A hA) :=
  (exists_maximal_eigenval A hA).choose_spec.2.1

lemma beta_is_maximal (hA : A.IsAperiodic) :
    ∀ γ : ℂ, Module.End.HasEigenvalue (A.toComplexMatrix.toLin') γ →
      γ ≠ (beta A hA) → ‖γ‖ < (beta A hA) :=
   (exists_maximal_eigenval A hA).choose_spec.2.2

/- α as in lem3.4 -/
noncomputable
def alpha (hA : A.IsAperiodic) (z : ℂ) : ℂ :=
  logDeriv (zeta A) z - (beta A hA)/(1 - z * beta A hA)

/- lem3.4 but for |z| < β⁻¹ -/
theorem alpha_analyticOnNhd (hA : A.IsAperiodic) :
    AnalyticOnNhd ℂ (alpha A hA) {z : ℂ | ‖z‖ < (beta A hA)⁻¹} := by
  sorry

-- NOW WE WILL START PROVING Prime Orbit Theorem USING ASYMPTOTICS

noncomputable
def psi (x : ℕ) : ℝ :=
  ∑' τ' : {τ' : PeriodicOrbit A // period A τ' ≤ x}, Λ A τ'
