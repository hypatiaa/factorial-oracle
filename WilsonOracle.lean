import Mathlib.NumberTheory.Wilson
import Mathlib.Data.Nat.Totient
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The exact Wilson gate and orbitvertices in Robin Miller's WilsonFactorial Oracle.
Here n is the factorial input n₁. The active detuning is n₇ = −1. -/
namespace WilsonOracle
noncomputable section

def candidate (n : ℕ) := n + 1
def activeShell (n : ℕ) := n.factorial + 1
def distanceToMultiple (M p : ℕ) := min (M % p) (p - M % p)

theorem distance_zero_iff {M p : ℕ} (hp : 0 < p) :
    distanceToMultiple M p = 0 ↔ p ∣ M := by
  have hr := Nat.mod_lt M hp
  rw [Nat.dvd_iff_mod_eq_zero]
  unfold distanceToMultiple
  omega

theorem active_gate_iff_prime {n : ℕ} (hn : 1 ≤ n) :
    distanceToMultiple (activeShell n) (candidate n) = 0 ↔ (candidate n).Prime := by
  have hp : 0 < candidate n := Nat.succ_pos n
  have hp1 : candidate n ≠ 1 := by unfold candidate; omega
  rw [distance_zero_iff hp, ← ZMod.natCast_eq_zero_iff, Nat.prime_iff_fac_equiv_neg_one hp1]
  rw [show candidate n - 1 = n by unfold candidate; omega,
    activeShell, Nat.cast_add, Nat.cast_one, add_eq_zero_iff_eq_neg]

inductive Readout where
  | inactive | uncertified | miss | antipodal | polygon
  deriving DecidableEq, Repr

/-- The integral-input branch of TextWilson in the GGB file. -/
def readout (n : ℕ) (detuning : ℤ) : Readout :=
  if detuning ≠ -1 then .inactive
  else if ¬ (1 ≤ n ∧ n ≤ 18) then .uncertified
  else if distanceToMultiple (activeShell n) (candidate n) = 0 then
    if candidate n = 2 then .antipodal else .polygon
  else .miss

theorem polygon_iff (n : ℕ) (d : ℤ) :
    readout n d = .polygon ↔
      d = -1 ∧ 1 ≤ n ∧ n ≤ 18 ∧ (candidate n).Prime ∧ 3 ≤ candidate n := by
  by_cases hd : d = -1
  · by_cases hn : 1 ≤ n ∧ n ≤ 18
    · have hp : 2 ≤ candidate n := by unfold candidate; omega
      have he : 3 ≤ candidate n ↔ candidate n ≠ 2 := by omega
      simp only [readout, hd, ne_self_iff_false, hn, not_true_eq_false, ite_false,
        true_and, active_gate_iff_prime hn.1, he]
      by_cases hprime : (candidate n).Prime <;> by_cases htwo : candidate n = 2 <;>
        simp [htwo, hprime, Nat.prime_two]
    · simp [readout, hd, hn]; omega
  · simp [readout, hd]

theorem two_cycle_readout : readout 1 (-1) = .antipodal := by decide

/-- t_c is the exact integral quotient whenever the active gate passes. -/
def step (n : ℕ) := activeShell n / candidate n

theorem step_times_candidate {n : ℕ}
    (hg : distanceToMultiple (activeShell n) (candidate n) = 0) :
    step n * candidate n = activeShell n :=
  Nat.div_mul_cancel ((distance_zero_iff (Nat.succ_pos n)).mp hg)

/-- Literal exponential used for element j of the file's orbitvertices sequence. -/
def vertex (n : ℕ) (a : ℝ) (j : ℕ) : ℂ := a * Complex.exp
  (2 * (Real.pi : ℂ) * Complex.I * j * (step n : ℂ) / (activeShell n : ℂ))

def root (n : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (candidate n : ℂ))

theorem vertex_eq {n : ℕ} (hg : distanceToMultiple (activeShell n) (candidate n) = 0)
    (a : ℝ) (j : ℕ) : vertex n a j = a * root n ^ j := by
  have ht : (step n : ℂ) * (candidate n : ℂ) = (activeShell n : ℂ) := by
    exact_mod_cast step_times_candidate hg
  have hM : (activeShell n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  have hp : (candidate n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  unfold vertex root
  rw [← Complex.exp_nat_mul]
  congr 2
  field_simp
  linear_combination (j : ℂ) * ht

theorem vertex_returns_iff {n : ℕ} (hg : distanceToMultiple (activeShell n) (candidate n) = 0)
    {a : ℝ} (ha : a ≠ 0) (j : ℕ) :
    vertex n a j = vertex n a 0 ↔ candidate n ∣ j := by
  have hprim : IsPrimitiveRoot (root n) (candidate n) :=
    Complex.isPrimitiveRoot_exp _ (Nat.succ_ne_zero n)
  rw [vertex_eq hg, vertex_eq hg, pow_zero, mul_right_inj' (Complex.ofReal_ne_zero.mpr ha)]
  exact hprim.pow_eq_one_iff_dvd j

theorem distinct_vertices {n : ℕ} (hg : distanceToMultiple (activeShell n) (candidate n) = 0)
    {a : ℝ} (ha : a ≠ 0) {i j : ℕ} (hi : i < candidate n) (hj : j < candidate n) :
    vertex n a i = vertex n a j → i = j := by
  rw [vertex_eq hg, vertex_eq hg, mul_right_inj' (Complex.ofReal_ne_zero.mpr ha)]
  exact (Complex.isPrimitiveRoot_exp _ (Nat.succ_ne_zero n)).pow_inj hi hj

theorem zero_radius (n j : ℕ) : vertex n 0 j = 0 := by simp [vertex]

theorem antipodal_vertices (a : ℝ) :
    vertex 1 a 0 = (a : ℂ) ∧ vertex 1 a 1 = -(a : ℂ) := by
  have hg : distanceToMultiple (activeShell 1) (candidate 1) = 0 := by decide
  have hr : root 1 = -1 := by
    unfold root
    convert Complex.exp_pi_mul_I using 1
    congr 1
    norm_num [candidate]
    ring
  simp [vertex_eq hg, hr]

theorem plotted_polygon {n : ℕ} {d : ℤ} (h : readout n d = .polygon)
    {a : ℝ} (ha : a ≠ 0) :
    (candidate n).Prime ∧
    (∀ j : ℕ, vertex n a j = vertex n a 0 ↔ candidate n ∣ j) ∧
    Function.Injective (fun j : Fin (candidate n) => vertex n a j.val) := by
  obtain ⟨_, hn, _, hp, _⟩ := (polygon_iff n d).mp h
  have hg := (active_gate_iff_prime hn).mpr hp
  exact ⟨hp, vertex_returns_iff hg ha,
    fun i j hij => Fin.ext (distinct_vertices hg ha i.isLt j.isLt hij)⟩

/-- The older viewer compares its totient condition to factorial-shell residency. -/
theorem spectral_agreement {n : ℕ} (hn : 1 ≤ n) :
    (candidate n).totient = candidate n - 1 ↔
      distanceToMultiple (activeShell n) (candidate n) = 0 := by
  exact (Nat.totient_eq_iff_prime (p := candidate n) (Nat.succ_pos n)).trans
    (active_gate_iff_prime hn).symm

/-- The independent candidate card accepts p directly and does not use the GGB cap. -/
theorem independent_candidate {p : ℕ} (hp : 2 ≤ p) :
    p.Prime ↔ p ∣ (p-1).factorial + 1 := by
  have hn : 1 ≤ p-1 := by omega
  have he : candidate (p-1) = p := by unfold candidate; omega
  have h := (active_gate_iff_prime hn).symm
  rwa [he, distance_zero_iff (by omega : 0 < p)] at h

/-- The actual natural-number defect on the eligible successor shell. -/
theorem gearbox_zero_iff_resident {n : ℕ} (hn : 1 ≤ n) :
    candidate n - 1 - (candidate n).totient = 0 ↔ candidate n ∣ activeShell n := by
  have hp : 1 < candidate n := by unfold candidate; omega
  have hlt := Nat.totient_lt _ hp
  rw [← distance_zero_iff (p := candidate n) (Nat.succ_pos n), ← spectral_agreement hn]
  omega

/-- Original Steps trace on the outer rim, after removing the integer carrier. -/
def selectedPhase (n : ℕ) (k : ℤ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * k / (activeShell n : ℂ))

theorem trace_at_spin_two (n : ℕ) (t₁ k : ℤ) (a : ℝ) :
    (a : ℂ) * Complex.exp ((((activeShell n : ℂ) * t₁ + k) * 2 * Real.pi * Complex.I)
        / (activeShell n : ℂ)) = a * selectedPhase n k := by
  have hM : (activeShell n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  have he : (((activeShell n : ℂ) * t₁ + k) * 2 * Real.pi * Complex.I)
        / (activeShell n : ℂ) = t₁ * (2 * Real.pi * Complex.I) +
          2 * (Real.pi : ℂ) * Complex.I * k / (activeShell n : ℂ) := by
    field_simp
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, selectedPhase]

theorem trace_recovers_vertices (n j : ℕ) (a : ℝ) :
    (a : ℂ) * selectedPhase n ((j : ℤ) * (step n : ℤ)) = vertex n a j := by
  unfold selectedPhase vertex
  push_cast
  rw [← mul_assoc]

theorem prime_iff_integer_steps {n : ℕ} (hn : 1 ≤ n) :
    (candidate n).Prime ↔ ∃ k : ℤ, IsPrimitiveRoot (selectedPhase n k) (candidate n) := by
  rw [← active_gate_iff_prime hn]
  constructor
  · intro hg
    refine ⟨(step n : ℤ), ?_⟩
    have h := (trace_recovers_vertices n 1 1).trans (vertex_eq hg 1 1)
    simp only [Int.natCast_one, one_mul, Complex.ofReal_one, pow_one] at h
    rw [h]
    exact Complex.isPrimitiveRoot_exp _ (Nat.succ_ne_zero n)
  · rintro ⟨k, hk⟩
    apply (distance_zero_iff (Nat.succ_pos n)).mpr
    apply hk.dvd_of_pow_eq_one
    unfold selectedPhase
    rw [← Complex.exp_nat_mul]
    have hM : (activeShell n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
    convert Complex.exp_int_mul_two_pi_mul_I k using 1
    congr 1
    field_simp

theorem canonical_heptagon :
    readout 6 (-1) = .polygon ∧ activeShell 6 = 721 ∧ step 6 = 103 := by decide

theorem composite_four :
    candidate 3 = 4 ∧ activeShell 3 = 7 ∧ distanceToMultiple 7 4 = 1 ∧
    readout 3 (-1) = .miss := by decide

theorem saved_and_active :
    readout 4 0 = .inactive ∧ readout 4 (-1) = .polygon ∧
    activeShell 4 = 25 ∧ candidate 4 = 5 ∧ step 4 = 5 := by decide

#print axioms active_gate_iff_prime
#print axioms polygon_iff
#print axioms vertex_returns_iff
#print axioms distinct_vertices
#print axioms plotted_polygon
#print axioms antipodal_vertices
#print axioms saved_and_active
#print axioms spectral_agreement
#print axioms independent_candidate
#print axioms gearbox_zero_iff_resident
#print axioms prime_iff_integer_steps
#print axioms trace_at_spin_two
#print axioms trace_recovers_vertices

end
end WilsonOracle
