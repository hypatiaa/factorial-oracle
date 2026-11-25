import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Robin Miller's original two-frequency helix and the equal-amplitude m-comb.
The radius is signed. The shell denominator must be nonzero in the results
which identify the original labels with carrier and spread. -/
namespace FourierHelix
noncomputable section

def phase (x : ℝ) : ℂ := Complex.exp (((Real.pi * x : ℝ) : ℂ) * Complex.I)

theorem phase_add (x y : ℝ) : phase (x+y) = phase x * phase y := by
  simp only [phase, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem phase_neg (x : ℝ) : phase (-x) = (phase x)⁻¹ := by
  simp [phase, Complex.exp_neg]

theorem phase_pair (x : ℝ) : phase (-x) + phase x = 2 * (Real.cos (Real.pi*x) : ℂ) := by
  simp only [phase, mul_neg, Complex.ofReal_neg, Complex.exp_mul_I,
    Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos]
  ring

def label (N t₁ t₂ c : ℝ) := N*t₁ + c*t₂

def tooth (N t₁ t₂ ρ s c : ℝ) : ℂ := ρ * phase (label N t₁ t₂ c * s / N)

theorem split_tooth {N : ℝ} (hN : N ≠ 0) (t₁ t₂ ρ s c : ℝ) :
    tooth N t₁ t₂ ρ s c = ρ * phase (t₁*s) * phase (c*(t₂*s/N)) := by
  have h : label N t₁ t₂ c * s/N = t₁*s + c*(t₂*s/N) := by
    unfold label
    field_simp
  rw [tooth, h, phase_add, mul_assoc]

/-- The two cases of offsets(m) in the viewer, with zero-based tooth index j. -/
def offset (m j : ℕ) : ℝ :=
  if m % 2 = 1 then (j : ℝ) - (m/2 : ℕ) else 2*(j : ℝ) - m + 1

def stride (m : ℕ) : ℝ := if m % 2 = 1 then 1 else 2

theorem offset_succ (m j : ℕ) : offset m (j+1) = offset m j + stride m := by
  by_cases h : m % 2 = 1 <;> simp [offset, stride, h] <;> ring

theorem offset_reflect {m j : ℕ} (hj : j < m) :
    offset m (m-1-j) = -offset m j := by
  have hj' : j ≤ m-1 := by omega
  have hm : 1 ≤ m := by omega
  by_cases ho : m % 2 = 1
  · have he : m = 2*(m/2)+1 := by omega
    have hr : (m : ℝ) = 2*((m/2 : ℕ) : ℝ)+1 := by exact_mod_cast he
    simp only [offset, ite_eq_left ho, Nat.cast_sub hj', Nat.cast_sub hm, Nat.cast_one]
    rw [hr]
    ring
  · simp only [offset, ite_eq_right ho, Nat.cast_sub hj', Nat.cast_sub hm, Nat.cast_one]
    ring

/-- The ordered partial walk, starting at the origin. Use j = m for its endpoint. -/
def walk (N t₁ t₂ ρ s : ℝ) (m : ℕ) : ℕ → ℂ
  | 0 => 0
  | j+1 => walk N t₁ t₂ ρ s m j + tooth N t₁ t₂ ρ s (offset m j)

theorem original_labels (N t₁ t₂ : ℝ) :
    label N t₁ t₂ (offset 2 0) = N*t₁-t₂ ∧
    label N t₁ t₂ (offset 2 1) = N*t₁+t₂ := by
  norm_num [label, offset]
  constructor

theorem original_pair {N : ℝ} (hN : N ≠ 0) (t₁ t₂ ρ s : ℝ) :
    walk N t₁ t₂ ρ s 2 2 =
      ρ * phase (t₁*s) * (2 * (Real.cos (Real.pi*(t₂*s/N)) : ℂ)) := by
  rw [← phase_pair]
  simp only [walk, zero_add, split_tooth hN]
  norm_num [offset]
  ring

def ratio (N t₂ s : ℝ) (m : ℕ) : ℂ := phase (stride m * (t₂*s/N))

theorem tooth_step {N : ℝ} (hN : N ≠ 0) (t₁ t₂ ρ s : ℝ) (m j : ℕ) :
    tooth N t₁ t₂ ρ s (offset m (j+1)) =
      tooth N t₁ t₂ ρ s (offset m j) * ratio N t₂ s m := by
  rw [offset_succ, split_tooth hN, split_tooth hN, add_mul, phase_add, ratio]
  simp only [mul_assoc]

theorem tooth_power {N : ℝ} (hN : N ≠ 0) (t₁ t₂ ρ s : ℝ) (m j : ℕ) :
    tooth N t₁ t₂ ρ s (offset m j) =
      tooth N t₁ t₂ ρ s (offset m 0) * ratio N t₂ s m ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [tooth_step hN, ih, pow_succ, mul_assoc]

theorem walk_geometric {N : ℝ} (hN : N ≠ 0) (t₁ t₂ ρ s : ℝ) (m j : ℕ) :
    walk N t₁ t₂ ρ s m j = tooth N t₁ t₂ ρ s (offset m 0) *
      ∑ i ∈ Finset.range j, ratio N t₂ s m ^ i := by
  induction j with
  | zero => simp [walk]
  | succ j ih => rw [walk, ih, Finset.sum_range_succ, mul_add, ← tooth_power hN]

/-- The real spread kernel, summed over the viewer's actual centered offsets. -/
def kernel (m : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range m, Real.cos (Real.pi*(offset m j*x))

theorem centered_kernel (m : ℕ) (x : ℝ) :
    ∑ j ∈ Finset.range m, phase (offset m j*x) = (kernel m x : ℂ) := by
  have hr : ∑ j ∈ Finset.range m, phase (-(offset m j*x)) =
      ∑ j ∈ Finset.range m, phase (offset m j*x) := by
    rw [← Finset.sum_range_reflect (fun j => phase (offset m j*x)) m]
    apply Finset.sum_congr rfl
    intro j hj
    rw [offset_reflect (Finset.mem_range.mp hj), neg_mul]
  have hp : (∑ j ∈ Finset.range m, phase (-(offset m j*x))) +
      (∑ j ∈ Finset.range m, phase (offset m j*x)) = 2 * (kernel m x : ℂ) := by
    rw [← Finset.sum_add_distrib, kernel]
    simp only [Complex.ofReal_sum]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => phase_pair _
  rw [hr, ← two_mul] at hp
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hp

theorem full_comb {N : ℝ} (hN : N ≠ 0) (t₁ t₂ ρ s : ℝ) (m : ℕ) :
    walk N t₁ t₂ ρ s m m = ρ * phase (t₁*s) * (kernel m (t₂*s/N) : ℂ) := by
  have partialWalk (j : ℕ) : walk N t₁ t₂ ρ s m j =
      ∑ i ∈ Finset.range j, tooth N t₁ t₂ ρ s (offset m i) := by
    induction j with
    | zero => simp [walk]
    | succ j ih => rw [walk, ih, Finset.sum_range_succ]
  rw [partialWalk, ← centered_kernel, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => split_tooth hN t₁ t₂ ρ s (offset m i)

theorem aligned_walk {N : ℝ} (hN : N ≠ 0) (t₁ t₂ ρ s : ℝ) (m j : ℕ)
    (ha : ratio N t₂ s m = 1) : walk N t₁ t₂ ρ s m j =
      (j : ℂ) * tooth N t₁ t₂ ρ s (offset m 0) := by
  rw [walk_geometric hN, ha]
  simp [mul_comm]

theorem closes_iff {N : ℝ} (hN : N ≠ 0) (t₁ t₂ ρ s : ℝ) (m j : ℕ)
    (hρ : ρ ≠ 0) (ha : ratio N t₂ s m ≠ 1) :
    walk N t₁ t₂ ρ s m j = 0 ↔ ratio N t₂ s m ^ j = 1 := by
  have hn : tooth N t₁ t₂ ρ s (offset m 0) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hρ) (Complex.exp_ne_zero _)
  have hd := sub_ne_zero.mpr ha
  have hg := geom_sum_mul (ratio N t₂ s m) j
  rw [walk_geometric hN, mul_eq_zero, or_iff_right hn]
  constructor
  · intro h
    rw [h, zero_mul] at hg
    exact sub_eq_zero.mp hg.symm
  · intro h
    rw [h, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_right hd

theorem phase_eq_one_iff (x : ℝ) : phase x = 1 ↔ ∃ n : ℤ, x = 2*(n : ℝ) := by
  rw [phase, Complex.exp_eq_one_iff]
  have hn (n : ℤ) : (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
      ((Real.pi * (2*(n : ℝ)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  constructor
  · rintro ⟨n, h⟩
    rw [hn] at h
    exact ⟨n, mul_left_cancel₀ Real.pi_ne_zero
      (Complex.ofReal_injective (mul_right_cancel₀ Complex.I_ne_zero h))⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, (hn n).symm⟩

/-- Odd combs align at even integral spread and even combs at integral spread. -/
theorem alignment_readout (N t₂ s : ℝ) (m : ℕ) :
    ratio N t₂ s m = 1 ↔
      if m % 2 = 1 then ∃ n : ℤ, t₂*s/N = 2*(n : ℝ)
      else ∃ n : ℤ, t₂*s/N = (n : ℝ) := by
  rw [ratio, phase_eq_one_iff]
  by_cases hm : m % 2 = 1 <;> simp [stride, hm]

/-- The host's scale-A chart, applied to any tooth or partial walk. -/
theorem chart_on_sphere (w : ℂ) :
    let r := w.re ^ 2 + w.im ^ 2
    (2*w.re/(r+1))^2 + (2*w.im/(r+1))^2 + ((r-1)/(r+1))^2 = 1 := by
  dsimp
  have hd : w.re^2 + w.im^2 + 1 ≠ 0 := by positivity
  field_simp
  ring

namespace Oracle

/-- GeoGebra's n₃, with the original two independent gear inputs. -/
def shell (n₁ : ℕ) (φ₁ φ₃ : ℝ) : ℝ := n₁.factorial - (φ₃-φ₁)

/-- The GeoGebra exponent slider takes integer steps from −1 to 1.
    Use a nonzero base at negative exponents when interpreting the file. -/
def amplitude (n₆ N : ℝ) (α : ℤ) : ℝ := (n₆*N)^α

/-- The exact order of operations in the exponent of the source file. -/
def sourcePhase (k s N : ℝ) : ℂ :=
  Complex.exp (((k*s*Real.pi : ℝ) : ℂ) * Complex.I / (N : ℂ))

theorem sourcePhase_eq (k s N : ℝ) : sourcePhase k s N = phase (k*s/N) := by
  unfold sourcePhase phase
  congr 1
  push_cast
  ring

/-- The two source expressions, before any carrier factorization.
    The argument a is the common, evaluated amplitude of the two teeth. -/
def z₁ (N t₁ t₂ a s : ℝ) : ℂ := a * sourcePhase (N*t₁-t₂) s N
def z₂ (N t₁ t₂ a s : ℝ) : ℂ := a * sourcePhase (N*t₁+t₂) s N

theorem pair_is_first_comb (N t₁ t₂ a s : ℝ) :
    z₁ N t₁ t₂ a s = tooth N t₁ t₂ a s (offset 2 0) ∧
    z₂ N t₁ t₂ a s = tooth N t₁ t₂ a s (offset 2 1) := by
  obtain ⟨hl, hr⟩ := original_labels N t₁ t₂
  simp [tooth, hl, hr, z₁, z₂, sourcePhase_eq]

/-- The GeoGebra point z₀ is the two-step walk endpoint. -/
theorem sum_is_walk (N t₁ t₂ a s : ℝ) :
    z₁ N t₁ t₂ a s + z₂ N t₁ t₂ a s = walk N t₁ t₂ a s 2 2 := by
  obtain ⟨hl, hr⟩ := pair_is_first_comb N t₁ t₂ a s
  simp [walk, hl, hr]

theorem factorial_pair (n₁ : ℕ) (φ₁ φ₃ n₆ t₁ t₂ s : ℝ) (α : ℤ)
    (hN : shell n₁ φ₁ φ₃ ≠ 0) :
    let N := shell n₁ φ₁ φ₃
    let a := amplitude n₆ N α
    z₁ N t₁ t₂ a s + z₂ N t₁ t₂ a s =
      a * phase (t₁*s) * (2 * (Real.cos (Real.pi*(t₂*s/N)) : ℂ)) := by
  dsimp only
  rw [sum_is_walk, original_pair hN]

/-- GeoGebra point C = z₁ - z₂, with its orientation. -/
theorem difference {N : ℝ} (hN : N ≠ 0) (t₁ t₂ a s : ℝ) :
    z₁ N t₁ t₂ a s - z₂ N t₁ t₂ a s =
      a * phase (t₁*s) * (-2 * (Real.sin (Real.pi*(t₂*s/N)) : ℂ) * Complex.I) := by
  have he (x : ℝ) : phase (-x) - phase x =
      -2 * (Real.sin (Real.pi*x) : ℂ) * Complex.I := by
    simp only [phase, mul_neg, Complex.ofReal_neg, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg, Complex.ofReal_sin]
    ring
  obtain ⟨hl, hr⟩ := pair_is_first_comb N t₁ t₂ a s
  rw [hl, hr, split_tooth hN, split_tooth hN, ← he, mul_sub]
  norm_num [offset]

/-- Exact length of the segment measured as distancez1z2. -/
theorem tip_distance {N : ℝ} (hN : N ≠ 0) (t₁ t₂ a s : ℝ) :
    dist (z₁ N t₁ t₂ a s) (z₂ N t₁ t₂ a s) =
      2 * |a| * |Real.sin (Real.pi*(t₂*s/N))| := by
  rw [dist_eq_norm, difference hN]
  simp only [norm_mul, phase, Complex.norm_exp_ofReal_mul_I, norm_neg,
    Complex.norm_ofNat, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, mul_one]
  ring

theorem saved_labels :
    shell 4 1 1 = 24 ∧ amplitude 1 (shell 4 1 1) 1 = 24 ∧
    label (shell 4 1 1) 1 1 (offset 2 0) = 23 ∧
    label (shell 4 1 1) 1 1 (offset 2 1) = 25 := by
  norm_num [shell, amplitude, Nat.factorial, label, offset]

end Oracle

#print axioms original_labels
#print axioms original_pair
#print axioms walk_geometric
#print axioms full_comb
#print axioms aligned_walk
#print axioms closes_iff
#print axioms alignment_readout
#print axioms chart_on_sphere
#print axioms Oracle.sum_is_walk
#print axioms Oracle.factorial_pair
#print axioms Oracle.difference
#print axioms Oracle.tip_distance
#print axioms Oracle.saved_labels

end
end FourierHelix
