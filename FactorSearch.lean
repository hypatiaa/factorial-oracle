import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! Reverse factor search on a direct integer shell. At spin two, with zero
carrier, the positive tooth has phase exp(2πi t/N). All executable functions
below work with integers; the complex phase only appears in the specification. -/
namespace FactorSearch

def toothOrder (N t : ℕ) := N / N.gcd t

noncomputable def toothPhase (N t : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * t / N)

theorem exact_tooth_order {N : ℕ} (hN : 0 < N) (t : ℕ) :
    orderOf (toothPhase N t) = toothOrder N t := by
  have hp := (Complex.isPrimitiveRoot_exp N hN.ne').pow_div_gcd t
    (Nat.gcd_pos_of_pos_left t hN).ne'
  have he : toothPhase N t = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / N) ^ t := by
    unfold toothPhase
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  rw [he]
  exact hp.eq_orderOf.symm

/-- Factorial stride with reduction after every multiplication. -/
def stride (N : ℕ) : ℕ → ℕ
  | 0 => 1 % N
  | k+1 => ((k+1) * stride N k) % N

theorem stride_eq (N k : ℕ) : stride N k = k.factorial % N := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [stride, ih, Nat.factorial_succ, Nat.mul_mod_mod]

def probe (N k : ℕ) := toothOrder N (stride N k)

theorem probe_eq (N k : ℕ) : probe N k = N / N.gcd k.factorial := by
  unfold probe toothOrder
  rw [stride_eq, Nat.gcd_comm N (k.factorial % N), ← Nat.gcd_rec]

theorem full_order_iff {N : ℕ} (hN : 2 ≤ N) (k : ℕ) :
    probe N k = N ↔ k < N.minFac := by
  rw [probe_eq, ← Nat.coprime_factorial_iff (by omega : N ≠ 1)]
  change N / N.gcd k.factorial = N ↔ N.gcd k.factorial = 1
  constructor
  · intro h
    have hg := Nat.gcd_pos_of_pos_left k.factorial (by omega : 0 < N)
    by_contra hn
    have := Nat.div_lt_self (by omega : 0 < N) (by omega : 1 < N.gcd k.factorial)
    omega
  · intro h
    rw [h, Nat.div_one]

theorem order_drop_iff {N : ℕ} (hN : 2 ≤ N) (k : ℕ) :
    probe N k < N ↔ N.minFac ≤ k := by
  have h := full_order_iff hN k
  have hle : probe N k ≤ N := Nat.div_le_self _ _
  omega

theorem first_shorter_orbit {N : ℕ} (hN : 2 ≤ N) :
    IsLeast {k : ℕ | orderOf (toothPhase N (stride N k)) < N} N.minFac := by
  have he (k : ℕ) : orderOf (toothPhase N (stride N k)) < N ↔ N.minFac ≤ k := by
    rw [exact_tooth_order (by omega : 0 < N)]
    exact order_drop_iff hN k
  exact ⟨(he _).mpr le_rfl, fun k hk => (he k).mp hk⟩

/-- At the first drop the gcd is exactly one copy of the least prime factor. -/
theorem first_drop_factor {N : ℕ} (hN : 2 ≤ N) :
    N / probe N N.minFac = N.minFac := by
  have hm := Nat.minFac_pos N
  have hc := (Nat.coprime_factorial_iff (by omega : N ≠ 1)).mpr
    (show N.minFac - 1 < N.minFac by omega)
  have hf : N.minFac.factorial = (N.minFac-1).factorial * N.minFac := by
    have hs := Nat.factorial_succ (N.minFac-1)
    rw [show N.minFac-1+1 = N.minFac by omega] at hs
    rw [hs, Nat.mul_comm]
  rw [probe_eq, Nat.div_div_self (Nat.gcd_dvd_left ..) (by omega), hf, Nat.gcd_comm]
  exact Nat.gcd_mul_of_coprime_of_dvd hc.symm (Nat.minFac_dvd N)

theorem endpoint_full_iff_prime {N : ℕ} (hN : 2 ≤ N) :
    probe N N.sqrt = N ↔ N.Prime := by
  rw [full_order_iff hN]
  constructor
  · intro h
    by_contra hc
    exact h.not_ge (Nat.le_sqrt'.mpr (Nat.minFac_sq_le_self (by omega) hc))
  · intro hp
    rw [hp.minFac_eq]
    exact Nat.sqrt_lt_self hN

/-- Check successive strides, carrying only the current residue. The last
    argument counts how many successive indices may still be visited. -/
def firstDrop (N k x : ℕ) : ℕ → Option ℕ
  | 0 => none
  | fuel+1 =>
    if toothOrder N x < N then some k
    else firstDrop N (k+1) (((k+1)*x) % N) fuel

theorem firstDrop_finds_minFac {N : ℕ} (hN : 2 ≤ N) (k fuel : ℕ)
    (hk : k ≤ N.minFac) (hf : N.minFac < k+fuel) :
    firstDrop N k (stride N k) fuel = some N.minFac := by
  induction fuel generalizing k with
  | zero => omega
  | succ fuel ih =>
    change (if probe N k < N then some k else firstDrop N (k+1) (stride N (k+1)) fuel) = _
    split
    · rename_i h
      exact congrArg some (Nat.le_antisymm hk ((order_drop_iff hN k).mp h))
    · rename_i h
      have hlt : k < N.minFac := Nat.lt_of_not_ge (fun he => h ((order_drop_iff hN k).mpr he))
      apply ih <;> omega

/-- Entry point for N ≥ 2. A proper endpoint split is used immediately.
    A total collapse restarts at stride 0! to locate the first order drop. -/
def factor? (N : ℕ) : Option ℕ :=
  if N < 2 then none else
  let r := probe N N.sqrt
  if r = N then none else
  if r = 1 then firstDrop N 0 (stride N 0) (N.sqrt+1) else some (N/r)

theorem composite_result {N : ℕ} (hN : 2 ≤ N) (hc : ¬ N.Prime) :
    ∃ d, factor? N = some d ∧ d ∣ N ∧ 1 < d ∧ d < N := by
  have hfull := (endpoint_full_iff_prime hN).not.mpr hc
  simp only [factor?, ite_eq_right (Nat.not_lt.mpr hN), ite_eq_right hfull]
  by_cases h : probe N N.sqrt = 1
  · rw [ite_eq_left h, firstDrop_finds_minFac hN]
    · exact ⟨_, rfl, Nat.minFac_dvd N, (Nat.minFac_prime (by omega : N ≠ 1)).one_lt,
        (Nat.not_prime_iff_minFac_lt hN).mp hc⟩
    · omega
    · have := Nat.le_sqrt'.mpr (Nat.minFac_sq_le_self (by omega : 0 < N) hc)
      omega
  · rw [ite_eq_right h]
    let g := N.gcd N.sqrt.factorial
    have hd : g ∣ N := Nat.gcd_dvd_left _ _
    have hrecover : N / probe N N.sqrt = g := by
      rw [probe_eq, Nat.div_div_self hd (by omega)]
    refine ⟨g, by rw [hrecover], hd, ?_, ?_⟩
    · have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
      have : g ≠ 1 := by
        intro he
        apply hfull
        rw [probe_eq, show N.gcd N.sqrt.factorial = 1 from he, Nat.div_one]
      omega
    · have hle := Nat.le_of_dvd (by omega : 0 < N) hd
      have : g ≠ N := by
        intro he
        apply h
        rw [probe_eq, show N.gcd N.sqrt.factorial = N from he, Nat.div_self (by omega)]
      omega

theorem returns_none_iff_prime {N : ℕ} (hN : 2 ≤ N) :
    factor? N = none ↔ N.Prime := by
  constructor
  · intro h
    by_contra hc
    obtain ⟨_, hd, _⟩ := composite_result hN hc
    simp [h] at hd
  · intro hp
    simp [factor?, Nat.not_lt.mpr hN, (endpoint_full_iff_prime hN).mpr hp]

theorem example_221 : stride 221 14 = 195 ∧ probe 221 14 = 17 ∧ factor? 221 = some 13 := by
  have hs : 14 = Nat.sqrt 221 := Nat.eq_sqrt.mpr (by decide)
  simp only [factor?, ← hs]
  decide

theorem example_60 : probe 60 7 = 1 ∧ factor? 60 = some 2 := by
  have hs : 7 = Nat.sqrt 60 := Nat.eq_sqrt.mpr (by decide)
  simp only [factor?, ← hs]
  decide

theorem example_97 : probe 97 9 = 97 ∧ factor? 97 = none := by
  have hs : 9 = Nat.sqrt 97 := Nat.eq_sqrt.mpr (by decide)
  simp only [factor?, ← hs]
  decide

#print axioms exact_tooth_order
#print axioms order_drop_iff
#print axioms first_shorter_orbit
#print axioms first_drop_factor
#print axioms composite_result
#print axioms returns_none_iff_prime
#print axioms example_221
#print axioms example_60
#print axioms example_97
end FactorSearch
