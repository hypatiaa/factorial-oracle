import FactorSearch
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.Simproc.Factors

/-! The canonical divisor path obtained by restarting the factorial-stride search at
each new shell. Descending records the first prime encountered. Ascending replays
the same labels in reverse and visits exactly the same shells. -/

namespace FactorSearch.Path

/-- The scan has enough fuel to see the first drop even when the shell is prime. -/
def firstLabel (n : ℕ) : ℕ :=
  (firstDrop n 0 (stride n 0) (n + 1)).getD n

theorem firstLabel_eq_minFac {n : ℕ} (hn : 2 ≤ n) : firstLabel n = n.minFac := by
  have hle := Nat.minFac_le (by omega : 0 < n)
  simp [firstLabel, firstDrop_finds_minFac hn 0 (n + 1) (by omega) (by omega)]

/-- The least prime labels the edge. The measured orbit order is its lower endpoint. -/
theorem first_edge {n : ℕ} (hn : 2 ≤ n) :
    (firstLabel n).Prime ∧
    probe n (firstLabel n) = n / firstLabel n ∧
    firstLabel n * probe n (firstLabel n) = n := by
  rw [firstLabel_eq_minFac hn]
  have hg := first_drop_factor hn
  rw [probe_eq, Nat.div_div_self (Nat.gcd_dvd_left ..) (by omega)] at hg
  rw [probe_eq, hg]
  exact ⟨Nat.minFac_prime (by omega), rfl, Nat.mul_div_cancel' (Nat.minFac_dvd _)⟩

theorem first_orbit_order {n : ℕ} (hn : 2 ≤ n) :
    orderOf (toothPhase n (stride n (firstLabel n))) = n / firstLabel n := by
  exact (exact_tooth_order (by omega : 0 < n) _).trans (first_edge hn).2.1

/-- Execute the scan at each shell and descend by the prime it returned. -/
def labels (n : ℕ) : List ℕ :=
  if _hn : 2 ≤ n then
    let p := firstLabel n
    p :: labels (n / p)
  else []
termination_by n
decreasing_by
  apply Nat.div_lt_self (by omega)
  rw [firstLabel_eq_minFac _hn]
  exact (Nat.minFac_prime (by omega : n ≠ 1)).one_lt

theorem labels_eq_primeFactorsList (n : ℕ) : labels n = n.primeFactorsList := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | k
    · rw [labels]
      simp
    · change labels 1 = (1 : ℕ).primeFactorsList
      rw [labels]
      simp
    · have hn : 2 ≤ k + 2 := by omega
      change labels (k + 2) = (k + 2).primeFactorsList
      rw [labels, dite_eq_left hn, firstLabel_eq_minFac hn, Nat.primeFactorsList_add_two]
      exact congrArg (List.cons (k + 2).minFac)
        (ih ((k + 2) / (k + 2).minFac) (Nat.div_lt_self (by omega)
          (Nat.minFac_prime (show k + 2 ≠ 1 by omega)).one_lt))

/-- Count each prime direction once, regardless of the number of steps along it. -/
theorem distinct_directions (n : ℕ) : (labels n).toFinset = n.primeFactors := by
  rw [labels_eq_primeFactorsList]
  rfl

/-- The pen records the starting shell as well as every successive quotient. -/
def downPath (n : ℕ) : List ℕ := (labels n).scanl (· / ·) n

/-- Replay the labels from the unit shell using multiplication. -/
def upPath (n : ℕ) : List ℕ :=
  (labels n).reverse.scanl (fun shell p => p * shell) 1

private theorem quotient_path (xs : List ℕ) (h : ∀ p ∈ xs, 0 < p) :
    xs.scanl (· / ·) xs.prod = xs.scanr (· * ·) 1 := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    have hp : 0 < p := h p (by simp)
    simp only [List.scanl_cons, List.scanr_cons, List.prod_cons, List.foldr_cons,
      Nat.mul_div_cancel_left _ hp]
    rw [← List.prod_eq_foldr, ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]

theorem labels_prod {n : ℕ} (hn : 0 < n) : (labels n).prod = n := by
  rw [labels_eq_primeFactorsList]
  exact Nat.prod_primeFactorsList (Nat.ne_of_gt hn)

/-- Replaying from 1 reconstructs every node of the canonical descent, in reverse. -/
theorem replay_every_shell {n : ℕ} (hn : 0 < n) : upPath n = (downPath n).reverse := by
  have hp : ∀ p ∈ labels n, 0 < p := by
    rw [labels_eq_primeFactorsList]
    exact fun _ h => (Nat.prime_of_mem_primeFactorsList h).pos
  have hdown := quotient_path (labels n) hp
  rw [labels_prod hn] at hdown
  unfold upPath downPath
  rw [hdown, List.scanr_eq_scanl_reverse, List.reverse_reverse]
  rfl

theorem reaches_one {n : ℕ} (hn : 0 < n) : (downPath n).getLast? = some 1 := by
  rw [← List.head?_reverse, ← replay_every_shell hn]
  simp only [upPath, List.head?_scanl]

theorem rebuilds_start {n : ℕ} (hn : 0 < n) : (upPath n).getLast? = some n := by
  rw [replay_every_shell hn, List.getLast?_reverse]
  simp only [downPath, List.head?_scanl]

theorem labels_720 : labels 720 = [2, 2, 2, 2, 3, 3, 5] := by
  rw [labels_eq_primeFactorsList]
  simp only [Nat.primeFactorsList_ofNat]

theorem round_trip_720 :
    downPath 720 = [720, 360, 180, 90, 45, 15, 5, 1] ∧
    upPath 720 = [1, 5, 15, 45, 90, 180, 360, 720] := by
  simp only [downPath, upPath, labels_720]
  exact ⟨rfl, rfl⟩

#print axioms first_edge
#print axioms first_orbit_order
#print axioms labels_eq_primeFactorsList
#print axioms distinct_directions
#print axioms replay_every_shell
#print axioms reaches_one
#print axioms rebuilds_start
#print axioms round_trip_720

end FactorSearch.Path
