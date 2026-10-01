import DMSolutions.OEIS_A370092.CoreTwoAdic
import DMSolutions.OEIS_A370092.CoreOdd

/-!
# OEIS A370092: Bala's period conjecture

`bounds_core`: for every `k > 2`, the sequence `a_mod_k k` is eventually periodic with period
`φ(k)`, from the index `k` on.

Assembly. The divisibility `k ∣ b(n + φ(k)) - b(n)` for `n ≥ k` is checked prime power by prime
power (`Nat.dvd_iff_prime_pow_dvd_dvd`).

* For an odd prime power `p^j ∣ k`, use `odd_prime_pow` and `φ(p^j) ∣ φ(k)`.
* For `2^j ∣ k` with `j ≥ 2`, use `two_adic` and `φ(2^j) = 2^(j-1) ∣ φ(k)`.
* For `j = 1`, `φ(k)` is even because `k > 2`, and `b` has period `2` modulo `4` from `n = 3` on.
-/

open Finset Nat

namespace A370092Core

/-- A congruence with period `P0` from `N` on also holds for every multiple `P` of `P0`. -/
theorem period_of_dvd (f : ℕ → ℤ) (q : ℤ) (N P0 P : ℕ) (h : ∀ m, N ≤ m → q ∣ f (m + P0) - f m)
    (hP : P0 ∣ P) : ∀ m, N ≤ m → q ∣ f (m + P) - f m := by
  obtain ⟨t, rfl⟩ := hP
  induction t with
  | zero =>
    intro m _
    simp
  | succ t ih =>
    intro m hm
    have e : f (m + P0 * (t + 1)) - f m =
        (f (m + P0 * t + P0) - f (m + P0 * t)) + (f (m + P0 * t) - f m) := by
      rw [show m + P0 * (t + 1) = m + P0 * t + P0 by ring]
      ring
    rw [e]
    exact dvd_add (h _ (le_trans hm (Nat.le_add_right m _))) (ih m hm)

/-- The prime `2`: `2^(f+2) ∣ b(n + 2^(f+1)) - b(n)` for `n ≥ f + 3`. -/
theorem two_pow_period (f n : ℕ) (hn : f + 3 ≤ n) :
    (2 : ℤ) ^ (f + 2) ∣ b (n + 2 ^ (f + 1)) - b n :=
  two_adic b A0Z A1Z two_b_eq_A (by rw [A1Z_one_add_two]; exact dvd_zero 2) f n hn

/-- `k ∣ b(n + φ(k)) - b(n)` for `k > 2` and `n ≥ k`. -/
theorem main_dvd (k : ℕ) (hk : 2 < k) (n : ℕ) (hn : k ≤ n) : (k : ℤ) ∣ b (n + φ k) - b n := by
  rw [Int.natCast_dvd, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p j hp hpj
  rw [← Int.natCast_dvd]
  push_cast
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  have hpj_le : p ^ j ≤ k := Nat.le_of_dvd (by omega) hpj
  have hj_lt : j < p ^ j := Nat.lt_pow_self hp.one_lt
  by_cases hp2 : p = 2
  · subst hp2
    rcases Nat.lt_or_ge j 2 with hj1 | hj2
    · obtain rfl : j = 1 := by omega
      have hev : 2 ∣ φ k := (Nat.totient_even hk).two_dvd
      have h4 : ∀ m, 3 ≤ m → (2 : ℤ) ^ 2 ∣ b (m + 2) - b m := fun m hm => two_pow_period 0 m hm
      rw [pow_one]
      exact (dvd_pow_self 2 two_ne_zero).trans (period_of_dvd b _ 3 2 (φ k) h4 hev n (by omega))
    · obtain ⟨f, rfl⟩ : ∃ f, j = f + 2 := ⟨j - 2, by omega⟩
      have hφ : 2 ^ (f + 1) ∣ φ k := by
        have h := Nat.totient_dvd_of_dvd hpj
        rwa [Nat.totient_prime_pow Nat.prime_two (by omega), show f + 2 - 1 = f + 1 by omega,
          show 2 - 1 = 1 from rfl, mul_one] at h
      have hle : f + 3 ≤ n := by
        have h1 : f + 2 < 2 ^ (f + 2) := hj_lt
        omega
      exact period_of_dvd b _ (f + 3) _ _ (fun m hm => two_pow_period f m hm) hφ n hle
  · have hφ : φ (p ^ j) ∣ φ k := Nat.totient_dvd_of_dvd hpj
    exact period_of_dvd b _ j _ _ (fun m hm => odd_prime_pow p j m hp hp2 hm) hφ n (by omega)

/-- **Bala's conjecture for A370092.** For every `k > 2`, `a_mod_k k` is eventually periodic with
period `φ(k)` (from the index `k` on). -/
theorem bounds_core (k : ℕ) (hk : 2 < k) :
    ∃ P : ℕ, P ∣ totient k ∧ eventually_periodic (a_mod_k k) P := by
  refine ⟨φ k, dvd_rfl, ?_⟩
  unfold eventually_periodic
  refine ⟨k, fun n hn => ?_⟩
  have h := main_dvd k hk n hn
  rw [← dvd_neg, neg_sub] at h
  simp only [a_mod_k]
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr h

end A370092Core
