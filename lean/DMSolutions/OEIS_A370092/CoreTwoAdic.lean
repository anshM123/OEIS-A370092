import Mathlib

/-!
# OEIS A370092: the prime 2

An abstract statement in `ℤ` (`two_adic`). Suppose that `2 b(n) = 2^n A0(n) + F(n)` for all `n`,
where `F(n) = ∑_m C(n, m) 2^m A1(m)`, and that `A1(1) + A1(2)` is even. Then, for `e = f + 2 ≥ 2`
and `n ≥ e + 1`, `2^e ∣ b(n + 2^(e-1)) - b(n)`.

Proof. `F(n) = Φ((1 + 2X)^n)` for the linear functional `Φ(X^m) = A1(m)` on `ℤ[X]` (`Phi_F`),
and `(1 + 2X)^(2^(e-1)) = 1 + 2^e (X + X^2) + 2^(e+1) R` (`sq_lemma`). Since `(1 + 2X)^n ≡ 1`
mod `2`, this gives `F(n + 2^(e-1)) - F(n) ≡ 2^e (A1(1) + A1(2)) ≡ 0 (mod 2^(e+1))`. The term
`2^n A0(n)` is `0` mod `2^(e+1)` for `n ≥ e + 1`.
-/

open Finset Polynomial

namespace A370092Core

/-- `Phi A1 N p = ∑_{i < N} A1 i * coeff p i`. -/
noncomputable def Phi (A1 : ℕ → ℤ) (N : ℕ) : ℤ[X] →ₗ[ℤ] ℤ :=
  ∑ i ∈ range N, A1 i • Polynomial.lcoeff ℤ i

theorem Phi_apply (A1 : ℕ → ℤ) (N : ℕ) (p : ℤ[X]) :
    Phi A1 N p = ∑ i ∈ range N, A1 i * p.coeff i := by
  simp [Phi]

theorem Phi_X_pow (A1 : ℕ → ℤ) (N j : ℕ) (hj : j < N) : Phi A1 N (X ^ j) = A1 j := by
  rw [Phi_apply]
  simp [Polynomial.coeff_X_pow, hj]

theorem Phi_intCast_mul (A1 : ℕ → ℤ) (N : ℕ) (c : ℤ) (p : ℤ[X]) :
    Phi A1 N ((c : ℤ[X]) * p) = c * Phi A1 N p := by
  rw [← zsmul_eq_mul, map_zsmul, smul_eq_mul]

theorem one_add_two_X_pow (m : ℕ) :
    (1 + 2 * X : ℤ[X]) ^ m = ∑ j ∈ range (m + 1), ((m.choose j * 2 ^ j : ℤ) : ℤ[X]) * X ^ j := by
  rw [add_comm (1 : ℤ[X]) (2 * X), add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

theorem Phi_F (A1 : ℕ → ℤ) (N m : ℕ) (hm : m < N) :
    Phi A1 N ((1 + 2 * X : ℤ[X]) ^ m) = ∑ j ∈ range (m + 1), (m.choose j : ℤ) * 2 ^ j * A1 j := by
  rw [one_add_two_X_pow, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < m + 1 := Finset.mem_range.mp hj
  rw [Phi_intCast_mul, Phi_X_pow A1 N j (by omega)]

theorem sq_lemma (f : ℕ) : ∃ R : ℤ[X],
    (1 + 2 * X : ℤ[X]) ^ (2 ^ (f + 1)) = 1 + 2 ^ (f + 2) * (X ^ 1 + X ^ 2) + 2 ^ (f + 3) * R := by
  induction f with
  | zero => exact ⟨0, by ring⟩
  | succ f ih =>
    obtain ⟨R, hR⟩ := ih
    refine ⟨R + 2 ^ f * (X ^ 1 + X ^ 2 + 2 * R) ^ 2, ?_⟩
    rw [show 2 ^ (f + 1 + 1) = 2 ^ (f + 1) * 2 by ring, pow_mul, hR]
    ring

theorem lin_lemma (n : ℕ) : ∃ Q : ℤ[X], (1 + 2 * X : ℤ[X]) ^ n = 1 + 2 * Q := by
  induction n with
  | zero => exact ⟨0, by ring⟩
  | succ n ih =>
    obtain ⟨Q, hQ⟩ := ih
    exact ⟨Q + X + 2 * Q * X, by rw [pow_succ, hQ]; ring⟩

/-- **The prime 2.** If `2 b(n) = 2^n A0(n) + ∑_m C(n, m) 2^m A1(m)` and `A1(1) + A1(2)` is even,
then `2^(f+2) ∣ b(n + 2^(f+1)) - b(n)` for `n ≥ f + 3`. -/
theorem two_adic (b A0 A1 : ℕ → ℤ)
    (hb : ∀ n, 2 * b n = 2 ^ n * A0 n + ∑ m ∈ range (n + 1), (n.choose m : ℤ) * 2 ^ m * A1 m)
    (hA : 2 ∣ A1 1 + A1 2) (f n : ℕ) (hn : f + 3 ≤ n) :
    (2 : ℤ) ^ (f + 2) ∣ b (n + 2 ^ (f + 1)) - b n := by
  obtain ⟨R, hR⟩ := sq_lemma f
  obtain ⟨Q, hQ⟩ := lin_lemma n
  obtain ⟨c, hc⟩ := hA
  have hdiff : (1 + 2 * X : ℤ[X]) ^ (n + 2 ^ (f + 1)) - (1 + 2 * X) ^ n =
      ((2 ^ (f + 2) : ℤ) : ℤ[X]) * (X ^ 1 + X ^ 2) +
        ((2 ^ (f + 3) : ℤ) : ℤ[X]) * (Q * (X ^ 1 + X ^ 2) + (1 + 2 * Q) * R) := by
    rw [pow_add, hR, hQ]
    push_cast
    ring
  have hF : (2 : ℤ) ^ (f + 3) ∣
      (∑ m ∈ range (n + 2 ^ (f + 1) + 1), ((n + 2 ^ (f + 1)).choose m : ℤ) * 2 ^ m * A1 m) -
        ∑ m ∈ range (n + 1), (n.choose m : ℤ) * 2 ^ m * A1 m := by
    have hN1 : n + 2 ^ (f + 1) < n + 2 ^ (f + 1) + 3 := Nat.lt_add_of_pos_right (by norm_num)
    have hN0 : n < n + 2 ^ (f + 1) + 3 := lt_of_le_of_lt (Nat.le_add_right n _) hN1
    have hN3 : 3 ≤ n + 2 ^ (f + 1) + 3 := Nat.le_add_left 3 _
    rw [← Phi_F A1 (n + 2 ^ (f + 1) + 3) (n + 2 ^ (f + 1)) hN1,
      ← Phi_F A1 (n + 2 ^ (f + 1) + 3) n hN0, ← map_sub, hdiff, map_add, Phi_intCast_mul,
      Phi_intCast_mul, map_add (Phi A1 (n + 2 ^ (f + 1) + 3)) (X ^ 1) (X ^ 2),
      Phi_X_pow A1 (n + 2 ^ (f + 1) + 3) 1 (lt_of_lt_of_le (by norm_num) hN3),
      Phi_X_pow A1 (n + 2 ^ (f + 1) + 3) 2 (lt_of_lt_of_le (by norm_num) hN3), hc]
    exact ⟨c + Phi A1 (n + 2 ^ (f + 1) + 3) (Q * (X ^ 1 + X ^ 2) + (1 + 2 * Q) * R), by ring⟩
  have hpow : (2 : ℤ) ^ (f + 3) ∣ 2 ^ (n + 2 ^ (f + 1)) * A0 (n + 2 ^ (f + 1)) - 2 ^ n * A0 n :=
    dvd_sub (dvd_mul_of_dvd_left (pow_dvd_pow 2 (le_trans hn (Nat.le_add_right n _))) _)
      (dvd_mul_of_dvd_left (pow_dvd_pow 2 hn) _)
  have h2 : (2 : ℤ) * 2 ^ (f + 2) ∣ 2 * (b (n + 2 ^ (f + 1)) - b n) := by
    have e : (2 : ℤ) * (b (n + 2 ^ (f + 1)) - b n) =
        (2 ^ (n + 2 ^ (f + 1)) * A0 (n + 2 ^ (f + 1)) - 2 ^ n * A0 n) +
          ((∑ m ∈ range (n + 2 ^ (f + 1) + 1), ((n + 2 ^ (f + 1)).choose m : ℤ) * 2 ^ m * A1 m) -
            ∑ m ∈ range (n + 1), (n.choose m : ℤ) * 2 ^ m * A1 m) := by
      rw [mul_sub, hb (n + 2 ^ (f + 1)), hb n]
      ring
    rw [e, show (2 : ℤ) * 2 ^ (f + 2) = 2 ^ (f + 3) by ring]
    exact dvd_add hpow hF
  exact (mul_dvd_mul_iff_left two_ne_zero).mp h2

end A370092Core
