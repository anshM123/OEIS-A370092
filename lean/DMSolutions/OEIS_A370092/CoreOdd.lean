import DMSolutions.OEIS_A370092.CoreArith

/-!
# OEIS A370092: odd prime powers

For an odd prime `p` and `e ≤ n`: `p^e ∣ b(n + φ(p^e)) - b(n)` (`odd_prime_pow`).

By `two_b_eq_V`, `2 (b(n + φ) - b(n)) = ∑_{k ≤ n + φ} θ_k (VZ (n + φ) k - VZ n k)`. Each
`VZ (n + φ) k - VZ n k` is an integer combination of the numbers `t^(n + φ) - t^n`, which are
divisible by `p^e` (Euler's theorem when `p ∤ t`; `e ≤ n` when `p ∣ t`). Each `θ_k` has a
power of `2` as denominator. So `2^N (b(n + φ) - b(n))` is divisible by `p^e` for some `N`,
and `p` is odd.
-/

open Finset Nat

namespace A370092Core

/-- Euler: `p^e ∣ t^(n + φ(p^e)) - t^n` for `e ≤ n`. -/
theorem euler_diff (p e n t : ℕ) (hp : p.Prime) (hn : e ≤ n) :
    (p : ℤ) ^ e ∣ (t : ℤ) ^ (n + φ (p ^ e)) - (t : ℤ) ^ n := by
  by_cases hpt : p ∣ t
  · have h1 : p ^ e ∣ t ^ n := (pow_dvd_pow_of_dvd hpt e).trans (pow_dvd_pow t hn)
    have h2 : p ^ e ∣ t ^ (n + φ (p ^ e)) := h1.trans (pow_dvd_pow t (Nat.le_add_right n _))
    exact dvd_sub (by exact_mod_cast h2) (by exact_mod_cast h1)
  · have hcop : Nat.Coprime t (p ^ e) :=
      Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpt).symm
    have h3 : t ^ n * t ^ φ (p ^ e) ≡ t ^ n * 1 [MOD p ^ e] :=
      Nat.ModEq.mul_left _ (Nat.ModEq.pow_totient hcop)
    rw [mul_one, ← pow_add] at h3
    have h4 := Nat.modEq_iff_dvd.mp h3.symm
    exact_mod_cast h4

theorem UZ_diff (p e n : ℕ) (hp : p.Prime) (hn : e ≤ n) (c j : ℕ) :
    (p : ℤ) ^ e ∣ UZ (c : ℤ) (n + φ (p ^ e)) j - UZ (c : ℤ) n j := by
  rw [UZ, UZ, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun i _ => ?_
  rw [← mul_sub]
  have h := euler_diff p e n (2 * i + c) hp hn
  push_cast at h
  exact dvd_mul_of_dvd_right h _

theorem VZ_diff (p e n : ℕ) (hp : p.Prime) (hn : e ≤ n) (k : ℕ) :
    (p : ℤ) ^ e ∣ VZ (n + φ (p ^ e)) k - VZ n k := by
  have h0 := UZ_diff p e n hp hn 0
  have h1 := UZ_diff p e n hp hn 1
  simp only [Nat.cast_zero, Nat.cast_one] at h0 h1
  have e : VZ (n + φ (p ^ e)) k - VZ n k =
      (UZ 0 (n + φ (p ^ e)) (k + 1) - UZ 0 n (k + 1)) +
        (UZ 0 (n + φ (p ^ e)) (k + 2) - UZ 0 n (k + 2)) +
          2 * (UZ 1 (n + φ (p ^ e)) k - UZ 1 n k) +
            (UZ 1 (n + φ (p ^ e)) (k + 1) - UZ 1 n (k + 1)) := by
    unfold VZ
    ring
  rw [e]
  exact dvd_add (dvd_add (dvd_add (h0 _) (h0 _)) (dvd_mul_of_dvd_right (h1 _) _)) (h1 _)

/-- `x ∈ q ℤ[1/2]`. -/
def Good (q : ℤ) (x : ℚ) : Prop := ∃ N : ℕ, ∃ z : ℤ, (2 : ℚ) ^ N * x = q * z

theorem Good.add {q : ℤ} {x y : ℚ} (hx : Good q x) (hy : Good q y) : Good q (x + y) := by
  obtain ⟨N1, z1, h1⟩ := hx
  obtain ⟨N2, z2, h2⟩ := hy
  refine ⟨N1 + N2, 2 ^ N2 * z1 + 2 ^ N1 * z2, ?_⟩
  push_cast
  calc (2 : ℚ) ^ (N1 + N2) * (x + y) = 2 ^ N2 * (2 ^ N1 * x) + 2 ^ N1 * (2 ^ N2 * y) := by ring
    _ = _ := by rw [h1, h2]; ring

theorem Good.sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (q : ℤ) (h : ∀ i ∈ s, Good q (f i)) :
    Good q (∑ i ∈ s, f i) :=
  Finset.sum_induction f (Good q) (fun _ _ hx hy => hx.add hy) ⟨0, 0, by simp⟩ h

theorem good_th_mul (q : ℤ) (k : ℕ) (w : ℤ) (hw : q ∣ w) : Good q (th (k + 2) * (w : ℚ)) := by
  obtain ⟨z, hz⟩ := th_int k
  obtain ⟨v, rfl⟩ := hw
  refine ⟨2 * (k / 3), z * v, ?_⟩
  rw [pow_mul, show ((2 : ℚ) ^ 2) = 4 by norm_num]
  push_cast
  calc (4 : ℚ) ^ (k / 3) * (th (k + 2) * (q * v)) = (4 ^ (k / 3) * th (k + 2)) * (q * v) := by
        ring
    _ = q * (z * v) := by rw [hz]; ring

/-- **Odd prime powers.** For an odd prime `p` and `e ≤ n`, `p^e ∣ b(n + φ(p^e)) - b(n)`. -/
theorem odd_prime_pow (p e n : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hn : e ≤ n) :
    (p : ℤ) ^ e ∣ b (n + φ (p ^ e)) - b n := by
  have hK : 2 * ((b (n + φ (p ^ e)) : ℚ) - b n) = ∑ k ∈ range (n + φ (p ^ e) + 1),
      th (k + 2) * ((VZ (n + φ (p ^ e)) k - VZ n k : ℤ) : ℚ) := by
    have h1 := two_b_eq_V (n + φ (p ^ e)) (n + φ (p ^ e)) le_rfl
    have h2 := two_b_eq_V n (n + φ (p ^ e)) (Nat.le_add_right n _)
    rw [mul_sub, h1, h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  have hG : Good ((p : ℤ) ^ e) (2 * ((b (n + φ (p ^ e)) : ℚ) - b n)) := by
    rw [hK]
    exact Good.sum _ _ _ fun k _ => good_th_mul _ k _ (VZ_diff p e n hp hn k)
  obtain ⟨N, z, hz⟩ := hG
  have hz' : (2 : ℤ) ^ (N + 1) * (b (n + φ (p ^ e)) - b n) = (p : ℤ) ^ e * z := by
    have h : ((2 ^ (N + 1) * (b (n + φ (p ^ e)) - b n) : ℤ) : ℚ) = (((p : ℤ) ^ e * z : ℤ) : ℚ) := by
      push_cast at hz ⊢
      linear_combination hz
    exact_mod_cast h
  have hcop : IsCoprime ((p : ℤ) ^ e) ((2 : ℤ) ^ (N + 1)) := by
    have h := Nat.isCoprime_iff_coprime.mpr
      (Nat.Coprime.pow e (N + 1) ((Nat.coprime_primes hp Nat.prime_two).mpr hp2))
    exact_mod_cast h
  exact hcop.dvd_of_dvd_mul_left ⟨z, hz'⟩

end A370092Core
