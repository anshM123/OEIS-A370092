import DMSolutions.OEIS_A370092.CoreClosed

/-!
# OEIS A370092: integrality

* `TZ m k = Δ^k (x ↦ x^m) (0) = k! S(m, k)` is divisible by `k!` (`fact_dvd_TZ`).
* `4^⌊k/3⌋ θ_k` is an integer (`th_int`), `4^⌊k/3⌋ ∣ 2 k!` and `4^⌊k/3⌋ ∣ (k+1)!`
  (from Legendre's formula).
* Hence `A0 n = ∑_{k ≤ n} θ_k (TZ n (k+1) + TZ n (k+2))` and
  `A1 m = ∑_{k ≤ m} θ_k (2 TZ m k + TZ m (k+1))` are integers. The closed formula gives
  `2 a(n) = 2^n A0(n) + ∑_m C(n, m) 2^m A1(m)` (`two_a_eq_A`), so `a(n)` is an integer `b n`.
* `two_b_eq_V`: the same closed formula with explicit integer sums, for the odd primes.
-/

open Finset Nat

namespace A370092Core

/-! ### The numbers `TZ m k = k! S(m, k)` -/

/-- `TZ m k = Δ^k (x ↦ x^m) (0)` over `ℤ`. -/
def TZ (m k : ℕ) : ℤ := (fwdDiff (1 : ℤ))^[k] (fun x : ℤ => x ^ m) 0

theorem TZ_eq_sum (m k : ℕ) :
    TZ m k = ∑ i ∈ range (k + 1), (-1 : ℤ) ^ (k - i) * (k.choose i : ℤ) * (i : ℤ) ^ m := by
  rw [TZ, fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem D_pow_eq_TZ (m k : ℕ) : D k (fun x : ℚ => x ^ m) = (TZ m k : ℚ) := by
  rw [D_eq_sum, TZ_eq_sum]
  push_cast
  rfl

theorem TZ_eq_zero (m k : ℕ) (h : m < k) : TZ m k = 0 := by
  rw [TZ, fwdDiff_iter_pow_eq_zero_of_lt h]
  rfl

theorem TZ_succ_succ (m k : ℕ) :
    TZ (m + 1) (k + 1) = ((k : ℤ) + 1) * (TZ m k + TZ m (k + 1)) := by
  have h1 : TZ m k + TZ m (k + 1) = (fwdDiff (1 : ℤ))^[k] (fun x : ℤ => x ^ m) 1 := by
    simp only [TZ, Function.iterate_succ_apply', fwdDiff, zero_add]
    ring
  have h2 : (fwdDiff (1 : ℤ))^[k] (fun x : ℤ => x ^ m) 1 =
      ∑ i ∈ range (k + 1), (-1 : ℤ) ^ (k - i) * (k.choose i : ℤ) * ((1 : ℤ) + i) ^ m := by
    rw [fwdDiff_iter_eq_sum_shift]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  have h3 : TZ (m + 1) (k + 1) = ((k : ℤ) + 1) *
      ∑ i ∈ range (k + 1), (-1 : ℤ) ^ (k - i) * (k.choose i : ℤ) * ((1 : ℤ) + i) ^ m := by
    rw [TZ_eq_sum, Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.cast_zero, ne_eq, Nat.add_one_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : ((k + 1).choose (i + 1) : ℤ) * ((i : ℤ) + 1) = ((k : ℤ) + 1) * (k.choose i : ℤ) := by
      exact_mod_cast (Nat.add_one_mul_choose_eq k i).symm
    rw [Nat.add_sub_add_right]
    push_cast
    linear_combination ((-1 : ℤ) ^ (k - i) * ((1 : ℤ) + i) ^ m) * hc
  rw [h3, h1, h2]

theorem fact_dvd_TZ (m k : ℕ) : (k ! : ℤ) ∣ TZ m k := by
  induction m generalizing k with
  | zero =>
    rcases k with _ | k
    · simp
    · rw [TZ_eq_zero 0 (k + 1) (Nat.succ_pos k)]
      exact dvd_zero _
  | succ m ih =>
    rcases k with _ | k
    · simp
    · rw [TZ_succ_succ, Nat.factorial_succ]
      push_cast
      refine mul_dvd_mul_left _ (dvd_add (ih k) ?_)
      exact (Int.natCast_dvd_natCast.mpr (Nat.factorial_dvd_factorial (Nat.le_succ k))).trans
        (ih (k + 1))

/-! ### Powers of `2` in factorials -/

theorem two_pow_dvd_fact (k : ℕ) : 2 ^ (k / 2 + k / 4) ∣ k ! := by
  rw [Nat.prime_two.pow_dvd_factorial_iff (show Nat.log 2 k < Nat.log 2 k + 3 by omega)]
  calc k / 2 + k / 4 = ∑ i ∈ ({1, 2} : Finset ℕ), k / 2 ^ i := by simp
    _ ≤ ∑ i ∈ Ico 1 (Nat.log 2 k + 3), k / 2 ^ i := by
      refine Finset.sum_le_sum_of_subset fun i hi => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      simp only [Finset.mem_Ico]
      omega

theorem four_pow_eq (k : ℕ) : (4 : ℕ) ^ (k / 3) = 2 ^ (2 * (k / 3)) := by
  rw [pow_mul]
  norm_num

theorem four_pow_dvd_two_mul_fact (k : ℕ) : 4 ^ (k / 3) ∣ 2 * k ! := by
  rw [four_pow_eq]
  refine (Nat.pow_dvd_pow 2 (show 2 * (k / 3) ≤ 1 + (k / 2 + k / 4) by omega)).trans ?_
  rw [pow_add, pow_one]
  exact Nat.mul_dvd_mul_left 2 (two_pow_dvd_fact k)

theorem four_pow_dvd_fact_succ (k : ℕ) : 4 ^ (k / 3) ∣ (k + 1) ! := by
  rw [four_pow_eq]
  exact (Nat.pow_dvd_pow 2 (show 2 * (k / 3) ≤ (k + 1) / 2 + (k + 1) / 4 by omega)).trans
    (two_pow_dvd_fact (k + 1))

/-! ### `4^⌊k/3⌋ θ_k` is an integer -/

theorem th_int (k : ℕ) : ∃ z : ℤ, (4 : ℚ) ^ (k / 3) * th (k + 2) = z := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | _ | k
    · exact ⟨1, by norm_num [th]⟩
    · exact ⟨-1, by norm_num [th]⟩
    · exact ⟨1, by norm_num [th]⟩
    · show ∃ z : ℤ, (4 : ℚ) ^ ((k + 3) / 3) * th (k + 3 + 2) = z
      obtain ⟨z1, hz1⟩ := ih (k + 2) (by omega)
      obtain ⟨z2, hz2⟩ := ih k (by omega)
      have e : th (k + 3 + 2) = -th (k + 2 + 2) + th (k + 2) / 4 := rfl
      have e1 : (k + 3) / 3 = k / 3 + 1 := by omega
      rw [e, e1]
      rcases Nat.lt_or_ge (k % 3) 1 with h | h
      · have e2 : (k + 2) / 3 = k / 3 := by omega
        rw [e2] at hz1
        refine ⟨-(4 * z1) + z2, ?_⟩
        push_cast
        rw [← hz1, ← hz2]
        ring
      · have e2 : (k + 2) / 3 = k / 3 + 1 := by omega
        rw [e2] at hz1
        refine ⟨-z1 + z2, ?_⟩
        push_cast
        rw [← hz1, ← hz2]
        ring

/-! ### Integer-valued rationals -/

/-- `x` is (the image of) an integer. -/
def IsInt (x : ℚ) : Prop := ∃ z : ℤ, (z : ℚ) = x

theorem IsInt.add {x y : ℚ} (hx : IsInt x) (hy : IsInt y) : IsInt (x + y) := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  exact ⟨u + v, by push_cast; ring⟩

theorem IsInt.sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, IsInt (f i)) :
    IsInt (∑ i ∈ s, f i) :=
  Finset.sum_induction f IsInt (fun _ _ hx hy => hx.add hy) ⟨0, by simp⟩ h

theorem IsInt.num_cast {x : ℚ} (h : IsInt x) : ((x.num : ℤ) : ℚ) = x := by
  obtain ⟨z, rfl⟩ := h
  rw [Rat.num_intCast]

theorem isInt_th_mul (k : ℕ) (t : ℤ) (h : (4 : ℤ) ^ (k / 3) ∣ t) : IsInt (th (k + 2) * t) := by
  obtain ⟨z, hz⟩ := th_int k
  obtain ⟨q, rfl⟩ := h
  refine ⟨z * q, ?_⟩
  push_cast
  rw [← hz]
  ring

/-! ### The integer sequences `A0`, `A1` and the identity `2 a(n) = 2^n A0(n) + F(n)` -/

/-- `A1 m = 2 μ_1(m) = ∑_{k ≤ m} θ_k (2 TZ m k + TZ m (k+1))`. -/
def A1 (m : ℕ) : ℚ := ∑ k ∈ range (m + 1), th (k + 2) * ((2 * TZ m k + TZ m (k + 1) : ℤ) : ℚ)

/-- `A0 n = 2 μ_0(n) = ∑_{k ≤ n} θ_k (TZ n (k+1) + TZ n (k+2))`. -/
def A0 (n : ℕ) : ℚ := ∑ k ∈ range (n + 1), th (k + 2) * ((TZ n (k + 1) + TZ n (k + 2) : ℤ) : ℚ)

theorem four_pow_dvd_TZ_succ (m k : ℕ) : (4 : ℤ) ^ (k / 3) ∣ TZ m (k + 1) :=
  (by exact_mod_cast four_pow_dvd_fact_succ k : (4 : ℤ) ^ (k / 3) ∣ ((k + 1) ! : ℤ)).trans
    (fact_dvd_TZ m (k + 1))

theorem A1_isInt (m : ℕ) : IsInt (A1 m) := by
  refine IsInt.sum _ _ fun k _ => isInt_th_mul k _ (dvd_add ?_ (four_pow_dvd_TZ_succ m k))
  exact (by exact_mod_cast four_pow_dvd_two_mul_fact k : (4 : ℤ) ^ (k / 3) ∣ 2 * (k ! : ℤ)).trans
    (mul_dvd_mul_left 2 (fact_dvd_TZ m k))

theorem A0_isInt (n : ℕ) : IsInt (A0 n) := by
  refine IsInt.sum _ _ fun k _ => isInt_th_mul k _ (dvd_add (four_pow_dvd_TZ_succ n k) ?_)
  exact (by exact_mod_cast four_pow_dvd_fact_succ k : (4 : ℤ) ^ (k / 3) ∣ ((k + 1) ! : ℤ)).trans
    ((Int.natCast_dvd_natCast.mpr (Nat.factorial_dvd_factorial (Nat.le_succ (k + 1)))).trans
      (fact_dvd_TZ n (k + 2)))

theorem D_pw0 (n j : ℕ) : D j (pw 0 n) = 2 ^ n * (TZ n j : ℚ) := by
  have h : pw 0 n = (2 ^ n : ℚ) • (fun x : ℚ => x ^ n) := by
    funext x
    simp [pw, mul_pow]
  rw [h, D_smul, D_pow_eq_TZ]

theorem D_pw1 (n j : ℕ) :
    D j (pw 1 n) = ∑ m ∈ range (n + 1), (n.choose m : ℚ) * 2 ^ m * (TZ m j : ℚ) := by
  have h : pw 1 n = ∑ m ∈ range (n + 1), ((n.choose m : ℚ) * 2 ^ m) • (fun x : ℚ => x ^ m) := by
    funext x
    simp only [pw, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [add_pow]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [h, D_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [D_smul, D_pow_eq_TZ]

theorem two_a_eq_A (n : ℕ) :
    2 * a n = 2 ^ n * A0 n + ∑ m ∈ range (n + 1), (n.choose m : ℚ) * 2 ^ m * A1 m := by
  have hA1 : ∀ m ∈ range (n + 1), A1 m =
      ∑ k ∈ range (n + 1), th (k + 2) * (2 * (TZ m k : ℚ) + TZ m (k + 1)) := by
    intro m hm
    have hm' : m < n + 1 := Finset.mem_range.mp hm
    rw [A1]
    push_cast
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro k hk hk'
    have h1 : m < k := by
      simp only [Finset.mem_range] at hk hk'
      omega
    rw [TZ_eq_zero m k h1, TZ_eq_zero m (k + 1) (by omega)]
    simp
  calc 2 * a n = E n (pw 0 n) (pw 1 n) := two_a_eq_E n n le_rfl
    _ = ∑ k ∈ range (n + 1), (2 ^ n * (th (k + 2) * ((TZ n (k + 1) : ℚ) + TZ n (k + 2))) +
          ∑ m ∈ range (n + 1), (n.choose m : ℚ) * 2 ^ m *
            (th (k + 2) * (2 * (TZ m k : ℚ) + TZ m (k + 1)))) := by
        unfold E
        refine Finset.sum_congr rfl fun k _ => ?_
        have e2 : ∑ m ∈ range (n + 1), (n.choose m : ℚ) * 2 ^ m *
              (th (k + 2) * (2 * (TZ m k : ℚ) + TZ m (k + 1))) =
            th (k + 2) * (2 * ∑ m ∈ range (n + 1), (n.choose m : ℚ) * 2 ^ m * (TZ m k : ℚ) +
              ∑ m ∈ range (n + 1), (n.choose m : ℚ) * 2 ^ m * (TZ m (k + 1) : ℚ)) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
          exact Finset.sum_congr rfl fun m _ => by ring
        rw [D_pw0, D_pw0, D_pw1, D_pw1, e2]
        ring
    _ = 2 ^ n * A0 n + ∑ m ∈ range (n + 1), (n.choose m : ℚ) * 2 ^ m * A1 m := by
        rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum]
        congr 1
        · simp only [A0, Int.cast_add]
        · refine Finset.sum_congr rfl fun m hm => ?_
          rw [hA1 m hm, Finset.mul_sum]

/-! ### `a n` is an integer -/

/-- The integer `A0 n`. -/
def A0Z (n : ℕ) : ℤ := (A0 n).num

/-- The integer `A1 m`. -/
def A1Z (m : ℕ) : ℤ := (A1 m).num

theorem A0Z_cast (n : ℕ) : (A0Z n : ℚ) = A0 n := (A0_isInt n).num_cast

theorem A1Z_cast (m : ℕ) : (A1Z m : ℚ) = A1 m := (A1_isInt m).num_cast

theorem two_a_eq_Z (n : ℕ) : 2 * a n =
    ((2 ^ n * A0Z n + ∑ m ∈ range (n + 1), (n.choose m : ℤ) * 2 ^ m * A1Z m : ℤ) : ℚ) := by
  rw [two_a_eq_A]
  push_cast
  simp only [A0Z_cast, A1Z_cast]

theorem th_two : th 2 = 1 := rfl

theorem th_three : th 3 = -1 := by norm_num [th]

theorem th_four : th 4 = 1 := by norm_num [th]

theorem A1_zero : A1 0 = 2 := by
  norm_num [A1, TZ_eq_sum, Finset.sum_range_succ, th_two]

theorem A1_one : A1 1 = -1 := by
  norm_num [A1, TZ_eq_sum, Finset.sum_range_succ, th_two, th_three]

theorem A1_two : A1 2 = 1 := by
  norm_num [A1, TZ_eq_sum, Finset.sum_range_succ, th_two, th_three, th_four]

theorem A1Z_zero : A1Z 0 = 2 := by exact_mod_cast (A1Z_cast 0).trans A1_zero

theorem A1Z_one : A1Z 1 = -1 := by exact_mod_cast (A1Z_cast 1).trans A1_one

theorem A1Z_two : A1Z 2 = 1 := by exact_mod_cast (A1Z_cast 2).trans A1_two

theorem a_isInt (n : ℕ) : IsInt (a n) := by
  rcases n with _ | n
  · exact ⟨1, by rw [a_zero]; simp⟩
  · have h := two_a_eq_Z (n + 1)
    have hs : ∑ m ∈ range (n + 1 + 1), ((n + 1).choose m : ℤ) * 2 ^ m * A1Z m =
        2 * (∑ m ∈ range (n + 1), ((n + 1).choose (m + 1) : ℤ) * 2 ^ m * A1Z (m + 1) + 1) := by
      rw [Finset.sum_range_succ', A1Z_zero, mul_add, Finset.mul_sum]
      simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul]
      congr 1
      · exact Finset.sum_congr rfl fun m _ => by ring
    refine ⟨2 ^ n * A0Z (n + 1) +
      (∑ m ∈ range (n + 1), ((n + 1).choose (m + 1) : ℤ) * 2 ^ m * A1Z (m + 1) + 1), ?_⟩
    rw [hs] at h
    push_cast at h ⊢
    linear_combination (-1 / 2 : ℚ) * h

/-- The integer value of `a n`; `a_mod_k k n` is its residue. -/
noncomputable def b (n : ℕ) : ℤ := (a n).num

theorem a_eq_b (n : ℕ) : a n = (b n : ℚ) := (a_isInt n).num_cast.symm

/-- The identity `2 a(n) = 2^n A0(n) + ∑_m C(n, m) 2^m A1(m)` in `ℤ`. -/
theorem two_b_eq_A (n : ℕ) :
    2 * b n = 2 ^ n * A0Z n + ∑ m ∈ range (n + 1), (n.choose m : ℤ) * 2 ^ m * A1Z m := by
  have h := two_a_eq_Z n
  rw [a_eq_b] at h
  exact_mod_cast h

theorem A1Z_one_add_two : A1Z 1 + A1Z 2 = 0 := by
  rw [A1Z_one, A1Z_two]
  norm_num

/-! ### Explicit integer sums, for the odd primes -/

/-- `UZ c n j = Δ^j (x ↦ (2x + c)^n) (0)`. -/
def UZ (c : ℤ) (n j : ℕ) : ℤ :=
  ∑ i ∈ range (j + 1), (-1 : ℤ) ^ (j - i) * (j.choose i : ℤ) * (2 * (i : ℤ) + c) ^ n

theorem D_pw_UZ (c : ℤ) (n j : ℕ) : D j (pw (c : ℚ) n) = (UZ c n j : ℚ) := by
  rw [D_eq_sum, UZ]
  push_cast
  rfl

/-- `VZ n k = UZ 0 n (k+1) + UZ 0 n (k+2) + 2 UZ 1 n k + UZ 1 n (k+1)`. -/
def VZ (n k : ℕ) : ℤ := UZ 0 n (k + 1) + UZ 0 n (k + 2) + 2 * UZ 1 n k + UZ 1 n (k + 1)

/-- The closed formula with explicit integer sums: for `n ≤ K`,
`2 a(n) = ∑_{k ≤ K} θ_k VZ n k`. -/
theorem two_b_eq_V (n K : ℕ) (hn : n ≤ K) :
    2 * (b n : ℚ) = ∑ k ∈ range (K + 1), th (k + 2) * (VZ n k : ℚ) := by
  rw [← a_eq_b, two_a_eq_E n K hn, E]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h0 : ∀ j, D j (pw 0 n) = (UZ 0 n j : ℚ) := fun j => by simpa using D_pw_UZ 0 n j
  have h1 : ∀ j, D j (pw 1 n) = (UZ 1 n j : ℚ) := fun j => by simpa using D_pw_UZ 1 n j
  rw [h0, h0, h1, h1, VZ]
  push_cast
  ring

end A370092Core
