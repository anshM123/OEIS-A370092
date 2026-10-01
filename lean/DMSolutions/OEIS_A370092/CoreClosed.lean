import DMSolutions.OEIS_A370092.CoreDefs

/-!
# OEIS A370092: a closed formula for `a`

Let `Δ f (x) = f (x + 1) - f x` act on functions `ℚ → ℚ`, and write `D k f = (Δ^k f)(0)`.
Put `pw c n x = (2x + c)^n`, and let `th (k + 2) = θ_k`, where `θ_0 = 1` and
`θ_k = -θ_{k-1} + θ_{k-3}/4`, so that `(4 + 4w - w^3) ∑ θ_k w^k = 4`.

Main result (`two_a_eq_E`): for all `n ≤ K`,

  `2 a(n) = ∑_{k ≤ K} θ_k (D (k+1) (pw 0 n) + D (k+2) (pw 0 n) + 2 D k (pw 1 n) + D (k+1) (pw 1 n))`.

This is the 2-section formula `A(x) = M_0(2x) + e^x M_1(2x)` with the Stirling expansions of
`M_0, M_1` in `w = e^y - 1`, written with finite differences. The right side satisfies the
convolution form of the recurrence. By linearity this comes down to the pointwise identity
`key_k` and the telescoping identity `telescope`. Uniqueness of the recurrence then gives the
formula.
-/

open Finset Nat

namespace A370092Core

/-- `th j = θ_{j-2}`: `th 0 = th 1 = 0`, `th 2 = 1`, `th (j + 3) = -th (j + 2) + th j / 4`. -/
def th : ℕ → ℚ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | (j + 3) => -th (j + 2) + th j / 4

/-- `D k f = (Δ^k f)(0)`, the `k`-th forward difference (step `1`) of `f` at `0`. -/
def D (k : ℕ) (f : ℚ → ℚ) : ℚ := (fwdDiff (1 : ℚ))^[k] f 0

theorem D_add (k : ℕ) (f g : ℚ → ℚ) : D k (f + g) = D k f + D k g := by
  simp only [D, fwdDiff_iter_add, Pi.add_apply]

theorem D_smul (k : ℕ) (c : ℚ) (f : ℚ → ℚ) : D k (c • f) = c * D k f := by
  simp only [D, fwdDiff_iter_const_smul, Pi.smul_apply, smul_eq_mul]

theorem D_sum {ι : Type*} (s : Finset ι) (k : ℕ) (f : ι → ℚ → ℚ) :
    D k (∑ i ∈ s, f i) = ∑ i ∈ s, D k (f i) := by
  simp only [D, fwdDiff_iter_finsetSum, Finset.sum_apply]

theorem D_fwdDiff (k : ℕ) (f : ℚ → ℚ) : D k (fwdDiff 1 f) = D (k + 1) f := by
  simp only [D, Function.iterate_succ_apply]

theorem D_eq_sum (k : ℕ) (f : ℚ → ℚ) :
    D k f = ∑ i ∈ range (k + 1), (-1 : ℚ) ^ (k - i) * (k.choose i : ℚ) * f i := by
  rw [D, fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [zsmul_eq_mul]

/-- The functions `x ↦ (2x + c)^n`. -/
def pw (c : ℚ) (n : ℕ) : ℚ → ℚ := fun x => (2 * x + c) ^ n

theorem D_pw_eq_zero (c : ℚ) (n j : ℕ) (h : n < j) : D j (pw c n) = 0 := by
  have hlin : (Polynomial.C (2 : ℚ) * Polynomial.X + Polynomial.C c).natDegree ≤ 1 :=
    Polynomial.natDegree_linear_le
  have hdeg : ((Polynomial.C (2 : ℚ) * Polynomial.X + Polynomial.C c) ^ n).natDegree < j := by
    refine lt_of_le_of_lt (Polynomial.natDegree_pow_le.trans ?_) h
    calc n * (Polynomial.C (2 : ℚ) * Polynomial.X + Polynomial.C c).natDegree ≤ n * 1 :=
          Nat.mul_le_mul_left n hlin
      _ = n := mul_one n
  have h2 := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg
  have hf : pw c n = fun x =>
      ((Polynomial.C (2 : ℚ) * Polynomial.X + Polynomial.C c) ^ n).eval x := by
    funext x
    simp [pw]
  rw [D, hf, h2]
  rfl

/-- Telescoping for `θ`: the identity `(4 + 4w - w^3) ∑_{k ≤ K} θ_k w^k ≡ 4 (mod w^{K+1})`
applied to a sequence `d`. -/
theorem telescope (d : ℕ → ℚ) (K : ℕ) :
    ∑ k ∈ range (K + 1), th (k + 2) * (4 * d k + 4 * d (k + 1) - d (k + 3)) =
      4 * d 0 + (4 * th (K + 2) - th K) * d (K + 1) - th (K + 1) * d (K + 2)
        - th (K + 2) * d (K + 3) := by
  induction K with
  | zero => norm_num [Finset.sum_range_one, th]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    have e : th (K + 1 + 2) = -th (K + 2) + th K / 4 := rfl
    rw [e]
    simp only [show K + 1 + 1 = K + 2 from rfl, show K + 1 + 2 = K + 3 from rfl,
      show K + 1 + 3 = K + 4 from rfl]
    ring

/-- `hh n t = t^n + (t-1)^n + (t-2)^n - (t+1)^n`. -/
def hh (n : ℕ) (t : ℚ) : ℚ := t ^ n + (t - 1) ^ n + (t - 2) ^ n - (t + 1) ^ n

/-- The binomial form of the weights `eps`. -/
theorem conv_pow (n : ℕ) (t : ℚ) :
    ∑ j ∈ range (n + 1), ((n.choose j : ℚ) * eps j) * t ^ (n - j) = hh n t := by
  have h1 : ∀ c : ℚ, ∑ j ∈ range (n + 1), (n.choose j : ℚ) * c ^ j * t ^ (n - j) =
      (t + c) ^ n := by
    intro c
    rw [add_comm t c, add_pow]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h0 : ∑ j ∈ range (n + 1), (n.choose j : ℚ) * (if j = 0 then 1 else 0) * t ^ (n - j) =
      t ^ n := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      simp at h
  calc ∑ j ∈ range (n + 1), ((n.choose j : ℚ) * eps j) * t ^ (n - j)
      = ∑ j ∈ range (n + 1), ((n.choose j : ℚ) * (if j = 0 then 1 else 0) * t ^ (n - j)
          + (n.choose j : ℚ) * (-1) ^ j * t ^ (n - j) + (n.choose j : ℚ) * (-2) ^ j * t ^ (n - j)
          - (n.choose j : ℚ) * 1 ^ j * t ^ (n - j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [eps]
        ring
    _ = hh n t := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, h0, h1, h1, h1]
        simp only [hh]
        ring

/-- The candidate functional: `E K g0 g1 = ∑_{k ≤ K} θ_k (D (k+1) g0 + D (k+2) g0 + 2 D k g1 +
D (k+1) g1)`. -/
def E (K : ℕ) (g0 g1 : ℚ → ℚ) : ℚ :=
  ∑ k ∈ range (K + 1), th (k + 2) * (D (k + 1) g0 + D (k + 2) g0 + 2 * D k g1 + D (k + 1) g1)

theorem E_add (K : ℕ) (f0 f1 g0 g1 : ℚ → ℚ) :
    E K (f0 + g0) (f1 + g1) = E K f0 f1 + E K g0 g1 := by
  simp only [E, D_add, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem E_smul (K : ℕ) (c : ℚ) (f0 f1 : ℚ → ℚ) : E K (c • f0) (c • f1) = c * E K f0 f1 := by
  simp only [E, D_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem E_zero (K : ℕ) : E K 0 0 = 0 := by
  simpa using E_smul K 0 0 0

theorem E_sum {ι : Type*} (K : ℕ) (s : Finset ι) (c : ι → ℚ) (g0 g1 : ι → ℚ → ℚ) :
    E K (∑ i ∈ s, c i • g0 i) (∑ i ∈ s, c i • g1 i) = ∑ i ∈ s, c i * E K (g0 i) (g1 i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [E_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi, E_add, E_smul, ih]

/-- The pointwise identity behind the 2-section:
`(S² - S) h(2·) + (1 + S) h(2·+1) = (4 + 4Δ - Δ³) F` with `F x = (2x - 1)^n`. -/
theorem key_k (n k : ℕ) :
    D (k + 1) (fun x => hh n (2 * x + 0)) + D (k + 2) (fun x => hh n (2 * x + 0)) +
        2 * D k (fun x => hh n (2 * x + 1)) + D (k + 1) (fun x => hh n (2 * x + 1)) =
      4 * D k (pw (-1) n) + 4 * D (k + 1) (pw (-1) n) - D (k + 3) (pw (-1) n) := by
  have hG : fwdDiff 1 (fun x => hh n (2 * x + 0)) + fwdDiff 1 (fwdDiff 1 (fun x => hh n (2 * x + 0)))
      + (2 : ℚ) • (fun x => hh n (2 * x + 1)) + fwdDiff 1 (fun x => hh n (2 * x + 1)) =
      (4 : ℚ) • pw (-1) n + (4 : ℚ) • fwdDiff 1 (pw (-1) n)
        + (-1 : ℚ) • fwdDiff 1 (fwdDiff 1 (fwdDiff 1 (pw (-1) n))) := by
    funext x
    simp only [fwdDiff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hh, pw]
    ring
  have h2 := congrArg (D k) hG
  simp only [D_add, D_smul, D_fwdDiff] at h2
  rw [show k + 1 + 1 = k + 2 from rfl, show k + 2 + 1 = k + 3 from rfl] at h2
  linarith

theorem E_key (K n : ℕ) :
    E K (fun x => hh n (2 * x + 0)) (fun x => hh n (2 * x + 1)) =
      ∑ k ∈ range (K + 1), th (k + 2) *
        (4 * D k (pw (-1) n) + 4 * D (k + 1) (pw (-1) n) - D (k + 3) (pw (-1) n)) := by
  unfold E
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [key_k]

/-- The candidate for `a n`. -/
def cf (K n : ℕ) : ℚ := (1 / 2) * E K (pw 0 n) (pw 1 n)

/-- The candidate satisfies the convolution form of the recurrence up to `K`. -/
theorem conv_cf (K n : ℕ) (hn : n ≤ K) :
    ∑ j ∈ range (n + 1), (n.choose j : ℚ) * eps j * cf K (n - j) = 2 * (-1 : ℚ) ^ n := by
  have step1 : ∑ j ∈ range (n + 1), (n.choose j : ℚ) * eps j * cf K (n - j) =
      (1 / 2) * E K (∑ j ∈ range (n + 1), ((n.choose j : ℚ) * eps j) • pw 0 (n - j))
        (∑ j ∈ range (n + 1), ((n.choose j : ℚ) * eps j) • pw 1 (n - j)) := by
    rw [E_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [cf]; ring
  have step2 : ∀ c : ℚ, (∑ j ∈ range (n + 1), ((n.choose j : ℚ) * eps j) • pw c (n - j)) =
      fun x => hh n (2 * x + c) := by
    intro c
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pw]
    exact conv_pow n (2 * x + c)
  rw [step1, step2, step2, E_key, telescope, D_pw_eq_zero (-1) n (K + 1) (by omega),
    D_pw_eq_zero (-1) n (K + 2) (by omega), D_pw_eq_zero (-1) n (K + 3) (by omega)]
  simp only [D, Function.iterate_zero, id_eq, pw]
  ring

theorem cf_zero (K : ℕ) : cf K 0 = 1 := by
  have h := conv_cf K 0 (Nat.zero_le K)
  norm_num [eps_zero] at h
  linarith

theorem a_eq_cf (K n : ℕ) (hn : n ≤ K) : a n = cf K n :=
  a_eq_of_rec (cf K) K (cf_zero K) (fun m hm => rec_of_conv (cf K) m (conv_cf K (m + 1) hm)) n hn

/-- **Closed formula.** For `n ≤ K`, `2 a(n) = E K (pw 0 n) (pw 1 n)`. -/
theorem two_a_eq_E (n K : ℕ) (hn : n ≤ K) : 2 * a n = E K (pw 0 n) (pw 1 n) := by
  rw [a_eq_cf K n hn, cf]
  ring

end A370092Core
