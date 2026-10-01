import Mathlib

/-!
# OEIS A370092: the definitions and the recurrence

This file contains verbatim copies of `OeisA370092.a`, `OeisA370092.eventually_periodic` and
`OeisA370092.a_mod_k` from `FormalConjectures/OEIS/370092.lean` (formal-conjectures pull
request 4946). It also proves two facts about the recurrence.

* `rec_of_conv`: the convolution form
  `∑_{j ≤ n} C(n, j) ε_j b(n - j) = 2 (-1)^n`, with `ε_0 = 2` and `ε_j = (-1)^j + (-2)^j - 1`
  for `j ≥ 1`, implies the recurrence of `a`.
* `a_eq_of_rec`: the recurrence determines `a`.
-/

open Finset Nat

namespace A370092Core

/--
$a(0) = 1$, and $a(n) = (-1)^n + \frac{1}{2} \sum_{j=1}^n (1 - (-1)^j - (-2)^j) \binom{n}{j}
a(n-j)$ for $n > 0$.
-/
noncomputable def a (n : ℕ) : ℚ :=
  match n with
  | 0 => 1
  | m_plus_one@(m + 1) =>
    -- The sum is over j from 1 to m_plus_one. k runs from 0 to m.
    let sum_val : ℚ := ∑ k ∈ range m_plus_one,
      let j : ℕ := k + 1 -- j is the index for the sum

      let a_term : ℚ := a (m_plus_one - j)
      let coeff_factor : ℚ := 1 - (-1 : ℚ)^j - (-2 : ℚ)^j

      (m_plus_one.choose j : ℚ) * coeff_factor * a_term
    (-1 : ℚ)^m_plus_one + (1 / 2) * sum_val

/--
A sequence `f` is eventually periodic with period `P` if after some index `N`, `f(n + P) = f(n)`.
-/
def eventually_periodic {α : Type*} (f : ℕ → α) (P : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f (n + P) = f n

/--
The reduction of `a n` modulo `k`. Since all terms of `a n` are integers, we take the
numerator of the rational number representation, which is the integer value, and reduce it
modulo `k`.
This requires `k > 0`, which is guaranteed by `2 < k`.
-/
noncomputable def a_mod_k (k : ℕ) (n : ℕ) : ZMod k :=
  Int.cast (a n).num

theorem a_zero : a 0 = 1 := by rw [a]

theorem a_succ (m : ℕ) : a (m + 1) = (-1 : ℚ) ^ (m + 1) + (1 / 2) * ∑ k ∈ range (m + 1),
    ((m + 1).choose (k + 1) : ℚ) * (1 - (-1 : ℚ) ^ (k + 1) - (-2 : ℚ) ^ (k + 1)) * a (m - k) := by
  rw [a]
  simp only [Nat.succ_eq_add_one, Nat.add_sub_add_right]

/-- The convolution weights: `eps 0 = 2` and `eps j = (-1)^j + (-2)^j - 1` for `j ≥ 1`. -/
def eps (j : ℕ) : ℚ := (if j = 0 then 1 else 0) + (-1 : ℚ) ^ j + (-2 : ℚ) ^ j - 1 ^ j

theorem eps_zero : eps 0 = 2 := by norm_num [eps]

/-- The convolution identity at `m + 1` gives the recurrence of `a` at `m + 1`. -/
theorem rec_of_conv (b : ℕ → ℚ) (m : ℕ)
    (h : ∑ j ∈ range (m + 2), ((m + 1).choose j : ℚ) * eps j * b (m + 1 - j) =
      2 * (-1 : ℚ) ^ (m + 1)) :
    b (m + 1) = (-1 : ℚ) ^ (m + 1) + (1 / 2) * ∑ k ∈ range (m + 1),
      ((m + 1).choose (k + 1) : ℚ) * (1 - (-1 : ℚ) ^ (k + 1) - (-2 : ℚ) ^ (k + 1)) * b (m - k) := by
  rw [Finset.sum_range_succ'] at h
  have key : ∑ k ∈ range (m + 1), ((m + 1).choose (k + 1) : ℚ) * eps (k + 1) * b (m + 1 - (k + 1))
      = -∑ k ∈ range (m + 1),
          ((m + 1).choose (k + 1) : ℚ) * (1 - (-1 : ℚ) ^ (k + 1) - (-2 : ℚ) ^ (k + 1)) * b (m - k) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.add_sub_add_right]
    simp only [eps, Nat.add_one_ne_zero, if_false, one_pow]
    ring
  rw [key, eps_zero, Nat.choose_zero_right, Nat.sub_zero] at h
  push_cast at h
  linarith

/-- Uniqueness: a sequence with `b 0 = 1` that satisfies the recurrence of `a` up to `K`
agrees with `a` up to `K`. -/
theorem a_eq_of_rec (b : ℕ → ℚ) (K : ℕ) (h0 : b 0 = 1)
    (hs : ∀ m, m + 1 ≤ K → b (m + 1) = (-1 : ℚ) ^ (m + 1) + (1 / 2) * ∑ k ∈ range (m + 1),
      ((m + 1).choose (k + 1) : ℚ) * (1 - (-1 : ℚ) ^ (k + 1) - (-2 : ℚ) ^ (k + 1)) * b (m - k)) :
    ∀ n, n ≤ K → a n = b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases n with _ | m
    · rw [a_zero, h0]
    · rw [a_succ, hs m hn]
      congr 2
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < m + 1 := Finset.mem_range.mp hk
      rw [ih (m - k) (by omega) (by omega)]

end A370092Core
