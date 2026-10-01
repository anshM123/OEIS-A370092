import DMSolutions.OEIS_A370092.Statement
import DMSolutions.OEIS_A370092.Core

/-!
# Solution of `OeisA370092.bounds`

The statement is `OeisA370092.bounds` from `FormalConjectures/OEIS/370092.lean`
(formal-conjectures pull request 4946), included unmodified as `Statement.lean`. It is stated here
with the repository's own definitions `OeisA370092.a`, `OeisA370092.eventually_periodic` and
`OeisA370092.a_mod_k`, which agree with the copies in `A370092Core` by `rfl`.

The period can be taken to be `φ(k)` itself, from the index `k` on.
-/

open Finset Nat

namespace OeisA370092

/-- The repository's `a` is definitionally the copy `A370092Core.a`. Both are the same
well-founded definition; `with_unfolding_all` lets `rfl` unfold them. -/
theorem a_eq_core : a = A370092Core.a := by with_unfolding_all rfl

theorem eventually_periodic_eq_core :
    @eventually_periodic = @A370092Core.eventually_periodic := rfl

theorem a_mod_k_eq_core : a_mod_k = A370092Core.a_mod_k := by with_unfolding_all rfl

/-- `OeisA370092.bounds`, proved: for `k > 2` the reductions of `a(n)` modulo `k` are eventually
periodic with a period dividing `φ(k)`. -/
theorem bounds_solved (k : ℕ) (hk : 2 < k) :
    ∃ P : ℕ, P ∣ totient k ∧ eventually_periodic (a_mod_k k) P := by
  rw [a_mod_k_eq_core, eventually_periodic_eq_core]
  exact A370092Core.bounds_core k hk

end OeisA370092
