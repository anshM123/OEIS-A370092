# OEIS A370092 modulo k has period dividing φ(k): a proof of Bala's conjecture

**Authors:** Ansh Mishra, Aryan Senthilkumar. **License:** MIT. **Paper:** [`paper/main.pdf`](paper/main.pdf)

[A370092](https://oeis.org/A370092) is defined by `a(0) = 1` and, for `n ≥ 1`,

```
a(n) = (−1)^n + (1/2) Σ_{j=1..n} (1 − (−1)^j − (−2)^j) C(n,j) a(n−j),
```

with e.g.f. `2e^x / (1 + e^x + e^{2x} − e^{3x})`. The sequence begins 1, 1, 3, 16, 105, …

In 2024 Peter Bala conjectured that for every `k > 2` the sequence `a(n) mod k` is eventually periodic with period
dividing `φ(k)`. Google DeepMind's [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) states
this as `OeisA370092.bounds` (`research open`), in pull request
[#4946](https://github.com/google-deepmind/formal-conjectures/pull/4946), file `FormalConjectures/OEIS/370092.lean`.

**This repository proves it, with a Lean 4 proof of the exact statement.**

## Result

**Theorem.**
1. `a(n)` is an integer for all `n`.
2. `a(n + φ(k)) ≡ a(n) (mod k)` for every `k ≥ 3` and every `n ≥ k`.
3. Modulo `2^e` (`e ≥ 2`) the eventual period is exactly `2^(e−1) = φ(2^e)`, and modulo 2 it is 2. So the conjecture
   is sharp at powers of 2 and genuinely needs `k > 2`.

- **Why the known general theorem does not apply.** Bala's general conjecture covers e.g.f.s `G(e^x − 1)` with integral `G`; that case is proved
  (arXiv:2609.07238, §2, and a Lean development in the-omega-institute/trureturing). Here
  `G(z) = (1+z)/(1 − z² − z³/2)` has 2-adic denominators about `2^{k/3}`, and the integral argument would give the
  wrong period `2^(e−2)` modulo `2^e`.
- **Key step: a 2-section in `e^x`.** `Q(u)Q(−u) = 1 + u² + 3u⁴ − u⁶` with `Q(u) = 1 + u + u² − u³`. It gives
  `A(x) = M_0(2x) + e^x M_1(2x)` and, after a Stirling expansion with half-integral coefficients, the integer identity
  `2a(n) = 2^n A_0(n) + Σ_m C(n,m) 2^m A_1(m)`.
- **The prime 2.** Modulo `2^e`, Vandermonde's identity leaves two terms, and they cancel because `A_1(1) + A_1(2) = 0`.
- **Odd primes and assembly.** Odd primes are handled by truncation and Euler's theorem; the Chinese remainder
  theorem then gives the general modulus.

## Lean 4 verification (`lean/`)

| File | Contents |
|---|---|
| `Statement.lean` | the pull-request file, byte-identical (git blob `61345ec3`), compiled with the repository's `leanOptions` |
| `CoreDefs.lean` | verbatim copies of `a`, `eventually_periodic`, `a_mod_k`; the recurrence |
| `CoreClosed.lean` | the closed formula for `2a(n)`, proved from the recurrence (no power series) |
| `CoreArith.lean` | integrality; `A_0`, `A_1` integer valued; `A_1(1) + A_1(2) = 0` |
| `CoreTwoAdic.lean` | `2^e ∣ b(n + 2^(e−1)) − b(n)` for `n ≥ e + 1` |
| `CoreOdd.lean` | `p^e ∣ b(n + φ(p^e)) − b(n)` for odd `p`, `n ≥ e` |
| `Core.lean` | the Chinese remainder step: `bounds_core` with `P = φ(k)` from `n = k` |
| `Solution.lean` | `OeisA370092.bounds_solved`, stated with the statement file's own definitions |
| `CheckAnswer.lean` | the definitions agree (`rfl`); `type_of% bounds = type_of% bounds_solved` (`rfl`); axioms |

```lean
theorem OeisA370092.bounds_solved (k : ℕ) (hk : 2 < k) :
    ∃ P : ℕ, P ∣ totient k ∧ eventually_periodic (a_mod_k k) P
```

- **Axioms:** only `propext`, `Classical.choice` and `Quot.sound`.
- **Forbidden keywords:** none of `sorry`, `admit`, `native_decide` or `axiom` appears in our files. The statement file
  keeps the repository's `sorry` for the open statement, unmodified.
- **Definitions:** the repository's `a` is a well-founded definition, so the equality of definitions is checked with
  `with_unfolding_all rfl`.

To reproduce, you need:
- Lean v4.33.1;
- a formal-conjectures checkout, tested at `ab0addc45f699bdd0b7cc58efa5140a72f101a9e`;
- `lake exe cache get`, run in that checkout.

Then run:

```bash
bash lean/check.sh /path/to/formal-conjectures
```

Log: `logs/lean_check.log` (exit 0, 246 s).

## Numerical checks (`scripts/verify_a370092.py`, `logs/verify_a370092.log`)

The script uses exact integer and rational arithmetic up to `n = 600`. It checks:
- every identity in the paper;
- the theorem for all `3 ≤ k ≤ 200`;
- the 2-adic statements for `e ≤ 10`.

## Prior work

- The conjecture is Bala's comment in A370092 (Feb 2024). The OEIS entry and its history contain no proof.
- The integral case of Bala's general `G(e^x − 1)` conjecture has been proved:
  - A. Kallat, arXiv:2609.07238 (Sep 2026), §2;
  - the-omega-institute/trureturing pull request 6811 (Sep 2026), in Lean.
- Fubini numbers: Gross (1962) and Barsky (1981).
- None of these covers A370092, whose `G` is not integral.
- Search date 2026-10-01. We found no proof of this conjecture in:
  - Formal Conjectures issues and pull requests;
  - the fc-review-results audits;
  - web search.
