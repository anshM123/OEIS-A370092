"""Exact-arithmetic checks for the proof of Bala's conjecture on OEIS A370092 (paper/main.pdf).

Everything is computed with Python ints and fractions.Fraction; nothing is floating point.
Usage: python verify_a370092.py [N]      (the log in logs/ was produced with N = 600)
"""
import sys
from fractions import Fraction as Fr
from math import comb, factorial, gcd

N = int(sys.argv[1]) if len(sys.argv) > 1 else 300


def v2(x):
    """2-adic valuation of a nonzero rational; +inf for 0."""
    x = Fr(x)
    if x == 0:
        return float("inf")
    num, den = x.numerator, x.denominator
    v = 0
    while num % 2 == 0:
        num //= 2
        v += 1
    while den % 2 == 0:
        den //= 2
        v -= 1
    return v


def vp(x, p):
    x = Fr(x)
    if x == 0:
        return float("inf")
    num, den = x.numerator, x.denominator
    v = 0
    while num % p == 0:
        num //= p
        v += 1
    while den % p == 0:
        den //= p
        v -= 1
    return v


def s2(k):
    return bin(k).count("1")


# ---------------------------------------------------------------- 1. the sequence, as in the Lean file
a = [Fr(1)]
for n in range(1, N + 1):
    s = Fr(0)
    for j in range(1, n + 1):
        s += comb(n, j) * (1 - (-1) ** j - (-2) ** j) * a[n - j]
    a.append(Fr((-1) ** n) + s / 2)
assert all(x.denominator == 1 for x in a), "a(n) not integral"
a = [int(x) for x in a]
OEIS = [1, 1, 3, 16, 105, 856, 8433, 96916, 1272225, 18789136, 308335713, 5565837916,
        109603592145, 2338198823416, 53718370204593, 1322292130204516, 34718481333932865,
        968552056638097696, 28609403248435931073, 892022330159009036716,
        29276492753074019702385]
assert a[:len(OEIS)] == OEIS
print(f"[1] a(0..{N}) from the Lean recurrence: all integers, first 21 agree with OEIS")

# ---------------------------------------------------------------- 2. e.g.f. 2e^x/(1+e^x+e^{2x}-e^{3x})
# (1+e^x+e^{2x}-e^{3x}) A(x) = 2 e^x  <=>  sum_j C(n,j) a(j) c(n-j) = 2,  c(0)=2, c(m)=1+2^m-3^m
for n in range(N + 1):
    tot = sum(comb(n, j) * a[j] * ((1 if n - j == 0 else 0) + 1 + 2 ** (n - j) - 3 ** (n - j))
              for j in range(n + 1))
    # m![x^m](1+e^x+e^{2x}-e^{3x}) = [m=0] + 1 + 2^m - 3^m  (equals 2 for m = 0)
    assert tot == 2, (n, tot)
print("[2] e.g.f. identity (1+e^x+e^2x-e^3x) A(x) = 2e^x holds coefficientwise")

# ---------------------------------------------------------------- Stirling numbers S(n,k)
S = [[0] * (N + 2) for _ in range(N + 2)]
S[0][0] = 1
for n in range(1, N + 1):
    for k in range(1, n + 1):
        S[n][k] = k * S[n - 1][k] + S[n - 1][k - 1]
fact = [factorial(k) for k in range(N + 2)]
# k! S(n,k) = sum_i (-1)^(k-i) C(k,i) i^n  (0^0 = 1), spot check
for n in range(0, 12):
    for k in range(0, n + 1):
        assert fact[k] * S[n][k] == sum((-1) ** (k - i) * comb(k, i) * (i ** n if (i or n) else 1)
                                        for i in range(k + 1))

# ---------------------------------------------------------------- 3. expansion in z = e^x - 1
# G(z) = (1+z)/(1-z^2-z^3/2) = sum rho_k z^k ; g_k = g_{k-2} + g_{k-3}/2
g = [Fr(0)] * (N + 1)
for k in range(N + 1):
    g[k] = (Fr(1) if k == 0 else Fr(0)) + (g[k - 2] if k >= 2 else 0) + (g[k - 3] / 2 if k >= 3 else 0)
rho = [g[k] + (g[k - 1] if k >= 1 else 0) for k in range(N + 1)]
for k in range(N + 1):
    assert rho[k] == 0 or v2(rho[k]) >= -(k // 3)
    assert all(vp(rho[k], p) >= 0 for p in (3, 5, 7, 11, 13) if rho[k] != 0)
    assert (rho[k] * fact[k]).denominator == 1
for n in range(N + 1):
    assert a[n] == sum(rho[k] * fact[k] * S[n][k] for k in range(n + 1))
minv = min(v2(rho[k]) + k // 3 for k in range(N + 1) if rho[k] != 0)
print(f"[3] a(n) = sum_k rho_k k! S(n,k); v2(rho_k) >= -floor(k/3) (slack min {minv});"
      " rho_k k! integral")

# ---------------------------------------------------------------- 4. the parity splitting
# theta: 1/(1+w-w^3/4) = sum theta_k w^k ;  theta_k = -theta_{k-1} + theta_{k-3}/4
th = [Fr(0)] * (N + 1)
for k in range(N + 1):
    th[k] = (Fr(1) if k == 0 else Fr(0)) - (th[k - 1] if k >= 1 else 0) + (th[k - 3] / 4 if k >= 3 else 0)
for k in range(N + 1):
    assert th[k] == 0 or v2(th[k]) >= -2 * (k // 3)
lam1 = [th[k] + (th[k - 1] / 2 if k >= 1 else 0) for k in range(N + 1)]       # (1+w/2)/(1+w-w^3/4)
lam0 = [((th[k - 1] if k >= 1 else Fr(0)) + (th[k - 2] if k >= 2 else Fr(0))) / 2 for k in range(N + 1)]  # (w+w^2)/(2(1+w-w^3/4))
mu1 = [sum(lam1[k] * fact[k] * S[m][k] for k in range(m + 1)) for m in range(N + 1)]
mu0 = [sum(lam0[k] * fact[k] * S[m][k] for k in range(m + 1)) for m in range(N + 1)]
# e.g.f. checks: D(e^y) M(y) = numerator(e^y), D(v)=1+v+3v^2-v^3
#   n![y^n] D(e^y) = [n=0] + 1 + 3*2^n - 3^n ; n![y^n] 2(1+e^y) = 2[n=0]+2 ; n![y^n] 2e^{2y}-2e^y = 2^(n+1)-2
for n in range(N + 1):
    d = lambda m: (1 if m == 0 else 0) + 1 + 3 * 2 ** m - 3 ** m
    t1 = sum(comb(n, j) * d(n - j) * mu1[j] for j in range(n + 1))
    t0 = sum(comb(n, j) * d(n - j) * mu0[j] for j in range(n + 1))
    assert t1 == (2 if n == 0 else 0) + 2, (n, t1)
    assert t0 == 2 ** (n + 1) - 2, (n, t0)
print("[4a] mu_1 has e.g.f. 2(1+e^y)/D(e^y), mu_0 has e.g.f. 2(e^{2y}-e^y)/D(e^y)")
# the key identity a(n) = 2^n mu0(n) + sum_m C(n,m) 2^m mu1(m)
for n in range(N + 1):
    assert a[n] == 2 ** n * mu0[n] + sum(comb(n, m) * 2 ** m * mu1[m] for m in range(n + 1)), n
print("[4b] a(n) = 2^n mu0(n) + sum_m C(n,m) 2^m mu1(m)  for n <=", N)
# the valuation bounds
b1 = min(v2(x) for x in mu1 if x != 0)
b0 = min(v2(x) for x in mu0 if x != 0)
assert b1 >= -1 and b0 >= -1
# the termwise bounds used in the proof: v2(lam_{i,k}) + v2(k!) >= -1
for k in range(N + 1):
    if lam1[k] != 0:
        assert v2(lam1[k]) + k - s2(k) >= -1, k
    if lam0[k] != 0:
        assert v2(lam0[k]) + k - s2(k) >= -1, k
    # the explicit lower bounds used in the paper (Lemma 4)
    if lam1[k] != 0:
        assert v2(lam1[k]) >= (0 if k == 0 else -2 * (k // 3) - (1 if k % 3 else 0)), k
    if lam0[k] != 0:
        assert v2(lam0[k]) >= -1 - 2 * ((k - 1) // 3), k
print(f"[4c] min v2(mu1(m)) = {b1}, min v2(mu0(m)) = {b0}  (m <= {N}); termwise bounds hold")
print("     mu1(0..6) =", [str(x) for x in mu1[:7]])
print("     mu0(0..6) =", [str(x) for x in mu0[:7]])

# ---------------------------------------------------------------- 5. nu_j and nu'_j
def polymul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            r[i + j] += x * y
    return r


def L1(poly):
    return sum(c * mu1[m] for m, c in enumerate(poly))


JMAX = N // 2 - 1
nu, nup = [], []
pw = [1]  # (s^2+s)^j
for j in range(JMAX + 1):
    nu.append(4 ** j * L1(pw))
    nup.append(4 ** j * L1(polymul([1, 2], pw)))
    pw = polymul(pw, [0, 1, 1])
assert nu[0] == 1 and nup[0] == 0 and nu[1] == 0
for j in range(1, JMAX + 1):
    need = 2 + (j.bit_length() - 1)
    assert v2(nu[j]) >= need and v2(nup[j]) >= need, (j, v2(nu[j]), v2(nup[j]))
    assert v2(nu[j]) >= 2 * j - 1 and v2(nup[j]) >= 2 * j - 1
print(f"[5] nu_0=1, nu'_0=0, nu_1=0, v2(nu'_1)={v2(nup[1])}; v2(nu_j),v2(nu'_j) >= 2+floor(log2 j) for 1<=j<={JMAX}")
# binomial (Newton) expansion of the odd part
for n in range(0, 2 * JMAX + 2):
    mm, r = divmod(n, 2)
    lhs = sum(comb(n, m) * 2 ** m * mu1[m] for m in range(n + 1))
    rhs = sum(comb(mm, j) * (nup[j] if r else nu[j]) for j in range(mm + 1))
    assert lhs == rhs, n
print("[5b] sum_m C(n,m)2^m mu1(m) = sum_j C(floor(n/2),j) nu_j (n even) / nu'_j (n odd)")

# ---------------------------------------------------------------- 6. 2-adic periodicity
print("[6] mod 2^e: a(n+2^(e-1)) == a(n) for n >= e+1 ; minimal start; is 2^(e-2) also a period?")
for e in range(2, 12):
    M = 2 ** e
    P = 2 ** (e - 1)
    if N - P < e + 40:
        break
    ok = all((a[n + P] - a[n]) % M == 0 for n in range(e + 1, N - P + 1))
    first = max([n for n in range(0, N - P + 1) if (a[n + P] - a[n]) % M != 0], default=-1) + 1
    half = None
    if e >= 2:
        Q = P // 2
        half = all((a[n + Q] - a[n]) % M == 0 for n in range(N // 2, N - Q + 1))
    print(f"    e={e:2d}: period 2^{e-1} from n>=e+1: {ok}; congruence holds exactly from n={first};"
          f" period 2^{e-2} on tail: {half}")
    if e >= 2:
        assert ok
# mod 2 pattern
assert all((a[n] - (n + 1)) % 2 == 0 for n in range(2, N + 1))
print("    mod 2: a(n) == n+1 (mod 2) for all n >= 2 (period exactly 2, not 1)")

# ---------------------------------------------------------------- 7. odd prime powers
for p in (3, 5, 7, 11, 13):
    for e in (1, 2, 3):
        M = p ** e
        ph = M - M // p
        if N - ph < e + 30:
            continue
        ok = all((a[n + ph] - a[n]) % M == 0 for n in range(e, N - ph + 1))
        first = max([n for n in range(0, N - ph + 1) if (a[n + ph] - a[n]) % M != 0], default=-1) + 1
        print(f"[7] p^e={M}: a(n+phi)==a(n) for n>=e: {ok}; exact start {first}")
        assert ok


# ---------------------------------------------------------------- 8. the full statement for k = 3..K
def phi(k):
    r, m, p = k, k, 2
    while p * p <= m:
        if m % p == 0:
            while m % p == 0:
                m //= p
            r -= r // p
        p += 1
    if m > 1:
        r -= r // m
    return r


def Nbound(k):
    """start index from the proof: e+1 for 2^e (e>=2), 3 for 2||k, e for odd p^e."""
    nb, m, p = 0, k, 2
    while m > 1:
        if m % p == 0:
            e = 0
            while m % p == 0:
                m //= p
                e += 1
            if p == 2:
                nb = max(nb, e + 1 if e >= 2 else 3)
            else:
                nb = max(nb, e)
        p += 1
    return nb


bad = []
for k in range(3, 201):
    P = phi(k)
    nb = Nbound(k)
    if N - P <= nb:
        continue
    if not all((a[n + P] - a[n]) % k == 0 for n in range(nb, N - P + 1)):
        bad.append(k)
print(f"[8] k=3..200: a(n+phi(k)) == a(n) (mod k) for all n >= N(k) (n+phi(k)<= {N}); failures: {bad}")
assert not bad
# corner cases k = 2^e: the period must divide 2^(e-1) itself
for e in range(2, 9):
    k = 2 ** e
    P = phi(k)
    print(f"    k=2^{e}: phi={P}, holds from n={e+1}: "
          f"{all((a[n + P] - a[n]) % k == 0 for n in range(e + 1, N - P + 1))}")
# k = 2 genuinely fails (phi(2)=1): conjecture correctly excludes it
print("    k=2: a(n+1)==a(n) mod 2 eventually?",
      all((a[n + 1] - a[n]) % 2 == 0 for n in range(N // 2, N)))
# uniform start N = k
bad = [k for k in range(3, 201) if N - phi(k) > k and
       not all((a[n + phi(k)] - a[n]) % k == 0 for n in range(k, N - phi(k) + 1))]
print(f"    uniform start: a(n+phi(k)) == a(n) (mod k) for all n >= k, k=3..200: failures {bad}")
assert not bad

# ================================================================ checks for the proof in the paper
# [9] polynomial identities (integer coefficient lists, index = degree)
def padd(p, q):
    r = [0] * max(len(p), len(q))
    for i, x in enumerate(p):
        r[i] += x
    for i, x in enumerate(q):
        r[i] += x
    while len(r) > 1 and r[-1] == 0:
        r.pop()
    return r


def pscale(c, p):
    return [c * x for x in p]


Qp = [1, 1, 1, -1]            # Q(u) = 1+u+u^2-u^3
Qm = [1, -1, 1, 1]            # Q(-u)
Du2 = [1, 0, 1, 0, 3, 0, -1]  # D(u^2) = 1+u^2+3u^4-u^6
assert padd(polymul(Qp, Qm), pscale(-1, Du2)) == [0]
assert polymul([0, 2], Qm) == padd([0, 0, -2, 0, 2], [0, 2, 0, 2])   # 2uQ(-u) = 2(u^4-u^2) + 2u(1+u^2)
D = [1, 1, 3, -1]


def compose_shift(p):  # p(1+w)
    r = [0]
    for i, c in enumerate(p):
        term = [1]
        for _ in range(i):
            term = polymul(term, [1, 1])
        r = padd(r, pscale(c, term))
    return r


assert compose_shift(D) == [4, 4, 0, -1]                       # D(1+w) = 4+4w-w^3
assert compose_shift([2, 2]) == [4, 2]                          # 2(1+v) -> 2(2+w)
assert compose_shift([0, -2, 2]) == [0, 2, 2]                   # 2(v^2-v) -> 2(w+w^2)
print("[9] polynomial identities Q(u)Q(-u)=D(u^2), 2uQ(-u)=2(u^4-u^2)+2u(1+u^2), D(1+w)=4+4w-w^3: OK")

# [10] A_i(m) = 2 mu_i(m) are integers; special values; integrality of 2 lambda_{i,k} k!
A0 = [2 * x for x in mu0]
A1 = [2 * x for x in mu1]
assert all(x.denominator == 1 for x in A0 + A1)
A0 = [int(x) for x in A0]
A1 = [int(x) for x in A1]
assert A1[:3] == [2, -1, 1]
for k in range(N + 1):
    assert (2 * lam1[k] * fact[k]).denominator == 1 and (2 * lam0[k] * fact[k]).denominator == 1  # c_{i,k} in Z
    assert (4 ** (k // 3) * 2 * lam1[k]).denominator == 1 and (4 ** (k // 3) * 2 * lam0[k]).denominator == 1
    assert (4 ** (k // 3) * th[k]).denominator == 1
    assert th[k] == 0 or v2(th[k]) >= -2 * (k // 3)
    vk = k - s2(k)
    assert vk >= 2 * (k // 3) - 1
    assert k == 0 or vk >= 2 * ((k - 1) // 3)
    assert vk >= k // 2 + k // 4
for n in range(N + 1):
    assert 2 * a[n] == 2 ** n * A0[n] + sum(comb(n, m) * 2 ** m * A1[m] for m in range(n + 1))
print("[10] A_i(m)=2mu_i(m) in Z (m<=N), A1(0..2)=2,-1,1, c_{i,k}=2k!lam_{i,k} in Z, 4^(k/3)theta_k in Z, Lemma-4 bounds, (Z1) identity: OK")
print("     A1(0..8) =", A1[:9], " A0(0..8) =", A0[:9])

# [11] the short 2-adic argument: F(n+P)-F(n) == 0 mod 2^(e+1) for ALL n; shifted-sum identity; Kummer bound
F = [sum(comb(n, m) * 2 ** m * A1[m] for m in range(n + 1)) for n in range(N + 1)]
emax = 1
for e in range(2, 11):
    P = 2 ** (e - 1)
    if P > N // 2:
        break
    emax = e
    assert all((F[n + P] - F[n]) % 2 ** (e + 1) == 0 for n in range(0, N - P + 1)), e
    assert all((2 ** (n + P) * A0[n + P] - 2 ** n * A0[n]) % 2 ** (e + 1) == 0 for n in range(e + 1, N - P + 1))
    for n in (0, 1, 5, 17):
        if n + P > N:
            continue
        Fsh = lambda r: sum(comb(n, j) * 2 ** j * A1[j + r] for j in range(n + 1))
        assert F[n + P] - F[n] == sum(comb(P, r) * 2 ** r * Fsh(r) for r in range(1, P + 1))
for aa in range(0, 13):
    Pq = 2 ** aa
    for r in range(1, Pq + 1):
        vr = (r & -r).bit_length() - 1
        assert v2(comb(Pq, r)) == aa - vr
print(f"[11] F(n+2^(e-1)) == F(n) mod 2^(e+1) for all n (e=2..{emax}); Vandermonde shift identity; v2(C(2^a,r)) = a - v2(r): OK")

# [12] exactness of the period 2^(e-1): for e>=3 and n>=e+1, a(n+2^(e-2))-a(n) == 2^(e-1) (n odd), 0 (n even) mod 2^e
emax2 = 2
for e in range(3, 11):
    Pp = 2 ** (e - 2)
    M = 2 ** e
    if Pp > N // 2:
        break
    emax2 = e
    for n in range(e + 1, N - Pp + 1):
        d = (a[n + Pp] - a[n]) % M
        assert d == (2 ** (e - 1) if n % 2 else 0), (e, n, d)
assert all((a[n + 1] - a[n]) % 2 == 1 for n in range(2, N))
print(f"[12] exact period: mod 2^e (e=3..{emax2}) the shift 2^(e-2) changes odd-index terms by 2^(e-1); mod 4 shift 1 fails: OK")

# [13] odd primes: truncation to k < p*e of the 2-section expansion
for p in (3, 5, 7):
    for e in (1, 2, 3):
        K = p * e
        for n in range(0, min(N, 150) + 1):
            trunc = sum(Fr(0) + sum((-1) ** (k - i) * comb(k, i) *
                                    (2 * lam0[k] * (2 * i) ** n + 2 * lam1[k] * (2 * i + 1) ** n)
                                    for i in range(k + 1)) for k in range(K))
            diff = 2 * a[n] - trunc
            assert diff == 0 or vp(diff, p) >= e, (p, e, n)
print("[13] odd p: 2a(n) == sum_{k<pe} sum_i (-1)^(k-i)C(k,i)[2lam0_k(2i)^n + 2lam1_k(2i+1)^n] (mod p^e): OK")
print("ALL CHECKS PASSED")
