#!/usr/bin/env python3
"""Exact computations accompanying "A proof of Karttunen's conjecture A401714(n) <= A401715(n)".

Reproduces, in exact rational arithmetic:
  * Proposition 4.1 / Table 1: for every prime q <= 73 and 1 <= a < q,
      G(q,a) = prod_{p<q} (1 + p^(1+v_p(a))) + prod_{p<q} (1+p)  >=  2 a P(q),
    the minimum of G(q,a)/(a P(q)) for each q, and the equality cases;
  * Table 2: N(y_t) >= 2 D_t for t <= 9;
  * the value of D_10.
Run with:  python3 equality_cases.py
"""
from fractions import Fraction as F


def primes_upto(n):
    sieve = [True] * (n + 1)
    sieve[0:2] = [False, False]
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = [False] * len(sieve[i * i::i])
    return [i for i, b in enumerate(sieve) if b]


PR = primes_upto(1000)


def v(a, p):
    e = 0
    while a % p == 0:
        a //= p
        e += 1
    return e


def N(x):
    r = F(1)
    for p in PR:
        if p >= x:
            break
        r *= F(p + 1, p)
    return r


# Proposition 4.1 and Table 1
pairs, equalities = 0, []
print("Table 1: min over 1<=a<q of G(q,a)/(a P(q))")
for q in [p for p in PR if p <= 73]:
    ps = [p for p in PR if p < q]
    Pq = 1
    for p in ps:
        Pq *= p
    best = None
    for a in range(1, q):
        pairs += 1
        G1 = G2 = 1
        for p in ps:
            G1 *= 1 + p ** (1 + v(a, p))
            G2 *= 1 + p
        ratio = F(G1 + G2, a * Pq)
        assert ratio >= 2, (q, a)
        if ratio == 2:
            equalities.append((q, a, a * Pq))
        if best is None or ratio < best[0]:
            best = (ratio, a)
    print(f"  q={q:2d}  min={float(best[0]):.4f}  at a={best[1]}")
print(f"Pairs checked: {pairs}")
print(f"Equality cases (q, a, n0 = a*P(q)): {equalities}")

# Table 2
D, P = [F(1)], [1]
for p in PR[:11]:
    D.append(D[-1] * F(p + 1, p))
    P.append(P[-1] * p)
ys = {0: 74, 1: 74, 2: 74, 3: 74, 4: 150, 5: 234, 6: 368, 7: 522, 8: 734, 9: 992}
print("Table 2: N(y_t) >= 2 D_t")
for t, y in ys.items():
    assert N(y) >= 2 * D[t], t
    assert t <= 3 or y <= P[t] + 1
    print(f"  t={t}  P_t={P[t]}  y_t={y}  N(y_t)={float(N(y)):.5f}  2D_t={float(2 * D[t]):.5f}")
print(f"D_10 = {D[10]} = {float(D[10]):.6f};  4 D_10 = {float(4 * D[10]):.4f} < 17")
print("All checks passed.")
