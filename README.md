# A proof of Karttunen's conjecture A401714(n) ≤ A401715(n)

**Status:** proved, with a complete machine-checked proof in Lean 4 + Mathlib.

## The statement

For n ≥ 1, let

* `A003557(n) = n / rad(n)`, where `rad(n)` is the product of the distinct primes dividing n;
* `A053669(n)` = the smallest prime not dividing n;
* `usigma(n) = A034448(n)`, the sum of the unitary divisors of n (divisors d with gcd(d, n/d) = 1);
* `ssq(n) = A048250(n)`, the sum of the squarefree divisors of n.

**Theorem.** For every n ≥ 1, if A003557(n) < A053669(n), then usigma(n) + ssq(n) ≥ 2n.

Equivalently:
* [A401714](https://oeis.org/A401714)(n) ≤ [A401715](https://oeis.org/A401715)(n) for all n ≥ 1 (conjectured by Antti Karttunen, Nov 06 2026);
* [A393981](https://oeis.org/A393981) is a subsequence of [A389215](https://oeis.org/A389215);
* [A388986](https://oeis.org/A388986) is a subsequence of [A393869](https://oeis.org/A393869) (the form stated on A388986).

The bound is sharp: under the hypothesis, equality holds exactly for n ∈ {1, 4, 24}; for example n = 4 gives usigma(4) + ssq(4) = 5 + 3 = 8 = 2·4.

## Files

| File | Content |
|---|---|
| `A401714.lean` | The complete formal proof (~870 lines). Main theorem: `A401714.A401714_le_A401715`. |
| `A401714_proof.pdf` (and `.tex`) | The paper: full written proof, tables, details of the formal verification. |
| `checks/equality_cases.py` | Exact rational computations: reproduces Tables 1 and 2, D₁₀, and the equality cases n = 1, 4, 24. |
| `checks/OEIS_fidelity_checks.lean` | The same file plus checks: the Lean definitions reproduce the OEIS data of A034448, A048250, A003557, A053669, A401714 and A401715 (70–105 terms each), and a non-vacuity example. |

Verified with Lean `4.36.0-rc2` and Mathlib (commit `9d581dfff2e41de989072ea63abf3daf69311520`). The formalization covers the main theorem; the classification of the equality cases (n = 1, 4, 24 under the hypothesis) is proved in the paper together with an exact computation, and is not formalized. `#print axioms A401714.A401714_le_A401715` gives only `[propext, Classical.choice, Quot.sound]`: no `sorry`, no `native_decide` (the finite computations are checked by the kernel with `decide`).

To check it yourself, inside a Lean project that depends on Mathlib:

```
lake env lean A401714.lean
```

## Sketch of the proof

Write n = ∏_{p ∈ S} p^{e_p}, let q = A053669(n), A = A003557(n) = ∏ p^{e_p − 1}, and T = {p : e_p ≥ 2}. Since q is the smallest prime not dividing n, every prime p < q divides n. Every p ∈ T satisfies p ≤ A < q.

**Product bounds.** We have usigma(n) ≥ ∏_{p∈S}(1 + p^{e_p}) and ssq(n) ≥ ∏_{p∈S}(1 + p). (These are in fact equalities. Only the inequalities are formalized, via injections of subsets of S into the divisors.)

**Case q ≤ 73 (finite check).** Primes of n greater than q have exponent 1, so n = n₀·s, where n₀ = a·∏_{p<q} p with a = A(n) < q, and s is squarefree with all prime factors > q. Both products are multiplicative across this split, so it suffices to check 2·n₀ ≤ ∏(1 + p^{e_p}) + ∏(1 + p) for every prime q ≤ 73 and every 1 ≤ a < q. That is 691 cases, decided by the Lean kernel. Equality occurs exactly for n₀ = 1, 4, 24 (exact computation, not formalized).

**Case q > 73.** Here usigma alone suffices: usigma(n)/n ≥ ∏_{p<q, p∉T}(1 + 1/p), so it is enough to show N(q) := ∏_{p<q}(1 + 1/p) ≥ 2·∏_{p∈T}(1 + 1/p).

* *Rearrangement.* If |T| = t and p₁ < … < p_t are the first t primes, then ∏_{p∈T}(1 + 1/p) ≤ D_t := ∏_{i≤t}(1 + 1/p_i), and P_t := p₁⋯p_t ≤ ∏_{p∈T} p ≤ A < q.
* *Small t (t ≤ 9).* Explicit partial products: N(q) ≥ ∏_{p<y_t}(1 + 1/p) ≥ 2·D_t, with y_t = 74, 74, 74, 74, 150, 234, 368, 522, 734, 992.
* *Large t (t ≥ 10).* Two elementary lemmas:
  1. **N(q) ≥ H(q−1)/2**, where H is the harmonic number. Expanding the product gives at least the sum of 1/d over squarefree d < q. Writing every m ≤ x as m = d·j² with d squarefree gives H(x) ≤ (Σ_{d≤x squarefree} 1/d)·Σ_j 1/j² ≤ 2·Σ_{d≤x squarefree} 1/d.
  2. **4·D_t ≤ H(P_t) for t ≥ 10**, by induction. Base: P₁₀ = 6469693230 ≥ 2³², H(2³²) ≥ 1 + 32/2 = 17 ≥ 4·D₁₀ ≈ 15.51. Step: H(16N) ≥ H(N) + 2 (four doublings, each adding at least 1/2), p_t ≥ 31 ≥ 16, and 4·D_{t+1} = 4·D_t + 4·D_t/p_t ≤ 4·D_t + 2, because D_t ≤ (t + 2)/2 ≤ p_t/2.

  Hence N(q) ≥ H(q−1)/2 ≥ H(P_t)/2 ≥ 2·D_t. ∎

No deep theorem is used: no Mertens estimates and no prime number theorem.

## Credits and transparency

Proof found and formalized by **A-guy-with-AI** (pseudonym), with substantial help from two AI assistants: **Claude** (Anthropic), which wrote the proof strategy and the Lean formalization, and **ChatGPT** (OpenAI), which found the reduction to n₀ = a·∏_{p<q} p and the rearrangement bound, and independently re-checked the final proof. The statement was checked against the OEIS data before release. Comments and corrections are welcome.

November 2026.
