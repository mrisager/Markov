# Theorem 1

Let $M(x)$ count triples of positive integers $a\le b\le c\le x$ with
$a^2+b^2+c^2=3abc$. As $x\to+\infty$, the formalization proves

$$
M(x)=C\bigl(\log(3x)\bigr)^2+
O\!\left(\frac{\log x\,(\log\log\log x)^{1/10}}
{(\log\log x)^{3/10}}\right).
$$

Under the quasi-Riemann hypothesis (QRH) of the paper, it also proves

$$
M(x)=C\bigl(\log(3x)\bigr)^2+
O\!\left(\frac{\log x}{(\log\log x)^{1/2}}\right).
$$

In both statements C = 2 × area(B<sub>X</sub>) / π² > 0, with the same
geometric $B_X$ as in [Theorem 12](THEOREM12.md). QRH is the existence of a
fixed $\delta>0$ such that the Riemann zeta function has no zeros inRe(s) > 1 − δ, with the pole $s=1$ excluded.

## Lean entry points

| Declaration | Definition or proof |
| --- | --- |
| `Markov.count` | [`Markov/Basic.lean`](../Markov/Basic.lean) |
| `Markov.MainTheorem` and `Markov.QuasiRiemannHypothesis` | [`Markov/Statements.lean`](../Markov/Statements.lean) |
| `Markov.t1_mainTheorem` and `Markov.t1_markovUnconditional` | [`T1ExactTheoremOne.lean`](../Theorem1/T1ExactTheoremOne.lean) |
| `Markov.t1_markovConditional_of_QRH` | [`T1QRHMertensPower.lean`](../Theorem1/T1QRHMertensPower.lean) |
| `Markov.t1_markovLeadingCoefficient` | [`T1ActualMarkovCountIdentity.lean`](../Theorem1/T1ActualMarkovCountIdentity.lean) |
| `Markov.t1_VKZeroFreeRegion_proved` | [`ZetaVinogradovZeroFree.lean`](../Theorem1/RiemannGaussian/ZetaVinogradovZeroFree.lean) |

`MainTheorem` expresses the two error terms with a common positive
coefficient. The separate branch theorems give them with the explicit
geometric coefficient.

## Proof route

1. Finite Möbius inversion converts the geometric lattice count into a
   primitive lattice count. Theorem 12 supplies the lattice error and the
   absolutely convergent Möbius square series gives the primitive density
   $6/\pi^2$.
2. The Farey and Vieta constructions identify the primitive lattice points
   in a fundamental sector with nonexceptional sorted Markov triples.
   The twelve symmetries and boundary corrections give an exact count
   identity at length 2 arcosh(3x/2) for $x\ge2$.
3. For the unconditional error, a checked Vinogradov–Korobov region for
   mathlib's Riemann zeta function yields the required Mertens estimate
   through contour bounds and desmoothing. Under QRH the fixed zero-free
   strip gives a power-saving Mertens estimate. The cutoff and scale
   transfers give the two stated errors.

The proof is about triples. It does not require a uniqueness conjecture
about recovery of a triple from its largest entry. See the
[dependency notes](DEPENDENCIES.md) for the origin of the unconditional
zero-free region.
