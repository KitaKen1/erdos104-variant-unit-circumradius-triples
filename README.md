# Erdős #104 related question on unit-circumradius triples

Erdős posed the following problem in 1975.

> **Problem.** Let $g(n)$ be the largest number of unordered triples with
> circumradius $1$ among $n$ distinct points in the plane, subject to the
> condition that no unit circle contains all $n$ points. Estimate $g(n)$
> or determine it exactly.

Erdős suggested that a configuration with $n-1$ points on a unit circle
attains the maximum.
[Erdős, *Some problems on elementary geometry*, p. 3](https://www.renyi.hu/~p_erdos/1975-41.pdf#page=2)

This repository gives the exact value. We have $g(2)=g(3)=0$, and for $n\ge4$,

$$
g(n)=\binom{n-1}{3}+n-2+\mathbf{1}_{3\mid(n-1)}.
$$

The statement is a proposed related entry for Erdős #104. The main #104
statement concerns the number of distinct unit circles.
[Formal Conjectures #104](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/104.lean)

### Main contributions

1. **FC-style formalization.** The exact-value statement for $g(n)$ counts
   three-point subsets using `LiesOnUnitCircle`.
   [FClikelean/104variant.lean](FClikelean/104variant.lean)
2. **Lean 4 proof.** An upper bound for every admissible configuration and a
   construction attaining it for each $n\ge2$.
   [Mathematical proof](lean/Erdos104UnitTriples.lean) · [Proof of the FC-style statement](leanWithComparator/Solution.lean)

### Subcontributions

1. **FC-style formalization of the maximizer statement.**

   > **Maximizers.** Let $P$ be a set of $n\ge4$ distinct points in the plane
   > such that no unit circle contains all of $P$. If $P$ has $g(n)$ triples
   > with circumradius $1$, some unit circle contains exactly $n-1$ points
   > of $P$.

   [FClikelean/104variantMaximizer.lean](FClikelean/104variantMaximizer.lean)
2. **Lean 4 proof of the maximizer statement.**
   [lean/104variantMaximizer.lean](lean/104variantMaximizer.lean)

[How the maximizer theorem arises from Erdős's paper](#appendix-subcontributions)

## Mathematical explanation (AI-generated)

Write $T(P)$ for the number of triples of $P$ with circumradius $1$. For $m\ge1$,
let $e(m)=m$ if $3\mid m$ and $e(m)=m-1$ otherwise. Set
$B_n=\binom{n-1}{3}+e(n-1)$ for $n\ge4$. We show that $g(n)=B_n$ and that every
configuration attaining this value has $n-1$ points on a unit circle.

### One point off the circle

Suppose $m$ points lie on the unit circle centered at the origin, and $x$ lies
off that circle. For distinct circle points $a,b$, the possible centers of unit
circles through $a,b$ are $0$ and $a+b$. Indeed, any second center is the
reflection of the first through the midpoint of the chord. Join $a$ and $b$
by an edge when $\lVert x-a-b\rVert=1$. The edges are exactly the pairs that
make a qualifying triple with $x$.

A neighbor $b$ of $a$ is the center of a unit circle through $0$ and $x-a$.
These two points are distinct, so $a$ has at most two neighbors. If $b,c$ are
distinct neighbors, the same reflection gives $b+c=x-a$. Then
$\lVert x-b-c\rVert=\lVert a\rVert=1$, so $b$ and $c$ are adjacent. The
components are therefore isolated vertices, single edges, and triangles.
Each component has at most as many edges as vertices, with equality only for
triangles. The graph has at most $e(m)$ edges.

For equality, take $x=0$, write $m=3q+r$ with $0\le r<3$, and choose $q$ full
orbits of a $120^\circ$ rotation and $r$ points from one more orbit. Every
within-orbit pair gives an edge, because the three vectors of a full orbit
sum to zero. This gives $3q+\binom{r}{2}=e(m)$ edges. For $m=n-1\ge3$, the
circle points contribute another $\binom{m}{3}$ triples and determine their
unit circle uniquely. Adding the origin gives an admissible configuration
attaining $B_n$.

### Upper bound by deleting a point

For $n=2,3$, no admissible configuration contributes any triple. A pair at
distance greater than $2$ gives admissible examples in both cases, adding a
distinct third point when needed. For $n=4$, there are only four triples.
For $n=5$, if no unit circle contains four points, any qualifying unit circle
contains exactly three points. Each point pair belongs to at most two such
circles, so $3T(P)\le 2\binom{5}{2}$ and $T(P)\le6<B_5$.

Now let $n\ge6$. If a unit circle contains $n-1$ points, the first argument
gives $T(P)\le B_n$. Otherwise every one-point deletion is admissible.
Each qualifying triple survives exactly $n-3$ such deletions, so induction
gives $(n-3)T(P)\le nB_{n-1}$. The small cases give the following bounds.

| $n$ | $\left\lfloor nB_{n-1}/(n-3)\right\rfloor$ | $B_n$ |
| ---: | ---: | ---: |
| 6 | 14 | 14 |
| 7 | 24 | 26 |
| 8 | 41 | 41 |
| 9 | 61 | 63 |

For $n\ge10$, the binomial part of $(n-3)B_n-nB_{n-1}$ is $\binom{n-2}{2}$.
Using $e(n-1)\ge n-2$ and $e(n-2)\le n-2$ gives the strict margin

$$
(n-3)B_n-nB_{n-1}
  \ge \binom{n-2}{2}-3(n-2)
  = \frac{(n-2)(n-9)}{2}>0.
$$

### Why every maximizer has an $(n-1)$-point circle

For $n=4$, any qualifying triple already supplies such a circle. The upper
bounds are strict for configurations without an $(n-1)$-point circle at
$n=5,7,9$ and all $n\ge10$. The two remaining cases are $n=6,8$. In either
case, if a circle contains all but two points $x,y$, at most four triples
contain both $x$ and $y$. There are at most two unit circles through this
pair, and each meets the original circle in at most two points.

For $n=8$, a six-point circle gives at most
$\binom{6}{3}+2e(6)+4=36$ qualifying triples. If each unit circle contains at
most five points, each seven-point subset has at most $24$ qualifying
triples by the deletion bound in the table. Counting their survival once
more gives $T(P)\le\lfloor8\cdot24/5\rfloor=38<41$.

For $n=6$, if each unit circle contains at most three points, the pair count
gives $T(P)\le10$. Otherwise take a four-point unit circle centered at $0$.
To attain $14=\binom{4}{3}+2e(4)+4$, each outside point must give three edges
on the four circle points, and four triples must contain both outside points.
Three edges on four vertices force a triangle in each of the two graphs.
These triangles are distinct because their vertex sums give their respective
outside points. Label the four points $a,b,c,d$ so that $x=a+b+c$ and
$y=a+b+d$.

The unit circle through $x,y$ centered at $u=a+b$ meets the original circle
at $a,b$. Here $u\ne0$, since $x$ is off the original circle. Four triples
through $x,y$ require the second circle, centered at $x+y-u=a+b+c+d$, to
contain both $c$ and $d$. Its center would have to be either $0$ or $c+d$.
The first possibility puts $x$ on the original circle, and the second forces
$u=0$. This rules out equality for six points without a five-point circle.

## Appendix: Subcontributions

Immediately after asking for $g(n)$, Erdős suggests a form for a configuration
that attains the maximum.

> It seems reasonable to assume that the maximum is achieved if $n-1$ of our
> $n$ points are on a unit circle.

[Erdős, *Some problems on elementary geometry*, p. 3](https://www.renyi.hu/~p_erdos/1975-41.pdf#page=2)

The construction for the exact value realizes this suggestion for each $n\ge4$.
It places $n-1$ points on a unit circle and the remaining point at its center.
[Construction](#one-point-off-the-circle)

The maximizer theorem comes from asking when the upper bound is attained.
If every unit circle contains at most $n-2$ of the points, the triple count is
strictly below $g(n)$. The deletion bound leaves equality possible at $n=6$ and
$n=8$, so the proof treats those two cases separately.
[Equality-case argument](#why-every-maximizer-has-an-n-1-point-circle)

Thus, for $n\ge4$, **every** admissible maximizing configuration has exactly
$n-1$ points on some unit circle. The two subcontributions give the FC-style
statement and its Lean proof.
[FC-style statement](FClikelean/104variantMaximizer.lean) · [Lean proof](lean/104variantMaximizer.lean)

## Appendix: Verification by Lean Comparator on GitHub CI runner

The Lean comparator workflow runs when its inputs change on `main`. You can
also run it manually from the Actions tab. It checks the generated definitions
against the FC value file and records the SHA-256 hashes of the verification
inputs at the tested commit. Lake uses bubblewrap on Ubuntu 24.04 to build and export the two FC-style
statements and the combined solution in separate Lean environments. Comparator
checks the exact-value and maximizer theorems and their reachable definitions.
It permits only `propext`, `Classical.choice`, and `Quot.sound`, and requires
acceptance by both nanoda and Lean's kernel. A fresh Lean kernel then replays
the solution module.
[Lean comparator workflow](.github/workflows/comparator.yml) · [Comparator configuration](comparator.json) · [Lean signature check](verification/Check.lean)

### Certification within 90 days

Each run attempt uploads an artifact named `comparator-<run-id>-<attempt>`
with a requested retention of 90 days. A successful artifact contains the
checked signatures and axioms in `statement.log`, both kernel verdicts in
`fc-target.log`, the tested commit and result in `result.json`, the input
hashes in `inputs.sha256`, and the fresh replay log and status.

On 18 November 2026, a trusted local macOS run passed Comparator with nanoda
and Lean. Its input hashes predate the addition of the `main` push trigger.
A GitHub Actions run records its own tested commit and sandbox status.
[Checked Lean signatures](verification/logs/local/statement.log) · [Local comparator log](verification/logs/local/fc-target.log)

### Certification after 90 days

Before the artifact expires, run [archive-run.py](verification/archive-run.py)
with an authenticated GitHub CLI. It checks the tested commit, the successful
attempt and GitHub's SHA-256 artifact digest, then saves the original ZIPs,
metadata, verification logs and `SHA256SUMS`.

```sh
python3 verification/archive-run.py --repo OWNER/REPO --run RUN_ID \
  --attempt ATTEMPT --expected-commit FULL_SHA --output verification/logs/ci-RUN_ID
```

### Reproduce the verification

With elan and bubblewrap installed on Linux, run from the repository root.
The toolchain and Mathlib revision are pinned.
[Lean toolchain](lean-toolchain) · [Dependency lock](lake-manifest.json)

```sh
lake exe cache get
LEAN_NUM_THREADS=1 python3 verification/verify.py
```

The runner checks the signatures, compares both targets and runs
`leanchecker --fresh --verbose`. By default it writes to
`verification/results/`. For a trusted macOS checkout, pass
`--trusted-local` to run Comparator without Linux's bubblewrap sandbox.
Use `--output` to select a new evidence directory.

After editing the model in `FClikelean/104variant.lean`, run
`python3 leanWithComparator/sync_definitions.py` to refresh the solution's definitions.

For an upstream submission, the target definitions and declarations can be
placed in `ErdosProblems/104.lean`. Add the external `formal_proof` attribute
once a Palomar entry can link to the published proof.
[Formal Conjectures contribution guide](https://github.com/google-deepmind/formal-conjectures/blob/main/CONTRIBUTING.md#the-formal_proof-attribute)

[Third-party source and license](THIRD_PARTY.md)

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced by Kenta Kitamura with assistance from OpenAI Codex using GPT-6.2 Astra.

## Appendix: Timeline

| Date | Development | Source |
| --- | --- | --- |
| 1975 | Erdős asks for the maximum number $g(n)$ of triples with unit circumradius when no unit circle contains all the points. He suggests that $n-1$ points on a unit circle suffice to attain the maximum. | [Erdős, *Some problems on elementary geometry*, p. 3](https://www.renyi.hu/~p_erdos/1975-41.pdf#page=2) |
| 1984 | Elekes constructs $n$-point sets that determine at least a constant times $n^{3/2}$ distinct unit circles for the related circle-counting problem. | [Elekes, *Combinatorica*](https://doi.org/10.1007/BF02579212) |
| 1986 | Harborth and Mengersen determine the maximum number of distinct unit circles through triples for $3\le n\le7$. | [Harborth and Mengersen, *Discrete Mathematics*](https://doi.org/10.1016/0012-365X(86)90011-7) |
| 7 September 2026 | Formal Conjectures adds the statement of Erdős #104 on the number of distinct unit circles. | [Formal Conjectures issue #335](https://github.com/google-deepmind/formal-conjectures/issues/335) |
| 18 November 2026 | **This repository solves Erdős's $g(n)$ problem.** It determines the exact value for every $n\ge2$ and proves that every maximizer for $n\ge4$ has $n-1$ points on a unit circle. Both results have Lean 4 proofs. | [Exact value](FClikelean/104variant.lean) · [Maximizer theorem](FClikelean/104variantMaximizer.lean) · [Verification log](leanWithComparator/verification.log) |
