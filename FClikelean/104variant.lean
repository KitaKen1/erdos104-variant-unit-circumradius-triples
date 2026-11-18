module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public meta import FormalConjecturesUtil.Attributes.Basic

/-!
# Erdős Problem 104, unit-circumradius triples

Erdős asks for the maximum number of triples with unit circumradius among
planar point sets that are not contained in a unit circle. He also suggests
that the maximum is attained with all but one point on a unit circle.

*References:*
- [Er75] P. Erdős, *Some problems on elementary geometry*, Austral. Math. Soc.
  Gaz. (1975), 2–3. The value question appears on p. 3.
  https://www.renyi.hu/~p_erdos/1975-41.pdf#page=2
- [Erdős Problem 104](https://www.erdosproblems.com/104) is the related
  problem about counting distinct circles.
-/

@[expose] public section

open EuclideanGeometry
open scoped Classical EuclideanGeometry

namespace Erdos104

/-- All the points of `P` lie on the circumference of a single unit circle. -/
def LiesOnUnitCircle (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ s : Sphere (EuclideanSpace ℝ (Fin 2)), s.radius = 1 ∧ ∀ p ∈ P, p ∈ s

-- The challenge theorem follows.

set_option warn.sorry false in
/-- The exact maximum number of triples with unit circumradius among sets of
`n` points that are not contained in any unit circle. -/
@[category research solved, AMS 52]
theorem erdos_104.variants.unitCircumradiusTriples (n : ℕ) (hn : 2 ≤ n) :
    sSup {k | ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
      P.card = n ∧ ¬ LiesOnUnitCircle P ∧
        ((P.powersetCard 3).filter LiesOnUnitCircle).card = k} =
        if n ≤ 3 then 0
        else (n - 1).choose 3 + (n - 2) + (if (n - 1) % 3 = 0 then 1 else 0) := by
  sorry

end Erdos104
