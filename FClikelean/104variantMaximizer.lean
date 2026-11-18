module

public import FClikelean.«104variant»
public meta import FormalConjecturesUtil.Attributes.Basic

/-!
# Maximizers in Erdős's unit-circumradius triple problem

This related theorem describes every configuration attaining the maximum
in the value question from `104variant.lean`.
-/

@[expose] public section

open EuclideanGeometry
open scoped Classical EuclideanGeometry

namespace Erdos104

set_option warn.sorry false in
/-- For `n ≥ 4`, every maximizer has exactly `n - 1` points on some unit circle. -/
@[category research solved, AMS 52]
theorem erdos_104.variants.unitCircumradiusTriplesMaximizer
    (P : Finset (EuclideanSpace ℝ (Fin 2))) (hn : 4 ≤ P.card) (hP : ¬ LiesOnUnitCircle P)
    (hmax : ((P.powersetCard 3).filter LiesOnUnitCircle).card =
      sSup {k | ∃ Q : Finset (EuclideanSpace ℝ (Fin 2)),
        Q.card = P.card ∧ ¬ LiesOnUnitCircle Q ∧
          ((Q.powersetCard 3).filter LiesOnUnitCircle).card = k}) :
    ∃ s : Sphere (EuclideanSpace ℝ (Fin 2)), s.radius = 1 ∧
      ((P.filter fun p => p ∈ s).card = P.card - 1) := by
  sorry

end Erdos104
