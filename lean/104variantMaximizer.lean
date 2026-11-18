module

public import leanWithComparator.Solution

/-!
# Maximizers of Erdős's unit-circumradius triple count

Every admissible configuration attaining the exact value with at least four
points has a unit circle containing all but one point.
-/

@[expose] public section

open EuclideanGeometry
open scoped Classical EuclideanGeometry

namespace Erdos104

/-- Every maximizer with at least four points has all but one point on a unit circle. -/
theorem erdos_104.variants.unitCircumradiusTriplesMaximizer
    (P : Finset (EuclideanSpace ℝ (Fin 2))) (hn : 4 ≤ P.card) (hP : ¬ LiesOnUnitCircle P)
    (hmax : ((P.powersetCard 3).filter LiesOnUnitCircle).card =
      sSup {k | ∃ Q : Finset (EuclideanSpace ℝ (Fin 2)),
        Q.card = P.card ∧ ¬ LiesOnUnitCircle Q ∧
          ((Q.powersetCard 3).filter LiesOnUnitCircle).card = k}) :
    ∃ s : Sphere (EuclideanSpace ℝ (Fin 2)), s.radius = 1 ∧
      ((P.filter fun p => p ∈ s).card = P.card - 1) := by
  classical
  have hAd : Erdos104UnitTriples.Admissible P :=
    fun h => hP ((liesOnUnitCircle_iff P).mpr h)
  rw [unitCircumradiusTripleCount_eq, count_set_eq, ← Erdos104UnitTriples.gn] at hmax
  obtain ⟨c, hc⟩ := Erdos104UnitTriples.maximizer_on_unit_circle P hn hAd hmax
  exact ⟨⟨c, 1⟩, rfl, hc⟩

end Erdos104

#print axioms Erdos104.erdos_104.variants.unitCircumradiusTriplesMaximizer
