module

public import leanWithComparator.Definitions
public import Erdos104UnitTriples

/-!
# Proof of the FC value statement

The challenge uses bundled unit spheres. These lemmas transport the checked
distance-based proof to the definitions used by the challenge.
-/

@[expose] public section

open EuclideanGeometry
open scoped Classical EuclideanGeometry

namespace Erdos104

/-- A bundled unit circle is equivalent to specifying its center. -/
theorem liesOnUnitCircle_iff (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    LiesOnUnitCircle P ↔ ∃ c : EuclideanSpace ℝ (Fin 2), ∀ p ∈ P, dist p c = 1 := by
  constructor
  · rintro ⟨s, hs, hP⟩
    exact ⟨s.center, fun p hp => (mem_sphere.mp (hP p hp)).trans hs⟩
  · rintro ⟨c, hc⟩
    exact ⟨⟨c, 1⟩, rfl, fun p hp => mem_sphere.mpr (hc p hp)⟩

/-- The sphere-based triple count agrees with the count in the proof. -/
theorem unitCircumradiusTripleCount_eq (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    ((P.powersetCard 3).filter LiesOnUnitCircle).card =
      (Erdos104UnitTriples.unitTriples P).card := by
  classical
  have h : (P.powersetCard 3).filter LiesOnUnitCircle = Erdos104UnitTriples.unitTriples P := by
    ext T
    change T ∈ (P.powersetCard 3).filter LiesOnUnitCircle ↔
      T ∈ (P.powersetCard 3).filter (fun A => ∃ c : EuclideanSpace ℝ (Fin 2), ∀ p ∈ A, dist p c = 1)
    simp only [Finset.mem_filter, liesOnUnitCircle_iff]
  exact congrArg Finset.card h

/-- The two models give the same set of attainable triple counts. -/
theorem count_set_eq (n : ℕ) :
    {k | ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
      P.card = n ∧ ¬ LiesOnUnitCircle P ∧
        ((P.powersetCard 3).filter LiesOnUnitCircle).card = k} =
        Erdos104UnitTriples.possibleCounts n := by
  ext k
  simp only [Erdos104UnitTriples.possibleCounts, Set.mem_ofPred_eq,
    Erdos104UnitTriples.Admissible, unitCircumradiusTripleCount_eq]
  simp only [liesOnUnitCircle_iff]

/-- The exact answer to Erdős's 1975 value question. -/
theorem erdos_104.variants.unitCircumradiusTriples (n : ℕ) (hn : 2 ≤ n) :
    sSup {k | ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
      P.card = n ∧ ¬ LiesOnUnitCircle P ∧
        ((P.powersetCard 3).filter LiesOnUnitCircle).card = k} =
        if n ≤ 3 then 0
        else (n - 1).choose 3 + (n - 2) + (if (n - 1) % 3 = 0 then 1 else 0) := by
  rw [count_set_eq, ← Erdos104UnitTriples.gn]
  split
  · exact Erdos104UnitTriples.gn_eq_zero hn (by assumption)
  · exact Erdos104UnitTriples.gn_eq n (by omega)

end Erdos104

#print axioms Erdos104.erdos_104.variants.unitCircumradiusTriples
