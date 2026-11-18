module

import «104variantMaximizer»

open Erdos104 EuclideanGeometry
open scoped Classical

example (n : ℕ) (hn : 2 ≤ n) :
    sSup {k | ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
      P.card = n ∧ ¬ LiesOnUnitCircle P ∧
        ((P.powersetCard 3).filter LiesOnUnitCircle).card = k} =
        if n ≤ 3 then 0
        else (n - 1).choose 3 + (n - 2) + (if (n - 1) % 3 = 0 then 1 else 0) :=
  erdos_104.variants.unitCircumradiusTriples n hn

example (P : Finset (EuclideanSpace ℝ (Fin 2))) (hn : 4 ≤ P.card) (hP : ¬ LiesOnUnitCircle P)
    (hmax : ((P.powersetCard 3).filter LiesOnUnitCircle).card =
      sSup {k | ∃ Q : Finset (EuclideanSpace ℝ (Fin 2)),
        Q.card = P.card ∧ ¬ LiesOnUnitCircle Q ∧
          ((Q.powersetCard 3).filter LiesOnUnitCircle).card = k}) :
    ∃ s : Sphere (EuclideanSpace ℝ (Fin 2)), s.radius = 1 ∧
      (P.filter fun p => p ∈ s).card = P.card - 1 :=
  erdos_104.variants.unitCircumradiusTriplesMaximizer P hn hP hmax

#check @erdos_104.variants.unitCircumradiusTriples
#check @erdos_104.variants.unitCircumradiusTriplesMaximizer
#print axioms Erdos104.erdos_104.variants.unitCircumradiusTriples
#print axioms Erdos104.erdos_104.variants.unitCircumradiusTriplesMaximizer
