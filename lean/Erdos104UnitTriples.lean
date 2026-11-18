module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Erdős's unit-circumradius triple problem

In *Some problems on elementary geometry* (1975), p. 3, Erdős asks for the maximum
number of triples on unit circles, among finite planar sets not contained in a
unit circle. This is a related question from the source of Erdős Problem 104.

https://www.renyi.hu/~p_erdos/1975-41.pdf#page=2

The geometric arguments use complex coordinates. The public extremal theorems
use the isometric Euclidean plane, with one count per three-element subset.

To check this file, run `lake env lean Erdos104UnitTriples.lean` in a project
using Lean and Mathlib v4.35.0, giving the file's path if it is outside the project.
-/

@[expose] public section

namespace Erdos104UnitTriples

open Finset
open scoped BigOperators
noncomputable section
open Classical

/-- The points of a finite set on the unit circle with center `c`. -/
def onCircle {E : Type*} [MetricSpace E] (P : Finset E) (c : E) : Finset E :=
  P.filter fun a => dist a c = 1

/-- An admissible configuration is contained in no unit circle. -/
def Admissible {E : Type*} [MetricSpace E] (P : Finset E) : Prop :=
  ¬ ∃ c, ∀ a ∈ P, dist a c = 1

private def faces {α : Type*} (k : ℕ) (P : Finset α) (Q : Finset α → Prop) :
    Finset (Finset α) :=
  (P.powersetCard k).filter Q

private theorem mem_faces {α : Type*} {k : ℕ} {P A : Finset α} {Q : Finset α → Prop} :
    A ∈ faces k P Q ↔ A ⊆ P ∧ A.card = k ∧ Q A := by
  simp [faces, and_assoc]

private theorem faces_mono {α : Type*} {k : ℕ} {P S : Finset α}
    {Q : Finset α → Prop} (h : P ⊆ S) : faces k P Q ⊆ faces k S Q := by
  intro A hA
  obtain ⟨hAP, hk, hQ⟩ := mem_faces.mp hA
  exact mem_faces.mpr ⟨hAP.trans h, hk, hQ⟩

private theorem faces_card_le_choose {α : Type*} (k : ℕ) (P : Finset α)
    (Q : Finset α → Prop) : (faces k P Q).card ≤ P.card.choose k := by
  rw [← card_powersetCard]
  exact card_filter_le _ _

/-- Three-element subsets on a unit circle, counted without ordering their vertices. -/
def unitTriples {E : Type*} [MetricSpace E] (P : Finset E) : Finset (Finset E) :=
  (P.powersetCard 3).filter fun A => ∃ c, ∀ a ∈ A, dist a c = 1

/-- The claimed maximum for at least four points. -/
def answer (n : ℕ) : ℕ :=
  (n - 1).choose 3 + (n - 2) + if (n - 1) % 3 = 0 then 1 else 0

private def edgeBound (m : ℕ) : ℕ :=
  if m % 3 = 0 then m else m - 1

private theorem answer_eq (n : ℕ) (hn : 2 ≤ n) :
    answer n = (n - 1).choose 3 + edgeBound (n - 1) := by
  unfold answer edgeBound
  split <;> omega

/-! ## Reflection of unit circles through a pair of points -/

private abbrev Unit (z : ℂ) : Prop := ‖z‖ = 1

private theorem unit_neg {z : ℂ} (h : Unit z) : Unit (-z) := by
  simpa only [Unit, norm_neg] using h

private theorem unit_sub_swap {a b : ℂ} (h : Unit (a - b)) : Unit (b - a) := by
  change ‖b - a‖ = 1
  rw [norm_sub_rev]
  exact h

private theorem unit_mul_conj {z : ℂ} (hz : Unit z) :
    z * (starRingEnd ℂ) z = 1 := by
  rw [Complex.mul_conj', hz]
  norm_num

/-- Two unit vectors with a prescribed nonzero sum are unique up to exchange. -/
private theorem unit_pair {a b c d : ℂ} (ha : Unit a) (hb : Unit b) (hc : Unit c)
    (hd : Unit d) (hs : a + b = c + d) (hn : a + b ≠ 0) : a = c ∨ a = d := by
  have mul_sum {x y : ℂ} (hx : Unit x) (hy : Unit y) :
      (starRingEnd ℂ) (x + y) * (x * y) = x + y := by
    rw [map_add]
    linear_combination y * unit_mul_conj hx + x * unit_mul_conj hy
  have hp : a * b = c * d := by
    apply mul_left_cancel₀ (a := (starRingEnd ℂ) (a + b)) ((map_ne_zero _).2 hn)
    rw [mul_sum ha hb, hs, mul_sum hc hd]
  have hz : (a - c) * (a - d) = 0 := by
    linear_combination a * hs - hp
  simpa [mul_eq_zero, sub_eq_zero] using hz

/-- The centers of two unit circles through the same distinct pair are reflected in its midpoint. -/
private theorem center_eq_or_reflect {a b c d : ℂ} (hab : a ≠ b)
    (ha : Unit (a - c)) (hb : Unit (b - c))
    (ha' : Unit (a - d)) (hb' : Unit (b - d)) : d = c ∨ d = a + b - c := by
  have hsum : (a - c) + -(b - c) = (a - d) + -(b - d) := by ring
  have hne : (a - c) + -(b - c) ≠ 0 := by
    rw [show (a - c) + -(b - c) = a - b by ring]
    exact sub_ne_zero.mpr hab
  have h := unit_pair ha (unit_neg hb) ha' (unit_neg hb') hsum hne
  rcases h with h | h
  · left
    linear_combination h
  · right
    linear_combination -h

private theorem unit_reflect {a b c : ℂ} (hb : Unit (b - c)) :
    Unit (a - (a + b - c)) := by
  rw [show a - (a + b - c) = -(b - c) by ring]
  exact unit_neg hb

private theorem card_inter_circles {P : Finset ℂ} {c d : ℂ} (hcd : c ≠ d) :
    ((onCircle P c).filter fun a => dist a d = 1).card ≤ 2 := by
  let X := (onCircle P c).filter fun a => dist a d = 1
  change X.card ≤ 2
  by_cases h : X.Nonempty
  · obtain ⟨a, ha⟩ := h
    have ha' : Unit (a - c) ∧ Unit (a - d) := by
      simp only [X, onCircle, mem_filter, dist_eq_norm] at ha
      exact ⟨ha.1.2, ha.2⟩
    have hsub : X ⊆ {a, c + d - a} := by
      intro b hb
      simp only [X, onCircle, mem_filter, dist_eq_norm] at hb
      rcases center_eq_or_reflect (a := c) (b := d) (c := a) (d := b) hcd
          (unit_sub_swap ha'.1) (unit_sub_swap ha'.2)
          (unit_sub_swap hb.1.2) (unit_sub_swap hb.2) with hb' | hb'
      all_goals simp [hb']
    exact (card_le_card hsub).trans card_le_two
  · simp [not_nonempty_iff_eq_empty.mp h]

private theorem unique_circle {A : Finset ℂ} (hk : 3 ≤ A.card) {c d : ℂ}
    (hc : ∀ a ∈ A, dist a c = 1) (hd : ∀ a ∈ A, dist a d = 1) : c = d := by
  by_contra h
  have hs : A ⊆ (onCircle A c).filter fun a => dist a d = 1 := by
    intro a ha
    simp [onCircle, ha, hc a ha, hd a ha]
  have := (card_le_card hs).trans (card_inter_circles h)
  omega

/-! ## Counting finite families of subsets -/

private theorem card_delete_faces {α : Type*} (k : ℕ) (P : Finset α)
    (Q : Finset α → Prop) :
    (∑ a ∈ P, (faces k (P.erase a) Q).card) = (P.card - k) * (faces k P Q).card := by
  let F := faces k P Q
  let R : α → Finset α → Prop := fun a A => a ∉ A
  have habove (a : α) (ha : a ∈ P) : F.bipartiteAbove R a = faces k (P.erase a) Q := by
    ext A
    simp only [F, R, mem_bipartiteAbove, mem_faces, subset_iff, mem_erase]
    grind
  have hbelow (A : Finset α) (hA : A ∈ F) : (P.bipartiteBelow R A).card = P.card - k := by
    obtain ⟨hsub, hk, _⟩ := mem_faces.mp hA
    rw [show P.bipartiteBelow R A = P \ A by ext a; simp [R]]
    rw [card_sdiff_of_subset hsub, hk]
  calc
    _ = ∑ a ∈ P, (F.bipartiteAbove R a).card := sum_congr rfl fun a ha => congrArg card (habove a ha).symm
    _ = ∑ A ∈ F, (P.bipartiteBelow R A).card := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
    _ = _ := by rw [sum_congr rfl hbelow]; simp [Nat.mul_comm, F]

private abbrev Fits {E : Type*} [MetricSpace E] (A : Finset E) : Prop :=
  ∃ c, ∀ a ∈ A, dist a c = 1

private theorem card_faces_insert {α : Type*} (k : ℕ) (V : Finset α) {x : α}
    (hx : x ∉ V) (Q : Finset α → Prop) :
    (faces (k + 1) (insert x V) Q).card =
      (faces (k + 1) V Q).card + (faces k V fun A => Q (insert x A)).card := by
  let L := faces (k + 1) V Q
  let R := faces k V fun A => Q (insert x A)
  have hR (A : Finset α) (hA : A ∈ R) : x ∉ A :=
    fun hm => hx ((mem_faces.mp hA).1 hm)
  have hi : Set.InjOn (insert x) (R : Set (Finset α)) := by
    intro A hA B hB h
    have hA' := hR A (mem_coe.mp hA)
    have hB' := hR B (mem_coe.mp hB)
    simpa [erase_insert, hA', hB'] using congrArg (fun Z : Finset α => Z.erase x) h
  have he : faces (k + 1) (insert x V) Q = L ∪ R.image (insert x) := by
    ext A
    simp only [mem_union, mem_image, L, R, mem_faces]
    constructor
    · rintro ⟨hsub, hc, hq⟩
      by_cases h : x ∈ A
      · have hI := insert_erase h
        exact Or.inr ⟨A.erase x, ⟨by grind,
          by rw [card_erase_of_mem h, hc]; omega, by rw [hI]; exact hq⟩, hI⟩
      · exact Or.inl ⟨by grind, hc, hq⟩
    · rintro (⟨hsub, hc, hq⟩ | ⟨B, ⟨hsub, hc, hq⟩, rfl⟩)
      · exact ⟨hsub.trans (subset_insert _ _), hc, hq⟩
      · exact ⟨insert_subset_insert _ hsub, by rw [card_insert_of_notMem (fun hm => hx (hsub hm)), hc], hq⟩
  have hd : Disjoint L (R.image (insert x)) := by
    apply disjoint_left.mpr
    intro A hA hB
    obtain ⟨B, _, rfl⟩ := mem_image.mp hB
    exact hx ((mem_faces.mp hA).1 (mem_insert_self x B))
  rw [he, card_union_of_disjoint hd, card_image_of_injOn hi]

private theorem card_faces_union_ge {α : Type*} {V W : Finset α} {k : ℕ} (hk : 0 < k)
    (hd : Disjoint V W) (Q : Finset α → Prop) :
    (faces k V Q).card + (faces k W Q).card ≤ (faces k (V ∪ W) Q).card := by
  have hd' : Disjoint (faces k V Q) (faces k W Q) := by
    apply disjoint_left.mpr
    intro A hV hW
    obtain ⟨hVA, hc, _⟩ := mem_faces.mp hV
    obtain ⟨a, ha⟩ := card_pos.mp (hc ▸ hk)
    exact disjoint_left.mp hd (hVA ha) ((mem_faces.mp hW).1 ha)
  rw [← card_union_of_disjoint hd']
  exact card_le_card (union_subset (faces_mono subset_union_left) (faces_mono subset_union_right))

/-! ## Pairs that form a unit-circumradius triangle with a fixed outside point -/

private abbrev Adj (x c a b : ℂ) : Prop := a ≠ b ∧ Unit (x - (a + b - c))

private theorem adj_symm {x c a b : ℂ} (h : Adj x c a b) : Adj x c b a :=
  ⟨h.1.symm, by simpa only [add_comm b a] using h.2⟩

private def edgeFaces (V : Finset ℂ) (x c : ℂ) : Finset (Finset ℂ) :=
  faces 2 V fun A => ∀ a ∈ A, ∀ b ∈ A, a ≠ b → Adj x c a b

private theorem pair_edge {V : Finset ℂ} {x c a b : ℂ} (ha : a ∈ V) (hb : b ∈ V)
    (h : Adj x c a b) : {a, b} ∈ edgeFaces V x c := by
  apply mem_faces.mpr
  refine ⟨insert_subset ha (singleton_subset_iff.mpr hb), by simp [h.1], ?_⟩
  intro u hu v hv hne
  simp only [mem_insert, mem_singleton] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact (hne rfl).elim
  · exact h
  · exact adj_symm h
  · exact (hne rfl).elim

private def neighbors (V : Finset ℂ) (x c a : ℂ) : Finset ℂ :=
  V.filter (Adj x c a)

private theorem mem_neighbors {V : Finset ℂ} {x c a b : ℂ} :
    b ∈ neighbors V x c a ↔ b ∈ V ∧ Adj x c a b := mem_filter

private theorem sum_degrees (V : Finset ℂ) (x c : ℂ) :
    (∑ a ∈ V, (neighbors V x c a).card) = 2 * (edgeFaces V x c).card := by
  let F := edgeFaces V x c
  let R : ℂ → Finset ℂ → Prop := fun a A => a ∈ A
  have habove (a : ℂ) (ha : a ∈ V) :
      F.bipartiteAbove R a = (neighbors V x c a).image (fun b => {a, b}) := by
    ext A
    constructor
    · intro hA
      rw [mem_bipartiteAbove] at hA
      obtain ⟨hF, hmem⟩ := hA
      obtain ⟨hsub, hk, hQ⟩ := mem_faces.mp hF
      obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hk
      simp only [R, mem_insert, mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · exact mem_image.mpr ⟨v, mem_neighbors.mpr
          ⟨hsub (by simp), hQ _ (by simp) _ (by simp) huv⟩, rfl⟩
      · exact mem_image.mpr ⟨u, mem_neighbors.mpr
          ⟨hsub (by simp), hQ _ (by simp) _ (by simp) huv.symm⟩, by ext z; simp [or_comm]⟩
    · intro hA
      obtain ⟨b, hb, rfl⟩ := mem_image.mp hA
      obtain ⟨hb, hadj⟩ := mem_neighbors.mp hb
      rw [mem_bipartiteAbove]
      exact ⟨pair_edge ha hb hadj, by simp [R]⟩
  have hcard (a : ℂ) (ha : a ∈ V) : (F.bipartiteAbove R a).card =
      (neighbors V x c a).card := by
    rw [habove a ha]
    apply card_image_of_injOn
    intro b hb d hd he
    have hba := (mem_neighbors.mp (mem_coe.mp hb)).2.1.symm
    have hbd : b ∈ ({a, d} : Finset ℂ) := by
      change ({a, b} : Finset ℂ) = {a, d} at he
      rw [← he]; simp
    simpa [hba] using hbd
  have hbelow (A : Finset ℂ) (hA : A ∈ F) : (V.bipartiteBelow R A).card = 2 := by
    obtain ⟨hsub, hk, _⟩ := mem_faces.mp hA
    rw [show V.bipartiteBelow R A = A by
      ext a
      simp only [mem_bipartiteBelow, R]
      exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩, hk]
  calc
    _ = ∑ a ∈ V, (F.bipartiteAbove R a).card := sum_congr rfl fun a ha => (hcard a ha).symm
    _ = ∑ A ∈ F, (V.bipartiteBelow R A).card := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
    _ = _ := by rw [sum_congr rfl hbelow]; simp [F, Nat.mul_comm]

private theorem neighbor_pair_sum {x c a b d : ℂ} (hx : ¬ Unit (x - c))
    (ha : Unit (a - c)) (hb : Unit (b - c)) (hd : Unit (d - c))
    (hab : Adj x c a b) (had : Adj x c a d) (hne : b ≠ d) :
    a + b + d = x + 2 * c := by
  let e := x + c - a
  have hce : c ≠ e := by
    intro he
    have hax : a = x := by dsimp [e] at he; linear_combination he
    exact hx (hax ▸ ha)
  have heb : Unit (e - b) := by
    simpa only [e, show x + c - a - b = x - (a + b - c) by ring] using hab.2
  have hed : Unit (e - d) := by
    simpa only [e, show x + c - a - d = x - (a + d - c) by ring] using had.2
  rcases center_eq_or_reflect hce
      (unit_sub_swap hb) heb (unit_sub_swap hd) hed with h | h
  · exact (hne h.symm).elim
  · dsimp [e] at h
    linear_combination h

private theorem degree_le_two {V : Finset ℂ} {x c a : ℂ}
    (hx : ¬ Unit (x - c)) (hV : ∀ b ∈ V, Unit (b - c)) (ha : a ∈ V) :
    (neighbors V x c a).card ≤ 2 := by
  let N := neighbors V x c a
  change N.card ≤ 2
  by_cases he : N.Nonempty
  · obtain ⟨b, hb⟩ := he
    have hsub : N ⊆ {b, x + 2 * c - a - b} := by
      intro d hd
      by_cases h : b = d
      · simp [h]
      · obtain ⟨hbV, hab⟩ := mem_neighbors.mp hb
        obtain ⟨hdV, had⟩ := mem_neighbors.mp hd
        have hs := neighbor_pair_sum hx (hV a ha) (hV b hbV) (hV d hdV) hab had h
        have heq : d = x + 2 * c - a - b := by linear_combination hs
        simp [heq]
    exact (card_le_card hsub).trans card_le_two
  · simp [not_nonempty_iff_eq_empty.mp he]

private theorem close_neighbors {V : Finset ℂ} {x c a b d : ℂ}
    (hx : ¬ Unit (x - c)) (hV : ∀ b ∈ V, Unit (b - c)) (ha : a ∈ V)
    (hb : b ∈ neighbors V x c a) (hd : d ∈ neighbors V x c a) (hne : b ≠ d) :
    Adj x c b d := by
  obtain ⟨hbV, hab⟩ := mem_neighbors.mp hb
  obtain ⟨hdV, had⟩ := mem_neighbors.mp hd
  have he := neighbor_pair_sum hx (hV a ha) (hV b hbV) (hV d hdV) hab had hne
  refine ⟨hne, ?_⟩
  rw [show x - (b + d - c) = a - c by linear_combination -he]
  exact hV a ha

private theorem closed_eq_of_adj {V : Finset ℂ} {x c a b : ℂ}
    (hx : ¬ Unit (x - c)) (hV : ∀ b ∈ V, Unit (b - c))
    (ha : a ∈ V) (hb : b ∈ V) (hab : Adj x c a b) :
    insert a (neighbors V x c a) = insert b (neighbors V x c b) := by
  have incl {u v : ℂ} (hu : u ∈ V) (hv : v ∈ V) (huv : Adj x c u v) :
      insert u (neighbors V x c u) ⊆ insert v (neighbors V x c v) := by
    intro d hd
    rcases mem_insert.mp hd with rfl | hd
    · exact mem_insert_of_mem (mem_neighbors.mpr ⟨hu, adj_symm huv⟩)
    · by_cases hvd : v = d
      · simp [hvd]
      · exact mem_insert_of_mem (mem_neighbors.mpr ⟨(mem_neighbors.mp hd).1,
          close_neighbors hx hV hu (mem_neighbors.mpr ⟨hv, huv⟩) hd hvd⟩)
  exact Subset.antisymm (incl ha hb hab) (incl hb ha (adj_symm hab))

private theorem dvd_of_all_degree_two {V : Finset ℂ} {x c : ℂ}
    (hx : ¬ Unit (x - c)) (hV : ∀ b ∈ V, Unit (b - c))
    (hdeg : ∀ a ∈ V, (neighbors V x c a).card = 2) : 3 ∣ V.card := by
  let f := fun a => insert a (neighbors V x c a)
  have hf (S : Finset ℂ) (hS : S ∈ V.image f) : (V.filter fun a => f a = S).card = 3 := by
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hS
    have he : (V.filter fun b => f b = f a) = f a := by
      ext b
      constructor
      · intro hb
        have he := (mem_filter.mp hb).2
        rw [← he]
        exact mem_insert_self _ _
      · intro hb
        rcases mem_insert.mp hb with rfl | hb
        · exact mem_filter.mpr ⟨ha, rfl⟩
        · obtain ⟨hbV, hab⟩ := mem_neighbors.mp hb
          exact mem_filter.mpr ⟨hbV, (closed_eq_of_adj hx hV ha hbV hab).symm⟩
    rw [he]
    have haN : a ∉ neighbors V x c a := fun h => (mem_neighbors.mp h).2.1 rfl
    simp [f, card_insert_of_notMem haN, hdeg a ha]
  rw [card_eq_sum_card_fiberwise
    (s := V) (t := V.image f) (f := f) (fun a ha => mem_image_of_mem f ha),
    sum_congr rfl hf]
  simp

private theorem edgeFaces_le {V : Finset ℂ} {x c : ℂ}
    (hx : ¬ Unit (x - c)) (hV : ∀ b ∈ V, Unit (b - c)) :
    (edgeFaces V x c).card ≤ edgeBound V.card := by
  have hsum := sum_degrees V x c
  have hdeg (a : ℂ) (ha : a ∈ V) := degree_le_two hx hV ha
  have hle : (∑ a ∈ V, (neighbors V x c a).card) ≤ V.card * 2 := by
    simpa using sum_le_sum hdeg
  have hcard : (edgeFaces V x c).card ≤ V.card := by omega
  unfold edgeBound
  split
  · exact hcard
  · rename_i hmod
    suffices h : (edgeFaces V x c).card ≠ V.card by omega
    intro he
    have hall (a : ℂ) (ha : a ∈ V) : (neighbors V x c a).card = 2 := by
      by_contra h
      have hl : (neighbors V x c a).card ≤ 1 := by have := hdeg a ha; omega
      have hh : (∑ b ∈ V.erase a, (neighbors V x c b).card) ≤ (V.card - 1) * 2 := by
        simpa [card_erase_of_mem ha] using
          (sum_le_sum (s := V.erase a) fun b hb => hdeg b (mem_of_mem_erase hb))
      rw [← sum_erase_add _ _ ha] at hsum
      have := card_pos.mpr ⟨a, ha⟩
      omega
    exact hmod (Nat.dvd_iff_mod_eq_zero.mp (dvd_of_all_degree_two hx hV hall))

/-! ## The upper bound for all configurations -/

private theorem fits_pair_iff {x c a b : ℂ} (hx : ¬ Unit (x - c))
    (ha : Unit (a - c)) (hb : Unit (b - c)) (hab : a ≠ b) :
    Fits ({x, a, b} : Finset ℂ) ↔ Adj x c a b := by
  constructor
  · rintro ⟨d, hd⟩
    have hx' : Unit (x - d) := by simpa [dist_eq_norm] using hd x (by simp)
    have ha' : Unit (a - d) := by simpa [dist_eq_norm] using hd a (by simp)
    have hb' : Unit (b - d) := by simpa [dist_eq_norm] using hd b (by simp)
    rcases center_eq_or_reflect hab ha hb ha' hb' with rfl | h
    · exact (hx hx').elim
    · exact ⟨hab, h ▸ hx'⟩
  · intro h
    refine ⟨a + b - c, ?_⟩
    intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with he | he | he <;> subst y
    · simpa only [dist_eq_norm] using h.2
    · rw [dist_eq_norm]
      exact unit_reflect hb
    · rw [dist_eq_norm, show b - (a + b - c) = -(a - c) by ring]
      exact unit_neg ha

private theorem outside_faces_eq {V : Finset ℂ} {x c : ℂ}
    (hx : ¬ Unit (x - c)) (hV : ∀ a ∈ V, Unit (a - c)) :
    (faces 2 V fun A => Fits (insert x A)) = edgeFaces V x c := by
  ext A
  simp only [edgeFaces, mem_faces]
  by_cases h : A ⊆ V ∧ A.card = 2
  · obtain ⟨hsub, hk⟩ := h
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hk
    have haV : a ∈ V := hsub (by simp)
    have hbV : b ∈ V := hsub (by simp)
    simp only [hsub, true_and, hk]
    rw [fits_pair_iff hx (hV a haV) (hV b hbV) hab]
    constructor
    · intro he u hu v hv hne
      simp only [mem_insert, mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact (hne rfl).elim
      · exact he
      · exact adj_symm he
      · exact (hne rfl).elim
    · intro he
      exact he a (by simp) b (by simp) hab
  · grind

private theorem triples_count_insert {V : Finset ℂ} {x c : ℂ}
    (hx : ¬ Unit (x - c)) (hV : ∀ a ∈ V, Unit (a - c)) :
    (unitTriples (insert x V)).card = V.card.choose 3 + (edgeFaces V x c).card := by
  have hxV : x ∉ V := fun hm => hx (hV x hm)
  have htrip : unitTriples V = V.powersetCard 3 := by
    ext A
    simp only [unitTriples, mem_filter, mem_powersetCard, and_assoc]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, c,
      fun a ha => by simpa only [dist_eq_norm] using hV a (h.1 ha)⟩⟩
  change (faces (2 + 1) (insert x V) Fits).card = _
  rw [card_faces_insert 2 V hxV Fits, outside_faces_eq hx hV]
  change (unitTriples V).card + _ = _
  rw [htrip, card_powersetCard]

private theorem onCircle_subset {P : Finset ℂ} (c : ℂ) : onCircle P c ⊆ P :=
  filter_subset _ _

private theorem circle_card_lt {P : Finset ℂ} (hP : Admissible P) (c : ℂ) :
    (onCircle P c).card < P.card := by
  apply card_lt_card
  refine (ssubset_iff_subset_ne).2 ⟨onCircle_subset c, ?_⟩
  intro h
  refine hP ⟨c, fun a ha => ?_⟩
  have hac : a ∈ onCircle P c := by rw [h]; exact ha
  exact (mem_filter.mp hac).2

private theorem onCircle_unit {P : Finset ℂ} {c : ℂ} :
    ∀ a ∈ onCircle P c, Unit (a - c) := fun a ha => by
  simpa only [dist_eq_norm] using (mem_filter.mp ha).2

private theorem split_circle_one {P : Finset ℂ} {c : ℂ} (hP : Admissible P)
    (hc : (onCircle P c).card = P.card - 1) :
    ∃ x, ¬ Unit (x - c) ∧ P = insert x (onCircle P c) := by
  have hpos := circle_card_lt hP c
  have hcard : (P \ onCircle P c).card = 1 := by
    rw [card_sdiff_of_subset (onCircle_subset c), hc]
    omega
  obtain ⟨x, hx⟩ := card_eq_one.mp hcard
  have hx' : x ∈ P \ onCircle P c := by simp [hx]
  refine ⟨x, fun hu => (mem_sdiff.mp hx').2 (mem_filter.mpr ⟨(mem_sdiff.mp hx').1,
    by simpa only [dist_eq_norm] using hu⟩), ?_⟩
  rw [← singleton_union, ← hx, sdiff_union_of_subset (onCircle_subset c)]

private theorem count_le_of_circle_one {P : Finset ℂ} {c : ℂ} (hP : Admissible P)
    (hn : 2 ≤ P.card) (hc : (onCircle P c).card = P.card - 1) :
    (unitTriples P).card ≤ answer P.card := by
  obtain ⟨x, hx, he⟩ := split_circle_one hP hc
  have hcount := triples_count_insert hx (onCircle_unit (P := P))
  rw [← he, hc] at hcount
  rw [hcount, answer_eq _ hn]
  have := edgeFaces_le hx (onCircle_unit (P := P))
  simpa only [hc, Nat.add_le_add_iff_left] using this

private theorem pair_multiplicity {P : Finset ℂ} (hsmall : ∀ c, (onCircle P c).card ≤ 3)
    {B : Finset ℂ} (hB : B.card = 2) :
    ((unitTriples P).filter fun A => B ⊆ A).card ≤ 2 := by
  let F := (unitTriples P).filter fun A => B ⊆ A
  change F.card ≤ 2
  by_cases hF : F.Nonempty
  · obtain ⟨A, hA⟩ := hF
    obtain ⟨_, hAfit⟩ := mem_filter.mp hA
    obtain ⟨_, _, c, hc⟩ := mem_faces.mp (mem_filter.mp hA).1
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hB
    have ha := hc a (hAfit (mem_insert_self a {b}))
    have hb := hc b (hAfit (by simp))
    have hsub : F ⊆ {onCircle P c, onCircle P (a + b - c)} := by
      intro T hT
      obtain ⟨hTp, hTb⟩ := mem_filter.mp hT
      obtain ⟨hsub, hk, d, hd⟩ := mem_faces.mp hTp
      have hTd : T = onCircle P d := by
        apply eq_of_subset_of_card_le
        · exact fun v hv => mem_filter.mpr ⟨hsub hv, hd v hv⟩
        · rw [hk]
          exact hsmall d
      have hcand := center_eq_or_reflect hab
        (by simpa only [dist_eq_norm] using ha) (by simpa only [dist_eq_norm] using hb)
        (by simpa only [dist_eq_norm] using hd a (hTb (by simp)))
        (by simpa only [dist_eq_norm] using hd b (hTb (by simp)))
      rw [hTd]
      rcases hcand with rfl | rfl <;> simp
    exact (card_le_card hsub).trans card_le_two
  · simp [not_nonempty_iff_eq_empty.mp hF]

private theorem pair_count_bound {P : Finset ℂ} (hsmall : ∀ c, (onCircle P c).card ≤ 3) :
    3 * (unitTriples P).card ≤ 2 * P.card.choose 2 := by
  let R : Finset ℂ → Finset ℂ → Prop := fun A B => B ⊆ A
  let F := unitTriples P
  let B := P.powersetCard 2
  have hA (A : Finset ℂ) (ha : A ∈ F) : (B.bipartiteAbove R A).card = 3 := by
    obtain ⟨hsub, hk, _⟩ := mem_faces.mp ha
    rw [show B.bipartiteAbove R A = A.powersetCard 2 by
      ext T
      simp only [B, R, mem_bipartiteAbove, mem_powersetCard]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans hsub, h.2⟩, h.1⟩⟩,
      card_powersetCard, hk]
    decide
  have hB (D : Finset ℂ) (hd : D ∈ B) : (F.bipartiteBelow R D).card ≤ 2 :=
    pair_multiplicity hsmall (mem_powersetCard.mp hd).2
  calc
    _ = ∑ A ∈ F, (B.bipartiteAbove R A).card := by rw [sum_congr rfl hA]; simp [F, Nat.mul_comm]
    _ = ∑ D ∈ B, (F.bipartiteBelow R D).card := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
    _ ≤ ∑ _ ∈ B, (2 : ℕ) := sum_le_sum hB
    _ = _ := by simp [B, Nat.mul_comm]

private theorem circle_small_of_no_near {P : Finset ℂ} (hP : Admissible P)
    (hnear : ¬ ∃ c, (onCircle P c).card = P.card - 1) (c : ℂ) :
    (onCircle P c).card ≤ P.card - 2 := by
  have hlt := circle_card_lt hP c
  have hne : (onCircle P c).card ≠ P.card - 1 := fun he => hnear ⟨c, he⟩
  omega

private theorem admissible_erase {P : Finset ℂ} (hP : Admissible P)
    (hnear : ¬ ∃ c, (onCircle P c).card = P.card - 1) {a : ℂ} (ha : a ∈ P) :
    Admissible (P.erase a) := by
  rintro ⟨c, hc⟩
  have hsub : P.erase a ⊆ onCircle P c :=
    fun b hb => mem_filter.mpr ⟨mem_of_mem_erase hb, hc b hb⟩
  have hle := card_le_card hsub
  rw [card_erase_of_mem ha] at hle
  have hlt := circle_card_lt hP c
  exact hnear ⟨c, by omega⟩

private theorem deletion_bound {P : Finset ℂ} (B : ℕ)
    (h : ∀ a ∈ P, (unitTriples (P.erase a)).card ≤ B) :
    (P.card - 3) * (unitTriples P).card ≤ P.card * B := by
  have he : (∑ a ∈ P, (unitTriples (P.erase a)).card) =
      (P.card - 3) * (unitTriples P).card := card_delete_faces 3 P Fits
  rw [← he]
  exact (sum_le_sum h).trans (by simp)

/-- The strict margin in the deletion step for ten or more points. -/
private theorem deletion_strict_large (n : ℕ) (hn : 10 ≤ n) :
    n * answer (n - 1) < (n - 3) * answer n := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ n by omega)
  rw [Nat.add_comm 3 t] at hn ⊢
  have ht : 7 ≤ t := by omega
  have hprev : (t + 3 - 1 - 1) = t + 1 := by omega
  have hnow : (t + 3 - 1) = t + 2 := by omega
  rw [answer_eq _ (by omega), answer_eq _ (by omega), hprev, hnow,
    Nat.add_sub_cancel]
  have hpascal := Nat.choose_succ_succ (t + 1) 2
  have hc₁ := Nat.add_one_mul_choose_eq t 2
  have hc₂ := Nat.choose_mul_succ_eq t 2
  have hc₃ := Nat.add_one_mul_choose_eq t 1
  rw [Nat.choose_one_right] at hc₃
  have hcf : (t + 1) - 2 + 1 = t := by omega
  have hgap : 3 * (t + 1).choose 3 + (t + 1).choose 2 =
      t * (t + 1).choose 2 := by
    nlinarith only [hc₁, hc₂,
      show ((t + 1) - 2) * (t + 1).choose 2 + (t + 1).choose 2 =
        t * (t + 1).choose 2 by
        calc
          _ = (t + 1 - 2 + 1) * (t + 1).choose 2 := by ring
          _ = _ := by rw [hcf]]
  have htop : edgeBound (t + 1) ≤ t + 1 := by unfold edgeBound; split <;> omega
  have hbot : t + 1 ≤ edgeBound (t + 2) := by unfold edgeBound; split <;> omega
  have hpos : 0 < (t + 1).choose 2 - 3 * (t + 1) := by
    have hm : (t + 1) * 7 ≤ (t + 1) * t := Nat.mul_le_mul_left _ ht
    have hpp : 0 < t + 1 := by omega
    have hl : 3 * (t + 1) < (t + 1).choose 2 := by nlinarith only [hc₃, hm, hpp]
    omega
  nlinarith only [hpascal, hgap, Nat.mul_le_mul_left (t + 3) htop,
    Nat.mul_le_mul_left t hbot, show 3 * (t + 1) < (t + 1).choose 2 by omega,
    congrArg (fun z : ℕ => t * z) hpascal]

private theorem deletion_step (n : ℕ) (hn : 6 ≤ n) :
    n * answer (n - 1) < (n - 3) * (answer n + 1) := by
  by_cases hh : 10 ≤ n
  · have hm := deletion_strict_large n hh
    have he := Nat.mul_le_mul_left (n - 3) (Nat.le_succ (answer n))
    exact hm.trans_le he
  · interval_cases n <;> decide

/-- The global upper bound for the triple problem. -/
theorem complex_upper (P : Finset ℂ) (hn : 4 ≤ P.card) (hP : Admissible P) :
    (unitTriples P).card ≤ answer P.card := by
  suffices H : ∀ n, ∀ A : Finset ℂ, A.card = n → 4 ≤ n → Admissible A →
      (unitTriples A).card ≤ answer n by exact H _ P rfl hn hP
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A hA hn hAd
    by_cases hnear : ∃ c, (onCircle A c).card = A.card - 1
    · obtain ⟨c, hc⟩ := hnear
      rw [← hA]
      exact count_le_of_circle_one hAd (by omega) hc
    by_cases h4 : n = 4
    · rw [h4] at hA ⊢
      have hle := faces_card_le_choose 3 A (Q := Fits)
      change (unitTriples A).card ≤ A.card.choose 3 at hle
      rw [hA] at hle
      exact hle
    by_cases h5 : n = 5
    · rw [h5] at hA ⊢
      have hle := pair_count_bound (P := A) (fun c => by
        have := circle_small_of_no_near hAd hnear c
        omega)
      rw [hA] at hle
      norm_num [answer, Nat.choose] at hle ⊢
      omega
    have hn6 : 6 ≤ n := by omega
    have hd := deletion_bound (P := A) (answer (n - 1)) (fun a ha => by
      have hc := card_erase_of_mem ha
      rw [hA] at hc
      exact ih (n - 1) (by omega) _ hc (by omega) (admissible_erase hAd hnear ha))
    rw [hA] at hd
    have hs := deletion_step n hn6
    by_contra! ho
    have hm := Nat.mul_le_mul_left (n - 3) (show answer n + 1 ≤ (unitTriples A).card by omega)
    omega

/-! ## Attainment by packing equilateral triples on a circle -/

private theorem unit_iff_normSq {z : ℂ} : Unit z ↔ Complex.normSq z = 1 := by
  change ‖z‖ = 1 ↔ Complex.normSq z = 1
  rw [Complex.normSq_eq_norm_sq]
  constructor
  · intro h
    norm_num [h]
  · intro h
    nlinarith [norm_nonneg z]

private theorem fresh_unit (F : Finset ℂ) : ∃ z, Unit z ∧ z ∉ F := by
  obtain ⟨t, ht, hf⟩ := (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).exists_notMem_finset
    (F.image Complex.im)
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2
  let z : ℂ := ⟨Real.sqrt (1 - t ^ 2), t⟩
  refine ⟨z, unit_iff_normSq.mpr ?_, fun hz => hf (mem_image_of_mem Complex.im hz)⟩
  have h := Real.sq_sqrt (show 0 ≤ 1 - t ^ 2 by nlinarith)
  change Real.sqrt (1 - t ^ 2) * Real.sqrt (1 - t ^ 2) + t * t = 1
  nlinarith only [h]

private def rotation : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

private theorem rotation_poly : rotation ^ 2 + rotation + 1 = 0 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  apply Complex.ext <;>
    norm_num [rotation, pow_two, Complex.mul_re, Complex.mul_im] <;> nlinarith only [h]

private theorem rotation_cube : rotation ^ 3 = 1 := by
  linear_combination (rotation - 1) * rotation_poly

private theorem rotation_ne_one : rotation ≠ 1 := by
  intro h
  have he := congrArg Complex.re h
  norm_num [rotation] at he

private theorem rotation_unit : Unit rotation := by
  apply unit_iff_normSq.mpr
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  change (-1 / 2 : ℝ) * (-1 / 2) + (Real.sqrt 3 / 2) * (Real.sqrt 3 / 2) = 1
  nlinarith only [h]

private theorem fresh_orbit (F : Finset ℂ) :
    ∃ S : Finset ℂ, S.card = 3 ∧ Disjoint S F ∧ (∀ a ∈ S, Unit a) ∧
      ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Adj 0 0 a b := by
  let w := rotation
  let G := F ∪ F.image (w * ·) ∪ F.image (w ^ 2 * ·)
  obtain ⟨z, hz, hzG⟩ := fresh_unit G
  have hz0 : z ≠ 0 := by intro h; norm_num [h, Unit] at hz
  have hw0 : w ≠ 0 := by
    intro h
    have hu : Unit w := rotation_unit
    norm_num [h, Unit] at hu
  have hw1 : w ≠ 1 := rotation_ne_one
  have hw3 : w ^ 3 = 1 := rotation_cube
  have hsum : z + w * z + w ^ 2 * z = 0 := by
    linear_combination z * rotation_poly
  have h₀₁ : z ≠ w * z := by
    intro h
    apply hw1
    apply mul_right_cancel₀ hz0
    simpa using h.symm
  have h₀₂ : z ≠ w ^ 2 * z := by
    intro h
    have hw2 : w ^ 2 = 1 := mul_right_cancel₀ hz0 (by simpa using h.symm)
    exact hw1 (by calc
      w = w ^ 2 * w := by rw [hw2, one_mul]
      _ = 1 := by rw [← pow_succ, hw3])
  have h₁₂ : w * z ≠ w ^ 2 * z := by
    intro h
    apply h₀₁
    apply mul_left_cancel₀ hw0
    simpa only [pow_two, mul_assoc] using h
  have hu₁ : Unit (w * z) := by
    change ‖w * z‖ = 1
    rw [norm_mul, (show ‖w‖ = 1 from rotation_unit), hz, one_mul]
  have hu₂ : Unit (w ^ 2 * z) := by
    change ‖w ^ 2 * z‖ = 1
    rw [norm_mul, norm_pow, (show ‖w‖ = 1 from rotation_unit), hz]
    norm_num
  have hnot₀ : z ∉ F := by intro he; apply hzG; simp [G, he]
  have hnot₁ : w * z ∉ F := by
    intro he
    apply hzG
    have heq : w ^ 2 * (w * z) = z := by rw [← mul_assoc, ← pow_succ, hw3, one_mul]
    exact mem_union_right _ (mem_image.mpr ⟨_, he, heq⟩)
  have hnot₂ : w ^ 2 * z ∉ F := by
    intro he
    apply hzG
    have heq : w * (w ^ 2 * z) = z := by
      rw [← mul_assoc, mul_comm w, ← pow_succ, hw3, one_mul]
    exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨_, he, heq⟩))
  let S : Finset ℂ := {z, w * z, w ^ 2 * z}
  refine ⟨S, card_eq_three.mpr ⟨_, _, _, h₀₁, h₀₂, h₁₂, rfl⟩, ?_, ?_, ?_⟩
  · exact disjoint_left.mpr fun a ha hf => by
      simp only [S, mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · exact hnot₀ hf
      · exact hnot₁ hf
      · exact hnot₂ hf
  · intro a ha
    simp only [S, mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact hz
    · exact hu₁
    · exact hu₂
  · have h01 : Adj 0 0 z (w * z) := ⟨h₀₁, by
      rw [show (0 : ℂ) - (z + w * z - 0) = w ^ 2 * z by linear_combination -hsum]
      exact hu₂⟩
    have h02 : Adj 0 0 z (w ^ 2 * z) := ⟨h₀₂, by
      rw [show (0 : ℂ) - (z + w ^ 2 * z - 0) = w * z by linear_combination -hsum]
      exact hu₁⟩
    have h12 : Adj 0 0 (w * z) (w ^ 2 * z) := ⟨h₁₂, by
      rw [show (0 : ℂ) - (w * z + w ^ 2 * z - 0) = z by linear_combination -hsum]
      exact hz⟩
    intro a ha b hb hne
    simp only [S, mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first | exact (hne rfl).elim | exact h01 | exact h02 | exact h12 |
        exact adj_symm h01 | exact adj_symm h02 | exact adj_symm h12

private theorem all_edges {S V : Finset ℂ} (hSV : V ⊆ S)
    (hS : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Adj 0 0 a b) :
    (edgeFaces V 0 0).card = V.card.choose 2 := by
  rw [← card_powersetCard]
  congr 1
  ext A
  simp only [edgeFaces, mem_faces, mem_powersetCard]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2,
    fun a ha b hb => hS a (hSV (h.1 ha)) b (hSV (h.1 hb))⟩⟩

private theorem edgeBound_add_three (m : ℕ) : edgeBound (m + 3) = edgeBound m + 3 := by
  have hmod : (m + 3) % 3 = m % 3 := by omega
  unfold edgeBound
  rw [hmod]
  split <;> omega

private theorem orbit_packing (m : ℕ) (F : Finset ℂ) :
    ∃ V : Finset ℂ, V.card = m ∧ Disjoint V F ∧ (∀ a ∈ V, Unit a) ∧
      edgeBound m ≤ (edgeFaces V 0 0).card := by
  induction m using Nat.strong_induction_on generalizing F with
  | h m ih =>
    obtain ⟨S, hS, hd, hu, he⟩ := fresh_orbit F
    by_cases hm : m < 3
    · obtain ⟨V, hv⟩ := powersetCard_nonempty.mpr (show m ≤ S.card by omega)
      obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hv
      refine ⟨V, hcard, disjoint_of_subset_left hsub hd, fun a ha => hu a (hsub ha), ?_⟩
      rw [all_edges hsub he, hcard]
      interval_cases m <;> decide
    · obtain ⟨V, hV, hdV, huV, hlV⟩ := ih (m - 3) (by omega) (F ∪ S)
      have hd' : Disjoint S V := (disjoint_union_right.mp hdV).2.symm
      refine ⟨S ∪ V, by rw [card_union_of_disjoint hd', hS, hV]; omega,
        disjoint_union_left.mpr ⟨hd, (disjoint_union_right.mp hdV).1⟩, ?_, ?_⟩
      · intro a ha
        rcases mem_union.mp ha with ha | ha
        · exact hu a ha
        · exact huV a ha
      · have hle := card_faces_union_ge (k := 2) (by decide) hd'
          (fun A => ∀ a ∈ A, ∀ b ∈ A, a ≠ b → Adj 0 0 a b)
        change (edgeFaces S 0 0).card + (edgeFaces V 0 0).card ≤
          (edgeFaces (S ∪ V) 0 0).card at hle
        rw [all_edges Subset.rfl he, hS] at hle
        have hr : edgeBound m = edgeBound (m - 3) + 3 := by
          have hEq : m - 3 + 3 = m := by omega
          rw [← edgeBound_add_three, hEq]
        norm_num [Nat.choose] at hle
        omega

/-- A configuration on a unit circle together with its center attains the bound. -/
theorem complex_attains (n : ℕ) (hn : 4 ≤ n) :
    ∃ P : Finset ℂ, P.card = n ∧ Admissible P ∧ (unitTriples P).card = answer n := by
  obtain ⟨V, hV, _, hu, hE⟩ := orbit_packing (n - 1) ∅
  have hzero : ¬ Unit ((0 : ℂ) - 0) := by norm_num [Unit]
  have hu' (a : ℂ) (ha : a ∈ V) : Unit (a - 0) := by simpa only [sub_zero] using hu a ha
  have hz : (0 : ℂ) ∉ V := fun h => hzero (hu' 0 h)
  have hc : (insert (0 : ℂ) V).card = n := by rw [card_insert_of_notMem hz, hV]; omega
  have hAd : Admissible (insert (0 : ℂ) V) := by
    rintro ⟨c, hall⟩
    have hC := unique_circle (A := V) (by omega)
      (fun a ha => by simpa only [dist_eq_norm] using hu' a ha)
      (fun a ha => hall a (mem_insert_of_mem ha))
    subst c
    have hz' := hall 0 (mem_insert_self _ _)
    norm_num at hz'
  refine ⟨insert 0 V, hc, hAd, le_antisymm ?_ ?_⟩
  · simpa only [hc] using complex_upper _ (by omega) hAd
  · rw [triples_count_insert hzero hu', hV, answer_eq _ (by omega)]
    exact Nat.add_le_add_left hE _

/-! ## The equality case with two points off the circle -/

private def mixedVertices (V : Finset ℂ) (x y : ℂ) : Finset ℂ :=
  V.filter fun a => Fits ({x, y, a} : Finset ℂ)

private theorem mixed_card_le_four (V : Finset ℂ) {x y c : ℂ} (hxy : x ≠ y)
    (hx : ¬ Unit (x - c)) (hV : ∀ a ∈ V, Unit (a - c)) :
    (mixedVertices V x y).card ≤ 4 := by
  by_cases hne : (mixedVertices V x y).Nonempty
  · obtain ⟨a, ha⟩ := hne
    obtain ⟨u, hu⟩ := (mem_filter.mp ha).2
    let I := fun d => V.filter (fun (z : ℂ) => dist z d = 1)
    have hu' : Unit (x - u) := by simpa only [dist_eq_norm] using hu x (by simp)
    have hv' : Unit (x - (x + y - u)) :=
      unit_reflect (by simpa only [dist_eq_norm] using hu y (by simp))
    have hsize {d : ℂ} (hd : Unit (x - d)) : (I d).card ≤ 2 := by
      have hcd : c ≠ d := fun he => hx (he.symm ▸ hd)
      apply le_trans (card_le_card (t := (onCircle V c).filter fun a => dist a d = 1) ?_)
        (card_inter_circles hcd)
      intro z hz
      simp only [I, onCircle, mem_filter] at hz ⊢
      exact ⟨⟨hz.1, by simpa only [dist_eq_norm] using hV z hz.1⟩, hz.2⟩
    have hsub : mixedVertices V x y ⊆ I u ∪ I (x + y - u) := by
      intro b hb
      obtain ⟨hbV, d, hd⟩ := mem_filter.mp hb
      have he := center_eq_or_reflect hxy hu'
        (by simpa only [dist_eq_norm] using hu y (by simp))
        (by simpa only [dist_eq_norm] using hd x (by simp))
        (by simpa only [dist_eq_norm] using hd y (by simp))
      have hm : b ∈ I d := mem_filter.mpr ⟨hbV, hd b (by simp)⟩
      rcases he with rfl | rfl
      · exact mem_union_left _ hm
      · exact mem_union_right _ hm
    exact (card_le_card hsub).trans ((card_union_le _ _).trans (by
      have h1 := hsize hu'; have h2 := hsize hv'; omega))
  · simp [not_nonempty_iff_eq_empty.mp hne]

private theorem triples_count_two {V : Finset ℂ} {x y c : ℂ} (hxy : x ≠ y)
    (hx : ¬ Unit (x - c)) (hy : ¬ Unit (y - c)) (hV : ∀ a ∈ V, Unit (a - c)) :
    (unitTriples (insert x (insert y V))).card =
      V.card.choose 3 + (edgeFaces V y c).card + (edgeFaces V x c).card +
        (mixedVertices V x y).card := by
  have hxV : x ∉ V := fun h => hx (hV x h)
  have hyV : y ∉ V := fun h => hy (hV y h)
  have hxV' : x ∉ insert y V := by simp [hxy, hxV]
  change (faces (2 + 1) (insert x (insert y V)) Fits).card = _
  rw [card_faces_insert 2 (insert y V) hxV' Fits,
    card_faces_insert 1 V hyV (fun A => Fits (insert x A)), outside_faces_eq hx hV]
  change (unitTriples (insert y V)).card + _ = _
  rw [triples_count_insert hy hV]
  have he : (faces 1 V fun A => Fits (insert x (insert y A))) =
      (mixedVertices V x y).image singleton := by
    ext A
    constructor
    · intro ha
      obtain ⟨hsub, hc, hfit⟩ := mem_faces.mp ha
      obtain ⟨a, rfl⟩ := card_eq_one.mp hc
      exact mem_image.mpr ⟨a, mem_filter.mpr ⟨hsub (by simp), hfit⟩, rfl⟩
    · intro ha
      rw [mem_image] at ha
      obtain ⟨a, hmem, hA⟩ := ha
      obtain ⟨haV, hf⟩ := mem_filter.mp (show a ∈ mixedVertices V x y from hmem)
      rw [← hA]
      exact mem_faces.mpr ⟨singleton_subset_iff.mpr haV, card_singleton _, hf⟩
  rw [he, card_image_of_injective _ (fun a b h => by simpa using h)]
  omega

private theorem split_circle_two {P : Finset ℂ} {c : ℂ}
    (hc : (onCircle P c).card = P.card - 2) (hn : 2 ≤ P.card) :
    ∃ x y, x ≠ y ∧ ¬ Unit (x - c) ∧ ¬ Unit (y - c) ∧ P = insert x (insert y (onCircle P c)) := by
  have hp : (P \ onCircle P c).card = 2 := by
    rw [card_sdiff_of_subset (onCircle_subset c), hc]
    omega
  obtain ⟨x, y, hxy, he⟩ := card_eq_two.mp hp
  have hout {a : ℂ} (ha : a ∈ P \ onCircle P c) : ¬ Unit (a - c) :=
    fun hu => (mem_sdiff.mp ha).2 (mem_filter.mpr ⟨(mem_sdiff.mp ha).1,
      by simpa only [dist_eq_norm] using hu⟩)
  refine ⟨x, y, hxy, hout (by simp [he]), hout (by simp [he]), ?_⟩
  calc
    P = (P \ onCircle P c) ∪ onCircle P c := (sdiff_union_of_subset (onCircle_subset c)).symm
    _ = {x, y} ∪ onCircle P c := by rw [he]
    _ = insert x (insert y (onCircle P c)) := by ext z; simp

private theorem triangle_of_three_edges {V : Finset ℂ} {x c : ℂ}
    (hcard : V.card = 4) (hx : ¬ Unit (x - c)) (hV : ∀ a ∈ V, Unit (a - c))
    (hE : 3 ≤ (edgeFaces V x c).card) :
    ∃ T : Finset ℂ, T ⊆ V ∧ T.card = 3 ∧ (∑ z ∈ T, z) = x + 2 * c := by
  have hdeg : ∃ a ∈ V, (neighbors V x c a).card = 2 := by
    by_contra! hh
    have hle (a : ℂ) (ha : a ∈ V) : (neighbors V x c a).card ≤ 1 := by
      have := degree_le_two hx hV ha
      have := hh a ha
      omega
    have hs : (∑ a ∈ V, (neighbors V x c a).card) ≤ V.card := by simpa using sum_le_sum hle
    rw [sum_degrees] at hs
    omega
  obtain ⟨a, ha, hna⟩ := hdeg
  obtain ⟨b, d, hbd, hn⟩ := card_eq_two.mp hna
  have hbN : b ∈ neighbors V x c a := by simp [hn]
  have hdN : d ∈ neighbors V x c a := by simp [hn]
  obtain ⟨hb, hab⟩ := mem_neighbors.mp hbN
  obtain ⟨hd, had⟩ := mem_neighbors.mp hdN
  refine ⟨{a, b, d}, insert_subset ha (insert_subset hb (singleton_subset_iff.mpr hd)),
    card_eq_three.mpr ⟨_, _, _, hab.1, had.1, hbd, rfl⟩, ?_⟩
  rw [sum_insert (by simp [hab.1, had.1]), sum_insert (by simp [hbd]), sum_singleton, ← add_assoc]
  exact neighbor_pair_sum hx (hV a ha) (hV b hb) (hV d hd) hab had hbd

private theorem mixed_card_lt_four {V : Finset ℂ} {x y c : ℂ}
    (hcard : V.card = 4) (hxy : x ≠ y)
    (hx : ¬ Unit (x - c)) (hy : ¬ Unit (y - c)) (hV : ∀ a ∈ V, Unit (a - c))
    (hEx : 3 ≤ (edgeFaces V x c).card) (hEy : 3 ≤ (edgeFaces V y c).card) :
    (mixedVertices V x y).card < 4 := by
  obtain ⟨S, hSV, hS, hs⟩ := triangle_of_three_edges hcard hx hV hEx
  obtain ⟨T, hTV, hT, ht⟩ := triangle_of_three_edges hcard hy hV hEy
  have hne : S ≠ T := by
    intro h
    rw [h, ht] at hs
    exact hxy (by linear_combination -hs)
  have hU : S ∪ T = V := by
    apply eq_of_subset_of_card_le (union_subset hSV hTV)
    have hp : S ⊂ S ∪ T := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_left, ?_⟩
      intro he
      have hsub : T ⊆ S := by rw [he]; exact subset_union_right
      exact hne ((eq_of_subset_of_card_le hsub (by omega : S.card ≤ T.card)).symm)
    have := card_lt_card hp
    omega
  have hI : (S ∩ T).card = 2 := by
    have h := card_union_add_card_inter S T
    rw [hU] at h
    omega
  obtain ⟨a, b, hab, hAB⟩ := card_eq_two.mp hI
  have hST : (S \ T).card = 1 := by rw [card_sdiff, hS, inter_comm T S, hI]
  have hTS : (T \ S).card = 1 := by rw [card_sdiff, hT, hI]
  obtain ⟨r, hr⟩ := card_eq_one.mp hST
  obtain ⟨s, hss⟩ := card_eq_one.mp hTS
  have hrST : r ∈ S \ T := by simp [hr]
  have hsTS : s ∈ T \ S := by simp [hss]
  have hra : r ≠ a := fun h => (mem_sdiff.mp hrST).2
    (mem_inter.mp (by simp [hAB, h] : r ∈ S ∩ T)).2
  have hrb : r ≠ b := fun h => (mem_sdiff.mp hrST).2
    (mem_inter.mp (by simp [hAB, h] : r ∈ S ∩ T)).2
  have hsa : s ≠ a := fun h => (mem_sdiff.mp hsTS).2
    (mem_inter.mp (by simp [hAB, h] : s ∈ S ∩ T)).1
  have hsb : s ≠ b := fun h => (mem_sdiff.mp hsTS).2
    (mem_inter.mp (by simp [hAB, h] : s ∈ S ∩ T)).1
  have hrs : r ≠ s := fun h => (mem_sdiff.mp hrST).2 (h.symm ▸ (mem_sdiff.mp hsTS).1)
  have hSC : S = {r, a, b} := by
    rw [← singleton_union, ← hr, ← hAB]
    ext z
    simp
    tauto
  have hTC : T = {s, a, b} := by
    rw [← singleton_union, ← hss, ← hAB]
    ext z
    simp
    tauto
  rw [hSC, sum_insert (by simp [hra, hrb]), sum_insert (by simp [hab]), sum_singleton] at hs
  rw [hTC, sum_insert (by simp [hsa, hsb]), sum_insert (by simp [hab]), sum_singleton] at ht
  have haV : a ∈ V := hSV (by simp [hSC])
  have hbV : b ∈ V := hSV (by simp [hSC])
  have hrV : r ∈ V := hSV (mem_sdiff.mp hrST).1
  have hsV : s ∈ V := hTV (mem_sdiff.mp hsTS).1
  let u := a + b - c
  let v := x + y - u
  have hxu : Unit (x - u) := by
    rw [show x - u = r - c by dsimp [u]; linear_combination -hs]
    exact hV r hrV
  have hyu : Unit (y - u) := by
    rw [show y - u = s - c by dsimp [u]; linear_combination -ht]
    exact hV s hsV
  have hcu : c ≠ u := fun h => hx (h.symm ▸ hxu)
  have haU : Unit (a - u) := unit_reflect (hV b hbV)
  have hbU : Unit (b - u) := by
    rw [show b - u = -(a - c) by dsimp [u]; ring]
    exact unit_neg (hV a haV)
  have hnotU {z : ℂ} (hzV : z ∈ V) (hza : z ≠ a) (hzb : z ≠ b) : ¬ Unit (z - u) := by
    intro hzU
    let A : Finset ℂ := {z, a, b}
    have hA : A.card = 3 := card_eq_three.mpr ⟨_, _, _, hza, hzb, hab, rfl⟩
    have hac : ∀ w ∈ A, dist w c = 1 := by
      intro w hw
      rw [dist_eq_norm]
      have hsub : A ⊆ V := insert_subset hzV (insert_subset haV (singleton_subset_iff.mpr hbV))
      exact hV w (hsub hw)
    have hau : ∀ w ∈ A, dist w u = 1 := by
      intro w hw
      simp only [A, mem_insert, mem_singleton] at hw
      rw [dist_eq_norm]
      rcases hw with he | he | he <;> subst w
      · exact hzU
      · exact haU
      · exact hbU
    exact hcu (unique_circle (by omega) hac hau)
  by_contra! hlarge
  have hAll : mixedVertices V x y = V := by
    apply eq_of_subset_of_card_le (filter_subset _ _)
    change V.card ≤ (mixedVertices V x y).card
    omega
  have hcand {z : ℂ} (hzV : z ∈ V) (hzU : ¬ Unit (z - u)) : Unit (z - v) ∧ Unit (x - v) := by
    have hmem : z ∈ mixedVertices V x y := hAll.symm ▸ hzV
    obtain ⟨d, hd⟩ := (mem_filter.mp hmem).2
    have hzd : Unit (z - d) := by simpa only [dist_eq_norm] using hd z (by simp)
    have hxd : Unit (x - d) := by simpa only [dist_eq_norm] using hd x (by simp)
    have hyd : Unit (y - d) := by simpa only [dist_eq_norm] using hd y (by simp)
    rcases center_eq_or_reflect hxy hxu hyu hxd hyd with he | he
    · exact (hzU (he ▸ hzd)).elim
    · change d = v at he
      exact ⟨he ▸ hzd, he ▸ hxd⟩
  obtain ⟨hrv, hxv⟩ := hcand hrV (hnotU hrV hra hrb)
  obtain ⟨hsv, _⟩ := hcand hsV (hnotU hsV hsa hsb)
  rcases center_eq_or_reflect hrs (hV r hrV) (hV s hsV) hrv hsv with hv | hv
  · exact hx (hv ▸ hxv)
  · have hxs : x = r := by dsimp [v, u] at hv; linear_combination hv + ht
    exact hx (hxs.symm ▸ hV r hrV)

private theorem deletion_no_near_bound {P : Finset ℂ} (hP : Admissible P)
    (hnear : ¬ ∃ c, (onCircle P c).card = P.card - 1) (hn : 5 ≤ P.card) :
    (P.card - 3) * (unitTriples P).card ≤ P.card * answer (P.card - 1) := by
  apply deletion_bound
  intro a ha
  have hc := card_erase_of_mem ha
  simpa only [hc] using complex_upper (P.erase a) (by omega) (admissible_erase hP hnear ha)

/-- Every maximizer has exactly all but one point on a unit circle. -/
private theorem complex_maximizer (P : Finset ℂ) (hn : 4 ≤ P.card) (hP : Admissible P)
    (hmax : (unitTriples P).card = answer P.card) :
    ∃ c, (onCircle P c).card = P.card - 1 := by
  by_contra hnear
  have hc := circle_small_of_no_near hP hnear
  by_cases hlarge : 10 ≤ P.card
  · have hstrict := deletion_strict_large P.card hlarge
    have hdel := deletion_no_near_bound hP hnear (by omega)
    rw [hmax] at hdel
    exact (not_lt_of_ge hdel) hstrict
  have hRange : P.card = 4 ∨ P.card = 5 ∨ P.card = 6 ∨ P.card = 7 ∨
      P.card = 8 ∨ P.card = 9 := by omega
  rcases hRange with h4 | h5 | h6 | h7 | h8 | h9
  · have hpos : 0 < (unitTriples P).card := by rw [hmax, h4]; decide
    obtain ⟨A, hA⟩ := card_pos.mp hpos
    obtain ⟨hsub, hs, c, hf⟩ := mem_faces.mp hA
    have hle : A.card ≤ (onCircle P c).card :=
      card_le_card (fun a ha => mem_filter.mpr ⟨hsub ha, hf a ha⟩)
    have h := hc c
    omega
  · have h := pair_count_bound (P := P) (fun c => by have := hc c; omega)
    rw [hmax, h5] at h
    revert h
    decide
  · by_cases he : ∃ c, (onCircle P c).card = 4
    · obtain ⟨c, he⟩ := he
      obtain ⟨x, y, hxy, hx, hy, hsplit⟩ := split_circle_two (P := P) (c := c) (by omega) (by omega)
      have hV := onCircle_unit (P := P) (c := c)
      have hcount := triples_count_two hxy hx hy hV
      rw [← hsplit, hmax, h6, he] at hcount
      change 14 = 4 + _ + _ + _ at hcount
      have hEx := edgeFaces_le hx hV
      have hEy := edgeFaces_le hy hV
      rw [he] at hEx hEy
      change _ ≤ 3 at hEx hEy
      have hM := mixed_card_le_four (onCircle P c) hxy hx hV
      have hm := mixed_card_lt_four he hxy hx hy hV (by omega) (by omega)
      omega
    · have h := pair_count_bound (P := P) (fun c => by
        have := hc c
        have hh : (onCircle P c).card ≠ 4 := fun h => he ⟨c, h⟩
        omega)
      rw [hmax, h6] at h
      revert h
      decide
  · have h := deletion_no_near_bound hP hnear (by omega)
    rw [hmax, h7] at h
    revert h
    decide
  · by_cases he : ∃ c, (onCircle P c).card = 6
    · obtain ⟨c, he⟩ := he
      obtain ⟨x, y, hxy, hx, hy, hsplit⟩ := split_circle_two (P := P) (c := c) (by omega) (by omega)
      have hV := onCircle_unit (P := P) (c := c)
      have hcount := triples_count_two hxy hx hy hV
      rw [← hsplit, hmax, h8, he] at hcount
      change 41 = 20 + _ + _ + _ at hcount
      have hEx := edgeFaces_le hx hV
      have hEy := edgeFaces_le hy hV
      rw [he] at hEx hEy
      change _ ≤ 6 at hEx hEy
      have hM := mixed_card_le_four (onCircle P c) hxy hx hV
      omega
    · have hdel : (P.card - 3) * (unitTriples P).card ≤ P.card * 24 := by
        apply deletion_bound
        intro a ha
        have h7 : (P.erase a).card = 7 := by have := card_erase_of_mem ha; omega
        have hnear7 : ¬ ∃ c, (onCircle (P.erase a) c).card = (P.erase a).card - 1 := by
          rintro ⟨c, hh⟩
          have hs : onCircle (P.erase a) c ⊆ onCircle P c := by
            intro b hb
            simp only [onCircle, mem_filter] at hb ⊢
            exact ⟨mem_of_mem_erase hb.1, hb.2⟩
          have := card_le_card hs
          have := hc c
          exact he ⟨c, by omega⟩
        have hh := deletion_no_near_bound (admissible_erase hP hnear ha) hnear7 (by omega)
        rw [h7] at hh
        change 4 * _ ≤ 98 at hh
        omega
      rw [hmax, h8] at hdel
      revert hdel
      decide
  · have h := deletion_no_near_bound hP hnear (by omega)
    rw [hmax, h9] at h
    revert h
    decide

/-! ## Statements in the Euclidean plane -/

/-- The ambient plane used by Formal Conjectures for Erdős #104. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

private abbrev complexToPlane : ℂ ≃ᵢ Plane :=
  Complex.orthonormalBasisOneI.repr.toIsometryEquiv

private theorem fits_map {E F : Type*} [MetricSpace E] [MetricSpace F] (e : E ≃ᵢ F)
    (A : Finset E) : Fits (A.map e.toEquiv.toEmbedding) ↔ Fits A := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨e.symm c, fun a ha => ?_⟩
    have h := hc (e a) (mem_map_of_mem e.toEquiv.toEmbedding ha)
    rw [← e.apply_symm_apply c, e.isometry.dist_eq] at h
    exact h
  · rintro ⟨c, hc⟩
    refine ⟨e c, ?_⟩
    intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hb
    change dist (e a) (e c) = 1
    rw [e.isometry.dist_eq]
    exact hc a ha

private theorem unitTriples_card_map {E F : Type*} [MetricSpace E] [MetricSpace F]
    (e : E ≃ᵢ F) (P : Finset E) :
    (unitTriples (P.map e.toEquiv.toEmbedding)).card = (unitTriples P).card := by
  let f := e.toEquiv.finsetCongr
  have h : unitTriples (P.map e.toEquiv.toEmbedding) =
      (unitTriples P).map f.toEmbedding := by
    ext B
    obtain ⟨A, rfl⟩ := f.surjective B
    change f A ∈ _ ↔ f.toEmbedding A ∈ _
    rw [mem_map' f.toEmbedding]
    change A.map e.toEquiv.toEmbedding ∈ faces 3 (P.map e.toEquiv.toEmbedding) Fits ↔
      A ∈ faces 3 P Fits
    simp only [mem_faces, map_subset_map, card_map, fits_map]
  rw [h, card_map]

private theorem onCircle_map {E F : Type*} [MetricSpace E] [MetricSpace F]
    (e : E ≃ᵢ F) (P : Finset E) (c : E) :
    onCircle (P.map e.toEquiv.toEmbedding) (e c) =
      (onCircle P c).map e.toEquiv.toEmbedding := by
  ext b
  obtain ⟨a, rfl⟩ := e.surjective b
  change e.toEquiv.toEmbedding a ∈ _ ↔ e.toEquiv.toEmbedding a ∈ _
  simp only [onCircle, mem_filter]
  rw [mem_map', mem_map', mem_filter]
  change a ∈ P ∧ dist (e a) (e c) = 1 ↔ a ∈ P ∧ dist a c = 1
  rw [e.isometry.dist_eq]

/-- The counts attained by admissible configurations with exactly `n` points. -/
def possibleCounts (n : ℕ) : Set ℕ :=
  {t | ∃ P : Finset Plane, P.card = n ∧ Admissible P ∧ (unitTriples P).card = t}

/-- Erdős's extremal function from his 1975 paper. -/
noncomputable def gn (n : ℕ) : ℕ := sSup (possibleCounts n)

/-- The value is attained and is an upper bound for every admissible configuration. -/
theorem unitCircumradiusTriples (n : ℕ) (hn : 4 ≤ n) :
    IsGreatest (possibleCounts n) (answer n) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨P, hc, ha, ht⟩ := complex_attains n hn
    refine ⟨P.map complexToPlane.toEquiv.toEmbedding, by rwa [card_map], ?_, ?_⟩
    · exact fun h => ha ((fits_map complexToPlane P).mp h)
    · rwa [unitTriples_card_map]
  · rintro t ⟨P, hc, ha, ht⟩
    let Q := P.map complexToPlane.symm.toEquiv.toEmbedding
    have hQ : Q.card = n := by simpa only [Q, card_map] using hc
    have hQa : Admissible Q := fun h => ha ((fits_map complexToPlane.symm P).mp h)
    have h := complex_upper Q (by omega) hQa
    change (unitTriples (P.map complexToPlane.symm.toEquiv.toEmbedding)).card ≤ answer Q.card at h
    rw [unitTriples_card_map, ht, hQ] at h
    exact h

/-- The exact formula for the maximum number of unit-circumradius triples. -/
theorem gn_eq (n : ℕ) (hn : 4 ≤ n) :
    gn n = (n - 1).choose 3 + (n - 2) + if (n - 1) % 3 = 0 then 1 else 0 :=
  (unitCircumradiusTriples n hn).csSup_eq

private theorem admissible_of_far_pair {E : Type*} [MetricSpace E] {P : Finset E}
    {a b : E} (ha : a ∈ P) (hb : b ∈ P) (hd : 2 < dist a b) : Admissible P := by
  rintro ⟨c, hc⟩
  have h := dist_triangle_right a b c
  rw [hc a ha, hc b hb] at h
  linarith

private theorem small_count (n : ℕ) (hn : 2 ≤ n) (hn' : n ≤ 3) :
    IsGreatest (possibleCounts n) 0 := by
  have hcount (P : Finset Plane) (hP : P.card = n) (hA : Admissible P) :
      (unitTriples P).card = 0 := by
    apply card_eq_zero.mpr
    apply not_nonempty_iff_eq_empty.mp
    rintro ⟨T, hT⟩
    obtain ⟨hsub, hk, hfit⟩ := mem_faces.mp hT
    have hEq := eq_of_subset_of_card_le hsub (show P.card ≤ T.card by omega)
    exact hA (hEq ▸ hfit)
  have hdist : 2 < dist (0 : ℂ) 3 := by norm_num [dist_eq_norm]
  refine ⟨?_, ?_⟩
  · suffices h : ∃ P : Finset ℂ, P.card = n ∧ Admissible P by
      obtain ⟨P, hP, hAd⟩ := h
      let Q := P.map complexToPlane.toEquiv.toEmbedding
      have hQ : Q.card = n := by rwa [show Q.card = P.card from card_map _]
      have hQa : Admissible Q := fun h => hAd ((fits_map complexToPlane P).mp h)
      exact ⟨Q, hQ, hQa, hcount Q hQ hQa⟩
    have h03 : (0 : ℂ) ≠ 3 := by norm_num
    have h04 : (0 : ℂ) ≠ 4 := by norm_num
    interval_cases n
    · exact ⟨{0, 3}, by simp [h03], admissible_of_far_pair (by simp) (by simp) hdist⟩
    · exact ⟨{0, 3, 4}, by simp [h03, h04],
        admissible_of_far_pair (by simp) (by simp) hdist⟩
  · rintro t ⟨P, hP, hAd, ht⟩
    rw [← ht, hcount P hP hAd]

/-- The two admissible boundary cases have maximum zero. -/
theorem gn_eq_zero {n : ℕ} (hn : 2 ≤ n) (hn' : n ≤ 3) :
    gn n = 0 :=
  (small_count n hn hn').csSup_eq

/-- In every maximizing configuration with at least four points, one unit circle
contains exactly all but one of the points. -/
theorem maximizer_on_unit_circle (P : Finset Plane) (hn : 4 ≤ P.card)
    (hP : Admissible P) (hmax : (unitTriples P).card = gn P.card) :
    ∃ c, (onCircle P c).card = P.card - 1 := by
  let Q := P.map complexToPlane.symm.toEquiv.toEmbedding
  have hQ : Q.card = P.card := card_map _
  have hQa : Admissible Q := fun h => hP ((fits_map complexToPlane.symm P).mp h)
  have hQt : (unitTriples Q).card = answer Q.card := by
    change (unitTriples (P.map complexToPlane.symm.toEquiv.toEmbedding)).card = _
    rw [unitTriples_card_map, hmax, hQ]
    exact (unitCircumradiusTriples P.card hn).csSup_eq
  obtain ⟨c, hc⟩ := complex_maximizer Q (by omega) hQa hQt
  have hm := onCircle_map complexToPlane.symm P (complexToPlane c)
  change onCircle Q (complexToPlane.symm (complexToPlane c)) = _ at hm
  rw [IsometryEquiv.symm_apply_apply] at hm
  refine ⟨complexToPlane c, ?_⟩
  have hh := congrArg card hm
  rw [card_map, hc, hQ] at hh
  exact hh.symm

end
end Erdos104UnitTriples
