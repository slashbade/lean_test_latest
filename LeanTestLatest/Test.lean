import Mathlib
import Reap
import Reap.Tactic.Search

open Finset Set

example (s t : Finset ℕ) (h : s ⊆ t)
  (h' : t ⊆ s) : #s = #t := by
  exact le_antisymm (Finset.card_le_card h) (Finset.card_le_card h')

section exercises
variable {G H : Type*} [Group G] [Group H]

open Subgroup

example (φ : G →* H) (S T : Subgroup H)
(hST : S ≤ T) : comap φ S ≤ comap φ T := by
  simpa only [comap_comap] using comap_mono hST

example (φ : G →* H) (S T : Subgroup G)
(hST : S ≤ T) : map φ S ≤ map φ T := by
  simp only [SetLike.le_def, Set.mem_image, SetLike.mem_coe]
  intro x a
  simp_all only [Subgroup.mem_map]
  obtain ⟨w, h⟩ := a
  obtain ⟨left, right⟩ := h
  subst right
  exact ⟨w, hST left, rfl⟩

/--
Addictive group of $\mathbb{Q}$ is not cyclic.
-/
theorem Rat.not_isAddCyclic : ¬ (IsAddCyclic ℚ) := by
  reap!!

open Real

example (x : ℝ) : (cos x + sin x)^2 = 2 * sin x * cos x + 1 := by
  rw [add_sq, sin_sq, cos_sq]
  simp_all only [one_div]
  ring
