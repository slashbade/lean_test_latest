import Mathlib
import Reap

open Finset Set

example (s t : Finset ℕ) (h : s ⊆ t)
  (h' : t ⊆ s) : #s = #t := by
  reap

section exercises
variable {G H : Type*} [Group G] [Group H]

open Subgroup

example (φ : G →* H) (S T : Subgroup H)
(hST : S ≤ T) : comap φ S ≤ comap φ T := by
  simpa only [comap_comap] using comap_mono hST

example (φ : G →* H) (S T : Subgroup G)
(hST : S ≤ T) : map φ S ≤ map φ T := by
  repeat reap

/--
Addictive group of $\mathbb{Q}$ is not cyclic.
-/
theorem Rat.not_isAddCyclic : ¬ (IsAddCyclic ℚ) := by
  sorry

open Real

example : (cos x + sin x)^2 = 2 * sin x * cos x + 1 := by
  ring_nf
  rw [← cos_sq_add_sin_sq x]
  ring
