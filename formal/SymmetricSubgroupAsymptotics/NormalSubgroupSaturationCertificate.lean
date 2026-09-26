import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Finite original commutator words certify a normal-subgroup saturation
property. If every displayed D-row outside R generates the displayed
R-generators by actual iterated commutators with the original ambient
tuple, every whole-ambient normal subgroup B≤D is comparable with R.
No normal-subgroup enumeration, centralizer dimension assumption or
replacement of whole-ambient normality by intrinsic normality is used. -/
set_option autoImplicit false
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable {G H ι κ : Type*} [Group G] [Group H]

/-- A path records successive original commutators, in list order.
For example [i,j] evaluates to [[x,g i],g j]. -/
def iteratedOriginalCommutator (g : ι → G) (x : G) : List ι → G
  | [] => x
  | i :: w => iteratedOriginalCommutator g ⁅x, g i⁆ w

/-- Products of original commutator paths retain the original element
and every original ambient generator used in the certificate. -/
def originalCommutatorProduct (g : ι → G) (x : G) (words : List (List ι)) : G :=
  (words.map (iteratedOriginalCommutator g x)).prod

theorem iteratedOriginalCommutator_mem (g : ι → G) (B : Subgroup G) [B.Normal]
    (x : G) (hx : x ∈ B) (w : List ι) : iteratedOriginalCommutator g x w ∈ B := by
  induction w generalizing x with
  | nil => exact hx
  | cons i w ih =>
    exact ih ⁅x, g i⁆ (Subgroup.commutator_le_left B ⊤
      (Subgroup.commutator_mem_commutator hx (Subgroup.mem_top (g i))))

theorem originalCommutatorProduct_mem (g : ι → G) (B : Subgroup G) [B.Normal]
    (x : G) (hx : x ∈ B) (words : List (List ι)) :
    originalCommutatorProduct g x words ∈ B := by
  apply B.list_prod_mem
  intro y hy
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hy
  exact iteratedOriginalCommutator_mem g B x hx w

/-- An actual group homomorphism preserves the original path. In
particular, an original permutation inclusion permits pointwise checks. -/
theorem map_iteratedOriginalCommutator (f : G →* H) (g : ι → G)
    (x : G) (w : List ι) :
    f (iteratedOriginalCommutator g x w) =
      iteratedOriginalCommutator (fun i => f (g i)) (f x) w := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih =>
    change f (iteratedOriginalCommutator g ⁅x, g i⁆ w) = _
    rw [ih, map_commutatorElement]
    rfl

theorem map_originalCommutatorProduct (f : G →* H) (g : ι → G)
    (x : G) (words : List (List ι)) :
    f (originalCommutatorProduct g x words) =
      originalCommutatorProduct (fun i => f (g i)) (f x) words := by
  have hfun : f ∘ iteratedOriginalCommutator g x =
      iteratedOriginalCommutator (fun i => f (g i)) (f x) := by
    funext w
    exact map_iteratedOriginalCommutator f g x w
  simp only [originalCommutatorProduct, map_list_prod, List.map_map, hfun]

/-- A complete list of original D-elements together with concrete words
recovering all original R-generators from every row not certified in R.
The Boolean inside marker has only a soundness requirement: every false
row must satisfy the displayed word equations. No original row is skipped. -/
structure NormalSubgroupSaturationCertificate
    (D R : Subgroup G) (ambient : ι → G) (radicalGenerators : κ → G) (n : ℕ) where
  radical_le : R ≤ D
  radical_full : Subgroup.closure (Set.range radicalGenerators) = R
  rows : Fin n → G
  rows_mem : ∀ i, rows i ∈ D
  rows_cover : ∀ x ∈ D, ∃ i, rows i = x
  inside : Fin n → Bool
  inside_mem : ∀ i, inside i = true → rows i ∈ R
  words : Fin n → κ → List (List ι)
  words_eq : ∀ i, inside i = false → ∀ j,
    originalCommutatorProduct ambient (rows i) (words i j) = radicalGenerators j

namespace NormalSubgroupSaturationCertificate

variable {D R : Subgroup G} {ambient : ι → G} {radicalGenerators : κ → G} {n : ℕ}
variable (C : NormalSubgroupSaturationCertificate D R ambient radicalGenerators n)
include C

/-- Every whole-original-group normal subgroup inside the same D lies
below R or contains R. This is the universal consequence of the finite
word certificate, not a list of individually selected normal subgroups. -/
theorem comparable (B : Subgroup G) [B.Normal] (hBD : B ≤ D) :
    B ≤ R ∨ R ≤ B := by
  classical
  by_cases hBR : B ≤ R
  · exact Or.inl hBR
  · right
    obtain ⟨b, hb, hbR⟩ := SetLike.not_le_iff_exists.mp hBR
    obtain ⟨i, hi⟩ := C.rows_cover b (hBD hb)
    have hiB : C.rows i ∈ B := by rw [hi]; exact hb
    have hiR : C.rows i ∉ R := by rw [hi]; exact hbR
    have hout : C.inside i = false := by
      cases h : C.inside i with
      | false => rfl
      | true => exact False.elim (hiR (C.inside_mem i h))
    rw [← C.radical_full]
    apply (Subgroup.closure_le B).mpr
    rintro _ ⟨j, rfl⟩
    rw [← C.words_eq i hout j]
    exact originalCommutatorProduct_mem ambient B (C.rows i) hiB (C.words i j)

/-- A normal containing any original D-element outside R contains all
of R, even if that normal is not itself a subgroup of D. -/
theorem radical_le_of_mem_outside (B : Subgroup G) [B.Normal]
    (x : G) (hxB : x ∈ B) (hxD : x ∈ D) (hxR : x ∉ R) : R ≤ B := by
  obtain ⟨i, hi⟩ := C.rows_cover x hxD
  have hiB : C.rows i ∈ B := by rw [hi]; exact hxB
  have hiR : C.rows i ∉ R := by rw [hi]; exact hxR
  have hout : C.inside i = false := by
    cases h : C.inside i with
    | false => rfl
    | true => exact False.elim (hiR (C.inside_mem i h))
  rw [← C.radical_full]
  apply (Subgroup.closure_le B).mpr
  rintro _ ⟨j, rfl⟩
  rw [← C.words_eq i hout j]
  exact originalCommutatorProduct_mem ambient B (C.rows i) hiB (C.words i j)

/-- Combine the finite saturation certificate with an independently
proved small-intersection collapse. The original intersection contains R
whenever the same original normal N is not contained in D. -/
theorem radical_le_intersection_of_not_le [D.Normal]
    (N : Subgroup G) [N.Normal] (hnot : ¬N ≤ D)
    (hcollapse : N ⊓ D ≤ R → N ≤ R) : R ≤ N ⊓ D := by
  rcases C.comparable (N ⊓ D) inf_le_right with hsmall | hlarge
  · exact False.elim (hnot ((hcollapse hsmall).trans C.radical_le))
  · exact hlarge

end NormalSubgroupSaturationCertificate
end SymmetricSubgroupAsymptotics
