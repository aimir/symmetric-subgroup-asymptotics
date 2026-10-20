import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixS3WreathSource

/-!
# The minimal ternary kernel in the two-block S3 wreath product

Only the literal kernel normal form and short commutator words are checked.
The normal-subgroup cover follows symbolically. This module does not import
the older native-decide algebra or any derived-character certificate.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics
namespace S3WreathTernaryCore

open SemidirectProduct

abbrev S3 := Equiv.Perm (Fin 3)
abbrev G := DegreeSixS3Wreath.G
abbrev projection := DegreeSixS3Wreath.projection

def rotation : S3 := Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2
def transposition : S3 := Equiv.swap (1 : Fin 3) 2
def firstRotation : G := inl (rotation, 1)
def secondRotation : G := inl (1, rotation)
def firstFlip : G := inl (transposition, 1)
def blockSwap : G := inr C2Wreath.gen

private theorem wreath_eq_iff (x y : G) :
    x = y ↔ x.left = y.left ∧ x.right = y.right :=
  ⟨fun h ↦ ⟨congrArg SemidirectProduct.left h, congrArg SemidirectProduct.right h⟩,
    fun h ↦ SemidirectProduct.ext h.1 h.2⟩

theorem mem_projection_ker_iff (x : G) :
    x ∈ projection.ker ↔
      x.right = 1 ∧ oddMarkerSign x.left.1 = 1 ∧ oddMarkerSign x.left.2 = 1 := by
  change (⟨(oddMarkerSign x.left.1, oddMarkerSign x.left.2), x.right⟩ :
    DegreeSixS3Wreath.D8) = 1 ↔ _
  constructor
  · intro h
    exact ⟨congrArg SemidirectProduct.right h,
      congrArg (fun y : DegreeSixS3Wreath.D8 ↦ y.left.1) h,
      congrArg (fun y : DegreeSixS3Wreath.D8 ↦ y.left.2) h⟩
  · rintro ⟨hr, ha, hb⟩
    exact SemidirectProduct.ext (Prod.ext ha hb) hr

theorem firstRotation_mem : firstRotation ∈ projection.ker := by
  rw [mem_projection_ker_iff]
  decide +kernel

theorem firstRotation_ne_one : firstRotation ≠ 1 := by decide +kernel

theorem secondRotation_mem : secondRotation ∈ projection.ker := by
  rw [mem_projection_ker_iff]
  decide +kernel

theorem kernel_normal_form : ∀ x : G, x ∈ projection.ker →
    ∃ i j : Fin 3,
      x = firstRotation ^ (i : ℕ) * secondRotation ^ (j : ℕ) := by
  intro x hx
  rw [mem_projection_ker_iff] at hx
  revert x
  simp only [wreath_eq_iff]
  decide +kernel

private theorem centralizer_test : ∀ x : G,
    x * firstRotation = firstRotation * x →
    x * secondRotation = secondRotation * x →
      x.right = 1 ∧ oddMarkerSign x.left.1 = 1 ∧ oddMarkerSign x.left.2 = 1 := by
  simp only [wreath_eq_iff]
  decide +kernel

theorem selfCentralizing (x : G)
    (hx : ∀ v ∈ projection.ker, x * v = v * x) : x ∈ projection.ker :=
  (mem_projection_ker_iff x).mpr
    (centralizer_test x (hx firstRotation firstRotation_mem)
      (hx secondRotation secondRotation_mem))

private theorem comm_mem (W : Subgroup G) (hW : W.Normal)
    {x : G} (hx : x ∈ W) (g : G) : ⁅g, x⁆ ∈ W := by
  rw [commutatorElement_def]
  exact W.mul_mem (hW.conj_mem _ hx g) (W.inv_mem hx)

set_option maxHeartbeats 2000000 in
private theorem isolate_first_rotation : ∀ x : G,
    x.right = 1 → oddMarkerSign x.left.1 = 1 → x.left.1 ≠ 1 →
    ⁅firstFlip, x⁆ = firstRotation ∨ ⁅firstFlip, x⁆ ^ 2 = firstRotation := by
  simp only [wreath_eq_iff]
  decide +kernel

private theorem firstRotation_mem_of_first_ne
    (W : Subgroup G) (hW : W.Normal) {x : G}
    (hxW : x ∈ W) (hxV : x ∈ projection.ker)
    (hx1 : x.left.1 ≠ 1) : firstRotation ∈ W := by
  have hc := comm_mem W hW hxW firstFlip
  have hx := (mem_projection_ker_iff x).mp hxV
  rcases isolate_first_rotation x hx.1 hx.2.1 hx1 with h | h
  · rw [← h]
    exact hc
  · rw [← h]
    exact W.pow_mem hc 2

private theorem swap_conjugate_first (x : G) :
    (blockSwap * x * blockSwap⁻¹).left.1 = x.left.2 := by
  revert x
  decide +kernel

private theorem swap_firstRotation :
    blockSwap * firstRotation * blockSwap⁻¹ = secondRotation := by
  decide +kernel

private theorem second_ne_of_first_eq_one (x : G)
    (hx : x ∈ projection.ker) (hne : x ≠ 1) (hfirst : x.left.1 = 1) :
    x.left.2 ≠ 1 := by
  intro hsecond
  exact hne (SemidirectProduct.ext (Prod.ext hfirst hsecond)
    ((mem_projection_ker_iff x).mp hx).1)

theorem minimal (W : Subgroup G) (hW : W.Normal) (hWV : W ≤ projection.ker) :
    W = ⊥ ∨ W = projection.ker := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  apply le_antisymm hWV
  obtain ⟨⟨x, hxW⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
  have hx1' : x ≠ 1 := fun h ↦ hx1 (Subtype.ext h)
  have hxV : x ∈ projection.ker := hWV hxW
  have hr1 : firstRotation ∈ W := by
    by_cases hfirst : x.left.1 = 1
    · let y := blockSwap * x * blockSwap⁻¹
      have hyW : y ∈ W := hW.conj_mem x hxW blockSwap
      have hyV : y ∈ projection.ker :=
        (inferInstance : projection.ker.Normal).conj_mem x hxV blockSwap
      apply firstRotation_mem_of_first_ne W hW hyW hyV
      dsimp only [y]
      rw [swap_conjugate_first]
      exact second_ne_of_first_eq_one x hxV hx1' hfirst
    · exact firstRotation_mem_of_first_ne W hW hxW hxV hfirst
  have hr2 : secondRotation ∈ W := by
    have h := hW.conj_mem firstRotation hr1 blockSwap
    rwa [swap_firstRotation] at h
  intro v hv
  obtain ⟨i, j, hij⟩ := kernel_normal_form v hv
  rw [hij]
  exact W.mul_mem (W.pow_mem hr1 (i : ℕ)) (W.pow_mem hr2 (j : ℕ))

theorem normal_cover (N : Subgroup G) (hN : N.Normal) (hNb : N ≠ ⊥) :
    projection.ker ≤ N := by
  letI : N.Normal := hN
  exact le_of_minimal_selfCentralizing projection.ker minimal selfCentralizing N hNb

end S3WreathTernaryCore
end SymmetricSubgroupAsymptotics

end
