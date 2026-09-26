import SymmetricSubgroupAsymptotics.BinaryMixtureCyclicFour
import SymmetricSubgroupAsymptotics.AllLifts

/-! The original square obstruction for C4^a × C2^r.
For each actual mod-two image U, squares identify U with its image in
the doubled C4 kernel coordinates. The remaining binary coordinates do
not contribute squares. The resulting fixed-image count is exact.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCyclicFourSquareObstruction

abbrev Original (r a : ℕ) :=
  Multiplicative (Fin a → ZMod 4) × Multiplicative (Fin r → ZMod 2)

abbrev ImageSpace (a : ℕ) := Fin a → ZMod 2
abbrev KernelSpace (r a : ℕ) := (Fin a → ZMod 2) × (Fin r → ZMod 2)

/-- Actual reduction of the original C4 coordinates; the binary factor is forgotten. -/
def projection (r a : ℕ) : Original r a →* Multiplicative (ImageSpace a) :=
  (MonoidHom.fst _ _).comp
    (cyclicFourProductProjection (Multiplicative (Fin r → ZMod 2)) a)

theorem projection_surjective (r a : ℕ) : Function.Surjective (projection r a) := by
  intro v
  obtain ⟨x,hx⟩ := cyclicFourProductProjection_surjective
    (Multiplicative (Fin r → ZMod 2)) a (v,1)
  exact ⟨x,congrArg Prod.fst hx⟩

/-- The literal kernel, including the whole original binary factor. -/
def kernelChart (r a : ℕ) : Multiplicative (KernelSpace r a) ≃* (projection r a).ker where
  toFun v := ⟨(Multiplicative.ofAdd (fun i => cyclicFourDouble (v.toAdd.1 i)),
      Multiplicative.ofAdd v.toAdd.2),by
    apply Multiplicative.toAdd.injective
    funext i
    exact cyclicFourReduction_double (v.toAdd.1 i)⟩
  invFun x := Multiplicative.ofAdd
    ((fun i => cyclicFourHalf (x.1.1.toAdd i)),x.1.2.toAdd)
  left_inv v := by
    apply Multiplicative.toAdd.injective
    apply Prod.ext
    · funext i
      exact cyclicFourHalf_double _
    · rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      funext i
      apply cyclicFourDouble_half
      exact congrArg (fun y : Multiplicative (ImageSpace a) => y.toAdd i) x.2
    · rfl
  map_mul' v z := by
    apply Subtype.ext
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      funext i
      exact map_add cyclicFourDouble _ _
    · rfl

theorem kernel_central (r a : ℕ) : (projection r a).ker ≤ Subgroup.center (Original r a) := by
  intro x _
  exact Subgroup.mem_center_iff.mpr (fun y => mul_comm y x)

def squareEmbedding (r a : ℕ) : ImageSpace a →ₗ[ZMod 2] KernelSpace r a :=
  LinearMap.inl (ZMod 2) (Fin a → ZMod 2) (Fin r → ZMod 2)

theorem squareEmbedding_injective (r a : ℕ) : Function.Injective (squareEmbedding r a) :=
  LinearMap.inl_injective

private theorem half_square (z : ZMod 4) :
    cyclicFourHalf (z+z) = cyclicFourReduction z := by
  revert z
  decide

/-- Every original square has exactly its original mod-two C4 coordinate. -/
theorem squareCoordinate (r a : ℕ) (g : Original r a) :
    binarySquareCoordinate (projection r a) (kernelChart r a) g =
      squareEmbedding r a (projection r a g).toAdd := by
  simp only [binarySquareCoordinate,pow_two]
  apply Prod.ext
  · funext i
    change cyclicFourHalf (g.1.toAdd i+g.1.toAdd i) = cyclicFourReduction (g.1.toAdd i)
    exact half_square _
  · funext i
    change g.2.toAdd i+g.2.toAdd i = 0
    rw [← two_smul (ZMod 2),show (2 : ZMod 2) = 0 by decide,zero_smul]

/-- Equality of actual subspaces, not just a bound on the obstruction rank. -/
theorem imageSquareObstruction_eq (r a : ℕ) (U : Submodule (ZMod 2) (ImageSpace a)) :
    binaryImageSquareObstruction (projection r a) (kernelChart r a) U =
      U.map (squareEmbedding r a) := by
  apply le_antisymm
  · apply (binaryImageSquareObstruction_le_iff (projection r a) (kernelChart r a) U _).mpr
    intro g hg
    rw [squareCoordinate]
    exact Submodule.mem_map.mpr ⟨(projection r a g).toAdd,hg,rfl⟩
  · intro x hx
    obtain ⟨v,hv,rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨g,hg⟩ := projection_surjective r a (Multiplicative.ofAdd v)
    have hmem := (binaryImageSquareObstruction_le_iff (projection r a)
      (kernelChart r a) U _).mp le_rfl g (by rw [hg]; exact hv)
    rw [squareCoordinate,hg] at hmem
    exact hmem

theorem imageSquareObstruction_finrank (r a : ℕ)
    (U : Submodule (ZMod 2) (ImageSpace a)) :
    Module.finrank (ZMod 2)
        (binaryImageSquareObstruction (projection r a) (kernelChart r a) U) =
      Module.finrank (ZMod 2) U := by
  rw [imageSquareObstruction_eq]
  exact (Submodule.equivMapOfInjective (squareEmbedding r a)
    (squareEmbedding_injective r a) U).finrank_eq.symm

theorem imageSquareAnnihilator_finrank (r a : ℕ)
    (U : Submodule (ZMod 2) (ImageSpace a)) :
    Module.finrank (ZMod 2)
        (binaryImageSquareObstruction (projection r a) (kernelChart r a) U).dualAnnihilator =
      r+a-Module.finrank (ZMod 2) U := by
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq
    (binaryImageSquareObstruction (projection r a) (kernelChart r a) U)
  rw [imageSquareObstruction_finrank] at h
  have hK : Module.finrank (ZMod 2) (KernelSpace r a) = a+r := by
    simp only [KernelSpace,Module.finrank_prod,Module.finrank_pi,Fintype.card_fin]
  rw [hK] at h
  omega

/-- The exact count of original subgroups with any specified original
mod-two image U. It retains the C4 square equations through the proved obstruction. -/
theorem image_card_gaussian (r a : ℕ) (U : Submodule (ZMod 2) (ImageSpace a)) :
    (Nat.card {H : Subgroup (Original r a) //
      H.map (projection r a) = U.toAddSubgroup.toSubgroup} : ℚ) =
      ∑ j ∈ Finset.range (r+a-Module.finrank (ZMod 2) U+1),
        binaryGaussianCoefficient (r+a-Module.finrank (ZMod 2) U) j *
          2^(Module.finrank (ZMod 2) U*j) := by
  simpa only [imageSquareAnnihilator_finrank] using
    binary_image_lifts_count_gaussian (projection r a) (projection_surjective r a)
      (kernelChart r a) (kernel_central r a) U

end SymmetricSubgroupAsymptotics.BinaryCyclicFourSquareObstruction
