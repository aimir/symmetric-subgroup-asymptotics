import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateComplementNormalizer
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSelfRootConjugation

/-! The Weyl extension of the FULL positive normalizer equals its
extension by the literal negative simple-root subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveWeylJoin
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckSelfRootConjugation
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

theorem positive_normalizer_weyl_join_eq_negative_join (K : Type) [Field K] (i : Fin r) :
    (Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)⊓canonicalElementaryGroup D K)⊔
      Subgroup.closure {canonicalWeyl D K i}=
    (Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)⊓canonicalElementaryGroup D K)⊔
      canonicalRootSubgroup D K true i := by
  let N := Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)⊓canonicalElementaryGroup D K
  let R := canonicalRootSubgroup D K true i
  let W := Subgroup.closure {canonicalWeyl D K i}
  have hp' (t : K) : canonicalRoot D K false i t∈N :=
    ⟨(rootGroup A hs hp b₀ s₀ K false).le_normalizer (Subgroup.subset_closure ⟨(i,t),rfl⟩),
      (canonicalElementaryRoot D K false i t).property⟩
  have hW : W≤N⊔R := by
    apply (Subgroup.closure_le _).mpr
    rintro g (rfl : g=canonicalWeyl D K i)
    change canonicalRoot D K false i 1*canonicalRoot D K true i (-1)*
      canonicalRoot D K false i 1∈N⊔R
    exact (N⊔R).mul_mem ((N⊔R).mul_mem
      ((show N≤N⊔R from le_sup_left) (hp' 1))
      ((show R≤N⊔R from le_sup_right) ⟨-1,rfl⟩))
      ((show N≤N⊔R from le_sup_left) (hp' 1))
  have hR : R≤N⊔W := by
    rintro g ⟨t,rfl⟩
    have hw : canonicalWeyl D K i∈N⊔W :=
      (show W≤N⊔W from le_sup_right) (Subgroup.subset_closure (Set.mem_singleton _))
    have hm := (N⊔W).mul_mem ((N⊔W).mul_mem hw
      ((show N≤N⊔W from le_sup_left) (hp' (-t)))) ((N⊔W).inv_mem hw)
    have he : canonicalWeyl D K i*canonicalRoot D K false i (-t)*(canonicalWeyl D K i)⁻¹=
        canonicalRoot D K true i t := by
      simpa only [neg_neg] using self_root_word A hs hp b₀ s₀ K i (-t)
    rwa [he] at hm
  exact le_antisymm (sup_le le_sup_left hW) (sup_le le_sup_left hR)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveWeylJoin
