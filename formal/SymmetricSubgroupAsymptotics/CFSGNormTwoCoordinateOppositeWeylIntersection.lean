import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeNormalizerIntersection

/-! The actual rank-one Weyl parabolic has the same simple-root
intersection as the full negative-normalizer/simple-root join. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeWeylIntersection
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGSerreQuadraticMatrix CFSGNormTwoGeckRootSignSteps
open CFSGNormTwoCoordinateOppositeNormalizerIntersection
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

theorem negative_normalizer_weyl_join_eq_simple_join (K : Type) [Field K] (i : Fin r) :
    (Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K true : Set _)⊓canonicalElementaryGroup D K)⊔
      Subgroup.closure {canonicalWeyl D K i}=
    (Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K true : Set _)⊓canonicalElementaryGroup D K)⊔
      canonicalRootSubgroup D K false i := by
  let N := Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K true : Set _)⊓canonicalElementaryGroup D K
  let R := canonicalRootSubgroup D K false i
  let W := Subgroup.closure {canonicalWeyl D K i}
  have hn (t : K) : canonicalRoot D K true i t∈N :=
    ⟨(rootGroup A hs hp b₀ s₀ K true).le_normalizer (Subgroup.subset_closure ⟨(i,t),rfl⟩),
      (canonicalElementaryRoot D K true i t).property⟩
  have hp1 : canonicalRoot D K false i 1∈R := ⟨1,rfl⟩
  have hW : W≤N⊔R := by
    apply (Subgroup.closure_le _).mpr
    rintro g (rfl : g=canonicalWeyl D K i)
    change canonicalRoot D K false i 1*canonicalRoot D K true i (-1)*
      canonicalRoot D K false i 1∈N⊔R
    exact (N⊔R).mul_mem ((N⊔R).mul_mem
      ((show R≤N⊔R from le_sup_right) hp1) ((show N≤N⊔R from le_sup_left) (hn (-1))))
      ((show R≤N⊔R from le_sup_right) hp1)
  have hR : R≤N⊔W := by
    rintro g ⟨t,rfl⟩
    have hw : canonicalWeyl D K i∈N⊔W :=
      (show W≤N⊔W from le_sup_right) (Subgroup.subset_closure (Set.mem_singleton _))
    have hmem := (N⊔W).mul_mem ((N⊔W).mul_mem hw
      ((show N≤N⊔W from le_sup_left) (hn (-t)))) ((N⊔W).inv_mem hw)
    have he := inverse_self_root_word A hs hp b₀ s₀ K i t
    have hflip : canonicalWeyl D K i*canonicalRoot D K true i (-t)*(canonicalWeyl D K i)⁻¹=
        canonicalRoot D K false i t := by
      rw [←he]
      group
    rwa [hflip] at hmem
  exact le_antisymm (sup_le le_sup_left hW) (sup_le le_sup_left hR)

theorem opposite_normalizer_weyl_intersection (K : Type) [Field K]
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (i : Fin r) :
    rootGroup A hs hp b₀ s₀ K false ⊓
      ((Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K true : Set _)⊓canonicalElementaryGroup D K)⊔
        Subgroup.closure {canonicalWeyl D K i})=canonicalRootSubgroup D K false i := by
  rw [negative_normalizer_weyl_join_eq_simple_join]
  exact opposite_normalizer_parabolic_intersection A hd hs hp ho K ε hε hA hidentity i

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeWeylIntersection
