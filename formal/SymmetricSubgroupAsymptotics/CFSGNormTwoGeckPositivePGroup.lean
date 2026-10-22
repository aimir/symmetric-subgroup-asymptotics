import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckHeightSupport
import SymmetricSubgroupAsymptotics.CFSGWeightedRootPGroup
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldOpposition

/-! The literal positive simple-root generated Geck subgroup is a p-group
in defining characteristic, by the actual height support. Its actual
integral opposition image is exactly the negative simple-root subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPositivePGroup
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckFieldOpposition
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

def rootGroup (K : Type) [Field K] (neg : Bool) : Subgroup
    ((Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ) :=
  Subgroup.closure (Set.range (fun z : Fin r×K=>canonicalRoot (realizationData A hs hp b s) K neg z.1 z.2))

theorem positive_isPGroup (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (hheight : ∀i : b.support,height (i:Roots A).val=1)
    (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    IsPGroup p (rootGroup A hs hp b s K false) := by
  apply CFSGWeightedRootPGroup.generated_isPGroup (weight A hs hp b height)
    (fun z : Fin r×K=>canonicalRoot (realizationData A hs hp b s) K false z.1 z.2)
  intro z
  exact CFSGWeightedRootPGroup.quadratic_identity_on_nonincreasing (weight A hs hp b height)
    (canonicalRoot (realizationData A hs hp b s) K false z.1 z.2)
    (fieldRoot (realizationData A hs hp b s) K false z.1)
    (fieldSecond (realizationData A hs hp b s) K false z.1) z.2
    (canonicalRoot_val (realizationData A hs hp b s) K false z.1 z.2)
    (field_E_strict A hs hp b s height hheight K z.1)
    (field_second_strict A hs hp b s height hheight K z.1)

theorem opposition_positive_eq_negative (K : Type) [Field K] :
    (rootGroup A hs hp b s K false).map
      (MulAut.conj (oppositionUnit A hs hp b K)).toMonoidHom=rootGroup A hs hp b s K true := by
  rw [rootGroup,MonoidHom.map_closure,rootGroup]
  congr 1
  ext x
  constructor
  · rintro ⟨y,⟨z,rfl⟩,rfl⟩
    refine ⟨z,?_⟩
    exact (canonicalRoot_conjugate A hs hp b s K false z.1 z.2).symm
  · rintro ⟨z,rfl⟩
    exact ⟨canonicalRoot (realizationData A hs hp b s) K false z.1 z.2,⟨z,rfl⟩,
      canonicalRoot_conjugate A hs hp b s K false z.1 z.2⟩

theorem negative_isPGroup (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (hheight : ∀i : b.support,height (i:Roots A).val=1)
    (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    IsPGroup p (rootGroup A hs hp b s K true) := by
  rw [←opposition_positive_eq_negative A hs hp b s K]
  exact (positive_isPGroup A hs hp b s height hheight K p).map _

theorem positive_sup_negative (K : Type) [Field K] :
    rootGroup A hs hp b s K false⊔rootGroup A hs hp b s K true=
      canonicalElementaryGroup (realizationData A hs hp b s) K := by
  apply le_antisymm
  · apply sup_le
    · apply (Subgroup.closure_le _).mpr
      rintro _ ⟨z,rfl⟩
      exact (canonicalElementaryRoot (realizationData A hs hp b s) K false z.1 z.2).property
    · apply (Subgroup.closure_le _).mpr
      rintro _ ⟨z,rfl⟩
      exact (canonicalElementaryRoot (realizationData A hs hp b s) K true z.1 z.2).property
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨neg,i,t,rfl⟩
    cases neg
    · have hL : rootGroup A hs hp b s K false≤
          rootGroup A hs hp b s K false⊔rootGroup A hs hp b s K true := le_sup_left
      exact hL (Subgroup.subset_closure ⟨(i,t),rfl⟩)
    · have hR : rootGroup A hs hp b s K true≤
          rootGroup A hs hp b s K false⊔rootGroup A hs hp b s K true := le_sup_right
      exact hR (Subgroup.subset_closure ⟨(i,t),rfl⟩)

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPositivePGroup
