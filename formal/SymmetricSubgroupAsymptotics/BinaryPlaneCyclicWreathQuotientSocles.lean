import SymmetricSubgroupAsymptotics.BinaryPlaneWreathNormalGenerators
import SymmetricSubgroupAsymptotics.TernaryPermutationWreathCyclicQuotientSocles
import SymmetricSubgroupAsymptotics.IrreducibleAbelianSemidirectSubgroupQuotientSocles

/-! Complete original-quotient bound two for arbitrary binary affine
subgroups with independent local Singers and full cyclic block image.
The actual complement is embedded in the local S3 wreath, where the odd
kernel and binary sign image are combined by the coprime maximum theorem.
No original normal denominator is split into independent coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneCyclicWreathQuotientSocles
open BinaryPlaneWreathIrreducible BinaryPlaneWreathNormalGenerators

variable {R I Q : Type} [Group R] [Finite R] [IsCyclic R]
  [MulAction R I] [Fintype I] [DecidableEq I] [Nonempty I] [FaithfulSMul R I] [Group Q]
  (K : Subgroup (BinaryPlaneWreathNormalGenerators.Model (R := R) (I := I)))

theorem socle_of_surjective
    (hloc : ∀ i : I, localEmbedding i singer ∈ actualImage K)
    (htrans : ∀ i j : I, ∃ g : actualImage K,
      (g : W (R := R) (I := I)).right • i = j)
    (hsurj : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := R) (I := I) →* R).comp
        (actualImage K).subtype))
    (c : R) (i : I) (hcycle : ∀ j : I, ∃ n : ℕ, c^n • i = j)
    (hR : Nat.Coprime 3 (Nat.card R))
    (π : K →* Q) (hπ : Function.Surjective π) : SocleNormalGeneratorBound Q 2 := by
  apply IrreducibleAbelianSemidirectSubgroup.socle_of_surjective_of_image_quotients
    BinaryPlaneWreathIrreducible.action K
    (BinaryPlaneWreathIrreducible.action_injective.comp Subtype.val_injective)
    (BinaryPlaneWreathIrreducible.irreducible (actualImage K) hloc htrans)
    (by decide : 1 ≤ 2) ?_ π hπ
  intro N hN
  letI := hN
  let f := (wreathMap (R := R) (I := I)).comp (actualImage K).subtype
  let J := f.range
  let e : actualImage K ≃* J := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h => (wreathMap_injective.comp Subtype.val_injective)
      (congrArg Subtype.val h),f.rangeRestrict_surjective⟩
  have hb : Function.Surjective
      ((PermutationalWreathProduct.rightHom :
        TernaryPermutationWreathEmbedding.W (R := R) (I := I) →* R).comp J.subtype) := by
    intro r
    obtain ⟨g,hg⟩ := hsurj r
    exact ⟨f.rangeRestrict g,hg⟩
  exact TernaryPermutationWreathCyclicQuotientSocles.socle_of_surjective J hb c i hcycle hR
    ((QuotientGroup.mk' N).comp e.symm.toMonoidHom)
    ((QuotientGroup.mk'_surjective N).comp e.symm.surjective)

theorem quotientSocle
    (hloc : ∀ i : I, localEmbedding i singer ∈ actualImage K)
    (htrans : ∀ i j : I, ∃ g : actualImage K,
      (g : W (R := R) (I := I)).right • i = j)
    (hsurj : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := R) (I := I) →* R).comp
        (actualImage K).subtype))
    (c : R) (i : I) (hcycle : ∀ j : I, ∃ n : ℕ, c^n • i = j)
    (hR : Nat.Coprime 3 (Nat.card R))
    (N : Subgroup K) [N.Normal] : SocleNormalGeneratorBound (K ⧸ N) 2 :=
  socle_of_surjective K hloc htrans hsurj c i hcycle hR
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end SymmetricSubgroupAsymptotics.BinaryPlaneCyclicWreathQuotientSocles

end
