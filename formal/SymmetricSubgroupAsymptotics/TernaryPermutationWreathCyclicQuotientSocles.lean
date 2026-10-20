import SymmetricSubgroupAsymptotics.TernaryPermutationWreathEmbedding
import SymmetricSubgroupAsymptotics.TernarySignedCyclicCoprimeQuotientSocles

/-! Quotient-socle bound two for every actual subgroup of the local S3
wreath with full coprime cyclic block image. Signs, translations and their
correlations are retained through the injective affine chart. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.TernaryPermutationWreathCyclicQuotientSocles
open TernaryPermutationWreathEmbedding

variable {R I Q : Type} [Group R] [Finite R] [IsCyclic R]
  [MulAction R I] [Fintype I] [DecidableEq I] [Group Q]
  (C : Subgroup (W (R := R) (I := I)))

theorem socle_of_surjective
    (hsurj : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := R) (I := I) →* R).comp C.subtype))
    (c : R) (i : I) (hcycle : ∀ j : I, ∃ n : ℕ, c^n • i = j)
    (hR : Nat.Coprime 3 (Nat.card R))
    (π : C →* Q) (hπ : Function.Surjective π) : SocleNormalGeneratorBound Q 2 := by
  let f : C →* Target (R := R) (I := I) := affine.comp C.subtype
  let J := f.range
  let e : C ≃* J := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h => (affine_injective.comp Subtype.val_injective)
      (congrArg Subtype.val h),f.rangeRestrict_surjective⟩
  have hb : Function.Surjective (TernarySignedPermutationSubgroupSocles.blocks signs J) := by
    intro r
    obtain ⟨g,hg⟩ := hsurj r
    refine ⟨(LinearSemidirectSubgroupKernelChart.projection
      (TernarySignedPermutationSubgroupSocles.linearAction signs) J).rangeRestrict
        (f.rangeRestrict g),?_⟩
    exact hg
  exact TernarySignedCyclicCoprimeQuotientSocles.socle_of_surjective signs J
    c i hcycle hb hR (π.comp e.symm.toMonoidHom) (hπ.comp e.symm.surjective)

theorem quotientSocle
    (hsurj : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := R) (I := I) →* R).comp C.subtype))
    (c : R) (i : I) (hcycle : ∀ j : I, ∃ n : ℕ, c^n • i = j)
    (hR : Nat.Coprime 3 (Nat.card R))
    (N : Subgroup C) [N.Normal] : SocleNormalGeneratorBound (C ⧸ N) 2 :=
  socle_of_surjective C hsurj c i hcycle hR
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end SymmetricSubgroupAsymptotics.TernaryPermutationWreathCyclicQuotientSocles

end
