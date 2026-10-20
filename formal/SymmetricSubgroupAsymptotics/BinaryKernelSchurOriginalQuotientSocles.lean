import SymmetricSubgroupAsymptotics.BinaryKernelSchurSocleTwo
import SymmetricSubgroupAsymptotics.OriginalKernelNonbinaryResidual
import SymmetricSubgroupAsymptotics.OriginalKernelPrimeSectionUniform
import SymmetricSubgroupAsymptotics.OriginalKernelSectionOddRestriction
import SymmetricSubgroupAsymptotics.CoprimeKernelQuotientSocles
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralCentralQuotients

/-! The Schur/odd-image sharing theorem retains the exact original N,
its elementary kernel section and actual residual top quotient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryKernelSchurOriginalQuotientSocles
open OriginalKernelModuleChart
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem quotientSocle {G B X : Type} [Group G] [Finite G] [IsSolvable G]
    [Group B] [Finite B] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (hX : Nat.card X=12) (pi : G →* B) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 2) B) [FiniteDimensional (ZMod 2) A]
    (E : OriginalKernelModuleChart pi A)
    (hB : ∀ (L : Subgroup B) [L.Normal], MarkedC4.normalGen L≤2)
    (hno : NoTernaryQuotient G)
    (hhead : ∀ (M : Subgroup G) [M.Normal],
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 M)≤2)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) 2 := by
  letI : IsSolvable (G ⧸ N) := solvable_of_surjective (QuotientGroup.mk'_surjective N)
  let K := E.sectionRepresentation pi A N
  letI : FiniteDimensional (ZMod 2) K := by
    change FiniteDimensional (ZMod 2) (E.sectionModule pi A N)
    infer_instance
  let s := sectionTop pi N hpi
  have hs : Function.Surjective s := by
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pi.ker ⊔ N) x
    exact ⟨pi g,sectionTop_apply pi N hpi g⟩
  have hD : ∀ (L : Subgroup (G ⧸ (pi.ker ⊔ N))) [L.Normal],
      MarkedC4.normalGen L≤2 := by
    intro L _
    exact CoprimeKernelQuotientSocles.normalGen_image_bound s hs 2
      (fun M hM => by letI := hM; exact hB M) L
  have hk : IsPGroup 2 (base pi N).ker :=
    (E.quotientChart pi A N).kernel_isPGroup_two (base pi N) K
  have hsection := binarySectionalRankBound_of_faithful_permutation_quotient
    (X := X) (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hrank : PrimeSectionalRankBound 2 (G ⧸ N) 6 := by
    simpa only [hX] using hsection
  exact BinaryKernelSchurSocleTwo.socle_two (base pi N) (base_surjective pi N)
    hk hD (hno.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N))
    hrank (TwelvePointRemainingStructural.centralOmega_quotient_finrank_le_allRelativeHeads 2 hhead N)
end SymmetricSubgroupAsymptotics.BinaryKernelSchurOriginalQuotientSocles
