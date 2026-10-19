import SymmetricSubgroupAsymptotics.ProductQuartetCanonicalKernelChart
import SymmetricSubgroupAsymptotics.BinaryPlaneCyclicActualKernelQuotientSocles

/-! A cyclic coarse-top chart gives the original quartet quotient-socle
bound two. Correlated local maps and all original denominators are kept. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
open BinaryPlanePermutationAffineEquiv
open CanonicalQuartetKernel

variable {X I R J : Type} [Finite X] [Fintype J] [DecidableEq J]
  [Group R] [Finite R] [IsCyclic R] [MulAction R J]
  {T : Subgroup (Equiv.Perm X)} (C : ProductBlockFrame T I Plane)

 theorem cyclic_nonbinary_quotientSocle
    (e : C.top.range ≃* R) (c : I ≃ J)
    (hc : ∀ b : C.top.range,∀ i : I,c (b • i)=e b • c i)
    (g : R) (i₀ : J) (hcycle : ∀ i : J,∃ n : ℕ,g^n • i₀=i)
    (hR : IsPGroup 2 R)
    (N : Subgroup T) [N.Normal] (hQ : ¬ IsPGroup 2 (T ⧸ N)) :
    SocleNormalGeneratorBound (T ⧸ N) 2 := by
  have hT : ¬ IsPGroup 2 T := fun h => hQ (h.to_quotient N)
  exact BinaryPlaneCyclicActualKernelQuotientSocles.quotientSocle
    (B C e c hc) (pi C e c hc) (pi_surjective C e c hc)
    (A C e c hc) (E C e c hc) (inclusion C e c hc)
    (inclusion_injective C e c hc) (blocks_surjective C e c hc)
    g i₀ hcycle hR hT N

end SymmetricSubgroupAsymptotics.ProductBlockFrame
