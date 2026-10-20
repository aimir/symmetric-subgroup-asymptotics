import SymmetricSubgroupAsymptotics.ProductQuartetCanonicalKernelChart
import SymmetricSubgroupAsymptotics.BinaryPlaneKleinRetainedQuotientSocles
import SymmetricSubgroupAsymptotics.BinaryPlaneDihedralRetainedQuotientSocles
import SymmetricSubgroupAsymptotics.NonbinaryQuotientRetainsBinaryKernel

/-! Nonbinary original quotients in the actual regular-Klein and D8
coarse charts have whole socle bound two. The charts concern only the
literal point action; translation and quotient data are constructed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathActualOddKernel
open CanonicalQuartetKernel
abbrev QuartetKlein := BinaryRegularKleinWreath.R
local instance quartetBinaryTopKleinFintype : Fintype QuartetKlein := BinaryRegularKleinWreath.rFintype
local instance quartetBinaryTopKleinDecidableEq : DecidableEq QuartetKlein := BinaryRegularKleinWreath.rDecidableEq

variable {X : Type} [Finite X] {T : Subgroup (Equiv.Perm X)}
  (C : ProductBlockFrame T (Fin 4) Plane)

 theorem klein_nonbinary_quotientSocle
    (e : C.top.range ≃* QuartetKlein) (c : Fin 4 ≃ QuartetKlein)
    (hc : ∀ b : C.top.range,∀ i : Fin 4,c (b • i)=e b*c i)
    (N : Subgroup T) [N.Normal] (hQ : ¬ IsPGroup 2 (T ⧸ N)) :
    SocleNormalGeneratorBound (T ⧸ N) 2 := by
  let D := B C e c hc
  let q := pi C e c hc
  have hR : IsPGroup 2 QuartetKlein := by
    intro r
    exact ⟨1,(by decide +kernel : ∀ r : QuartetKlein,r^2=1) r⟩
  have hnot : ¬ (oddKernel D).comap q≤N :=
    nonbinary_quotient_not_le_kernel ((signProjection D).comp q)
      (sign_isPGroup (I := QuartetKlein) hR) N hQ
  have hT : ¬ IsPGroup 2 T := fun h => hQ (h.to_quotient N)
  exact BinaryPlaneKleinRetainedQuotientSocles.quotientSocle D q
    (pi_surjective C e c hc) (A C e c hc) (E C e c hc)
    (inclusion C e c hc) (inclusion_injective C e c hc)
    (blocks_surjective C e c hc) hT N hnot

 theorem dihedral_nonbinary_quotientSocle
    (e : C.top.range ≃* DihedralEightRegularKleinBlockModel.Q)
    (c : Fin 4 ≃ QuartetKlein)
    (hc : ∀ b : C.top.range,∀ i : Fin 4,c (b • i)=e b • c i)
    (N : Subgroup T) [N.Normal] (hQ : ¬ IsPGroup 2 (T ⧸ N)) :
    SocleNormalGeneratorBound (T ⧸ N) 2 := by
  let D := B C e c hc
  let q := pi C e c hc
  have hR := DihedralEightRegularKleinBlockModel.binary
  have hnot : ¬ (oddKernel D).comap q≤N :=
    nonbinary_quotient_not_le_kernel ((signProjection D).comp q)
      (sign_isPGroup (I := QuartetKlein) hR) N hQ
  have hT : ¬ IsPGroup 2 T := fun h => hQ (h.to_quotient N)
  exact BinaryPlaneDihedralRetainedQuotientSocles.quotientSocle D q
    (pi_surjective C e c hc) (A C e c hc) (E C e c hc)
    (inclusion C e c hc) (inclusion_injective C e c hc)
    (blocks_surjective C e c hc) hT N hnot

end SymmetricSubgroupAsymptotics.ProductBlockFrame
