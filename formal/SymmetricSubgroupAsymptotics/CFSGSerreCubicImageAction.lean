import SymmetricSubgroupAsymptotics.CFSGSerreModelRootGeneration
import SymmetricSubgroupAsymptotics.CFSGIntegralCubicRootOperators
import SymmetricSubgroupAsymptotics.CFSGSerreImageRepresentation
import SymmetricSubgroupAsymptotics.CFSGSerreModelLieAutomorphisms
import SymmetricSubgroupAsymptotics.PerfectLieCentralDeviation

/-! Genuine ORIGINAL model-image action through ALL cubic root terms.
There is no quadratic matrix datum. Integral DP intertwining and source
DP cutoff4 themselves kill conjugation coefficients4–6 on the image. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreCubicImageAction
attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra
open CFSG.Models.Chevalley CFSGIntegralCubicRootOperators
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (K : Type) [Field K]
    {B : Type*} [Ring B] [Algebra K B]
    (beta : Space A K →ₗ⁅K⁆ B)
    (E D C : Bool → Fin n → B)
    (hDP : ∀ neg i k x, beta ((integralOperator A neg i k).baseChange K x) =
      operator K (E neg i) (D neg i) (C neg i) k (beta x))
include hDP

def imageRepresentation : Model A K →* (beta.toLinearMap.range ≃ₗ[K] beta.toLinearMap.range) :=
  CFSGSerreImageRepresentation.imageRepresentation A K beta.toLinearMap
    (fun neg i k => operator K (E neg i) (D neg i) (C neg i) k) hDP

theorem imageRepresentation_intertwines (g : Model A K) (x : Space A K) :
    (imageRepresentation A K beta E D C hDP g (beta.toLinearMap.rangeRestrict x)).val =
      beta (g.val x) :=
  CFSGSerreImageRepresentation.imageRepresentation_intertwines A K beta.toLinearMap
    (fun neg i k => operator K (E neg i) (D neg i) (C neg i) k) hDP g x

variable (hge : ∀ neg i k, 4 ≤ k → integralOperator A neg i k = 0)
include hge

/-- These three image coefficient vanishings are PROVED from the SAME
integral operator cutoff, not installed as independent image hypotheses. -/
theorem higher_coefficient_zero (neg : Bool) (i : Fin n) (k : ℕ) (hk : 4 ≤ k)
    (x : Space A K) : operator K (E neg i) (D neg i) (C neg i) k (beta x) = 0 := by
  rw [←hDP, hge neg i k hk, LinearMap.baseChange_zero, LinearMap.zero_apply, map_zero]

/-- Includes the genuine t^3 third divided-power term in characteristic2/3.
No inverse of2,3 or6 occurs in this coefficient-ring equality. -/
theorem rootOperator_intertwines (neg : Bool) (i : Fin n) (t : K) (x : Space A K) :
    beta (rootOperator A K neg i t x) =
      exponential K (E neg i) (D neg i) (C neg i) t * beta x *
        exponential K (E neg i) (D neg i) (C neg i) (-t) := by
  rw [rootOperator]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,hDP]
  exact truncated_sum_eq_conjugation K t (E neg i) (D neg i) (C neg i) (beta x)
    (higher_coefficient_zero A K beta E D C hDP hge neg i 4 (by decide) x)
    (higher_coefficient_zero A K beta E D C hDP hge neg i 5 (by decide) x)
    (higher_coefficient_zero A K beta E D C hDP hge neg i 6 (by decide) x)

theorem imageRepresentation_root (neg : Bool) (i : Fin n) (t : K) (x : Space A K) :
    (imageRepresentation A K beta E D C hDP (CFSGSerreModelRootGeneration.modelRoot A K neg i t)
      (beta.toLinearMap.rangeRestrict x)).val =
      exponential K (E neg i) (D neg i) (C neg i) t * beta x *
        exponential K (E neg i) (D neg i) (C neg i) (-t) := by
  rw [imageRepresentation_intertwines]
  change beta (rootOperator A K neg i t x) = _
  exact rootOperator_intertwines A K beta E D C hDP hge neg i t x

/-- Central deviations are killed by ACTUAL original Lie perfectness,
for cubic root actions just as for quadratic ones. -/
theorem imageRepresentation_injective
    (hperfect : Submodule.span K
      (Set.range (fun xy : Space A K × Space A K => ⁅xy.1,xy.2⁆)) = ⊤)
    (hker : ∀ z : Space A K, beta z = 0 → ∀ y : Space A K, ⁅z,y⁆ = 0) :
    Function.Injective (imageRepresentation A K beta E D C hDP) := by
  apply (imageRepresentation A K beta E D C hDP).ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro g hg
  have hrep : imageRepresentation A K beta E D C hDP g = 1 := hg
  have himage (x : Space A K) : beta (g.val x) = beta x := by
    have h := imageRepresentation_intertwines A K beta E D C hDP g x
    rw [hrep] at h
    exact h.symm
  have heq := PerfectLieCentralDeviation.eq_id_of_central_kernel beta
    (CFSGSerreModelLieAutomorphisms.modelLieHom A K hge g) hperfect hker himage
  change g = 1
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact congrArg (fun f : Space A K →ₗ⁅K⁆ Space A K => f x) heq

end SymmetricSubgroupAsymptotics.CFSGSerreCubicImageAction
