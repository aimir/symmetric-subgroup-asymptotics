import SymmetricSubgroupAsymptotics.BinaryPairTriangularLeadingDerivatives
import SymmetricSubgroupAsymptotics.BinaryGenericPairLeadingGeneratorBound
import SymmetricSubgroupAsymptotics.BinaryPairPolynomialGeneralKernelShears
import SymmetricSubgroupAsymptotics.FiniteModulePaddedGenerators

/-! Uniform generation of every original natural subrepresentation
from genuine triangular top lifts and genuine pointwise kernel shears.
No pure translation, split extension, or independent projection module
is substituted for the original action. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open BinaryBooleanFourPolynomialCoordinates BinaryElementaryPairMonomialWidth
open BinaryMonomialRaisingWords (index)
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16))

theorem uniform_generatedBy_of_triangular_leading_shears
    (T : BinaryTriangularPointCoordinates F.top.range (Fin 16) 4)
    (Allowed : Finset (Fin 4) → Prop) (w : ℕ)
    (hshears : ∀ b : Fin 16, Allowed (support b) → ∃ a : V,
      FiniteRowLeadingWeight.HasLeading a b ∧
        (fun x => evaluate a (T.booleanPointLabels x)) ∈ F.kernelSpace)
    (hwidth : ∀ s : Finset Monomial,
      IsAntichain (BinaryGenericPairLeadingGeneratorBound.Raises Allowed) (s : Set Monomial) →
        s.card ≤ w) :
    UniformSubrepresentationGeneratorBound (permutationFunctionRepresentation (ZMod 2) U X) w := by
  intro W
  let M := W.toRepresentation.asModule
  letI : AddCommGroup M := inferInstanceAs (AddCommGroup W.toRepresentation.asModule)
  letI : Module (ZMod 2) M := inferInstanceAs (Module (ZMod 2) W.toRepresentation.asModule)
  letI : Module (ZMod 2)[U] M :=
    inferInstanceAs (Module (ZMod 2)[U] W.toRepresentation.asModule)
  let C₀ : (X → ZMod 2) →ₗ[ZMod 2] (Fin 32 → ZMod 2) :=
    (pairLayerFlatten (w := 16)).toLinearMap.comp
      (F.polynomialPairCoordinateEquiv T.booleanPointLabels).toLinearMap
  let C : M →ₗ[ZMod 2] (Fin 32 → ZMod 2) :=
    C₀.comp (W.toSubmodule.subtype.comp W.toRepresentation.asModuleEquiv.toLinearMap)
  have hC : Function.Injective C :=
    (pairLayerFlatten (w := 16)).injective.comp
      ((F.polynomialPairCoordinateEquiv T.booleanPointLabels).injective.comp
        (Subtype.val_injective.comp W.toRepresentation.asModuleEquiv.injective))
  have hd : ModuleGeneratedBy (ZMod 2)[U] M (Module.finrank (ZMod 2) W.toSubmodule) :=
    representationGeneratedBy_scalar_finrank W.toRepresentation
  have hdiff (u : U) (v : M) :
      C ((MonoidAlgebra.single u (1 : ZMod 2) - 1) • v) =
        C₀ (permutationFunctionRepresentation (ZMod 2) U X u
          (W.toRepresentation.asModuleEquiv v).val - (W.toRepresentation.asModuleEquiv v).val) := by
    rw [sub_smul, Representation.single_smul, one_smul, one_smul]
    rfl
  have hderivative : ∀ (l : Bool) (i : Fin 4) (v : M) (a : Fin 16),
      FiniteRowLeadingWeight.HasLeading (C v) (index (l, a)) → i ∈ support a →
      ∃ r : (ZMod 2)[U], FiniteRowLeadingWeight.HasLeading (C (r • v))
        (index (l, removeIndex i a)) := by
    intro l i v a hv hi
    obtain ⟨u, hu⟩ := F.exists_actual_pair_leading_derivative T i
    refine ⟨MonoidAlgebra.single u (1 : ZMod 2) - 1, ?_⟩
    rw [hdiff]
    exact hu (W.toRepresentation.asModuleEquiv v).val l a hv hi
  have hshear : ∀ (v : M) (a b : Fin 16),
      FiniteRowLeadingWeight.HasLeading (C v) (index (true, a)) →
      Allowed (support b) → Disjoint (support b) (support a) →
      ∃ r : (ZMod 2)[U], FiniteRowLeadingWeight.HasLeading (C (r • v))
        (index (false, unionIndex b a)) := by
    intro v a b hv hb hdisj
    obtain ⟨aKernel, haKernel, hmemKernel⟩ := hshears b hb
    obtain ⟨k, hk⟩ := F.exists_kernel_bits _ hmemKernel
    have hbits (x : Fin 16) : F.bits k (T.booleanPointLabels.symm x) = evaluate aKernel x := by
      rw [hk]
      change evaluate aKernel (T.booleanPointLabels (T.booleanPointLabels.symm x)) = _
      rw [Equiv.apply_symm_apply]
    let f := (W.toRepresentation.asModuleEquiv v).val
    let z := (F.polynomialPairCoordinateEquiv T.booleanPointLabels f).1
    let s := (F.polynomialPairCoordinateEquiv T.booleanPointLabels f).2
    have hc : C ((MonoidAlgebra.single (k : U) (1 : ZMod 2) - 1) • v) =
        Fin.append (polynomialMultiply aKernel s) (0 : V) := by
      rw [hdiff]
      change pairLayerFlatten (F.polynomialPairCoordinateEquiv T.booleanPointLabels
        (permutationFunctionRepresentation (ZMod 2) U X (k : U) f - f)) = _
      rw [F.polynomialPairCoordinate_general_kernel_difference T.booleanPointLabels k aKernel hbits f]
      rfl
    refine ⟨MonoidAlgebra.single (k : U) (1 : ZMod 2) - 1, ?_⟩
    rw [hc]
    change FiniteRowLeadingWeight.HasLeading (Fin.append z s) (Fin.natAdd 16 a) at hv
    exact kernelGeneralShear_hasLeading aKernel z s b a haKernel hv hdisj
  obtain ⟨S, hS, hcard⟩ := BinaryGenericPairLeadingGeneratorBound.generating_finset_le_of_width
    C hd hC Allowed hderivative hshear hwidth
  exact ModuleGeneratedBy.of_finset_card_le S hS w hcard

end SymmetricSubgroupAsymptotics.BinaryPairFrame
