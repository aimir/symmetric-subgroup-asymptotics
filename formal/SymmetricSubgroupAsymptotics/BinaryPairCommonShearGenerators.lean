import SymmetricSubgroupAsymptotics.BinaryPairPolynomialKernelShears
import SymmetricSubgroupAsymptotics.BinaryCommonShearGeneratorBound
import SymmetricSubgroupAsymptotics.FiniteModulePaddedGenerators

/-! Six generators for every original natural submodule when the actual
top contains the four Boolean translations and the actual correlated
kernel contains the common eight-dimensional shear space. Every operator
below is `u - 1` in the original group algebra; lift offsets are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

open BinaryBooleanFourPolynomialCoordinates BinaryElementaryPairMonomialWidth
open BinaryMonomialRaisingWords
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16))

theorem naturalSubrepresentation_generatedBy_six_of_common_shears
    (e : Equiv.Perm (Fin 16))
    (htranslations : ∀ i : Fin 4, ∃ u : U,
      ∀ j, (F.top u)⁻¹ (e.symm j) = e.symm (flipIndex i j))
    (hshears : ∀ b : Fin 16, BinaryThreeVariablePairMonomialWidth.Allowed (support b) →
      (fun x => monomial (support b) (e x)) ∈ F.kernelSpace)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X)) :
    RepresentationGeneratedBy W.toRepresentation 6 := by
  let M := W.toRepresentation.asModule
  letI : AddCommGroup M := inferInstanceAs (AddCommGroup W.toRepresentation.asModule)
  letI : Module (ZMod 2) M := inferInstanceAs (Module (ZMod 2) W.toRepresentation.asModule)
  letI : Module (ZMod 2)[U] M :=
    inferInstanceAs (Module (ZMod 2)[U] W.toRepresentation.asModule)
  let C₀ : (X → ZMod 2) →ₗ[ZMod 2] (Fin 32 → ZMod 2) :=
    (pairLayerFlatten (w := 16)).toLinearMap.comp
      (F.polynomialPairCoordinateEquiv e).toLinearMap
  let C : M →ₗ[ZMod 2] (Fin 32 → ZMod 2) :=
    C₀.comp (W.toSubmodule.subtype.comp W.toRepresentation.asModuleEquiv.toLinearMap)
  have hC : Function.Injective C :=
    (pairLayerFlatten (w := 16)).injective.comp
      ((F.polynomialPairCoordinateEquiv e).injective.comp
        (Subtype.val_injective.comp W.toRepresentation.asModuleEquiv.injective))
  have hd : ModuleGeneratedBy (ZMod 2)[U] M (Module.finrank (ZMod 2) W.toSubmodule) := by
    exact representationGeneratedBy_scalar_finrank W.toRepresentation
  have hdiff (u : U) (v : M) :
      C ((MonoidAlgebra.single u (1 : ZMod 2) - 1) • v) =
        C₀ (permutationFunctionRepresentation (ZMod 2) U X u
          (W.toRepresentation.asModuleEquiv v).val - (W.toRepresentation.asModuleEquiv v).val) := by
    rw [sub_smul, Representation.single_smul, one_smul, one_smul]
    rfl
  have hstep : ∀ op a b, BinaryMonomialRaisingWords.step op a = some b →
      ∀ v : M, FiniteRowLeadingWeight.HasLeading (C v) (index a) →
        ∃ r : (ZMod 2)[U], FiniteRowLeadingWeight.HasLeading (C (r • v)) (index b) := by
    intro op a b hab v hv
    rcases a with ⟨layer, a⟩
    cases op with
    | derivative i =>
      change (if i ∈ support a then some (layer, removeIndex i a) else none) = some b at hab
      split_ifs at hab with hi
      · have he : (layer, removeIndex i a) = b := Option.some.inj hab
        subst b
        obtain ⟨u, hu⟩ := htranslations i
        let f := (W.toRepresentation.asModuleEquiv v).val
        let z := (F.polynomialPairCoordinateEquiv e f).1
        let s := (F.polynomialPairCoordinateEquiv e f).2
        have hc : C ((MonoidAlgebra.single u (1 : ZMod 2) - 1) • v) =
            Fin.append (derivative i z + offsetError (F.polynomialLiftOffset e u) i s)
              (derivative i s) := by
          rw [hdiff]
          change pairLayerFlatten (F.polynomialPairCoordinateEquiv e
            (permutationFunctionRepresentation (ZMod 2) U X u f - f)) = _
          rw [F.polynomialPairCoordinate_difference e u i hu f]
          rfl
        refine ⟨MonoidAlgebra.single u (1 : ZMod 2) - 1, ?_⟩
        rw [hc]
        cases layer
        · change FiniteRowLeadingWeight.HasLeading (Fin.append z s) (Fin.castAdd 16 a) at hv
          exact triangularDerivative_lower i a z s _ hv hi
        · change FiniteRowLeadingWeight.HasLeading (Fin.append z s) (Fin.natAdd 16 a) at hv
          exact triangularDerivative_upper i a z s _ hv hi
    | shear c =>
      change (if layer = true ∧ BinaryThreeVariablePairMonomialWidth.Allowed (support c) ∧
          Disjoint (support c) (support a) then some (false, unionIndex c a) else none) = some b at hab
      split_ifs at hab with hvalid
      · rcases hvalid with ⟨rfl, hcAllowed, hdisj⟩
        have he : (false, unionIndex c a) = b := Option.some.inj hab
        subst b
        obtain ⟨k, hk⟩ := F.exists_kernel_bits _ (hshears c hcAllowed)
        have hbits (j : Fin 16) : F.bits k (e.symm j) = monomial (support c) j := by
          rw [hk]
          change monomial (support c) (e (e.symm j)) = monomial (support c) j
          rw [Equiv.apply_symm_apply]
        let f := (W.toRepresentation.asModuleEquiv v).val
        let z := (F.polynomialPairCoordinateEquiv e f).1
        let s := (F.polynomialPairCoordinateEquiv e f).2
        have hc : C ((MonoidAlgebra.single (k : U) (1 : ZMod 2) - 1) • v) =
            Fin.append (monomialMultiplier c s) (0 : V) := by
          rw [hdiff]
          change pairLayerFlatten (F.polynomialPairCoordinateEquiv e
            (permutationFunctionRepresentation (ZMod 2) U X (k : U) f - f)) = _
          rw [F.polynomialPairCoordinate_kernel_difference e k c hbits f]
          rfl
        refine ⟨MonoidAlgebra.single (k : U) (1 : ZMod 2) - 1, ?_⟩
        rw [hc]
        change FiniteRowLeadingWeight.HasLeading (Fin.append z s) (Fin.natAdd 16 a) at hv
        exact kernelShear_hasLeading c a z s hv hdisj
  obtain ⟨S, hS, hcard⟩ := binary_generating_finset_le_six_of_common_shear_steps
    (A := (ZMod 2)[U]) (M := M) hd C hC hstep
  exact ModuleGeneratedBy.of_finset_card_le S hS 6 hcard

end SymmetricSubgroupAsymptotics.BinaryPairFrame
