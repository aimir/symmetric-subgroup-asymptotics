import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingScalarGauge
import SymmetricSubgroupAsymptotics.BinaryCubicScalarLinearRepresentation

/-! The actual cubic centralizer subgroup carries the scalar-linear
representation needed for the polynomial witness. All operators are
restrictions of the actual linear image in its constructed chart. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingScalarCentralizer
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathActualOddKernel
open BinaryPlaneAlternatingKernelPartition (Frame Cubic)
open BinaryPlaneAlternatingCentralizerCommutators (R)
open BinaryPlaneAlternatingCentralizerKleinLift (alpha)
open BinaryQuadraticField (Scalar omega)
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

abbrev H (C : Subgroup Frame) := (alpha C).ker

/-- Actual K lies in its own centralizer; no abstract scalar subgroup is
adjoined to the action. -/
def cubic (C : Subgroup Frame) (e : oddKernel C ≃* Cubic) : H C :=
  ⟨(BinaryPlaneRankOneOddGenerator.generator C e : C),by
    apply MulEquiv.ext
    intro o
    apply Subtype.ext
    let k := BinaryPlaneRankOneOddGenerator.generator C e
    have hm : (k : C)*(o : C)=(o : C)*(k : C) :=
      congrArg (fun v : oddKernel C => (v : C))
        (isMulCommutative_iff.mp (commutative C) k o)
    change (k : C)*(o : C)*(k : C)⁻¹=(o : C)
    rw [hm,mul_assoc,mul_inv_cancel,mul_one]⟩

theorem centralizes_cubic (C : Subgroup Frame) (e : oddKernel C ≃* Cubic)
    (h : H C) : Commute h (cubic C e) := by
  have ha : alpha C (h : C)=1 := h.property
  have hh := congrArg (fun f : MulAut (oddKernel C) =>
    (f (BinaryPlaneRankOneOddGenerator.generator C e) : C)) ha
  change (h : C)*(BinaryPlaneRankOneOddGenerator.generator C e : C)*(h : C)⁻¹=
    (BinaryPlaneRankOneOddGenerator.generator C e : C) at hh
  apply Subtype.ext
  exact mul_inv_eq_iff_eq_mul.mp hh

/-- The actual centralizer restriction is binary-conjugate to the
constructed scalar representation. No numerical generation premise. -/
theorem exists_representation (C : Subgroup Frame) (e : oddKernel C ≃* Cubic)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val) :
    ∃ (E : (Fin 4 → Plane) ≃ₗ[ZMod 2] (R → Scalar))
      (rho2 : Representation (ZMod 2) (H C) (R → Scalar))
      (rho4 : Representation Scalar (H C) (R → Scalar)),
      (∀ h v, rho2 h v=E (BinaryPlaneCyclicWreathUniform.representation C
        (h : C) (E.symm v))) ∧
      (∀ h v, rho4 h v=rho2 h v) ∧
      ∀ v, rho2 (cubic C e) v=omega • v := by
  obtain ⟨l,E,hl,ht,hregular,hscalar⟩ :=
    BinaryPlaneAlternatingScalarGauge.exists_scalar_gauge C e heven
  let rho2 : Representation (ZMod 2) (H C) (R → Scalar) :=
    E.conjRingEquiv.toMonoidHom.comp
      ((BinaryPlaneCyclicWreathUniform.representation C).comp (H C).subtype)
  have hk : ∀ v, rho2 (cubic C e) v=omega • v := by
    intro v
    funext r
    change E (BinaryPlaneCyclicWreathUniform.representation C
      (BinaryPlaneRankOneOddGenerator.generator C e : C) (E.symm v)) r=omega*v r
    rw [hscalar,LinearEquiv.apply_symm_apply]
  let rho4 := BinaryCubicScalarLinearRepresentation.representation rho2
    (cubic C e) hk (centralizes_cubic C e)
  exact ⟨E,rho2,rho4,fun _ _ => rfl,fun _ _ => rfl,hk⟩

end SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingScalarCentralizer
