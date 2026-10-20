import SymmetricSubgroupAsymptotics.TernaryDihedralMonomialNonbinaryQuotientSocles
import SymmetricSubgroupAsymptotics.LinearSemidirectActualImageKernelChart
import SymmetricSubgroupAsymptotics.BinaryPlaneWreathActualOddKernelStructure
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools

/-! Actual nonbinary quotients of ANY GL2(2) wreath D8 linear subgroup
with full block image have whole-socle bound two. Literal S3 affine
coordinates construct the ternary kernel chart internally. The binary
quotients are not bounded here and belong to the retained comparator. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneDihedralLinearNonbinarySocles
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathNormalGenerators BinaryPlaneWreathActualOddKernel
open LinearSemidirectSubgroupKernelChart
open DihedralEightRegularKleinBlockModel (R Q action_injective)
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq
abbrev Signs := Sign (R := Q) (I := R)
abbrev ESign := TernaryPermutationWreathEmbedding.signs (R := Q) (I := R)
abbrev LinearAction := TernarySignedPermutationSubgroupSocles.linearAction ESign
abbrev TernaryModel := TernaryPermutationWreathEmbedding.Target (R := Q) (I := R)

def binaryTop (B : Subgroup Signs) : B →* Q :=
  (SemidirectProduct.rightHom : Signs →* Q).comp B.subtype

def scalar (B : Subgroup Signs) (g : B) (i : R) : ZMod 3 :=
  TernarySignedPermutationSubgroupSocles.coefficient ESign (g : Signs) i

theorem scalar_one (B : Subgroup Signs) (i : R) : scalar B 1 i=1 := rfl

theorem scalar_mul (B : Subgroup Signs) (g h : B) (i : R) :
    scalar B (g*h) i=scalar B g i*scalar B h (binaryTop B g⁻¹ • i) :=
  TernarySignedPermutationSubgroupSocles.coefficient_mul ESign (g : Signs) (h : Signs) i

abbrev ambient (B : Subgroup Signs) :=
  TernaryDihedralMonomialNonbinaryQuotientSocles.ambient (binaryTop B) (scalar B)
    (scalar_one B) (scalar_mul B)

/-- Faithfulness is proved from8 probe labels, not by enumerating the
binary sign group or its subgroups. -/
theorem ambient_injective (B : Subgroup Signs) : Function.Injective (ambient B) := by
  have hlabels : Function.Injective (fun z : ZMod 2 × R => fun j : R =>
      BinarySignTernaryLinear.coefficient z.1*((Pi.single j (1 : ZMod 3) : R → ZMod 3) z.2)) := by
    decide +kernel
  intro g h he
  have hp (i : R) :
      ((g : Signs).left.toAdd.1 i,(g : Signs).right⁻¹ • i)=
        ((h : Signs).left.toAdd.1 i,(h : Signs).right⁻¹ • i) := by
    apply hlabels
    funext j
    exact congrArg (fun f : Module.End (ZMod 3) (R → ZMod 3) => f (Pi.single j 1) i) he
  apply Subtype.ext
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    exact congrArg Prod.fst (hp i)
  · apply inv_injective
    apply DihedralEightRegularKleinBlockModel.action_injective
    apply Equiv.ext
    intro i
    exact congrArg Prod.snd (hp i)

variable (C : Subgroup (W (R := Q) (I := R)))

def affineMap : C →* TernaryModel :=
  TernaryPermutationWreathEmbedding.affine.comp ((wreathMap (R := Q) (I := R)).comp C.subtype)

theorem affineMap_injective : Function.Injective (affineMap C) :=
  TernaryPermutationWreathEmbedding.affine_injective.comp
    (wreathMap_injective.comp Subtype.val_injective)

/-- Every actual nonbinary surjective image retains capacity two. This
constructs its kernel module from the actual affine-coordinate image. -/
theorem socle_of_surjective
    (hblocks : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := Q) (I := R) →* Q).comp C.subtype))
    {D : Type} [Group D] (phi : C →* D) (hphi : Function.Surjective phi)
    (hQ : ¬ IsPGroup 2 D) : SocleNormalGeneratorBound D 2 := by
  let f := affineMap C
  let J : Subgroup TernaryModel := f.range
  let e : C ≃* J := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h => affineMap_injective C (congrArg Subtype.val h),f.rangeRestrict_surjective⟩
  let B := Image LinearAction J
  let pi := LinearSemidirectActualImageKernelChart.top LinearAction J
  let A := LinearSemidirectActualImageKernelChart.kernelModule LinearAction J
  let E := LinearSemidirectActualImageKernelChart.originalKernelChart LinearAction J
  have hpi : Function.Surjective pi := (projection LinearAction J).rangeRestrict_surjective
  have htop : Function.Surjective (binaryTop B) := by
    intro r
    obtain ⟨g,hg⟩ := hblocks r
    exact ⟨(projection LinearAction J).rangeRestrict (e g),hg⟩
  have hR : IsPGroup 2 Q := DihedralEightRegularKleinBlockModel.binary
  have hB : IsPGroup 2 B := (sign_isPGroup (I := R) hR).to_subgroup B
  let j : Representation.IntertwiningMap A.ρ (ambient B) :=
    LinearSemidirectActualImageKernelChart.inclusion LinearAction J
  have hj : Function.Injective j := LinearSemidirectActualImageKernelChart.inclusion_injective LinearAction J
  let psi := phi.comp e.symm.toMonoidHom
  have hpsi : Function.Surjective psi := hphi.comp e.symm.surjective
  let eqQ := QuotientGroup.quotientKerEquivOfSurjective psi hpsi
  have hnonbinary : ¬ IsPGroup 2 (J ⧸ psi.ker) := by
    intro hp
    exact hQ (hp.of_surjective eqQ.toMonoidHom eqQ.surjective)
  have hbound := TernaryDihedralMonomialNonbinaryQuotientSocles.quotientSocle
    (binaryTop B) (scalar B) (scalar_one B) (scalar_mul B) hB htop (ambient_injective B)
    pi hpi A E j hj psi.ker hnonbinary
  exact CyclicSocleQuotientTools.socleBound_equiv eqQ hbound

/-- The final quotient is the literal original C/N. -/
theorem quotientSocle
    (hblocks : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := Q) (I := R) →* Q).comp C.subtype))
    (N : Subgroup C) [N.Normal] (hQ : ¬ IsPGroup 2 (C ⧸ N)) :
    SocleNormalGeneratorBound (C ⧸ N) 2 :=
  socle_of_surjective C hblocks (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hQ

end SymmetricSubgroupAsymptotics.BinaryPlaneDihedralLinearNonbinarySocles
