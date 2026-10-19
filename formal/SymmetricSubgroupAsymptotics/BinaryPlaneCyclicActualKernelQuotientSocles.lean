import SymmetricSubgroupAsymptotics.BinaryPlaneCyclicActualKernelBounds
import SymmetricSubgroupAsymptotics.BinaryPlaneCyclicLinearQuotientSocles
import SymmetricSubgroupAsymptotics.SocleNormalSubgroupGeneratorInheritance

/-! Whole-socle capacity two for a nonbinary actual extension inside a
cyclic binary-plane wreath. Every normal denominator is the original N.
The moving and fixed action rows share positions; the fixed-row image uses
genuine normal-subgroup inheritance inside the actual linear socle. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneCyclicActualKernelQuotientSocles
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel OriginalKernelModuleChart

variable {R I G : Type} [Group R] [Finite R] [IsCyclic R] [MulAction R I]
  [Fintype I] [DecidableEq I] [Group G] [Finite G]

 theorem quotientSocle
    (C : Subgroup (W (R := R) (I := I)))
    (pi : G →* C) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 2) C) (E : OriginalKernelModuleChart pi A)
    [FiniteDimensional (ZMod 2) A]
    (j : Representation.IntertwiningMap A.ρ (BinaryPlaneCyclicWreathUniform.representation C))
    (hj : Function.Injective j)
    (hsurj : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := R) (I := I) →* R).comp C.subtype))
    (c : R) (i₀ : I) (hcycle : ∀ i : I, ∃ n : ℕ, c^n • i₀=i)
    (hR : IsPGroup 2 R) (hG : ¬ IsPGroup 2 G)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) 2 := by
  let O := oddKernel C
  letI : IsMulCommutative O := commutative C
  letI : NeZero (Nat.card O : ZMod 2) := ⟨card_cast_ne_zero C⟩
  have hC := BinaryPlaneCyclicActualKernelBounds.linear_nonbinary
    (C := C) (pi := pi) (A := A) (E := E) hG
  have hA := BinaryPlaneCyclicActualKernelBounds.uniform
    (C := C) (A := A) (j := j) (hj := hj) (hsurj := hsurj)
    (c := c) (i₀ := i₀) (hcycle := hcycle)
  have hfixed := BinaryPlaneCyclicActualKernelBounds.kernel_fixedFree
    (C := C) (A := A) (j := j) (hj := hj) (hsurj := hsurj)
    (c := c) (i₀ := i₀) (hcycle := hcycle) hR hC
  let D := retainedOddSeparator pi N O
  let F := trivialActionSoclePart (G ⧸ N) D
  let f := base pi N
  have hf : Function.Surjective f := base_surjective pi N
  have htopSurj : Function.Surjective (sectionTop pi N hpi) := by
    intro b
    obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (pi.ker ⊔ N) b
    exact ⟨pi g,(sectionTop_apply pi N hpi g).trans hg⟩
  have hcop : Nat.Coprime 3 (Nat.card R) := by
    obtain ⟨n,hn⟩ := hR.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hlinear : SocleNormalGeneratorBound (G ⧸ (pi.ker ⊔ N)) 2 :=
    BinaryPlaneCyclicLinearQuotientSocles.socle_of_surjective C hsurj c i₀ hcycle
      hcop (sectionTop pi N hpi) htopSurj
  letI : (F.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hFImage : F.map f≤finiteGroupSocle (G ⧸ (pi.ker ⊔ N)) :=
    (Subgroup.map_mono (minimalNormalSoclePart_le_finiteGroupSocle _ _)).trans
      (SocleActionPartQuotientKernel.socle_map_le f hf)
  have hFImageBound : MarkedC4.normalGen (F.map f)≤2 :=
    (MarkedC4.normalGen_le_socle_of_normal_le (F.map f) hFImage).trans
      ((socleNormalGeneratorBound_iff_normalGen_le _ _).mp hlinear)
  have hF : MarkedC4.normalGen F≤2 :=
    (E.fixedSocleRow_normalGen_le_image pi A N hpi O hfixed).trans hFImageBound
  have hM : MarkedC4.normalGen
      (nontrivialActionSoclePart (G ⧸ N) D)≤2 :=
    E.movingSocleRow_normalGen_le_two pi A N hpi O hA
  apply (socleNormalGeneratorBound_iff_normalGen_le _ _).mpr
  exact (normalGen_finiteGroupSocle_le_max_actionSocleParts (G ⧸ N) D).trans
    (max_le hM hF)

end SymmetricSubgroupAsymptotics.BinaryPlaneCyclicActualKernelQuotientSocles
