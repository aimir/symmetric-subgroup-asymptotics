import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckProjectiveOrder
import SymmetricSubgroupAsymptotics.CFSGSimpleProjectiveDescent
import SymmetricSubgroupAsymptotics.CFSGPGeneratedCentralKernel

/-! The literal original simple G2 model is the central quotient of
its SAME cubic integral action image. The resulting surjection from
J(K,id) has central kernel by actual p-subgroup generation and one
injective Sylow restriction, without a perfectness premise or an
original-automorphism lift. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalProjection
open CFSGGTwoD4GeckImageRealization CFSGGTwoD4GeckGeneratedGroup
open CFSGGTwoD4GeckImageSylows CFSGGTwoD4GeckProjectiveOrder
open CFSGTrialityGeckGeneratedSylow CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckRootGeneratedPGroup CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K]
local notation "J" => fixedRootGenerated K (RingEquiv.refl K)

local instance imageFinite : Finite (imageGroup K) :=
  Finite.of_surjective (generatedToImage K) (generatedToImage_surjective K)

def sourceToImage : Model CartanMatrix.G₂ K→*imageGroup K :=
  (sourceImageRepresentation K).codRestrict (imageGroup K) (fun x=>by
    change sourceImageRepresentation K x∈(generatedImageAction K).range
    rw [←generated_action_ranges_eq K]
    exact ⟨x,rfl⟩)

theorem sourceToImage_surjective : Function.Surjective (sourceToImage K) := by
  intro y
  have hy : y.val∈(sourceImageRepresentation K).range :=
    (generated_action_ranges_eq K).symm ▸ y.property
  obtain ⟨x,hx⟩ := hy
  exact ⟨x,Subtype.ext hx⟩

def originalProjectiveImageEquiv [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    Projective CartanMatrix.G₂ K≃*(imageGroup K⧸Subgroup.center (imageGroup K)) := by
  letI : Nontrivial (imageGroup K⧸Subgroup.center (imageGroup K)) := imageProjective_nontrivial K
  exact CFSGSimpleProjectiveDescent.projectiveEquivOfSimple
    (sourceToImage K) (sourceToImage_surjective K)

def imageToOriginal [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    imageGroup K→*Projective CartanMatrix.G₂ K :=
  (originalProjectiveImageEquiv K).symm.toMonoidHom.comp
    (QuotientGroup.mk' (Subgroup.center (imageGroup K)))

theorem imageToOriginal_surjective [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    Function.Surjective (imageToOriginal K) :=
  (originalProjectiveImageEquiv K).symm.surjective.comp (QuotientGroup.mk'_surjective _)

theorem imageToOriginal_kernel [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    (imageToOriginal K).ker=Subgroup.center (imageGroup K) :=
  (MonoidHom.ker_mulEquiv_comp (QuotientGroup.mk' (Subgroup.center (imageGroup K)))
    (originalProjectiveImageEquiv K).symm).trans (QuotientGroup.ker_mk' _)

def generatedToOriginal [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    J→*Projective CartanMatrix.G₂ K := (imageToOriginal K).comp (generatedToImage K)

theorem generatedToOriginal_surjective [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    Function.Surjective (generatedToOriginal K) :=
  (imageToOriginal_surjective K).comp (generatedToImage_surjective K)

theorem imageToOriginal_positive_injective (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    Function.Injective ((imageToOriginal K).comp (imagePositiveSylow K p : Subgroup (imageGroup K)).subtype) := by
  intro x y he
  apply CFSGDisjointSylowProjectiveCardinality.central_quotient_injective
    (imagePositiveSylow K p) (imageNegativeSylow K p) (imageSylows_inf K p)
  exact (originalProjectiveImageEquiv K).symm.injective he

theorem generatedToOriginal_injOn_positive [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    Set.InjOn (generatedToOriginal K) (rootPart K (RingEquiv.refl K) false : Set J) := by
  letI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  intro x hx y hy he
  have hpos (z : J) (hz : z∈rootPart K (RingEquiv.refl K) false) :
      generatedToImage K z∈(imagePositiveSylow K (ringChar K) : Subgroup (imageGroup K)) := by
    rw [imagePositiveSylow_coe]
    exact ⟨z,hz,rfl⟩
  let u : imagePositiveSylow K (ringChar K) := ⟨generatedToImage K x,hpos x hx⟩
  let v : imagePositiveSylow K (ringChar K) := ⟨generatedToImage K y,hpos y hy⟩
  have huv : u=v := imageToOriginal_positive_injective K (ringChar K) he
  exact generatedToImage_injOn_positive K hx hy (congrArg (fun z : imagePositiveSylow K (ringChar K)=>z.val) huv)

theorem generatedToOriginal_kernel_le_center [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    (generatedToOriginal K).ker≤Subgroup.center J := by
  letI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  let P := positiveSylow K (RingEquiv.refl K) (ringChar K)
  have hP : Function.Injective ((generatedToOriginal K).comp (P : Subgroup J).subtype) := by
    intro x y he
    apply Subtype.ext
    have hx : x.val∈rootPart K (RingEquiv.refl K) false := by
      rw [←positiveSylow_coe K (RingEquiv.refl K) (ringChar K)]
      exact x.property
    have hy : y.val∈rootPart K (RingEquiv.refl K) false := by
      rw [←positiveSylow_coe K (RingEquiv.refl K) (ringChar K)]
      exact y.property
    exact generatedToOriginal_injOn_positive K hx hy he
  have hpi : (generatedToOriginal K).ker≤
      (Subgroup.center (imageGroup K)).comap (generatedToImage K) := by
    intro x hx
    change generatedToImage K x∈Subgroup.center (imageGroup K)
    rw [←imageToOriginal_kernel K]
    exact hx
  exact CFSGPGeneratedCentralKernel.kernel_le_center_of_injective_sylow
    (generatedToImage K) (generatedToImage_kernel_le_center K) (generatedToOriginal K) hpi P hP
    (rootPart K (RingEquiv.refl K) false) (rootPart K (RingEquiv.refl K) true)
    (rootPart_isPGroup K (RingEquiv.refl K) (ringChar K) false)
    (rootPart_isPGroup K (RingEquiv.refl K) (ringChar K) true)
    (rootPart_sup K (RingEquiv.refl K))

def originalPositiveSylow (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective CartanMatrix.G₂ K)] : Sylow p (Projective CartanMatrix.G₂ K) :=
  (positiveSylow K (RingEquiv.refl K) p).mapSurjective
    (f:=generatedToOriginal K) (generatedToOriginal_surjective K)

theorem originalPositiveSylow_coe (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K))=
      (rootPart K (RingEquiv.refl K) false).map (generatedToOriginal K) := by
  simp only [originalPositiveSylow,Sylow.coe_mapSurjective,positiveSylow_coe]

theorem original_order_lower [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    Nat.card K^12≤Nat.card (Projective CartanMatrix.G₂ K) := by
  letI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  rw [Nat.card_congr (originalProjectiveImageEquiv K).toEquiv]
  exact image_projective_order_lower K (ringChar K)

theorem original_finite [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    Finite (Projective CartanMatrix.G₂ K) :=
  Finite.of_surjective (generatedToOriginal K) (generatedToOriginal_surjective K)

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalProjection
