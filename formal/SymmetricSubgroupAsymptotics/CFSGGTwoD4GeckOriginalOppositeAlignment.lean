import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckGeneratedOppositeAlignment
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckImageSylows
import SymmetricSubgroupAsymptotics.CFSGQuotientOppositeAlignment

/-! Genuine positive-conjugator alignment descends to the same
original G2 model through its actual central cover. Both original
signed subgroups are proved disjoint Sylows. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalOppositeAlignment
open CFSGGTwoD4GeckGeneratedOppositeAlignment CFSGGTwoD4GeckOriginalProjection
open CFSGGTwoD4GeckOriginalSimpleParameters CFSGGTwoD4GeckImageSylows
open CFSGTrialityGeckGeneratedSylow CFSGTrialityGeckRootGeneratedPGroup
open CFSGTrialityGeckRelativeRootGenerated CFSGQuotientOppositeAlignment CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K] [IsSimpleGroup (Projective CartanMatrix.G₂ K)]

def originalNegative : Subgroup (Projective CartanMatrix.G₂ K) :=
  (rootPart K (RingEquiv.refl K) true).map (generatedToOriginal K)

def originalOppositeSylow (p : ℕ) [Fact p.Prime] [CharP K p] :
    Sylow p (Projective CartanMatrix.G₂ K) :=
  (negativeSylow K p).mapSurjective (f := generatedToOriginal K) (generatedToOriginal_surjective K)

theorem originalOppositeSylow_coe (p : ℕ) [Fact p.Prime] [CharP K p] :
    (originalOppositeSylow K p : Subgroup (Projective CartanMatrix.G₂ K)) = originalNegative K := by
  simp only [originalOppositeSylow, Sylow.coe_mapSurjective, negativeSylow_coe, originalNegative]

theorem original_opposite_sylows_disjoint (p : ℕ) [Fact p.Prime] [CharP K p] :
    (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)) ⊓
      (originalOppositeSylow K p : Subgroup (Projective CartanMatrix.G₂ K)) = ⊥ := by
  have hpinj : Function.Injective ((generatedToOriginal K).comp
      (positiveSylow K (RingEquiv.refl K) p : Subgroup
        (fixedRootGenerated K (RingEquiv.refl K))).subtype) := by
    intro x y he
    apply Subtype.ext
    apply generatedToOriginal_injOn_positive K
    · rw [←positiveSylow_coe K (RingEquiv.refl K) p]
      exact x.property
    · rw [←positiveSylow_coe K (RingEquiv.refl K) p]
      exact y.property
    · exact he
  rw [originalPositiveSylow_coe, originalOppositeSylow_coe]
  exact CFSGCentralKernelPElements.disjoint_map (generatedToOriginal K)
    (positiveSylow K (RingEquiv.refl K) p) hpinj (generatedToOriginal_kernel_le_center K)
    (rootPart K (RingEquiv.refl K) false) (rootPart K (RingEquiv.refl K) true)
    (rootPart_isPGroup K (RingEquiv.refl K) p false)
    (rootPart_isPGroup K (RingEquiv.refl K) p true) (rootParts_inf_eq_bot K)

theorem original_opposite_conjugate_by_positive (p : ℕ) [Fact p.Prime] [CharP K p]
    (g : Projective CartanMatrix.G₂ K)
    (hdisj : (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)) ⊓
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)).map
        (MulAut.conj g).toMonoidHom = ⊥) :
    ∃ b ∈ (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)),
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)).map
        (MulAut.conj g).toMonoidHom = (originalNegative K).map (MulAut.conj b).toMonoidHom := by
  have h := opposite_alignment_map (generatedToOriginal K) (generatedToOriginal_surjective K)
    (rootPart K (RingEquiv.refl K) false) (rootPart K (RingEquiv.refl K) true)
    (rootPart K (RingEquiv.refl K) false) (original_injective_on_rootPart K false)
    (generated_opposite_conjugate_by_positive K) g
  rw [←originalPositiveSylow_coe K p] at h
  exact h hdisj

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalOppositeAlignment
