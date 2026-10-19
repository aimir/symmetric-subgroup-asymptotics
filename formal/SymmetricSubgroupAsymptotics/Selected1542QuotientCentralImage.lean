import SymmetricSubgroupAsymptotics.Selected1542RetainedQuotient
import SymmetricSubgroupAsymptotics.GeneratedCentralImage
import Mathlib.GroupTheory.Commutator.Basic

/-! L/N is central in the selected SAME quotient Original/N. No statement
that L itself is central in the original transitive group is made. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure

private theorem source_preimage_commutator_mem (j : Fin 3) (i : Fin 64) :
    source j*preimageOriginal i*(source j)⁻¹*(preimageOriginal i)⁻¹∈originalNormal := by
  refine ⟨centralResidue j i,?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact (all_central_mod_N i j x).symm

private theorem source_preimage_commute (j : Fin 3) (l : originalPreimage) :
    QuotientGroup.mk' originalNormal (source j)*QuotientGroup.mk' originalNormal (l : Original)=
      QuotientGroup.mk' originalNormal (l : Original)*QuotientGroup.mk' originalNormal (source j) := by
  obtain ⟨i,rfl⟩ := preimageTable.chart_surjective l
  have hm := source_preimage_commutator_mem j i
  have hq : QuotientGroup.mk' originalNormal
      (source j*preimageOriginal i*(source j)⁻¹*(preimageOriginal i)⁻¹)=1 := by
    change ((source j*preimageOriginal i*(source j)⁻¹*(preimageOriginal i)⁻¹ : Original) : Quotient)=1
    exact (QuotientGroup.eq_one_iff _).mpr hm
  apply commutatorElement_eq_one_iff_mul_comm.mp
  change QuotientGroup.mk' originalNormal (source j)*QuotientGroup.mk' originalNormal (preimageOriginal i)*
    (QuotientGroup.mk' originalNormal (source j))⁻¹*
      (QuotientGroup.mk' originalNormal (preimageOriginal i))⁻¹=1
  simpa only [map_mul,map_inv] using hq

theorem preimage_central_in_quotient (l : originalPreimage) (g : Quotient) :
    QuotientGroup.mk' originalNormal (l : Original)*g=
      g*QuotientGroup.mk' originalNormal (l : Original) :=
  GeneratedCentralImage.central_image source source_generates
    (QuotientGroup.mk' originalNormal) (QuotientGroup.mk'_surjective originalNormal)
    originalPreimage.subtype source_preimage_commute l g

theorem quotientAlternating_kernel_central (z : quotientAlternating.ker) (g : Quotient) :
    (z : Quotient)*g=g*(z : Quotient) := by
  have hz : (z : Quotient)∈originalPreimage.map (QuotientGroup.mk' originalNormal) := by
    rw [←quotientAlternating_kernel]
    exact z.property
  obtain ⟨h,hh,he⟩ := hz
  have hc := preimage_central_in_quotient ⟨h,hh⟩ g
  change QuotientGroup.mk' originalNormal h*g=g*QuotientGroup.mk' originalNormal h at hc
  rw [he] at hc
  exact hc

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
