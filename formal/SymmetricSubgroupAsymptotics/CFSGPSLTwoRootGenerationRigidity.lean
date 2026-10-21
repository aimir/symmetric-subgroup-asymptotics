import SymmetricSubgroupAsymptotics.CFSGPSLTwoRootCoordinates

/-! Fixing the original projective upper root group pointwise and the
original Weyl element fixes every original PSL2 element. The proof lifts
the equalizer to SL2 and uses the checked elementary generation theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoRootCoordinates
open Matrix CFSGTypeASLTwoWeyl CFSGTypeAElementaryMatrices
variable {F : Type*} [Field F]

theorem automorphism_eq_one_of_root_and_weyl (f : MulAut (PSL (F:=F)))
    (hfix : ∀ u : projectiveRoot (F:=F),f u.val=u.val)
    (hW : f projectiveWeyl=projectiveWeyl) : f=1 := by
  let α := f.toMonoidHom.comp (projection (F:=F))
  let β := projection (F:=F)
  let K := α.eqLocus β
  have hu (a : F) : upper a∈K := hfix ⟨projectiveUpper a,projectiveUpper_mem a⟩
  have hw : weyl (F:=F)∈K := hW
  have hl (a : F) : lower a∈K := by
    have he : weyl*upper (-a)*weyl⁻¹=lower a := by rw [weyl_upper,neg_neg]
    rw [←he]
    exact K.mul_mem (K.mul_mem hw (hu (-a))) (K.inv_mem hw)
  have htop : K=⊤ := by
    apply CFSGTypeAElementaryGeneration.eq_top_of_elementary
    intro i j hij a
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hu a
    · exact hl a
    · exact (hij rfl).elim
  apply MulEquiv.ext
  intro g
  obtain ⟨x,rfl⟩ := projection_surjective g
  have hx : x∈K := by rw [htop];trivial
  exact hx

end SymmetricSubgroupAsymptotics.CFSGPSLTwoRootCoordinates
