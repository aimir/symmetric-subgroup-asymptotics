import SymmetricSubgroupAsymptotics.CFSGReeFFourSignedBlockGeneration
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalSignedRootAction

/-! Signed-simple-block generation and pointwise faithfulness in the
SAME original Ree quotient. A subgroup is pulled back through the proved
surjection; no automorphism is pulled back. The result applies to actual
homomorphisms and hence to original quotient automorphisms. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalSignedBlockGeneration
open CFSGReeFFourPerfectProjection CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourOriginalSignedRootAction CFSGReeFFourOriginalRootIntersections
open CFSGReeFFourOriginalNegativeRootIntersections CFSGReeFFourOriginalMinimalParabolics
open CFSGReeFFourOriginalOppositeAlignment CFSGReeFFourSignedBlockGeneration
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourOppositionFixedPositiveNegative
open CFSGReeFFourMinimalParabolics CFSGOpposedSubgroupPeeling

theorem original_subgroup_eq_top_of_signed_root_blocks (m : ℕ) (hm : 0<m)
    (S : Subgroup (CFSG.Models.ReeF4 m))
    (h : ∀neg b : Bool,originalSignedRootBlock m hm neg b≤S) : S=⊤ := by
  have hs : S.comap (fixedToOriginal m hm)=⊤ := by
    apply subgroup_eq_top_of_signed_blocks m (S.comap (fixedToOriginal m hm))
    · intro b x hx
      exact h false b ⟨x,hx,rfl⟩
    · intro b x hx
      have hv : fixedToOriginal m hm x∈originalNegative m hm := ⟨x,hx.1,rfl⟩
      have hp : fixedToOriginal m hm x∈originalSimpleParabolic m hm b := ⟨x,hx.2,rfl⟩
      have hb : fixedToOriginal m hm x∈originalNegativeRootBlock m hm b := by
        rw [←original_negative_inf_simpleParabolic]
        exact ⟨hv,hp⟩
      exact h true b hb
  apply eq_top_iff.mpr
  intro g _
  obtain ⟨x,rfl⟩ := fixedToOriginal_surjective m hm g
  have hx : x∈S.comap (fixedToOriginal m hm) := by rw [hs];trivial
  exact hx

theorem original_hom_ext_of_signed_root_blocks {Q : Type*} [Group Q] (m : ℕ) (hm : 0<m)
    (f g : CFSG.Models.ReeF4 m→*Q)
    (h : ∀neg b : Bool,∀x∈originalSignedRootBlock m hm neg b,f x=g x) : f=g := by
  have hs : f.eqLocus g=⊤ :=
    original_subgroup_eq_top_of_signed_root_blocks m hm (f.eqLocus g) h
  apply MonoidHom.ext
  intro x
  have hx : x∈f.eqLocus g := by rw [hs];trivial
  exact hx

theorem original_aut_ext_of_signed_root_blocks (m : ℕ) (hm : 0<m)
    (f g : MulAut (CFSG.Models.ReeF4 m))
    (h : ∀neg b : Bool,∀x∈originalSignedRootBlock m hm neg b,f x=g x) : f=g := by
  have he := original_hom_ext_of_signed_root_blocks m hm f.toMonoidHom g.toMonoidHom h
  apply MulEquiv.ext
  intro x
  exact DFunLike.congr_fun he x

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalSignedBlockGeneration
