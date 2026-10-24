import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPairRestriction
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalBorelNormalizers
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedDiagonalTorus
import SymmetricSubgroupAsymptotics.CFSGKernelControlledIntersection

/-! The genuine diagonal image in the original Ree quotient is intrinsic
to its opposed Sylow pair. A pair-preserving automorphism preserves this
image; its elements are actual projected fixed-torus words. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPairDiagonal
open CFSGReeFFourOriginalPairRestriction CFSGReeFFourOriginalBorelNormalizers
open CFSGReeFFourOriginalPositiveSylow CFSGReeFFourOriginalOppositeAlignment
open CFSGReeFFourPerfectProjection CFSGReeFFourFixedBruhatCover
open CFSGReeFFourBorelIntersection CFSGReeFFourFixedDiagonalTorus
open CFSGReeFFourFixedTorus CFSGReeFFourFieldParameters CFSGKernelControlledIntersection

def originalDiagonal (m : ℕ) (hm : 0<m) : Subgroup (CFSG.Models.ReeF4 m) :=
  Subgroup.normalizer (reePositiveSylow m hm : Set (CFSG.Models.ReeF4 m)) ⊓
    Subgroup.normalizer (originalNegative m hm : Set (CFSG.Models.ReeF4 m))

theorem fixedDiagonal_map_originalDiagonal (m : ℕ) (hm : 0<m) :
    (fixedDiagonal m).map (fixedToOriginal m hm)=originalDiagonal m hm := by
  rw [fixedDiagonal_eq_borel_inf_opposite,
    map_inf_eq_of_kernel_le_right (fixedToOriginal m hm) _ _
      (fixedToOriginal_kernel_le_oppositeBorel m hm),
    borel_map_original_normalizer,oppositeBorel_map_original_normalizer]
  rfl

theorem originalDiagonal_map_pair (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm) :
    (originalDiagonal m hm).map f.val.toMonoidHom=originalDiagonal m hm := by
  have hP := (Subgroup.map_equiv_normalizer_eq
    (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)) f.val).trans
    (congrArg (fun H : Subgroup (CFSG.Models.ReeF4 m)=>Subgroup.normalizer (H : Set (CFSG.Models.ReeF4 m)))
      (pair_preserves_positive m hm f))
  have hN := (Subgroup.map_equiv_normalizer_eq (originalNegative m hm) f.val).trans
    (congrArg (fun H : Subgroup (CFSG.Models.ReeF4 m)=>Subgroup.normalizer (H : Set (CFSG.Models.ReeF4 m)))
      (pair_preserves_negative m hm f))
  exact (Subgroup.map_inf _ _ f.val.toMonoidHom f.val.injective).trans
    (congrArg₂ (· ⊓ ·) hP hN)

theorem exists_originalDiagonal_torus (m : ℕ) (hm : 0<m)
    (d : CFSG.Models.ReeF4 m) (hd : d∈originalDiagonal m hm) :
    ∃ a b : (Field m)ˣ,d=fixedToOriginal m hm (fixedTorus m a b) := by
  rw [←fixedDiagonal_map_originalDiagonal m hm] at hd
  obtain ⟨g,hg,rfl⟩ := hd
  obtain ⟨a,b,rfl⟩ := exists_fixedDiagonal_torus m g hg
  exact ⟨a,b,rfl⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPairDiagonal
