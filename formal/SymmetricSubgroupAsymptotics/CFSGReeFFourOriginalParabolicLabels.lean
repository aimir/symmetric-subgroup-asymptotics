import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalSignedRootAction

/-! The positive minimal parabolics are fixed label by label under an
original pair-preserving automorphism. The label test uses the actual
opposite root intersections of distinct orders q and q squared. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalParabolicLabels
open CFSGReeFFourOriginalPositiveSylow CFSGReeFFourOriginalOppositeAlignment
open CFSGReeFFourOriginalMinimalParabolics CFSGMinimalOvergroupAutomorphismAction
open CFSGReeFFourOriginalRootAction CFSGReeFFourOriginalSignedRootAction
open CFSGReeFFourOriginalNegativeRootIntersections CFSGReeFFourOriginalRootIntersections

theorem original_simple_parabolic_map_eq (m : ℕ) (hm : 0<m)
    (f : MulAut (CFSG.Models.ReeF4 m))
    (hU : (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)).map f.toMonoidHom=
      (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)))
    (hV : (originalNegative m hm).map f.toMonoidHom=originalNegative m hm) (b : Bool) :
    (originalSimpleParabolic m hm b).map f.toMonoidHom=originalSimpleParabolic m hm b := by
  have hB : (Subgroup.normalizer (reePositiveSylow m hm : Set (CFSG.Models.ReeF4 m))).map
      f.toMonoidHom=Subgroup.normalizer (reePositiveSylow m hm : Set (CFSG.Models.ReeF4 m)) :=
    (Subgroup.map_equiv_normalizer_eq
      (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)) f).trans
      (congrArg (fun P : Subgroup (CFSG.Models.ReeF4 m)=>Subgroup.normalizer
        (P : Set (CFSG.Models.ReeF4 m))) hU)
  obtain ⟨sigma,hsigma⟩ := exists_minimal_overgroup_permutation
    (Subgroup.normalizer (reePositiveSylow m hm : Set (CFSG.Models.ReeF4 m)))
    (originalSimpleParabolic m hm) (original_normalizer_lt_simpleParabolic m hm)
    (original_simpleParabolic_minimal m hm) (minimal_original_overgroup_eq_simpleParabolic m hm)
    (originalSimpleParabolic_injective m hm) f hB
  have hroots : originalNegativeRootBlock m hm b=originalNegativeRootBlock m hm (sigma b) := by
    calc
      originalNegativeRootBlock m hm b=(originalNegativeRootBlock m hm b).map f.toMonoidHom :=
        (original_negative_root_block_map_eq m hm f hU hV b).symm
      _=originalNegativeRootBlock m hm (sigma b) := by
        rw [←original_negative_inf_simpleParabolic,Subgroup.map_inf _ _ _ f.injective,
          hV,hsigma b,original_negative_inf_simpleParabolic]
  have hc := congrArg (fun P : Subgroup (CFSG.Models.ReeF4 m)=>Nat.card P) hroots
  dsimp only at hc
  rw [originalNegativeRootBlock_card,originalNegativeRootBlock_card] at hc
  have hp : Nat.card (originalRootBlock m hm b)=Nat.card (originalRootBlock m hm (sigma b)) := by
    rw [originalRootBlock_card,originalRootBlock_card]
    exact hc
  have he : b=sigma b := originalRootBlock_card_injective m hm hp
  have hh := hsigma b
  rw [←he] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalParabolicLabels
