import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalRootAction
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeRootIntersections

/-! Every original quotient automorphism admits an inner adjustment
fixing BOTH signed q/q² root families label by label. Both signs are
recovered from actual minimal-overgroup intersections and their distinct
orders, without an automorphism lift or a rank-one presentation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalSignedRootAction
open CFSGReeFFourOriginalPositiveSylow CFSGReeFFourOriginalOppositeAlignment
open CFSGReeFFourOriginalPairAlignment CFSGReeFFourOriginalMinimalParabolics
open CFSGReeFFourOriginalRootIntersections CFSGReeFFourOriginalNegativeRootIntersections
open CFSGReeFFourOriginalRootAction CFSGMinimalOvergroupAutomorphismAction

theorem original_negative_root_block_map_eq (m : ℕ) (hm : 0<m)
    (f : MulAut (CFSG.Models.ReeF4 m))
    (hU : (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)).map f.toMonoidHom=
      (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)))
    (hV : (originalNegative m hm).map f.toMonoidHom=originalNegative m hm) (b : Bool) :
    (originalNegativeRootBlock m hm b).map f.toMonoidHom=originalNegativeRootBlock m hm b := by
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
  have hroots (c : Bool) : (originalNegativeRootBlock m hm c).map f.toMonoidHom=
      originalNegativeRootBlock m hm (sigma c) := by
    rw [←original_negative_inf_simpleParabolic,Subgroup.map_inf _ _ _ f.injective,
      hV,hsigma c,original_negative_inf_simpleParabolic]
  have hc := Nat.card_congr (f.subgroupMap (originalNegativeRootBlock m hm b)).toEquiv
  change Nat.card (originalNegativeRootBlock m hm b)=
    Nat.card ((originalNegativeRootBlock m hm b).map f.toMonoidHom) at hc
  have hcards := hc.trans
    (congrArg (fun P : Subgroup (CFSG.Models.ReeF4 m)=>Nat.card P) (hroots b))
  dsimp only at hcards
  rw [originalNegativeRootBlock_card,originalNegativeRootBlock_card] at hcards
  have hp : Nat.card (originalRootBlock m hm b)=Nat.card (originalRootBlock m hm (sigma b)) := by
    rw [originalRootBlock_card,originalRootBlock_card]
    exact hcards
  have he : b=sigma b := originalRootBlock_card_injective m hm hp
  have hh := hroots b
  rw [←he] at hh
  exact hh

def originalSignedRootBlock (m : ℕ) (hm : 0<m) (neg b : Bool) : Subgroup (CFSG.Models.ReeF4 m) :=
  if neg then originalNegativeRootBlock m hm b else originalRootBlock m hm b

theorem original_signed_root_block_map_eq (m : ℕ) (hm : 0<m)
    (f : MulAut (CFSG.Models.ReeF4 m))
    (hU : (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)).map f.toMonoidHom=
      (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)))
    (hV : (originalNegative m hm).map f.toMonoidHom=originalNegative m hm) (neg b : Bool) :
    (originalSignedRootBlock m hm neg b).map f.toMonoidHom=originalSignedRootBlock m hm neg b := by
  cases neg
  · exact original_root_block_map_eq m hm f hU hV b
  · exact original_negative_root_block_map_eq m hm f hU hV b

theorem exists_inner_fix_pair_and_signed_root_blocks (m : ℕ) (hm : 0<m)
    (f : MulAut (CFSG.Models.ReeF4 m)) :
    ∃g : CFSG.Models.ReeF4 m,
      (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)).map (MulAut.conj g*f).toMonoidHom=
        (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)) ∧
      (originalNegative m hm).map (MulAut.conj g*f).toMonoidHom=originalNegative m hm ∧
      ∀neg b : Bool,(originalSignedRootBlock m hm neg b).map (MulAut.conj g*f).toMonoidHom=
        originalSignedRootBlock m hm neg b := by
  obtain ⟨g,hU,hV⟩ := original_exists_inner_fix_pair m hm f
  exact ⟨g,hU,hV,original_signed_root_block_map_eq m hm (MulAut.conj g*f) hU hV⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalSignedRootAction
