import SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedRankOneGeometry
import SymmetricSubgroupAsymptotics.CFSGRankOneTwoCellCardinality
import Mathlib.GroupTheory.Sylow

/-! The exact order and actual Sylow subgroup of the original Ree fixed
group, derived from the two-cell bijection. The exceptional order formula
is an output, and the full original derived/central quotient remains a
separate transport step. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedCardinalitySylow
open CFSGReeGTwoFieldParameters CFSGReeGTwoFixedModelEquivalence
open CFSGReeGTwoOriginalPositiveSubgroup CFSGReeGTwoOriginalBorel
open CFSGReeGTwoOriginalOpposition CFSGReeGTwoFixedFactorDescent
open CFSGReeGTwoFixedRankOneGeometry CFSGGTwoOriginalBruhatUniqueness

theorem fixedModel_finite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fun g : originalModelFixed m=>nativeHom (Field m) g.val)
    ((nativeHom_injective (Field m)).comp Subtype.val_injective)

attribute [local instance] fixedModel_finite

theorem fixed_group_card (m : ℕ) :
    Nat.card (originalModelFixed m)=
      (3^(2*m+1))^3*(3^(2*m+1)-1)*((3^(2*m+1))^3+1) := by
  have hc := CFSGRankOneTwoCellCardinality.card_eq
    (borelGroup m) (fixedPositiveGroup m) (fixedOpposition m)
    (positive_le_fixed_borel m) (fixedOpposition_not_mem_borel m)
    (fixed_borel_inf_opposite m) (by
      intro g
      rcases fixed_bruhat m g with hg|⟨b,hb,u,hu,he⟩
      · exact Or.inl hg
      · exact Or.inr ⟨⟨b,hb⟩,⟨u,hu⟩,he⟩)
  rw [borelGroup_card,fixedPositiveGroup_card] at hc
  simpa only [Nat.add_comm] using hc

theorem fixed_positive_index (m : ℕ) :
    (fixedPositiveGroup m).index=(3^(2*m+1)-1)*((3^(2*m+1))^3+1) := by
  have hq : 0<(3^(2*m+1))^3 := pow_pos (pow_pos (by decide : 0<3) _) _
  apply Nat.eq_of_mul_eq_mul_left hq
  calc
    (3^(2*m+1))^3*(fixedPositiveGroup m).index=
        Nat.card (originalModelFixed m) := by
      simpa only [fixedPositiveGroup_card] using (fixedPositiveGroup m).card_mul_index
    _=(3^(2*m+1))^3*((3^(2*m+1)-1)*((3^(2*m+1))^3+1)) := by
      rw [fixed_group_card,Nat.mul_assoc]

theorem fixed_positive_not_dvd_index (m : ℕ) : ¬3∣(fixedPositiveGroup m).index := by
  rw [fixed_positive_index]
  let q := 3^(2*m+1)
  change ¬3∣(q-1)*(q^3+1)
  have hqpos : 0<q := pow_pos (by decide : 0<3) _
  have hqdvd : 3∣q := dvd_pow_self 3 (by omega : 2*m+1≠0)
  have hq : q%3=0 := Nat.mod_eq_zero_of_dvd hqdvd
  have hsub : (q-1)%3=2 := by omega
  have hcube : q^3%3=0 := by simp [Nat.pow_mod,hq]
  have hmod : ((q-1)*(q^3+1))%3=2 := by
    rw [Nat.mul_mod,Nat.add_mod,hsub,hcube]
  intro hd
  have hz := Nat.mod_eq_zero_of_dvd hd
  omega

def fixedPositiveSylow (m : ℕ) : Sylow 3 (originalModelFixed m) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact (fixedPositiveGroup_isPGroup m).toSylow (fixed_positive_not_dvd_index m)

theorem fixedPositiveSylow_coe (m : ℕ) :
    (fixedPositiveSylow m:Subgroup (originalModelFixed m))=fixedPositiveGroup m := rfl

theorem fixedPositiveSylow_normalizer_soluble (m : ℕ) :
    IsSolvable (Subgroup.normalizer (fixedPositiveSylow m:Set (originalModelFixed m))) := by
  change IsSolvable (Subgroup.normalizer (fixedPositiveGroup m:Set (originalModelFixed m)))
  exact fixed_positive_normalizer_soluble m

end SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedCardinalitySylow
