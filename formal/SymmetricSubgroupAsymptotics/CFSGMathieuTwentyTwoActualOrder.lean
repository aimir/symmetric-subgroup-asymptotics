import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu22.Cardinality
import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.GroupTheory.Sylow

/-! The existing pinned Apache-2.0 certificate chain proves the order
and transitivity of the SAME original22-point generated subgroup.
Its order11 elements have no fixed point. No named-model identification,
simplicity, outer budget, or Sylow-generation premise occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoActualOrder

theorem card : Nat.card CFSG.Models.Mathieu22=443520 :=
  CFSG.Certificates.Mathieu22.M22Cardinality.card_M22

theorem orbit_zero_eq_univ :
    MulAction.orbit CFSG.Models.Mathieu22 (0 : Fin 22)=Set.univ :=
  CFSG.Certificates.Mathieu22.M22Certificates.ChainOrbits.orbit_zero_eq_univ

theorem isPretransitive : MulAction.IsPretransitive CFSG.Models.Mathieu22 (Fin 22) :=
  (MulAction.isPretransitive_iff_orbit_eq_univ (G:=CFSG.Models.Mathieu22) (0 : Fin 22)).mpr
    orbit_zero_eq_univ

theorem stabilizer_card (x : Fin 22) :
    Nat.card (MulAction.stabilizer CFSG.Models.Mathieu22 x)=20160 := by
  letI : MulAction.IsPretransitive CFSG.Models.Mathieu22 (Fin 22) := isPretransitive
  have hi : (MulAction.stabilizer CFSG.Models.Mathieu22 x).index=22 := by
    simpa only [Nat.card_fin] using
      MulAction.index_stabilizer_of_transitive CFSG.Models.Mathieu22 x
  have hh := (MulAction.stabilizer CFSG.Models.Mathieu22 x).card_mul_index
  rw [hi,card] at hh
  omega

theorem no_fixed_point_of_order_eleven (g : CFSG.Models.Mathieu22) (hg : orderOf g=11)
    (x : Fin 22) : (g : Equiv.Perm (Fin 22)) x≠x := by
  intro hx
  let H := MulAction.stabilizer CFSG.Models.Mathieu22 x
  let y : H := ⟨g,hx⟩
  have ho : orderOf y=11 := by
    rw [←orderOf_injective H.subtype H.subtype_injective y]
    exact hg
  have hd : 11∣Nat.card H := by rw [←ho]; exact orderOf_dvd_natCard y
  rw [stabilizer_card] at hd
  norm_num at hd

theorem sylow_eleven_card (P : Sylow 11 CFSG.Models.Mathieu22) : Nat.card P=11 := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  rw [P.card_eq_multiplicity,card]
  decide +kernel

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoActualOrder
