import SymmetricSubgroupAsymptotics.CFSGReeGTwoDerivedPairNormalizer
import SymmetricSubgroupAsymptotics.CFSGInvolutionOrder

/-! The already constructed DERIVED opposition is square-one and outside
its actual Sylow normalizer. Every central element normalizes that Sylow,
so opposition survives the FULL derived-centre quotient defining the
original ReeG2 model. No ambient-model recognition, known order,
simple/finite premise or assumption that fixed opposition lies in the
derived subgroup is used. The existing torus translate is retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoSelectedDerivedInvolution
open CFSGReeGTwoFixedModelEquivalence CFSGReeGTwoDerivedBruhat
open CFSGReeGTwoDerivedPairNormalizer

abbrev Derived (m : ℕ) := commutator (originalModelFixed m)

def quotientHom (m : ℕ) : Derived m →* CFSG.Models.ReeG2 m :=
  (originalReeEquiv m).symm.toMonoidHom.comp
    (QuotientGroup.mk' (Subgroup.center (Derived m)))

theorem derivedOpposition_not_mem_center (m : ℕ) (hm : 1≤m) :
    derivedOpposition m hm ∉ Subgroup.center (Derived m) := by
  intro hc
  apply derivedOpposition_not_mem_borel m hm
  rw [derived_borel_normalizer m hm]
  exact Subgroup.center_le_normalizer (derivedPositiveSylow m hm : Set (Derived m)) hc

def selectedInvolution (m : ℕ) (hm : 1≤m) : CFSG.Models.ReeG2 m :=
  quotientHom m (derivedOpposition m hm)

theorem selected_square (m : ℕ) (hm : 1≤m) : selectedInvolution m hm ^ 2 = 1 := by
  have hs : (derivedOpposition m hm)^2=1 := by
    simpa only [pow_two] using derivedOpposition_square m hm
  exact (map_pow (quotientHom m) (derivedOpposition m hm) 2).symm.trans
    ((congrArg (quotientHom m) hs).trans (map_one (quotientHom m)))

private theorem quotient_image_ne_one {G H : Type*} [Group G] [Group H]
    (e : G ⧸ Subgroup.center G ≃* H) (x : G)
    (hx : x ∉ Subgroup.center G) :
    e (QuotientGroup.mk' (Subgroup.center G) x) ≠ 1 := by
  intro he
  apply hx
  apply (QuotientGroup.eq_one_iff _).mp
  apply e.injective
  exact he.trans (map_one e).symm

theorem selected_ne_one (m : ℕ) (hm : 1≤m) : selectedInvolution m hm ≠ 1 :=
  quotient_image_ne_one (originalReeEquiv m).symm (derivedOpposition m hm)
    (derivedOpposition_not_mem_center m hm)

theorem reeG2_even_card (m : ℕ) (hm : 1≤m) : Even (Nat.card (CFSG.Models.ReeG2 m)) := by
  by_contra he
  have hodd : Odd (Nat.card (CFSG.Models.ReeG2 m)) := Nat.not_even_iff_odd.mp he
  exact selected_ne_one m hm
    (CFSGReduction.eq_one_of_square_eq_one_of_odd_card hodd
      (selectedInvolution m hm) (selected_square m hm))

end SymmetricSubgroupAsymptotics.CFSGReeGTwoSelectedDerivedInvolution
