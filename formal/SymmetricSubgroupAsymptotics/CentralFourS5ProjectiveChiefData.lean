import SymmetricSubgroupAsymptotics.S5SubgroupProjectiveClassification
import SymmetricSubgroupAsymptotics.AlternatingSymmetricChiefCertificateFactories
import SymmetricSubgroupAsymptotics.DegreeTwentyFiveCentralFourBound
import SymmetricSubgroupAsymptotics.FixedTargetCompositionTrace

/-! Actual central-kernel maps to S5 supply both degree25 structural
branches. Only Burnside's ordinary two-prime solvability theorem remains
an input; neither a chief capacity nor a projective subgroup census is
assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CentralFourS5ProjectiveChiefData
open Non2UnipotentPrefixFiniteMenu
open S5SubgroupProjectiveClassification
open AlternatingSymmetricChiefCertificateFactories
variable {G : Type} [Group G] [Finite G]

private def rangeKernelEquiv (f : G →* FiveSymmetric) : f.rangeRestrict.ker ≃* f.ker where
  toFun x := ⟨x.val,congrArg Subtype.val x.property⟩
  invFun x := ⟨x.val,Subtype.ext x.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := rfl

def solubleDatum (f : G →* FiveSymmetric)
    (hcentral : ∀ z ∈ f.ker,∀ x : G,z*x=x*z)
    (chi : f.ker →* Multiplicative (ZMod 4)) (hchi : Function.Injective chi)
    (hG : IsSolvable G) : CentralFourQuotientDatum G := by
  letI : IsSolvable G := hG
  have hI : IsSolvable f.range :=
    solvable_of_surjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  exact {
    P := f.range
    groupP := inferInstance
    finiteP := inferInstance
    projection := f.rangeRestrict
    projection_surjective := f.rangeRestrict_surjective
    central_kernel := fun z hz x => hcentral z ((rangeKernelEquiv f ⟨z,hz⟩).property) x
    kernelCharacter := chi.comp (rangeKernelEquiv f).toMonoidHom
    kernelCharacter_injective := hchi.comp (rangeKernelEquiv f).injective
    projective_order_le := card_le_twentyFour_of_isSolvable f.range hI }

private theorem order_budget_of_dvd (hcard : Nat.card G ∣ 480) :
    ArithmeticFunction.cardFactors (Nat.card G) ≤ 7 := by
  obtain ⟨c,hc⟩ := hcard
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  have hs : ArithmeticFunction.cardFactors 480=
      ArithmeticFunction.cardFactors (Nat.card G)+ArithmeticFunction.cardFactors c := by
    rw [hc,ArithmeticFunction.cardFactors_mul (Nat.card_pos (α := G)).ne' hc0]
  have h7 : ArithmeticFunction.cardFactors 480=7 := by decide +kernel
  omega

private theorem alternating_order_charge :
    ArithmeticFunction.cardFactors (Nat.card FiveAlternating)=4 := by
  rw [nat_card_alternatingGroup,Nat.card_fin]
  decide +kernel

def nonsolubleCertificate (B : PublishedBurnsideTwoPrimeSolvabilityInput)
    (f : G →* FiveSymmetric) (hcentral : ∀ z ∈ f.ker,∀ x : G,z*x=x*z)
    (hcard : Nat.card G ∣ 480) (hG : ¬ IsSolvable G) :
    SmallAffineChiefOrderSavingCertificate G 3 := by
  classical
  apply Classical.choice
  have hex : Nonempty (SmallAffineChiefOrderSavingCertificate G 3) := by
    have hI : ¬ IsSolvable f.range := by
      intro h
      letI : IsSolvable f.range := h
      letI : IsSolvable f.ker := isSolvable_of_comm (fun x y =>
        Subtype.ext (hcentral x x.property y))
      apply hG
      exact solvable_of_ker_le_range f.ker.subtype f.rangeRestrict (by
        rw [Subgroup.range_subtype]
        intro x hx
        exact congrArg Subtype.val hx)
    have hb := order_budget_of_dvd hcard
    have hcharge := alternating_order_charge
    rcases eq_alternating_or_top_of_not_isSolvable B f.range hI with hA | htop
    · let q : G →* FiveAlternating := f.codRestrict FiveAlternating (fun x => by
        rw [← hA]
        exact ⟨x,rfl⟩)
      have hq : Function.Surjective q := by
        rintro ⟨a,ha⟩
        have hr : a ∈ f.range := by rwa [hA]
        obtain ⟨x,hx⟩ := hr
        exact ⟨x,Subtype.ext hx⟩
      exact ⟨alternatingQuotient 5 (by decide) 3 q hq (by
        change ArithmeticFunction.cardFactors (Nat.card G) ≤
          ArithmeticFunction.cardFactors (Nat.card FiveAlternating)+3
        omega)⟩
    · exact ⟨symmetricQuotient 5 (by decide) 3 f (MonoidHom.range_eq_top.mp htop) (by
        change ArithmeticFunction.cardFactors (Nat.card G) ≤
          ArithmeticFunction.cardFactors (Nat.card FiveAlternating)+3
        omega)⟩
  exact hex

theorem nonsolubleTrace (B : PublishedBurnsideTwoPrimeSolvabilityInput)
    (f : G →* FiveSymmetric) (hcentral : ∀ z ∈ f.ker,∀ x : G,z*x=x*z)
    (hcard : Nat.card G ∣ 480) (hG : ¬ IsSolvable G)
    (T : FixedTargetCompositionTrace G) : T.envelope.abelianLength ≤ 3 := by
  rw [T.abelianLength_eq]
  exact (nonsolubleCertificate B f hcentral hcard hG).chief_bound T.chief

end SymmetricSubgroupAsymptotics.CentralFourS5ProjectiveChiefData
