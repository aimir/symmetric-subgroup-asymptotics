import SymmetricSubgroupAsymptotics.StandardThreeLinearNoncommutative
import SymmetricSubgroupAsymptotics.SmallAffineChiefCertificateNonsolvable

/-! Corrected chief-order certificates for the standard complements of
small affine rows(8,3),(27,10),(27,11). The determinant kernel is an actual
simple normal subgroup, without any uniqueness requirement. -/
set_option autoImplicit false
noncomputable section
open scoped IsMulCommutative
namespace SymmetricSubgroupAsymptotics.StandardThreeDimensionalLinearGroups
open Non2UnipotentPrefixFiniteMenu

local instance standardChiefPrimeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance standardChiefPrimeThree : Fact (Nat.Prime 3) := ⟨by decide⟩

private theorem noncommutative_top {G : Type} [Group G]
    (h : ¬ IsMulCommutative G) : ¬ IsMulCommutative (⊤ : Subgroup G) := by
  intro ht
  letI : IsMulCommutative (⊤ : Subgroup G) := ht
  apply h
  refine ⟨⟨?_⟩⟩
  intro x y
  exact congrArg Subtype.val
    (mul_comm (⟨x, trivial⟩ : (⊤ : Subgroup G)) ⟨y, trivial⟩)

private def simpleTopCertificate (G : Type) [Group G] [Finite G]
    [IsSimpleGroup G] (hnc : ¬ IsMulCommutative G) :
    SmallAffineChiefOrderSavingCertificate G 0 := by
  letI : IsSimpleGroup (⊤ : Subgroup G) :=
    (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).isSimpleGroup
  apply SmallAffineChiefOrderSavingCertificate.simpleNormal
  refine {
    core := ⊤
    noncommutative := noncommutative_top hnc
    order_budget := ?_ }
  have hc : Nat.card (⊤ : Subgroup G) = Nat.card G :=
    Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv
  simpa only [hc, Nat.add_zero] using
    (le_refl (ArithmeticFunction.cardFactors (Nat.card G)))

/-- Standard complement of affine row(8,3). -/
def generalTwoCertificate (h : PublishedSimplicity) :
    SmallAffineChiefOrderSavingCertificate (GeneralThree 2) 0 := by
  letI : IsSimpleGroup (GeneralThree 2) := simple_GL_two h
  exact simpleTopCertificate (GeneralThree 2) noncommutative_GL_two

/-- Standard complement of affine row(27,10). -/
def specialThreeCertificate (h : PublishedSimplicity) :
    SmallAffineChiefOrderSavingCertificate (SpecialThree 3) 0 := by
  letI : IsSimpleGroup (SpecialThree 3) := simple_SL_three h
  exact simpleTopCertificate (SpecialThree 3) (noncommutative_SL 3)

/-- Standard complement of affine row(27,11), retaining the actual
normal determinant kernel of order5616 inside the group of order11232. -/
def generalThreeCertificate (h : PublishedSimplicity) :
    SmallAffineChiefOrderSavingCertificate (GeneralThree 3) 1 := by
  letI : IsSimpleGroup determinantKernelThree := simple_determinantKernelThree h
  apply SmallAffineChiefOrderSavingCertificate.simpleNormal
  exact SmallAffineSimpleNormalChiefCertificate.ofOrders
    determinantKernelThree noncommutative_determinantKernelThree
    11232 5616 card_GL_three card_determinantKernelThree (by decide +kernel)

theorem nonsolvable_generalTwo (h : PublishedSimplicity) :
    ¬ IsSolvable (GeneralThree 2) :=
  (generalTwoCertificate h).not_isSolvable

theorem nonsolvable_specialThree (h : PublishedSimplicity) :
    ¬ IsSolvable (SpecialThree 3) :=
  (specialThreeCertificate h).not_isSolvable

theorem nonsolvable_generalThree (h : PublishedSimplicity) :
    ¬ IsSolvable (GeneralThree 3) :=
  (generalThreeCertificate h).not_isSolvable

end SymmetricSubgroupAsymptotics.StandardThreeDimensionalLinearGroups
