import SymmetricSubgroupAsymptotics.NonabelianSimpleNormalChiefSaving

/-! Corrected small-affine chief receipts. A nonabelian simple normal core
need not be the unique minimal normal subgroup of the ambient group.
The numerical order budget and the exact quotient-order form both imply
the same bound for every actual chief series. No old catalogue receipt is
an input to this adapter. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- A simple normal core together with the exact remaining order budget. -/
structure SmallAffineSimpleNormalChiefCertificate
    (G : Type) [Group G] [Finite G] (cap : ℕ) where
  core : Subgroup G
  [normal : core.Normal]
  [simple : IsSimpleGroup core]
  noncommutative : ¬ IsMulCommutative core
  order_budget : ArithmeticFunction.cardFactors (Nat.card G) ≤
    ArithmeticFunction.cardFactors (Nat.card core)+cap

namespace SmallAffineSimpleNormalChiefCertificate

variable {G : Type} [Group G] [Finite G] {cap : ℕ}

theorem chief_bound (C : SmallAffineSimpleNormalChiefCertificate G cap)
    (s : ActualChiefSeries G) : actualChiefSeriesAbelianLength s ≤ cap := by
  letI : C.core.Normal := C.normal
  letI : IsSimpleGroup C.core := C.simple
  have hs := actualChiefSeriesAbelianLength_add_simple_normal_order_le
    C.core s C.noncommutative
  have hb := C.order_budget
  omega

/-- Bind literal total/core orders and a finite numerical calculation. -/
def ofOrders (E : Subgroup G) [E.Normal] [IsSimpleGroup E]
    (hnc : ¬ IsMulCommutative E) (totalOrder coreOrder : ℕ)
    (hG : Nat.card G=totalOrder) (hE : Nat.card E=coreOrder)
    (hbudget : ArithmeticFunction.cardFactors totalOrder ≤
      ArithmeticFunction.cardFactors coreOrder+cap) :
    SmallAffineSimpleNormalChiefCertificate G cap where
  core := E
  noncommutative := hnc
  order_budget := by simpa only [hG,hE] using hbudget

end SmallAffineSimpleNormalChiefCertificate

/-- A drop-in replacement for the old uniqueness-based core receipt.
Its final parameter is still the actual quotient order. -/
structure SmallAffineSimpleNormalCoreCertificate
    (G : Type) [Group G] [Finite G] (quotientOrder : ℕ) where
  core : Subgroup G
  [normal : core.Normal]
  [simple : IsSimpleGroup core]
  noncommutative : ¬ IsMulCommutative core
  quotient_card_eq : Nat.card (G ⧸ core)=quotientOrder

namespace SmallAffineSimpleNormalCoreCertificate

variable {G : Type} [Group G] [Finite G] {quotientOrder : ℕ}

theorem chief_bound (C : SmallAffineSimpleNormalCoreCertificate G quotientOrder)
    (s : ActualChiefSeries G) :
    actualChiefSeriesAbelianLength s ≤ ArithmeticFunction.cardFactors quotientOrder := by
  letI : C.core.Normal := C.normal
  letI : IsSimpleGroup C.core := C.simple
  have hs := actualChiefSeriesAbelianLength_add_simple_normal_order_le
    C.core s C.noncommutative
  have horder : ArithmeticFunction.cardFactors (Nat.card G)=
      ArithmeticFunction.cardFactors quotientOrder+
        ArithmeticFunction.cardFactors (Nat.card C.core) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup C.core,
      ArithmeticFunction.cardFactors_mul
        (Nat.card_pos (α := G ⧸ C.core)).ne' (Nat.card_pos (α := C.core)).ne',
      C.quotient_card_eq]
  rw [horder] at hs
  omega

def toChiefCertificate (C : SmallAffineSimpleNormalCoreCertificate G quotientOrder)
    (cap : ℕ) (hcap : ArithmeticFunction.cardFactors quotientOrder ≤ cap) :
    SmallAffineSimpleNormalChiefCertificate G cap where
  core := C.core
  normal := C.normal
  simple := C.simple
  noncommutative := C.noncommutative
  order_budget := by
    letI : C.core.Normal := C.normal
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup C.core,
      ArithmeticFunction.cardFactors_mul
        (Nat.card_pos (α := G ⧸ C.core)).ne' (Nat.card_pos (α := C.core)).ne',
      C.quotient_card_eq]
    omega

end SmallAffineSimpleNormalCoreCertificate
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
