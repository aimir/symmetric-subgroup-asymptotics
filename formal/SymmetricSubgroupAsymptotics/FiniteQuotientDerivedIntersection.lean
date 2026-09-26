import SymmetricSubgroupAsymptotics.FiniteQuotientInvariantCertificates

/-! Actual quotient invariants reduce to the intersection of the original
normal subgroup with the original derived subgroup. The quotient center
preimages are literally equal subgroups of G. Cardinal identities use the
actual restricted quotient map, without assuming N is contained in G′. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal]

/-- The original commutator criterion without a chosen finite tuple. -/
theorem mem_quotientCenterPreimage_iff_all_commutators (x : G) :
    x ∈ quotientCenterPreimage N ↔ ∀ y : G, ⁅x,y⁆ ∈ N := by
  have hgen : Subgroup.closure (Set.range (fun y : G => y)) = ⊤ := by
    apply top_unique
    intro y _
    exact Subgroup.subset_closure ⟨y,rfl⟩
  exact mem_quotientCenterPreimage_iff N (fun y : G => y) hgen x

/-- Every original commutator already lies in G′, so replacing N by
N ∩ G′ leaves the literal quotient-center preimage unchanged. -/
theorem quotientCenterPreimage_eq_inf_commutator :
    quotientCenterPreimage N = quotientCenterPreimage (N ⊓ commutator G) := by
  ext x
  rw [mem_quotientCenterPreimage_iff_all_commutators N x,
    mem_quotientCenterPreimage_iff_all_commutators (N ⊓ commutator G) x]
  constructor
  · intro hx y
    exact ⟨hx y, Subgroup.commutator_mem_commutator
      (Subgroup.mem_top x) (Subgroup.mem_top y)⟩
  · intro hx y
    exact (hx y).1

variable (C : Subgroup G) [C.Normal]

/-- The kernel of C → G/N is the actual intersection N ∩ C, with
unchanged original elements. There is no containment premise N≤C. -/
def normalChainKernelInfEquiv : (normalChainMap N C).ker ≃* ↥(N ⊓ C) where
  toFun x := ⟨(x.1 : G),
    ⟨(QuotientGroup.eq_one_iff (N := N) (x.1 : G)).mp
      (congrArg Subtype.val x.2), x.1.2⟩⟩
  invFun b := ⟨⟨(b : G),b.2.2⟩, Subtype.ext
    ((QuotientGroup.eq_one_iff (N := N) (b : G)).mpr b.2.1)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Cardinal factorization of the image of C in the actual quotient G/N. -/
theorem normalChainQuotient_card_mul_inf [Finite G] :
    Nat.card (normalChainQuotient N C) * Nat.card ↥(N ⊓ C) = Nat.card C := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (normalChainMap N C).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      (normalChainMap N C) (normalChainMap_surjective N C)).toEquiv,
    Nat.card_congr (normalChainKernelInfEquiv N C).toEquiv] at h
  exact h.symm

/-- The derived group of G/N is the image of the actual G′; its kernel
is N ∩ G′ even when the original normal N is not contained in G′. -/
theorem quotientCommutator_card_mul_inf [Finite G] :
    Nat.card (commutator (G ⧸ N)) * Nat.card ↥(N ⊓ commutator G) =
      Nat.card (commutator G) := by
  have he : normalChainQuotient N (commutator G) = commutator (G ⧸ N) := by
    rw [normalChainQuotient, map_commutator_eq,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)]
    rfl
  have hc := normalChainQuotient_card_mul_inf N (commutator G)
  rwa [he] at hc

/-- The original center preimage depends only on N ∩ G′, while the
quotient-center order retains the size of the complete original N. -/
theorem quotientCenter_card_mul_inf_commutator [Finite G] :
    Nat.card (Subgroup.center (G ⧸ N)) * Nat.card N =
      Nat.card (quotientCenterPreimage (N ⊓ commutator G)) := by
  rw [← quotientCenterPreimage_eq_inf_commutator N]
  exact quotientCenter_card_mul N

theorem quotientCommutator_card_eq_div_inf [Finite G] :
    Nat.card (commutator (G ⧸ N)) =
      Nat.card (commutator G) / Nat.card ↥(N ⊓ commutator G) := by
  rw [← quotientCommutator_card_mul_inf N,
    Nat.mul_div_cancel _ (Nat.card_pos (α := ↥(N ⊓ commutator G)))]

theorem quotientCenter_card_eq_div_inf_commutator [Finite G] :
    Nat.card (Subgroup.center (G ⧸ N)) =
      Nat.card (quotientCenterPreimage (N ⊓ commutator G)) / Nat.card N := by
  rw [← quotientCenter_card_mul_inf_commutator N,
    Nat.mul_div_cancel _ (Nat.card_pos (α := N))]

end SymmetricSubgroupAsymptotics
