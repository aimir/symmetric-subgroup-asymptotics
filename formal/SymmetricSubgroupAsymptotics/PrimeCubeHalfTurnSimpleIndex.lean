import SymmetricSubgroupAsymptotics.PrimeCubeHalfTurnAmbientAction
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimeCubeHalfTurnSimpleIndex
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {p : ℕ}

theorem index_ge_two_prime_square (hp : p.Prime) (R : Subgroup G)
    (hR : Nat.card R = p ^ 3)
    (hZ : Nat.card ↥(R ⊓ Subgroup.centralizer (R : Set G)) = p)
    (hcomm : ⁅R, R⁆ = R ⊓ Subgroup.centralizer (R : Set G))
    (t : G) (ht : t ∈ Subgroup.normalizer (R : Set G))
    (hline : ∀ F : Subgroup G,
      R ⊓ Subgroup.centralizer (R : Set G) ≤ F → F ≤ R → F.relIndex R = p →
      t ∉ Subgroup.normalizer (F : Set G))
    (K : Subgroup G) (hK : K ≠ ⊤) : 2 * p ^ 2 ≤ K.index := by
  letI : FaithfulSMul G (G ⧸ K) :=
    { eq_of_smul_eq_smul := by
        intro a b hab
        by_contra hne
        have hz : b⁻¹ * a ≠ 1 := by
          simpa only [inv_mul_eq_one, ne_eq, eq_comm] using hne
        obtain ⟨x, hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one K hK _ hz
        apply hx
        calc
          (b⁻¹ * a) • x = b⁻¹ • (a • x) := mul_smul _ _ _
          _ = b⁻¹ • (b • x) := by rw [hab x]
          _ = x := inv_smul_smul b x }
  exact PrimeCubeHalfTurnAmbientAction.card_ge_two_prime_square
    (X := G ⧸ K) hp R hR hZ hcomm t ht hline

end SymmetricSubgroupAsymptotics.PrimeCubeHalfTurnSimpleIndex
