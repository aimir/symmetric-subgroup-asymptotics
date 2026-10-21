import SymmetricSubgroupAsymptotics.LinearSemidirectProperNormalF
import SymmetricSubgroupAsymptotics.QuotientSubgroupProjectionCard

/-! A joint centralizer bound for a proper normal image retains the SAME
original normal denominator. Its two factors are the actual z-fixed
translation axis and the actual top action on B modulo that axis. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.LinearSemidirectCoprimeSocleBounds
open SemidirectProduct
variable {p : ℕ} [Fact p.Prime] {R V : Type}
    [Group R] [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V]
    (rho : R →* (V ≃ₗ[ZMod p] V))

private theorem quotient_centralizer_commutator_mem
    (N D : Subgroup (Model rho)) [N.Normal]
    (g : Model rho)
    (hg : QuotientGroup.mk' N g ∈
      Subgroup.centralizer ((D.map (QuotientGroup.mk' N)) : Set (Model rho ⧸ N)))
    (f : Model rho) (hf : f ∈ D) : ⁅g, f⁆ ∈ N := by
  have h := Subgroup.mem_centralizer_iff.mp hg (QuotientGroup.mk' N f)
    ⟨f, hf, rfl⟩
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' N ⁅g, f⁆ = 1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact h.symm

theorem properNormalF_quotient_centralizer_card_mul_le
    [Finite R] [Finite V]
    (B A : Submodule (ZMod p) V) (z : R) (hz : z ∈ Subgroup.center R)
    (N : Subgroup (Model rho)) [N.Normal]
    (hNA : ∀ v, (inl (Multiplicative.ofAdd v) : Model rho) ∈ N ↔ v ∈ A) :
    Nat.card N * Nat.card (Subgroup.centralizer
      (((properNormalF rho B z).map (QuotientGroup.mk' N)) : Set (Model rho ⧸ N))) ≤
      Nat.card {v : V // rho z v - v ∈ A} *
        Nat.card {t : R // ∀ v, v ∈ B → rho t v - v ∈ A} := by
  letI : Finite (Model rho) :=
    Finite.of_equiv (Multiplicative V × R) SemidirectProduct.equivProd.symm
  let q := QuotientGroup.mk' N
  let S := Subgroup.centralizer (((properNormalF rho B z).map q) : Set (Model rho ⧸ N))
  let P := S.comap q
  let K := P ⊓ (rightHom : Model rho →* R).ker
  have hzF : (inr z : Model rho) ∈ properNormalF rho B z :=
    Subgroup.subset_closure ⟨Sum.inr (), rfl⟩
  have hfixed (g : Model rho) (hg : q g ∈ S) : rho z g.left.toAdd - g.left.toAdd ∈ A := by
    have hm := quotient_centralizer_commutator_mem rho N (properNormalF rho B z) g hg
      (inr z) hzF
    have hi : ⁅(inr z : Model rho), g⁆ ∈ N := by
      rw [← commutatorElement_inv]
      exact N.inv_mem hm
    rw [commutator_central_complement rho z hz] at hi
    exact (hNA _).mp hi
  have htop (g : Model rho) (hg : q g ∈ S) :
      ∀ v, v ∈ B → rho g.right v - v ∈ A := by
    intro v hv
    have hvF : (inl (Multiplicative.ofAdd v) : Model rho) ∈ properNormalF rho B z :=
      Subgroup.subset_closure ⟨Sum.inl (⟨v, hv⟩ : B), rfl⟩
    have hm := quotient_centralizer_commutator_mem rho N (properNormalF rho B z) g hg
      (inl (Multiplicative.ofAdd v)) hvF
    rw [commutator_translation] at hm
    exact (hNA _).mp hm
  have hb := QuotientSubgroupProjectionCard.card_mul_le N S
    (rightHom : Model rho →* R) K
    (fun t => ∀ v, v ∈ B → rho t v - v ∈ A)
    (fun g hg hu => ⟨hu, hg⟩) htop
  let f : K → {v : V // rho z v - v ∈ A} := fun g =>
    ⟨g.val.left.toAdd, hfixed g.val g.property.1⟩
  have hf : Function.Injective f := by
    intro g h he
    apply Subtype.ext
    apply SemidirectProduct.ext
    · exact congrArg Multiplicative.ofAdd (congrArg Subtype.val he)
    · exact g.property.2.trans h.property.2.symm
  exact hb.trans (Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective f hf))

end SymmetricSubgroupAsymptotics.LinearSemidirectCoprimeSocleBounds
