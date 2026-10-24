import SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupPeelingChain
import SymmetricSubgroupAsymptotics.FiniteIndexedBruhatCoverCardinality

/-! The indexed cover consumes genuine recursive opposed residuals.
Their proved containment in the inverse-prefix conjugate is enough to
absorb the right coset factors. No equality with a single intersection,
whole-group order, or unique cell coordinates is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupPeelingCover
open CFSGOpposedSubgroupPeeling CFSGOpposedSubgroupPeelingChain
variable {G I : Type*} [Group G] [Finite G] [Fintype I]

theorem card_le_ambient_residual_cover
    (U D : Subgroup G) (w : I → G) (R : I → Subgroup G) (c : I → ℕ)
    (hRU : ∀ i, R i ≤ U)
    (hcover : ∀ g : G, ∃ (u : U) (d : D) (i : I) (v : U),
      g=u.val*d.val*w i*v.val)
    (hD : ∀ (d : D) (u : U), d.val*u.val*d.val⁻¹ ∈ U)
    (hR : ∀ i, ∀ r ∈ R i, w i*r*(w i)⁻¹ ∈ U)
    (hcard : ∀ i, Nat.card U = Nat.card (R i)*c i) :
    Nat.card G ≤ Nat.card U * Nat.card D * ∑ i, c i := by
  let S : I → Subgroup U := fun i => (R i).comap U.subtype
  have hc (i : I) : Nat.card (S i) = Nat.card (R i) := by
    let e : S i ≃ R i := {
      toFun r := ⟨r.val.val,r.property⟩
      invFun r := ⟨⟨r.val,hRU i r.property⟩,r.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    exact Nat.card_congr e
  apply FiniteIndexedBruhatCoverCardinality.card_le_of_residual_card_factors
    U D w S c hcover hD
  · intro i r
    exact hR i r.val.val r.property
  · intro i
    rw [hc]
    exact hcard i

theorem residual_conjugates_mem (U : Subgroup G) (step : ℕ → G)
    (n : ℕ) (w : G) (hp : wordPrefix step n = w⁻¹)
    (r : G) (hr : r ∈ residual U step n) : w*r*w⁻¹ ∈ U := by
  obtain ⟨u,hu,he⟩ := residual_le_prefix U step n hr
  change wordPrefix step n*u*(wordPrefix step n)⁻¹=r at he
  rw [hp] at he
  have hx : w*r*w⁻¹=u := by rw [←he]; group
  rw [hx]
  exact hu

theorem card_le_sum_inversion_products
    (U V D : Subgroup G) (w : I → G) (step : I → ℕ → G) (n : I → ℕ)
    (hcover : ∀ g : G, ∃ (u : U) (d : D) (i : I) (v : U),
      g=u.val*d.val*w i*v.val)
    (hD : ∀ (d : D) (u : U), d.val*u.val*d.val⁻¹ ∈ U)
    (hdis : Disjoint U V)
    (hprefix : ∀ i, wordPrefix (step i) (n i) = (w i)⁻¹)
    (hBR : ∀ i j, j < n i → inversionPart U V (step i j) ≤ residual U (step i) j)
    (hfactor : ∀ i j, j < n i → ∀ x ∈ U,
      ∃ p ∈ U, ∃ b ∈ inversionPart U V (step i j), x=p*b ∧
        step i j*p*(step i j)⁻¹ ∈ U) :
    Nat.card G ≤ Nat.card U * Nat.card D *
      ∑ i, ∏ j ∈ Finset.range (n i), Nat.card (inversionPart U V (step i j)) := by
  apply card_le_ambient_residual_cover U D w (fun i => residual U (step i) (n i))
    (fun i => ∏ j ∈ Finset.range (n i), Nat.card (inversionPart U V (step i j)))
    (fun i => residual_le U (step i) (n i)) hcover hD
  · intro i r hr
    exact residual_conjugates_mem U (step i) (n i) (w i) (hprefix i) r hr
  · intro i
    exact card_eq_residual_mul_blocks U V (step i) (n i) hdis (hBR i) (hfactor i)

end SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupPeelingCover
