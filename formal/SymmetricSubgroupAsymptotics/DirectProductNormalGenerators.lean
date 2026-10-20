import SymmetricSubgroupAsymptotics.NormalGeneratorQuotientSocles
import SymmetricSubgroupAsymptotics.FiniteNormalChainGenerators
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Normal generators in a direct product

For an actual normal subgroup of a product, first generate its intersection
with the first factor, then lift generators of its image in the second.
The normal subgroup need not itself be a product. This avoids assuming a
splitting for diagonal or otherwise coupled normal subgroups.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Uniform ambient normal-generator bounds add under direct products. -/
theorem normal_generating_tuples_prod
    {G H : Type} [Group G] [Group H] {a b : ℕ}
    (hG : ∀ K : Subgroup G, K.Normal →
      ∃ x : Fin a → G, Subgroup.normalClosure (Set.range x) = K)
    (hH : ∀ K : Subgroup H, K.Normal →
      ∃ x : Fin b → H, Subgroup.normalClosure (Set.range x) = K) :
    ∀ N : Subgroup (G × H), N.Normal →
      ∃ x : Fin (a + b) → G × H, Subgroup.normalClosure (Set.range x) = N := by
  intro N hN
  letI := hN
  let ι : G →* G × H := MonoidHom.inl G H
  let π : G × H →* H := MonoidHom.snd G H
  have hπ : Function.Surjective π := fun h ↦ ⟨(1, h), rfl⟩
  obtain ⟨x, hx⟩ := hG (N.comap ι) (hN.comap ι)
  obtain ⟨y, hy⟩ := hH (N.map π) (hN.map π hπ)
  have hxN (i : Fin a) : ι (x i) ∈ N := by
    change x i ∈ N.comap ι
    rw [← hx]
    exact Subgroup.subset_normalClosure (Set.mem_range_self i)
  have hlift : ∀ i, ∃ z : G × H, z ∈ N ∧ π z = y i := by
    intro i
    have hyN : y i ∈ N.map π := by
      rw [← hy]
      exact Subgroup.subset_normalClosure (Set.mem_range_self i)
    exact hyN
  choose z hzN hz using hlift
  let u : Fin (a + b) → G × H := Fin.addCases (fun i ↦ ι (x i)) z
  let L := Subgroup.normalClosure (Set.range u)
  letI : L.Normal := by dsimp [L]; infer_instance
  have hxL (i : Fin a) : ι (x i) ∈ L := by
    have h := Subgroup.subset_normalClosure (Set.mem_range_self (f := u) (i.castAdd b))
    simpa only [u, Fin.addCases_left] using h
  have hzL (i : Fin b) : z i ∈ L := by
    have h := Subgroup.subset_normalClosure (Set.mem_range_self (f := u) (i.natAdd a))
    simpa only [u, Fin.addCases_right] using h
  have hLN : L ≤ N := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [u, Fin.addCases_left] using hxN j
    · intro j
      simpa only [u, Fin.addCases_right] using hzN j
  have hKL : N.comap ι ≤ L.comap ι := by
    rw [← hx]
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact hxL i
  have hML : N.map π ≤ L.map π := by
    letI : (L.map π).Normal := (inferInstance : L.Normal).map π hπ
    rw [← hy]
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact ⟨z i, hzL i, hz i⟩
  refine ⟨u, le_antisymm hLN ?_⟩
  intro n hn
  obtain ⟨l, hl, heq⟩ := hML (show π n ∈ N.map π from ⟨n, hn, rfl⟩)
  have hpair : ι (n * l⁻¹).1 = n * l⁻¹ := by
    apply Prod.ext
    · rfl
    · change 1 = n.2 * l.2⁻¹
      change l.2 = n.2 at heq
      simp [heq]
  have hk : (n * l⁻¹).1 ∈ N.comap ι := by
    change ι (n * l⁻¹).1 ∈ N
    rw [hpair]
    exact N.mul_mem hn (N.inv_mem (hLN hl))
  have hd : n * l⁻¹ ∈ L := by
    simpa only [Subgroup.mem_comap, hpair] using hKL hk
  simpa only [inv_mul_cancel_right] using L.mul_mem hd hl

/-- Every original quotient of the product has the same additive socle bound. -/
theorem quotientSocle_of_product_normal_generators
    {G H : Type} [Group G] [Group H] {a b : ℕ}
    (hG : ∀ K : Subgroup G, K.Normal →
      ∃ x : Fin a → G, Subgroup.normalClosure (Set.range x) = K)
    (hH : ∀ K : Subgroup H, K.Normal →
      ∃ x : Fin b → H, Subgroup.normalClosure (Set.range x) = K)
    (N : Subgroup (G × H)) [N.Normal] :
    SocleNormalGeneratorBound ((G × H) ⧸ N) (a + b) :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    (normal_generating_tuples_prod hG hH) N

/-- Two finite normal chains give two generators for every product normal
subgroup, including normal subgroups that couple the factors. -/
theorem normal_generating_pairs_prod_of_normal_total
    {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (hG : ∀ K L : Subgroup G, K.Normal → L.Normal → K ≤ L ∨ L ≤ K)
    (hH : ∀ K L : Subgroup H, K.Normal → L.Normal → K ≤ L ∨ L ≤ K) :
    ∀ N : Subgroup (G × H), N.Normal →
      ∃ x : Fin 2 → G × H, Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_prod
    (normal_generating_singletons_of_finite_normal_total hG)
    (normal_generating_singletons_of_finite_normal_total hH)

end SymmetricSubgroupAsymptotics

end
