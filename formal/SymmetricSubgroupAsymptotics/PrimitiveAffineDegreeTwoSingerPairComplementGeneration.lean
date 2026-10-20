import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSingerPairComplements
import SymmetricSubgroupAsymptotics.GeneratedLiteralImage

/-! Four displayed generators generate the full paired Singer complement
image. The proof uses residue powers in two coordinates and the actual
semidirect decomposition, with no order comparison or group table. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoSingerPairComplements

open SemidirectProduct

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

variable (twisted : Bool)

def sourceGenerators : Fin 4 → Model twisted :=
  ![inl (Multiplicative.ofAdd (![1, 0] : Plane)),
    inl (Multiplicative.ofAdd (![0, 1] : Plane)),
    inr (inl (Multiplicative.ofAdd 1)), inr (inr C2Wreath.gen)]

private theorem plane_decomposition (v : Multiplicative Plane) :
    (Multiplicative.ofAdd (![1, 0] : Plane)) ^ (v.toAdd 0).val *
      (Multiplicative.ofAdd (![0, 1] : Plane)) ^ (v.toAdd 1).val = v := by
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · change ((v.toAdd 0).val • (1 : ZMod 7)) + ((v.toAdd 1).val • 0) = v.toAdd 0
    simp only [nsmul_eq_mul, mul_one, mul_zero, add_zero, ZMod.natCast_zmod_val]
  · change ((v.toAdd 0).val • (0 : ZMod 7)) + ((v.toAdd 1).val • 1) = v.toAdd 1
    simp only [nsmul_eq_mul, mul_one, mul_zero, zero_add, ZMod.natCast_zmod_val]

private theorem ternary_decomposition (c : Ternary) :
    (Multiplicative.ofAdd (1 : ZMod 3)) ^ c.toAdd.val = c := by
  apply Multiplicative.toAdd.injective
  change c.toAdd.val • (1 : ZMod 3) = c.toAdd
  simp only [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

theorem source_mem_of_generators {H : Type} [Group H]
    (q : Model twisted →* H) (K : Subgroup H)
    (hg : ∀ i, q (sourceGenerators twisted i) ∈ K)
    (g : Model twisted) : q g ∈ K := by
  have ht (v : Multiplicative Plane) : q (inl v) ∈ K := by
    rw [← plane_decomposition v]
    simp only [map_mul, map_pow]
    exact K.mul_mem (K.pow_mem (hg 0) _) (K.pow_mem (hg 1) _)
  have hc (c : Ternary) : q (inr (inl c)) ∈ K := by
    rw [← ternary_decomposition c]
    simp only [map_pow]
    exact K.pow_mem (hg 2) _
  have hb (b : Binary) : q (inr (inr b)) ∈ K := by
    rcases C2Wreath.cases b with rfl | rfl
    · rw [map_one, map_one, map_one]
      exact K.one_mem
    · exact hg 3
  have hu (u : Upper twisted) : q (inr u) ∈ K := by
    rw [← inl_left_mul_inr_right u]
    simp only [map_mul]
    exact K.mul_mem (hc u.left) (hb u.right)
  rw [← inl_left_mul_inr_right g, map_mul]
  exact K.mul_mem (ht g.left) (hu g.right)

theorem source_generators_top : Subgroup.closure (Set.range (sourceGenerators twisted)) = ⊤ := by
  apply le_antisymm le_top
  intro g _
  exact source_mem_of_generators twisted (MonoidHom.id _) _
    (fun i ↦ Subgroup.subset_closure (Set.mem_range_self i)) g

theorem source_generators_binding (i : Fin 4) :
    intoWreath twisted (sourceGenerators twisted i) = generators twisted i := by
  fin_cases i
  · change ScalarPairSwapWreathImage.intoWreath 7 (alpha twisted) scalarCharacter
      singerPower frobeniusPower scalar_conjugation
      (inl (Multiplicative.ofAdd (![1, 0] : Plane))) = C2Wreath.firstFactor s
    rw [ScalarPairSwapWreathImage.intoWreath, SemidirectProduct.lift_inl]
    apply SemidirectProduct.ext
    · exact Prod.ext (ZModPowerHom.apply_ofAdd_one 7 s _ (by decide)) singerPower.map_one
    · rfl
  · change ScalarPairSwapWreathImage.intoWreath 7 (alpha twisted) scalarCharacter
      singerPower frobeniusPower scalar_conjugation
      (inl (Multiplicative.ofAdd (![0, 1] : Plane))) = inl (1, s)
    rw [ScalarPairSwapWreathImage.intoWreath, SemidirectProduct.lift_inl]
    apply SemidirectProduct.ext
    · exact Prod.ext singerPower.map_one (ZModPowerHom.apply_ofAdd_one 7 s _ (by decide))
    · rfl
  · change ScalarPairSwapWreathImage.intoWreath 7 (alpha twisted) scalarCharacter
      singerPower frobeniusPower scalar_conjugation
      (inr (inl (Multiplicative.ofAdd 1))) = ternaryPair twisted
    rw [ScalarPairSwapWreathImage.intoWreath, SemidirectProduct.lift_inr]
    rfl
  · change ScalarPairSwapWreathImage.intoWreath 7 (alpha twisted) scalarCharacter
      singerPower frobeniusPower scalar_conjugation (inr (inr C2Wreath.gen)) = inr C2Wreath.gen
    rw [ScalarPairSwapWreathImage.intoWreath, SemidirectProduct.lift_inr]
    exact C2WreathTwistedDiagonal.intoWreath_inr (alpha twisted) frobeniusPower C2Wreath.gen

theorem complement_eq_closure : Complement twisted = Subgroup.closure (Set.range (generators twisted)) :=
  GeneratedLiteralImage.range_eq (intoWreath twisted) (sourceGenerators twisted)
    (generators twisted) (Equiv.refl _) (source_generators_top twisted)
    (source_generators_binding twisted)

theorem mem_of_generators (K : Subgroup (C2Wreath.W R))
    (hg : ∀ i, generators twisted i ∈ K) (c : Complement twisted) : c.val ∈ K := by
  have hle : Complement twisted ≤ K := by
    rw [complement_eq_closure]
    exact (Subgroup.closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact hg i)
  exact hle c.property

/-- Generator transport inside the exact image, without replacing its
subtype by an abstract isomorphic group. -/
theorem hom_mem_of_generators {H : Type} [Group H]
    (q : Complement twisted →* H) (K : Subgroup H)
    (hg : ∀ i, q ⟨generators twisted i, generators_mem twisted i⟩ ∈ K)
    (c : Complement twisted) : q c ∈ K := by
  obtain ⟨g, hgimage⟩ := c.property
  have he : (intoWreath twisted).rangeRestrict g = c := Subtype.ext hgimage
  rw [← he]
  apply source_mem_of_generators twisted (q.comp (intoWreath twisted).rangeRestrict) K
  intro i
  change q ((intoWreath twisted).rangeRestrict (sourceGenerators twisted i)) ∈ K
  have hi : (intoWreath twisted).rangeRestrict (sourceGenerators twisted i) =
      ⟨generators twisted i, generators_mem twisted i⟩ :=
    Subtype.ext (source_generators_binding twisted i)
  rw [hi]
  exact hg i

end PrimitiveAffineDegreeTwoSingerPairComplements
end SymmetricSubgroupAsymptotics

end
