import SymmetricSubgroupAsymptotics.PrimitiveSoclePowerDegreeOrderBound
import SymmetricSubgroupAsymptotics.AlternatingSocleProductOrderNumerics
import SymmetricSubgroupAsymptotics.CFSGAlternatingOuterBound
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! All original subgroups are covered when the actual alternating
socle has at least two factors and the degree is the proper-index form.
The socle isomorphism and outer-wreath embedding are those of the
original raw structure. No product-action recognition is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.card_le_alternating_product
    (D : NonaffineData G X) (m : ℕ) (hm : 5 ≤ m)
    (e : D.Simple ≃* alternatingGroup (Fin m)) :
    Nat.card G ≤ (2*m.factorial)^D.factorCount*D.factorCount.factorial := by
  let s := Nat.card D.Simple
  let o := Nat.card (Outer D.Simple)
  let k := D.factorCount
  have hs : 2*s=m.factorial := by
    letI : Nontrivial (Fin m) := Finite.one_lt_card_iff_nontrivial.mp (by simp; omega)
    dsimp only [s]
    rw [Nat.card_congr e.toEquiv]
    simpa only [Nat.card_perm,Nat.card_fin] using
      (two_mul_nat_card_alternatingGroup (α := Fin m))
  have ho : o ≤ 4 := by
    dsimp only [o]
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGAlternatingOuterBound.outer_card_le_four m hm
  have hso : s*o ≤ 2*m.factorial := by nlinarith
  have hsocle : Nat.card (finiteGroupSocle G)=s^k := by
    rw [Nat.card_congr D.socleEquiv.toEquiv,Nat.card_fun,Nat.card_fin]
  have hquotient : Nat.card (G⧸finiteGroupSocle G) ≤ o^k*k.factorial := by
    have h := Nat.card_le_card_of_injective D.quotientEmbedding D.quotientEmbedding_injective
    have he : Nat.card (OuterWreathPermutationCompression.Wreath (Outer D.Simple) k)=
        o^k*k.factorial := by
      rw [PermutationalWreathProduct.natCard_eq,Nat.card_fin,Nat.card_perm,Nat.card_fin]
    exact h.trans_eq he
  calc
    Nat.card G = Nat.card (G⧸finiteGroupSocle G)*Nat.card (finiteGroupSocle G) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (finiteGroupSocle G)
    _ ≤ (o^k*k.factorial)*s^k := Nat.mul_le_mul hquotient hsocle.le
    _ = (s*o)^k*k.factorial := by rw [mul_pow]; ring
    _ ≤ (2*m.factorial)^k*k.factorial :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hso k)

theorem NonaffineData.subgroup_class_cube_le_of_alternating_index_form
    (D : NonaffineData G X) (m : ℕ) (hm : 5 ≤ m)
    (e : D.Simple ≃* alternatingGroup (Fin m)) (hk : 2 ≤ D.factorCount)
    (K : Subgroup D.Simple) (hK : K≠⊤)
    (hdegree : Nat.card X=K.index^D.factorCount) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  have hell := CFSGReduction.leastProperIndex_of_mulEquiv e.symm m
    (CFSGAlternatingMinimumIndex.leastProperIndex_degree m hm)
  have hdegreeLower : m^D.factorCount ≤ Nat.card X :=
    (Nat.pow_le_pow_left (hell.2 K hK) _).trans_eq hdegree.symm
  have hc : Nat.card (ConjClasses H) ≤
      (2*m.factorial)^D.factorCount*D.factorCount.factorial :=
    (Nat.card_le_card_of_surjective (@ConjClasses.mk H _) ConjClasses.mk_surjective).trans
      (H.card_le_card_group.trans (D.card_le_alternating_product m hm e))
  exact (Nat.pow_le_pow_left hc 3).trans
    ((AlternatingSocleProductOrderNumerics.factorial_product_cube m D.factorCount hm hk).trans
      (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hdegreeLower 1)))

theorem NonaffineData.subgroup_class_cube_le_of_alternating_multiple_factors
    (D : NonaffineData G X) (m : ℕ) (hm : 5 ≤ m)
    (e : D.Simple ≃* alternatingGroup (Fin m)) (hk : 2 ≤ D.factorCount)
    (hn : 1024 ≤ Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  rcases D.indexForm with ⟨K,hK,hdegree⟩ | ⟨a,hka,hdegree⟩
  · exact D.subgroup_class_cube_le_of_alternating_index_form m hm e hk K hK hdegree H
  · exact D.subgroup_class_cube_le_of_power_form a hka hdegree hn H

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
