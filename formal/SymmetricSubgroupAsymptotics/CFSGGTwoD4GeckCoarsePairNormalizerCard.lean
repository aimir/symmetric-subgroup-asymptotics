import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckTorusStabilizer
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalPairNormalizer
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart

/-! A coarse but actual opposed-pair normalizer count for original G2.
The original centreless group embeds by inner action into its already
proved opposed-pair automorphism stabilizer. Its actual torus range and
the two checked indices supply the cardinality; no model order formula
or extra automorphism description is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckCoarsePairNormalizerCard
open CFSGGTwoD4GeckTorusStabilizer CFSGGTwoD4GeckOriginalSimpleStabilizer
open CFSGGTwoD4GeckOriginalPairNormalizer CFSGGTwoD4GeckOriginalProjection
open CFSG.Models.Chevalley PrimitiveSocleRawStructure CFSGSubgroupFamilyStabilizer
variable (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.G₂ K)]
    (p : ℕ) [Fact p.Prime] [CharP K p]

private theorem map_conj_eq {G : Type*} [Group G] (P : Subgroup G) (d : G)
    (hd : d∈Subgroup.normalizer (P : Set G)) :
    P.map (MulAut.conj d).toMonoidHom=P := by
  apply SetLike.coe_injective
  exact Subgroup.mem_normalizer_iff_conj_image_eq.mp hd

theorem pairStabilizer_card_le :
    Nat.card (pairStabilizer K p)≤2*Nat.card (Kˣ)^2*Nat.card (RingAut K) := by
  letI := original_finite K
  have htorus : Nat.card (productTorusSimpleHom K p).range≤Nat.card (Kˣ)^2 := by
    have h := Nat.card_le_card_of_surjective
      ((productTorusSimpleHom K p).rangeRestrict)
      (productTorusSimpleHom K p).rangeRestrict_surjective
    simpa only [Nat.card_fun,Nat.card_fin] using h
  have hs : Nat.card (simpleStabilizer K p)≤Nat.card (Kˣ)^2*Nat.card (RingAut K) := by
    rw [←(productTorusSimpleHom K p).range.card_mul_index]
    exact Nat.mul_le_mul htorus (product_torus_index_le K p)
  calc
    Nat.card (pairStabilizer K p)=
        Nat.card (simpleStabilizer K p)*(simpleStabilizer K p).index :=
      (simpleStabilizer K p).card_mul_index.symm
    _ ≤ (Nat.card (Kˣ)^2*Nat.card (RingAut K))*2 :=
      Nat.mul_le_mul hs (simple_stabilizer_index_le_two K p)
    _ = _ := by ring

theorem originalPairNormalizer_card_le
    (hn : ¬IsMulCommutative (Projective CartanMatrix.G₂ K)) :
    Nat.card (originalPairNormalizer K p)≤2*Nat.card (Kˣ)^2*Nat.card (RingAut K) := by
  letI := original_finite K
  have hcent := centerless_of_nonabelian_simple (Projective CartanMatrix.G₂ K) hn
  have hconj : Function.Injective
      (MulAut.conj : Projective CartanMatrix.G₂ K→*MulAut (Projective CartanMatrix.G₂ K)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_antisymm ?_ bot_le
    intro x hx
    change x=1
    apply hcent x
    intro y
    have he : x*y*x⁻¹=y := congrArg
      (fun f : MulAut (Projective CartanMatrix.G₂ K)=>f y) hx
    have hh := congrArg (fun z=>z*x) he
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
  let encode (d : originalPairNormalizer K p) : pairStabilizer K p :=
    ⟨MulAut.conj d.val,by
      intro neg
      cases neg
      · exact map_conj_eq _ d.val d.property.1
      · exact map_conj_eq _ d.val d.property.2⟩
  have hi : Function.Injective encode := by
    intro d e he
    exact Subtype.ext (hconj (congrArg Subtype.val he))
  exact (Nat.card_le_card_of_injective encode hi).trans (pairStabilizer_card_le K p)

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckCoarsePairNormalizerCard
