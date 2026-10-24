import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckCoarsePairNormalizerCard
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFiniteFixedBruhatCover
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckFixedPositiveCardinality
import SymmetricSubgroupAsymptotics.FiniteFourFactorCoverCardinality
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsParameters

/-! The actual twelve-word fixed Bruhat cover descends to original G2.
Its two positive factors have order q^6; the actual opposed-pair
normalizer is counted through proved original inner actions. This
improves the coarse matrix-space ceiling without supplying a group
order formula or assuming full fixed-group perfectness. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckFixedBruhatOrderUpper
open CFSGGTwoD4GeckOriginalProjection CFSGGTwoD4GeckOriginalPairNormalizer
open CFSGGTwoD4GeckFixedPositiveCardinality CFSGGTwoD4GeckCoarsePairNormalizerCard
open CFSGTrialityGeckFiniteFixedBruhatCover CFSGTrialityD4FiniteWeylMenu
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckRootGeneratedPGroup
open CFSGTrialityGeckFixedPairNormalizer CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.G₂ K)]

def originalMenuWord (i : Menu) : Projective CartanMatrix.G₂ K :=
  generatedToOriginal K ⟨menuMatrix K i,menuMatrix_mem_generated K (RingEquiv.refl K) i⟩

theorem exists_original_finite_cell (p : ℕ) [Fact p.Prime] [CharP K p]
    (g : Projective CartanMatrix.G₂ K) :
    ∃ u : (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)),
      ∃ d : originalPairNormalizer K p, ∃ i : Menu,
      ∃ v : (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)),
        g=u.val*d.val*originalMenuWord K i*v.val := by
  obtain ⟨x,rfl⟩ := generatedToOriginal_surjective K g
  obtain ⟨u,hu,d,hd,i,v,hv,he⟩ := exists_finite_fixed_cell K (RingEquiv.refl K) x.val x.property
  let U : fixedRootGenerated K (RingEquiv.refl K) :=
    ⟨u,signedFixed_le_generated K (RingEquiv.refl K) false hu⟩
  let D : fixedRootGenerated K (RingEquiv.refl K) := ⟨d,hd.2⟩
  let V : fixedRootGenerated K (RingEquiv.refl K) :=
    ⟨v,signedFixed_le_generated K (RingEquiv.refl K) false hv⟩
  let W : fixedRootGenerated K (RingEquiv.refl K) :=
    ⟨menuMatrix K i,menuMatrix_mem_generated K (RingEquiv.refl K) i⟩
  have huO : generatedToOriginal K U∈(originalPositiveSylow K p : Subgroup _) := by
    rw [originalPositiveSylow_coe]
    exact ⟨U,hu,rfl⟩
  have hvO : generatedToOriginal K V∈(originalPositiveSylow K p : Subgroup _) := by
    rw [originalPositiveSylow_coe]
    exact ⟨V,hv,rfl⟩
  have hdO : generatedToOriginal K D∈originalPairNormalizer K p :=
    (mem_originalPairNormalizer_iff K p D).mpr hd
  refine ⟨⟨_,huO⟩,⟨_,hdO⟩,i,⟨_,hvO⟩,?_⟩
  have hx : x=U*D*W*V := Subtype.ext he
  simpa only [map_mul,originalMenuWord,W] using congrArg (generatedToOriginal K) hx

theorem originalPositiveSylow_card_le (p : ℕ) [Fact p.Prime] [CharP K p] :
    Nat.card (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)) ≤
      Nat.card K^6 := by
  let P := rootPart K (RingEquiv.refl K) false
  have hm : Nat.card (P.map (generatedToOriginal K)) ≤ Nat.card P :=
    Nat.card_le_card_of_surjective ((generatedToOriginal K).subgroupMap P)
      ((generatedToOriginal K).subgroupMap_surjective P)
  have hc : Nat.card P = Nat.card K ^ 6 := rootPart_card K
  have he := Nat.card_congr (MulEquiv.subgroupCongr
    (originalPositiveSylow_coe K p)).toEquiv
  exact he.le.trans (hm.trans_eq hc)

theorem original_order_le (p : ℕ) [Fact p.Prime] [CharP K p]
    (hn : ¬IsMulCommutative (Projective CartanMatrix.G₂ K)) :
    Nat.card (Projective CartanMatrix.G₂ K)≤
      24*Nat.card (Kˣ)^2*Nat.card (RingAut K)*Nat.card K^12 := by
  letI := original_finite K
  have hc := FiniteFourFactorCoverCardinality.card_le_of_cover
    (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K))
    (originalPairNormalizer K p)
    (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K))
    (originalMenuWord K) (exists_original_finite_cell K p)
  rw [menu_card] at hc
  have hncard := CFSGGTwoD4GeckCoarsePairNormalizerCard.originalPairNormalizer_card_le K p hn
  exact hc.trans ((Nat.mul_le_mul
    (Nat.mul_le_mul_right 12 (Nat.mul_le_mul (originalPositiveSylow_card_le K p) hncard))
    (originalPositiveSylow_card_le K p)).trans_eq (by ring))

theorem typeGTwo_order_le (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.G2 q)]
    (hn : ¬IsMulCommutative (CFSG.Models.G2 q)) :
    Nat.card (CFSG.Models.G2 q)≤24*q.exponent*q.order^14 := by
  have hu : Nat.card (q.Fieldˣ)≤q.order := by
    rw [←q.card_field]
    exact Nat.card_le_card_of_injective (fun x : q.Fieldˣ=>(x : q.Field)) Units.val_injective
  have hc := original_order_le q.Field q.prime hn
  rw [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q,q.card_field] at hc
  exact hc.trans ((Nat.mul_le_mul_right (q.order^12)
    (Nat.mul_le_mul_right q.exponent (Nat.mul_le_mul_left 24 (Nat.pow_le_pow_left hu 2)))).trans_eq
      (by ring))

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckFixedBruhatOrderUpper
