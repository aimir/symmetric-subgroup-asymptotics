import SymmetricSubgroupAsymptotics.TransitiveTwoRegularOrbitChart
import SymmetricSubgroupAsymptotics.BinaryPairEightResidualReduction
import SymmetricSubgroupAsymptotics.PermutationBinaryRankTwoImages

/-! Actual top and source orders in the remaining eight-pair residual.

The normal index-two kernel embeds by its two literal regular orbit
images into V × V and maps onto each actual V of order four. This gives
its actual orders 4,8,16 and the actual top orders 8,16,32. The original
source orders are consequently 512,1024,2048. At top order eight the
unchanged original normal quotient already has order at most 128.
The full original normal image is retained; no N = N intersect K or
split outside complement is assumed.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.TransitiveTwoRegularOrbitChart

section Subdirect
variable {H V : Type} [Group H] [Group V] [Finite H] [Finite V]

/-- A literal injective group map with a surjective first coordinate is
enough for the three possible orders. No independent-product equality
or vector-space dimension is supplied. -/
theorem subdirect_four_card_cases (f : H →* V × V) (hf : Function.Injective f)
    (honto : Function.Surjective (fun h => (f h).1)) (hV : Nat.card V=4) :
    Nat.card H=4 ∨ Nat.card H=8 ∨ Nat.card H=16 := by
  have hd := Subgroup.card_dvd_of_injective f hf
  rw [Nat.card_prod,hV] at hd
  have hlo := Nat.card_le_card_of_surjective (fun h => (f h).1) honto
  rw [hV] at hlo
  have hd' : Nat.card H∣2^4 := by simpa using hd
  obtain ⟨a,ha,hcard⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hd'
  interval_cases a <;> norm_num at hcard <;> omega

theorem subdirect_pow_two (f : H →* V × V) (hf : Function.Injective f)
    (hV : ∀ v : V,v^2=1) : ∀ h : H,h^2=1 := by
  intro h
  apply hf
  rw [map_pow,map_one]
  apply Prod.ext
  · change (f h).1^2=1
    exact hV _
  · change (f h).2^2=1
    exact hV _

theorem commutative_of_pow_two (hH : ∀ h : H,h^2=1) : ∀ h k : H,h*k=k*h := by
  have hinv : ∀ h : H,h⁻¹=h := fun h =>
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hH h)
  intro h k
  calc
    h*k = (h*k)⁻¹ := (hinv _).symm
    _ = k⁻¹*h⁻¹ := mul_inv_rev _ _
    _ = k*h := by rw [hinv,hinv]

end Subdirect
end SymmetricSubgroupAsymptotics.TransitiveTwoRegularOrbitChart

namespace SymmetricSubgroupAsymptotics

section OriginalAction
variable {G X A : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [MulAction.IsPretransitive G X] [FaithfulSMul G X]
    [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]

/-- The actual normal kernel is elementary abelian and has order 4,8 or
16; the original faithful top has order 8,16 or32. All coordinates come
from its original orbit images and one original outside element. -/
theorem permutationBinary_twoBlockCharacter_top_orders
    (hG : IsPGroup 2 G) (x : X) (hX : Nat.card X=8)
    (ρ : Representation (ZMod 2) G A)
    (M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))
    (q : M.toRepresentation.IntertwiningMap ρ) (hq : Function.Surjective q)
    (hA : Module.finrank (ZMod 2) A=4)
    (data : RepresentationBinaryCommonCharacter.TwoBlockCharacter ρ) :
    (Nat.card G=8 ∨ Nat.card G=16 ∨ Nat.card G=32) ∧
      (Nat.card ρ.ker=4 ∨ Nat.card ρ.ker=8 ∨ Nat.card ρ.ker=16) ∧
      (∀ h : ρ.ker,h^2=1) ∧
      (∀ h k : ρ.ker,h*k=k*h) := by
  obtain ⟨o₁,o₂,hne,hcover,_,_⟩ :=
    permutationBinary_twoBlockCharacter_original_module_eq hG x hX ρ M q hq hA data
  let x₀ : o₁.orbit := ⟨o₁.nonempty_orbit.choose,o₁.nonempty_orbit.choose_spec⟩
  obtain ⟨hV,hsquare,hregular⟩ :=
    permutationBinary_twoBlockCharacter_regular_orbit_images hG x hX ρ M q hq hA data o₁
  obtain ⟨g,hg⟩ := PermutationBinaryTwoOrbitSplit.exists_orbit_translation ρ.ker o₁ o₂
  let f := TransitiveTwoRegularOrbitChart.translationPair ρ.ker o₁ g
  have hf : Function.Injective f :=
    TransitiveTwoRegularOrbitChart.translationPair_injective
      ρ.ker o₁ o₂ x₀ (hregular x₀) g hg hne hcover
  have honto : Function.Surjective (fun h : ρ.ker => (f h).1) :=
    TransitiveTwoRegularOrbitChart.translationPair_fst_surjective ρ.ker o₁ g
  have hH := TransitiveTwoRegularOrbitChart.subdirect_four_card_cases f hf honto hV
  have hsq := TransitiveTwoRegularOrbitChart.subdirect_pow_two f hf hsquare
  have hsource := ρ.ker.card_mul_index
  rw [data.kernel_index] at hsource
  refine ⟨?_,hH,hsq,TransitiveTwoRegularOrbitChart.commutative_of_pow_two hsq⟩
  rcases hH with hH | hH | hH <;> omega

end OriginalAction

namespace BinaryPairFrame
variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U) [N.Normal]

/-- Concrete original residual orders, including the complete original
normal-image guard and an actual target-order escape at top order eight. -/
theorem eight_rank_two_original_orders [Finite X] [Finite I]
    [MulAction.IsPretransitive F.top.range I] (hU : IsPGroup 2 U)
    (hI : Nat.card I=8) (hres : F.EightPairRankTwoResidual N) :
    (Nat.card F.top.range=8 ∨ Nat.card F.top.range=16 ∨ Nat.card F.top.range=32) ∧
      (Nat.card U=512 ∨ Nat.card U=1024 ∨ Nat.card U=2048) ∧
      (Nat.card F.top.range=8 → Nat.card (U ⧸ N)≤128) ∧
      (∀ h : (F.sectionTopRepresentation N).ker,h^2=1) ∧
      N.map F.top.rangeRestrict≤(F.sectionTopRepresentation N).ker := by
  rcases hres with ⟨hd,_,_,⟨data⟩,_,_,hN⟩
  have hnonempty : Nonempty I := (Nat.card_pos_iff.mp (by rw [hI]; decide)).1
  let i : I := Classical.choice hnonempty
  obtain ⟨htop,_,hsquare,_⟩ := permutationBinary_twoBlockCharacter_top_orders
    (F.top_isPGroup hU) i hI (F.sectionTopRepresentation N)
    F.kernelTopPermutationSubrepresentation (F.sectionTopIntertwiner N)
    (F.normalSpace N).mkQ_surjective hd data
  obtain ⟨_,_,_,_,_,hM⟩ := permutationBinary_twoBlockCharacter_original_module_eq
    (F.top_isPGroup hU) i hI (F.sectionTopRepresentation N)
    F.kernelTopPermutationSubrepresentation (F.sectionTopIntertwiner N)
    (F.normalSpace N).mkQ_surjective hd data
  have hker : Nat.card F.top.ker=64 := by
    calc
      Nat.card F.top.ker = Nat.card F.kernelSpace :=
        (Nat.card_congr F.kernelChart.toEquiv).trans (Nat.card_congr Multiplicative.toAdd)
      _ = 2^Module.finrank (ZMod 2) F.kernelSpace := by
        simpa only [Nat.card_zmod] using
          (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.kernelSpace))
      _ = 64 := by change Module.finrank (ZMod 2) F.kernelSpace=6 at hM; rw [hM]; norm_num
  have hsource := F.top.ker.card_mul_index
  rw [Subgroup.index_ker,hker] at hsource
  refine ⟨htop,?_,?_,hsquare,hN⟩
  · rcases htop with ht | ht | ht <;> omega
  · intro ht
    have hbase : Nat.card (U ⧸ (F.top.ker⊔N))≤8 :=
      (Nat.card_le_card_of_surjective (F.sectionTopQuotient N)
        (F.sectionTopQuotient_surjective N)).trans ht.le
    have hA : Nat.card (F.zeroCutBase N).ker=16 := by
      calc
        Nat.card (F.zeroCutBase N).ker = Nat.card (F.kernelSpace ⧸ F.normalSpace N) :=
          (Nat.card_congr (F.sectionKernelEquiv N).symm.toEquiv).trans
            (Nat.card_congr Multiplicative.toAdd)
        _ = 2^Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N) := by
          simpa only [Nat.card_zmod] using
            (Module.natCard_eq_pow_finrank (K := ZMod 2)
              (V := F.kernelSpace ⧸ F.normalSpace N))
        _ = 16 := by rw [hd]; norm_num
    have hindex : (F.zeroCutBase N).ker.index=Nat.card (U ⧸ (F.top.ker⊔N)) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (F.zeroCutBase N)
        (F.zeroCutBase_surjective N)).toEquiv
    have htarget := (F.zeroCutBase N).ker.card_mul_index
    rw [hA,hindex] at htarget
    omega

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
