import SymmetricSubgroupAsymptotics.BlockKernelFullCoordinates
import SymmetricSubgroupAsymptotics.DegreeSixTernaryBlockOwner
import SymmetricSubgroupAsymptotics.PrimitiveTernaryStrictHeadPublished
import SymmetricSubgroupAsymptotics.RelativeAmbientSubgroup

/-!
# The nine-by-two degree-eighteen head bound

For two blocks of size nine the faithful transitive top is regular of order
two.  Hence the literal block kernel projects onto the exact primitive
degree-nine component in both coordinates.  The relative coordinate theorem
then bounds every normal block-kernel core by two primitive heads, each at
most one.  The top contributes no ternary head.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω]
variable [Finite A] [Finite Ω] [MulAction.IsPretransitive A Ω]
variable [FaithfulSMul A Ω]
variable {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

include D in
omit [FaithfulSMul A Ω] in
/-- The faithful degree-two top action is free. -/
theorem twoBlock_top_free
    (hPoints : Nat.card D.Points = 2)
    (q : D.Top) (x : D.Points) (hfix : q • x = x) : q = 1 := by
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : Finite D.Top := D.top_finite
  let S := MulAction.stabilizer D.Top x
  have hTop : Nat.card D.Top = 2 := D.twoBlock_top_card hPoints
  have hindex : S.index = 2 := by
    simpa only [S, hPoints] using
      MulAction.index_stabilizer_of_transitive D.Top x
  have hcard : Nat.card S = 1 := by
    have hmul := S.card_mul_index
    rw [hindex, hTop] at hmul
    omega
  letI : Subsingleton S := (Nat.card_eq_one_iff_unique.mp hcard).1
  let qs : S := ⟨q, hfix⟩
  have hq : qs = 1 := Subsingleton.elim _ _
  exact congrArg (fun z : S => (z : D.Top)) hq

include D in
/-- Every normal pair in an actual nine-by-two minimal block system has
ternary relative head at most two. -/
theorem degreeEighteen_nineByTwo_ternaryHead_le_two
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (N : Subgroup A) [N.Normal]
    (hFibre : Nat.card D.Fibre = 9)
    (hPoints : Nat.card D.Points = 2) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤ 2 := by
  letI : Nontrivial D.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hFibre]; norm_num)
  letI : Finite D.Component :=
    Finite.of_surjective
      (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict
      (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective
  letI : MulAction.IsPreprimitive D.Component D.Fibre := D.component_preprimitive
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : Finite D.Top := D.top_finite
  let K := BlockKernelFullCoordinates.Kernel D.map D.map_equivariant D.base
  letI : K.Normal := inferInstance
  let eX : D.Points ≃ Fin 2 := Finite.equivFinOfCardEq hPoints
  let ρ : ∀ _ : Fin 2, K →* D.Component := fun i =>
    BlockKernelFullCoordinates.coordinate D.map D.map_equivariant D.base (eX.symm i)
  have hfree : ∀ (q : D.Top) (x : D.Points), q • x = x → q = 1 :=
    fun q x h => D.twoBlock_top_free hPoints q x h
  have honto : ∀ i, Function.Surjective (ρ i) := by
    intro i
    exact BlockKernelFullCoordinates.coordinate_surjective_of_free
      D.map D.map_equivariant D.base hfree (eX.symm i)
  have hfaithful : Function.Injective (fun k : K => fun i => ρ i k) := by
    intro k l hkl
    apply BlockKernelFullCoordinates.coordinates_injective
      D.map D.map_equivariant D.base
    funext x
    have h := congrFun hkl (eX x)
    simpa only [ρ, eX, Equiv.symm_apply_apply] using h
  have hcomponent : ∀ (_i : Fin 2) (M : Subgroup D.Component) (hM : M.Normal),
      letI := hM
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 M) ≤ 1 := by
    intro i M hM
    letI : M.Normal := hM
    have hstrict := hPrimitive D.Component D.Fibre
      (by omega) (by omega) (by omega) M
    rw [hFibre] at hstrict
    omega
  have hK : K = D.topMap.ker :=
    BlockKernelFullCoordinates.kernel_eq_topMap_ker
      D.map D.map_equivariant D.base
  let K₀ : Subgroup A := D.topMap.ker
  letI : K₀.Normal := inferInstance
  let eK : K₀ ≃* K := MulEquiv.subgroupCongr hK.symm
  let ρ₀ : ∀ _ : Fin 2, K₀ →* D.Component := fun i =>
    (ρ i).comp eK.toMonoidHom
  have honto₀ : ∀ i, Function.Surjective (ρ₀ i) := by
    intro i d
    obtain ⟨k, hk⟩ := honto i d
    obtain ⟨k₀, rfl⟩ := eK.surjective k
    exact ⟨k₀, hk⟩
  have hfaithful₀ : Function.Injective (fun k : K₀ => fun i => ρ₀ i k) := by
    intro k l hkl
    apply eK.injective
    apply hfaithful
    exact hkl
  let P₀ : Subgroup K₀ := N.subgroupOf K₀
  letI : P₀.Normal := subgroupOf_normal N K₀
  have hP₀ : Module.finrank (ZMod 3) (primeRelativeCharacters 3 P₀) ≤ 2 := by
    have h := primeRelativeHead_faithful_family_le 3 2
      (fun _ : Fin 2 => D.Component) ρ₀ honto₀ hfaithful₀
      (fun _ => 1) hcomponent P₀
    simpa using h
  have hIntersection₀ : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (N ⊓ K₀)) ≤ 2 :=
    (primeRelativeHead_inf_le_subgroupOf 3 N K₀).trans hP₀
  let T := originalNormalRange D.topMap N
  letI : T.Normal := originalNormalRange_normal D.topMap N
  have hTopCard : Nat.card D.Top = 2 := D.twoBlock_top_card hPoints
  have hTopPGroup : IsPGroup 2 D.Top :=
    IsPGroup.of_card (n := 1) (by simpa using hTopCard)
  have hTzero : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 T) = 0 :=
    primeRelativeHead_power_group 3 T 2 (by decide) (hTopPGroup.to_subgroup T)
  have hchain := primeRelativeHead_chain_le (N ⊓ K₀) N 3 inf_le_left
  rw [primeRelativeHead_second_isomorphism 3 N K₀] at hchain
  change Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 (N ⊓ K₀)) +
        Module.finrank (ZMod 3)
          (primeRelativeCharacters 3
            (normalChainQuotient D.topMap.ker N)) at hchain
  rw [primeRelativeHead_original_range 3 D.topMap N, hTzero] at hchain
  exact hchain.trans (by simpa using hIntersection₀)

end OriginalMinimalBlock
end SymmetricSubgroupAsymptotics

end
