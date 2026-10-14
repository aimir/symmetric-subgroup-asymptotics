import SymmetricSubgroupAsymptotics.BinaryDiagonalSwapPermutation
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenDiagonalTops
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightAffineSocles

/-! Exact diagonal/swap coordinates for the retained two-affine row2.
Only the short generator bindings are finite checks. Translation closure
uses the already checked Singer orbit, not a table of group elements. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow2SwapTop

open SemidirectProduct
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoPairedEightAffineTops

abbrev R := Row18.linearGroup
abbrev V := Multiplicative Vector
abbrev φ := AffineModel.linAut R
abbrev Model := BinaryDiagonalSwap.Model φ
abbrev Top := DegreeTwoTwoAffineSixteenInterfaces.row2.top

def singerElement : R := ⟨singer, Row18.singer_mem⟩
def linearInr : R →* Model :=
  (inr : R × BinaryDiagonalSwap.Binary →* Model).comp
    (MonoidHom.inl R BinaryDiagonalSwap.Binary)
def firstTranslation : V →* Model :=
  (inl : V × V →* Model).comp (MonoidHom.inl V V)

def localPointChart : Fin 8 ≃ Vector :=
  PrimitiveAffineDegreeTwoTwoAffineSixteenDiagonalTops.Row1.localChart.trans
    pointEquiv.symm

def pointChart : Fin 16 ≃ Vector ⊕ Vector :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr localPointChart localPointChart)

def literalAction : Model →* Equiv.Perm (Fin 16) :=
  pointChart.symm.permCongrHom.toMonoidHom.comp
    (BinaryDiagonalSwap.permutationAction φ (AffineModel.action R))

theorem literalAction_injective : Function.Injective literalAction :=
  pointChart.symm.permCongrHom.injective.comp
    (BinaryDiagonalSwap.permutationAction_injective φ _ (AffineModel.action_injective R))

def vector (n : ℕ) : V := Multiplicative.ofAdd (binaryVectorOfMask 3 n)

def modelGenerators : Fin 11 → Model :=
  ![inl (vector 3, 1), inl (vector 6, 1), inl (vector 1, 1),
    inl (1, vector 3), inl (1, vector 6), inl (1, vector 1),
    inl (vector 1, 1), inl (vector 4, 1), inl (vector 7, 1),
    linearInr singerElement,
    ⟨(vector 7, 1), (singerElement ^ 5, C2Wreath.gen)⟩]

theorem generators_binding (i : Fin 11) :
    literalAction (modelGenerators i) = DegreeTwoTwoAffineSixteenInterfaces.row2Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem linear_singer_binding : literalAction (linearInr singerElement) =
    DegreeTwoTwoAffineSixteenInterfaces.row2Generators 9 := generators_binding 9

theorem first_translation_binding :
    literalAction (firstTranslation (Multiplicative.ofAdd firstVector)) =
      DegreeTwoTwoAffineSixteenInterfaces.row2Generators 2 := generators_binding 2

def swapWord : Equiv.Perm (Fin 16) :=
  DegreeTwoTwoAffineSixteenInterfaces.row2Generators 9 ^ 2 *
    DegreeTwoTwoAffineSixteenInterfaces.row2Generators 8 *
    DegreeTwoTwoAffineSixteenInterfaces.row2Generators 10

theorem swap_binding : literalAction (inr (1, C2Wreath.gen)) = swapWord := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

private theorem first_conjugate (r : R) (v : V) :
    linearInr r * firstTranslation v * (linearInr r)⁻¹ =
      firstTranslation (φ r v) := by
  change (inr (r, 1) : Model) * inl (v, 1) * (inr (r, 1))⁻¹ = _
  rw [BinaryDiagonalSwap.conj_inl, right_inr, BinaryDiagonalSwap.action_one, map_one]
  rfl

theorem action_range : literalAction.range = Top := by
  let K : Subgroup Model := Top.comap literalAction
  have hg (i : Fin 11) : DegreeTwoTwoAffineSixteenInterfaces.row2Generators i ∈ Top :=
    Subgroup.subset_closure (Set.mem_range_self i)
  have hs : linearInr singerElement ∈ K := by
    change literalAction (linearInr singerElement) ∈ Top
    rw [linear_singer_binding]
    exact hg 9
  have ht : firstTranslation (Multiplicative.ofAdd firstVector) ∈ K := by
    change literalAction (firstTranslation (Multiplicative.ofAdd firstVector)) ∈ Top
    rw [first_translation_binding]
    exact hg 2
  have hswap : (inr (1, C2Wreath.gen) : Model) ∈ K := by
    change literalAction (inr (1, C2Wreath.gen)) ∈ Top
    rw [swap_binding]
    exact Top.mul_mem (Top.mul_mem (Top.pow_mem (hg 9) 2) (hg 8)) (hg 10)
  have hlinear (r : R) : linearInr r ∈ K := by
    have hr : r.1 ∈ Subgroup.zpowers singer := by
      rw [← Row18.linearGroup_eq_zpowers]
      exact r.2
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hr
    have heq : singerElement ^ z = r := Subtype.ext hz
    rw [← heq, map_zpow]
    exact K.zpow_mem hs z
  have hfirst (v : V) : firstTranslation v ∈ K := by
    by_cases hv : Multiplicative.toAdd v = 0
    · have heq : v = 1 := Multiplicative.toAdd.injective hv
      rw [heq, map_one]
      exact K.one_mem
    obtain ⟨i, hi⟩ := singer_nonzero_orbit firstVector (Multiplicative.toAdd v)
      firstVector_ne_zero hv
    have hc := K.mul_mem (K.mul_mem (hlinear (singerElement ^ i.val)) ht)
      (K.inv_mem (hlinear (singerElement ^ i.val)))
    rw [first_conjugate] at hc
    have heq : φ (singerElement ^ i.val) (Multiplicative.ofAdd firstVector) = v := by
      apply Multiplicative.toAdd.injective
      exact hi
    exact heq ▸ hc
  have hsecond (v : V) : (inl (1, v) : Model) ∈ K := by
    have hc := K.mul_mem (K.mul_mem hswap (hfirst v)) (K.inv_mem hswap)
    change (inr (1, C2Wreath.gen) : Model) * inl (v, 1) *
      (inr (1, C2Wreath.gen))⁻¹ ∈ K at hc
    rw [BinaryDiagonalSwap.conj_inl, right_inr, BinaryDiagonalSwap.action_swap,
      map_one] at hc
    exact hc
  have htranslations (v : V × V) : (inl v : Model) ∈ K := by
    have h := K.mul_mem (hfirst v.1) (hsecond v.2)
    change (inl (v.1, 1) : Model) * inl (1, v.2) ∈ K at h
    rw [← map_mul] at h
    simpa only [Prod.mk_mul_mk, mul_one, one_mul, Prod.eta] using h
  have hcomplement (r : R × BinaryDiagonalSwap.Binary) : (inr r : Model) ∈ K := by
    rcases r with ⟨r, c⟩
    rcases C2Wreath.cases c with rfl | rfl
    · exact hlinear r
    · have h := K.mul_mem (hlinear r) hswap
      change (inr (r, 1) : Model) * inr (1, C2Wreath.gen) ∈ K at h
      rw [← map_mul] at h
      simpa only [Prod.mk_mul_mk, mul_one, one_mul] using h
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    change g ∈ K
    rw [← inl_left_mul_inr_right g]
    exact K.mul_mem (htranslations g.left) (hcomplement g.right)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨modelGenerators i, generators_binding i⟩

/-- Exact equivalence to the original retained row2 top. -/
def modelEquiv : Model ≃* Top :=
  (MonoidHom.ofInjective (f := literalAction) literalAction_injective).trans
    (MulEquiv.subgroupCongr action_range)

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow2SwapTop
end SymmetricSubgroupAsymptotics

end
