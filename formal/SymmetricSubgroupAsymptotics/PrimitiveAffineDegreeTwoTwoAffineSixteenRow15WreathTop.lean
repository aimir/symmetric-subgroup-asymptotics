import SymmetricSubgroupAsymptotics.C2WreathGeneration
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop

/-! The original row15 is the wreath product of the checked local affine
group. Only the literal sixteen-point generator identities are finite. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow15WreathTop

open SemidirectProduct
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoPairedEightAffineTops

abbrev R := Row20.linearGroup
abbrev Local := AffineModel.Aff R
abbrev Model := C2Wreath.W Local
abbrev Top := DegreeTwoTwoAffineSixteenInterfaces.row15.top

def first : Local →* Model := C2Wreath.firstFactor
def second : Local →* Model := (inl : Local × Local →* Model).comp (MonoidHom.inr _ _)

def pointChart : Fin 16 ≃ Vector ⊕ Vector :=
  PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop.pointChart

def literalAction : Model →* Equiv.Perm (Fin 16) :=
  pointChart.symm.permCongrHom.toMonoidHom.comp (C2Wreath.action (AffineModel.action R))

theorem literalAction_injective : Function.Injective literalAction :=
  pointChart.symm.permCongrHom.injective.comp
    (C2Wreath.action_injective _ (AffineModel.action_injective R))

def translation (n : ℕ) : Local := inl (Multiplicative.ofAdd (binaryVectorOfMask 3 n))
def transvection : Local :=
  inr PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop.transvection
def coordinateRotation : Local :=
  inr PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop.coordinateRotation

def modelGenerators : Fin 16 → Model :=
  ![first (translation 1), first (translation 2), first (translation 4),
    first transvection, first coordinateRotation,
    second (translation 1), second (translation 2), second (translation 4),
    second transvection, second coordinateRotation,
    first (translation 1), first (translation 2), first (translation 4),
    first transvection, first coordinateRotation,
    first (translation 7) * inr C2Wreath.gen]

theorem generators_binding (i : Fin 16) :
    literalAction (modelGenerators i) = DegreeTwoTwoAffineSixteenInterfaces.row15Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def literalSinger : Equiv.Perm (Fin 16) :=
  DegreeTwoTwoAffineSixteenInterfaces.row15Generators 3 *
    DegreeTwoTwoAffineSixteenInterfaces.row15Generators 4 ^ 2

def literalSwap : Equiv.Perm (Fin 16) :=
  (literalSinger ^ 4)⁻¹ * DegreeTwoTwoAffineSixteenInterfaces.row15Generators 3 *
    literalSinger ^ 4

theorem linear_generator_words (i : Fin 2) :
    literalAction (first (inr
      (⟨Row20.linearGenerators i, Subgroup.subset_closure (Set.mem_range_self i)⟩ : R))) =
        ![literalSinger, literalSwap] i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def swapWord : Equiv.Perm (Fin 16) :=
  DegreeTwoTwoAffineSixteenInterfaces.row15Generators 0 *
    DegreeTwoTwoAffineSixteenInterfaces.row15Generators 1 *
    DegreeTwoTwoAffineSixteenInterfaces.row15Generators 2 *
    DegreeTwoTwoAffineSixteenInterfaces.row15Generators 15

theorem swap_binding : literalAction (inr C2Wreath.gen) = swapWord := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

private theorem local_mem_of_generators (K : Subgroup Model)
    (hlinear : ∀ r : R, first (inr r) ∈ K)
    (ht : first (inl (Multiplicative.ofAdd firstVector)) ∈ K)
    (g : Local) : first g ∈ K := by
  let s : R := ⟨singer, Row20.singer_mem⟩
  have htranslations (v : Multiplicative Vector) : first (inl v) ∈ K := by
    by_cases hv : v.toAdd = 0
    · have heq : v = 1 := Multiplicative.toAdd.injective hv
      rw [heq, map_one, map_one]
      exact K.one_mem
    obtain ⟨i, hi⟩ := singer_nonzero_orbit firstVector v.toAdd firstVector_ne_zero hv
    have h := K.mul_mem (K.mul_mem (hlinear (s ^ i.val)) ht)
      (K.inv_mem (hlinear (s ^ i.val)))
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← inl_aut] at h
    have heq : AffineModel.linAut R (s ^ i.val) (Multiplicative.ofAdd firstVector) = v := by
      apply Multiplicative.toAdd.injective
      exact hi
    exact heq ▸ h
  rw [← inl_left_mul_inr_right g, map_mul]
  exact K.mul_mem (htranslations g.left) (hlinear g.right)

theorem action_range : literalAction.range = Top := by
  let K : Subgroup Model := Top.comap literalAction
  have hg (i : Fin 16) : DegreeTwoTwoAffineSixteenInterfaces.row15Generators i ∈ Top :=
    Subgroup.subset_closure (Set.mem_range_self i)
  have hs : literalSinger ∈ Top := Top.mul_mem (hg 3) (Top.pow_mem (hg 4) 2)
  have hb : literalSwap ∈ Top :=
    Top.mul_mem (Top.mul_mem (Top.inv_mem (Top.pow_mem hs 4)) (hg 3)) (Top.pow_mem hs 4)
  have hlinear (r : R) : first (inr r) ∈ K := by
    apply BinaryDiagonalSwap.hom_mem_of_closure_generators Row20.linearGenerators
      (literalAction.comp (first.comp (inr : R →* Local))) Top _ r
    intro i
    change literalAction (first (inr _)) ∈ Top
    rw [linear_generator_words]
    fin_cases i
    · exact hs
    · exact hb
  have ht : first (inl (Multiplicative.ofAdd firstVector)) ∈ K := by
    change literalAction (modelGenerators 0) ∈ Top
    rw [generators_binding]
    exact hg 0
  have hswap : (inr C2Wreath.gen : Model) ∈ K := by
    change literalAction (inr C2Wreath.gen) ∈ Top
    rw [swap_binding]
    exact Top.mul_mem (Top.mul_mem (Top.mul_mem (hg 0) (hg 1)) (hg 2)) (hg 15)
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact C2Wreath.mem_of_first_and_swap K (local_mem_of_generators K hlinear ht) hswap g
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨modelGenerators i, generators_binding i⟩

def modelEquiv : Model ≃* Top :=
  (MonoidHom.ofInjective (f := literalAction) literalAction_injective).trans
    (MulEquiv.subgroupCongr action_range)

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow15WreathTop
end SymmetricSubgroupAsymptotics

end
