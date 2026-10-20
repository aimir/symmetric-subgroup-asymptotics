import SymmetricSubgroupAsymptotics.TwistedBinaryAffineGeneration
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow19AffineTop
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow20AffineSocleClosure
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop
import SymmetricSubgroupAsymptotics.DiagonalBinaryPermutationProduct

/-! Three literal pairing graphs share the same affine bound. Every finite
identity below concerns only three-bit coordinates or the fixed two-block
projection operator; no group or invariant-subgroup table is used. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwistedSingerModels

open SemidirectProduct
open PrimitiveAffineDegreeTwoPairedEightAffineTops
open PairedFormSwapAffine

abbrev V := Multiplicative Vector

def form7 (x y : V) : ZMod 2 :=
  x.toAdd 0 * (y.toAdd 1 + y.toAdd 2) +
  x.toAdd 1 * (y.toAdd 0 + y.toAdd 1 + y.toAdd 2) +
  x.toAdd 2 * (y.toAdd 0 + y.toAdd 1)

def form168 (x y : V) : ZMod 2 :=
  x.toAdd 0 * y.toAdd 2 + x.toAdd 1 * y.toAdd 1 + x.toAdd 2 * y.toAdd 0

theorem form7_symmetric : ∀ x y, form7 x y = form7 y x := by decide +kernel
theorem form7_separates : ∀ u v : V, (∀ x, form7 x u = form7 x v) → u = v := by
  decide +kernel
theorem form168_symmetric : ∀ x y, form168 x y = form168 y x := by decide +kernel
theorem form168_separates : ∀ u v : V, (∀ x, form168 x u = form168 x v) → u = v := by
  decide +kernel

private theorem local_normal_generators {G : Type} [Group G] [Finite G]
    (R : Subgroup LinearGroup) (e : G ≃* AffineModel.Aff R)
    (htotal : ∀ A B : Subgroup G, A.Normal → B.Normal → A ≤ B ∨ B ≤ A) :
    ∀ N : Subgroup R, N.Normal →
      ∃ x : Fin 1 → R, Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective
    ((rightHom : AffineModel.Aff R →* R).comp e.toMonoidHom)
    (rightHom_surjective.comp e.surjective)
    (normal_generating_singletons_of_finite_normal_total htotal)

namespace Row3

abbrev R := Row18.linearGroup
abbrev φ := AffineModel.linAut R
abbrev Pair := Graph φ form7
abbrev Complement := PairedFormSwapAffine.Complement φ form7 form7_symmetric
abbrev Model := PairedFormSwapAffine.Model φ form7 form7_symmetric

def s : R := ⟨singer, Row18.singer_mem⟩
def singerPair : Pair := ⟨(s, s⁻¹), by
  change ∀ x y : V, form7 (φ s x) (φ s⁻¹ y) = form7 x y
  decide +kernel⟩
def pairs : Fin 1 → Pair := fun _ ↦ singerPair

theorem pairs_first (i : Fin 1) : (pairs i).val.1 =
    (⟨Row18.linearGenerators i, Subgroup.subset_closure (Set.mem_range_self i)⟩ : R) := rfl

theorem first_surjective : Function.Surjective
    (PairedFormSwapComplement.first (localAction φ) form7) :=
  graph_first_surjective_of_generators Row18.linearGenerators form7 pairs pairs_first

theorem singerPair_first : singerPair.val.1.val = singer := rfl

theorem projection_identity : ∀ v : V × V,
    action φ form7 form7_symmetric ((inl singerPair : Complement) ^ 4) v *
      action φ form7 form7_symmetric ((inl singerPair : Complement) ^ 2) v *
      action φ form7 form7_symmetric (inl singerPair) v = (1, v.2) := by
  decide +kernel

theorem normal_generators : ∀ N : Subgroup Model, N.Normal →
    ∃ x : Fin 2 → Model, Subgroup.normalClosure (Set.range x) = N :=
  PairedFormSwapAffine.normal_generating_tuples φ form7 form7_symmetric
    (BinaryDiagonalSwap.affine_linAut_injective R) form7_separates first_surjective
    (BinaryDiagonalSwap.affine_irreducible R Row18.irreducible)
    (inl singerPair) projection_identity
    (local_normal_generators R Row18.modelEquiv
      (DiagonalBinaryPermutationProduct.normal_total_of_three_chain Row18.normalChain))

end Row3

namespace Row7

abbrev R := PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.linearGroup
abbrev φ := AffineModel.linAut R
abbrev Pair := Graph φ form7
abbrev Complement := PairedFormSwapAffine.Complement φ form7 form7_symmetric
abbrev Model := PairedFormSwapAffine.Model φ form7 form7_symmetric

def s : R := ⟨singer, PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.singer_mem⟩
def f : R := ⟨PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.frobenius,
  PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.frobenius_mem⟩
def singerPair : Pair := ⟨(s, s⁻¹), by
  change ∀ x y : V, form7 (φ s x) (φ s⁻¹ y) = form7 x y
  decide +kernel⟩
def frobeniusPair : Pair := ⟨(f, s ^ 4 * f), by
  change ∀ x y : V, form7 (φ f x) (φ (s ^ 4 * f) y) = form7 x y
  decide +kernel⟩
def pairs : Fin 2 → Pair := ![singerPair, frobeniusPair]

theorem pairs_first (i : Fin 2) : (pairs i).val.1 =
    (⟨PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.linearGenerators i,
      Subgroup.subset_closure (Set.mem_range_self i)⟩ : R) := by
  fin_cases i <;> rfl

theorem first_surjective : Function.Surjective
    (PairedFormSwapComplement.first (localAction φ) form7) :=
  graph_first_surjective_of_generators
    PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.linearGenerators form7 pairs pairs_first

theorem singerPair_first : singerPair.val.1.val = singer := rfl

theorem projection_identity : ∀ v : V × V,
    action φ form7 form7_symmetric ((inl singerPair : Complement) ^ 4) v *
      action φ form7 form7_symmetric ((inl singerPair : Complement) ^ 2) v *
      action φ form7 form7_symmetric (inl singerPair) v = (1, v.2) := by
  decide +kernel

theorem normal_generators : ∀ N : Subgroup Model, N.Normal →
    ∃ x : Fin 2 → Model, Subgroup.normalClosure (Set.range x) = N :=
  PairedFormSwapAffine.normal_generating_tuples φ form7 form7_symmetric
    (BinaryDiagonalSwap.affine_linAut_injective R) form7_separates first_surjective
    (BinaryDiagonalSwap.affine_irreducible R
      PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.irreducible)
    (inl singerPair) projection_identity
    (local_normal_generators R PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.modelEquiv
      PrimitiveAffineDegreeTwoPairedEightRow19NormalChain.top_normal_total)

end Row7

namespace Row14

abbrev R := Row20.linearGroup
abbrev φ := AffineModel.linAut R
abbrev Pair := Graph φ form168
abbrev Complement := PairedFormSwapAffine.Complement φ form168 form168_symmetric
abbrev Model := PairedFormSwapAffine.Model φ form168 form168_symmetric

def transvectionLinear : LinearGroup where
  toFun v := ![v 0, v 1 + v 2, v 2]
  invFun v := ![v 0, v 1 + v 2, v 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def rotationLinear : LinearGroup where
  toFun v := ![v 2, v 0, v 1]
  invFun v := ![v 1, v 2, v 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

theorem transvectionLinear_eq_word : transvectionLinear =
    PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop.transvection.val := by
  apply LinearEquiv.ext
  intro v
  revert v
  decide +kernel

theorem rotationLinear_eq_word : rotationLinear =
    PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop.coordinateRotation.val := by
  apply LinearEquiv.ext
  intro v
  revert v
  decide +kernel

def t : R := ⟨transvectionLinear, by
  rw [transvectionLinear_eq_word]
  exact PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop.transvection.property⟩
def r : R := ⟨rotationLinear, by
  rw [rotationLinear_eq_word]
  exact PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop.coordinateRotation.property⟩
def transvectionPair : Pair := ⟨(t, r ^ 2 * t * r), by
  change ∀ x y : V, form168 (φ t x) (φ (r ^ 2 * t * r) y) = form168 x y
  decide +kernel⟩
def rotationPair : Pair := ⟨(r, r⁻¹), by
  change ∀ x y : V, form168 (φ r x) (φ r⁻¹ y) = form168 x y
  decide +kernel⟩
def singerPair : Pair := transvectionPair * rotationPair ^ 2
def swapPair : Pair := (singerPair ^ 4)⁻¹ * transvectionPair * singerPair ^ 4
def pairs : Fin 2 → Pair := ![singerPair, swapPair]

theorem pairs_first (i : Fin 2) : (pairs i).val.1 =
    (⟨Row20.linearGenerators i, Subgroup.subset_closure (Set.mem_range_self i)⟩ : R) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  revert i v
  decide +kernel

theorem first_surjective : Function.Surjective
    (PairedFormSwapComplement.first (localAction φ) form168) :=
  graph_first_surjective_of_generators Row20.linearGenerators form168 pairs pairs_first

theorem singerPair_first : singerPair.val.1.val = singer := by
  apply LinearEquiv.ext
  intro v
  revert v
  decide +kernel

theorem projection_identity : ∀ v : V × V,
    action φ form168 form168_symmetric ((inl singerPair : Complement) ^ 4) v *
      action φ form168 form168_symmetric ((inl singerPair : Complement) ^ 2) v *
      action φ form168 form168_symmetric (inl singerPair) v = (1, v.2) := by
  decide +kernel

theorem normal_generators : ∀ N : Subgroup Model, N.Normal →
    ∃ x : Fin 2 → Model, Subgroup.normalClosure (Set.range x) = N :=
  PairedFormSwapAffine.normal_generating_tuples φ form168 form168_symmetric
    (BinaryDiagonalSwap.affine_linAut_injective R) form168_separates first_surjective
    (BinaryDiagonalSwap.affine_irreducible R Row20.irreducible)
    (inl singerPair) projection_identity
    (local_normal_generators R Row20.modelEquiv
      (DiagonalBinaryPermutationProduct.normal_total_of_three_chain Row20.normalChain))

end Row14
end PrimitiveAffineDegreeTwoTwistedSingerModels
end SymmetricSubgroupAsymptotics

end
