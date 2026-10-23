import SymmetricSubgroupAsymptotics.CFSGHermitianMaximalExchange
import Mathlib.LinearAlgebra.Dual.Basis

/-! A nondegenerate subspace of a finite Hermitian space has its actual
orthogonal complement. The restricted duality is constructed from the
pairing and proved surjective using a basis and finiteness; no Witt
decomposition or extension theorem is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGFiniteHermitianNondegenerateComplement
open CFSGTwistedAUnitaryParameters CFSGHermitianOrthogonalSpan
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

def restrictedDual (W : Submodule K (I → K)) : W →+ Module.Dual K W where
  toFun x := (pairRightLinear sigma H x.val).comp W.subtype
  map_zero' := by
    apply LinearMap.ext
    intro y
    exact pair_zero_left sigma H y.val
  map_add' x y := by
    apply LinearMap.ext
    intro z
    exact hermitianPair_add_left sigma H x.val y.val z.val

theorem restrictedDual_injective (W : Submodule K (I → K))
    (hND : ∀ x ∈ W, (∀ y ∈ W, hermitianPair sigma H x y = 0) → x = 0) :
    Function.Injective (restrictedDual sigma H W) := by
  intro x y he
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply hND _ (x - y).property
  intro z hz
  have hh : restrictedDual sigma H W (x - y) = 0 := by
    rw [map_sub, he, sub_self]
  exact congrArg (fun L : Module.Dual K W => L ⟨z,hz⟩) hh

theorem restrictedDual_surjective [Finite K] (W : Submodule K (I → K))
    (hND : ∀ x ∈ W, (∀ y ∈ W, hermitianPair sigma H x y = 0) → x = 0) :
    Function.Surjective (restrictedDual sigma H W) := by
  let E := (Module.finBasis K W).toDualEquiv
  have hs : Function.Surjective (fun x => E.symm (restrictedDual sigma H W x)) :=
    Finite.surjective_of_injective
      (E.symm.injective.comp (restrictedDual_injective sigma H W hND))
  intro L
  obtain ⟨x,hx⟩ := hs (E.symm L)
  exact ⟨x,E.symm.injective hx⟩

theorem exists_orthogonal_remainder [Finite K] (W : Submodule K (I → K))
    (hND : ∀ x ∈ W, (∀ y ∈ W, hermitianPair sigma H x y = 0) → x = 0)
    (hswap : ∀ x y, hermitianPair sigma H x y = 0 ↔ hermitianPair sigma H y x = 0)
    (v : I → K) : ∃ w ∈ W, v - w ∈ rightPerp sigma H W := by
  obtain ⟨w,hw⟩ := restrictedDual_surjective sigma H W hND
    ((pairRightLinear sigma H v).comp W.subtype)
  refine ⟨w.val,w.property,?_⟩
  intro z hz
  apply (hswap (v - w.val) z).mp
  have he := congrArg (fun L : Module.Dual K W => L ⟨z,hz⟩) hw
  change hermitianPair sigma H w.val z = hermitianPair sigma H v z at he
  have hh := hermitianPair_add_left sigma H (v - w.val) w.val z
  rw [sub_add_cancel,he] at hh
  exact (add_eq_right.mp hh.symm)

theorem disjoint_rightPerp (W : Submodule K (I → K))
    (hND : ∀ x ∈ W, (∀ y ∈ W, hermitianPair sigma H x y = 0) → x = 0)
    (hswap : ∀ x y, hermitianPair sigma H x y = 0 ↔ hermitianPair sigma H y x = 0) :
    Disjoint W (rightPerp sigma H W) := by
  apply disjoint_iff.mpr
  apply le_antisymm
  · intro x hx
    change x = 0
    exact hND x hx.1 (fun y hy => (hswap y x).mp (hx.2 y hy))
  · exact bot_le

theorem isCompl_rightPerp [Finite K] (W : Submodule K (I → K))
    (hND : ∀ x ∈ W, (∀ y ∈ W, hermitianPair sigma H x y = 0) → x = 0)
    (hswap : ∀ x y, hermitianPair sigma H x y = 0 ↔ hermitianPair sigma H y x = 0) :
    IsCompl W (rightPerp sigma H W) := by
  apply IsCompl.of_eq (disjoint_rightPerp sigma H W hND hswap).eq_bot
  apply top_unique
  intro v _
  obtain ⟨w,hw,hr⟩ := exists_orthogonal_remainder sigma H W hND hswap v
  apply Submodule.mem_sup.mpr
  exact ⟨w,hw,v-w,hr,(add_comm w (v-w)).trans (sub_add_cancel v w)⟩

theorem finrank_add_rightPerp [Finite K] (W : Submodule K (I → K))
    (hND : ∀ x ∈ W, (∀ y ∈ W, hermitianPair sigma H x y = 0) → x = 0)
    (hswap : ∀ x y, hermitianPair sigma H x y = 0 ↔ hermitianPair sigma H y x = 0) :
    Module.finrank K W + Module.finrank K (rightPerp sigma H W) = Fintype.card I := by
  simpa only [Module.finrank_pi] using
    (Submodule.finrank_add_eq_of_isCompl (isCompl_rightPerp sigma H W hND hswap))

end SymmetricSubgroupAsymptotics.CFSGFiniteHermitianNondegenerateComplement
