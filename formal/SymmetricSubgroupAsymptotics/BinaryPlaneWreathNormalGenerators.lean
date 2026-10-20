import SymmetricSubgroupAsymptotics.BinaryPlaneWreathIrreducible
import SymmetricSubgroupAsymptotics.TernaryPermutationWreathEmbedding
import SymmetricSubgroupAsymptotics.IrreducibleAbelianSemidirectSubgroup

/-! The local binary linear group acts faithfully on the three nonzero
vectors. Its wreath therefore inherits actual-image normal bounds from
the literal three-point wreath. An irreducible retained binary translation
kernel adds no position to a positive bound on that actual image. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneWreathNormalGenerators

open BinaryPlanePermutationAffineEquiv
open BinaryPlaneWreathIrreducible

abbrev Nonzero := {v : Plane // v ≠ 0}

def nonzeroChart : Fin 3 ≃ Nonzero where
  toFun i := ⟨![![1,0],![0,1],![1,1]] i,by revert i; decide +kernel⟩
  invFun v := if v.val 0 = 0 then 1 else if v.val 1 = 0 then 0 else 2
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def nonzeroAction : Linear →* Equiv.Perm Nonzero where
  toFun L :=
    { toFun v := ⟨L v,fun h => v.property (L.injective (h.trans (map_zero L).symm))⟩
      invFun v := ⟨L.symm v,fun h => v.property (L.symm.injective (h.trans (map_zero L.symm).symm))⟩
      left_inv v := Subtype.ext (L.symm_apply_apply v)
      right_inv v := Subtype.ext (L.apply_symm_apply v) }
  map_one' := by apply Equiv.ext; intro v; apply Subtype.ext; rfl
  map_mul' _ _ := by apply Equiv.ext; intro v; apply Subtype.ext; rfl

def toThree : Linear →* Equiv.Perm (Fin 3) :=
  nonzeroChart.symm.permCongrHom.toMonoidHom.comp nonzeroAction

theorem toThree_injective : Function.Injective toThree := by
  intro L M h
  have hn : nonzeroAction L = nonzeroAction M := nonzeroChart.symm.permCongrHom.injective h
  apply LinearEquiv.ext
  intro v
  by_cases hv : v = 0
  · simp only [hv,map_zero]
  · exact congrArg (fun f : Equiv.Perm Nonzero => (f ⟨v,hv⟩).val) hn

variable {R I : Type} [Group R] [MulAction R I] [Fintype I] [DecidableEq I]

def wreathMap : W (R := R) (I := I) →*
    TernaryPermutationWreathEmbedding.W (R := R) (I := I) where
  toFun g := ⟨fun i => toThree (g.left i),g.right⟩
  map_one' := by
    apply PermutationalWreathProduct.ext
    · funext i; exact toThree.map_one
    · rfl
  map_mul' g h := by
    apply PermutationalWreathProduct.ext
    · funext i; exact toThree.map_mul _ _
    · rfl

theorem wreathMap_injective : Function.Injective (wreathMap (R := R) (I := I)) := by
  intro g h he
  apply PermutationalWreathProduct.ext
  · funext i
    exact toThree_injective (congrArg (fun z : TernaryPermutationWreathEmbedding.W
      (R := R) (I := I) => z.left i) he)
  · exact congrArg (fun z : TernaryPermutationWreathEmbedding.W
      (R := R) (I := I) => z.right) he

variable [Finite R]

instance : Finite (W (R := R) (I := I)) := Finite.of_injective wreathMap wreathMap_injective

theorem normal_generating_tuples (C : Subgroup (W (R := R) (I := I)))
    (hsurj : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := R) (I := I) →* R).comp C.subtype))
    (c : R) (i : I) (hcycle : ∀ j : I, ∃ n : ℕ, c^n • i = j)
    (a : ℕ) (ha : ∀ N : Subgroup R, N.Normal → MarkedC4.normalGen N ≤ a) :
    ∀ N : Subgroup C, N.Normal →
      ∃ x : Fin (2+a) → C, Subgroup.normalClosure (Set.range x) = N := by
  let f := (wreathMap (R := R) (I := I)).comp C.subtype
  let J := f.range
  let e : C ≃* J := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h => (wreathMap_injective.comp Subtype.val_injective)
      (congrArg Subtype.val h),f.rangeRestrict_surjective⟩
  have hb : Function.Surjective
      ((PermutationalWreathProduct.rightHom :
        TernaryPermutationWreathEmbedding.W (R := R) (I := I) →* R).comp J.subtype) := by
    intro r
    obtain ⟨g,hg⟩ := hsurj r
    exact ⟨f.rangeRestrict g,hg⟩
  exact normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective
    (TernaryPermutationWreathEmbedding.normal_generating_tuples J hb c i hcycle a ha)

abbrev Model := PermutationalWreathAffineCoordinates.Model (R := R) (I := I) localAction
abbrev actualImage (K : Subgroup (Model (R := R) (I := I))) :=
  IrreducibleAbelianSemidirectSubgroup.Image action K

theorem affine_normal_generating_tuples [Nonempty I] [FaithfulSMul R I]
    (K : Subgroup (Model (R := R) (I := I)))
    (hloc : ∀ i : I, localEmbedding i singer ∈ actualImage K)
    (htrans : ∀ i j : I, ∃ g : actualImage K,
      (g : W (R := R) (I := I)).right • i = j)
    (hsurj : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := R) (I := I) →* R).comp
        (actualImage K).subtype))
    (c : R) (i : I) (hcycle : ∀ j : I, ∃ n : ℕ, c^n • i = j)
    (a : ℕ) (ha : ∀ N : Subgroup R, N.Normal → MarkedC4.normalGen N ≤ a) :
    ∀ N : Subgroup K, N.Normal →
      ∃ x : Fin (2+a) → K, Subgroup.normalClosure (Set.range x) = N :=
  IrreducibleAbelianSemidirectSubgroup.normal_generating_tuples action K
    (BinaryPlaneWreathIrreducible.action_injective.comp Subtype.val_injective)
    (BinaryPlaneWreathIrreducible.irreducible (actualImage K) hloc htrans)
    (by omega) (normal_generating_tuples (actualImage K) hsurj c i hcycle a ha)

end SymmetricSubgroupAsymptotics.BinaryPlaneWreathNormalGenerators

end
