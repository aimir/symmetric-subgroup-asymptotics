import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Solvable

/-! The actual normalizer of a cyclic subgroup is solvable whenever its
actual centralizer is solvable. The quotient embeds in the commutative
automorphism group of the SAME cyclic subgroup. No odd-order theorem is
assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CyclicNormalizerSolvableOfCentralizer

theorem isSolvable {G : Type*} [Group G] (P : Subgroup G) [IsCyclic P]
    (hC : IsSolvable (Subgroup.centralizer (P : Set G))) :
    IsSolvable (Subgroup.normalizer (P : Set G)) := by
  let C := Subgroup.centralizer (P : Set G)
  let k := P.normalizerMonoidHom
  let a := IsCyclic.mulAutMulEquiv P
  letI : IsSolvable (MulAut P) :=
    solvable_of_solvable_injective (f:=a.toMonoidHom) a.injective
  letI : IsSolvable C := hC
  let f : k.ker →* C := {
    toFun := fun x => ⟨x.val.val,by
      have hx := x.property
      change x.val∈P.normalizerMonoidHom.ker at hx
      have hm := Eq.mp (congrArg
        (fun L : Subgroup (Subgroup.normalizer (P : Set G)) =>
          (x.val : Subgroup.normalizer (P : Set G))∈L)
        P.normalizerMonoidHom_ker) hx
      exact hm⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro x y h
    have he : x.val.val=y.val.val := congrArg (fun z : C => z.val) h
    exact Subtype.ext (Subtype.ext he)
  letI : IsSolvable k.ker := solvable_of_solvable_injective (f:=f) hf
  exact solvable_of_ker_le_range k.ker.subtype k (by
    rw [Subgroup.range_subtype])

end SymmetricSubgroupAsymptotics.CyclicNormalizerSolvableOfCentralizer
