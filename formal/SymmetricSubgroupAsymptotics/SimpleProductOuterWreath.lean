import SymmetricSubgroupAsymptotics.SimpleProductAutomorphismWreath
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex

/-! The outer-coordinate quotient has exactly the inner automorphisms of
the original simple power as its kernel. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SimpleProductOuterWreath
open PrimitiveSocleRawStructure SimpleProductAutomorphismWreath

variable {I T : Type} [Group T]

abbrev OuterWreath (T I : Type) [Group T] :=
  PermutationalWreathProduct (Outer T) (Equiv.Perm I) I

def outerHom : Wreath T I →* OuterWreath T I where
  toFun w := ⟨fun i => QuotientGroup.mk' (PrimitiveSocleRawStructure.Inner T) (w.left i), w.right⟩
  map_one' := by
    apply PermutationalWreathProduct.ext
    · funext i
      exact map_one _
    · rfl
  map_mul' a b := by
    apply PermutationalWreathProduct.ext
    · funext i
      exact map_mul (QuotientGroup.mk' (PrimitiveSocleRawStructure.Inner T)) _ _
    · rfl

theorem outerHom_inner (x : I → T) :
    outerHom (innerCoordinates x) = 1 := by
  apply PermutationalWreathProduct.ext
  · funext i
    exact (QuotientGroup.eq_one_iff _).mpr ⟨x i, rfl⟩
  · rfl

theorem inner_of_outerHom_eq_one (w : Wreath T I)
    (h : outerHom w = 1) :
    ∃ x : I → T, w = innerCoordinates x := by
  have hr : w.right = 1 := congrArg PermutationalWreathProduct.right h
  have hl (i : I) : w.left i ∈ PrimitiveSocleRawStructure.Inner T := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact congrFun (congrArg PermutationalWreathProduct.left h) i
  choose x hx using fun i => hl i
  refine ⟨x, ?_⟩
  apply PermutationalWreathProduct.ext ?_ hr
  funext i
  exact (hx i).symm

def automorphismOuter [Fintype I] [Finite T] [IsSimpleGroup T]
    (hT : IsCenterless T) : MulAut (I → T) →* OuterWreath T I :=
  outerHom.comp (equiv hT).toMonoidHom

/-- The exact literal inner subgroup is the whole kernel. -/
theorem automorphismOuter_ker [Fintype I] [Finite T] [IsSimpleGroup T]
    (hT : IsCenterless T) :
    (automorphismOuter (I := I) hT).ker = PrimitiveSocleRawStructure.Inner (I → T) := by
  apply le_antisymm
  · intro e he
    obtain ⟨x, hx⟩ := inner_of_outerHom_eq_one (equiv hT e) he
    refine ⟨x, ?_⟩
    apply (equiv hT).injective
    exact (equiv_inner hT x).trans hx.symm
  · rintro e ⟨x, rfl⟩
    change outerHom (equiv hT (MulAut.conj x)) = 1
    rw [equiv_inner]
    exact outerHom_inner x

end SymmetricSubgroupAsymptotics.SimpleProductOuterWreath
