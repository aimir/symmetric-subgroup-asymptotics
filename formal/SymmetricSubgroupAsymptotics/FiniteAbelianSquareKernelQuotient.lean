import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! A surjective map of finite abelian groups cannot increase the size of
the subgroup killed by squaring. This is proved through the actual induced
map modulo squares, rather than by choosing invariant factors. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteAbelianSquareKernelQuotient
variable {Z A : Type} [CommGroup Z] [CommGroup A] [Finite Z] [Finite A]

 theorem card_quotient_squares (G : Type) [CommGroup G] [Finite G] :
    Nat.card (G ⧸ (powMonoidHom (α := G) 2).range)=
      Nat.card (powMonoidHom (α := G) 2).ker := by
  rw [← Subgroup.index_eq_card]
  exact Subgroup.index_range

 theorem card_square_kernel_le (q : Z →* A) (hq : Function.Surjective q) :
    Nat.card (powMonoidHom (α := A) 2).ker≤
      Nat.card (powMonoidHom (α := Z) 2).ker := by
  let S := (powMonoidHom (α := Z) 2).range
  let R := (powMonoidHom (α := A) 2).range
  have hSR : S≤R.comap q := by
    rintro x ⟨z,rfl⟩
    exact ⟨q z,(map_pow q z 2).symm⟩
  let induced : Z ⧸ S →* A ⧸ R := QuotientGroup.map S R q hSR
  have hi : Function.Surjective induced := by
    apply QuotientGroup.map_surjective_of_surjective S R q _ hSR
    exact (QuotientGroup.mk'_surjective R).comp hq
  have hc := Nat.card_le_card_of_surjective induced hi
  simpa only [S,R,card_quotient_squares] using hc

end SymmetricSubgroupAsymptotics.FiniteAbelianSquareKernelQuotient
