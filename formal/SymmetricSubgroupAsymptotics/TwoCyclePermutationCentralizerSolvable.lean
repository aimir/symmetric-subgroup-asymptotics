import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Data.Finite.Perm
import Mathlib.GroupTheory.Solvable

/-! A fixed-point-free permutation with at most two actual cycle factors
has solvable centralizer. The existing cycle-factor map has abelian
kernel and image. No permutation enumeration or known group order occurs. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TwoCyclePermutationCentralizerSolvable

theorem isSolvable {α : Type*} [Fintype α] [DecidableEq α] (g : Equiv.Perm α)
    (hfix : ∀ x : α, g x≠x) (hcycles : Nat.card g.cycleFactorsFinset≤2) :
    IsSolvable (Subgroup.centralizer ({g} : Set (Equiv.Perm α))) := by
  let C := Subgroup.centralizer ({g} : Set (Equiv.Perm α))
  let Q := (Equiv.Perm (Function.fixedPoints g)) ×
    ((c : g.cycleFactorsFinset) → Subgroup.zpowers c.val)
  letI : IsEmpty (Function.fixedPoints g) := ⟨fun x => hfix x.val x.property⟩
  letI : IsSolvable Q := isSolvable_of_comm (fun a b => by
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · funext c
      exact mul_comm' _ _)
  letI : IsMulCommutative (Equiv.Perm g.cycleFactorsFinset) :=
    Equiv.Perm.isMulCommutative_iff_card_le_two.mpr hcycles
  letI : IsSolvable (Equiv.Perm g.cycleFactorsFinset) :=
    isSolvable_of_comm (fun a b => mul_comm' a b)
  let f : Q →* C := (Equiv.Perm.OnCycleFactors.kerParam g).codRestrict C (fun x =>
    Equiv.Perm.OnCycleFactors.kerParam_range_le_centralizer (g:=g) ⟨x,rfl⟩)
  let k := Equiv.Perm.OnCycleFactors.toPermHom g
  apply solvable_of_ker_le_range f k
  intro z hz
  have hm : (z : Equiv.Perm α)∈(Equiv.Perm.OnCycleFactors.kerParam g).range := by
    rw [Equiv.Perm.OnCycleFactors.kerParam_range_eq]
    exact ⟨z,hz,rfl⟩
  obtain ⟨x,hx⟩ := hm
  exact ⟨x,Subtype.ext hx⟩

end SymmetricSubgroupAsymptotics.TwoCyclePermutationCentralizerSolvable
