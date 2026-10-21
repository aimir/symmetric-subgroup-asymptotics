import SymmetricSubgroupAsymptotics.SimpleLeastIndexCompositionChart
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart
import SymmetricSubgroupAsymptotics.PerfectSubdirect
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.Data.Fintype.Perm

/-! Small faithful permutation embeddings of the actual simple factor.
The only retained estimate is the ordinary XL simple-index inequality;
no bounded primitive correspondence is used by these declarations. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics

/-- The sign of every permutation image of a perfect group is trivial. -/
def perfectPermutationToAlternating {T : Type} [Group T] [Group.IsPerfect T]
    {n : ℕ} (f : T→*Equiv.Perm (Fin n)) : T→*alternatingGroup (Fin n) where
  toFun t := ⟨f t,by
    change Equiv.Perm.sign (f t)=1
    exact Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp f)
      (Group.IsPerfect.mem_commutator (g := t))⟩
  map_one' := Subtype.ext f.map_one
  map_mul' x y := Subtype.ext (f.map_mul x y)

theorem perfectPermutationToAlternating_injective
    {T : Type} [Group T] [Group.IsPerfect T] {n : ℕ}
    (f : T→*Equiv.Perm (Fin n)) (hf : Function.Injective f) :
    Function.Injective (perfectPermutationToAlternating f) := by
  intro x y h
  exact hf (congrArg Subtype.val h)

/-- The faithful coset action of a proper subgroup of a simple group
bounds the actual group order by the factorial of that actual index. -/
theorem simple_card_le_index_factorial
    {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (H : Subgroup T) (hH : H≠⊤) : Nat.card T≤H.index.factorial := by
  have h := Nat.card_le_card_of_injective _
    (PrimitiveSocleRawStructure.simple_cosetAction_injective H hH)
  simpa only [Nat.card_perm,←H.index_eq_card] using h

/-- The ordinary simple-index inequality excludes order30 by giving a
faithful five-point action; perfectness then gives an impossible index-two
subgroup of the simple group A5. -/
theorem nonabelianSimple_card_ne_thirty
    {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hnc : ¬IsMulCommutative T)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) : Nat.card T≠30 := by
  intro hT
  obtain ⟨ell,hell⟩ := PrimitiveSocleRawStructure.exists_leastProperIndex T
  have hf : 5≤ell := nonabelianSimple_leastProperIndex_five_le
    (fun hc => hnc (isMulCommutative_iff.mpr hc)) hell.1
  have horder := (hindex T hnc ell hell).1
  rw [hT] at horder
  have he : ell=5 := by
    by_contra h
    have h6 : 6≤ell := by omega
    have h36 : 36≤ell^2 := Nat.pow_le_pow_left h6 2
    omega
  obtain ⟨H,hH,hi⟩ := hell.1
  let points : (T⧸H)≃Fin 5 := Finite.equivFinOfCardEq (by
    rw [←H.index_eq_card,hi,he])
  let f : T→*Equiv.Perm (Fin 5) := points.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom T (T⧸H))
  have hf' : Function.Injective f := points.permCongrHom.injective.comp
    (PrimitiveSocleRawStructure.simple_cosetAction_injective H hH)
  letI : Group.IsPerfect T := simple_perfect_of_nonabelian hnc
  let j := perfectPermutationToAlternating f
  have hj : Function.Injective j := perfectPermutationToAlternating_injective f hf'
  let J := j.range
  have hJ : Nat.card J=30 := (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm.trans hT
  have hA : Nat.card (alternatingGroup (Fin 5))=60 := by
    rw [nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hiJ : J.index=2 := by
    have hm := J.card_mul_index
    rw [hJ,hA] at hm
    omega
  have hJne : J≠⊤ := by
    intro h
    have hm := hJ
    rw [h,Subgroup.card_top,hA] at hm
    omega
  letI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hb := simple_card_le_index_factorial J hJne
  rw [hA,hiJ] at hb
  norm_num [Nat.factorial] at hb

end SymmetricSubgroupAsymptotics
