import SymmetricSubgroupAsymptotics.BinaryGeneratorWords
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools

/-! Exact word certificates for cyclic normal generation. In particular
an element in the first natural coordinate of the Xg kernel has conjugates
spanning both coordinates; no inference from a two-slot bound is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- A displayed subgroup basis expressed in original conjugates of one
actual vector proves equality with its singleton normal closure. -/
theorem normalClosure_single_eq_of_conjugate_words
    {G I J : Type} [Group G]
    (V : Subgroup G) [V.Normal] (basis : I → G)
    (hbasis : Subgroup.closure (Set.range basis) = V)
    (v : G) (hv : v ∈ V) (conjugators : J → G)
    (words : BinaryNormalGeneratorWords basis
      (fun j => conjugators j * v * (conjugators j)⁻¹)) :
    Subgroup.normalClosure (Set.range (fun _ : Fin 1 => v)) = V := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact hv
  · rw [← hbasis]
    apply words.closure_le.trans
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    exact (inferInstance : (Subgroup.normalClosure
      (Set.range (fun _ : Fin 1 => v))).Normal).conj_mem v
      (Subgroup.subset_normalClosure (Set.mem_range_self (0 : Fin 1)))
      (conjugators j)

/-- Bind the checked cyclic word equality to the actual whole socle. -/
theorem socleBound_of_conjugate_words
    {G I J : Type} [Group G]
    (V : Subgroup G) [V.Normal] (basis : I → G)
    (hbasis : Subgroup.closure (Set.range basis) = V)
    (v : G) (hv : v ∈ V) (conjugators : J → G)
    (words : BinaryNormalGeneratorWords basis
      (fun j => conjugators j * v * (conjugators j)⁻¹))
    (hsocle : finiteGroupSocle G = V) : SocleNormalGeneratorBound G 1 :=
  ⟨fun _ => v,
    (normalClosure_single_eq_of_conjugate_words V basis hbasis v hv
      conjugators words).trans hsocle.symm⟩

end SymmetricSubgroupAsymptotics
