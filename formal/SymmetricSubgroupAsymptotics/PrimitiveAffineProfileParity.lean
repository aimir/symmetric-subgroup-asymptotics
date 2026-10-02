import SymmetricSubgroupAsymptotics.PrimitiveAffineSolubleSource

/-!
# Prime-power degree and nontrivial complements in affine profiles

These elementary consequences turn the conditional soluble affine owner into
an actual classifier branch.  In even degree the regular prime is two.  A
trivial point stabilizer would then make the whole retained action a 2-group,
contrary to its defining non-2 condition.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineProfile

variable {L : Type} [Group L] {w : ℕ} [MulAction L (Fin w)]
  (P : PrimitiveAffineProfile L (Fin w))

/-- The affine action degree is a power of the profile prime. -/
theorem degree_eq_prime_power [Finite L] (x : Fin w) :
    ∃ d : ℕ, w = P.p ^ d := by
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  obtain ⟨d, hd⟩ := IsPGroup.exists_card_eq P.V_pgroup
  refine ⟨d, ?_⟩
  calc
    w = Nat.card (Fin w) := by simp
    _ = Nat.card P.V := (P.card_eq x).symm
    _ = P.p ^ d := hd

/-- An even affine degree forces the profile prime to be two. -/
theorem prime_eq_two_of_even_degree [Finite L] (x : Fin w)
    (hweven : Even w) : P.p = 2 := by
  obtain ⟨d, hd⟩ := P.degree_eq_prime_power x
  rcases P.p_prime.eq_two_or_odd' with hp | hp
  · exact hp
  · exact False.elim
      ((Nat.not_odd_iff_even.mpr hweven) (hd.symm ▸ hp.pow))

end PrimitiveAffineProfile

namespace Non2UnipotentPrefixFiniteMenu

variable {w : ℕ}

/-- In an even-degree retained non-2 affine action, every point stabilizer is
nontrivial. -/
theorem complement_nontrivial_of_even_nonTwo
    {U : PreE7NonPairActionClass w}
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (hweven : Even w) : Nontrivial (P.complement x) := by
  let hp2 := P.prime_eq_two_of_even_degree x hweven
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hVp : IsPGroup 2 P.V := by simpa [hp2] using P.V_pgroup
  obtain ⟨d, hd⟩ := IsPGroup.exists_card_eq hVp
  by_contra hnt
  have hsub : Subsingleton (P.complement x) := not_nontrivial_iff_subsingleton.mp hnt
  letI : Subsingleton (P.complement x) := hsub
  have hcomp : Nat.card (P.complement x) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  have hfactor := (P.isComplement'_complement x).card_mul
  have hcard : Nat.card (preE7NonPairAction w U) = 2 ^ d := by
    calc
      Nat.card (preE7NonPairAction w U) =
          Nat.card P.V * Nat.card (P.complement x) := hfactor.symm
      _ = 2 ^ d := by rw [hd, hcomp, mul_one]
  exact U.1.1.representative_not_isPGroup (IsPGroup.of_card hcard)

/-- Every even-degree, sub-`1024`, soluble primitive affine profile supplies
the concrete SAPRIM source.  All side conditions are derived from the literal
profile and the retained non-2 action. -/
noncomputable def primitiveAffineEvenSoluble_rankTailOwnerSourceData
    {w : ℕ} (U : PreE7NonPairActionClass w)
    (hw6 : 6 ≤ w) (hw1024 : w < 1024) (hweven : Even w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hsolvable : IsSolvable (P.complement ⟨0, by omega⟩)) :
    PreE7RankTailOwnerSourceData w U := by
  let x : Fin w := ⟨0, by omega⟩
  letI : Nontrivial (P.complement x) :=
    complement_nontrivial_of_even_nonTwo P x hweven
  letI : IsSolvable (P.complement x) := hsolvable
  let D : SolubleDerivedLength (P.complement x) :=
    Classical.choice (SolubleDerivedLength.nonempty _ inferInstance)
  exact PrimitiveAffineSolubleSource.toRankTailOwnerSource
    P x hw6 hw1024 hweven hprimitive D

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
