import SymmetricSubgroupAsymptotics.AlternatingSmallFibreRefinedShortIndexResidual
import SymmetricSubgroupAsymptotics.OriginalNaturalSymmetricTopOrdinaryClassBound

/-! The ordinary GM residual excludes every actual natural alternating
degree for both small fibre sizes. The surviving proper subgroup K is
the SAME original one, with its literal short nonnatural index; no
small-index classification or new index-gap premise is used. The older
stronger two-exponent residual is unchanged. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.AlternatingSmallFibreOrdinaryShortIndexResidual
open PrimitiveSocleRawStructure OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω] [MulAction.IsPretransitive A X]

theorem subnormal_class_cube_le_or_actual_nonnatural_short_index
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω),b (g • ω)=g • b ω)
    (c : ℕ) (hc : c=2 ∨ c=3) (hsize : ∀ x,Nat.card (originalBlockFibre b x)=c)
    (D : NonaffineData (Top (A:=A) (X:=X)) X)
    (m : ℕ) (hm : 5 ≤ m) (e : D.Simple ≃* alternatingGroup (Fin m))
    (K : Subgroup D.Simple) (hK : K≠⊤)
    (hdegree : Nat.card X=K.index^D.factorCount)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-1) ∨
      (D.factorCount=1 ∧ m≤K.index ∧ K.index<2*m+2 ∧ K.index≠m) := by
  rcases AlternatingSmallFibreRefinedShortIndexResidual.subnormal_class_cube_gap_or_actual_short_index
      b hb c hc hsize D m hm e K hK hdegree H hH with h|⟨hk,hmin,hmax,_,_⟩
  · exact Or.inl (h.trans (Nat.pow_le_pow_right (by decide) (by omega)))
  · by_cases he : K.index=m
    · have hd : Nat.card X=m := by simpa only [hk,pow_one,he] using hdegree
      letI : Nonempty X := Finite.card_pos_iff.mp (by omega)
      exact Or.inl
        (OriginalNaturalSymmetricTopOrdinaryClassBound.subnormal_class_cube_le_of_single_factor_natural_degree
          b hb (Classical.arbitrary X) c hc (hsize _) D m hm e hk hd H hH)
    · exact Or.inr ⟨hk,hmin,hmax,he⟩

end SymmetricSubgroupAsymptotics.AlternatingSmallFibreOrdinaryShortIndexResidual
