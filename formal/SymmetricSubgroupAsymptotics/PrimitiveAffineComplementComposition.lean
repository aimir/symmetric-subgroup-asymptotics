import SymmetricSubgroupAsymptotics.FixedTargetCompositionTrace
import SymmetricSubgroupAsymptotics.ChiefAbelianSeriesTransport
import SymmetricSubgroupAsymptotics.PrimitiveCompositionLengthInput
import SymmetricSubgroupAsymptotics.PrimitiveAffineBottomFibre

/-!
# Composition budget of a primitive affine complement

The complement trace is pulled back to the literal quotient by the regular
translation subgroup, then prepended to that elementary subgroup.  The
published primitive composition-length theorem therefore bounds the exact
abelian exponent of the complement, with one additional saved edge when the
complement is nonsoluble.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineProfile

variable {L Ω : Type} [Group L] [Finite L] [MulAction L Ω] [Finite Ω]
  [Nontrivial Ω] [FaithfulSMul L Ω]
  (P : PrimitiveAffineProfile L Ω)

/-- The quotient by translations is the actual point stabilizer. -/
def quotientComplementEquiv (x : Ω) :
    (L ⧸ P.V) ≃* P.complement x :=
  (QuotientGroup.quotientMulEquivOfEq
      (P.complementProjection_ker x).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (P.complementProjection x) (P.complementProjection_surjective x))

/-- The exact complement exponent plus the translation dimension and one
nonsoluble edge lies below the published primitive composition bound. -/
theorem complementTrace_charge_le_primitiveBound
    (hcomp : PrimitiveCompositionLengthInput)
    {w : ℕ} (hw : 2 ≤ w)
    (U : Subgroup (Equiv.Perm (Fin w))) [Nontrivial (Fin w)]
    (A : PrimitiveAffineProfile U (Fin w))
    (hprimitive : MulAction.IsPreprimitive U (Fin w))
    (x : Fin w)
    (C : A.ElementaryChart hprimitive)
    (T : FixedTargetCompositionTrace (A.complement x))
    (hnonsolvable : ¬ IsSolvable (A.complement x)) :
    ((T.envelope.abelianLength + C.d + 1 : ℕ) : ℝ) ≤
      (8 / 3 : ℝ) * Real.logb 2 w - 4 / 3 := by
  letI : Fact A.p.Prime := C.primeFact
  let e := A.quotientComplementEquiv x
  let sq : ActualChiefSeries (U ⧸ A.V) :=
    actualChiefSeriesComap e T.chief
  have hVnt : Nontrivial A.V := C.equiv.symm.injective.nontrivial
  have hVne : A.V ≠ ⊥ := A.V.nontrivial_iff_ne_bot.mp hVnt
  let su : ActualChiefSeries U :=
    prependMinimalNormalChiefSeries A.V hVne
      (fun K hK hKV => A.minimal hprimitive K hK hKV) sq
  have hab := prependMinimalNormalChiefSeries_abelianLength A.V hVne
    (fun K hK hKV => A.minimal hprimitive K hK hKV) sq
  have hnon := prependMinimalNormalChiefSeries_nonabelianCount A.V hVne
    (fun K hK hKV => A.minimal hprimitive K hK hKV) sq
  have hcomm : IsMulCommutative A.V := A.isMulCommutative hprimitive
  have hsqa : actualChiefSeriesAbelianLength sq =
      actualChiefSeriesAbelianLength T.chief :=
    actualChiefSeriesComap_abelianLength e T.chief
  have hsqn : actualChiefSeriesNonabelianCount sq =
      actualChiefSeriesNonabelianCount T.chief :=
    actualChiefSeriesComap_nonabelianCount e T.chief
  have hsua : actualChiefSeriesAbelianLength su =
      C.d + T.envelope.abelianLength := by
    have hd : C.d = Module.finrank (ZMod A.p) C.V := rfl
    rw [hd]
    rw [show su = prependMinimalNormalChiefSeries A.V hVne
        (fun K hK hKV => A.minimal hprimitive K hK hKV) sq from rfl,
      hab, chiefAbelianLength_elementary (p := A.p) C.equiv, hsqa,
      ← T.abelianLength_eq]
  have hsun : actualChiefSeriesNonabelianCount su = T.nonabelianCount := by
    rw [show su = prependMinimalNormalChiefSeries A.V hVne
        (fun K hK hKV => A.minimal hprimitive K hK hKV) sq from rfl,
      hnon, chiefNonabelianIndicator, if_pos hcomm, zero_add, hsqn,
      ← T.nonabelianCount_eq]
  obtain ⟨t, ht⟩ := actualChiefTotalCharge_le_some_compositionLength su
  have hnonpos : 1 ≤ T.nonabelianCount :=
    T.one_le_nonabelianCount_of_not_solvable hnonsolvable
  have hnat : T.envelope.abelianLength + C.d + 1 ≤ t.chain.length := by
    rw [hsua, hsun] at ht
    omega
  exact (show ((T.envelope.abelianLength + C.d + 1 : ℕ) : ℝ) ≤
      (t.chain.length : ℝ) by exact_mod_cast hnat).trans
    (hcomp w hw U hprimitive t)

end PrimitiveAffineProfile
end SymmetricSubgroupAsymptotics

end
