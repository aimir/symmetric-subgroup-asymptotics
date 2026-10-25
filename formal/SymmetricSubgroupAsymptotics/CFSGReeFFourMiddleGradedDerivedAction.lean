import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleGradedKernel
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixStrictPGroup
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleDerivedFiveSurvival

/-! The literal derived middle parabolic has a genuine normal 2-kernel.
The actual order-five word conjugates it nontrivially. No independent
radical model, irreducibility, known Tits order, or index bound is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleGradedDerivedAction
open CFSGReeFFourMiddleGradedKernel CFSGReeFFourMiddleParabolicFlag
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFieldParameters
open CFSGReeFFourMiddleDerivedFiveWord CFSGReeFFourMiddleDerivedFiveRootWords
open CFSGReeFFourMiddleDerivedFiveSurvival CFSGFFourOriginalMiddleWords
open CFSGReeFFourFixedPositiveFamilies CFSGGradedMatrixStrictPGroup
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem parabolicRawHom_injective (m : ℕ) : Function.Injective (parabolicRawHom m) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact rawHom_injective (Field m) h

theorem gradedKernel_isPGroup (m : ℕ) : IsPGroup 2 (gradedKernel m) :=
  (strictUnits_isPGroup middleWeight 2).comap_of_injective (parabolicRawHom m)
    (parabolicRawHom_injective m)

def derivedParabolic (m : ℕ) : Subgroup (commutator (originalModelFixed m)) :=
  (middleParabolic m).comap (commutator (originalModelFixed m)).subtype

def toParabolic (m : ℕ) : derivedParabolic m →* middleParabolic m where
  toFun g := ⟨g.val.val,g.property⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem toParabolic_injective (m : ℕ) : Function.Injective (toParabolic m) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : middleParabolic m => z.val) h

def derivedGradedKernel (m : ℕ) : Subgroup (derivedParabolic m) :=
  (gradedKernel m).comap (toParabolic m)

instance derivedGradedKernel_normal (m : ℕ) : (derivedGradedKernel m).Normal := by
  letI := gradedKernel_normal m
  change ((gradedKernel m).comap (toParabolic m)).Normal
  infer_instance

theorem derivedGradedKernel_isPGroup (m : ℕ) : IsPGroup 2 (derivedGradedKernel m) :=
  (gradedKernel_isPGroup m).comap_of_injective (toParabolic m) (toParabolic_injective m)

def derivedParabolicFiveWord (m : ℕ) : derivedParabolic m :=
  ⟨derivedFiveWord m,(fiveWordInParabolic m).property⟩

def kernelCommutator (m : ℕ) : derivedGradedKernel m :=
  ⟨⟨(derivedPositiveCommutator m).val,(commutatorInParabolic m).property⟩,
    commutator_mem_gradedKernel m⟩

def kernelToDerived (m : ℕ) : derivedGradedKernel m →* commutator (originalModelFixed m) :=
  (derivedParabolic m).subtype.comp (derivedGradedKernel m).subtype

theorem kernelToDerived_injective (m : ℕ) : Function.Injective (kernelToDerived m) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact h

def radicalConjugation (m : ℕ) : derivedParabolic m →* MulAut (derivedGradedKernel m) :=
  MulAut.conjNormal

theorem kernelToDerived_conjugation (m : ℕ) (g : derivedParabolic m)
    (u : derivedGradedKernel m) :
    kernelToDerived m (radicalConjugation m g u) =
      g.val * kernelToDerived m u * g.val⁻¹ := rfl

def fiveAction (m : ℕ) : MulAut (derivedGradedKernel m) :=
  radicalConjugation m (derivedParabolicFiveWord m)

theorem fiveAction_pow_five (m : ℕ) : (fiveAction m)^5 = 1 := by
  have hp : (derivedParabolicFiveWord m)^5 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact fiveWord_pow_five m
  exact (map_pow (radicalConjugation m) (derivedParabolicFiveWord m) 5).symm.trans
    ((congrArg (radicalConjugation m) hp).trans (map_one (radicalConjugation m)))

private theorem aut_apply_of_eq_one {H : Type*} [Group H] (f : MulAut H)
    (hf : f = 1) (x : H) : f x = x := by
  rw [hf]
  rfl

theorem fiveAction_ne_one (m : ℕ) : fiveAction m ≠ 1 := by
  intro he
  have hh := aut_apply_of_eq_one (fiveAction m) he (kernelCommutator m)
  have hd : derivedFiveWord m * kernelToDerived m (kernelCommutator m) *
      (derivedFiveWord m)⁻¹ = kernelToDerived m (kernelCommutator m) :=
    (kernelToDerived_conjugation m (derivedParabolicFiveWord m) (kernelCommutator m)).symm.trans
      (congrArg (kernelToDerived m) hh)
  have h := congrArg (fun z : commutator (originalModelFixed m) => z.val) hd
  change fiveWord m * positiveCommutator m * (fiveWord m)⁻¹ = positiveCommutator m at h
  exact fiveWord_positiveCommutator_ne m (mul_inv_eq_iff_eq_mul.mp h)

theorem fiveAction_order (m : ℕ) : orderOf (fiveAction m) = 5 :=
  orderOf_eq_prime (fiveAction_pow_five m) (fiveAction_ne_one m)

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleGradedDerivedAction
