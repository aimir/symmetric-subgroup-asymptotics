import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCommutingTransport

/-! A rational zero root bracket gives commutation of the SAME integral
quadratic root units in every coefficient ring. The two-parameter
polynomial transport is reused from the checked commuting-word theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCommutingRoots
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticParameterizedCollectingTransport
open CFSGSerreQuadraticCommutingTransport
variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

theorem roots_commute (K : Type*) [CommRing K] (i j : Fin r)
    (h : ⁅fieldRoot D ℚ false i,fieldRoot D ℚ false j⁆=0) (t a : K) :
    Commute (canonicalRoot D K false i t) (canonicalRoot D K false j a) := by
  have he := commuting_word_of_rational D K i j
    (rational_commuting_word D i j h) t a
  change canonicalRoot D K false i t*canonicalRoot D K false j a=
    canonicalRoot D K false j a*canonicalRoot D K false i t
  have hh := congrArg (fun u : (Matrix I I K)ˣ=>u*canonicalRoot D K false j a*
    canonicalRoot D K false i t) he
  dsimp only [parameterPositiveWord] at hh
  simpa only [mul_assoc,inv_mul_cancel,mul_one,one_mul] using hh

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCommutingRoots
