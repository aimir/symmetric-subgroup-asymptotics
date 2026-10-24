import SymmetricSubgroupAsymptotics.LinearMapPrimaryWeightedCode
import SymmetricSubgroupAsymptotics.WeightedMultisetCappedCode
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Algebra.Group.ConjFinite

/-! A finite polynomial family and an actual primary-factor mass cap
give a finite code separating general-linear conjugacy. The code may
be used only on the desired subset of operators: no fallback element,
nonemptiness, canonical chart, or conjugacy-invariant chart choice is
needed. Equal chosen codes construct an actual conjugator. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.GeneralLinearPrimaryFiniteCode
open Polynomial UniqueFactorizationMonoid LinearMapPrimaryWeightedCode
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

abbrev Code (P : ι → K[X]) (N : ℕ) :=
  WeightedMultisetCappedCode.Code (fun i => normalizedFactors (P i)) N

def code (P : ι → K[X]) (N : ℕ) (g : LinearMap.GeneralLinearGroup K V)
    (i : ι) (hi : (g : Module.End K V).charpoly = P i)
    (hmass : (normalizedFactors (g : Module.End K V).charpoly).card ≤ N) : Code P N := by
  let C := LinearMapPositivePrimaryDecomposition.chart (g : Module.End K V)
  have hcap : (normalizedFactors (P i)).card ≤ N := by rw [← hi]; exact hmass
  exact ⟨⟨i, hcap⟩, ⟨labels C, labels_positive C,
    (expand_labels C).trans (congrArg normalizedFactors hi)⟩⟩

theorem code_labels (P : ι → K[X]) (N : ℕ) (g : LinearMap.GeneralLinearGroup K V)
    (i : ι) (hi : (g : Module.End K V).charpoly = P i)
    (hmass : (normalizedFactors (g : Module.End K V).charpoly).card ≤ N) :
    (code P N g i hi hmass).2.val =
      labels (LinearMapPositivePrimaryDecomposition.chart (g : Module.End K V)) := rfl

theorem isConj_of_code_eq (P : ι → K[X]) (N : ℕ)
    (g h : LinearMap.GeneralLinearGroup K V) (i j : ι)
    (hgi : (g : Module.End K V).charpoly = P i)
    (hhj : (h : Module.End K V).charpoly = P j)
    (hgmass : (normalizedFactors (g : Module.End K V).charpoly).card ≤ N)
    (hhmass : (normalizedFactors (h : Module.End K V).charpoly).card ≤ N)
    (he : code P N g i hgi hgmass = code P N h j hhj hhmass) : IsConj g h := by
  have hl := congrArg (fun c : Code P N => c.2.val) he
  dsimp only at hl
  rw [code_labels, code_labels] at hl
  obtain ⟨F, hF⟩ := exists_intertwining_equiv_of_labels_eq
    (LinearMapPositivePrimaryDecomposition.chart (g : Module.End K V))
    (LinearMapPositivePrimaryDecomposition.chart (h : Module.End K V)) hl
  let u := LinearMap.GeneralLinearGroup.ofLinearEquiv F
  have hu : u * g = h * u := by
    apply Units.ext
    apply LinearMap.ext
    exact hF
  exact isConj_iff.mpr ⟨u, mul_inv_eq_iff_eq_mul.mpr hu⟩

theorem card_le [Fintype ι] (P : ι → K[X]) (N : ℕ) :
    Nat.card (Code P N) ≤ Nat.card ι * 2^(N-1) :=
  WeightedMultisetCappedCode.card_le (fun i => normalizedFactors (P i)) N

end SymmetricSubgroupAsymptotics.GeneralLinearPrimaryFiniteCode
