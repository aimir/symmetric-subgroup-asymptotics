import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveTemplate
import SymmetricSubgroupAsymptotics.Non2PreE7NumericalEarlierPackage

/-!
# Numerical packaging for small fixed-degree additive owners

The small-family model files prove a literal comparator-or-tail certificate
on every normal axis.  T1 additionally needs the two finite axis totals in
the common menu-mass scale.  This file records exactly those two numerical
facts and turns the result into the same `PreE7EarlierNumericalPackage` used
by the four large templates.

There is no new group-theoretic assumption here.  Concrete family modules
must prove their own finite coefficient totals; this wrapper only prevents
each of the fifteen small owners from rebuilding the catalogue plumbing.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- A small additive comparator together with the two finite coefficient
totals required by the global menu-mass theorem. -/
structure PreE7SmallAdditiveNumericalData
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  data : PreE7SmallAdditiveData w i
  main_total_bound : ∀ b,
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
        ((data.certificate family).C b) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  tail_total_bound : ∀ b,
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
        ((data.certificate family).tailCoefficient b) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

namespace PreE7SmallAdditiveNumericalData

variable {family : PreE7NoPairNoC3EarlierOwnerFamily}
  {w : ℕ} {i : PreE7NonPairActionClass w}

/-- The small fixed-degree source as a numerically complete ordinary owner. -/
noncomputable def toPackage
    (D : PreE7SmallAdditiveNumericalData family w i) :
    PreE7EarlierNumericalPackage family w i :=
  .ofComparator (D.data.certificate family)
    (D.data.entryParameters family) D.main_total_bound D.tail_total_bound

theorem numericalFamilyAction
    (D : PreE7SmallAdditiveNumericalData family w i) :
    preE7NoPairNoC3EarlierNumericalFamilyAction family w i :=
  ⟨D.toPackage⟩

end PreE7SmallAdditiveNumericalData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
