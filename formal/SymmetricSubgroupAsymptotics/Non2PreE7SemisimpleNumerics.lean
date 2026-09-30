import SymmetricSubgroupAsymptotics.Non2PreE7SemisimpleInstances
import SymmetricSubgroupAsymptotics.Non2PreE7PaddedCertificateNumerics

/-!
# Entry numerics for the ordinary semisimple owners

The four pointwise semisimple families use the common padded degree with
seed degree two.  Their structural source certificates already prove the
original exponent margin.  This file converts those margins into the exact
entry parameter records consumed by the global pre-E7 numerical closure.

`SNS2` is intentionally absent: it is an all-width correlated rank-tail row
and is aggregated by `Non2PreE7Sns2Forward`, outside the pointwise menu.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

namespace PreE7SsActionCertificate

variable {w : ℕ} {i : PreE7NonPairActionClass w}

theorem entryParameters (C : PreE7SsActionCertificate w i) :
    PreE7CharacterEntryParameters preE7CharacterRho w C.degree 0 C.delta
      C.cutoff C.cutoff 0 := by
  have hmargin : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - (2 : ℕ)) / 8 - 0 := by
    simpa using C.degree_margin
  simpa [PreE7SsActionCertificate.degree,
    PreE7SsActionCertificate.delta, PreE7SsActionCertificate.cutoff] using
    (preE7Padded_entryParameters (w := w) (v0 := 2) (eta := 0)
      (by norm_num) (by norm_num) hmargin)

end PreE7SsActionCertificate

namespace PreE7SoOrderSourceData

variable {w : ℕ} {i : PreE7NonPairActionClass w}

theorem entryParameters (D : PreE7SoOrderSourceData w i) :
    PreE7CharacterEntryParameters preE7CharacterRho w D.degree D.eta D.delta
      D.cutoff D.alpha 0 := by
  simpa [PreE7SoOrderSourceData.degree, PreE7SoOrderSourceData.delta,
    PreE7SoOrderSourceData.cutoff, PreE7SoOrderSourceData.alpha] using
    (preE7Padded_entryParameters (w := w) (v0 := 2) (eta := D.eta)
      D.eta_nonneg (by norm_num) D.degree_margin)

end PreE7SoOrderSourceData

namespace PreE7SnsActionCertificate

variable {w : ℕ} {i : PreE7NonPairActionClass w}

theorem eta_nonneg (C : PreE7SnsActionCertificate w i) : 0 ≤ C.eta := by
  unfold PreE7SnsActionCertificate.eta
  positivity

theorem entryParameters (C : PreE7SnsActionCertificate w i) :
    PreE7CharacterEntryParameters preE7CharacterRho w C.degree C.eta C.delta
      C.cutoff (C.eta + C.cutoff) 0 := by
  simpa [PreE7SnsActionCertificate.degree,
    PreE7SnsActionCertificate.delta, PreE7SnsActionCertificate.cutoff] using
    (preE7Padded_entryParameters (w := w) (v0 := 2) (eta := C.eta)
      C.eta_nonneg (by norm_num) C.degree_margin)

end PreE7SnsActionCertificate

namespace PreE7NsaprimActionCertificate

variable {w : ℕ} {i : PreE7NonPairActionClass w}

theorem entryParameters (C : PreE7NsaprimActionCertificate w i) :
    PreE7CharacterEntryParameters preE7CharacterRho w C.degree C.eta C.delta
      C.cutoff (C.eta + C.cutoff) 0 := by
  simpa [PreE7NsaprimActionCertificate.degree,
    PreE7NsaprimActionCertificate.delta,
    PreE7NsaprimActionCertificate.cutoff] using
    (preE7Padded_entryParameters (w := w) (v0 := 2) (eta := C.eta)
      C.eta_nonneg (by norm_num) C.exponent_margin)

end PreE7NsaprimActionCertificate

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
