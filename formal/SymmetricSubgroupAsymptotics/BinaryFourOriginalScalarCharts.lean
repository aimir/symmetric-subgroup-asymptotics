import SymmetricSubgroupAsymptotics.BinaryFourA4OriginalInducedChart
import SymmetricSubgroupAsymptotics.BinaryFourS4OriginalInducedChart

/-! Scalar transport is internal to the exact original charts. Original
profile consumers keep their own prime parameter and vector space. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourOriginalScalarCharts

open BinaryFourBlockAugmentation BinaryFourSymmetricBlockActions

variable {G V L : Type} [Group G] [Finite G] [Group L] [Finite L]

def a4Frame {p : ℕ} (hp : p = 2) (eG : G ≃* Complement) :
    Representation (ZMod p) G (Fin 8 → ZMod p) := by
  subst p
  exact BinaryFourCanonicalInducedChart.fullCoordinatesRepresentation.comp eG.toMonoidHom

def s4Frame {p : ℕ} (hp : p = 2) (eG : G ≃* SymmetricComplement) :
    Representation (ZMod p) G (Fin 8 → ZMod p) := by
  subst p
  exact BinaryFourCanonicalSymmetricInducedChart.fullCoordinatesRepresentation.comp eG.toMonoidHom

def a4Chart {p : ℕ} [Fact p.Prime] (hp : p = 2)
    [AddCommGroup V] [_root_.Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (H : Subgroup G) (eG : G ≃* Complement)
    (eH : H ≃* BinaryFourCanonicalInducedChart.stabilizer)
    (commutes : ∀ h : H, eG h.1 = (eH h).1)
    (f : H →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (theta : Representation (ZMod p) L V)
    (hdim : _root_.Module.finrank (ZMod p) V = 2) (htheta : Function.Injective theta) :
    (Representation.coind H.subtype (theta.comp f)).Equiv (a4Frame hp eG) := by
  subst p
  exact BinaryFourA4OriginalInducedChart.originalCoinducedChart_of_local_epi
    H eG eH commutes hdim f hf hL theta htheta

def s4Chart {p : ℕ} [Fact p.Prime] (hp : p = 2)
    [AddCommGroup V] [_root_.Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (H : Subgroup G) (eG : G ≃* SymmetricComplement)
    (eH : H ≃* BinaryFourCanonicalSymmetricInducedChart.stabilizer)
    (commutes : ∀ h : H, eG h.1 = (eH h).1)
    (f : H →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (theta : Representation (ZMod p) L V)
    (hdim : _root_.Module.finrank (ZMod p) V = 2) (htheta : Function.Injective theta) :
    (Representation.coind H.subtype (theta.comp f)).Equiv (s4Frame hp eG) := by
  subst p
  exact BinaryFourS4OriginalInducedChart.originalCoinducedChart_of_local_epi
    H eG eH commutes hdim f hf hL theta htheta

end SymmetricSubgroupAsymptotics.BinaryFourOriginalScalarCharts

end
