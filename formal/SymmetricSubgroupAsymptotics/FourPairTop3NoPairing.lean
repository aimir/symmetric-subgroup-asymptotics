import SymmetricSubgroupAsymptotics.FiniteStabilizerPairingObstruction
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop3CatalogueBinding
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FourPairTop3NoPairing
private def paths : Fin 8 → List (Fin 5) :=
  ![[],[1,3],[1,3],[4],[4],[4],[4],[1,3]]
private def wordFor (y : Fin 8) : FiniteGeneratorWord (Fin 5) :=
  (paths y).foldl (fun w j => .mul (.generator j) w) .one
private theorem fixes_checked : ∀ y : Fin 8, y ≠ 0 →
    (wordFor y).eval PrimitiveAffineEightTop3CatalogueBinding.catalogueGenerators 0 = 0 := by
  decide +kernel
private theorem moves_checked : ∀ y : Fin 8, y ≠ 0 →
    (wordFor y).eval PrimitiveAffineEightTop3CatalogueBinding.catalogueGenerators y ≠ y := by
  decide +kernel
def certificate : FiniteStabilizerPairingObstruction PrimitiveAffineEightTop3CatalogueBinding.catalogueGenerators 0 where
  words y := wordFor y.1
  fixes y := fixes_checked y.1 y.2
  moves y := moves_checked y.1 y.2
theorem no_frame {I : Type*} (F : BinaryPairFrame PrimitiveAffineEightTop3CatalogueBinding.catalogueAction I) : False :=
  certificate.no_frame F
end SymmetricSubgroupAsymptotics.FourPairTop3NoPairing
end
