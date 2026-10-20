import SymmetricSubgroupAsymptotics.FiniteStabilizerPairingObstruction
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop8CatalogueBinding
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FourPairTop8NoPairing
private def paths : Fin 8 → List (Fin 4) :=
  ![[],[0,1],[0,1],[0,2,0],[0,2,0],[3,0,3],[3,0,3],[0,1]]
private def wordFor (y : Fin 8) : FiniteGeneratorWord (Fin 4) :=
  (paths y).foldl (fun w j => .mul (.generator j) w) .one
private theorem fixes_checked : ∀ y : Fin 8, y ≠ 0 →
    (wordFor y).eval PrimitiveAffineEightTop8CatalogueBinding.catalogueGenerators 0 = 0 := by
  decide +kernel
private theorem moves_checked : ∀ y : Fin 8, y ≠ 0 →
    (wordFor y).eval PrimitiveAffineEightTop8CatalogueBinding.catalogueGenerators y ≠ y := by
  decide +kernel
def certificate : FiniteStabilizerPairingObstruction PrimitiveAffineEightTop8CatalogueBinding.catalogueGenerators 0 where
  words y := wordFor y.1
  fixes y := fixes_checked y.1 y.2
  moves y := moves_checked y.1 y.2
theorem no_frame {I : Type*} (F : BinaryPairFrame PrimitiveAffineEightTop8CatalogueBinding.catalogueAction I) : False :=
  certificate.no_frame F
end SymmetricSubgroupAsymptotics.FourPairTop8NoPairing
end
