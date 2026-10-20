import SymmetricSubgroupAsymptotics.FiniteStabilizerPairingObstruction
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop4CatalogueBinding
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FourPairTop4NoPairing
private def paths : Fin 8 → List (Fin 3) :=
  ![[],[0,1,0],[0,1,0],[2,0,2],[0,1,0],[0,1,0],[0,1,0],[0,1,0]]
private def wordFor (y : Fin 8) : FiniteGeneratorWord (Fin 3) :=
  (paths y).foldl (fun w j => .mul (.generator j) w) .one
private theorem fixes_checked : ∀ y : Fin 8, y ≠ 0 →
    (wordFor y).eval PrimitiveAffineEightTop4CatalogueBinding.catalogueGenerators 0 = 0 := by
  decide +kernel
private theorem moves_checked : ∀ y : Fin 8, y ≠ 0 →
    (wordFor y).eval PrimitiveAffineEightTop4CatalogueBinding.catalogueGenerators y ≠ y := by
  decide +kernel
def certificate : FiniteStabilizerPairingObstruction PrimitiveAffineEightTop4CatalogueBinding.catalogueGenerators 0 where
  words y := wordFor y.1
  fixes y := fixes_checked y.1 y.2
  moves y := moves_checked y.1 y.2
theorem no_frame {I : Type*} (F : BinaryPairFrame PrimitiveAffineEightTop4CatalogueBinding.catalogueAction I) : False :=
  certificate.no_frame F
end SymmetricSubgroupAsymptotics.FourPairTop4NoPairing
end
