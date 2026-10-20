import SymmetricSubgroupAsymptotics.FiniteStabilizerPairingObstruction
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop22CatalogueBinding
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FourPairTop22NoPairing
private def paths : Fin 8 → List (Fin 3) :=
  ![[],[0,1,2],[0,1,2],[0,1,2],[2,0,0],[0,1,2],[0,1,2],[0,1,2]]
private def wordFor (y : Fin 8) : FiniteGeneratorWord (Fin 3) :=
  (paths y).foldl (fun w j => .mul (.generator j) w) .one
private theorem fixes_checked : ∀ y : Fin 8, y ≠ 0 →
    (wordFor y).eval PrimitiveAffineEightTop22CatalogueBinding.catalogueGenerators 0 = 0 := by
  decide +kernel
private theorem moves_checked : ∀ y : Fin 8, y ≠ 0 →
    (wordFor y).eval PrimitiveAffineEightTop22CatalogueBinding.catalogueGenerators y ≠ y := by
  decide +kernel
def certificate : FiniteStabilizerPairingObstruction PrimitiveAffineEightTop22CatalogueBinding.catalogueGenerators 0 where
  words y := wordFor y.1
  fixes y := fixes_checked y.1 y.2
  moves y := moves_checked y.1 y.2
theorem no_frame {I : Type*} (F : BinaryPairFrame PrimitiveAffineEightTop22CatalogueBinding.catalogueAction I) : False :=
  certificate.no_frame F
end SymmetricSubgroupAsymptotics.FourPairTop22NoPairing
end
