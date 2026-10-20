import SymmetricSubgroupAsymptotics.FiniteStabilizerPairingObstruction
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop18CatalogueBinding
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FourPairTop18NoPairing
private def paths : Fin 8 → List (Fin 4) :=
  ![[],[0,3,0],[0,3,0],[0,3,0],[0,3,0],[0,3,0],[0,3,0],[0,3,0]]
private def wordFor (y : Fin 8) : FiniteGeneratorWord (Fin 4) :=
  (paths y).foldl (fun w j => .mul (.generator j) w) .one
private theorem fixes_checked : ∀ y : Fin 8, y ≠ 0 →
    (wordFor y).eval PrimitiveAffineEightTop18CatalogueBinding.catalogueGenerators 0 = 0 := by
  decide +kernel
private theorem moves_checked : ∀ y : Fin 8, y ≠ 0 →
    (wordFor y).eval PrimitiveAffineEightTop18CatalogueBinding.catalogueGenerators y ≠ y := by
  decide +kernel
def certificate : FiniteStabilizerPairingObstruction PrimitiveAffineEightTop18CatalogueBinding.catalogueGenerators 0 where
  words y := wordFor y.1
  fixes y := fixes_checked y.1 y.2
  moves y := moves_checked y.1 y.2
theorem no_frame {I : Type*} (F : BinaryPairFrame PrimitiveAffineEightTop18CatalogueBinding.catalogueAction I) : False :=
  certificate.no_frame F
end SymmetricSubgroupAsymptotics.FourPairTop18NoPairing
end
