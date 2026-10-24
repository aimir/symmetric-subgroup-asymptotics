import SymmetricSubgroupAsymptotics.CFSGFFourOriginalFullCoefficientCertificate
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalSparseFamilyInstaller

/-! The complete actual original F4 source actions on the displayed
positive paths and Cartan vectors, for both signs. All finite coefficient
premises are discharged by the integral certificate; all source premises
are discharged by the original Serre-family installer. This proves source
identities, while integral spanning and tensor faithfulness remain separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalSourceActionTables
open CFSG.Models.Chevalley CFSGSerreSignedRootWeights
open CFSGFFourOriginalRootFamilyProfile CFSGFFourOriginalFullCoefficientCertificate
open CFSGFFourOriginalSparseFamilyInstaller
local notation "A" => CartanMatrix.F₄

theorem source_tables (neg:Bool) :
    (∀i j,⁅rootVector A neg i,family neg j⁆=
      ((raisingEntry i j).2:ℚ) • family neg (raisingEntry i j).1) ∧
      (∀a j,0<height j→⁅oppositeVector A neg a,family neg j⁆=
        ((loweringEntry a j).2:ℚ) • family neg (loweringEntry a j).1) :=
  source_tables_of_integer_certificate neg raisingEntry loweringEntry
    cartan_entries simple_entries parent_entries lowering_height raising_height raising_weight mixed_entries

theorem raising (neg:Bool) (i:Fin 4) (j:Slot) :
    ⁅rootVector A neg i,family neg j⁆=
      ((raisingEntry i j).2:ℚ) • family neg (raisingEntry i j).1 :=
  (source_tables neg).1 i j

theorem lowering (neg:Bool) (a:Fin 4) (j:Slot) (hj:0<height j) :
    ⁅oppositeVector A neg a,family neg j⁆=
      ((loweringEntry a j).2:ℚ) • family neg (loweringEntry a j).1 :=
  (source_tables neg).2 a j hj

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalSourceActionTables
