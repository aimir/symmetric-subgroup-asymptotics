import SymmetricSubgroupAsymptotics.BinarySymmetricThreeTwoRowUniform
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinarySymmetricThreeTwoRowUniform
 theorem uniform {H : Type} [Group H] (rho : Representation Bit H Space)
    (a b : H) (ha : rho a=cycle) (hb : rho b=swap) :
    UniformSubrepresentationGeneratorBound rho 1 :=
  (uniformSubrepresentationGeneratorBound_iff_submodule rho 1).mpr
    (module_uniform rho a b ha hb)
end SymmetricSubgroupAsymptotics.BinarySymmetricThreeTwoRowUniform
