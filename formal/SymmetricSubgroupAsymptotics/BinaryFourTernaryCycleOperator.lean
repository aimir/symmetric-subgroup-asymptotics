import SymmetricSubgroupAsymptotics.RepresentationAlgebraCyclicPointBasis

/-! One cyclic algebra operator for four ternary blocks with a possibly
twisted block mover. A ternary norm isolates one augmentation fibre; its
four transports separate the block constants. Three fibre transfers and
one local ternary rotation replace the mover's last augmentation transfer,
while its action on the constants is retained. This construction tolerates
reflection monodromy in the actual group element moving the blocks. -/

set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourTernaryCycleOperator

variable {G : Type} [Group G]

def normOperator (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (g : G) :
    Module.End (ZMod 2) (Fin 12 → ZMod 2) := 1 + rho g + rho g ^ 2

def normScalar (g : G) : (ZMod 2)[G] :=
  1 + MonoidAlgebra.single g 1 + MonoidAlgebra.single g 1 ^ 2

theorem normOperator_eq (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (g : G) :
    normOperator rho g = rho.asAlgebraHom (normScalar g) := by
  simp only [normOperator, normScalar, map_add, map_pow, map_one,
    Representation.asAlgebraHom_single, one_smul]

def localRotation (singleBlock : Bool) (t c : G) : G :=
  if singleBlock then t else c * t * c⁻¹

def fibreOperator (singleBlock : Bool)
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t c : G) :
    Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  if singleBlock then 1 + normOperator rho t
  else normOperator rho t * (1 + normOperator rho (c * t * c⁻¹))

def fibreScalar (singleBlock : Bool) (t c : G) : (ZMod 2)[G] :=
  if singleBlock then 1 + normScalar t
  else normScalar t * (1 + normScalar (c * t * c⁻¹))

theorem fibreOperator_eq (singleBlock : Bool)
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t c : G) :
    fibreOperator singleBlock rho t c = rho.asAlgebraHom (fibreScalar singleBlock t c) := by
  cases singleBlock <;>
    simp only [fibreOperator, fibreScalar, Bool.false_eq_true, if_false, if_true,
      map_mul, map_add, map_one, ← normOperator_eq]

def constantsOperator (singleBlock : Bool)
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t c : G) :
    Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  1 + ∑ i : Fin 4, rho (c ^ i.val) * fibreOperator singleBlock rho t c *
    rho ((c ^ i.val)⁻¹)

def constantsScalar (singleBlock : Bool) (t c : G) : (ZMod 2)[G] :=
  1 + ∑ i : Fin 4, MonoidAlgebra.single (c ^ i.val) 1 * fibreScalar singleBlock t c *
    MonoidAlgebra.single ((c ^ i.val)⁻¹) 1

theorem constantsOperator_eq (singleBlock : Bool)
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t c : G) :
    constantsOperator singleBlock rho t c =
      rho.asAlgebraHom (constantsScalar singleBlock t c) := by
  simp only [constantsOperator, constantsScalar, map_add, map_sum, map_mul, map_one,
    Representation.asAlgebraHom_single, one_smul, ← fibreOperator_eq]

def actualOperator (singleBlock : Bool)
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t c : G) :
    Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  constantsOperator singleBlock rho t c * rho c +
    (∑ i : Fin 3, rho (c ^ (i.val + 1)) * fibreOperator singleBlock rho t c *
      rho ((c ^ i.val)⁻¹)) +
    rho (localRotation singleBlock t c) * fibreOperator singleBlock rho t c *
      rho ((c ^ 3)⁻¹)

def algebraElement (singleBlock : Bool) (t c : G) : (ZMod 2)[G] :=
  constantsScalar singleBlock t c * MonoidAlgebra.single c 1 +
    (∑ i : Fin 3, MonoidAlgebra.single (c ^ (i.val + 1)) 1 * fibreScalar singleBlock t c *
      MonoidAlgebra.single ((c ^ i.val)⁻¹) 1) +
    MonoidAlgebra.single (localRotation singleBlock t c) 1 * fibreScalar singleBlock t c *
      MonoidAlgebra.single ((c ^ 3)⁻¹) 1

theorem actualOperator_eq (singleBlock : Bool)
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t c : G) :
    actualOperator singleBlock rho t c =
      rho.asAlgebraHom (algebraElement singleBlock t c) := by
  simp only [actualOperator, algebraElement, map_add, map_sum, map_mul,
    Representation.asAlgebraHom_single, one_smul,
    ← fibreOperator_eq, ← constantsOperator_eq]

/-- The displayed eleven steps through a permuted twelve-point basis
certify the uniform cyclic bound at the original acting group. -/
theorem uniform_of_pointCycle (singleBlock : Bool)
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t c : G)
    (p : Equiv.Perm (Fin 12))
    (hstep : ∀ (m : Fin 11) (x : Fin 12),
      actualOperator singleBlock rho t c (Pi.single (p m.castSucc) 1) x =
        (Pi.single (p m.succ) 1 : Fin 12 → ZMod 2) x) :
    UniformSubrepresentationGeneratorBound rho 1 :=
  uniformSubrepresentationGeneratorBound_of_algebra_pointCycle
    rho (algebraElement singleBlock t c) (actualOperator singleBlock rho t c)
    (actualOperator_eq singleBlock rho t c) p (fun m ↦ funext (hstep m))

end BinaryFourTernaryCycleOperator
end SymmetricSubgroupAsymptotics

end
