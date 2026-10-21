import SymmetricSubgroupAsymptotics.BinaryLinearSolutionChart
import Mathlib.Algebra.Field.ZMod

/-! A sparse coefficient certificate bounds fixed vectors modulo one
actual coordinate subspace. Only retained generator/basis columns occur;
no enumeration of all vectors in the original kernel is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
local instance coordinateFixedDisplacementFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev binaryCoordinateFixedDisplacements {w k r : ℕ} (K : BinaryCoordinateSpace w k)
    (moves : Fin r → ((Fin w → ZMod 2) →ₗ[ZMod 2] (Fin w → ZMod 2)))
    (A : Submodule (ZMod 2) (Fin w → ZMod 2)) :=
  {v : Fin w → ZMod 2 // v∈K.space ∧ ∀ i,moves i v-v∈A}

theorem binaryCoordinateFixedDisplacements_card_le_of_certificate
    {w k r a d : ℕ} (K : BinaryCoordinateSpace w k)
    (moves : Fin r → ((Fin w → ZMod 2) →ₗ[ZMod 2] (Fin w → ZMod 2)))
    (A : Submodule (ZMod 2) (Fin w → ZMod 2))
    (ann : Fin a → ((Fin w → ZMod 2) →ₗ[ZMod 2] ZMod 2))
    (generatorIndex : Fin a → Fin r)
    (C : BinaryCoordinateSpace k d) (input : Fin a → Fin k → ZMod 2)
    (cert : BinaryLinearConstraintCertificate input (binaryCoordinateDefectRows C))
    (hinput : ∀ i,binaryRowFunctional (input i)=
      (ann i).comp ((moves (generatorIndex i)-LinearMap.id).comp K.inclusion))
    (hkill : ∀ i v,v∈A → ann i v=0) :
    Nat.card (binaryCoordinateFixedDisplacements K moves A)≤2^d := by
  have hsol (v : binaryCoordinateFixedDisplacements K moves A) : K.coordinates v.val∈C.space := by
    apply binaryCoordinate_mem_of_constraints C input cert
    intro i
    change binaryRowFunctional (input i) (K.coordinates v.val)=0
    rw [hinput]
    change ann i (moves (generatorIndex i) (K.inclusion (K.coordinates v.val))-
      K.inclusion (K.coordinates v.val))=0
    rw [(K.mem_iff _).mp v.property.1]
    exact hkill i _ (v.property.2 _)
  let f : binaryCoordinateFixedDisplacements K moves A → (Fin d → ZMod 2) :=
    fun v => C.coordinates (K.coordinates v.val)
  have hf : Function.Injective f := by
    intro v z he
    have hcoord : K.coordinates v.val=K.coordinates z.val := by
      calc
        K.coordinates v.val=C.inclusion (C.coordinates (K.coordinates v.val)) :=
          ((C.mem_iff _).mp (hsol v)).symm
        _ = C.inclusion (C.coordinates (K.coordinates z.val)) := congrArg C.inclusion he
        _ = K.coordinates z.val := (C.mem_iff _).mp (hsol z)
    apply Subtype.ext
    calc
      v.val=K.inclusion (K.coordinates v.val) := ((K.mem_iff _).mp v.property.1).symm
      _ = K.inclusion (K.coordinates z.val) := congrArg K.inclusion hcoord
      _ = z.val := (K.mem_iff _).mp z.property.1
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_fun,Nat.card_fin,Nat.card_zmod] using hc

end SymmetricSubgroupAsymptotics
