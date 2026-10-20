import SymmetricSubgroupAsymptotics.FiniteGeneratorWord
import SymmetricSubgroupAsymptotics.BinaryPairFramePairing

/-! Seven short original words can exclude a pair system on eight points.
Only word evaluation on two original points is checked. No group elements,
normal subgroups, centralizers or involutions are enumerated. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

structure FiniteStabilizerPairingObstruction {X ι : Type*}
    (generators : ι → Equiv.Perm X) (a : X) where
  words : {y : X // y ≠ a} → FiniteGeneratorWord ι
  fixes : ∀ y, (words y).eval generators a = a
  moves : ∀ y, (words y).eval generators y.1 ≠ y.1

namespace FiniteStabilizerPairingObstruction
variable {X ι : Type*} {generators : ι → Equiv.Perm X} {a : X}
    (C : FiniteStabilizerPairingObstruction generators a)

include C

/-- Every actual equivariant partner is moved by one checked original
point-stabilizer word, contradicting equivariance at the original point. -/
theorem no_pairing :
    IsEmpty (EquivariantPairing (Subgroup.closure (Set.range generators)) X) := by
  refine ⟨?_⟩
  intro p
  let y : {y : X // y ≠ a} := ⟨p.1 a,p.2.2.1 a⟩
  let g : Subgroup.closure (Set.range generators) :=
    ⟨(C.words y).eval generators,(C.words y).eval_mem_closure generators⟩
  have he := p.2.2.2 g a
  change p.1 ((C.words y).eval generators a) =
    (C.words y).eval generators (p.1 a) at he
  rw [C.fixes y] at he
  exact C.moves y he.symm

theorem no_frame {I : Type*}
    (F : BinaryPairFrame (Subgroup.closure (Set.range generators)) I) : False :=
  C.no_pairing.false F.underlyingPairing

end FiniteStabilizerPairingObstruction
end SymmetricSubgroupAsymptotics
end
