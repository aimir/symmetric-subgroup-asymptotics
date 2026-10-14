import SymmetricSubgroupAsymptotics.PrimePairSwapSemidirectNormalGenerators

/-! Two scalar coordinates interchanged by a binary complement. The
second scalar character is the first character composed with the binary
automorphism. This gives the exact diagonal or antidiagonal action used
by the paired Singer complements, with a uniformly cyclic kernel module. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace ScalarPairSwapRepresentation

open SemidirectProduct

abbrev Binary := Multiplicative (ZMod 2)
abbrev Vector (p : ℕ) := Fin 2 → ZMod p

variable (p : ℕ) [Fact p.Prime]
  {C : Type} [Group C]
  (alpha : Binary →* MulAut C) (chi : C →* (ZMod p)ˣ)

def coordinateCharacter (i : Fin 2) : C →* (ZMod p)ˣ :=
  if i = 0 then chi else chi.comp (alpha C2Wreath.gen).toMonoidHom

def coefficient (i : Fin 2) : C →* ZMod p :=
  (Units.coeHom (ZMod p)).comp (coordinateCharacter p alpha chi i)

def diagonal : C →* (Vector p ≃ₗ[ZMod p] Vector p) where
  toFun c := LinearEquiv.piCongrRight fun i : Fin 2 ↦
    (LinearEquiv.smulOfUnit (coordinateCharacter p alpha chi i c) :
      ZMod p ≃ₗ[ZMod p] ZMod p)
  map_one' := by
    apply LinearEquiv.ext
    intro v
    funext i
    change coefficient p alpha chi i 1 * v i = v i
    rw [map_one, one_mul]
  map_mul' c d := by
    apply LinearEquiv.ext
    intro v
    funext i
    change coefficient p alpha chi i (c * d) * v i =
      coefficient p alpha chi i c * (coefficient p alpha chi i d * v i)
    rw [map_mul, mul_assoc]

theorem alpha_twice (c : C) : alpha C2Wreath.gen (alpha C2Wreath.gen c) = c := by
  change (alpha C2Wreath.gen * alpha C2Wreath.gen) c = c
  rw [← map_mul, C2Wreath.gen_mul_gen, map_one]
  rfl

abbrev Upper := C ⋊[alpha] Binary

instance [Finite C] : Finite (Upper alpha) :=
  Finite.of_equiv (C × Binary) SemidirectProduct.equivProd.symm

def linearAction : Upper alpha →* (Vector p ≃ₗ[ZMod p] Vector p) :=
  SemidirectProduct.lift (diagonal p alpha chi)
    (PrimePairWreathNormalGenerators.linearAction p) (by
      intro b
      apply MonoidHom.ext
      intro c
      rcases C2Wreath.cases b with rfl | rfl
      · change diagonal p alpha chi (alpha 1 c) =
          PrimePairWreathNormalGenerators.linearAction p 1 * diagonal p alpha chi c *
            (PrimePairWreathNormalGenerators.linearAction p 1)⁻¹
        rw [map_one, map_one]
        simp only [MulAut.one_apply, one_mul, inv_one, mul_one]
      · change diagonal p alpha chi (alpha C2Wreath.gen c) =
          PrimePairWreathNormalGenerators.linearAction p C2Wreath.gen * diagonal p alpha chi c *
            (PrimePairWreathNormalGenerators.linearAction p C2Wreath.gen)⁻¹
        rw [← map_inv, C2Wreath.gen_inv]
        apply LinearEquiv.ext
        intro v
        funext i
        fin_cases i
        · change (chi (alpha C2Wreath.gen c) : ZMod p) * v 0 =
            (chi (alpha C2Wreath.gen c) : ZMod p) * v 0
          rfl
        · change (chi (alpha C2Wreath.gen (alpha C2Wreath.gen c)) : ZMod p) * v 1 =
            (chi c : ZMod p) * v 1
          rw [alpha_twice])

theorem linearAction_comp_swap :
    (linearAction p alpha chi).comp (inr : Binary →* Upper alpha) =
      PrimePairWreathNormalGenerators.linearAction p :=
  SemidirectProduct.lift_comp_inr _ _ _

theorem uniform : UniformSubrepresentationGeneratorBound
    (LinearSemidirectCoprimeSocleBounds.linearRepresentation (linearAction p alpha chi)) 1 :=
  PrimePairSwapSemidirectNormalGenerators.uniform p (linearAction p alpha chi) inr
    (linearAction_comp_swap p alpha chi)

abbrev Model := LinearSemidirectCoprimeSocleBounds.Model (linearAction p alpha chi)

theorem normal_generating_tuples [Finite C] {a : ℕ}
    (hupper : ∀ N : Subgroup (Upper alpha), N.Normal →
      ∃ x : Fin a → Upper alpha, Subgroup.normalClosure (Set.range x) = N) :
    ∀ N : Subgroup (Model p alpha chi), N.Normal →
      ∃ x : Fin (1 + a) → Model p alpha chi, Subgroup.normalClosure (Set.range x) = N :=
  PrimePairSwapSemidirectNormalGenerators.normal_generating_tuples p
    (linearAction p alpha chi) inr (linearAction_comp_swap p alpha chi) hupper

end ScalarPairSwapRepresentation
end SymmetricSubgroupAsymptotics

end
