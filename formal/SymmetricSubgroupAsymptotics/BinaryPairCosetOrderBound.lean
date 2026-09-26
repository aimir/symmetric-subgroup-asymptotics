import SymmetricSubgroupAsymptotics.GeneratorCosetOrderBound
import SymmetricSubgroupAsymptotics.BinaryPairSchreierBinding

/-!
# Compressed original order bounds from correlated pair flips

An arbitrary proposed flip subspace bounds its actual preimage in the
original source. Coset transitions whose defects lie in that preimage then
bound the source order. Neither inclusion of the entire proposed subspace
in the actual kernel nor an exact quotient chart is required.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X ι : Type} {w q : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

/-- Injectivity uses the faithful original flip coordinates, without any
surjectivity claim for the proposed subspace. -/
theorem coordinateKernelHom_injective
    (C : Submodule (ZMod 2) (Fin w → ZMod 2)) :
    Function.Injective (F.coordinateKernelHom C) := by
  intro k l h
  apply Subtype.ext
  apply F.bitsHom_injective
  exact congrArg (fun z : Multiplicative C => Multiplicative.ofAdd z.toAdd.val) h

/-- The original subgroup contains only the vectors of C that actually
occur in the source, so its cardinality is at most that of C. -/
theorem coordinateSubgroup_card_le
    (C : Submodule (ZMod 2) (Fin w → ZMod 2)) :
    Nat.card (F.coordinateSubgroup C) ≤ Nat.card C := by
  have e := (F.coordinateKernelSubgroup C).equivMapOfInjective
    F.top.ker.subtype Subtype.val_injective
  calc
    Nat.card (F.coordinateSubgroup C) = Nat.card (F.coordinateKernelSubgroup C) :=
      (Nat.card_congr e.toEquiv).symm
    _ ≤ Nat.card (Multiplicative C) :=
      Nat.card_le_card_of_injective (F.coordinateKernelHom C)
        (F.coordinateKernelHom_injective C)
    _ = Nat.card C := Nat.card_congr Multiplicative.toAdd

/-- Correlations in the proposed binary subspace are retained in the
exponent; independent flips are not substituted for its dimension. -/
theorem coordinateSubgroup_card_le_pow
    (C : Submodule (ZMod 2) (Fin w → ZMod 2)) :
    Nat.card (F.coordinateSubgroup C) ≤ 2 ^ Module.finrank (ZMod 2) C := by
  have h := F.coordinateSubgroup_card_le C
  simpa only [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := C),
    Nat.card_zmod] using h

/-- A finite coset cover bounds the actual original source. No equality
between the proposed flip space and the full kernel is needed. -/
theorem card_le_of_cosetOrderBound [Finite X]
    (C : Submodule (ZMod 2) (Fin w → ZMod 2))
    (generators : ι → U) (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (cert : GeneratorCosetOrderBoundCertificate generators (F.coordinateSubgroup C) q) :
    Nat.card U ≤ q * 2 ^ Module.finrank (ZMod 2) C := by
  have h := cert.card_closure_le
  rw [hgen, Subgroup.card_top] at h
  exact h.trans (Nat.mul_le_mul_left q (F.coordinateSubgroup_card_le_pow C))

/-- Original pointwise flip equations install all coset defects. The
representatives can repeat, and no quotient multiplication table is used. -/
def cosetOrderBoundOfActions
    (C : Submodule (ZMod 2) (Fin w → ZMod 2))
    (generators : ι → U) (representatives : Fin q → U)
    (identity : Fin q) (hidentity : representatives identity = 1)
    (next : Fin q → ι → Fin q)
    (defect : Fin q → ι → Fin w → ZMod 2)
    (hdefect : ∀ i j, defect i j ∈ C)
    (hstep : ∀ i j (p : Fin w × ZMod 2),
      F.frame.symm
        (((representatives i * generators j * (representatives (next i j))⁻¹ : U) :
          Equiv.Perm X) (F.frame p)) = (p.1, p.2 + defect i j p.1)) :
    GeneratorCosetOrderBoundCertificate generators (F.coordinateSubgroup C) q where
  representatives := representatives
  identity := identity
  identity_mem := by rw [hidentity]; exact (F.coordinateSubgroup C).one_mem
  next := next
  step_mem i j := F.mem_coordinateSubgroup_of_action C _ (defect i j)
    (hdefect i j) (hstep i j)

end SymmetricSubgroupAsymptotics.BinaryPairFrame

end
