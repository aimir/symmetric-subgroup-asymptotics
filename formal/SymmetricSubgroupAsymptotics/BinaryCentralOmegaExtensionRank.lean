import SymmetricSubgroupAsymptotics.BinaryPrimaryLinearCharacter
import SymmetricSubgroupAsymptotics.OriginalKernelCenter

/-!
# Central binary ranks in an original module extension

The central omega of an extension maps into the central omega of its
actual surjective top. Its kernel is the literal central omega remaining
inside the module kernel. An original kernel chart injects that kernel
into the fixed space of the original module representation.

If the top is commutative, the derived subgroup is contained in the
module kernel, so the derived-central rank has only the fixed-module
cost. Neither statement assumes that the extension splits.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped IsMulCommutative

namespace SymmetricSubgroupAsymptotics

variable {Q B : Type} [Group Q] [Group B]

/-- A surjection takes central involutions into central involutions. -/
def binaryCentralOmegaMap (pi : Q →* B) (hpi : Function.Surjective pi) :
    binaryCentralOmega Q →* binaryCentralOmega B where
  toFun z := ⟨⟨pi (binaryCentralOmegaEmbedding z), by
    apply Subgroup.mem_center_iff.mpr
    intro b
    obtain ⟨q, rfl⟩ := hpi b
    simpa only [map_mul] using
      congrArg pi (Subgroup.mem_center_iff.mp z.val.property q)⟩, by
        apply Subtype.ext
        change pi (binaryCentralOmegaEmbedding z) ^ 2 = 1
        have hz : binaryCentralOmegaEmbedding z ^ 2 = 1 :=
          congrArg Subtype.val z.property
        rw [← map_pow, hz, map_one]⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one pi
  map_mul' z w := by apply Subtype.ext; apply Subtype.ext; exact map_mul pi _ _

def binaryCentralOmegaLinearMap (pi : Q →* B) (hpi : Function.Surjective pi) :
    Additive (binaryCentralOmega Q) →ₗ[ZMod 2] Additive (binaryCentralOmega B) :=
  (binaryCentralOmegaMap pi hpi).toAdditive.toZModLinearMap 2

theorem binaryCentralOmegaLinearMap_ker
    (pi : Q →* B) (hpi : Function.Surjective pi) :
    (binaryCentralOmegaLinearMap pi hpi).ker = binaryCentralOmegaSubmodule pi.ker := by
  ext z
  change binaryCentralOmegaMap pi hpi z.toMul = 1 ↔
    pi (binaryCentralOmegaEmbedding z.toMul) = 1
  constructor
  · intro h
    exact congrArg (binaryCentralOmegaEmbedding (G := B)) h
  · intro h
    apply binaryCentralOmegaEmbedding_injective
    exact h

theorem binaryCentralOmega_finrank_le_kernel_add_top [Finite Q] [Finite B]
    (pi : Q →* B) (hpi : Function.Surjective pi) :
    Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) ≤
      Module.finrank (ZMod 2) (binaryCentralOmegaSubmodule pi.ker) +
        Module.finrank (ZMod 2) (Additive (binaryCentralOmega B)) := by
  have hsum := (binaryCentralOmegaLinearMap pi hpi).finrank_range_add_finrank_ker
  have hrange := Submodule.finrank_le (binaryCentralOmegaLinearMap pi hpi).range
  rw [binaryCentralOmegaLinearMap_ker] at hsum
  omega

theorem binaryCentralOmegaSubmodule_mono {H K : Subgroup Q} (h : H ≤ K) :
    binaryCentralOmegaSubmodule H ≤ binaryCentralOmegaSubmodule K := by
  intro z hz
  exact h hz

/-- Commutativity of the actual top places the entire derived subgroup
in the actual kernel. -/
theorem binaryCentralOmega_derived_finrank_le_kernel [Finite Q]
    [IsMulCommutative B] (pi : Q →* B) :
    Module.finrank (ZMod 2) (binaryCentralOmegaSubmodule (commutator Q)) ≤
      Module.finrank (ZMod 2) (binaryCentralOmegaSubmodule pi.ker) :=
  Submodule.finrank_mono
    (binaryCentralOmegaSubmodule_mono (Abelianization.commutator_subset_ker pi))

namespace OriginalKernelModuleChart

variable {pi : Q →* B} {A : Rep (ZMod 2) B}
  (E : OriginalKernelModuleChart pi A)

/-- Central involutions of the whole group lying in the kernel, viewed
inside the fixed vectors of the exact module chart. -/
def centralResidualToInvariants (hpi : Function.Surjective pi) :
    binaryCentralOmegaSubmodule pi.ker → A.ρ.invariants := fun z ↦ by
  let kz : pi.ker := ⟨binaryCentralOmegaEmbedding z.val.toMul, z.property⟩
  let a : A := (E.equiv.symm kz).toAdd
  have ha : E.element a = binaryCentralOmegaEmbedding z.val.toMul := by
    exact congrArg Subtype.val (E.equiv.apply_symm_apply kz)
  refine ⟨a, (E.element_mem_center_iff hpi a).mp ?_⟩
  rw [ha]
  exact z.val.toMul.val.property

theorem centralResidualToInvariants_injective (hpi : Function.Surjective pi) :
    Function.Injective (E.centralResidualToInvariants hpi) := by
  intro z w h
  apply Subtype.ext
  apply Additive.toMul.injective
  apply binaryCentralOmegaEmbedding_injective
  have ha := congrArg Subtype.val h
  change (E.equiv.symm ⟨binaryCentralOmegaEmbedding z.val.toMul, z.property⟩).toAdd =
    (E.equiv.symm ⟨binaryCentralOmegaEmbedding w.val.toMul, w.property⟩).toAdd at ha
  exact congrArg (fun k : pi.ker ↦ (k : Q))
    (E.equiv.symm.injective (Multiplicative.toAdd.injective ha))

include E

/-- The dimension bound uses an injection into actual fixed vectors;
there is no assumption that all intrinsic kernel-central vectors are
ambient fixed. -/
theorem centralResidual_finrank_le_invariants [Finite Q] [Finite A]
    (hpi : Function.Surjective pi) :
    Module.finrank (ZMod 2) (binaryCentralOmegaSubmodule pi.ker) ≤
      Module.finrank (ZMod 2) A.ρ.invariants := by
  have hcard := Nat.card_le_card_of_injective _
    (E.centralResidualToInvariants_injective hpi)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := binaryCentralOmegaSubmodule pi.ker),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := A.ρ.invariants),
    Nat.card_zmod] at hcard
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hcard

theorem central_finrank_le_invariants_add_top [Finite Q] [Finite B] [Finite A]
    (hpi : Function.Surjective pi) :
    Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) ≤
      Module.finrank (ZMod 2) A.ρ.invariants +
        Module.finrank (ZMod 2) (Additive (binaryCentralOmega B)) :=
  (binaryCentralOmega_finrank_le_kernel_add_top pi hpi).trans
    (Nat.add_le_add_right (E.centralResidual_finrank_le_invariants hpi) _)

theorem derivedCentral_finrank_le_invariants [Finite Q] [Finite A]
    [IsMulCommutative B] (hpi : Function.Surjective pi) :
    Module.finrank (ZMod 2) (binaryCentralOmegaSubmodule (commutator Q)) ≤
      Module.finrank (ZMod 2) A.ρ.invariants :=
  (binaryCentralOmega_derived_finrank_le_kernel pi).trans
    (E.centralResidual_finrank_le_invariants hpi)

end OriginalKernelModuleChart
end SymmetricSubgroupAsymptotics
