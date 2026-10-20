import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTowerCyclicCapacity
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopRelativeKernelOrbitRows

/-!
# Exact prefixes for a pair tower with cyclic natural sections

The three genuine kernel layers have Schur capacity at most three. The
last top quotient supplies either one faithful irreducible, using the
published Zmud input, or an explicit embedding in a binary plane. The
latter supplies two binary linear characters. Both constructions keep
the original quotient and the actual direct tower kernel.

The binary-plane embedding is a group-theoretic input, not an assumed
character-feasibility statement. No assertion about which literal tops
satisfy the alternative is made in this module.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairTowerCyclicPrefix

abbrev BinaryPlane := Fin 2 → Multiplicative (ZMod 2)

/-- The two concrete quotient alternatives needed by the paired-six
branch. The second clause has an actual faithful binary-plane map. -/
def TopAlternative (B : Type) [Group B] : Prop :=
  SocleNormalGeneratorBound B 1 ∨
    ∃ f : B →* BinaryPlane, Function.Injective f

variable {Q B : Type} [Group Q] [Finite Q] [Group B] [Finite B]

def binaryCoordinate (f : B →* BinaryPlane) (i : Fin 2) : B →* ℂˣ :=
  (binaryScalarSign (k := ℂ)).toHomUnits.comp
    ((Pi.evalMonoidHom (fun _ : Fin 2 ↦ Multiplicative (ZMod 2)) i).comp f)

omit [Finite Q] [Finite B] in
theorem binaryCoordinate_eq_one_iff (f : B →* BinaryPlane)
    (i : Fin 2) (b : B) : binaryCoordinate f i b = 1 ↔ f b i = 1 := by
  constructor
  · intro h
    exact (binaryScalarSign_eq_one (k := ℂ) _).mp
      (congrArg (fun z : ℂˣ ↦ (z : ℂ)) h)
  · intro h
    apply Units.ext
    change binaryScalarSign (k := ℂ) (f b i) = 1
    rw [h, map_one]

omit [Finite Q] [Finite B] in
theorem binaryCoordinate_isPGroup (f : B →* BinaryPlane) (i : Fin 2) :
    IsPGroup 2 (binaryCoordinate f i).range := by
  rintro ⟨z, b, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  change binaryCoordinate f i b ^ 2 = 1
  apply Units.ext
  change (binaryScalarSign (k := ℂ) (f b i)) ^ 2 = 1
  rw [← map_pow]
  have h : (f b i) ^ 2 = 1 := by
    have htwo : ∀ x : Multiplicative (ZMod 2), x ^ 2 = 1 := by decide +kernel
    exact htwo _
  rw [h, map_one]

/-- Inflate the two faithful binary coordinates. Their common kernel is
exactly the displayed quotient kernel, which may be nonabelian. -/
def ofBinaryPlane
    (pi : Q →* B) (f : B →* BinaryPlane) (hf : Function.Injective f)
    (hkernel : IsPGroup 2 pi.ker)
    (hcap : representationSchurCapacity
      (finiteRepresentationSocle
        (binaryKernelOmegaConjugationRepresentation pi)).toRepresentation ≤ 3) :
    DegreeTwoPairRelativeKernelOrbitInput Q
      (degreeTwoPairRelativeProfile 2 0 0 3) := by
  let binary : Fin 2 → Q →* ℂˣ := fun i ↦ (binaryCoordinate f i).comp pi
  apply DegreeTwoPairRelativeKernelOrbitInput.ofSocleSchurCapacity pi binary
    (fun i ↦ (binaryCoordinate_isPGroup f i).to_le (by
      rintro z ⟨q, rfl⟩
      exact ⟨pi q, rfl⟩)) Fin.elim0 Fin.elim0 _ hkernel
    (by simpa using hcap)
  ext q
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker]
  constructor
  · intro hq
    refine ⟨⟨?_, fun i ↦ Fin.elim0 i⟩, fun i ↦ Fin.elim0 i⟩
    intro i
    change binaryCoordinate f i (pi q) = 1
    rw [hq, map_one]
  · rintro ⟨⟨hbinary, _⟩, _⟩
    apply hf
    ext i
    have hi : binaryCoordinate f i (pi q) = 1 := hbinary i
    simpa only [map_one, Pi.one_apply] using
      (binaryCoordinate_eq_one_iff f i (pi q)).mp hi

variable {s t : ℕ} {D : DegreeTwoPairTopFiniteInterface t}
  (uniform : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)) 1)
  {p : PreE7PairActionClass s} (R : DegreeTwoPairTopTowerRealization D p)

include uniform in
/-- The ordinary branch requires one normal generator of the actual last
top quotient's socle, and no capacity premise from the row producer. -/
def ordinary (hZmud : ZmudFaithfulCharacterTupleInput)
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (htop : SocleNormalGeneratorBound (D.top ⧸ R.topNormal N.1) 1) :
    DegreeTwoPairRelativeKernelOrbitInput (preE7PairAction s p ⧸ N.1)
      (degreeTwoPairRelativeProfile 0 0 1 3) :=
  DegreeTwoPairRelativeKernelOrbitInput.ofSurjectiveBinaryKernelSocleSchurCapacity
    hZmud (R.rawQuotientMap N) (R.rawQuotientMap_surjective N) htop
    (R.rawQuotientMap_kernel_isPGroup N)
    (by
      simpa using DegreeTwoPairTowerCyclicCapacity.omegaSocle_capacity_le_three
        uniform R N)

include uniform in
/-- The binary-plane branch consumes an actual quotient embedding. The
three relative positions follow from the cyclic natural-module theorem. -/
def twoBinary
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (f : (D.top ⧸ R.topNormal N.1) →* BinaryPlane)
    (hf : Function.Injective f) :
    DegreeTwoPairRelativeKernelOrbitInput (preE7PairAction s p ⧸ N.1)
      (degreeTwoPairRelativeProfile 2 0 0 3) :=
  ofBinaryPlane (R.rawQuotientMap N) f hf
    (R.rawQuotientMap_kernel_isPGroup N)
    (DegreeTwoPairTowerCyclicCapacity.omegaSocle_capacity_le_three uniform R N)

end DegreeTwoPairTowerCyclicPrefix
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
