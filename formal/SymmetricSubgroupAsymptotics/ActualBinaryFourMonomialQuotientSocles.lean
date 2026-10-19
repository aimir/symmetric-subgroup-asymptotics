import SymmetricSubgroupAsymptotics.CubicKernelSingleTopQuotientSocleProfile
import SymmetricSubgroupAsymptotics.PGroupOriginalSocleRelativeHeads
import SymmetricSubgroupAsymptotics.TernaryFourMonomialUniform
import SymmetricSubgroupAsymptotics.LinearSemidirectActualImageKernelChart

/-! Correlated ternary affine subgroups over an actual signed binary top.
Actual top relative heads and transitive four-coordinate action suffice;
no full translation subgroup or split original extension is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualBinaryFourMonomialQuotientSocles
open LinearSemidirectSubgroupKernelChart
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {R : Type} [Group R] [Finite R]
    (b : R →* Equiv.Perm (Fin 4)) (d : R → Fin 4 → ZMod 3)
    (h1 : ∀ i,d 1 i=1)
    (hm : ∀ g h i,d (g*h) i=d g i*d h (b g⁻¹ i))

abbrev rho := TernaryMonomialCocycle.linearAction b d h1 hm

 theorem quotientSocle (K : Subgroup (LinearSemidirectCoprimeSocleBounds.Model (rho b d h1 hm)))
    (hp : IsPGroup 2 (Image (rho b d h1 hm) K))
    (hhead : ∀ L : {L : Subgroup (Image (rho b d h1 hm) K) // L.Normal},
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 L.1)≤2)
    (htrans : ∀ x y : Fin 4,∃ g : Image (rho b d h1 hm) K,b g.val x=y)
    (N : Subgroup K) [N.Normal] : SocleNormalGeneratorBound (K ⧸ N) 2 := by
  let r := rho b d h1 hm
  let A := LinearSemidirectActualImageKernelChart.kernelModule r K
  let E := LinearSemidirectActualImageKernelChart.originalKernelChart r K
  let pi := LinearSemidirectActualImageKernelChart.top r K
  letI : FiniteDimensional (ZMod 3) A := by
    change FiniteDimensional (ZMod 3) (translationSpace r K)
    infer_instance
  have huFull : UniformSubrepresentationGeneratorBound (imageRepresentation r K) 1 := by
    change UniformSubrepresentationGeneratorBound
      (TernaryMonomialOrbitUniform.representation
        (b.comp (Image r K).subtype) (fun g => d g.val)
        (fun i => h1 i) (fun g h i => hm g.val h.val i)) 1
    exact TernaryFourMonomialUniform.uniform _ _ _ _ htrans
  have hu : UniformSubrepresentationGeneratorBound A.ρ 1 :=
    huFull.of_injective (LinearSemidirectActualImageKernelChart.inclusion r K)
      (LinearSemidirectActualImageKernelChart.inclusion_injective r K)
  letI : Group.IsNilpotent (Image r K) := hp.isNilpotent
  letI : IsSolvable pi.ker := solvable_of_solvable_injective (f := E.equiv.symm.toMonoidHom) E.equiv.symm.injective
  letI : IsSolvable K := solvable_of_ker_le_range pi.ker.subtype pi
    (by rw [Subgroup.range_subtype])
  obtain ⟨a,ha⟩ := hp.exists_card_eq
  have hc : Nat.card (Image r K)∣2^a*3 := by rw [ha]; exact dvd_mul_right _ _
  apply CubicKernelSingleTopQuotientSocleProfile.quotientSocle pi
    (projection r K).rangeRestrict_surjective A E hu a hc ?_ N
  intro L hL
  letI := hL
  exact PGroupOriginalSocleRelativeHeads.quotientSocle 2 hp 2 hhead L
end SymmetricSubgroupAsymptotics.ActualBinaryFourMonomialQuotientSocles
