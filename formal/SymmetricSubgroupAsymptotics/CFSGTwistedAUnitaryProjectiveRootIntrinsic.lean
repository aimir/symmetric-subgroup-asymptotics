import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryProjectiveRootLabels
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOriginalSylow
import SymmetricSubgroupAsymptotics.CFSGInjectiveCenterImage

/-! The projective central-root family is intrinsic: its base subgroup
is the actual centre of the literal projective Sylow. The natural
parameter subgroup and the original projective Sylow are related by
the proved injective map, not by a model-name identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent

def unitaryProjectiveUpperHom (q : CFSG.PrimePower) (s : ℕ) :
    naturalUnipotent (s + 3) q →* CFSG.Models.TwistedA (s + 3) q :=
  (unitaryProjectiveCover q s).comp (upperFixedHom q (s + 3))

theorem unitaryProjectiveUpperHom_injective (q : CFSG.PrimePower) (s : ℕ) :
    Function.Injective (unitaryProjectiveUpperHom q s) := by
  intro u v he
  have hp (a : naturalUnipotent (s + 3) q) :
      ∃ n : ℕ, upperFixedHom q (s + 3) a ^ (q.prime ^ n) = 1 := by
    obtain ⟨n, hn⟩ := naturalUnipotent_isPGroup (s + 3) q a
    exact ⟨n, by simpa only [map_pow, map_one] using congrArg (upperFixedHom q (s + 3)) hn⟩
  have hh := unitaryProjectiveCover_eq_of_p_powers q s
    (upperFixedHom q (s + 3) u) (upperFixedHom q (s + 3) v) (hp u) (hp v) he
  apply Subtype.ext
  exact congrArg (fun a : naturalFixed (s + 3) q => a.val) hh

theorem projectiveCentralRootLine_eq_intrinsic_center (q : CFSG.PrimePower) (s : ℕ) :
    projectiveCentralRootLine q s =
      (Subgroup.center (unitaryProjectiveUpperHom q s).range).map
        (unitaryProjectiveUpperHom q s).range.subtype := by
  change (naturalCentralRootLine q (s + 1)).map (unitaryProjectiveCover q s) = _
  rw [naturalCentralRootLine_eq_center_image, Subgroup.map_map]
  exact CFSGInjectiveCenterImage.center_image (unitaryProjectiveUpperHom q s)
    (unitaryProjectiveUpperHom_injective q s)

def unitaryProjectiveSylow (q : CFSG.PrimePower) (s : ℕ) :
    Sylow q.prime (CFSG.Models.TwistedA (s + 3) q) := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  letI : Finite (Fixed (s + 3) q) := originalFixed_finite q (s + 3) (by omega)
  exact ((originalSylow q (s + 3) (by omega)).subtype (originalSylow_le_derived q s)).mapSurjective
    (QuotientGroup.mk'_surjective (Subgroup.center (commutator (Fixed (s + 3) q))))

theorem unitaryProjectiveSylow_coe (q : CFSG.PrimePower) (s : ℕ) :
    (unitaryProjectiveSylow q s : Subgroup (CFSG.Models.TwistedA (s + 3) q)) =
      (unitaryProjectiveUpperHom q s).range := by
  ext x
  change (∃ d : commutator (Fixed (s + 3) q),
    d.val ∈ originalUnipotent (s + 3) q ∧ QuotientGroup.mk' _ d = x) ↔
      x ∈ (unitaryProjectiveUpperHom q s).range
  constructor
  · rintro ⟨d, hd, rfl⟩
    change d.val ∈ originalUnipotent (s + 3) q at hd
    obtain ⟨u, hu⟩ := hd
    refine ⟨u, ?_⟩
    change QuotientGroup.mk' _ (originalDerivedCover q s (upperFixedHom q (s + 3) u)) =
      QuotientGroup.mk' _ d
    congr 1
    exact Subtype.ext hu
  · rintro ⟨u, rfl⟩
    refine ⟨originalDerivedCover q s (upperFixedHom q (s + 3) u), ?_, rfl⟩
    change (originalDerivedCover q s (upperFixedHom q (s + 3) u)).val ∈
      originalUnipotent (s + 3) q
    exact ⟨u, rfl⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
