import SymmetricSubgroupAsymptotics.CentralFourS5ProjectiveChiefData
import SymmetricSubgroupAsymptotics.StandardGLTwoFiveKernelCharacter
import SymmetricSubgroupAsymptotics.PrimitiveAffineTwentyFiveLinearEmbedding
import SymmetricSubgroupAsymptotics.PrimitiveAffinePublishedSmallStructuralInput

/-! Construct the legacy degree25 data from ordinary Burnside solvability
and the standard PGL2(F5)=S5 isomorphism. Both legacy capacity fields are
proved from the SAME actual complement embedding and projective map. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.DegreeTwentyFiveActualProjectiveData
open Non2UnipotentPrefixFiniteMenu StandardGLTwoFiveProjective
variable {G : Type} [Group G] [Finite G]

def projectiveMap (h : PublishedProjectiveIsomorphism) (phi : G →* LinearFive) :
    G →* Equiv.Perm (Fin 5) := (projective h).comp phi

private def kernelMap (h : PublishedProjectiveIsomorphism) (phi : G →* LinearFive) :
    (projectiveMap h phi).ker →* (projective h).ker where
  toFun x := ⟨phi x,x.property⟩
  map_one' := Subtype.ext phi.map_one
  map_mul' x y := Subtype.ext (phi.map_mul x y)

private theorem kernelMap_injective (h : PublishedProjectiveIsomorphism)
    (phi : G →* LinearFive) (hphi : Function.Injective phi) :
    Function.Injective (kernelMap h phi) := by
  intro x y hxy
  apply Subtype.ext
  apply hphi
  exact congrArg Subtype.val hxy

private theorem central_kernel (h : PublishedProjectiveIsomorphism)
    (phi : G →* LinearFive) (hphi : Function.Injective phi) :
    ∀ z ∈ (projectiveMap h phi).ker,∀ x : G,z*x=x*z := by
  intro z hz x
  apply hphi
  rw [map_mul,map_mul]
  have hc : phi z ∈ Subgroup.center LinearFive := projective_kernel_central h hz
  exact (Subgroup.mem_center_iff.mp hc (phi x)).symm

def solubleDatum (h : PublishedProjectiveIsomorphism)
    (phi : G →* LinearFive) (hphi : Function.Injective phi) (hG : IsSolvable G) :
    CentralFourQuotientDatum G :=
  CentralFourS5ProjectiveChiefData.solubleDatum (projectiveMap h phi)
    (central_kernel h phi hphi) ((kernelCharacter h).comp (kernelMap h phi))
    ((kernelCharacter_injective h).comp (kernelMap_injective h phi hphi)) hG

theorem nonsolubleTrace (B : PublishedBurnsideTwoPrimeSolvabilityInput)
    (h : PublishedProjectiveIsomorphism) (phi : G →* LinearFive)
    (hphi : Function.Injective phi) (hG : ¬ IsSolvable G)
    (T : FixedTargetCompositionTrace G) : T.envelope.abelianLength ≤ 3 := by
  have hc : Nat.card G ∣ 480 := by
    rw [← card_linearFive]
    exact Subgroup.card_dvd_of_injective phi hphi
  exact CentralFourS5ProjectiveChiefData.nonsolubleTrace B (projectiveMap h phi)
    (central_kernel h phi hphi) hc hG T

/-- The external inputs are ordinary group theorems, never a chief budget. -/
def publishedDegreeTwentyFiveLinearData
    (B : PublishedBurnsideTwoPrimeSolvabilityInput) (h : PublishedProjectiveIsomorphism) :
    PublishedDegreeTwentyFiveLinearData where
  solubleProjective U P hprimitive x hG :=
    solubleDatum h (P.complementLinearMap_degreeTwentyFive hprimitive x)
      (P.complementLinearMap_degreeTwentyFive_injective hprimitive x) hG
  nonsolubleComposition U P hprimitive x T hG :=
    nonsolubleTrace B h (P.complementLinearMap_degreeTwentyFive hprimitive x)
      (P.complementLinearMap_degreeTwentyFive_injective hprimitive x) hG T

end SymmetricSubgroupAsymptotics.DegreeTwentyFiveActualProjectiveData
