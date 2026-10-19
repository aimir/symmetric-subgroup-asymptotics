import SymmetricSubgroupAsymptotics.AlternatingEdgeOriginalSocleCoinvariance
import SymmetricSubgroupAsymptotics.AlternatingEdgeActualProjectorRanks

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AlternatingEdgeOriginalProjectorHeads
open AlternatingEdgeBinaryProjectors
open OriginalKernelModuleChart

abbrev Top := alternatingGroup (Fin 4)
def a : Top := ⟨FourPointAlternatingGeneratorCover.a, by change Equiv.Perm.sign _ = 1; decide +kernel⟩
def t (d : Fin 3) : Top := ⟨klein d, by change Equiv.Perm.sign _ = 1; revert d; decide +kernel⟩
def beta : Representation (ZMod 2) Top Vector := rho.comp (alternatingGroup (Fin 4)).subtype
private theorem t_mem : ∀ d, t d ∈ alternatingGroup.kleinFour (Fin 4) := by
  intro d
  rw [← NaturalA4ScalarFourHead.top_ker]
  change NaturalA4ScalarFourHead.top (t d)=1
  revert d
  decide +kernel

theorem projector_heads {G : Type} [Group G]
    (pi : G →* Top) (hpi : Function.Surjective pi)
    (B : Rep.{0} (ZMod 2) Top) (E : OriginalKernelModuleChart pi B)
    (j : Representation.IntertwiningMap B.ρ beta) (hj : Function.Injective j)
    (N : Subgroup G) [N.Normal] :
    let tau := (E.sectionRepresentation pi B N).ρ.comp (sectionTop pi N hpi)
    a^3=1 ∧
      Module.finrank (ZMod 2) (LinearMap.range (1+tau a+(tau a)^2)) ≤ 2 ∧
      Module.finrank (ZMod 2) (LinearMap.range (tau a+(tau a)^2)) ≤ 4 ∧
      (finiteGroupSocle (G ⧸ N) ≤ (base pi N).ker ∨
        Module.finrank (ZMod 2) (LinearMap.range (tau a+(tau a)^2)) ≤ 2) := by
  letI : Finite B := Finite.of_injective j hj
  letI : FiniteDimensional (ZMod 2) (E.sectionModule pi B N) := inferInstance
  letI : FiniteDimensional (ZMod 2) (E.sectionRepresentation pi B N) := by
    change FiniteDimensional (ZMod 2) (E.sectionModule pi B N)
    infer_instance
  let tau := (E.sectionRepresentation pi B N).ρ.comp (sectionTop pi N hpi)
  let q := E.sectionProjectionOnBase pi B N hpi
  have hq : Function.Surjective q := E.sectionProjectionOnBase_surjective pi B N hpi
  have hfull := AlternatingEdgeActualProjectorRanks.section_ranks beta a (fun _ => rfl)
    tau B.ρ j hj q hq
  refine ⟨by decide +kernel,hfull.1,hfull.2,?_⟩
  rcases AlternatingEdgeOriginalSocleCoinvariance.dichotomy pi hpi B E N with hi | hc
  · exact Or.inl hi
  · right
    have hqt : ∀ d, tau (t d)=1 := by
      intro d
      exact congrArg Units.val (hc (t_mem d))
    exact AlternatingEdgeActualSectionHead.section_active beta a t (fun _ => rfl)
      (fun _ _ => rfl) tau B.ρ j hj q hq hqt

end SymmetricSubgroupAsymptotics.AlternatingEdgeOriginalProjectorHeads
