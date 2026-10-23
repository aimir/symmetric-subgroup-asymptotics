import SymmetricSubgroupAsymptotics.CFSGE6GeckOrbitRootIntersection
import SymmetricSubgroupAsymptotics.CFSGE6GeckFixedPairChart
import SymmetricSubgroupAsymptotics.CFSGE6GeckFixedSimpleParameters

/-! Fixed points of the orbit-zero positive root groups are precisely
the already constructed singleton/paired fixed parameter charts. This
identifies the groups, rather than assuming a chart exhausts a fixed
subgroup. No folded abelianization assertion occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckFixedOrbitRootGroups
open CFSGE6GeckOrbitRootIntersection CFSGE6GeckFixedPairChart
open CFSGE6GeckFixedSimpleParameters CFSGE6GeckOrthogonalPairChart
open CFSGE6GeckSignedSimpleParameters CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6RelativeWeylOrbits CFSGTwistedE6PairedFixedRoots
open CFSGTwistedE6FixedA2 CFSGSerreQuadraticMatrix

def pairedOrbit (j : Fin 2) : Fin 4 := ⟨j.val,by omega⟩
def singletonOrbit (j : Fin 2) : Fin 4 := ![3,2] j

private theorem orbitGroup_pair_word (K : Type) [Field K] (a : Fin 4) (i j : Fin 6)
    (hw : orbitWord a=[i,j]) :
    orbitPositiveGroup K a=canonicalRootSubgroup rawData K false i⊔
      canonicalRootSubgroup rawData K false j := by
  apply le_antisymm
  · apply iSup_le
    intro k
    apply iSup_le
    intro hk
    rw [hw] at hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl
    · exact le_sup_left
    · exact le_sup_right
  · apply sup_le
    · exact le_iSup_of_le i (le_iSup_of_le (by rw [hw];simp) le_rfl)
    · exact le_iSup_of_le j (le_iSup_of_le (by rw [hw];simp) le_rfl)

private theorem orbitGroup_single_word (K : Type) [Field K] (a : Fin 4) (i : Fin 6)
    (hw : orbitWord a=[i]) : orbitPositiveGroup K a=canonicalRootSubgroup rawData K false i := by
  apply le_antisymm
  · apply iSup_le
    intro k
    apply iSup_le
    intro hk
    rw [hw,List.mem_singleton] at hk
    subst k
    exact le_rfl
  · exact le_iSup_of_le i (le_iSup_of_le (by rw [hw];simp) le_rfl)

theorem orbitPositiveGroup_paired (K : Type) [Field K] (j : Fin 2) :
    orbitPositiveGroup K (pairedOrbit j)=canonicalRootSubgroup rawData K false (pairedNode j)⊔
      canonicalRootSubgroup rawData K false (pairedPartner j) := by
  apply orbitGroup_pair_word
  fin_cases j <;> rfl

theorem orbitPositiveGroup_singleton (K : Type) [Field K] (j : Fin 2) :
    orbitPositiveGroup K (singletonOrbit j)=canonicalRootSubgroup rawData K false (node j) := by
  apply orbitGroup_single_word
  fin_cases j <;> rfl

def fixedOrbitPositive (K : Type) [Field K] (sigma : K≃+*K) (a : Fin 4) :
    Subgroup (signedFixed K sigma false) := (orbitPositiveGroup K a).subgroupOf (signedFixed K sigma false)

theorem fixedOrbitPositive_paired (K : Type) [Field K] (sigma : K≃+*K)
    (hsigma : Function.Involutive sigma) (j : Fin 2) :
    fixedOrbitPositive K sigma (pairedOrbit j)=(pairedFixedHom K sigma hsigma false j).range := by
  apply Subgroup.ext
  intro g
  constructor
  · intro hg
    have hj : g.val∈canonicalRootSubgroup rawData K false (pairedNode j)⊔
        canonicalRootSubgroup rawData K false (pairedPartner j) := by
      change g.val∈orbitPositiveGroup K (pairedOrbit j) at hg
      rwa [orbitPositiveGroup_paired] at hg
    obtain ⟨a,ha⟩ := exists_paired_parameter_of_fixed K sigma hsigma false j g.val hj g.property.2
    exact ⟨Multiplicative.ofAdd a,Subtype.ext ha.symm⟩
  · rintro ⟨a,rfl⟩
    change rawPairedHom K sigma false j a∈orbitPositiveGroup K (pairedOrbit j)
    rw [orbitPositiveGroup_paired,←rawPairHom_range]
    exact ⟨(a,Multiplicative.ofAdd (sigma a.toAdd)),rfl⟩

theorem fixedOrbitPositive_singleton (K : Type) [Field K] (sigma : K≃+*K) (j : Fin 2) :
    fixedOrbitPositive K sigma (singletonOrbit j)=(singletonFixedHom K sigma false j).range := by
  apply Subgroup.ext
  intro g
  constructor
  · intro hg
    have hj : g.val∈canonicalRootSubgroup rawData K false (node j) := by
      change g.val∈orbitPositiveGroup K (singletonOrbit j) at hg
      rwa [orbitPositiveGroup_singleton] at hg
    obtain ⟨a,ha⟩ := hj
    have hfix : unitTwist K sigma (canonicalRoot rawData K false (node j) a)=
        canonicalRoot rawData K false (node j) a := by
      rw [ha]
      exact g.property.2
    have haFix := (singleton_fixed_iff K sigma false j a).mp hfix
    let af : fixedCoefficient K sigma := ⟨a,haFix⟩
    exact ⟨Multiplicative.ofAdd af,Subtype.ext ha⟩
  · rintro ⟨a,rfl⟩
    change rawSingletonHom K false j (Multiplicative.ofAdd (a.toAdd : K))∈
      orbitPositiveGroup K (singletonOrbit j)
    rw [orbitPositiveGroup_singleton]
    exact ⟨(a.toAdd : K),rfl⟩

end SymmetricSubgroupAsymptotics.CFSGE6GeckFixedOrbitRootGroups
