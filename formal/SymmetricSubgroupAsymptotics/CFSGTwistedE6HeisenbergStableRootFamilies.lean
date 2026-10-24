import SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergRootPilot
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRootSubgroupTwist
import SymmetricSubgroupAsymptotics.CFSGTwistedE6WeylChamber

/-! The actual twenty-one-root E6 Heisenberg configuration admits two
commuting complementary families which are separately diagram-stable.
Only pairs 8 and 9 are reversed.  The resulting literal root-subgroup
join is stable under every actual diagram--field matrix twist.  No
fixed-point surjectivity or descended commutator pairing is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergStableRootFamilies
open CFSGExceptionalHeisenbergRootPilot CFSGNormTwoRootPairing
open CFSGExceptionalCartanPositiveDefinite CFSGTwistedE6WeylChamber
open CFSGTwistedE6GeckRootSubgroupTwist CFSGTwistedE6GeckMatrixTwist
open CFSGNormTwoCoordinateRootSubgroup
open CFSGSerreDiagram

private def first (i : Fin 10) : Fin 6 → ℤ :=
  if i.val = 8 ∨ i.val = 9 then E6.y i else E6.x i
private def second (i : Fin 10) : Fin 6 → ℤ :=
  if i.val = 8 ∨ i.val = 9 then E6.x i else E6.y i

def configuration : RootConfig CartanMatrix.E₆ 10 where
  x := first
  y := second
  z := E6.z
  head := E6.head
  norm_x := by decide
  norm_y := by decide
  norm_z := E6.norm_z
  positive_x := by decide
  positive_y := by decide
  positive_z := E6.positive_z
  injective := by decide
  grade_x := by decide
  grade_y := by decide
  grade_z := E6.grade_z
  sum := by decide
  paired := by decide
  within_x := by decide
  within_y := by decide
  cross := by decide
  central_x := by decide
  central_y := by decide

def partner : Equiv.Perm (Fin 10) :=
  Equiv.ofBijective (![0,1,4,9,2,5,8,7,6,3] : Fin 10 → Fin 10) (by decide)

theorem partner_involutive : Function.Involutive partner := by
  intro i
  fin_cases i <;> decide

private theorem diagram_inverse (j : Fin 6) : e6Permutation.symm j = e6Permutation j := by
  have hh : e6Permutation (e6Permutation j) = j := by fin_cases j <;> rfl
  apply e6Permutation.injective
  rw [e6Permutation.apply_symm_apply, hh]

theorem diagram_first (i : Fin 10) :
    diagramRoot (configuration.xRoot i).val = (configuration.xRoot (partner i)).val := by
  apply Subtype.ext
  funext j
  change first i (e6Permutation.symm j) = first (partner i) j
  rw [diagram_inverse]
  fin_cases i <;> fin_cases j <;> decide

theorem diagram_second (i : Fin 10) :
    diagramRoot (configuration.yRoot i).val = (configuration.yRoot (partner i)).val := by
  apply Subtype.ext
  funext j
  change second i (e6Permutation.symm j) = second (partner i) j
  rw [diagram_inverse]
  fin_cases i <;> fin_cases j <;> decide

theorem diagram_central : diagramRoot configuration.zRoot.val = configuration.zRoot.val := by
  apply Subtype.ext
  funext j
  change E6.z (e6Permutation.symm j) = E6.z j
  rw [diagram_inverse]
  fin_cases j <;> decide

abbrev rootLine (K : Type) [Field K] (k : Roots CartanMatrix.E₆) :=
  rootSubgroup CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k

def firstGroup (K : Type) [Field K] := ⨆ i : Fin 10, rootLine K (configuration.xRoot i).val
def secondGroup (K : Type) [Field K] := ⨆ i : Fin 10, rootLine K (configuration.yRoot i).val
def centralGroup (K : Type) [Field K] := rootLine K configuration.zRoot.val
def heisenbergGroup (K : Type) [Field K] := firstGroup K ⊔ secondGroup K ⊔ centralGroup K

private theorem reindex_subgroups {G : Type*} [Group G] {I : Type*}
    (p : Equiv.Perm I) (F : I → Subgroup G) : (⨆ i, F (p i)) = ⨆ i, F i :=
  Equiv.iSup_comp (g := F) p

theorem firstGroup_twist (K : Type) [Field K] (sigma : K ≃+* K) :
    (firstGroup K).map (unitTwist K sigma).toMonoidHom = firstGroup K := by
  calc
    (firstGroup K).map (unitTwist K sigma).toMonoidHom =
        ⨆ i : Fin 10, (rootLine K (configuration.xRoot i).val).map
          (unitTwist K sigma).toMonoidHom := Subgroup.map_iSup _ _
    _ =
      (⨆ i : Fin 10, rootLine K (configuration.xRoot (partner i)).val) := by
      congr 1
      funext i
      exact (root_subgroup_twist K sigma (configuration.xRoot i).val).trans
        (congrArg (rootLine K) (diagram_first i))
    _ = ⨆ i : Fin 10, rootLine K (configuration.xRoot i).val :=
      reindex_subgroups partner (fun i : Fin 10 => rootLine K (configuration.xRoot i).val)

theorem secondGroup_twist (K : Type) [Field K] (sigma : K ≃+* K) :
    (secondGroup K).map (unitTwist K sigma).toMonoidHom = secondGroup K := by
  calc
    (secondGroup K).map (unitTwist K sigma).toMonoidHom =
        ⨆ i : Fin 10, (rootLine K (configuration.yRoot i).val).map
          (unitTwist K sigma).toMonoidHom := Subgroup.map_iSup _ _
    _ =
      (⨆ i : Fin 10, rootLine K (configuration.yRoot (partner i)).val) := by
      congr 1
      funext i
      exact (root_subgroup_twist K sigma (configuration.yRoot i).val).trans
        (congrArg (rootLine K) (diagram_second i))
    _ = ⨆ i : Fin 10, rootLine K (configuration.yRoot i).val :=
      reindex_subgroups partner (fun i : Fin 10 => rootLine K (configuration.yRoot i).val)

theorem centralGroup_twist (K : Type) [Field K] (sigma : K ≃+* K) :
    (centralGroup K).map (unitTwist K sigma).toMonoidHom = centralGroup K := by
  exact (root_subgroup_twist K sigma configuration.zRoot.val).trans
    (congrArg (rootLine K) diagram_central)

theorem heisenbergGroup_twist (K : Type) [Field K] (sigma : K ≃+* K) :
    (heisenbergGroup K).map (unitTwist K sigma).toMonoidHom = heisenbergGroup K := by
  calc
    (heisenbergGroup K).map (unitTwist K sigma).toMonoidHom =
        (firstGroup K ⊔ secondGroup K).map (unitTwist K sigma).toMonoidHom ⊔
          (centralGroup K).map (unitTwist K sigma).toMonoidHom := Subgroup.map_sup _ _ _
    _ = ((firstGroup K).map (unitTwist K sigma).toMonoidHom ⊔
          (secondGroup K).map (unitTwist K sigma).toMonoidHom) ⊔
          (centralGroup K).map (unitTwist K sigma).toMonoidHom :=
      congrArg (fun J => J ⊔ (centralGroup K).map (unitTwist K sigma).toMonoidHom)
        (Subgroup.map_sup _ _ _)
    _ = heisenbergGroup K := by
      rw [firstGroup_twist, secondGroup_twist, centralGroup_twist]
      rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergStableRootFamilies
