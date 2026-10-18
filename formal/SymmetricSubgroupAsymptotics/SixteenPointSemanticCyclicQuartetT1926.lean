import SymmetricSubgroupAsymptotics.SixteenPointSemanticCyclicQuartetProjectors
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoNonbinary16T1932QuotientSocles
import SymmetricSubgroupAsymptotics.OriginalSixteenPreE7Representative

/-! Exact correlated-odd-image pilot16T1926. Four short positive words
isolate the binary coordinates by three-term averaging. Neither the full
original group nor its normal subgroups are enumerated. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixteenPointSemanticCyclicQuartetT1926
open BinaryPlanePermutationWreathCoordinates
open BinaryPlaneWreathIrreducible BinaryPlaneWreathNormalGenerators
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoNonbinary16T1932QuotientSocles
  (Blocks Point Affine Lin localPerm blocks_cycle blocks_transitive blocks_coprime)

def generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,9,11,8,10,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,10,8,11,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,3,2,0,1,7,5,6,4,11,8,10,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,11,9,10,8,13,15,14,12,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 2 → Equiv.Perm (Fin 16) := ![generator0,generator1]
abbrev Original := Subgroup.closure (Set.range generators)

def localPermutations (j : Fin 2) (i : Fin 4) : Equiv.Perm (Fin 4) where
  toFun x := (![![![1,0,3,2],![1,0,3,2],![1,3,0,2],![3,2,0,1]],![![3,2,0,1],![3,1,2,0],![3,0,2,1],![2,3,0,1]]] : Fin 2 → Fin 4 → Fin 4 → Fin 4) j i x
  invFun x := (![![![1,0,3,2],![1,0,3,2],![2,0,3,1],![2,3,1,0]],![![2,3,1,0],![3,1,2,0],![1,3,2,0],![2,3,0,1]]] : Fin 2 → Fin 4 → Fin 4 → Fin 4) j i x
  left_inv := by intro x; revert j i x; decide +kernel
  right_inv := by intro x; revert j i x; decide +kernel

def pointLifts (j : Fin 2) : Point :=
  ⟨fun i => localPerm (localPermutations j i),![1,PrimitiveAffineDegreeTwoNonbinary16T1932QuotientSocles.rotation⁻¹] j⟩
def lifted (j : Fin 2) : Affine := coordinates (pointLifts j)
abbrev K := Subgroup.closure (Set.range lifted)
abbrev C := actualImage K

theorem bindings (j : Fin 2) : PrimitiveAffineDegreeTwoNonbinary16T1932QuotientSocles.action (lifted j) = generators j := by
  apply Equiv.ext; intro x; revert j x; decide +kernel

def linearGenerator (j : Fin 2) : C :=
  ⟨(lifted j).right,⟨closureGenerators lifted j,rfl⟩⟩

def projectorWords (i : Fin 4) : List (Fin 2) :=
  (#[[0,1,0,1,0,1,1,1,1,1,0,1],[0,1,0,1,1,1,1,1,0,1,0,1],[0,1,1,1,1,1,0,1,0,1,0,1],[0,1,0,1,0,1,0,1,1,1,1,1]] : Array (List (Fin 2)))[i.val]!

def projector (i : Fin 4) : C := ((projectorWords i).map linearGenerator).prod

def localMover (i : Fin 4) : C :=
  projector (i+1)

theorem mover_top (i : Fin 4) : (localMover i : Lin).right = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro j
  revert i j
  decide +kernel

theorem local_orbit (i : Fin 4) (u v : V) (hu : u ≠ 1) (hv : v ≠ 1) :
    ∃ n : Fin 3, localAction ((((localMover i)^n.val : C) : Lin).left i) u = v := by
  revert i u v hu hv
  decide +kernel

theorem local_orbit_single (i : Fin 4) (u v : V) (hu : u ≠ 1) (hv : v ≠ 1) :
    ∃ g : C, restrictedAction C g (Pi.mulSingle i u) = Pi.mulSingle i v := by
  obtain ⟨n,hn⟩ := local_orbit i u v hu hv
  refine ⟨(localMover i)^n.val,?_⟩
  change BinaryPlaneWreathIrreducible.action (((localMover i)^n.val : C) : Lin) (Pi.mulSingle i u) = _
  rw [action_single]
  have ht : (((localMover i)^n.val : C) : Lin).right = 1 := by
    have hm := map_pow (PermutationalWreathProduct.rightHom.comp C.subtype) (localMover i) n.val
    change (((localMover i)^n.val : C) : Lin).right =
      (localMover i : Lin).right^n.val at hm
    rw [mover_top,one_pow] at hm
    exact hm
  rw [ht,one_smul,hn]

theorem projector_top (i : Fin 4) : (projector i : Lin).right = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro j
  revert i j
  decide +kernel

theorem projector_coordinate : ∀ (i j : Fin 4) (v : V),
    v * localAction ((projector i : Lin).left j) v *
      localAction ((((projector i)^2 : C) : Lin).left j) v =
        if j=i then v else 1 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem projection (i : Fin 4) (v : Fin 4 → V) :
    v * restrictedAction C (projector i) v *
      restrictedAction C ((projector i)^2) v = Pi.mulSingle i (v i) := by
  funext j
  change v j * localAction ((projector i : Lin).left j)
    (v ((projector i : Lin).right⁻¹ • j)) *
    localAction ((((projector i)^2 : C) : Lin).left j)
      (v ((((projector i)^2 : C) : Lin).right⁻¹ • j)) = _
  have ht : (((projector i)^2 : C) : Lin).right = 1 := by
    have hm := map_pow (PermutationalWreathProduct.rightHom.comp C.subtype) (projector i) 2
    change (((projector i)^2 : C) : Lin).right =
      (projector i : Lin).right^2 at hm
    rw [projector_top,one_pow] at hm
    exact hm
  rw [projector_top,ht,inv_one,one_smul,projector_coordinate]
  by_cases hj : j=i
  · subst j; simp [Pi.mulSingle_eq_same]
  · simp only [if_neg hj,Pi.mulSingle_eq_of_ne hj]

def beta : C →* Blocks := PermutationalWreathProduct.rightHom.comp C.subtype

theorem beta_surjective : Function.Surjective beta := by
  have hi : PrimitiveAffineDegreeTwoNonbinary16T1932QuotientSocles.rotation⁻¹ ∈ beta.range := ⟨linearGenerator 1,rfl⟩
  have hr : PrimitiveAffineDegreeTwoNonbinary16T1932QuotientSocles.rotation ∈ beta.range := by simpa only [inv_inv] using beta.range.inv_mem hi
  intro r
  obtain ⟨z,hz⟩ := Subgroup.mem_zpowers_iff.mp r.property
  have he : PrimitiveAffineDegreeTwoNonbinary16T1932QuotientSocles.rotation^z=r := Subtype.ext hz
  rw [← he]
  exact beta.range.zpow_mem hr z

theorem transitiveImage (i j : Fin 4) : ∃ q : C, (q : Lin).right • i=j := by
  obtain ⟨r,hr⟩ := blocks_transitive i j
  obtain ⟨q,hq⟩ := beta_surjective r
  exact ⟨q,by change beta q • i=j; rw [hq,hr]⟩

def originalMap : K →* Original :=
  GeneratedLiteralImage.toTop (PrimitiveAffineDegreeTwoNonbinary16T1932QuotientSocles.action.comp K.subtype) (closureGenerators lifted)
    generators (Equiv.refl _) (closureGenerators_full lifted) bindings

theorem originalMap_surjective : Function.Surjective originalMap :=
  GeneratedLiteralImage.toTop_surjective (PrimitiveAffineDegreeTwoNonbinary16T1932QuotientSocles.action.comp K.subtype)
    (closureGenerators lifted) generators (Equiv.refl _)
    (closureGenerators_full lifted) bindings

def ambient (j : Fin 2) : Original :=
  ⟨generators j,Subgroup.subset_closure (Set.mem_range_self j)⟩

def pointWords (x : Fin 16) : List (Fin 2) :=
  (#[[],[0],[1,1,1,1,0],[1,1,1,0,1],[1,1,0,1],[1,1,1,0],[1,1,1],[1,0,1,1],[0,1,1],[1,1,0],[1,1],[1,0,1],[0,1],[0,1,0],[1],[1,0]] : Array (List (Fin 2)))[x.val]!

theorem pointWords_checked : ∀ x : Fin 16,
    ((pointWords x).map generators).prod (0 : Fin 16) = x := by decide +kernel

theorem transitive : MulAction.IsPretransitive Original (Fin 16) := by
  apply (MulAction.isPretransitive_iff_base (G := Original) (0 : Fin 16)).mpr
  intro x
  refine ⟨((pointWords x).map ambient).prod,?_⟩
  change (((pointWords x).map ambient).prod : Equiv.Perm (Fin 16)) 0=x
  simpa [Subgroup.val_list_prod,ambient] using pointWords_checked x

theorem nonbinary : ¬ IsPGroup 2 Original := by
  intro h
  let cubic : Original := (((projectorWords 0).map ambient).prod)^2
  have hc : cubic^3=1 := by apply Subtype.ext; decide +kernel
  have hn : cubic ≠ 1 := by
    intro he
    have hx := congrArg (fun g : Original => (g : Equiv.Perm (Fin 16)) 4) he
    have hh : ((((projectorWords 0).map generators).prod)^2) (4 : Fin 16) ≠ 4 := by decide +kernel
    exact hh hx
  apply hn
  apply (h.powEquiv (by decide : Nat.Coprime 2 3)).injective
  simpa only [IsPGroup.powEquiv_apply,one_pow] using hc

def chart : OriginalSixteenPreE7Representative.Chart Original :=
  OriginalSixteenPreE7Representative.choose Original nonbinary transitive

def source (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7RankTailSourceOrYonedaTopData 16 chart.index :=
  SixteenPointSemanticCyclicQuartetProjectors.source K
    (SixteenPointSemanticCyclicQuartetProjectors.irreducible K
      local_orbit_single transitiveImage projector projection)
    beta_surjective PrimitiveAffineDegreeTwoNonbinary16T1932QuotientSocles.rotation blocks_cycle blocks_coprime chart.index
    (chart.groupEquiv.toMonoidHom.comp originalMap)
    (chart.groupEquiv.surjective.comp originalMap_surjective) hMN hZmud

end SymmetricSubgroupAsymptotics.SixteenPointSemanticCyclicQuartetT1926
end
