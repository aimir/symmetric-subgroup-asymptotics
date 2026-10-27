import SymmetricSubgroupAsymptotics.CFSGPSLTwoIndexThreeTorusFibre

/-! The actual correlated index-three cover of a product Borel.
H is one normal subgroup of the whole Borel power, not a product of
coordinate index-three subgroups. All transport takes place in G/H. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoProductTorusCover
open CFSGPSLTwoGeometry CFSGPSLTwoRootCoordinates CFSGPSLTwoTorusCosetFibre
variable {F J : Type*} [Field F]

def borelPowerHom : (J → projectiveBorel (F:=F)) →* (J → PSL (F:=F)) where
  toFun b i := (b i).val
  map_one' := rfl
  map_mul' _ _ := rfl

def rootPowerHom : (J → projectiveRoot (F:=F)) →* (J → projectiveBorel (F:=F)) where
  toFun u i := ⟨(u i).val,projectiveRoot_le_borel (u i).property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def torusPowerHom : (J → pairTorus (F:=F)) →* (J → PSL (F:=F)) where
  toFun t i := (t i).val
  map_one' := rfl
  map_mul' _ _ := rfl

theorem rootPowerHom_injective : Function.Injective (rootPowerHom (F:=F) (J:=J)) := by
  intro u v huv
  funext i
  apply Subtype.ext
  exact congrArg (fun b : J → projectiveBorel (F:=F) => (b i).val) huv

theorem rootPower_card [Finite J] :
    Nat.card (rootPowerHom (F:=F) (J:=J)).range = (Nat.card F)^Nat.card J := by
  calc
    _ = Nat.card (J → projectiveRoot (F:=F)) :=
      Nat.card_congr (MonoidHom.ofInjective (rootPowerHom_injective (F:=F) (J:=J))).symm.toEquiv
    _ = _ := by rw [Nat.card_fun,projectiveRoot_card]

theorem rootPower_le_index_three [Finite J]
    (H : Subgroup (J → projectiveBorel (F:=F))) [H.Normal]
    (hindex : H.index = 3) (hcop : (Nat.card F).Coprime 3) :
    (rootPowerHom (F:=F) (J:=J)).range ≤ H := by
  apply NormalSubgroupCoprimeIndexContainment.le_of_coprime_card_index
  rw [rootPower_card,hindex]
  exact hcop.pow_left (Nat.card J)

/-- Every point of the single correlated B/H quotient has a torus-power
representative. No choice of independent three-point coordinate fibres. -/
theorem exists_product_torus_coset_rep [Finite J]
    (H : Subgroup (J → projectiveBorel (F:=F))) [H.Normal]
    (hindex : H.index = 3) (hcop : (Nat.card F).Coprime 3)
    (b : J → projectiveBorel (F:=F)) :
    ∃ t : J → pairTorus (F:=F),
      (QuotientGroup.mk (borelPowerHom b) :
        (J → PSL (F:=F)) ⧸ H.map borelPowerHom) =
      QuotientGroup.mk (torusPowerHom t) := by
  classical
  have hex (i : J) : ∃ z : pairTorus (F:=F) × projectiveRoot (F:=F),
      borelProduct z = b i := borelProduct_surjective (b i)
  let z := fun i => Classical.choose (hex i)
  let t : J → pairTorus (F:=F) := fun i => (z i).1
  let u : J → projectiveRoot (F:=F) := fun i => (z i).2
  have hz (i : J) : (t i).val*(u i).val=(b i).val :=
    congrArg Subtype.val (Classical.choose_spec (hex i))
  have hu : rootPowerHom u ∈ H :=
    rootPower_le_index_three H hindex hcop ⟨u,rfl⟩
  have hua : borelPowerHom (rootPowerHom u) ∈ H.map borelPowerHom := ⟨_,hu,rfl⟩
  have hv : borelPowerHom b = torusPowerHom t*borelPowerHom (rootPowerHom u) := by
    funext i
    exact (hz i).symm
  refine ⟨t,QuotientGroup.eq.mpr ?_⟩
  change (borelPowerHom b)⁻¹*torusPowerHom t ∈ H.map borelPowerHom
  rw [hv]
  simpa only [mul_inv_rev,mul_assoc,inv_mul_cancel,mul_one] using
    (H.map borelPowerHom).inv_mem hua

/-- Torus transport in the complete original cover over a normalizing
product representative; the same H and the same original coset are kept. -/
theorem exists_product_torus_move [Finite J]
    (H : Subgroup (J → projectiveBorel (F:=F))) [H.Normal]
    (hindex : H.index = 3) (hcop : (Nat.card F).Coprime 3)
    (g : J → PSL (F:=F))
    (hconj : ∀ (i : J) (t : pairTorus (F:=F)), g i*t.val*(g i)⁻¹ ∈ pairTorus (F:=F))
    (b : J → projectiveBorel (F:=F)) :
    ∃ n : J → pairTorus (F:=F),
      (torusPowerHom n) • (QuotientGroup.mk g :
        (J → PSL (F:=F)) ⧸ H.map borelPowerHom) =
      QuotientGroup.mk (g*borelPowerHom b) := by
  obtain ⟨t,ht⟩ := exists_product_torus_coset_rep H hindex hcop b
  let n : J → pairTorus (F:=F) := fun i => ⟨g i*(t i).val*(g i)⁻¹,hconj i (t i)⟩
  have hn : torusPowerHom n=g*torusPowerHom t*g⁻¹ := rfl
  have hh := congrArg (fun q : (J → PSL (F:=F)) ⧸ H.map borelPowerHom => g • q) ht
  change (QuotientGroup.mk (g*borelPowerHom b) :
    (J → PSL (F:=F)) ⧸ H.map borelPowerHom) = QuotientGroup.mk (g*torusPowerHom t) at hh
  refine ⟨n,?_⟩
  change (QuotientGroup.mk (torusPowerHom n*g) :
    (J → PSL (F:=F)) ⧸ H.map borelPowerHom) = _
  rw [hn]
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh.symm

def weylMask (s : Set J) [DecidablePred (· ∈ s)] : J → PSL (F:=F) :=
  fun i => if i ∈ s then projectiveWeyl else 1

theorem weylMask_conjugates_torus (s : Set J) [DecidablePred (· ∈ s)]
    (i : J) (t : pairTorus (F:=F)) :
    weylMask (F:=F) s i*t.val*(weylMask (F:=F) s i)⁻¹ ∈ pairTorus (F:=F) := by
  by_cases hi : i ∈ s
  · simpa only [weylMask,if_pos hi] using weyl_conjugates_torus t
  · simpa only [weylMask,if_neg hi,inv_one,one_mul,mul_one] using t.property

end SymmetricSubgroupAsymptotics.CFSGPSLTwoProductTorusCover
