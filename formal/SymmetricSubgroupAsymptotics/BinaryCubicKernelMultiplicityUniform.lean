import SymmetricSubgroupAsymptotics.BinaryCubicDistinctKernelUniform

/-! Actual cubic kernel classes may share generator positions. Bounded
class multiplicity supplies colors injective within each literal kernel
fibre. Odd subgroup averages then recover individual packed coordinates;
no independent local group elements or external F4 action are assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators MonoidAlgebra
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics.BinaryCubicKernelMultiplicityUniform
open BinaryPlanePermutationAffineEquiv

section Coloring
variable {I C : Type} [Finite I] (key : I → C) (m : ℕ)
    (hbound : ∀ c : C, Nat.card {i : I // key i = c} ≤ m)

/-- Each actual key fibre is embedded independently into the same finite
set of positions; no product or independence of the fibres is inferred. -/
def fibreColor (i : I) : Fin m :=
  Fin.castLEEmb (hbound (key i))
    (Finite.equivFin {j : I // key j = key i} ⟨i,rfl⟩)

include hbound in
theorem fibreColor_injective_on_fibre (i j : I) (he : key i = key j)
    (hc : fibreColor key m hbound i = fibreColor key m hbound j) : i = j := by
  let label (c : C) : {x : I // key x = c} ↪ Fin m :=
    (Finite.equivFin {x : I // key x = c}).toEmbedding.trans (Fin.castLEEmb (hbound c))
  have transport (c d : C) (h : c = d) (x : I) (hx : key x = c) :
      label c ⟨x,hx⟩ = label d ⟨x,hx.trans h⟩ := by
    subst d
    rfl
  have hi : fibreColor key m hbound i = label (key j) ⟨i,he⟩ :=
    transport (key i) (key j) he i rfl
  have hj : fibreColor key m hbound j = label (key j) ⟨j,rfl⟩ := rfl
  exact congrArg Subtype.val ((label (key j)).injective (hi.symm.trans (hc.trans hj)))
end Coloring

variable {O I : Type} [Group O] [Finite O] [Fintype I] [DecidableEq I]
    (rho : Representation (ZMod 2) O (I → Plane)) (L : I → O →* Linear)
    (happly : ∀ g v i, rho g v i = L i g (v i))

abbrev localKernel := BinaryCubicDistinctKernelUniform.localKernel L

omit [Fintype I] [DecidableEq I] in
private theorem average_formula (D : Subgroup O)
    [Invertible (Fintype.card D : ZMod 2)] (v : I → Plane) :
    (Representation.averageMap (rho.comp D.subtype)) v =
      ⅟(Fintype.card D : ZMod 2) • ∑ g : D, rho (g : O) v := by
  simp [Representation.averageMap,GroupAlgebra.average,map_sum,
    LinearMap.smul_apply,Finset.sum_apply]

include happly in
private theorem average_coordinate_same (i j : I)
    [Invertible (Fintype.card (localKernel L i) : ZMod 2)]
    (he : localKernel L i = localKernel L j) (v : I → Plane) :
    ((Representation.averageMap (rho.comp (localKernel L i).subtype)) v) j = v j := by
  have htriv (g : localKernel L i) : L j (g : O) = 1 := by
    have hg : (g : O) ∈ localKernel L j := he ▸ g.property
    exact hg
  rw [average_formula]
  change ⅟(Fintype.card (localKernel L i) : ZMod 2) •
    (∑ g : localKernel L i, rho (g : O) v) j = v j
  simp only [Finset.sum_apply,happly,htriv]
  change ⅟(Fintype.card (localKernel L i) : ZMod 2) •
    (∑ _g : localKernel L i, v j) = v j
  rw [Finset.sum_const,Finset.card_univ,←Nat.cast_smul_eq_nsmul (ZMod 2),
    smul_smul,invOf_mul_self,one_smul]

include happly in
omit [Fintype I] [DecidableEq I] in
private theorem average_coordinate_different (i j : I)
    [Invertible (Fintype.card (localKernel L i) : ZMod 2)]
    (hcubic : ∀ i g, L i g ^ 3 = 1)
    (hcards : ∀ i j, Nat.card (localKernel L i) = Nat.card (localKernel L j))
    (he : localKernel L i ≠ localKernel L j) (v : I → Plane) :
    ((Representation.averageMap (rho.comp (localKernel L i).subtype)) v) j = 0 := by
  have hnot : ¬localKernel L i ≤ localKernel L j := by
    intro hle
    exact he (Subgroup.eq_of_le_of_card_ge hle (by rw [hcards i j]))
  obtain ⟨g,hgi,hgj⟩ := Set.not_subset.mp hnot
  let h : localKernel L i := ⟨g,hgi⟩
  let w := (Representation.averageMap (rho.comp (localKernel L i).subtype)) v
  have hw := (Representation.averageMap_invariant (rho.comp (localKernel L i).subtype)) v h
  have hj := congrFun hw j
  change rho g w j = w j at hj
  rw [happly] at hj
  exact BinaryPlaneNontrivialCubicFixedFree.fixedFree (L j g) (hcubic j g) hgj (w j) hj

private theorem cubic_card_cast_one (hO : IsPGroup 3 O) (D : Subgroup O) :
    (Fintype.card D : ZMod 2) = 1 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨n,hn⟩ := (hO.to_subgroup D).exists_card_eq
  rw [←Nat.card_eq_fintype_card,hn,Nat.cast_pow,
    show ((3 : ℕ) : ZMod 2) = 1 by decide +kernel,one_pow]

/-- Averaging over the actual coordinate kernel; invertibility follows
from the displayed actual 3-group, not an assumed projector. -/
def kernelProjector (hO : IsPGroup 3 O) (i : I) : Module.End (ZMod 2) (I → Plane) := by
  letI : Invertible (Fintype.card (localKernel L i) : ZMod 2) :=
    invertibleOfNonzero (by rw [cubic_card_cast_one hO]; exact one_ne_zero)
  exact Representation.averageMap (rho.comp (localKernel L i).subtype)

/-- One row position is shared across the actual kernel classes. -/
def packedSeed {m : ℕ} (color : I → Fin m) (j : Fin m) (v : Plane) : I → Plane :=
  fun i => if color i = j then v else 0

include happly in
/-- Averaging one packed row over the literal kernel recovers precisely
one coordinate, even when the same kernel occurs at several coordinates. -/
theorem packed_average_single (hO : IsPGroup 3 O)
    (hcubic : ∀ i g, L i g ^ 3 = 1)
    (hcards : ∀ i j, Nat.card (localKernel L i) = Nat.card (localKernel L j))
    (m : ℕ) (hbound : ∀ K : Subgroup O, Nat.card {i : I // localKernel L i = K} ≤ m)
    (i : I) (v : Plane) :
    kernelProjector rho L hO i
        (packedSeed (fibreColor (localKernel L) m hbound)
          (fibreColor (localKernel L) m hbound i) v) = Pi.single i v := by
  letI : Invertible (Fintype.card (localKernel L i) : ZMod 2) :=
    invertibleOfNonzero (by rw [cubic_card_cast_one hO]; exact one_ne_zero)
  change (Representation.averageMap (rho.comp (localKernel L i).subtype))
    (packedSeed (fibreColor (localKernel L) m hbound)
      (fibreColor (localKernel L) m hbound i) v) = Pi.single i v
  funext j
  by_cases he : localKernel L i = localKernel L j
  · rw [average_coordinate_same rho L happly i j he]
    by_cases hji : j = i
    · subst j
      simp only [packedSeed,Pi.single_eq_same,if_true]
    · have hc : fibreColor (localKernel L) m hbound j ≠
          fibreColor (localKernel L) m hbound i := by
        intro hc
        exact hji (fibreColor_injective_on_fibre (localKernel L) m hbound j i he.symm hc)
      simp only [packedSeed,if_neg hc,Pi.single_eq_of_ne hji]
  · rw [average_coordinate_different rho L happly i j hcubic hcards he]
    have hji : j ≠ i := by intro h; subst j; exact he rfl
    rw [Pi.single_eq_of_ne hji]

end SymmetricSubgroupAsymptotics.BinaryCubicKernelMultiplicityUniform
