import SymmetricSubgroupAsymptotics.BinaryCoordinateRegistry
import SymmetricSubgroupAsymptotics.RepresentationGeneratorInvariants

/-! Exact central cuts and full fixed preimages of the retained coordinate
module. Original generator tests imply the complete action statements;
no declared dimension or capacity is a certificate hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G ι V : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- A point is fixed modulo an actual invariant cut if and only if the
retained original generators fix it modulo that cut. -/
theorem binaryCoordinate_fixed_mod_iff
    (ρ : Representation (ZMod 2) G V) (C : Subrepresentation ρ)
    (generators : ι → G) (hgen : Subgroup.closure (Set.range generators)=⊤) (v : V) :
    (∀ g, ρ g v-v∈C.toSubmodule) ↔ ∀ j, ρ (generators j) v-v∈C.toSubmodule := by
  let q := ρ.quotient C.toSubmodule (fun g => C.apply_mem_toSubmodule g)
  have he (g : G) : q g (C.toSubmodule.mkQ v)=C.toSubmodule.mkQ v ↔
      ρ g v-v∈C.toSubmodule := by
    exact Submodule.Quotient.eq C.toSubmodule
  constructor
  · exact fun h j => h (generators j)
  · intro h
    have hv : C.toSubmodule.mkQ v∈q.invariants :=
      (binaryPair_invariants_iff_generators q generators hgen _).mpr
        (fun j => (he _).mpr (h j))
    exact fun g => (he g).mp (hv g)

/-- The mathematical content of one shared central cut. `fixed` is the
complete fixed preimage, not merely a chosen subspace of fixed points. -/
structure BinaryCoordinateCutData (ρ : Representation (ZMod 2) G V)
    (kernel axis cut fixed : Subrepresentation ρ) : Prop where
  axis_le_cut : axis.toSubmodule≤cut.toSubmodule
  cut_le_kernel : cut.toSubmodule≤kernel.toSubmodule
  central : ∀ g v, v∈cut.toSubmodule → ρ g v-v∈axis.toSubmodule
  fixed_iff : ∀ v, v∈fixed.toSubmodule ↔
    v∈kernel.toSubmodule ∧ ∀ g, ρ g v-v∈cut.toSubmodule

/-- Finite basis tests and the complete coordinate predicate construct an
actual central-cut certificate for the entire original action. -/
theorem binaryCoordinate_cut_of_checks {w k a c d : ℕ}
    (K : BinaryCoordinateSpace w k) (A : BinaryCoordinateSpace w a)
    (C : BinaryCoordinateSpace w c) (D : BinaryCoordinateSpace w d)
    (ρ : Representation (ZMod 2) G (Fin w → ZMod 2))
    (Ks As Cs Ds : Subrepresentation ρ)
    (hK : Ks.toSubmodule=K.space) (hA : As.toSubmodule=A.space)
    (hC : Cs.toSubmodule=C.space) (hD : Ds.toSubmodule=D.space)
    (generators : ι → G) (hgen : Subgroup.closure (Set.range generators)=⊤)
    (hac : ∀ j, A.inclusion (Pi.single j 1)∈C.space)
    (hck : ∀ j, C.inclusion (Pi.single j 1)∈K.space)
    (hcentral : ∀ i j, ρ (generators i) (C.inclusion (Pi.single j 1))-
      C.inclusion (Pi.single j 1)∈A.space)
    (hfixed : ∀ v, v∈D.space ↔ v∈K.space ∧
      ∀ j, ρ (generators j) v-v∈C.space) :
    BinaryCoordinateCutData ρ Ks As Cs Ds where
  axis_le_cut := by rw [hA,hC]; exact A.le_of_basis_mem C.space hac
  cut_le_kernel := by rw [hC,hK]; exact C.le_of_basis_mem K.space hck
  central g v hv := by
    apply (binaryCoordinate_fixed_mod_iff ρ As generators hgen v).mpr ?_ g
    intro i
    have he : C.space≤A.space.comap (ρ (generators i)-LinearMap.id) :=
      C.le_of_basis_mem _ (hcentral i)
    rw [hA]
    exact he (hC ▸ hv)
  fixed_iff v := by
    rw [hD,hK,binaryCoordinate_fixed_mod_iff ρ Cs generators hgen v,hC]
    exact hfixed v

end SymmetricSubgroupAsymptotics
