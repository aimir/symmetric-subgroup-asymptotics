import SymmetricSubgroupAsymptotics.NormalSubgroupOrbitIndex
import SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockCubeReduction

/-! Coarsen the SAME original fibres by actual normal-subgroup orbits.
The quotient consists of actual orbit sets, with the original ambient
action. Its fibres and number of blocks are proved by exact equivalences.
The final bound invokes only strict-smaller general permutation IH. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators Pointwise
namespace SymmetricSubgroupAsymptotics.NormalOrbitFibreCoarsening

variable {G X : Type} [Group G] [MulAction G X]
    (K : Subgroup G) [K.Normal] [MulAction.IsPretransitive G X] (x₀ : X)

abbrev Blocks := MulAction.orbit G (MulAction.orbit K x₀)

local instance finiteBlocks [Finite X] : Finite (Blocks K x₀) :=
  Finite.of_equiv (MulAction.orbitRel.Quotient K X)
    (normalOrbitClassesEquivBlockOrbit K x₀)

def map (x : X) : Blocks K x₀ := ⟨MulAction.orbit K x,by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G x₀ x
  refine ⟨g,?_⟩
  change g • MulAction.orbit K x₀=MulAction.orbit K x
  rw [MulAction.smul_orbit_eq_orbit_smul,hg]⟩

theorem map_equivariant (g : G) (x : X) : map K x₀ (g • x)=g • map K x₀ x := by
  apply Subtype.ext
  exact (MulAction.smul_orbit_eq_orbit_smul K x g).symm

theorem map_eq_iff (x : X) (y : Blocks K x₀) : map K x₀ x=y ↔ x∈(y : Set X) := by
  have he : map K x₀ x=y ↔ MulAction.orbit K x=(y : Set X) := by
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      apply Subtype.ext
      change MulAction.orbit K x=(y : Set X)
      exact h
  obtain ⟨g,hg⟩ := y.property
  change g • MulAction.orbit K x₀=(y : Set X) at hg
  have hy : (y : Set X)=MulAction.orbit K (g • x₀) := by
    rw [← hg,MulAction.smul_orbit_eq_orbit_smul]
  rw [he,hy,MulAction.orbit_eq_iff]

private def fibreEquiv (y : Blocks K x₀) :
    {x : X // map K x₀ x=y} ≃ (y : Set X) :=
  Equiv.subtypeEquivRight (fun x => map_eq_iff K x₀ x y)

theorem fibre_card [Finite X] (b : ℕ)
    (hcard : ∀ x : X, Nat.card (MulAction.orbit K x)=b) (y : Blocks K x₀) :
    Nat.card {x : X // map K x₀ x=y}=b := by
  rw [Nat.card_congr (fibreEquiv K x₀ y)]
  obtain ⟨g,hg⟩ := y.property
  change g • MulAction.orbit K x₀=(y : Set X) at hg
  rw [← hg,MulAction.smul_orbit_eq_orbit_smul]
  exact hcard _

theorem blocks_card_mul [Finite X] (b : ℕ)
    (hcard : ∀ x : X, Nat.card (MulAction.orbit K x)=b) :
    b*Nat.card (Blocks K x₀)=Nat.card X := by
  calc
    b*Nat.card (Blocks K x₀)=
        Nat.card (MulAction.orbit K x₀)*Nat.card (MulAction.orbitRel.Quotient K X) := by
      rw [hcard x₀,Nat.card_congr (normalOrbitClassesEquivBlockOrbit K x₀)]
    _=Nat.card X := normal_orbit_card_mul_classes K x₀

theorem composed_fibre_card {Ω : Type} [Finite Ω] [Finite X]
    (π : Ω → X) (a b : ℕ)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=a)
    (hcard : ∀ x : X, Nat.card (MulAction.orbit K x)=b) (y : Blocks K x₀) :
    Nat.card (originalBlockFibre (fun ω => map K x₀ (π ω)) y)=b*a := by
  letI : Fintype {x : X // map K x₀ x=y} := Fintype.ofFinite _
  let e : (Σ x : {x : X // map K x₀ x=y}, {ω : Ω // π ω=x.val}) ≃
      {ω : Ω // map K x₀ (π ω)=y} :=
    Equiv.sigmaSubtypeFiberEquivSubtype π
      (p:=fun ω => map K x₀ (π ω)=y) (q:=fun x => map K x₀ x=y)
      (fun _ => Iff.rfl)
  calc
    _=Nat.card (Σ x : {x : X // map K x₀ x=y}, {ω : Ω // π ω=x.val}) :=
      (Nat.card_congr e).symm
    _=∑ x : {x : X // map K x₀ x=y}, Nat.card (originalBlockFibre π x.val) :=
      Nat.card_sigma
    _=Nat.card {x : X // map K x₀ x=y}*a := by
      simp only [hsize,Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]
    _=b*a := by rw [fibre_card K x₀ b hcard y]

theorem exact_exponent_large_block_cube_step {Ω : Type}
    [Finite G] [Finite Ω] [Finite X] [MulAction G Ω] [FaithfulSMul G Ω]
    (π : Ω → X) (hπ : ∀ (g : G) (ω : Ω), π (g • ω)=g • π ω)
    (a b : ℕ) (hab : 4≤b*a) (hblocks : 4≤Nat.card (Blocks K x₀))
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=a)
    (hcard : ∀ x : X, Nat.card (MulAction.orbit K x)=b)
    (hSmaller : ∀ m : ℕ, m<Nat.card Ω → 4≤m →
      ∀ L : Subgroup (Equiv.Perm (Fin m)), Nat.card (ConjClasses L)^3≤5^(m-1)) :
    Nat.card (ConjClasses G)^3≤5^(Nat.card Ω-1) := by
  have heq (g : G) (ω : Ω) :
      map K x₀ (π (g • ω))=g • map K x₀ (π ω) := by
    rw [hπ,map_equivariant]
  exact GaronziMarotiLargeBlockCubeReduction.exact_exponent_large_block_cube_step
    (fun ω => map K x₀ (π ω)) heq (b*a) hab hblocks
    (composed_fibre_card K x₀ π a b hsize hcard) hSmaller

end SymmetricSubgroupAsymptotics.NormalOrbitFibreCoarsening
