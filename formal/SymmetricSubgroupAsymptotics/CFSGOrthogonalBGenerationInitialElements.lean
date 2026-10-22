import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationForkTorus
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCoxeter

/-! The literal odd-field B candidate in every rank at least three.
Its short root is terminal, and its initial long root is the adjacent
negative chain root; no rank-parity split is hidden in this definition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationInitialElements
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationElements
open CFSGOrthogonalBGenerationShortArrays CFSGOrthogonalBGenerationShortCommutator
open CFSGOrthogonalBGenerationForkTorus
variable (K : Type) [Field K]

def penIndex (s : ℕ) : Fin (s + 3) := (Fin.last (s + 1)).castSucc
def lastIndex (s : ℕ) : Fin (s + 3) := Fin.last (s + 2)

theorem pen_ne_last (s : ℕ) : penIndex s ≠ lastIndex s := by
  intro he
  have hh := congrArg Fin.val he
  change s + 1 = s + 2 at hh
  omega

def alphaArray (s : ℕ) : Mat K (s + 3) :=
  Matrix.single (pos (s + 3) (lastIndex s)) (pos (s + 3) (penIndex s)) 1 -
    Matrix.single (CFSGOrthogonalBSerreMatrices.neg (s + 3) (penIndex s))
      (CFSGOrthogonalBSerreMatrices.neg (s + 3) (lastIndex s)) 1

def alphaElement (s : ℕ) (a : K) : elementaryRootGroup K (s + 3) :=
  rootElement K (s + 3) true (penIndex s) a

def betaElement (s : ℕ) (a : K) : elementaryRootGroup K (s + 3) :=
  rootElement K (s + 3) false (lastIndex s) a

def alphaUnit (s : ℕ) (a : K) : (Mat K (s + 3))ˣ := (alphaElement K s a).val
def betaUnit (s : ℕ) (a : K) : (Mat K (s + 3))ˣ :=
  shortUnit K (s + 3) (Sum.inl (lastIndex s)) a

theorem alphaUnit_val (s : ℕ) (a : K) :
    (alphaUnit K s a : Mat K (s + 3)) = 1 + a • alphaArray K s := by
  have hi : (penIndex s).val + 1 < s + 3 := by dsimp [penIndex]; omega
  have hn : (⟨(penIndex s).val + 1, hi⟩ : Fin (s + 3)) = lastIndex s := by
    apply Fin.ext
    dsimp [penIndex, lastIndex]
  change (rootTransvection K (s + 3) true (penIndex s) a : Mat K (s + 3)) = _
  simp only [rootTransvection_val, rootMatrix, rootSecond, if_true,
    negative, negativeSecond, dif_pos hi, if_pos hi, smul_zero, add_zero, hn]
  rfl

theorem betaElement_val (s : ℕ) (a : K) : (betaElement K s a).val = betaUnit K s a := by
  exact terminal_positive K (s + 3) (lastIndex s) (by dsimp [lastIndex]; omega) a

theorem alphaUnit_zero (s : ℕ) : alphaUnit K s 0 = 1 :=
  congrArg Subtype.val (rootElement_zero K (s + 3) true (penIndex s))

theorem alphaUnit_add (s : ℕ) (a b : K) :
    alphaUnit K s (a + b) = alphaUnit K s a * alphaUnit K s b :=
  congrArg Subtype.val (rootElement_add K (s + 3) true (penIndex s) a b)

theorem betaUnit_zero (s : ℕ) : betaUnit K s 0 = 1 :=
  shortUnit_zero K (s + 3) (Sum.inl (lastIndex s))

theorem betaUnit_add (s : ℕ) (a b : K) :
    betaUnit K s (a + b) = betaUnit K s a * betaUnit K s b :=
  shortUnit_add K (s + 3) (Sum.inl (lastIndex s)) a b

def initialTorus (h2 : (2 : K) ≠ 0) (s : ℕ) (g : Kˣ) : elementaryRootGroup K (s + 3) :=
  forkTorus K h2 (s + 1) g

def initialMixedWeyl (s : ℕ) : elementaryRootGroup K (s + 3) :=
  alphaElement K s 1 * betaElement K s 1 * CFSGOrthogonalBGenerationCoxeter.coxeterWeyl K (s + 2)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationInitialElements
