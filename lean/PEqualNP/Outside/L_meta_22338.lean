import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22338_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit :=
  ⟨[⟨.not, [2]⟩,
     ⟨.and, [0, 6]⟩,
     ⟨.or, [0, 1]⟩,
     ⟨.or, [8, 3]⟩,
     ⟨.or, [9, 4]⟩,
     ⟨.or, [10, 5]⟩,
     ⟨.not, [11]⟩,
     ⟨.and, [2, 12]⟩,
     ⟨.or, [3, 4]⟩,
     ⟨.or, [14, 5]⟩,
     ⟨.and, [1, 15]⟩,
     ⟨.or, [7, 13]⟩,
     ⟨.or, [17, 16]⟩], 18⟩

private def gateOK (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => decide (g.inputs.length ≤ 2)
  | _ => false

private theorem shape : FanInTwo witness := by
  have checked : witness.gates.all gateOK = true := by decide +kernel
  intro g hg
  have good := List.all_eq_true.mp checked g hg
  cases h : g.op <;> simp [gateOK, h] at good ⊢ <;> assumption

end PEqualNP.Outside.L_meta_22338_aux

open PEqualNP.Outside.L_meta_22338_aux in
theorem PEqualNP.Outside.L_meta_22338 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (20027 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, shape, by decide +kernel, by decide +kernel⟩
