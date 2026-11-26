import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22276_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit :=
  ⟨[⟨.or, [3, 4]⟩,
     ⟨.or, [0, 6]⟩,
     ⟨.and, [0, 6]⟩,
     ⟨.not, [8]⟩,
     ⟨.and, [7, 9]⟩,
     ⟨.and, [1, 2]⟩,
     ⟨.or, [5, 11]⟩,
     ⟨.or, [10, 12]⟩,
     ⟨.not, [13]⟩], 14⟩

private def gateOK (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => decide (g.inputs.length ≤ 2)
  | _ => false

private theorem shape : FanInTwo witness := by
  have checked : witness.gates.all gateOK = true := by decide +kernel
  intro g hg
  have good := List.all_eq_true.mp checked g hg
  cases h : g.op <;> simp [gateOK, h] at good ⊢ <;> assumption

end PEqualNP.Outside.L_meta_22276_aux

open PEqualNP.Outside.L_meta_22276_aux in
theorem PEqualNP.Outside.L_meta_22276 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16536 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, shape, by decide +kernel, by decide +kernel⟩
