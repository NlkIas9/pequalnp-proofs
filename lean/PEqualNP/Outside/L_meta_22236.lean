import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22236_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩,
     ⟨.not, [6]⟩,
     ⟨.and, [3, 7]⟩,
     ⟨.and, [4, 7]⟩,
     ⟨.and, [2, 6]⟩,
     ⟨.or, [5, 8]⟩,
     ⟨.or, [11, 9]⟩,
     ⟨.or, [12, 10]⟩,
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

end PEqualNP.Outside.L_meta_22236_aux

open PEqualNP.Outside.L_meta_22236_aux in
theorem PEqualNP.Outside.L_meta_22236 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18075 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, shape, by decide +kernel, by decide +kernel⟩
