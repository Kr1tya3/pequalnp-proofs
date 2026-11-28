import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53884

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.or, [5, 11]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.and, [10, 13]⟩], output := 14 }

theorem f1 : PEqualNP.MetaComplexity.FanInTwo c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_53884

theorem PEqualNP.Outside.L_meta_53884 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50719 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_53884.c1, PEqualNP.Outside.L_meta_53884.f1, by decide +kernel, by decide +kernel⟩
