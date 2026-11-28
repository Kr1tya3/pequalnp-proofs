import Mathlib
import PEqualNP.Defs
import PEqualNP.Library.Helpers.GraphSampleDistance

namespace PEqualNP.Outside.L_meta_57336

def cls {α κ : Type} [DecidableEq α] (comp : κ → Finset α) (a : κ) (h : Finset α → Bool) :=
  ∀ x y, x ∩ comp a = y ∩ comp a → h x = h y

def good {α κ : Type} [DecidableEq α] (comp : κ → Finset α) (h : Finset α → Bool) :=
  (∀ x y, h x = h y) ∨ ∃ a, cls comp a h

theorem memEq {α κ : Type} {inst : DecidableEq α} {color : α → κ} {comp : κ → Finset α}
    (hcomp : ∀ i j, i ∈ comp j ↔ color i = j) {a : κ} {x y : Finset α}
    (hxy : x ∩ comp a = y ∩ comp a) (k : α) (hk : color k = a) : k ∈ x ↔ k ∈ y := by
  have hc : k ∈ comp a := (hcomp k a).mpr hk
  constructor
  · intro h
    have : k ∈ y ∩ comp a := hxy ▸ Finset.mem_inter.mpr ⟨h, hc⟩
    exact (Finset.mem_inter.mp this).1
  · intro h
    have : k ∈ x ∩ comp a := hxy.symm ▸ Finset.mem_inter.mpr ⟨h, hc⟩
    exact (Finset.mem_inter.mp this).1

theorem goodAll (n c : Nat) (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c)
    (sameColor : ∀ e ∈ E, color e.1 = color e.2) (comp : Fin c → Finset (Fin n))
    (hcomp : ∀ i j, i ∈ comp j ↔ color i = j) :
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let W := Finset (Fin n)
  let bit := fun (i : Fin n) (x : W) => decide (i ∈ x)
  let neg := fun (i : Fin n) (x : W) => !(bit i x)
  let same := fun (e : Fin n × Fin n) (x : W) => bit e.1 x == bit e.2 x
  let raw : Finset (W → Bool) := {fun _ => false,fun _ => true} ∪ Finset.univ.image bit ∪
    E.image same ∪ E.image (fun e x => !(same e x))
  let need := Finset.univ.image neg ∪ E.image (fun e x => neg e.1 x && neg e.2 x) ∪
    E.image (fun e x => bit e.1 x && neg e.2 x) ∪ E.image (fun e x => neg e.1 x && bit e.2 x)
  ∀ h, (h ∈ raw ∨ h ∈ need) → good comp h := by
  intro W bit neg same raw need h hh
  simp only [raw, need, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_univ, true_and] at hh
  have one : ∀ (i : Fin n) (x y : W), (∀ k, color k = color i → (k ∈ x ↔ k ∈ y)) →
      bit i x = bit i y := by
    intro i x y hxy
    have e := hxy i rfl
    by_cases h1 : i ∈ x
    · have h2 := e.mp h1; simp [bit, h1, h2]
    · have h2 : i ∉ y := fun h => h1 (e.mpr h); simp [bit, h1, h2]
  have two : ∀ e ∈ E, ∀ (x y : W), (∀ k, color k = color e.1 → (k ∈ x ↔ k ∈ y)) →
      bit e.1 x = bit e.1 y ∧ bit e.2 x = bit e.2 y := by
    intro e he x y hxy
    refine ⟨one e.1 x y hxy, ?_⟩
    apply one
    rw [← sameColor e he]; exact hxy
  rcases hh with ((((rfl | rfl) | ⟨i, rfl⟩) | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩) |
    (((⟨i, rfl⟩ | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩)
  · exact Or.inl (fun _ _ => rfl)
  · exact Or.inl (fun _ _ => rfl)
  · exact Or.inr ⟨color i, fun x y hxy => one i x y (memEq hcomp hxy)⟩
  · refine Or.inr ⟨color e.1, fun x y hxy => ?_⟩
    obtain ⟨a, b⟩ := two e he x y (memEq hcomp hxy)
    simp only [same, a, b]
  · refine Or.inr ⟨color e.1, fun x y hxy => ?_⟩
    obtain ⟨a, b⟩ := two e he x y (memEq hcomp hxy)
    simp only [same, a, b]
  · refine Or.inr ⟨color i, fun x y hxy => ?_⟩
    simp only [neg, one i x y (memEq hcomp hxy)]
  all_goals
    refine Or.inr ⟨color e.1, fun x y hxy => ?_⟩
    obtain ⟨a, b⟩ := two e he x y (memEq hcomp hxy)
    simp only [neg, a, b]

section gen
variable {α κ : Type} {inst : DecidableEq α} (color : α → κ) (comp : κ → Finset α)
  (norm : Finset α → Finset α)

def dl (h : Finset α → Bool) (j : κ) : Int := ((h (comp j)).toNat : Int) - ((h ∅).toNat : Int)

variable {color comp norm}

theorem disj (hcomp : ∀ i j, i ∈ comp j ↔ color i = j) {a b : κ} (ne : a ≠ b) :
    Disjoint (comp a) (comp b) := by
  rw [Finset.disjoint_left]
  intro i ha hb
  exact ne (((hcomp i a).mp ha).symm.trans ((hcomp i b).mp hb))

theorem normSub (hnorm : ∀ x i, i ∈ norm x ↔ i ∈ x ∧ ¬ comp (color i) ⊆ x) (x : Finset α) :
    norm x ⊆ x := fun i hi => ((hnorm x i).mp hi).1

theorem normIdem (hnorm : ∀ x i, i ∈ norm x ↔ i ∈ x ∧ ¬ comp (color i) ⊆ x) (x : Finset α) :
    norm (norm x) = norm x := by
  ext i
  rw [hnorm]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, fun s => ((hnorm x i).mp h).2 (s.trans (normSub hnorm x))⟩

theorem normPair (hcomp : ∀ i j, i ∈ comp j ↔ color i = j)
    (hnorm : ∀ x i, i ∈ norm x ↔ i ∈ x ∧ ¬ comp (color i) ⊆ x) (u : Finset α) (j : κ)
    (du : Disjoint u (comp j)) : norm (u ∪ comp j) = norm u := by
  ext i
  rw [hnorm, hnorm, Finset.mem_union]
  by_cases hc : color i = j
  · have hi : i ∈ comp j := (hcomp i j).mpr hc
    have nu : i ∉ u := fun h => Finset.disjoint_left.mp du h hi
    rw [hc]
    simp only [nu, false_and, iff_false, not_and, not_not]
    intro _
    exact Finset.subset_union_right
  · have hi : i ∉ comp j := fun h => hc ((hcomp i j).mp h)
    have dd := disj hcomp hc
    simp only [hi, or_false]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun s => h2 (s.trans Finset.subset_union_left)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun s => h2 ?_⟩
      intro k hk
      rcases Finset.mem_union.mp (s hk) with h | h
      · exact h
      · exact absurd h (Finset.disjoint_left.mp dd hk)

theorem normDisj (hnorm : ∀ x i, i ∈ norm x ↔ i ∈ x ∧ ¬ comp (color i) ⊆ x) (u : Finset α) (j : κ)
    (du : Disjoint u (comp j)) : Disjoint (norm u) (comp j) :=
  Finset.disjoint_of_subset_left (normSub hnorm u) du

theorem dlZero (hcomp : ∀ i j, i ∈ comp j ↔ color i = j) {a j : κ} {h : Finset α → Bool}
    (hc : cls comp a h) (ne : j ≠ a) : dl comp h j = 0 := by
  have : h (comp j) = h ∅ := by
    apply hc
    rw [Finset.empty_inter]
    exact Finset.disjoint_iff_inter_eq_empty.mp (disj hcomp ne)
  simp [dl, this]

theorem stepCls (hcomp : ∀ i j, i ∈ comp j ↔ color i = j) {a : κ} {h : Finset α → Bool}
    (hc : cls comp a h) (u : Finset α) (j : κ) (du : Disjoint u (comp j)) :
    ((h (u ∪ comp j)).toNat : Int) - (h u).toNat = dl comp h j := by
  by_cases e : j = a
  · subst e
    have h1 : h (u ∪ comp j) = h (comp j) := by
      apply hc
      rw [Finset.union_inter_distrib_right, Finset.disjoint_iff_inter_eq_empty.mp du]
      simp
    have h2 : h u = h ∅ := by
      apply hc
      rw [Finset.disjoint_iff_inter_eq_empty.mp du]
      simp
    simp [dl, h1, h2]
  · rw [dlZero hcomp hc e]
    have : h (u ∪ comp j) = h u := by
      apply hc
      rw [Finset.union_inter_distrib_right,
        Finset.disjoint_iff_inter_eq_empty.mp (disj hcomp e)]
      simp
    simp [this]

theorem stepGood (hcomp : ∀ i j, i ∈ comp j ↔ color i = j) {h : Finset α → Bool}
    (hg : good comp h) (u : Finset α) (j : κ) (du : Disjoint u (comp j)) :
    ((h (u ∪ comp j)).toNat : Int) - (h u).toNat = dl comp h j := by
  rcases hg with hc | ⟨a, hc⟩
  · simp [dl, hc (u ∪ comp j) u, hc (comp j) ∅]
  · exact stepCls hcomp hc u j du

theorem shiftCls (hcomp : ∀ i j, i ∈ comp j ↔ color i = j)
    (hnorm : ∀ x i, i ∈ norm x ↔ i ∈ x ∧ ¬ comp (color i) ⊆ x) {a : κ} {h : Finset α → Bool}
    (hc : cls comp a h) (x : Finset α) :
    (comp a ⊆ x → ((h x).toNat : Int) = (h (norm x)).toNat + dl comp h a) ∧
    (¬ comp a ⊆ x → h x = h (norm x)) := by
  constructor
  · intro s
    have h1 : h x = h (comp a) := by
      apply hc
      rw [Finset.inter_self]
      exact Finset.inter_eq_right.mpr s
    have h2 : h (norm x) = h ∅ := by
      apply hc
      rw [Finset.empty_inter, Finset.eq_empty_iff_forall_notMem]
      intro i hi
      obtain ⟨hi1, hi2⟩ := Finset.mem_inter.mp hi
      have := ((hnorm x i).mp hi1).2
      rw [(hcomp i a).mp hi2] at this
      exact this s
    simp [dl, h1, h2]
  · intro s
    apply hc
    ext i
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(hnorm x i).mpr ⟨h1, ?_⟩, h2⟩
      rw [(hcomp i a).mp h2]
      exact s
    · rintro ⟨h1, h2⟩
      exact ⟨normSub hnorm x h1, h2⟩

theorem toNatEq (p q : Bool) : p = q ↔ (p.toNat : Int) = q.toNat := by
  cases p <;> cases q <;> simp

theorem agree (hcomp : ∀ i j, i ∈ comp j ↔ color i = j)
    (hnorm : ∀ x i, i ∈ norm x ↔ i ∈ x ∧ ¬ comp (color i) ⊆ x) {f g : Finset α → Bool}
    (hf : good comp f) (hg : good comp g) (hd : dl comp f = dl comp g) (x : Finset α) :
    f x = g x ↔ f (norm x) = g (norm x) := by
  have dlc : ∀ {h : Finset α → Bool}, (∀ x y, h x = h y) → ∀ j, dl comp h j = 0 := by
    intro h hc j
    simp [dl, hc (comp j) ∅]
  rcases hf with hf | ⟨a, hf⟩ <;> rcases hg with hg | ⟨b, hg⟩
  · rw [hf x (norm x), hg x (norm x)]
  · have z : dl comp g b = 0 := by rw [← hd]; exact dlc hf b
    have : g x = g (norm x) := by
      by_cases s : comp b ⊆ x
      · rw [toNatEq, (shiftCls hcomp hnorm hg x).1 s, z, add_zero]
      · exact (shiftCls hcomp hnorm hg x).2 s
    rw [hf x (norm x), this]
  · have z : dl comp f a = 0 := by rw [hd]; exact dlc hg a
    have : f x = f (norm x) := by
      by_cases s : comp a ⊆ x
      · rw [toNatEq, (shiftCls hcomp hnorm hf x).1 s, z, add_zero]
      · exact (shiftCls hcomp hnorm hf x).2 s
    rw [hg x (norm x), this]
  · have fx : ((f x).toNat : Int) = (f (norm x)).toNat +
        (if comp a ⊆ x then dl comp f a else 0) := by
      by_cases s : comp a ⊆ x
      · rw [if_pos s, (shiftCls hcomp hnorm hf x).1 s]
      · rw [if_neg s, (shiftCls hcomp hnorm hf x).2 s, add_zero]
    have gx : ((g x).toNat : Int) = (g (norm x)).toNat +
        (if comp b ⊆ x then dl comp g b else 0) := by
      by_cases s : comp b ⊆ x
      · rw [if_pos s, (shiftCls hcomp hnorm hg x).1 s]
      · rw [if_neg s, (shiftCls hcomp hnorm hg x).2 s, add_zero]
    have same : (if comp a ⊆ x then dl comp f a else 0) =
        (if comp b ⊆ x then dl comp g b else 0) := by
      by_cases e : a = b
      · subst e; rw [hd]
      · have z1 : dl comp f a = 0 := by
          rw [hd]; exact dlZero hcomp hg e
        have z2 : dl comp g b = 0 := by
          rw [← hd]; exact dlZero hcomp hf (Ne.symm e)
        simp [z1, z2]
    rw [toNatEq, toNatEq, fx, gx, same]
    omega

end gen

theorem forest {α : Type} {inst : DecidableEq α} {c : Nat} (comp : Fin c → Finset α)
    (disj : ∀ i j, i ≠ j → Disjoint (comp i) (comp j)) (ne : ∀ j, (comp j).Nonempty) :
    ∀ (Y : Finset (Finset α)) (D : Finset (Fin c)), Y.Nonempty →
      (∀ j ∈ D, ∃ u ∈ Y, Disjoint u (comp j) ∧ u ∪ comp j ∈ Y) → D.card + 1 ≤ Y.card := by
  intro Y
  induction Y using Finset.strongInduction with
  | H Y ih =>
  intro D hY hD
  rcases D.eq_empty_or_nonempty with rfl | ⟨j, hj⟩
  · simpa using hY.card_pos
  let Y0 := Y.filter (fun u => ¬ comp j ⊆ u)
  let Y1 := Y.filter (fun u => comp j ⊆ u)
  obtain ⟨u, hu, du, hu'⟩ := hD j hj
  have notsub : ¬ comp j ⊆ u := by
    intro h
    obtain ⟨i, hi⟩ := ne j
    exact Finset.disjoint_left.mp du (h hi) hi
  have n0 : Y0.Nonempty := ⟨u, Finset.mem_filter.mpr ⟨hu, notsub⟩⟩
  have n1 : Y1.Nonempty := ⟨u ∪ comp j, Finset.mem_filter.mpr ⟨hu', Finset.subset_union_right⟩⟩
  have split : Y0.card + Y1.card = Y.card := by
    have := Finset.card_filter_add_card_filter_not (s := Y) (fun u => comp j ⊆ u)
    simp only [Y0, Y1]; omega
  have s0 : Y0 ⊂ Y := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro h
    have := n1.card_pos
    rw [h] at split; omega
  have s1 : Y1 ⊂ Y := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro h
    have := n0.card_pos
    rw [h] at split; omega
  let D0 := (D.erase j).filter (fun k => ∃ v ∈ Y0, Disjoint v (comp k) ∧ v ∪ comp k ∈ Y0)
  let D1 := (D.erase j).filter (fun k => ¬ ∃ v ∈ Y0, Disjoint v (comp k) ∧ v ∪ comp k ∈ Y0)
  have h0 := ih Y0 s0 D0 n0 (fun k hk => (Finset.mem_filter.mp hk).2)
  have stay (k : Fin c) (hk : k ≠ j) (v : Finset α) :
      comp j ⊆ v ∪ comp k ↔ comp j ⊆ v := by
    constructor
    · intro h i hi
      rcases Finset.mem_union.mp (h hi) with h' | h'
      · exact h'
      · exact absurd h' (Finset.disjoint_left.mp (disj j k (Ne.symm hk)) hi)
    · intro h
      exact h.trans Finset.subset_union_left
  have h1 := ih Y1 s1 D1 n1 (by
    intro k hk
    obtain ⟨hk, no⟩ := Finset.mem_filter.mp hk
    obtain ⟨hkj, hkD⟩ := Finset.mem_erase.mp hk
    obtain ⟨v, hv, dv, hv'⟩ := hD k hkD
    by_cases hs : comp j ⊆ v
    · exact ⟨v, Finset.mem_filter.mpr ⟨hv, hs⟩, dv,
        Finset.mem_filter.mpr ⟨hv', (stay k hkj v).mpr hs⟩⟩
    · exact absurd ⟨v, Finset.mem_filter.mpr ⟨hv, hs⟩, dv,
        Finset.mem_filter.mpr ⟨hv', fun h => hs ((stay k hkj v).mp h)⟩⟩ no)
  have hsplit := Finset.card_filter_add_card_filter_not (s := D.erase j)
    (fun k => ∃ v ∈ Y0, Disjoint v (comp k) ∧ v ∪ comp k ∈ Y0)
  have he := Finset.card_erase_add_one hj
  simp only [D0, D1] at h0 h1
  omega

theorem hallAssign {c : Nat} {β : Type} (P : Finset β) (M : β → Nat) (b : Nat)
    (elig : Fin c → β → Prop) :
    letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
    (∀ z ∈ P, 0 < M z) → (∀ j, ∃ z ∈ P, elig j z) →
    (∀ T : Finset (Fin c), T.card ≤ b + (P.filter (fun z => ∃ j ∈ T, elig j z)).sum (fun z => M z - 1)) →
    ∃ σ : Fin c → β, (∀ j, σ j ∈ P ∧ elig j (σ j)) ∧ ∃ u : β → Nat,
      (∀ z ∈ P, (Finset.univ.filter (fun j => σ j = z)).card + 1 ≤ M z + u z) ∧ P.sum u ≤ b := by
  classical
  intro hM cover hall
  let R := fun _ : β => Nat
  let X := fun j : Fin c => (P.filter (elig j)).sigma (fun z => Finset.range (M z - 1))
  let t := fun j : Fin c => (X j).disjSum (Finset.range b)
  have cond : ∀ s : Finset (Fin c), s.card ≤ (s.biUnion t).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | ⟨j0, hj0⟩
    · simp
    have eq : s.biUnion t = ((P.filter (fun z => ∃ j ∈ s, elig j z)).sigma
        (fun z => Finset.range (M z - 1))).disjSum (Finset.range b) := by
      ext q
      rcases q with ⟨z, k⟩ | k
      · simp only [t, X, Finset.mem_biUnion, Finset.inl_mem_disjSum, Finset.mem_sigma,
          Finset.mem_filter]
        constructor
        · rintro ⟨j, hj, ⟨hz, e⟩, hk⟩
          exact ⟨⟨hz, j, hj, e⟩, hk⟩
        · rintro ⟨⟨hz, j, hj, e⟩, hk⟩
          exact ⟨j, hj, ⟨hz, e⟩, hk⟩
      · simp only [t, Finset.mem_biUnion, Finset.inr_mem_disjSum]
        exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨j0, hj0, h⟩⟩
    rw [eq, Finset.card_disjSum, Finset.card_sigma]
    rw [Nat.add_comm]
    convert hall s using 3
    all_goals first | simp | congr 1
  obtain ⟨f, inj, mem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp cond
  let ε := fun j => (cover j).choose
  have hε (j) : ε j ∈ P ∧ elig j (ε j) := (cover j).choose_spec
  let σ := fun j => Sum.elim (fun q : (Σ _ : β, Nat) => q.1) (fun _ => ε j) (f j)
  let isR := fun j => ∃ k, f j = Sum.inr k
  let u := fun z => (Finset.univ.filter (fun j => isR j ∧ ε j = z)).card
  refine ⟨σ, ?_, u, ?_, ?_⟩
  · intro j
    have m := mem j
    rcases h : f j with ⟨z, k⟩ | k
    · rw [h] at m
      simp only [t, X, Finset.inl_mem_disjSum, Finset.mem_sigma, Finset.mem_filter] at m
      simp only [σ, h, Sum.elim_inl]
      exact m.1
    · simp only [σ, h, Sum.elim_inr]
      exact hε j
  · intro z hz
    let Aset := Finset.univ.filter (fun j => ∃ k, f j = Sum.inl ⟨z, k⟩)
    let Bset := Finset.univ.filter (fun j => isR j ∧ ε j = z)
    have sub : Finset.univ.filter (fun j => σ j = z) ⊆ Aset ∪ Bset := by
      intro j hj
      have hj := (Finset.mem_filter.mp hj).2
      rcases h : f j with ⟨z', k⟩ | k
      · simp only [σ, h, Sum.elim_inl] at hj
        subst hj
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, h⟩)
      · simp only [σ, h, Sum.elim_inr] at hj
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨k, h⟩, hj⟩)
    let g := fun j => Sum.elim (fun q : (Σ _ : β, Nat) => q.2) (fun _ => 0) (f j)
    have ga : Aset.card ≤ (Finset.range (M z - 1)).card := by
      apply Finset.card_le_card_of_injOn g
      · intro j hj
        obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hj).2
        have m := mem j
        rw [hk] at m
        simp only [t, X, Finset.inl_mem_disjSum, Finset.mem_sigma] at m
        simpa [g, hk] using m.2
      · intro j hj j' hj' e
        obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hj).2
        obtain ⟨k', hk'⟩ := (Finset.mem_filter.mp hj').2
        simp only [g, hk, hk', Sum.elim_inl] at e
        apply inj
        rw [hk, hk', e]
    have := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
    simp only [Finset.card_range] at ga
    have := hM z hz
    have : Bset.card = u z := rfl
    omega
  · have fib := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter isR) (t := P)
      (f := ε) (fun j _ => (hε j).1)
    have same : P.sum u = ∑ z ∈ P, ((Finset.univ.filter isR).filter (fun j => ε j = z)).card := by
      apply Finset.sum_congr rfl
      intro z _
      simp only [u, Finset.filter_filter]
    rw [same, ← fib]
    let g := fun j => Sum.elim (fun _ : (Σ _ : β, Nat) => 0) (fun k => k) (f j)
    have := Finset.card_le_card_of_injOn (s := Finset.univ.filter isR) (t := Finset.range b) g
      (by
        intro j hj
        obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hj).2
        have m := mem j
        rw [hk] at m
        simp only [t, Finset.inr_mem_disjSum] at m
        simpa [g, hk] using m)
      (by
        intro j hj j' hj' e
        obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hj).2
        obtain ⟨k', hk'⟩ := (Finset.mem_filter.mp hj').2
        simp only [g, hk, hk', Sum.elim_inr] at e
        apply inj
        rw [hk, hk', e])
    simpa using this

theorem keepsBridge (n c : Nat) (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c)
    (sorted : ∀ e ∈ E, e.1 < e.2) (onto : Function.Surjective color)
    (part : ∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
      ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z)) (A : Finset (Finset (Fin n))) :
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let W := Finset (Fin n)
  let bit := fun (i : Fin n) (x : W) => decide (i ∈ x)
  let neg := fun (i : Fin n) (x : W) => !(bit i x)
  let same := fun (e : Fin n × Fin n) (x : W) => bit e.1 x == bit e.2 x
  let raw : Finset (W → Bool) := {fun _ => false,fun _ => true} ∪ Finset.univ.image bit ∪
    E.image same ∪ E.image (fun e x => !(same e x))
  let need := Finset.univ.image neg ∪ E.image (fun e x => neg e.1 x && neg e.2 x) ∪
    E.image (fun e x => bit e.1 x && neg e.2 x) ∪ E.image (fun e x => neg e.1 x && bit e.2 x)
  let comp := fun j : Fin c => Finset.univ.filter (fun i : Fin n => color i = j)
  (∀ (S : W) (p : Nat),
    let L := (raw ∪ S.image neg).toList
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length C ∧
      C.output < L.length+C.size ∧ C.size ≤ p ∧ ∀ f ∈ need, ∃ j < L.length+C.size,
        ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = f x) ↔
    (∀ j, ∃ i ∈ S, color i = j) ∧ n+3*E.card-S.card ≤ p) ↔
  ((∀ j, ∃ u ∈ A, Disjoint u (comp j) ∧ u ∪ comp j ∈ A) ∧
    ∀ f ∈ need, ∀ g : W → Bool, (g ∈ raw ∨ (g ∈ need ∧ f ≠ g)) → ∃ x ∈ A, f x ≠ g x) := by
  intro W bit neg same raw need comp
  have cr := PEqualNP.GraphSampleDistance.criterion n c E color onto sorted part A (fun _ => 1) 0
    (by simp)
  dsimp only at cr
  have filt : ∀ lost : Finset (Fin n) → Nat, A.sum lost ≤ 0 →
      A.filter (fun u => lost u < 1) = A := by
    intro lost hl
    apply Finset.filter_true_of_mem
    intro u hu
    have := Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hl) u hu
    omega
  simp (config := {contextual := true}) only [filt, Finset.image_union, Finset.image_image,
    Function.comp_def] at cr
  refine Iff.trans ?_ (cr.trans ?_)
  · constructor
    · intro h lost _
      convert! h using 0
      congr! 80
      all_goals (rename_i a u; first
        | (by_cases h1 : a.1 ∈ u <;> by_cases h2 : a.2 ∈ u <;> simp [same, bit, h1, h2])
        | (by_cases h1 : a ∈ u <;> simp [neg, bit, h1]))
    · intro h
      have h' := h (fun _ => 0) (by simp)
      convert! h' using 0
      congr! 80
      all_goals (rename_i a u; first
        | (by_cases h1 : a.1 ∈ u <;> by_cases h2 : a.2 ∈ u <;> simp [same, bit, h1, h2])
        | (by_cases h1 : a ∈ u <;> simp [neg, bit, h1]))
  · simp only [min_self, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_pos,
      Finset.filter_nonempty_iff]
    have inj : Function.Injective (fun (f : (Fin n → Bool) → Bool) (u : Finset (Fin n)) =>
        f (fun i => decide (i ∈ u))) := by
      intro f g h
      funext x
      have := congrFun h (Finset.univ.filter (fun i => x i = true))
      simpa using this
    have key : ∀ T R : Finset ((Fin n → Bool) → Bool),
        ((∀ f ∈ T, ∀ g ∈ T, f ≠ g → ∃ u ∈ A, f (fun i => decide (i ∈ u)) ≠ g (fun i => decide (i ∈ u))) ∧
          ∀ f ∈ T, ∀ g ∈ R, ∃ u ∈ A, f (fun i => decide (i ∈ u)) ≠ g (fun i => decide (i ∈ u))) ↔
        ∀ f ∈ T.image (fun (f : (Fin n → Bool) → Bool) (u : Finset (Fin n)) => f (fun i => decide (i ∈ u))),
          ∀ g : Finset (Fin n) → Bool, (g ∈ R.image (fun (f : (Fin n → Bool) → Bool) (u : Finset (Fin n)) =>
            f (fun i => decide (i ∈ u))) ∨ (g ∈ T.image (fun (f : (Fin n → Bool) → Bool) (u : Finset (Fin n)) =>
            f (fun i => decide (i ∈ u))) ∧ f ≠ g)) → ∃ x ∈ A, f x ≠ g x := by
      intro T R
      constructor
      · rintro ⟨h1, h2⟩ f hf g hg
        obtain ⟨f, hf', rfl⟩ := Finset.mem_image.mp hf
        rcases hg with hg | ⟨hg, ne⟩
        · obtain ⟨g, hg', rfl⟩ := Finset.mem_image.mp hg
          exact h2 f hf' g hg'
        · obtain ⟨g, hg', rfl⟩ := Finset.mem_image.mp hg
          exact h1 f hf' g hg' (fun e => ne (by rw [e]))
      · intro h
        refine ⟨fun f hf g hg ne => ?_, fun f hf g hg => ?_⟩
        · exact h _ (Finset.mem_image_of_mem _ hf) _ (Or.inr ⟨Finset.mem_image_of_mem _ hg,
            fun e => ne (inj e)⟩)
        · exact h _ (Finset.mem_image_of_mem _ hf) _ (Or.inl (Finset.mem_image_of_mem _ hg))
    refine (Iff.and Iff.rfl (key _ _)).trans ?_
    have hx : (fun (x : Fin n × Fin n) (u : Finset (Fin n)) => decide (x.1 ∈ u) ^^ decide (x.2 ∈ u)) =
        fun (x : Fin n × Fin n) (u : Finset (Fin n)) => !(decide (x.1 ∈ u) == decide (x.2 ∈ u)) := by
      funext x u
      cases decide (x.1 ∈ u) <;> cases decide (x.2 ∈ u) <;> rfl
    simp only [Finset.image_union, Finset.image_image, Function.comp_def, Finset.image_insert,
      Finset.image_singleton]
    rw [hx]
    constructor <;> intro h <;> convert! h using 0 <;> congr! 80
    all_goals (rename_i a u; first
      | (by_cases h1 : a.1 ∈ u <;> by_cases h2 : a.2 ∈ u <;> simp [same, neg, bit, h1, h2])
      | (by_cases h1 : a ∈ u <;> simp [neg, bit, h1]))

theorem ar1 (D Wz M : Nat) (h1 : D + 1 ≤ Wz) (h2 : M ≤ Wz) (h3 : 0 < M) :
    D ≤ (M - 1) + (Wz - M) := by omega

theorem ar2 (T X A1 A2 A3 SM SW Sw b : Nat) (F1 : T ≤ X) (F2 : X ≤ A1 + A2) (F4 : A2 ≤ A3)
    (F5 : A3 + SM = SW) (F6 : SW ≤ Sw) (ht : Sw ≤ SM + b) : T ≤ b + A1 := by omega

theorem ar3 (M k : Nat) : M ≤ max (M - k) 1 + k := by
  rcases le_total (M - k) 1 with h | h
  · rw [max_eq_right h]; omega
  · rw [max_eq_left h]; omega

theorem ar4 (M k u : Nat) (h : k + 1 ≤ M + u) : max (M - k) 1 + k ≤ M + u := by
  rcases le_total (M - k) 1 with h' | h'
  · rw [max_eq_right h']; omega
  · rw [max_eq_left h']; omega

theorem ar5 (Sw S1 S2 Smax c Sk SM Su b : Nat) (t1 : Sw = S1 + S2) (t2 : S1 = Smax) (t3 : S2 = c)
    (t4 : c = Sk) (t5 : Smax + Sk ≤ SM + Su) (hub : Su ≤ b) : Sw ≤ SM + b := by omega

theorem ar6 (M a b c d : Nat) (h1 : M ≤ a + b) (h2 : a ≤ c) (h3 : b ≤ d) : M ≤ c + d := by omega

end PEqualNP.Outside.L_meta_57336

open PEqualNP.Outside.L_meta_57336

theorem PEqualNP.Outside.L_meta_57336 : ∀ (n c : Nat) (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c),
  (∀ e ∈ E, e.1 < e.2) → Function.Surjective color →
  (∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
    ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z)) →
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let W := Finset (Fin n)
  let bit := fun (i : Fin n) (x : W) => decide (i ∈ x)
  let neg := fun (i : Fin n) (x : W) => !(bit i x)
  let same := fun (e : Fin n × Fin n) (x : W) => bit e.1 x == bit e.2 x
  let raw : Finset (W → Bool) := {fun _ => false,fun _ => true} ∪ Finset.univ.image bit ∪
    E.image same ∪ E.image (fun e x => !(same e x))
  let need := Finset.univ.image neg ∪ E.image (fun e x => neg e.1 x && neg e.2 x) ∪
    E.image (fun e x => bit e.1 x && neg e.2 x) ∪ E.image (fun e x => neg e.1 x && bit e.2 x)
  let keeps := fun A : Finset W => ∀ (S : W) (p : Nat),
    let L := (raw ∪ S.image neg).toList
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length C ∧
      C.output < L.length+C.size ∧ C.size ≤ p ∧ ∀ f ∈ need, ∃ j < L.length+C.size,
        ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = f x) ↔
    (∀ j, ∃ i ∈ S, color i = j) ∧ n+3*E.card-S.card ≤ p
  let comp := fun j : Fin c => Finset.univ.filter (fun i : Fin n => color i = j)
  let norm := fun x : W => x.filter (fun i => ¬ comp (color i) ⊆ x)
  let delta := fun (f : W → Bool) (j : Fin c) =>
    ((f (comp j)).toNat : Int) - ((f ∅).toNat : Int)
  let admissible := fun P : Finset W => P.image norm = P ∧
    (∀ j, ∃ z ∈ P, Disjoint z (comp j)) ∧
    ∀ f ∈ need, ∀ g : W → Bool, (g ∈ raw ∨ (g ∈ need ∧ f ≠ g)) →
      delta f = delta g → ∃ z ∈ P, f z ≠ g z
  ∀ (P : Finset W) (M : W → Nat) (b : Nat) (_hM : ∀ z ∈ P, 0 < M z),
  (∃ w : W → Nat,
    let A := Finset.univ.filter (fun x : W => 0 < w x)
    A.image norm = P ∧ keeps A ∧
    (∀ z ∈ P, M z ≤ (Finset.univ.filter (fun x : W => norm x = z)).sum w) ∧
    (∑ x, w x) ≤ P.sum M + b) ↔
  admissible P ∧ ∀ T : Finset (Fin c),
    T.card ≤ b + (P.filter (fun z => ∃ j ∈ T, Disjoint z (comp j))).sum (fun z => M z - 1) := by
  intro n c E color sorted onto part W bit neg same raw need keeps comp norm delta admissible
    P M b hM
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  have hcomp : ∀ i j, i ∈ comp j ↔ color i = j := by intro i j; simp [comp]
  have hnorm : ∀ x i, i ∈ norm x ↔ i ∈ x ∧ ¬ comp (color i) ⊆ x := by intro x i; simp [norm]
  have sameColor : ∀ e ∈ E, color e.1 = color e.2 := by
    intro e he
    have h := (part (comp (color e.1))).mpr (by intro i k hik; rw [hcomp, hcomp, hik]) e he
    exact ((hcomp _ _).mp (h.mp ((hcomp _ _).mpr rfl))).symm
  have ne : ∀ j, (comp j).Nonempty := fun j =>
    ⟨(onto j).choose, (hcomp _ _).mpr (onto j).choose_spec⟩
  have dsj : ∀ i j, i ≠ j → Disjoint (comp i) (comp j) := fun i j h => disj hcomp h
  have gd := goodAll n c E color sameColor comp hcomp
  have kb := fun A => keepsBridge n c E color sorted onto part A
  dsimp only at gd kb
  constructor
  · rintro ⟨w, hex⟩
    dsimp only at hex
    obtain ⟨hA, hk, hfib, htot⟩ := hex
    obtain ⟨C1, Sep⟩ := (kb _).mp hk
    have memA : ∀ x, x ∈ Finset.univ.filter (fun x : W => 0 < w x) ↔ 0 < w x := by
      intro x; simp
    have normA : ∀ x ∈ Finset.univ.filter (fun x : W => 0 < w x), norm x ∈ P :=
      fun x hx => hA ▸ Finset.mem_image_of_mem _ hx
    have Pnorm : ∀ z ∈ P, norm z = z := by
      intro z hz
      rw [← hA] at hz
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
      exact normIdem hnorm y
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · ext z
      constructor
      · intro hz
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
        rw [Pnorm y hy]; exact hy
      · intro hz
        exact Finset.mem_image.mpr ⟨z, hz, Pnorm z hz⟩
    · intro j
      obtain ⟨u, hu, du, _⟩ := C1 j
      exact ⟨norm u, normA u hu, normDisj hnorm u j du⟩
    · intro f hf g hg hd
      obtain ⟨x, hx, hne⟩ := Sep f hf g hg
      refine ⟨norm x, normA x hx, ?_⟩
      have hgg : good comp g := by
        rcases hg with hg | ⟨hg, _⟩
        · exact gd g (Or.inl hg)
        · exact gd g (Or.inr hg)
      exact fun h => hne ((agree hcomp hnorm (gd f (Or.inr hf)) hgg hd x).mpr h)
    · intro T
      let A := Finset.univ.filter (fun x : W => 0 < w x)
      let Y := fun z : W => A.filter (fun x => norm x = z)
      let Wz := fun z : W => (Finset.univ.filter (fun x : W => norm x = z)).sum w
      let PT := P.filter (fun z => ∃ j ∈ T, Disjoint z (comp j))
      let D := fun z : W => T.filter (fun j => ∃ u ∈ Y z, Disjoint u (comp j) ∧ u ∪ comp j ∈ Y z)
      have cov : T ⊆ PT.biUnion D := by
        intro j hj
        obtain ⟨u, hu, du, hu'⟩ := C1 j
        have np : norm (u ∪ comp j) = norm u := normPair hcomp hnorm u j du
        refine Finset.mem_biUnion.mpr ⟨norm u, Finset.mem_filter.mpr ⟨normA u hu, j, hj,
          normDisj hnorm u j du⟩, Finset.mem_filter.mpr ⟨hj, u, Finset.mem_filter.mpr ⟨hu, rfl⟩,
          du, Finset.mem_filter.mpr ⟨hu', np⟩⟩⟩
      have F1 : T.card ≤ ∑ z ∈ PT, (D z).card :=
        (Finset.card_le_card cov).trans Finset.card_biUnion_le
      have YW : ∀ z ∈ P, (D z).card + 1 ≤ Wz z := by
        intro z hz
        have nY : (Y z).Nonempty := by
          rw [← hA] at hz
          obtain ⟨y, hy, hyz⟩ := Finset.mem_image.mp hz
          exact ⟨y, Finset.mem_filter.mpr ⟨hy, hyz⟩⟩
        have fo := forest comp dsj ne (Y z) (D z) nY (fun j hj => (Finset.mem_filter.mp hj).2)
        have c1 : (Y z).card ≤ (Y z).sum w := by
          rw [Finset.card_eq_sum_ones]
          apply Finset.sum_le_sum
          intro x hx
          exact (memA x).mp (Finset.mem_filter.mp hx).1
        have c2 : (Y z).sum w ≤ Wz z := by
          apply Finset.sum_le_sum_of_subset
          intro x hx
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
        exact fo.trans (c1.trans c2)
      have F2 : ∑ z ∈ PT, (D z).card ≤ ∑ z ∈ PT, ((M z - 1) + (Wz z - M z)) := by
        apply Finset.sum_le_sum
        intro z hz
        have hzP := (Finset.mem_filter.mp hz).1
        have := YW z hzP
        have := hfib z hzP
        change M z ≤ Wz z at this
        exact ar1 _ _ _ (YW z hzP) this (hM z hzP)
      rw [Finset.sum_add_distrib] at F2
      have F4 : ∑ z ∈ PT, (Wz z - M z) ≤ ∑ z ∈ P, (Wz z - M z) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      have F5 : ∑ z ∈ P, (Wz z - M z) + ∑ z ∈ P, M z = ∑ z ∈ P, Wz z := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro z hz
        have := hfib z hz
        change M z ≤ Wz z at this
        exact Nat.sub_add_cancel this
      have F6 : ∑ z ∈ P, Wz z ≤ ∑ x, w x := by
        have fw := Finset.sum_fiberwise_of_maps_to
          (s := Finset.univ.filter (fun x : W => norm x ∈ P)) (t := P) (g := norm)
          (fun x hx => (Finset.mem_filter.mp hx).2) w
        have eq : ∀ z ∈ P, Wz z = ∑ x ∈ (Finset.univ.filter (fun x : W => norm x ∈ P)).filter
            (fun x => norm x = z), w x := by
          intro z hz
          apply Finset.sum_congr _ (fun _ _ => rfl)
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro rfl; exact ⟨hz, rfl⟩
          · exact fun h => h.2
        rw [Finset.sum_congr rfl eq, fw]
        exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      change T.card ≤ b + ∑ z ∈ PT, (M z - 1)
      exact ar2 _ _ _ _ _ _ _ _ _ F1 F2 F4 F5 F6 htot
  · rintro ⟨⟨hPn, hcov, hsep⟩, hall⟩
    obtain ⟨σ, hσ, u, hu, hub⟩ := hallAssign P M b (fun j z => Disjoint z (comp j)) hM hcov hall
    have Pnorm : ∀ z ∈ P, norm z = z := by
      intro z hz
      rw [← hPn] at hz
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
      exact normIdem hnorm y
    let k := fun z : W => (Finset.univ.filter (fun j => σ j = z)).card
    let cnt := fun x : W => (Finset.univ.filter (fun j => σ j ∪ comp j = x)).card
    let w := fun x : W => (if x ∈ P then max (M x - k x) 1 else 0) + cnt x
    have pn : ∀ j, norm (σ j ∪ comp j) = σ j := fun j =>
      (normPair hcomp hnorm (σ j) j (hσ j).2).trans (Pnorm _ (hσ j).1)
    refine ⟨w, ?_⟩
    intro A
    have memA : ∀ x, x ∈ A ↔ 0 < w x := by intro x; simp [A]
    have PA : ∀ z ∈ P, z ∈ A := by
      intro z hz
      rw [memA]
      simp only [w, if_pos hz]
      exact Nat.lt_of_lt_of_le (lt_max_of_lt_right Nat.one_pos) (Nat.le_add_right _ _)
    have pairA : ∀ j, σ j ∪ comp j ∈ A := by
      intro j
      rw [memA]
      have : 0 < cnt (σ j ∪ comp j) :=
        Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
      simp only [w]
      exact Nat.lt_of_lt_of_le this (Nat.le_add_left _ _)
    have supp : ∀ x ∈ A, x ∈ P ∨ ∃ j, σ j ∪ comp j = x := by
      intro x hx
      by_cases hP : x ∈ P
      · exact Or.inl hP
      · right
        rw [memA] at hx
        simp only [w, if_neg hP, zero_add] at hx
        obtain ⟨j, hj⟩ := Finset.card_pos.mp hx
        exact ⟨j, (Finset.mem_filter.mp hj).2⟩
    have C1 : ∀ j, ∃ v ∈ A, Disjoint v (comp j) ∧ v ∪ comp j ∈ A :=
      fun j => ⟨σ j, PA _ (hσ j).1, (hσ j).2, pairA j⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext z
      constructor
      · intro hz
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
        rcases supp x hx with h | ⟨j, rfl⟩
        · rw [Pnorm x h]; exact h
        · rw [pn j]; exact (hσ j).1
      · intro hz
        exact Finset.mem_image.mpr ⟨z, PA z hz, Pnorm z hz⟩
    · apply (kb A).mpr
      refine ⟨C1, ?_⟩
      intro f hf g hg
      have hgg : good comp g := by
        rcases hg with hg | ⟨hg, _⟩
        · exact gd g (Or.inl hg)
        · exact gd g (Or.inr hg)
      by_cases hd : delta f = delta g
      · obtain ⟨z, hz, hne⟩ := hsep f hf g hg hd
        exact ⟨z, PA z hz, hne⟩
      · obtain ⟨j, hj⟩ : ∃ j, delta f j ≠ delta g j := by
          by_contra h
          push_neg at h
          exact hd (funext h)
        obtain ⟨v, hv, dv, hv'⟩ := C1 j
        by_contra hno
        push_neg at hno
        have s1 := stepGood hcomp (gd f (Or.inr hf)) v j dv
        have s2 := stepGood hcomp hgg v j dv
        rw [hno _ hv, hno _ hv'] at s1
        exact hj (s1.symm.trans s2)
    · intro z hz
      let F := Finset.univ.filter (fun x : W => norm x = z)
      have zF : z ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Pnorm z hz⟩
      have e1 : F.sum w = F.sum (fun x => if x ∈ P then max (M x - k x) 1 else 0) + F.sum cnt :=
        Finset.sum_add_distrib
      have e2 : (if z ∈ P then max (M z - k z) 1 else 0) ≤
          F.sum (fun x => if x ∈ P then max (M x - k x) 1 else 0) :=
        Finset.single_le_sum (f := fun x => if x ∈ P then max (M x - k x) 1 else 0)
          (fun _ _ => Nat.zero_le _) zF
      rw [if_pos hz] at e2
      have e3 : k z ≤ F.sum cnt := by
        have fib := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter (fun j => σ j = z))
          (t := F) (f := fun j => σ j ∪ comp j) (by
            intro j hj
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (pn j).trans (Finset.mem_filter.mp hj).2⟩)
        change k z = _ at fib
        rw [fib]
        apply Finset.sum_le_sum
        intro x _
        exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
      change M z ≤ F.sum w
      rw [e1]
      exact ar6 _ _ _ _ _ (ar3 (M z) (k z)) e2 e3
    · have t1 : ∑ x, w x = ∑ x, (if x ∈ P then max (M x - k x) 1 else 0) + ∑ x, cnt x :=
        Finset.sum_add_distrib
      have t2 : ∑ x, (if x ∈ P then max (M x - k x) 1 else 0) = ∑ x ∈ P, max (M x - k x) 1 := by
        rw [← Finset.sum_filter]
        congr 1
        ext x
        simp
      have t3 : ∑ x, cnt x = c := by
        have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin c)))
          (t := (Finset.univ : Finset W)) (f := fun j => σ j ∪ comp j) (fun _ _ => Finset.mem_univ _)
        simp only [Finset.card_univ, Fintype.card_fin] at this
        exact this.symm
      have t4 : c = ∑ z ∈ P, k z := by
        have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin c)))
          (t := P) (f := σ) (fun j _ => (hσ j).1)
        simp only [Finset.card_univ, Fintype.card_fin] at this
        exact this
      have t5 : ∑ z ∈ P, (max (M z - k z) 1 + k z) ≤ ∑ z ∈ P, (M z + u z) := by
        apply Finset.sum_le_sum
        intro z hz
        have := hu z hz
        change k z + 1 ≤ M z + u z at this
        exact ar4 _ _ _ this
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at t5
      change ∑ x, w x ≤ P.sum M + b
      exact ar5 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 hub
