import KanadeRussell.Partitions.Blocks
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Unique initial-block decomposition of every admissible partition. -/
namespace KanadeRussell.Partitions

private theorem split_small (l : List ℕ) (h : Valid l) :
    ∃ s t, l = s++t ∧ (∀ a ∈ s, a ≤ 3) ∧ (∀ a ∈ t, 3 < a) := by
  induction l with
  | nil => exact ⟨[],[],rfl,by simp,by simp⟩
  | cons a l ih =>
    by_cases ha : a ≤ 3
    · obtain ⟨s,t,he,hs,ht⟩ := ih h.2.2
      exact ⟨a::s,t,by simp [he],by simpa using And.intro ha hs,ht⟩
    · refine ⟨[],a::l,rfl,by simp,?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · omega
      · have := valid_head_le a l h b hb; omega

/-- The partition conditions determine a block and a translated admissible tail. -/
theorem exists_decomposition (minimum : ℕ) (hm : 1 ≤ minimum)
    (l : List ℕ) (h : Admissible minimum l) :
    ∃ i t, l = block i ++ t.map (·+3) ∧
      (∀ a ∈ block i, minimum ≤ a) ∧ Admissible (nextMinimum i) t := by
  obtain ⟨s,u,he,hs,hu⟩ := split_small l h.2
  have hsp : Admissible 1 s := by
    refine ⟨fun a ha => hm.trans (h.1 a ?_), ?_⟩
    · rw [he]; exact List.mem_append_left u ha
    · have hv := valid_take l s.length h.2
      simpa [he] using hv
  obtain ⟨i,hi⟩ := exists_block s hsp hs
  let t := u.map (·-3)
  have ht : ∀ a ∈ t, 1 ≤ a := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    have := hu b hb; omega
  have htu : t.map (·+3) = u := by
    simp only [t, List.map_map]
    trans u.map id
    · apply List.map_congr_left
      intro a ha
      dsimp only [Function.comp_def, id_eq]
      have := hu a ha; omega
    · exact List.map_id u
  have he' : l = block i ++ t.map (·+3) := by rw [htu,hi]; exact he
  refine ⟨i,t,he',?_,?_⟩
  · intro a ha
    exact h.1 a (by rw [he']; exact List.mem_append_left _ ha)
  · apply (block_append i t ht).mp
    rw [← he']
    exact ⟨fun a ha => hm.trans (h.1 a ha),h.2⟩

theorem admissible_block_append (minimum : ℕ) (hm : 1 ≤ minimum) (hm3 : minimum ≤ 3)
    (i : Fin 7) (t : List ℕ) (ht : ∀ a ∈ t, 1 ≤ a) :
    Admissible minimum (block i ++ t.map (·+3)) ↔
      (∀ a ∈ block i, minimum ≤ a) ∧ Admissible (nextMinimum i) t := by
  constructor
  · intro h
    exact ⟨fun a ha => h.1 a (List.mem_append_left _ ha),
      (block_append i t ht).mp ⟨fun a ha => hm.trans (h.1 a ha),h.2⟩⟩
  · rintro ⟨hb,ha⟩
    have hv := (block_append i t ht).mpr ha
    refine ⟨?_,hv.2⟩
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hb a ha
    · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      omega

theorem takeWhile_block_append (i : Fin 7) (t : List ℕ) (ht : ∀ a ∈ t, 1 ≤ a) :
    (block i ++ t.map (·+3)).takeWhile (fun a => decide (a ≤ 3)) = block i := by
  have hb : (block i).takeWhile (fun a => decide (a ≤ 3)) = block i :=
    List.takeWhile_eq_self_iff.mpr (by intro a ha; simpa using (block_bounds i a ha).2)
  have hz : (t.map (·+3)).takeWhile (fun a => decide (a ≤ 3)) = [] := by
    cases t with
    | nil => rfl
    | cons a t =>
      have ha := ht a (by simp)
      simp [show ¬a+3 ≤ 3 by omega]
  rw [List.takeWhile_append,hb]
  simp [hz]

/-- No partition can be assembled from two different initial blocks or tails. -/
theorem decomposition_unique (i j : Fin 7) (s t : List ℕ)
    (hs : ∀ a ∈ s, 1 ≤ a) (ht : ∀ a ∈ t, 1 ≤ a)
    (he : block i ++ s.map (·+3) = block j ++ t.map (·+3)) : i = j ∧ s = t := by
  have hh := congrArg (List.takeWhile (fun a => decide (a ≤ 3))) he
  rw [takeWhile_block_append i s hs,takeWhile_block_append j t ht] at hh
  have hij := block_injective hh
  subst j
  have hst := List.append_cancel_left he
  have hh := congrArg (List.map (·-3)) hst
  exact ⟨rfl, by simpa [List.map_map, Function.comp_def] using hh⟩

end KanadeRussell.Partitions
