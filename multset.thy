theory multset
  imports Main
  OBHeaps_modeling
  "HOL-Library.Multiset"
begin
(*** tree to multiset ***)
fun mset_tree :: "'a::linorder obtree \<Rightarrow> 'a multiset" where
  "mset_tree (Node _ a ts) = {#a#} + (\<Sum>t\<in>#mset ts. mset_tree t)"

(*** trees to multiset ***)
definition mset_heap :: "'a::linorder trees \<Rightarrow> 'a multiset" where
  "mset_heap ts = (\<Sum>t\<in>#mset ts. mset_tree t)"

(*** obheap to multiset ***)
fun mset_obheap :: "'a::linorder obheap \<Rightarrow> 'a multiset" where
  "mset_obheap Empty = {#}"|
  "mset_obheap (OBHeaps n m xs) = mset_tree m + mset_heap xs"




(***proof of mset_tree  ***)
lemma mset_tree_nonempty[simp]: "mset_tree t \<noteq> {#}"
by (cases t) auto

lemma root_in_mset[simp]: "root t \<in># mset_tree t"
by (cases t) auto

lemma mset_tree_simp_alt[simp]:
  "mset_tree (Node r a ts) = {#a#} + mset_heap ts"
  unfolding mset_heap_def by auto
declare mset_tree.simps[simp del]

(***proof of meset_trees ***)
lemma mset_heap_Nil[simp]:
  "mset_heap [] = {#}"
by (auto simp: mset_heap_def)

lemma mset_heap_Cons[simp]: "mset_heap (t#ts) = mset_tree t + mset_heap ts"
  by (auto simp: mset_heap_def)
lemma mset_heap_Cons':" mset_tree t + mset_heap ts =mset_heap (t#ts) "
  by (auto simp: mset_heap_def)
lemma mset_heap_empty_iff[simp]: "mset_heap ts = {#} \<longleftrightarrow> ts=[]"
  by (auto simp: mset_heap_def)

lemma mset_heap_rev_eq[simp]: "mset_heap (rev ts) = mset_heap ts"
by (auto simp: mset_heap_def)

(***proof of meset_obheap ***)
lemma mset_obheap_empty[simp]:
  "mset_obheap Empty = {#}" 
  by simp

lemma mset_obheap_no_empty[simp]:
  assumes "\<not> is_empty_obheap fh"
  shows "mset_obheap fh = mset_heap (roots fh) + mset_tree (min_tree fh)"
  using assms
  apply(induct fh rule:mset_obheap.induct) 
  by auto

lemma mset_obheap_empty_iff[simp]: "mset_obheap fh = {#} \<longleftrightarrow> is_empty_obheap fh" 
  using mset_obheap.elims by force

lemma app_mset_heap:"mset_heap (x @ y) = mset_heap x + mset_heap y" 
using mset_heap_def 
  by (metis image_mset_union mset_append sum_mset.union)

lemma add_mset_tree:"mset_tree t = {#root t#} + (mset_heap (children t))"
  by (metis mset_tree_simp_alt obtree.exhaust_sel)

lemma add_mset_heaps:"mset_heap (t#ts) = {#root t#} + mset_heap ((children t) @ ts)"
  apply (auto split: obtree.split)
  apply(induct ts)
   apply (auto simp:add_mset_tree app_mset_heap)
  done

end