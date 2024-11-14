theory TimeComplexity
  imports Main OBHeaps_modeling
begin
definition T_link :: "'a::linorder obtree \<Rightarrow> 'a obtree \<Rightarrow> nat" where
[simp]: "T_link _ _ = 1"

definition T_make_heap :: "'a::linorder \<Rightarrow> nat" where
[simp]: "T_make_heap x = 1"

fun T_merge :: "'a::linorder obheap \<Rightarrow> 'a obheap \<Rightarrow> nat" where
  "T_merge h Empty =  1"|
  "T_merge Empty h =  1"|
  "T_merge (OBHeaps size1 min1 t1) (OBHeaps size2 min2 t2) =
          (if root min1 < root min2 then 1
                                    else 1) "
definition T_insert :: "'a::linorder \<Rightarrow> 'a obheap \<Rightarrow> nat" where
"T_insert x h = T_merge h (make_heap x) + T_make_heap x"

lemma T_merge_bound: "T_merge h1 h2 \<le>  1"
  by (induction h1 h2 rule: T_merge.induct) auto

lemma T_make_heap_bound: "T_make_heap x \<le>  1"
  by  auto

lemma T_insert_bound: "T_insert x ts \<le> 2"
  using T_insert_def T_make_heap_def
  apply (auto simp: T_make_heap_bound T_merge_bound) 
  by (smt (verit) T_insert_def T_make_heap_def 
                T_merge_bound add_le_mono1 nat_1_add_1)



fun T_get_min :: "'a::linorder obheap \<Rightarrow> nat" where
  "T_get_min h = 1"


lemma T_get_min_bound: "T_get_min fh \<le>  1"
  by auto




end