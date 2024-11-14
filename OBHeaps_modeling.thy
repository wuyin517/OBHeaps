theory OBHeaps_modeling_pro
  imports
    Main
    "HOL-Library.Pattern_Aliases"
begin


(*** Definition of a tree  ***)
datatype 'a obtree = Node (rank: nat) (root: 'a) (children: "'a obtree list")
(*** Definition of a obheap  ***)
datatype 'a obheap = Empty| OBHeaps (num: nat) (min_tree: "'a obtree") (roots: "'a obtree list")   

type_synonym 'a trees = "'a obtree list"

context
includes pattern_aliases
begin
fun link :: "'a::linorder obtree \<Rightarrow> 'a obtree \<Rightarrow> 'a obtree" where
  "link (Node r x\<^sub>1  ts\<^sub>1 =: t\<^sub>1 ) (Node r' x\<^sub>2  ts\<^sub>2=: t\<^sub>2) =
    (if x\<^sub>1\<le>x\<^sub>2 then Node (r+1) x\<^sub>1 (t\<^sub>2#ts\<^sub>1)  else Node (r+1) x\<^sub>2 (t\<^sub>1#ts\<^sub>2) )"


fun link_same_rank :: "'a::linorder trees \<Rightarrow> 'a obtree \<Rightarrow> 'a trees" where
  "link_same_rank [] t= [t]"
| "link_same_rank (t\<^sub>2#ts) t\<^sub>1 =
  (if rank t\<^sub>1 < rank t\<^sub>2 then t\<^sub>1#t\<^sub>2#ts else
            (if  rank t\<^sub>2 < rank t\<^sub>1 then t\<^sub>2#(link_same_rank ts t\<^sub>1) else
                                    link_same_rank ts (link t\<^sub>1 t\<^sub>2)))"


fun merge_same_ranks :: "'a::linorder trees \<Rightarrow> 'a obtree list" where
  "merge_same_ranks ts = foldl link_same_rank [] ts "


end


subsection \<open>\<open>empty heap \<close>\<close>
fun is_empty_obheap:: "'a obheap \<Rightarrow> bool" where
  "is_empty_obheap heap  \<longleftrightarrow> (heap=Empty )"

lemma no_empty_obheap_eq:"\<not> is_empty_obheap (OBHeaps m (mintree) xs ) "
  by auto


subsection \<open>\<open>make heap \<close>\<close>
definition make_heap :: "'a::linorder \<Rightarrow> 'a obheap" where
  "make_heap x = OBHeaps 1 (Node 0 x []) []"
     

subsection \<open>\<open>merge\<close>\<close>
fun merge :: "'a::linorder obheap \<Rightarrow> 'a obheap \<Rightarrow> 'a obheap" where
  "merge h Empty = h"
| "merge Empty h = h"
| "merge (OBHeaps size1 min1 t1) (OBHeaps size2 min2 t2) =
    (if root min1 < root min2 then OBHeaps (size1 + size2) min1 (min2 # t2 @ t1)
     else OBHeaps (size1 + size2) min2 (min1 # t1 @ t2))"


subsection \<open>\<open>insert\<close>\<close>
fun insert :: " 'a::linorder \<Rightarrow> 'a obheap\<Rightarrow> 'a obheap" where
  "insert x h = merge h (make_heap x)"



value "merge_same_ranks [Node 0 (1::nat) [], Node 0 2 [], Node 0 3 []]"


subsection \<open>\<open>get_min\<close>\<close>
fun get_min :: "'a::linorder obheap \<Rightarrow> 'a " where
  "get_min fh = root (min_tree fh)"


subsection \<open>\<open>del_min\<close>\<close>
fun get_min_tree :: "'a::linorder trees \<Rightarrow> ('a obtree \<times> 'a trees)" where
  "get_min_tree [t] = (t,[])"
| "get_min_tree (t#ts) = (let (t',ts') = get_min_tree ts
                     in if root t \<le> root t' then (t,ts) else (t',t#ts'))"

fun del_min :: "'a::linorder obheap \<Rightarrow> 'a obheap" where
  "del_min Empty = Empty"
| "del_min (OBHeaps _ (Node _ _ []) []) = Empty"
| "del_min (OBHeaps m (Node _ _ []) ts) = (let (new_min, ts') =
             (get_min_tree (merge_same_ranks ts)) in OBHeaps (m - 1) new_min ts')"
| "del_min (OBHeaps m mintree ts) = (let (new_min, ts') = 
             get_min_tree (merge_same_ranks (children mintree @ ts)) in OBHeaps (m - 1) new_min ts')"



fun insert_list::"'a::linorder list \<Rightarrow> 'a obheap" where
  "insert_list [] = Empty"|
  "insert_list (t#ts) = insert t (insert_list ts)"

value "get_min_tree (merge_same_ranks (roots(insert_list [1::nat,5,6,9,8,4])))"

value "insert_list [1::nat,5,6,9,8,4,12,33,22,15,85,98,45,44]"
value "merge_same_ranks (roots(insert_list [1::nat,5,6,9,8,4]))"
value "del_min (insert_list [1::nat,5,6,9,8,4,12,33,22,15,85,98,45,7,2,10,23,55,66,88,45])"

end