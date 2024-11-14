theory OBHeaps_binomial_verification
  imports Complex_Main
          OBHeaps_modeling
          OBHeaps_verification
begin

subsection \<open>Binomial Heap invariant\<close>
fun invar_btree :: "'a::linorder obtree \<Rightarrow> bool" where
"invar_btree (Node r x ts) \<longleftrightarrow>
   (\<forall>t\<in>set ts. invar_btree t) \<and> map rank ts = rev [0..<r]"

definition "binvar_tree t \<longleftrightarrow> invar_btree t \<and> invar_otree t"

definition "bhinvar ts \<longleftrightarrow> (\<forall>t\<in>set ts. binvar_tree t) \<and> (sorted_wrt (<) (map rank ts))"

lemma binvar_tree0: "binvar_tree (Node 0 x [])"
  unfolding binvar_tree_def by auto


lemma binvar_tree_Cons:
  "bhinvar (t#ts)
  \<longleftrightarrow> binvar_tree t \<and> bhinvar ts \<and> (\<forall>t'\<in>set ts. rank t < rank t')"
  by (auto simp: bhinvar_def)

lemma invat_btrees_add:
  assumes "(\<forall>t\<in>set ts. binvar_tree t)"
  assumes "binvar_tree t\<^sub>1"
  shows "(\<forall>t\<in>set (t\<^sub>1#ts). binvar_tree t)"
  using assms
  by auto


lemma bhinvar_empty: "bhinvar []"
  by (simp add: bhinvar_def)

subsection \<open>link\<close>
lemma binvar_tree_link:
  assumes "binvar_tree t\<^sub>1"
  assumes "binvar_tree t\<^sub>2"
  assumes "rank t\<^sub>1 = rank t\<^sub>2"
  shows "binvar_tree (link t\<^sub>1 t\<^sub>2)"
using assms unfolding binvar_tree_def
by (cases "(t\<^sub>1, t\<^sub>2)" rule: link.cases) auto



lemma rank_link: "rank (link t\<^sub>1 t\<^sub>2) = rank t\<^sub>1 + 1"
  by (cases "(t\<^sub>1, t\<^sub>2)" rule: link.cases) simp

subsection \<open>link_same_rank\<close>
lemma link_same_rank_bound:
  assumes "t' \<in> set (link_same_rank ts t)"
  assumes "\<forall>t'\<in>set ts. rank t\<^sub>0 < rank t'"
  assumes "rank t\<^sub>0 < rank t"
  shows "rank t\<^sub>0 < rank t'"
  using assms
  by (induction ts t rule: link_same_rank.induct) (auto split: if_splits simp:rank_link) 


lemma sort_add:
  assumes "\<forall>t\<in>set(map rank ts). rank t\<^sub>2 < t "
  assumes "rank t\<^sub>2 < rank t\<^sub>1"
  assumes "sorted_wrt (<) (map rank (link_same_rank ts t\<^sub>1))"
  shows "\<forall>t\<in>set (map rank (link_same_rank ts t\<^sub>1)). rank t\<^sub>2 < t"
  using assms 
proof (induction ts t\<^sub>1 rule: link_same_rank.induct)
  case (1 t)
  then show ?case  by simp
next
  case (2 t\<^sub>1 t\<^sub>2 ts)
  then show ?case by (auto simp:rank_link)
qed

lemma bhinvar_link_same_rank_tree:
  assumes "binvar_tree t"
  assumes "bhinvar ts"
  shows "bhinvar (link_same_rank ts t)"
using assms 
proof (induction ts t rule: link_same_rank.induct)
  case (1 t)
  have 01:"(\<forall>t\<in>set [t]. binvar_tree t)" using bhinvar_def[of "[t]"]  link_same_rank.simps(1)[of t] 
    by (simp add: "1.prems"(1))
  then show ?case using 1 bhinvar_def[of "[t]"]  link_same_rank.simps(1)[of t] 
    by simp
next
  case (2 t\<^sub>2 ts t\<^sub>1)
 consider (LT) "rank t\<^sub>1 < rank t\<^sub>2"
         | (GT) "rank t\<^sub>1 > rank t\<^sub>2"
         | (EQ) "rank t\<^sub>1 = rank t\<^sub>2"
    using antisym_conv3 by blast
  then show ?case proof cases
    case LT
    then show ?thesis 
    proof -
      obtain tt :: "'a obtree \<Rightarrow> 'a trees \<Rightarrow> 'a obtree" and tta :: "'a obtree \<Rightarrow> 'a trees \<Rightarrow> 'a obtree" where
        f1: "\<forall>t ts. (binvar_tree t \<and> (\<forall>ta. ta \<notin> set ts \<or> rank t < rank ta) \<and> bhinvar ts \<or> \<not> bhinvar (t # ts)) \<and> (bhinvar (t # ts) \<or> \<not> binvar_tree t \<or> tt t ts \<in> set ts \<and> \<not> rank t < rank (tt t ts) \<or> \<not> bhinvar ts)"
        by (metis (no_types) binvar_tree_Cons)
      have "t\<^sub>2 = tt t\<^sub>1 (t\<^sub>2 # ts) \<longrightarrow> rank t\<^sub>1 < rank (tt t\<^sub>1 (t\<^sub>2 # ts)) \<or> rank t\<^sub>2 < rank (tt t\<^sub>1 (t\<^sub>2 # ts))"
        by (simp add: LT)
      then have "rank t\<^sub>2 < rank (tt t\<^sub>1 (t\<^sub>2 # ts)) \<or> rank t\<^sub>1 < rank (tt t\<^sub>1 (t\<^sub>2 # ts)) \<or> bhinvar (t\<^sub>1 # t\<^sub>2 # ts)"
        using f1 by (metis (no_types) "2.prems"(1) "2.prems"(2) set_ConsD)
      then have "rank t\<^sub>1 < rank (tt t\<^sub>1 (t\<^sub>2 # ts)) \<or> bhinvar (t\<^sub>1 # t\<^sub>2 # ts)"
        using LT by auto
      then show ?thesis
        using f1 by (metis (no_types) "2.prems"(1) "2.prems"(2) LT link_same_rank.simps(2))
    qed
   next
    case GT   
      have 02:" binvar_tree t\<^sub>2 \<Longrightarrow> bhinvar ts \<Longrightarrow> bhinvar (link_same_rank ts t\<^sub>1)" using 2 GT
        by simp
      have 03:"bhinvar (link_same_rank ts t\<^sub>1)"
        using "02" "2.prems"(1) "2.prems"(2) binvar_tree_Cons by auto 
      have 04:"(\<forall>t\<in>set ((link_same_rank ts t\<^sub>1)). binvar_tree t)"  using 03 bhinvar_def by auto
      have 05:"(\<forall>t\<in>set (t\<^sub>2#(link_same_rank ts t\<^sub>1)). binvar_tree t)" using 04 invat_btrees_add 
        using "2.prems"(2) binvar_tree_Cons by blast
      have 06:"sorted_wrt (<) (map rank (link_same_rank ts t\<^sub>1))" using 03 bhinvar_def by auto
      have ss:"\<forall>t\<in>set(map rank ts). rank t\<^sub>2 < t" using "2.prems" 
        by (simp add: bhinvar_def)
      have 07:"\<forall>t\<in>set(map rank (link_same_rank ts t\<^sub>1)). rank t\<^sub>2 < t " using 03 GT "2.prems"(2) ss sort_add
        using "06" by blast 
      have 08:"sorted_wrt (<) (map rank (t\<^sub>2#(link_same_rank ts t\<^sub>1)))" using GT 06  07 
        by simp
      then show ?thesis using 05 08 bhinvar_def GT 
        using "2.prems"(1) by fastforce
  next
    case EQ
    then show ?thesis
      by (metis "2.IH"(2) "2.prems"(1) "2.prems"(2) link_same_rank.simps(2) binvar_tree_Cons binvar_tree_link nat_neq_iff) 
  qed
qed


subsection \<open>merge_same_ranks\<close>
lemma bhinvar_foldl:
  assumes "bhinvar t"
  assumes "(\<forall>t\<in>set ts. binvar_tree t) "
  shows "bhinvar (foldl link_same_rank t ts)"
  using assms
proof (induction ts arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons t' ts')
  have "bhinvar (foldl link_same_rank (link_same_rank t t') ts')" 
  proof -
    from Cons.prems(2) have "\<forall>t''\<in>set ts'. binvar_tree t''" 
      by simp
    from Cons.IH[OF Cons.prems(1) this] have IH: "bhinvar (foldl link_same_rank (link_same_rank t t') ts')"
      by (simp add: Cons.IH Cons.prems(1) Cons.prems(2) bhinvar_link_same_rank_tree)
    show "bhinvar (foldl link_same_rank (link_same_rank t t') ts')"
      using IH by simp
  qed
  moreover have "bhinvar (link_same_rank t t')"
  proof -
    have "binvar_tree t'" using Cons.prems(2) by simp
    then show "bhinvar (link_same_rank t t')" 
      using Cons.prems(1) bhinvar_link_same_rank_tree 
      by auto 
  qed
  ultimately show ?case 
    by simp
qed

lemma bhinvar_merge_same_ranks:
  assumes "(\<forall>t\<in>set ts. binvar_tree t) "
  shows "bhinvar (merge_same_ranks ts)"
  using assms
  by (simp add: bhinvar_empty bhinvar_foldl)


lemma binvar_trees_linears_foldl:
 assumes "bhinvar xs"
  assumes "invar_trees_linear ts"
  shows "bhinvar (foldl link_same_rank xs ts)"
  using assms
proof (induct ts arbitrary: xs )
  case Nil
  then show ?case  
    by (simp add: bhinvar_empty)
next
  case (Cons a xs)
  then show ?case apply auto
    by (metis bhinvar_link_same_rank_tree binvar_tree0 obtree.exhaust_sel)
qed

lemma invar_trees_linear_foldl:
  assumes "invar_trees_linear ts"
  shows "bhinvar (foldl link_same_rank [] ts)"
  using assms
proof (induct ts )
  case Nil
  then show ?case  
    by (simp add: bhinvar_empty)
next
  case (Cons a xs)
  then show ?case apply auto 
    by (metis bhinvar_empty bhinvar_link_same_rank_tree binvar_tree0 binvar_trees_linears_foldl
          link_same_rank.simps(1) obtree.exhaust_sel)

qed

lemma bhinvar_merge_same_rank:
  assumes "invar_trees_linear ts"
  shows "bhinvar (merge_same_ranks ts)"
  using assms
  by (simp add: invar_trees_linear_foldl)


subsection \<open>get_min_tree\<close>

lemma binvar_get_min_tree:
  assumes "get_min_tree ts = (t',ts')"
  assumes "ts\<noteq>[]"
  assumes "bhinvar ts"
  shows "binvar_tree t'" and "bhinvar ts'"
proof -
  have "binvar_tree t' \<and> bhinvar ts'"
    using assms
    proof (induction ts arbitrary: t' ts' rule: get_min_tree.induct)
      case (1 t)
      then show ?case 
        by (simp add: binvar_tree_Cons)
    next
      case (2 t v va)
      then show ?case 
        apply (clarsimp split: prod.splits if_splits) 
        using binvar_tree_Cons apply blast 
        by (metis binvar_tree_Cons insert_iff list.distinct(1) set_get_min_rest)
    next
      case 3
      then show ?case 
        by blast
    qed
  thus "binvar_tree t'" and "bhinvar ts'" by auto
qed



subsection \<open>del_min\<close>

theorem binvar_mintree_del_min:
  assumes "invar_linear fh"
  assumes "\<not>is_empty_obheap (del_min fh)"
  shows " binvar_tree(min_tree(del_min fh))"
  using assms
  proof (induction fh rule:del_min.induct)
    case 1
    then show ?case by auto
  next
    case (2 uu uv uw)
    then show ?case  by simp
  next
    case (3 m ux uy v va)
    then show ?case  apply (simp split:prod.splits) 
      by (metis (no_types, lifting) binvar_get_min_tree(1) foldl_Cons invar_trees_linear.simps(2) 
          invar_trees_linear_foldl link_same_rank.simps(1) noempty_foldl not_Cons_self2)
  next
    case ("4_1" m v va vc vd ts)
    then show ?case by auto 
  next
    case ("4_2" m vb vc ve vf v va)
    then show ?case  by simp
  qed



theorem binvar_roots_del_min:
  assumes "invar_linear fh"
  assumes "\<not>is_empty_obheap (del_min fh)"
  shows " bhinvar(roots(del_min fh))"
  using assms
  proof (induction fh rule:del_min.induct)
    case 1
    then show ?case by auto
  next
    case (2 uu uv uw)
    then show ?case by simp
  next
    case (3 m ux uy v va)
    then show ?case  apply (simp split:prod.splits) 
      by (metis bhinvar_empty bhinvar_link_same_rank_tree binvar_get_min_tree(2)
              binvar_tree0 binvar_trees_linears_foldl link_same_rank.simps(1) 
              noempty_foldl not_Cons_self2 obtree.collapse)
  next
    case ("4_1" m v va vc vd ts)
    then show ?case  by auto 
  next
    case ("4_2" m vb vc ve vf v va)
    then show ?case  by simp
  qed

text \<open>The size of a binomial tree is determined by its rank\<close>
lemma size_mset_btree:
  assumes "invar_btree t"
  shows "size (mset_tree t) = 2^rank t"
  using assms
proof (induction t)
  case (Node r v ts)
  hence IH: "size (mset_tree t) = 2^rank t" if "t \<in> set ts" for t
    using that by auto

  from Node have COMPL: "map rank ts = rev [0..<r]" by auto

  have "size (mset_heap ts) = (\<Sum>t\<leftarrow>ts. size (mset_tree t))"
    by (induction ts) auto
  also have "\<dots> = (\<Sum>t\<leftarrow>ts. 2^rank t)" using IH
    by (auto cong: map_cong)
  also have "\<dots> = (\<Sum>r\<leftarrow>map rank ts. 2^r)"
    by (induction ts) auto
  also have "\<dots> = (\<Sum>i\<in>{0..<r}. 2^i)"
    unfolding COMPL
    by (auto simp: rev_map[symmetric] interv_sum_list_conv_sum_set_nat)
  also have "\<dots> = 2^r - 1"
    by (induction r) auto
  finally show ?case
    by (simp)
qed

lemma size_mset_tree:
  assumes "binvar_tree t"
  shows "size (mset_tree t) = 2^rank t"
using assms unfolding binvar_tree_def
by (simp add: size_mset_btree)

lemma size_mset_heap:
  assumes "bhinvar ts"
  shows "length ts \<le> log 2 (size (mset_heap ts) + 1)"
proof -
  from \<open>bhinvar ts\<close> have
    ASC: "sorted_wrt (<) (map rank ts)" and
    TINV: "\<forall>t\<in>set ts. binvar_tree t" 
    using bhinvar_def by auto

  have "(2::nat)^length ts = (\<Sum>i\<in>{0..<length ts}. 2^i) + 1"
    by (simp add: sum_power2)
  also have "\<dots> \<le> (\<Sum>t\<leftarrow>ts. 2^rank t) + 1"
    using sorted_wrt_less_sum_mono_lowerbound[OF _ ASC, of "(^) (2::nat)"]
    using power_increasing[where a="2::nat"]
    by (auto simp: o_def)
  also have "\<dots> = (\<Sum>t\<leftarrow>ts. size (mset_tree t)) + 1" using TINV
    by (auto cong: map_cong simp: size_mset_tree)
  also have "\<dots> = size (mset_heap ts) + 1"
    unfolding mset_heap_def by (induction ts) auto
  finally have "2^length ts \<le> size (mset_heap ts) + 1" .
  then show ?thesis using le_log2_of_power by blast
qed



end