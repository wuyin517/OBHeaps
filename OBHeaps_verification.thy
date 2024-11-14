theory OBHeaps_verification_pro
  imports
    Main
    OBHeaps_modeling
    multset
begin

subsection \<open> invariant of OBHeaps \<close>
fun invar_otree :: "'a::linorder obtree \<Rightarrow> bool" where
"invar_otree (Node _ x  ts) \<longleftrightarrow> (\<forall>t\<in>set ts. invar_otree t \<and> x \<le> root t)"

fun invar_otrees::"'a::linorder trees\<Rightarrow> bool " where
  "invar_otrees ts \<longleftrightarrow> (\<forall>t\<in>set ts. invar_otree t) "

fun invar_order::"'a::linorder obheap \<Rightarrow> bool " where
"invar_order Empty = True"|
"invar_order (OBHeaps n m ts) \<longleftrightarrow>(invar_otree m) \<and> (invar_otrees ts) "

fun invar_min::"'a::linorder obheap \<Rightarrow> bool " where
"invar_min Empty = True"|
"invar_min (OBHeaps n m ts) \<longleftrightarrow> (\<forall>t\<in>set ts. root m \<le>root t) "

fun invar ::"'a::linorder obheap \<Rightarrow> bool " where
"invar heap \<longleftrightarrow> invar_min heap \<and> invar_order heap"




subsection \<open> invar of OBHeaps \<close>
lemma invar_order_tree:"\<not> is_empty_obheap fh \<Longrightarrow> invar_order fh \<Longrightarrow>invar_otree(min_tree fh)"
  using invar_order.elims(2) by fastforce

lemma invar_order_trees :"\<not> is_empty_obheap fh \<Longrightarrow> invar_order fh  \<Longrightarrow>invar_otrees (roots fh )"
  using invar_order.elims(2) by force

lemma invar_mintree_roots :"\<not> is_empty_obheap fh \<Longrightarrow> invar fh  \<Longrightarrow> invar_otree(min_tree fh) \<and> invar_otrees (roots fh )"
  using invar_order_tree invar_order_trees by auto

lemma invar_empty:"invar Empty" 
  by simp

lemma root_invar_min:" \<not> is_empty_obheap fh  \<Longrightarrow> 
                         (\<forall>t\<in>set (roots fh). root (min_tree fh) \<le>root t) 
                            \<Longrightarrow> invar_min fh"
  using invar_min.elims(3) by fastforce

lemma roots_mintree_invar_order:"\<not> is_empty_obheap fh \<Longrightarrow>
                      invar_otrees (roots fh) \<Longrightarrow> 
                        invar_otree (min_tree fh) \<Longrightarrow> invar_order fh"
  using invar_order.elims(3) by fastforce

lemma roots_mintree_invar :"\<not> is_empty_obheap fh \<Longrightarrow>
                            invar_otrees (roots fh) \<Longrightarrow> 
                              invar_otree (min_tree fh) \<Longrightarrow>
                                (\<forall>t\<in>set (roots fh). root (min_tree fh) \<le>root t)\<Longrightarrow>invar fh "
  by (simp add: root_invar_min roots_mintree_invar_order)

lemma invar_otree_children:
  "invar_otree (Node r a ts) \<Longrightarrow> (\<forall>t\<in>set ts. invar_otree t)" 
  by simp

lemma invar_otrees_empty: "invar_otrees []"
  by simp 


subsection \<open>\<open>make heap \<close>\<close>

lemma invar_make_heap:
  "invar (make_heap x)" 
  by (simp add:  make_heap_def) 

lemma mset_make_heap:
"mset_obheap (make_heap x) = {#x#}" 
  by (simp add: make_heap_def)

subsection \<open>\<open>merge\<close>\<close>

lemma app_mest_tress:"mset_heap(ts1 @ ts2) = mset_heap ts1 + mset_heap ts2"
  apply(induct ts1) 
  by auto

lemma invar_order_merge:
  assumes "invar ts\<^sub>1"
  assumes "invar ts\<^sub>2"
  shows "invar_order ((merge ts\<^sub>1 ts\<^sub>2))"
  using assms
proof (induction ts\<^sub>1 ts\<^sub>2 rule: merge.induct)
  case (1 h)
  then show ?case by simp
next
  case (2 v va vb)
  then show ?case by simp
next
  case (3 size1 min1 t1 size2 min2 t2)
  then show ?case 
    by auto
 qed

lemma inv_min_merge:
  assumes "invar ts\<^sub>1"
  assumes "invar ts\<^sub>2"
  shows "invar_min (merge ts\<^sub>1 ts\<^sub>2)"
  using assms
proof (induction ts\<^sub>1 ts\<^sub>2 rule: merge.induct)
  case (1 h)
  then show ?case by simp
next
  case (2 v va vb)
  then show ?case by simp
next
  case (3 size1 min1 t1 size2 min2 t2)
  then show ?case 
  proof (cases "root min1 < root min2")
    case True
    then show ?thesis
      using 3 
      by auto
  next
    case False
    then show ?thesis  using 3  by auto
  qed
qed

    
theorem invar_merge[simp]:
  assumes "invar ts\<^sub>1"
  assumes "invar ts\<^sub>2"
  shows "invar (merge ts\<^sub>1 ts\<^sub>2)"
  using assms
  by (simp add: inv_min_merge invar_order_merge)


theorem mset_merge[simp]:
  "mset_obheap (merge ts\<^sub>1 ts\<^sub>2) = mset_obheap ts\<^sub>1 + mset_obheap ts\<^sub>2"
  apply (induction ts\<^sub>1 ts\<^sub>2 rule: merge.induct)
  by (auto simp:app_mest_tress) 



subsection \<open>\<open>insert\<close>\<close>

lemma obheap0: "invar_otree (Node 0 x [])"
   by auto

theorem invar_insert[simp]: "invar fh \<Longrightarrow> invar (insert  x fh)" 
  using invar_make_heap invar_merge by auto

theorem mset_insert[simp]: "mset_obheap (insert x fh) = {#x#} + mset_obheap fh" 
  using mset_make_heap mset_merge by auto

subsection \<open>\<open>get_min\<close>\<close>
lemma obheap_root_min:
  assumes "invar_otree t"
  assumes "x \<in># mset_tree t"
  shows "root t \<le> x"
using assms
by (induction t arbitrary: x rule: mset_tree.induct) (fastforce simp: mset_heap_def)

lemma get_min_mset:
  assumes "\<not> is_empty_obheap fh"
  assumes "invar fh"
  assumes "x \<in># mset_obheap fh"
  shows "get_min fh \<le> x"
  using assms
  apply auto defer 
  apply (simp add: invar_order_tree obheap_root_min) 
proof -
  fix b::'a and fs::"'a obtree" 
  have 01 :"invar_otree (min_tree fh)\<and>invar_otrees (roots fh)"
    by (metis assms(1) assms(2) invar.elims(2) invar_order.simps(2) is_empty_obheap.simps obheap.collapse)
  have 02: "a \<in># mset_tree (min_tree fh) \<Longrightarrow> root (min_tree fh) \<le> a" 
    by (simp add: "01" obheap_root_min)
  have 03:"\<forall>t\<in>set (roots fh). root(min_tree fh)\<le>root t" 
    using assms(1) assms(2) invar_min.elims(2) by force
  have 04:"b\<in># mset_tree fs \<Longrightarrow> invar_otree fs \<Longrightarrow> root fs \<le> b" 
    by (simp add: obheap_root_min)
  then show "invar_order fh \<Longrightarrow> x \<in># mset_heap (roots fh) \<Longrightarrow> root (min_tree fh) \<le> x" using 01 02 03 04
    by (metis obheap_root_min invar_otree.simps invar_otrees.simps mset_tree_simp_alt obtree.sel(2) union_iff) 
qed
 

lemma get_min_member:
  "\<not> is_empty_obheap fh \<Longrightarrow> get_min fh \<in># mset_obheap fh" 
  by simp

theorem get_min_value:
  assumes "mset_obheap fh \<noteq> {#}"
  assumes "invar fh"
  shows "get_min fh = Min_mset (mset_obheap fh)"
  using assms 
  apply(induct fh rule:mset_obheap.induct) 
  apply simp  
  by (metis Min_eqI finite_set_mset get_min_member get_min_mset mset_obheap_empty_iff)

subsection \<open>\<open>del_min\<close>\<close>




subsubsection \<open>\<open>link\<close>\<close>
lemma ftree_link:
  assumes "invar_otree t\<^sub>1"
  assumes "invar_otree t\<^sub>2"
  shows "invar_otree (link t\<^sub>1 t\<^sub>2)"
using assms 
  by (cases "(t\<^sub>1, t\<^sub>2)" rule: link.cases) auto


lemma mset_link: "mset_tree (link t\<^sub>1 t\<^sub>2) = mset_tree t\<^sub>1 + mset_tree t\<^sub>2"
  by (cases "(t\<^sub>1, t\<^sub>2)" rule: link.cases) simp

subsubsection \<open>\<open>link_same_rank\<close>\<close>
lemma invar_otrees_instrees:
  assumes "invar_otree t"
  assumes "invar_otrees ts"
  shows "invar_otrees (link_same_rank ts t)"
using assms
  apply (induction  ts t rule: link_same_rank.induct) 
  apply simp 
  using ftree_link by auto


lemma mset_heap_link_same_rank:
  "mset_heap (link_same_rank ts t) = mset_tree t + mset_heap ts"
  by (induction ts t rule: link_same_rank.induct) (auto simp:mset_link)


subsubsection \<open>\<open>merge_same_rank\<close>\<close>

lemma invar_otrees_foldl:
  assumes "invar_otrees t"
  assumes "invar_otrees ts "
  shows "invar_otrees (foldl link_same_rank t ts)"
  using assms
proof (induction ts arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons t' ts') 
  have "invar_otrees (foldl link_same_rank (link_same_rank t t') ts')" 
  proof -
    from Cons.prems(2) have 01: " invar_otrees ts'" 
      by simp
    show IH: "invar_otrees (foldl link_same_rank (link_same_rank t t') ts')" 
      by (meson "01" Cons.IH Cons.prems(1) Cons.prems(2) invar_otrees_instrees invar_otrees.elims(2) list.set_intros(1))
  qed
  moreover have "invar_otrees (link_same_rank t t')"
  proof -
    have "invar_otree t'" using Cons.prems(2) by simp
    then show "invar_otrees (link_same_rank t t')" 
      using Cons.prems(1) invar_otrees_instrees by blast
  qed
  ultimately show ?case 
    by simp
qed

lemma app_mset_foldl: "mset_heap (foldl link_same_rank ts xs) = mset_heap ts + mset_heap xs"
proof (induct xs arbitrary: ts)
  case Nil
  then show ?case by simp
next
  case (Cons a ts)
  then show ?case apply auto
    by (simp add: mset_heap_link_same_rank)
qed

lemma mset_heap_merge_same_ranks: 
          "mset_heap ts = mset_heap (merge_same_ranks ts)"                              
             by (simp add: app_mset_foldl)

lemma merge_invar_otrees:
  assumes "invar_otrees ts "
  shows "invar_otrees (merge_same_ranks ts)"
  using assms
  apply auto
  using invar_otrees.simps invar_otrees_empty invar_otrees_foldl by blast

lemma mset_merge_same_ranks:
  "mset_heap (merge_same_ranks ts) =  mset_heap ts"
  by (induction ts rule: merge_same_ranks.induct) (auto simp:app_mset_foldl)

subsubsection \<open>\<open>get_min_tree\<close>\<close>
lemma get_min_tree_root':
  assumes "ts\<noteq>[]"
  assumes "get_min_tree ts = (t',ts')"
  shows " (\<forall>t\<in>set ts. root t' \<le> root t)"
using assms
  apply (induction ts arbitrary: t' ts' rule: get_min_tree.induct)
  apply (auto  split: prod.splits) 
  apply (metis Pair_inject linorder_le_cases)
  by (metis order.trans prod.inject)+


lemma get_min_tree_root:
  assumes "ts\<noteq>[]"
  assumes "get_min_tree ts = (t',ts')"
  shows " (\<forall>t\<in>set ts'. root t' \<le> root t)"
  using assms
  apply (induction ts arbitrary: t' ts' rule: get_min_tree.induct)
    apply (auto  split: prod.splits) 
  by (metis (no_types, lifting) dual_order.trans get_min_tree_root' linorder_le_cases list.distinct(1) prod.inject set_ConsD)


lemma mset_get_min_tree':
  assumes "get_min_tree ts = (t',ts')"
  assumes "ts\<noteq>[]"
  shows "mset ts = {#t'#} + mset ts'"
using assms
by (induction ts arbitrary: t' ts' rule: get_min_tree.induct) (auto split: prod.splits if_splits)

lemma mset_get_min_tree:
  assumes "get_min_tree ts = (t',ts')"
  assumes "ts\<noteq>[]"
  shows "mset_heap ts = mset_tree t' + mset_heap ts'"
using assms
  by (induction ts arbitrary: t' ts' rule: get_min_tree.induct) (auto split: prod.splits if_splits)


lemma set_get_min_rest:
  assumes "get_min_tree ts = (t', ts')"
  assumes "ts\<noteq>[]"
  shows "set ts = Set.insert t' (set ts')"
using mset_get_min_tree'[OF assms, THEN arg_cong[where f=set_mset]]
by auto

lemma invar_otree_get_min_rest:
  assumes "get_min_tree ts = (t',ts')"
  assumes "ts\<noteq>[]"
  assumes "invar_otrees ts"
  shows "invar_otree t'\<and>invar_otrees ts'"
proof -
  have "invar_otree t' \<and> invar_otrees ts'"
    using assms
    proof (induction ts arbitrary: t' ts' rule: get_min_tree.induct)
      case (1 t)
      then show ?case 
        by simp 
    next
      case (2 t v va)
      then show ?case 
        apply (clarsimp split: prod.splits if_splits) 
        by auto
    next
      case 3
      then show ?case 
        by blast
    qed
  thus "invar_otree t'\<and>invar_otrees ts'" by auto
qed


subsubsection \<open>\<open>del_min\<close>\<close>
lemma noempty_foldl:
  assumes "ts \<noteq> []  "
  shows "(foldl link_same_rank ts xs) \<noteq> []"
  using assms
 proof (induction xs arbitrary: ts)
   case Nil
   then show ?case 
     by simp
 next
   case (Cons t' ts')
   have 01: "(foldl link_same_rank (link_same_rank ts t') ts') \<noteq> []" 
     apply auto
     by (metis Cons.IH list.discI mset_heap_link_same_rank mset_heap_Cons' mset_heap_empty_iff)
   then show ?case  
     using "01" by auto
 qed



lemma invar_min_del_min:
  assumes "\<not> is_empty_obheap fh"
  assumes "invar_min fh"
  shows "invar_min (del_min fh)"
  using assms
apply (induct fh rule:del_min.induct)
      apply simp
     apply simp
    apply (simp split:prod.splits) 
  using get_min_tree_root noempty_foldl apply blast 
   apply (simp split:prod.splits)
   apply (meson get_min_tree_root list.discI noempty_foldl)
  apply (simp split:prod.splits)
  by (metis foldl_Cons get_min_tree_root list.distinct(1) noempty_foldl)



lemma invar_oreder_del_min:
  assumes "\<not> is_empty_obheap fh"
  assumes "invar_order fh"
  shows "invar_order (del_min fh)"
  using assms
  apply (induct fh rule:del_min.induct)
      apply simp
     apply simp 
    apply (simp split:prod.splits)  
  apply (metis invar_otree_get_min_rest invar_otrees.simps invar_otrees_foldl list.set(1) list.simps(15) noempty_foldl not_Cons_self2 singletonD)
  apply (simp split:prod.splits)  
  apply (metis invar_otree_get_min_rest invar_otrees.elims(1) invar_otrees_empty invar_otrees_foldl not_Cons_self2 noempty_foldl set_ConsD)
  apply (simp split:prod.splits) 
  by (metis (no_types, opaque_lifting) foldl_Cons invar_otree_get_min_rest invar_otrees.simps invar_otrees_empty invar_otrees_foldl invar_otrees_instrees link_same_rank.simps(1) list.simps(3) noempty_foldl)




theorem invar_del_min[simp]:
  assumes "\<not> is_empty_obheap fh"
  assumes "invar fh"
  shows "invar (del_min fh)"
  using assms 
  by (simp add: invar_min_del_min invar_oreder_del_min)



theorem mset_del_min[simp]:
  assumes "\<not>is_empty_obheap fh"
  assumes "invar fh"
  shows " mset_obheap (del_min fh) = mset_obheap fh - {# get_min fh #}"
  using assms
  apply (induction fh rule:del_min.induct)
  apply simp 
     apply auto[1] 
    apply (simp split:prod.splits) 
    apply (smt (verit, del_insts) add.commute add_right_cancel foldl_Nil get_min_tree.simps(1) 
          mset_get_min_tree not_Cons_self2 noempty_foldl app_mset_foldl)
   apply (simp split:prod.splits) 
   apply (smt (verit, ccfv_threshold) add.commute add.right_neutral mset_get_min_tree 
          mset_heap_Cons' mset_heap_Nil not_Cons_self2 noempty_foldl app_mset_foldl)
  apply (simp split:prod.splits) 
  by (smt (verit, ccfv_threshold) add_right_imp_eq app_mset_foldl empty_eq_union 
          mset_get_min_tree mset_tree_nonempty mset_heap_Cons mset_heap_Nil 
            mset_heap_link_same_rank union_commute union_lcomm)
(* by (smt (verit) empty_neutral(2) mset_get_min_tree mset_tree_nonempty mset_heap_Cons' mset_heap_Nil mset_heap_link_same_rank q union_assoc union_commute union_eq_empty) 
proof -
  fix vc :: 'a and ve :: "'a obtree" and vf :: "'a obtree list" and v :: "'a obtree" and va :: "'a obtree list"
  obtain tts :: "'a obtree list" and tt :: "'a obtree" where
    f1: "(\<exists>X0 E_x1. mset_tree ve + mset_heap vf + (mset_tree v + mset_heap va) \<noteq> mset_heap E_x1 + mset_tree X0 \<and> get_min_tree (foldl link_same_rank (link_same_rank (foldl link_same_rank [ve] vf) v) va) = (X0, E_x1)) \<longrightarrow> mset_tree ve + mset_heap vf + (mset_tree v + mset_heap va) \<noteq> mset_heap tts + mset_tree tt \<and> get_min_tree (foldl link_same_rank (link_same_rank (foldl link_same_rank [ve] vf) v) va) = (tt, tts)"
    by blast
  have f2: "\<forall>ts tsa. (mset_heap (foldl link_same_rank tsa ts)::'a multiset) = mset_heap (foldl link_same_rank ts tsa)"
    by (simp add: app_mset_foldl)
  have f3: "\<forall>t f ts. f (ts::'a trees) (t::'a obtree) = foldl f ts [t]"
    by simp
  have f4: "\<forall>ts t tsa. [] \<noteq> foldl link_same_rank (foldl link_same_rank [t::'a obtree] tsa) ts"
    by (metis (no_types) not_Cons_self2 noempty_foldl)
  have f5: "\<forall>t ts tsa. mset_heap (foldl link_same_rank tsa ((t::'a obtree) # ts)) = mset_heap (foldl link_same_rank ts (link_same_rank tsa t))"
    using f2 by simp
  have "\<forall>ts t. mset_heap (foldl link_same_rank [t::'a obtree] ts) = mset_heap (link_same_rank ts t)"
    using f2 by fastforce
  then have "\<forall>t ts. mset_heap ((t::'a obtree) # ts) = mset_heap (link_same_rank ts t)"
    by (simp add: app_mset_foldl)
  then show "\<forall>t ts. get_min_tree (foldl link_same_rank (link_same_rank (foldl link_same_rank [ve] vf) v) va) = (t, ts) \<longrightarrow> mset_heap ts + mset_tree t = mset_tree ve + mset_heap vf + (mset_tree v + mset_heap va)"
    using f5 f4 f3 f2 f1 by (smt (z3) add.commute foldl_Cons mset_get_min_tree mset_heap_Cons' app_mset_foldl)
qed *)


subsection \<open> insert_list \<close>
lemma invar_insert_list:"invar (insert_list xs)"
proof(induct xs rule:insert_list.induct)
  case 1
  then show ?case 
    by simp
next
  case (2 t ts)
  then show ?case 
    using invar_insert by auto
qed

lemma mset_insert_list:"mset_obheap (insert_list xs) = mset xs"
proof(induct xs rule:insert_list.induct)
  case 1
  then show ?case 
    by simp
next
  case (2 t ts)
  then show ?case  
    using mset_make_heap by auto
qed


subsection \<open> invariant_linear \<close>
fun invar_trees_linear::"'a::linorder trees \<Rightarrow> bool" where
"invar_trees_linear [] = True"|
"invar_trees_linear (x#xs)  \<longleftrightarrow> (rank x = 0) \<and> (children x = []) \<and> (invar_trees_linear xs) "


fun invar_linear::"'a::linorder obheap \<Rightarrow> bool" where
"invar_linear Empty = True"|
"invar_linear (OBHeaps n m ts)  \<longleftrightarrow> (rank m = 0) \<and> (children m = [])\<and>(length ts + 1 = n) \<and> (invar_trees_linear ts) "

subsection \<open> invar_linear of insert \<close>
lemma invar_linear_make_heap:
  " invar_linear (make_heap x)" 
  by (simp add:  make_heap_def  ) 

lemma app_invar_trees_linear:" invar_trees_linear t1 \<Longrightarrow> invar_trees_linear t2  \<Longrightarrow> invar_trees_linear (t1 @ t2)"
 apply(induct t1) 
  by auto

lemma invar_linear_merge:
  assumes "invar_linear ts\<^sub>1"
  assumes "invar_linear ts\<^sub>2"
  shows "invar_linear (merge ts\<^sub>1 ts\<^sub>2)"
  using assms
proof (induction ts\<^sub>1 ts\<^sub>2 rule: merge.induct)
  case (1 h)
  then show ?case
    by simp
next
  case (2 v va vb)
  then show ?case 
    by auto
next
  case (3 size1 min1 t1 size2 min2 t2)
  then show ?case apply auto
    using app_invar_trees_linear
    by auto
qed


lemma invar_linear_insert: "invar_linear fh \<Longrightarrow> invar_linear (insert  x fh)" 
  using invar_linear_make_heap invar_linear_merge by auto


lemma insert_list_invar_linear:"invar_linear (insert_list xs)" 
proof(induct xs rule:insert_list.induct)
  case 1
  then show ?case  by auto
next
  case (2 t ts)
  then show ?case 
    by (simp add: invar_linear_make_heap invar_linear_merge)
qed
  


end