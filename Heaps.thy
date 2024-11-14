section \<open>Heaps\<close>

theory Heaps
imports
  OBHeaps_modeling_pro
  OBHeaps_verification_pro
  Priority_Queue_Specs
begin

  
locale Heap =
fixes  empty ::"'h"
and is_empty ::"'h \<Rightarrow> bool"
and   insert :: "'a::linorder \<Rightarrow>'h\<Rightarrow> 'h"
and  get_min :: "'h \<Rightarrow> 'a"
and  del_min :: "'h \<Rightarrow> 'h"
and    invar :: "'h \<Rightarrow> bool"
and      mset::"'h \<Rightarrow> 'a multiset"
assumes invar_empty:"invar empty"
and        is_empty:"invar h \<Longrightarrow> is_empty h = (mset h = {#})"
and      mset_empty:"mset empty = {#}"
and     mset_insert:"invar h \<Longrightarrow> mset (insert x h) = {#x#} + mset h"
and    invar_insert:"invar h \<Longrightarrow> invar (insert x h)"
and    mset_get_min:"invar h \<Longrightarrow> mset h\<noteq> {#}\<Longrightarrow>get_min h = Min_mset (mset h)" 
and    mset_del_min:"\<lbrakk> invar h;  \<not>is_empty h \<rbrakk> \<Longrightarrow> mset (del_min h) = mset h - {#get_min h#}"
and   invar_del_min:"\<lbrakk> invar h;  \<not>is_empty h \<rbrakk> \<Longrightarrow> invar(del_min h)"

locale Heap_Merge = Heap +
  fixes merge :: "'h \<Rightarrow> 'h \<Rightarrow> 'h"
assumes mset_merge: "\<lbrakk> invar h1; invar h2 \<rbrakk> \<Longrightarrow> mset (merge h1 h2) = mset h1 + mset h2"
and invar_merge: "\<lbrakk> invar h1; invar h2 \<rbrakk> \<Longrightarrow> invar (merge h1 h2)"



interpretation OBHeaps: Heap_Merge 
where empty = Empty
and is_empty = is_empty_obheap
and merge = merge
and insert = insert
and get_min = get_min
and del_min = delete_min 
and invar = invar 
and mset = mset_obheap 
                  

proof(standard, goal_cases)
  case 1 then show ?case using invar_empty by blast 
next
  case (2 h) then show ?case using mset_obheap_empty_iff by blast 
next
  case 3 then show ?case using mset_obheap_empty by blast  
next
  case (4 h x) then show ?case using mset_insert by blast  
next
  case (5 h x) then show ?case using invar_insert by blast
next
  case (6 h) then show ?case  using get_min_value by blast 
next
  case (7 h) then show ?case  using mset_del_min  by blast 
next                                    
  case (8 h) then show ?case using invar_del_min by blast
next
  case (9 h1 h2) then show ?case using mset_merge by blast
next
  case (10 h1 h2) then show ?case using invar_merge by blast
qed  


end
