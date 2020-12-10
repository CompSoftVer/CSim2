(*
 * Copyright 2017, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou.
 *)

theory Separata_Pointers
imports Main Separata_Advanced
begin

abbreviation (input)
pred_eq :: "'a \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> bool" (infixr "eq" 50) where
"a eq b \<equiv> \<lambda>s. a = b"  
  
text {* In the heap model, 'b are the addresses, 'c are the values, 'a 
are the heaps. *}  
  
locale pointsto_algebra = 
  fixes pointsto :: "'a \<Rightarrow> 'b \<Rightarrow> ('c::heap_sep_algebra) \<Rightarrow> bool" (infix "\<mapsto>" 40)
    
  assumes pointsto_inject: "\<lbrakk>(n \<mapsto> l) h1; (n \<mapsto> l) h2\<rbrakk> \<Longrightarrow> h1 = h2"  
begin

lemma lssl_l5: 
"Gamma \<and> h1 = h2 \<and> (n \<mapsto> l) h1 \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (n \<mapsto> l) h1 \<and> (n \<mapsto> l) h2 \<longrightarrow> Delta"
using local.pointsto_inject by blast

lemma lssl_l5_inv: 
"Gamma \<and> (n \<mapsto> l) h1 \<and> (n \<mapsto> l) h2 \<longrightarrow> Delta \<Longrightarrow> 
 Gamma \<and> h1 = h2 \<and> (n \<mapsto> l) h1 \<longrightarrow> Delta"
by auto
  
lemma lssl_l5_der: "(n \<mapsto> l) h1 \<Longrightarrow> (n \<mapsto> l) h2 \<Longrightarrow> h1 = h2"
by (simp add: local.pointsto_inject)  
  
text {* Operations about pointers. *}  
  
definition substate:: "'c \<Rightarrow> 'c \<Rightarrow> bool" (infix "\<sqsubseteq>" 40) where
"h1 \<sqsubseteq> h2 \<equiv> \<exists>h3. (h1,h3\<triangleright>h2)"  
  
definition state_as_fun:: "'c \<Rightarrow> 'a \<Rightarrow> 'b option" (infix "\<restriction>" 100) where
"h\<restriction>a \<equiv> 
  let P = (\<lambda>v h a. \<exists>h'. h' \<sqsubseteq> h \<and> (a \<mapsto> v) h') in
  if  \<exists>v. P v h a then 
    Some (SOME v. P v h a) 
  else None"

definition set_val:: "'c \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c" where
"set_val h a v \<equiv> SOME h'. (\<forall>a'. (a'\<noteq>a \<longrightarrow> h'\<restriction>a' = h\<restriction>a') \<and> (h'\<restriction>a = Some v))"  

definition all_elements:: "'a set" where
"all_elements \<equiv> {x. True}"

definition domain:: "'c \<Rightarrow> 'a set" where
"domain h \<equiv> {a. \<exists>v. h\<restriction>a = Some v}"  

definition all_domains:: "'c set \<Rightarrow> 'a set" where
"all_domains hs \<equiv> {a. \<forall>h \<in> hs. \<exists>v. h\<restriction>a = Some v}"  

definition heaps_of_domain:: "'a set \<Rightarrow> 'c set" where
"heaps_of_domain d \<equiv> {h. domain h = d}" 

definition full_domain_heaps:: "'c set" where
"full_domain_heaps \<equiv> {h. domain h = all_elements}"

definition disjoint_domain::"'c \<Rightarrow> 'a set" where
"disjoint_domain h \<equiv> all_elements - (domain h)"

definition vals:: "'c \<Rightarrow> 'b set" where
"vals h \<equiv> {v. \<exists>a. h\<restriction>a = Some v}"  
  
definition is_empty:: "'c \<Rightarrow> bool" where
"is_empty h \<equiv> domain h = {}"  

definition get_state:: "'a \<Rightarrow> 'b \<Rightarrow> 'c" where
"get_state a v \<equiv> THE h. (a \<mapsto> v) h"

lemma dom_not_empty: "(a \<in> domain h) = (\<exists>v. (h\<restriction>a = Some v \<and> is_empty h = False))"
using domain_def local.is_empty_def by auto

lemma dom_not_none: "(a \<in> domain h) \<Longrightarrow> (h\<restriction>a \<noteq> None)"
by (simp add: dom_not_empty)      
  
end                                            
  
locale reynolds_algebra = pointsto_algebra +    
  assumes pointsto_no_emp: "\<not>((n \<mapsto> l) 0)" 
  assumes pointsto_no_larger_than_one: "\<lbrakk>(n \<mapsto> l) h; (h1,h2\<triangleright>h)\<rbrakk> \<Longrightarrow> (h1 = 0) \<or> (h2 = 0)"  
  assumes pointsto_addr_disj: "\<lbrakk>(n1 \<mapsto> l1) h1; (n2 \<mapsto> l2) h2; (h1,h2\<triangleright>h)\<rbrakk> \<Longrightarrow> \<not> (n1 = n2)"  
  assumes pointsto_unique: "\<lbrakk>(n1 \<mapsto> l1) h; (n2 \<mapsto> l2) h\<rbrakk> \<Longrightarrow> n1 = n2 \<and> l1 = l2"
    
  assumes pointsto_extend: "\<exists>n h1 h2. (h1,h\<triangleright>h2) \<and> (n \<mapsto> l) h1"  
begin  
  
text {* The following are properties of definitions on pointers. *}  
  
lemma id_is_empty: "is_empty 0"
by (metis (no_types, lifting) Collect_empty_eq dom_not_none domain_def local.is_empty_def lspasl_iu_eq mem_Collect_eq pointsto_no_emp state_as_fun_def substate_def)
  
text {* The following are more inferences rules for pointers. *}  
  
lemma lssl_l1: "Gamma \<and> (n \<mapsto> l) 0 \<longrightarrow> Delta"
by (simp add: local.pointsto_no_emp)

lemma lssl_l2: 
"\<lbrakk>Gamma \<and> (0,h0\<triangleright>h0) \<and> (n \<mapsto> l) h0 \<and> h1 = 0 \<and> h2 = h0 \<longrightarrow> Delta;
  Gamma \<and> (h0,0\<triangleright>h0) \<and> (n \<mapsto> l) h0 \<and> h2 = 0 \<and> h1 = h0 \<longrightarrow> Delta\<rbrakk> \<Longrightarrow>
  Gamma \<and> (h1,h2\<triangleright>h0) \<and> (n \<mapsto> l) h0 \<longrightarrow> Delta"
by (metis heap_sep_algebra_class.lspasl_eq_der2 heap_sep_algebra_class.lspasl_eq_eq pointsto_no_larger_than_one)

lemma lssl_l2_inv:
"Gamma \<and> (h1,h2\<triangleright>h0) \<and> (n \<mapsto> l) h0 \<longrightarrow> Delta \<Longrightarrow>
(Gamma \<and> (0,h0\<triangleright>h0) \<and> (n \<mapsto> l) h0 \<and> h1 = 0 \<and> h0 = h2 \<longrightarrow> Delta) \<or> 
(Gamma \<and> (h0,0\<triangleright>h0) \<and> (n \<mapsto> l) h0 \<and> h2 = 0 \<and> h0 = h1 \<longrightarrow> Delta)"
by blast

lemma lssl_l2_der: 
"(h1,h2\<triangleright>h0) \<Longrightarrow> (n \<mapsto> l) h0 \<Longrightarrow> (h1 = 0 \<and> h0 = h2) \<or> (h2 = 0 \<and> h0 = h1)"
by (metis lssl_l2)  
  
lemma lssl_l3: "Gamma \<and> (h1,h2\<triangleright>h0) \<and> (n\<mapsto>l1) h1 \<and> (n\<mapsto>l2) h2 \<longrightarrow> Delta"
using local.pointsto_addr_disj by blast

lemma lssl_l3_der:
"(h1,h2\<triangleright>h0) \<Longrightarrow> (n\<mapsto>l1) h1 \<Longrightarrow> (n\<mapsto>l2) h2 \<Longrightarrow> False"
using local.pointsto_addr_disj by blast
  
lemma lssl_l4: 
"Gamma \<and> (n1\<mapsto>l1) h \<and> n1 = n2 \<and> l1 = l2 \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (n1\<mapsto>l1) h \<and> (n2\<mapsto>l2) h \<longrightarrow> Delta"
using local.pointsto_unique by blast  

lemma lssl_l4_inv: 
"Gamma \<and> (n1\<mapsto>l1) h \<and> (n2\<mapsto>l2) h \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (n1\<mapsto>l1) h \<and> n1 = n2 \<and> l1 = l2 \<longrightarrow> Delta"
by auto  

lemma lssl_l4_der:
"(n1\<mapsto>l1) h \<Longrightarrow> (n2\<mapsto>l2) h \<Longrightarrow> n1 = n2 \<and> l1 = l2"
by (simp add: local.pointsto_unique)     
  
lemma lssl_l6: 
"(\<exists>h1 h2 n. (Gamma \<and> (h1,h0\<triangleright>h2) \<and> (n\<mapsto>l) h1)) \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<longrightarrow> Delta"
using local.pointsto_extend by blast  

lemma lssl_l6_inv: 
"Gamma \<longrightarrow> Delta \<Longrightarrow>
 (\<exists>h1 h2 n. (Gamma \<and> (h1,h0\<triangleright>h2) \<and> (n\<mapsto>l) h1)) \<longrightarrow> Delta"
by simp  

lemma lssl_l6_der: "\<exists>h1 h2 n. (h1,h0\<triangleright>h2) \<and> (n\<mapsto>l) h1"
using local.pointsto_extend by blast
  
end   
  
context reynolds_algebra  
begin  
 
text {* The following rule applications are for the |-> predicate. *}
  
method try_lssl_l1 = (
match premises in P[thin]:"(?n \<mapsto> ?l) (0)" \<Rightarrow>
  \<open>insert P, auto simp add: pointsto_no_emp\<close>  
)  

method try_lssl_l2 = (
match premises in P:"(n \<mapsto> l) (h)" for h n l \<Rightarrow>
  \<open>match premises in P'[thin]: "(?h1,?h2\<triangleright>h)" \<Rightarrow>
    \<open>match P' in "(0,h\<triangleright>h)" \<Rightarrow> \<open>fail\<close>
     \<bar>"(h,0\<triangleright>h)" \<Rightarrow> \<open>fail\<close>
     \<bar>_ \<Rightarrow> \<open>insert lssl_l2_der[OF P' P],auto\<close>\<close>\<close>,
simp_all?
)  

method try_lssl_l3 = (
match premises in P:"(h1,h2\<triangleright>?h0)" and P':"(n \<mapsto> ?l1) (h1)"
  and P'':"(n \<mapsto> ?l2) (h2)" for h1 h2 n \<Rightarrow>
  \<open>insert lssl_l3_der[OF P P' P'']\<close>,
auto?  
)

method try_lssl_l4 = (
match premises in P[thin]:"(n1\<mapsto>l1) (h)" for n1 l1 h \<Rightarrow>
  \<open>match premises in "(n1\<mapsto>l1) h" \<Rightarrow> \<open>fail\<close>
  \<bar>P':"(?n2\<mapsto>?l2) h" \<Rightarrow> \<open>insert lssl_l4_der[OF P P']\<close>\<close>,
simp?  
)

method try_lssl_l5 = (
match premises in P[thin]: "(n\<mapsto>l) (h1)" for n l h1 \<Rightarrow>
  \<open>match premises in "(n\<mapsto>l) h1" \<Rightarrow> \<open>fail\<close>
  \<bar>P':"(n\<mapsto>l) ?h" \<Rightarrow> \<open>insert lssl_l5_der[OF P P']\<close>\<close>,
simp?
)

text {* We don't implement the application of HE because it's too expensive. *}  
  
text {* The following is an alternative for reasoning about pointers. *}

method invert_pointer = (
(try_lssl_l1
|try_lssl_l3
|try_lssl_l4 
|try_lssl_l5  
|try_lspasl_empl 
|try_lspasl_iu
|try_lspasl_d
|try_lspasl_eq     
|try_lspasl_p
|try_lspasl_c
|try_lssl_l2  
|(magic_mp_tac,(drule magic_mp),auto?,prep?)    
|try_lspasl_starl
|try_lspasl_magicr  
|try_lspasl_starr_guided
|try_lspasl_magicl_guided)+,
auto?)    
  
method sepointer = 
(prep
 |(invert_pointer
  |try_lsfasl_boxl         
  |struct  
  |noninvert   
 )+
 |rare
)+  

method starpointer =
(prep
 |(invert_pointer            
  |(try_lspasl_starr_smart,(try_lspasl_starr,starr_solve_terns?)+) (* Tactics for solving *R formulae. *)   
  |try_lsfasl_boxl
  |struct
  |noninvert          
 )+ 
 |rare
)+

end
  
end  