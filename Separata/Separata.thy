(*
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou, David Sanan.
 *)

theory Separata
imports Main "Sep_Algebra.Separation_Algebra" "HOL-Eisbach.Eisbach_Tools"
begin

text {* The tactics in this file are a simple proof search procedure based on
the labelled sequent calculus LS\_PASL for Propositional Abstract Separation Logic 
in Zhe Hou's PhD thesis. 

We extend the tactics with a treatment for quantifiers over heaps a la Zhe Hou \&
Alwen Tiu's APLAS2016 paper. *}

text {* We define a class which is an extension to cancellative\_sep\_algebra 
with other useful properties in separation algebra, including:
indivisible unit, disjointness, and cross-split. 
We also add a property about the (reverse) distributivity of the disjointness. *}

class heap_sep_algebra = cancellative_sep_algebra +
  assumes sep_add_ind_unit: "\<lbrakk>x + y = 0; x ## y\<rbrakk> \<Longrightarrow> x = 0"
  assumes sep_add_disj: "x##x \<Longrightarrow>x= 0 "   
  assumes sep_add_cross_split: 
      "\<lbrakk>a + b = w; c + d = w; a ## b; c ## d\<rbrakk> \<Longrightarrow>
       \<exists> e f g h. e + f = a \<and> g + h = b \<and> e + g = c \<and> f + h = d \<and> 
                  e ## f \<and> g ## h \<and> e ## g \<and> f ## h"
  assumes disj_dstri: "\<lbrakk>x ## y; y ## z; x ## z\<rbrakk> \<Longrightarrow> x ## (y + z)"
begin

section {* Lemmas about the labelled sequent calculus. *}

text {* An abbreviation of the + and \#\# operators in Separation\_Algebra.thy. 
This notion is closer to the ternary relational atoms used in the literature. 
This will be the main data structure which our labelled sequent calculus works on. *}

definition tern_rel:: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("(_,_\<triangleright>_)" 25) where
"(a,b\<triangleright>c) \<equiv> a ## b \<and> a + b = c"

lemma exist_comb: "x ## y \<Longrightarrow> \<exists>z. (x,y\<triangleright>z)"
by (simp add: tern_rel_def)

lemma disj_comb: 
assumes a1: "(x,y\<triangleright>z)" 
assumes a2: "x ## w" 
assumes a3: "y ## w"
shows "z ## w"
proof -
  from a1 have f1: "x ## y \<and> x + y = z"
    by (simp add: tern_rel_def)
  then show ?thesis using a2 a3
    using local.disj_dstri local.sep_disj_commuteI by blast      
qed

text {* The following lemmas corresponds to inference rules in LS\_PASL. 
Thus these lemmas prove the soundness of LS\_PASL. 
We also show the invertibility of those rules. *}

lemma lspasl_id: 
"Gamma \<and> (A h) \<Longrightarrow> (A h) \<or> Delta"
by simp

lemma lspasl_botl: 
"Gamma \<and> (sep_false h) \<Longrightarrow> Delta"
by simp

lemma lspasl_topr: 
"Gamma \<Longrightarrow> (sep_true h) \<or> Delta"
by simp

lemma lspasl_empl: 
"Gamma \<and> (h = 0) \<longrightarrow> Delta \<Longrightarrow> 
 Gamma \<and> (sep_empty h) \<longrightarrow> Delta"
by (simp add: local.sep_empty_def)

lemma lspasl_empl_inv:
"Gamma \<and> (sep_empty h) \<longrightarrow> Delta \<Longrightarrow>  
 Gamma \<and> (h = 0) \<longrightarrow> Delta"
by simp

text {* The following two lemmas are the same as applying 
simp add: sep\_empty\_def. *}

lemma lspasl_empl_der: "sep_empty h \<Longrightarrow> h = 0"
by (simp add: local.sep_empty_def)

lemma lspasl_empl_eq: "(sep_empty h) = (h = 0)"
by (simp add: local.sep_empty_def)

lemma lspasl_empr: 
"Gamma \<longrightarrow> (sep_empty 0) \<or> Delta"
by simp

lemma lspasl_notl: 
"Gamma \<longrightarrow> (A h) \<or> Delta \<Longrightarrow> 
 Gamma \<and> ((not A) h) \<longrightarrow> Delta"
by auto

lemma lspasl_notl_inv:
"Gamma \<and> ((not A) h) \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<longrightarrow> (A h) \<or> Delta"
by auto

lemma lspasl_notr: 
"Gamma \<and> (A h) \<longrightarrow> Delta \<Longrightarrow> 
 Gamma \<longrightarrow> ((not A) h) \<or> Delta"
by simp

lemma lspasl_notr_inv:
"Gamma \<longrightarrow> ((not A) h) \<or> Delta \<Longrightarrow>
 Gamma \<and> (A h) \<longrightarrow> Delta"
by simp

lemma lspasl_andl: 
"Gamma \<and> (A h) \<and> (B h) \<longrightarrow> Delta \<Longrightarrow> 
 Gamma \<and> ((A and B) h) \<longrightarrow> Delta"
by simp

lemma lspasl_andl_inv:
"Gamma \<and> ((A and B) h) \<longrightarrow> Delta \<Longrightarrow> 
 Gamma \<and> (A h) \<and> (B h) \<longrightarrow> Delta"
by simp

lemma lspasl_andr: 
"\<lbrakk>Gamma \<longrightarrow> (A h) \<or> Delta; Gamma \<longrightarrow> (B h) \<or> Delta\<rbrakk> \<Longrightarrow>
 Gamma \<longrightarrow> ((A and B) h) \<or> Delta"
by auto

lemma lspasl_andr_inv:
"Gamma \<longrightarrow> ((A and B) h) \<or> Delta \<Longrightarrow>
 (Gamma \<longrightarrow> (A h) \<or> Delta) \<and> (Gamma \<longrightarrow> (B h) \<or> Delta)"
by auto

lemma lspasl_orl:
"\<lbrakk>Gamma \<and> (A h) \<longrightarrow> Delta; Gamma \<and> (B h) \<longrightarrow> Delta\<rbrakk> \<Longrightarrow>
 Gamma \<and> (A or B) h \<longrightarrow> Delta"
by auto

lemma lspasl_orl_inv:
"Gamma \<and> (A or B) h \<longrightarrow> Delta \<Longrightarrow>
 (Gamma \<and> (A h) \<longrightarrow> Delta) \<and> (Gamma \<and> (B h) \<longrightarrow> Delta)"
by simp

lemma lspasl_orr:
"Gamma \<longrightarrow> (A h) \<or> (B h) \<or> Delta \<Longrightarrow>
 Gamma \<longrightarrow> ((A or B) h) \<or> Delta"
by simp

lemma lspasl_orr_inv:
"Gamma \<longrightarrow> ((A or B) h) \<or> Delta \<Longrightarrow>
 Gamma \<longrightarrow> (A h) \<or> (B h) \<or> Delta"
by simp

lemma lspasl_impl:
"\<lbrakk>Gamma \<longrightarrow> (A h) \<or> Delta; Gamma \<and> (B h) \<longrightarrow> Delta\<rbrakk> \<Longrightarrow>
 Gamma \<and> ((A imp B) h) \<longrightarrow> Delta"
by auto

lemma lspasl_impl_inv:
"Gamma \<and> ((A imp B) h) \<longrightarrow> Delta \<Longrightarrow>
 (Gamma \<longrightarrow> (A h) \<or> Delta) \<and> (Gamma \<and> (B h) \<longrightarrow> Delta)"    
by auto

lemma lspasl_impr:
"Gamma \<and> (A h) \<longrightarrow> (B h) \<or> Delta \<Longrightarrow>
 Gamma \<longrightarrow> ((A imp B) h) \<or> Delta"
by simp

lemma lspasl_impr_inv:
"Gamma \<longrightarrow> ((A imp B) h) \<or> Delta \<Longrightarrow>
 Gamma \<and> (A h) \<longrightarrow> (B h) \<or> Delta"
by simp

text {* We don't provide lemmas for derivations for the classical connectives,
as Isabelle proof methods can easily deal with them. *}

lemma lspasl_starl:
"(\<exists>h1 h2. (Gamma \<and> (h1,h2\<triangleright>h0) \<and> (A h1) \<and> (B h2))) \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> ((A ** B) h0) \<longrightarrow> Delta"
using local.sep_conj_def by (auto simp add: tern_rel_def)

lemma lspasl_starl_inv:
"Gamma \<and> ((A ** B) h0) \<longrightarrow> Delta \<Longrightarrow>
 (\<exists>h1 h2. (Gamma \<and> (h1,h2\<triangleright>h0) \<and> (A h1) \<and> (B h2))) \<longrightarrow> Delta"
using local.sep_conjI by (auto simp add: tern_rel_def)

lemma lspasl_starl_der:
"((A ** B) h0) \<Longrightarrow> (\<exists>h1 h2. (h1,h2\<triangleright>h0) \<and> (A h1) \<and> (B h2))"
by (metis lspasl_starl)

lemma lspasl_starl_eq:
"((A ** B) h0) = (\<exists>h1 h2. (h1,h2\<triangleright>h0) \<and> (A h1) \<and> (B h2))"
by (metis lspasl_starl lspasl_starl_inv)

lemma lspasl_starr:
"\<lbrakk>Gamma \<and> (h1,h2\<triangleright>h0) \<longrightarrow> (A h1) \<or> ((A ** B) h0) \<or> Delta; 
  Gamma \<and> (h1,h2\<triangleright>h0) \<longrightarrow> (B h2) \<or> ((A ** B) h0) \<or> Delta\<rbrakk> \<Longrightarrow>
 Gamma \<and> (h1,h2\<triangleright>h0) \<longrightarrow> ((A ** B) h0) \<or> Delta"
using local.sep_conjI by (auto simp add: tern_rel_def)

lemma lspasl_starr_inv:
"Gamma \<and> (h1,h2\<triangleright>h0) \<longrightarrow> ((A ** B) h0) \<or> Delta \<Longrightarrow> 
 (Gamma \<and> (h1,h2\<triangleright>h0) \<longrightarrow> (A h1) \<or> ((A ** B) h0) \<or> Delta) \<and> 
 (Gamma \<and> (h1,h2\<triangleright>h0) \<longrightarrow> (B h2) \<or> ((A ** B) h0) \<or> Delta)"
by simp

text {* For efficiency we only apply *R on a pair of a ternary relational atom
and a formula ONCE. To achieve this, we create a special predicate to indicate that
a pair of a ternary relational atom and a formula has already been used in
a *R application. 
Note that the predicate is true even if the *R rule hasn't been applied. 
We will not infer the truth of this predicate in proof search, but only
check its syntactical appearance, which is only generated by the lemma lspasl\_starr\_der. 
We need to ensure that this predicate is not generated elsewhere
in the proof search. *}

definition starr_applied:: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
"starr_applied h1 h2 h0 F \<equiv> (h1,h2\<triangleright>h0) \<and> \<not>(F h0)"

lemma lspasl_starr_der:
"(h1,h2\<triangleright>h0) \<Longrightarrow> \<not> ((A ** B) h0) \<Longrightarrow> 
  ((h1,h2\<triangleright>h0) \<and> \<not> ((A h1) \<or> ((A ** B) h0)) \<and> (starr_applied h1 h2 h0 (A ** B))) \<or> 
  ((h1,h2\<triangleright>h0) \<and> \<not> ((B h2) \<or> ((A ** B) h0)) \<and> (starr_applied h1 h2 h0 (A ** B)))"
by (simp add: lspasl_starl_eq starr_applied_def)

lemma lspasl_starr_der2:
"(h1,h2\<triangleright>h0) \<Longrightarrow> \<not> ((A ** B) h0) \<Longrightarrow> 
  ((h1,h2\<triangleright>h0) \<and> \<not> ((A h2) \<or> ((A ** B) h0)) \<and> (starr_applied h2 h1 h0 (A ** B))) \<or> 
  ((h1,h2\<triangleright>h0) \<and> \<not> ((B h1) \<or> ((A ** B) h0)) \<and> (starr_applied h2 h1 h0 (A ** B)))"
using local.sep_add_commute local.sep_disj_commute lspasl_starr_der tern_rel_def by auto

lemma lspasl_starr_eq: 
"((h1,h2\<triangleright>h0) \<and> \<not> ((A ** B) h0)) = 
  (((h1,h2\<triangleright>h0) \<and> \<not> ((A h1) \<or> ((A ** B) h0))) \<or> ((h1,h2\<triangleright>h0) \<and> \<not> ((B h2) \<or> ((A ** B) h0))))"
using lspasl_starr_der by blast

lemma lspasl_magicl:
"\<lbrakk>Gamma \<and> (h1,h2\<triangleright>h0) \<and> ((A \<longrightarrow>* B) h2) \<longrightarrow> (A h1) \<or> Delta;
  Gamma \<and> (h1,h2\<triangleright>h0) \<and> ((A \<longrightarrow>* B) h2) \<and> (B h0) \<longrightarrow> Delta\<rbrakk> \<Longrightarrow>
 Gamma \<and> (h1,h2\<triangleright>h0) \<and> ((A \<longrightarrow>* B) h2) \<longrightarrow> Delta"
using local.sep_add_commute local.sep_disj_commuteI local.sep_implD tern_rel_def
by fastforce

lemma lspasl_magicl_inv:
"Gamma \<and> (h1,h2\<triangleright>h0) \<and> ((A \<longrightarrow>* B) h2) \<longrightarrow> Delta \<Longrightarrow>
 (Gamma \<and> (h1,h2\<triangleright>h0) \<and> ((A \<longrightarrow>* B) h2) \<longrightarrow> (A h1) \<or> Delta) \<and> 
 (Gamma \<and> (h1,h2\<triangleright>h0) \<and> ((A \<longrightarrow>* B) h2) \<and> (B h0) \<longrightarrow> Delta)"
by simp

text {* For efficiency we only apply -*L on a pair of a ternary relational atom
and a formula ONCE. To achieve this, we create a special predicate to indicate that
a pair of a ternary relational atom and a formula has already been used in
a *R application. 
Note that the predicate is true even if the *R rule hasn't been applied. 
We will not infer the truth of this predicate in proof search, but only
check its syntactical appearance, which is only generated by the lemma lspasl\_magicl\_der.
We need to ensure that in the proof search of Separata, this predicate is 
not generated elsewhere.*}

definition magicl_applied:: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
"magicl_applied h1 h2 h0 F \<equiv> (h1,h2\<triangleright>h0) \<and> (F h2)"

lemma lspasl_magicl_der:
"(h1,h2\<triangleright>h0) \<Longrightarrow> ((A \<longrightarrow>* B) h2) \<Longrightarrow>
  ((h1,h2\<triangleright>h0) \<and> \<not>(A h1) \<and> ((A \<longrightarrow>* B) h2) \<and> (magicl_applied h1 h2 h0 (A \<longrightarrow>* B))) \<or> 
  ((h1,h2\<triangleright>h0) \<and> (B h0) \<and> ((A \<longrightarrow>* B) h2) \<and> (magicl_applied h1 h2 h0 (A \<longrightarrow>* B)))"
by (metis lspasl_magicl magicl_applied_def)

lemma lspasl_magicl_der2:
"(h2,h1\<triangleright>h0) \<Longrightarrow> ((A \<longrightarrow>* B) h2) \<Longrightarrow>
  ((h2,h1\<triangleright>h0) \<and> \<not>(A h1) \<and> ((A \<longrightarrow>* B) h2) \<and> (magicl_applied h1 h2 h0 (A \<longrightarrow>* B))) \<or> 
  ((h2,h1\<triangleright>h0) \<and> (B h0) \<and> ((A \<longrightarrow>* B) h2) \<and> (magicl_applied h1 h2 h0 (A \<longrightarrow>* B)))"
by (metis local.sep_add_commute local.sep_disj_commuteI local.sep_implD magicl_applied_def tern_rel_def)

lemma lspasl_magicl_eq:
"((h1,h2\<triangleright>h0) \<and> ((A \<longrightarrow>* B) h2)) =
  (((h1,h2\<triangleright>h0) \<and> \<not>(A h1) \<and> ((A \<longrightarrow>* B) h2)) \<or> ((h1,h2\<triangleright>h0) \<and> (B h0) \<and> ((A \<longrightarrow>* B) h2)))"
using lspasl_magicl_der by blast

lemma lspasl_magicr:
"(\<exists>h1 h0. Gamma \<and> (h1,h2\<triangleright>h0) \<and> (A h1) \<and> ((not B) h0)) \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<longrightarrow> ((A \<longrightarrow>* B) h2) \<or> Delta"
using local.sep_add_commute local.sep_disj_commute local.sep_impl_def tern_rel_def
by auto

lemma lspasl_magicr_inv:
"Gamma \<longrightarrow> ((A \<longrightarrow>* B) h2) \<or> Delta \<Longrightarrow>
 (\<exists>h1 h0. Gamma \<and> (h1,h2\<triangleright>h0) \<and> (A h1) \<and> ((not B) h0)) \<longrightarrow> Delta"
by (metis lspasl_magicl)

lemma lspasl_magicr_der:
"\<not> ((A \<longrightarrow>* B) h2) \<Longrightarrow> 
 (\<exists>h1 h0. (h1,h2\<triangleright>h0) \<and> (A h1) \<and> ((not B) h0))"
by (metis lspasl_magicr)

lemma lspasl_magicr_eq:
"(\<not> ((A \<longrightarrow>* B) h2)) = 
 ((\<exists>h1 h0. (h1,h2\<triangleright>h0) \<and> (A h1) \<and> ((not B) h0)))"
by (metis lspasl_magicl lspasl_magicr)

lemma lspasl_eq: 
"Gamma \<and> (0,h2\<triangleright>h2) \<and> h1 = h2 \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (0,h1\<triangleright>h2) \<longrightarrow> Delta"
by (simp add: tern_rel_def)

lemma lspasl_eq_inv:
"Gamma \<and> (0,h1\<triangleright>h2) \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (0,h2\<triangleright>h2) \<and> h1 = h2 \<longrightarrow> Delta"
by simp

lemma lspasl_eq_der: "(0,h1\<triangleright>h2) \<Longrightarrow> ((0,h1\<triangleright>h1) \<and> h1 = h2)"
using lspasl_eq by auto

lemma lspasl_eq_eq: "(0,h1\<triangleright>h2) = ((0,h1\<triangleright>h1) \<and> (h1 = h2))"
by (simp add: tern_rel_def)

lemma lspasl_eq2: 
"Gamma \<and> (h2,0\<triangleright>h2) \<and> h1 = h2 \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (h1,0\<triangleright>h2) \<longrightarrow> Delta"
by (simp add: tern_rel_def)

lemma lspasl_eq_inv2:
"Gamma \<and> (h1,0\<triangleright>h2) \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (h2,0\<triangleright>h2) \<and> h1 = h2 \<longrightarrow> Delta"
by simp

lemma lspasl_eq_der2: "(h1,0\<triangleright>h2) \<Longrightarrow> ((h1,0\<triangleright>h1) \<and> h1 = h2)"
using lspasl_eq2 by auto

lemma lspasl_eq_eq2: "(h1,0\<triangleright>h2) = ((h1,0\<triangleright>h1) \<and> (h1 = h2))"
by (simp add: tern_rel_def)

lemma lspasl_u:
"Gamma \<and> (h,0\<triangleright>h) \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<longrightarrow> Delta"
by (simp add: tern_rel_def)

lemma lspasl_u_inv:
"Gamma \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (h,0\<triangleright>h) \<longrightarrow> Delta"
by simp

lemma lspasl_u_der: "(h,0\<triangleright>h)"
using lspasl_u by auto

lemma lspasl_e:
"Gamma \<and> (h1,h2\<triangleright>h0) \<and> (h2,h1\<triangleright>h0) \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (h1,h2\<triangleright>h0) \<longrightarrow> Delta"
by (simp add: local.sep_add_commute local.sep_disj_commute tern_rel_def)

lemma lspasl_e_inv:
"Gamma \<and> (h1,h2\<triangleright>h0) \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (h1,h2\<triangleright>h0) \<and> (h2,h1\<triangleright>h0) \<longrightarrow> Delta"
by simp

lemma lspasl_e_der: "(h1,h2\<triangleright>h0) \<Longrightarrow> (h1,h2\<triangleright>h0) \<and> (h2,h1\<triangleright>h0)"
using lspasl_e by blast           

lemma lspasl_e_eq: "(h1,h2\<triangleright>h0) = ((h1,h2\<triangleright>h0) \<and> (h2,h1\<triangleright>h0))"
using lspasl_e by blast

lemma lspasl_a_der: 
assumes a1: "(h1,h2\<triangleright>h0)"
    and a2: "(h3,h4\<triangleright>h1)"
shows "(\<exists>h5. (h3,h5\<triangleright>h0) \<and> (h2,h4\<triangleright>h5) \<and> (h1,h2\<triangleright>h0) \<and> (h3,h4\<triangleright>h1))"
proof -
  have f1: "h1 ## h2"
    using a1 by (simp add: tern_rel_def)    
  have f2: "h3 ## h4"
    using a2 by (simp add: tern_rel_def)    
  have f3: "h3 + h4 = h1"
    using a2 by (simp add: tern_rel_def)    
  then have "h3 ## h2"
    using f2 f1 by (metis local.sep_disj_addD1 local.sep_disj_commute)
  then have f4: "h2 ## h3"
    by (metis local.sep_disj_commute)
  then have f5: "h2 + h4 ## h3"
    using f3 f2 f1 by (metis (no_types) local.sep_add_commute local.sep_add_disjI1)
  have "h4 ## h2"
    using f3 f2 f1 by (metis local.sep_add_commute local.sep_disj_addD1 local.sep_disj_commute)
  then show ?thesis
    using f5 f4 by (metis (no_types) assms tern_rel_def local.sep_add_assoc local.sep_add_commute local.sep_disj_commute)
qed

lemma lspasl_a:
"(\<exists>h5. Gamma \<and> (h3,h5\<triangleright>h0) \<and> (h2,h4\<triangleright>h5) \<and> (h1,h2\<triangleright>h0) \<and> (h3,h4\<triangleright>h1)) \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (h1,h2\<triangleright>h0) \<and> (h3,h4\<triangleright>h1) \<longrightarrow> Delta"
using lspasl_a_der by blast

lemma lspasl_a_inv:
"Gamma \<and> (h1,h2\<triangleright>h0) \<and> (h3,h4\<triangleright>h1) \<longrightarrow> Delta \<Longrightarrow>
 (\<exists>h5. Gamma \<and> (h3,h5\<triangleright>h0) \<and> (h2,h4\<triangleright>h5) \<and> (h1,h2\<triangleright>h0) \<and> (h3,h4\<triangleright>h1)) \<longrightarrow> Delta"
by auto

lemma lspasl_a_eq: 
"((h1,h2\<triangleright>h0) \<and> (h3,h4\<triangleright>h1)) = 
 (\<exists>h5. (h3,h5\<triangleright>h0) \<and> (h2,h4\<triangleright>h5) \<and> (h1,h2\<triangleright>h0) \<and> (h3,h4\<triangleright>h1))"
using lspasl_a_der by blast

lemma lspasl_p:
"Gamma \<and> (h1,h2\<triangleright>h0) \<and> h0 = h3 \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (h1,h2\<triangleright>h0) \<and> (h1,h2\<triangleright>h3) \<longrightarrow> Delta"
by (auto simp add: tern_rel_def)

lemma lspasl_p_inv:
"Gamma \<and> (h1,h2\<triangleright>h0) \<and> (h1,h2\<triangleright>h3) \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (h1,h2\<triangleright>h0) \<and> h0 = h3 \<longrightarrow> Delta"
by auto

lemma lspasl_p_der:
"(h1,h2\<triangleright>h0) \<Longrightarrow> (h1,h2\<triangleright>h3) \<Longrightarrow> (h1,h2\<triangleright>h0) \<and> h0 = h3"
by (simp add: tern_rel_def)

lemma lspasl_p_eq: 
"((h1,h2\<triangleright>h0) \<and> (h1,h2\<triangleright>h3)) = ((h1,h2\<triangleright>h0) \<and> h0 = h3)"
using lspasl_p_der by auto

lemma lspasl_p2:
"Gamma \<and> (h1,h2\<triangleright>h0) \<and> (h2,h1\<triangleright>h0) \<and> h0 = h3 \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (h1,h2\<triangleright>h0) \<and> (h2,h1\<triangleright>h3) \<longrightarrow> Delta"
using lspasl_e_der lspasl_p_eq by blast

lemma lspasl_p_inv2:
"Gamma \<and> (h1,h2\<triangleright>h0) \<and> (h2,h1\<triangleright>h3) \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (h1,h2\<triangleright>h0) \<and> (h2,h1\<triangleright>h0) \<and> h0 = h3 \<longrightarrow> Delta"
by auto

lemma lspasl_p_der2:
"(h1,h2\<triangleright>h0) \<Longrightarrow> (h2,h1\<triangleright>h3) \<Longrightarrow> (h1,h2\<triangleright>h0) \<and> (h2,h1\<triangleright>h0) \<and> h0 = h3"
using lspasl_e_der lspasl_p_eq by blast

lemma lspasl_p_eq2: 
"((h1,h2\<triangleright>h0) \<and> (h2,h1\<triangleright>h3)) = ((h1,h2\<triangleright>h0) \<and> (h2,h1\<triangleright>h0) \<and> h0 = h3)"
using lspasl_p_der lspasl_e_der by blast

lemma lspasl_c:
"Gamma \<and> (h1,h2\<triangleright>h0) \<and> h2 = h3 \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (h1,h2\<triangleright>h0) \<and> (h1,h3\<triangleright>h0) \<longrightarrow> Delta"
by (metis local.sep_add_cancelD local.sep_add_commute tern_rel_def
local.sep_disj_commuteI)

lemma lspasl_c_inv:
"Gamma \<and> (h1,h2\<triangleright>h0) \<and> (h1,h3\<triangleright>h0) \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (h1,h2\<triangleright>h0) \<and> h2 = h3 \<longrightarrow> Delta"
by auto

lemma lspasl_c_der:
"(h1,h2\<triangleright>h0) \<Longrightarrow> (h1,h3\<triangleright>h0) \<Longrightarrow> (h1,h2\<triangleright>h0) \<and> h2 = h3"
using lspasl_c by blast

lemma lspasl_c_eq:
"((h1,h2\<triangleright>h0) \<and> (h1,h3\<triangleright>h0)) = ((h1,h2\<triangleright>h0) \<and> h2 = h3)"
using lspasl_c_der by auto

lemma lspasl_c2:
"Gamma \<and> (h1,h2\<triangleright>h0) \<and> (h2,h1\<triangleright>h0) \<and> h2 = h3 \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (h1,h2\<triangleright>h0) \<and> (h3,h1\<triangleright>h0) \<longrightarrow> Delta"
by (metis local.sep_add_cancelD local.sep_add_commute tern_rel_def
local.sep_disj_commuteI)

lemma lspasl_c_inv2:
"Gamma \<and> (h1,h2\<triangleright>h0) \<and> (h3,h1\<triangleright>h0) \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (h1,h2\<triangleright>h0) \<and> (h2,h1\<triangleright>h0) \<and> h2 = h3 \<longrightarrow> Delta"
by auto

lemma lspasl_c_der2:
"(h1,h2\<triangleright>h0) \<Longrightarrow> (h3,h1\<triangleright>h0) \<Longrightarrow> (h1,h2\<triangleright>h0) \<and> (h2,h1\<triangleright>h0) \<and> h2 = h3"
using lspasl_c2 by blast

lemma lspasl_c_eq2:
"((h1,h2\<triangleright>h0) \<and> (h3,h1\<triangleright>h0)) = ((h1,h2\<triangleright>h0) \<and> (h2,h1\<triangleright>h0) \<and> h2 = h3)"
using lspasl_c_der lspasl_e_der by blast

lemma lspasl_c3:
"Gamma \<and> (h2,h1\<triangleright>h0) \<and> (h1,h2\<triangleright>h0) \<and> h2 = h3 \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (h2,h1\<triangleright>h0) \<and> (h1,h3\<triangleright>h0) \<longrightarrow> Delta"
by (metis local.sep_add_cancelD local.sep_add_commute tern_rel_def
local.sep_disj_commuteI)

lemma lspasl_c_inv3:
"Gamma \<and> (h2,h1\<triangleright>h0) \<and> (h1,h3\<triangleright>h0) \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (h2,h1\<triangleright>h0) \<and> (h1,h2\<triangleright>h0) \<and> h2 = h3 \<longrightarrow> Delta"
by auto

lemma lspasl_c_der3:
"(h2,h1\<triangleright>h0) \<Longrightarrow> (h1,h3\<triangleright>h0) \<Longrightarrow> (h2,h1\<triangleright>h0) \<and> (h1,h2\<triangleright>h0) \<and> h2 = h3"
using lspasl_c3 by blast

lemma lspasl_c_eq3:
"((h2,h1\<triangleright>h0) \<and> (h1,h3\<triangleright>h0)) = ((h2,h1\<triangleright>h0) \<and> (h1,h2\<triangleright>h0) \<and> h2 = h3)"
using lspasl_c_der3 by blast

lemma lspasl_c4:
"Gamma \<and> (h2,h1\<triangleright>h0) \<and> h2 = h3 \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (h2,h1\<triangleright>h0) \<and> (h3,h1\<triangleright>h0) \<longrightarrow> Delta"
by (metis local.sep_add_cancelD  tern_rel_def)

lemma lspasl_c_inv4:
"Gamma \<and> (h2,h1\<triangleright>h0) \<and> (h3,h1\<triangleright>h0) \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (h2,h1\<triangleright>h0) \<and> h2 = h3 \<longrightarrow> Delta"
by auto

lemma lspasl_c_der4:
"(h2,h1\<triangleright>h0) \<Longrightarrow> (h3,h1\<triangleright>h0) \<Longrightarrow> (h2,h1\<triangleright>h0) \<and> h2 = h3"
using lspasl_c4 by blast

lemma lspasl_c_eq4:
"((h2,h1\<triangleright>h0) \<and> (h3,h1\<triangleright>h0)) = ((h2,h1\<triangleright>h0) \<and> h2 = h3)"
using lspasl_c_der4 by blast

lemma lspasl_iu:
"Gamma \<and> (0,h2\<triangleright>0) \<and> h1 = 0 \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (h1,h2\<triangleright>0) \<longrightarrow> Delta"
using local.sep_add_ind_unit tern_rel_def by blast

lemma lspasl_iu_inv:
"Gamma \<and> (h1,h2\<triangleright>0) \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (0,h2\<triangleright>0) \<and> h1 = 0 \<longrightarrow> Delta"
by simp

lemma lspasl_iu_der:
"(h1,h2\<triangleright>0) \<Longrightarrow> ((0,0\<triangleright>0) \<and> h1 = 0 \<and> h2 = 0)"
using lspasl_eq_der lspasl_iu by (auto simp add: tern_rel_def) 

lemma lspasl_iu_eq:
"(h1,h2\<triangleright>0) = ((0,0\<triangleright>0) \<and> h1 = 0 \<and> h2 = 0)"
using lspasl_iu_der by blast 

lemma lspasl_d:
"Gamma \<and> (0,0\<triangleright>h2) \<and> h1 = 0 \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (h1,h1\<triangleright>h2) \<longrightarrow> Delta"
using local.sep_add_disj tern_rel_def by blast

lemma lspasl_d_inv:
"Gamma \<and> (h1,h1\<triangleright>h2) \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (0,0\<triangleright>h2) \<and> h1 = 0 \<longrightarrow> Delta"
by blast

lemma lspasl_d_der:
"(h1,h1\<triangleright>h2) \<Longrightarrow> (0,0\<triangleright>0) \<and> h1 = 0 \<and> h2 = 0"
using lspasl_d lspasl_eq_der by blast

lemma lspasl_d_eq:
"(h1,h1\<triangleright>h2) = ((0,0\<triangleright>0) \<and> h1 = 0 \<and> h2 = 0)"
using lspasl_d_der by blast

lemma lspasl_cs_der: 
assumes a1: "(h1,h2\<triangleright>h0)" 
    and a2: "(h3,h4\<triangleright>h0)" 
shows "(\<exists>h5 h6 h7 h8. (h5,h6\<triangleright>h1) \<and> (h7,h8\<triangleright>h2) \<and>(h5,h7\<triangleright>h3) \<and> (h6,h8\<triangleright>h4)
        \<and> (h1,h2\<triangleright>h0) \<and> (h3,h4\<triangleright>h0))"
proof -
  from a1 a2 have "h1 + h2 = h0 \<and> h3 + h4 = h0 \<and> h1 ## h2 \<and> h3 ## h4"
   by (simp add: tern_rel_def)
  then have "\<exists>h5 h6 h7 h8. h5 + h6 = h1 \<and> h7 + h8 = h2 \<and>
    h5 + h7 = h3 \<and> h6 + h8 = h4 \<and> h5 ## h6 \<and> h7 ## h8 \<and>
    h5 ## h7 \<and> h6 ## h8"
   using local.sep_add_cross_split by auto
  then have "\<exists>h5 h6 h7 h8. (h5,h6\<triangleright>h1) \<and> h7 + h8 = h2 \<and>
    h5 + h7 = h3 \<and> h6 + h8 = h4 \<and> h7 ## h8 \<and>
    h5 ## h7 \<and> h6 ## h8"
   by (auto simp add: tern_rel_def)
  then have "\<exists>h5 h6 h7 h8. (h5,h6\<triangleright>h1) \<and> (h7,h8\<triangleright>h2) \<and>
    h5 + h7 = h3 \<and> h6 + h8 = h4 \<and> h5 ## h7 \<and> h6 ## h8"
   by (auto simp add: tern_rel_def)
  then have "\<exists>h5 h6 h7 h8. (h5,h6\<triangleright>h1) \<and> (h7,h8\<triangleright>h2) \<and>
    (h5,h7\<triangleright>h3) \<and> h6 + h8 = h4 \<and> h6 ## h8"
   by (auto simp add: tern_rel_def)
  then show ?thesis using a1 a2 tern_rel_def by blast 
qed

lemma lspasl_cs:
"(\<exists>h5 h6 h7 h8. Gamma \<and> (h5,h6\<triangleright>h1) \<and> (h7,h8\<triangleright>h2) \<and>(h5,h7\<triangleright>h3) \<and> (h6,h8\<triangleright>h4) \<and> (h1,h2\<triangleright>h0) \<and> (h3,h4\<triangleright>h0)) \<longrightarrow> Delta \<Longrightarrow>
 Gamma \<and> (h1,h2\<triangleright>h0) \<and> (h3,h4\<triangleright>h0) \<longrightarrow> Delta"
using lspasl_cs_der by auto

lemma lspasl_cs_inv:
"Gamma \<and> (h1,h2\<triangleright>h0) \<and> (h3,h4\<triangleright>h0) \<longrightarrow> Delta \<Longrightarrow>
 (\<exists>h5 h6 h7 h8. Gamma \<and> (h5,h6\<triangleright>h1) \<and> (h7,h8\<triangleright>h2) \<and>(h5,h7\<triangleright>h3) \<and> (h6,h8\<triangleright>h4) \<and> (h1,h2\<triangleright>h0) \<and> (h3,h4\<triangleright>h0)) \<longrightarrow> Delta"
by auto

lemma lspasl_cs_eq: 
"((h1,h2\<triangleright>h0) \<and> (h3,h4\<triangleright>h0)) =
 (\<exists>h5 h6 h7 h8. (h5,h6\<triangleright>h1) \<and> (h7,h8\<triangleright>h2) \<and>(h5,h7\<triangleright>h3) \<and> (h6,h8\<triangleright>h4) \<and> 
  (h1,h2\<triangleright>h0) \<and> (h3,h4\<triangleright>h0))"
using lspasl_cs_der by auto 

text {* This section extends separata with treatments for quantifiers over 
heaps. This is similar to the modalities [] and <> we used in our APLAS2016 
paper. Here we use /\ h. A h be mean that h is universally quantified, which 
is h: []A in the APLAS2016 paper. Similarly, Formulae like this are frequently used in seL4's proofs. *}

lemma lsfasl_boxl_der:
"(\<And>h. A h) \<Longrightarrow> \<forall>h. A h"
by simp

end

text {* The above proves the soundness and invertibility of LS\_PASL. *}

section {* Lemmas David proved for separation algebra. *}

lemma sep_substate_tran: 
  "x \<preceq> y \<and> y \<preceq> z \<Longrightarrow> x \<preceq> z" 
  unfolding sep_substate_def
proof -
  assume "(\<exists>z. x ## z \<and> x + z = y) \<and> (\<exists>za. y ## za \<and> y + za = z)"
  then obtain x' y' where  fixed:"(x ## x' \<and> x + x' = y) \<and> (y ## y' \<and> y + y' = z)"
   by auto
  then have disj_x:"x ## y' \<and> x' ## y'" 
    using sep_disj_addD sep_disj_commute by blast 
  then have p1:"x ## (x' + y')" using fixed sep_disj_commute sep_disj_addI3 
    by blast
  then have "x + (x' + y') = z" using disj_x by (metis (no_types) fixed sep_add_assoc) 
  thus "\<exists>za. x ## za \<and> x + za = z" using p1 by auto
qed

lemma precise_sep_conj: 
 assumes a1:"precise I" and
        a2:"precise I'"
 shows "precise (I \<and>* I')"
proof  (clarsimp simp: precise_def)
  fix hp hp' h
  assume hp:"hp \<preceq> h" and hp': "hp' \<preceq> h" and ihp: "(I \<and>* I') hp" and ihp': "(I \<and>* I') hp'"
  obtain hp1 hp2 where ihpex: "hp1 ## hp2 \<and> hp = hp1 + hp2 \<and> I hp1 \<and> I' hp2" using ihp sep_conjD by blast
  obtain hp1' hp2' where ihpex': "hp1' ## hp2' \<and> hp' = hp1' + hp2' \<and> I hp1' \<and> I' hp2'" using ihp' sep_conjD by blast
  have f3: "hp2' ## hp1'"
    by (simp add: ihpex' sep_disj_commute)
  have f4: "hp2 ## hp1"
    using ihpex sep_disj_commute by blast
  have f5:"\<And>a. \<not> a \<preceq> hp \<or> a \<preceq> h"
    using hp sep_substate_tran by blast
  have f6:"\<And>a. \<not> a \<preceq> hp' \<or> a \<preceq> h"
    using hp' sep_substate_tran by blast    
  thus "hp = hp'"
    using f4 f3 f5 a2 a1 a1 a2 ihpex ihpex' 
    unfolding precise_def by (metis sep_add_commute sep_substate_disj_add')  
qed

lemma unique_subheap:
"(\<sigma>1,\<sigma>2\<triangleright>\<sigma>) \<Longrightarrow> \<exists>!\<sigma>2'.(\<sigma>1,\<sigma>2'\<triangleright>\<sigma>)"
using lspasl_c_der by blast

lemma sep_split_substate:
  "(\<sigma>1, \<sigma>2\<triangleright> \<sigma>) \<Longrightarrow> 
   (\<sigma>1  \<preceq> \<sigma>) \<and> (\<sigma>2  \<preceq> \<sigma>)"
proof-
assume a1:"(\<sigma>1, \<sigma>2\<triangleright> \<sigma>)"  
  thus "(\<sigma>1  \<preceq> \<sigma>) \<and> (\<sigma>2  \<preceq> \<sigma>)"
   by (auto simp add: sep_disj_commute 
       tern_rel_def 
      sep_substate_disj_add 
      sep_substate_disj_add')   
qed

abbreviation sep_septraction :: "(('a::sep_algebra) \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infixr "\<longrightarrow>\<oplus>" 25)
where
  "P \<longrightarrow>\<oplus> Q \<equiv>  not (P \<longrightarrow>* not Q)"

section {* Below we integrate the inference rules in proof search. *}

method try_lspasl_empl = (
match premises in P[thin]:"sep_empty ?h" \<Rightarrow> 
  \<open>insert lspasl_empl_der[OF P]\<close>,
simp?
)

method try_lspasl_starl = (
match premises in P[thin]:"(?A ** ?B) ?h" \<Rightarrow> 
  \<open>insert lspasl_starl_der[OF P], auto\<close>,
simp?
)

method try_lspasl_magicr = (
match premises in P[thin]:"\<not>(?A \<longrightarrow>* ?B) ?h" \<Rightarrow> 
  \<open>insert lspasl_magicr_der[OF P], auto\<close>,
simp?
)

text {* Only apply the rule Eq on (0,h1,h2) where h1 and h2
are not syntactically the same. 
Note that we build commutativity in this rule application. *}

method try_lspasl_eq = (
match premises in P[thin]:"(0,?h1\<triangleright>?h2)" \<Rightarrow> 
  \<open>match P in 
    "(0,h\<triangleright>h)" for h \<Rightarrow> \<open>fail\<close>     
    \<bar>_ \<Rightarrow> \<open>insert lspasl_eq_der[OF P], auto\<close>\<close>
\<bar> P'[thin]: "(?h1,0\<triangleright>?h2)" \<Rightarrow>
  \<open>match P' in
    "(h,0\<triangleright>h)" for h \<Rightarrow> \<open>fail\<close>
    \<bar>_ \<Rightarrow> \<open>insert lspasl_eq_der2[OF P'], auto\<close>\<close>,
simp?
)

text {* We restrict that the rule IU can't be applied 
on (0,0,0). *}

method try_lspasl_iu = (
match premises in P[thin]:"(?h1,?h2\<triangleright>0)" \<Rightarrow> 
  \<open>match P in
    "(0,0\<triangleright>0)" \<Rightarrow> \<open>fail\<close>
    \<bar>_ \<Rightarrow> \<open>insert lspasl_iu_der[OF P], auto\<close>\<close>,
simp?
)

text {* We restrict that the rule D can't be applied 
on (0,0,0). *}

method try_lspasl_d = (
match premises in P[thin]:"(h1,h1\<triangleright>h2)" for h1 h2 \<Rightarrow> 
  \<open>match P in 
    "(0,0\<triangleright>0)" \<Rightarrow> \<open>fail\<close>
    \<bar>_ \<Rightarrow> \<open>insert lspasl_d_der[OF P], auto\<close>\<close>,
simp?
)

text {* We restrict that the rule P can't be applied to
two syntactically identical ternary relational atoms. 
Note that we build communtativity in this rule application. *}

method try_lspasl_p = (
match premises in P[thin]:"(h1,h2\<triangleright>h0)" for h0 h1 h2 \<Rightarrow> 
  \<open>match premises in "(h1,h2\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
  \<bar>"(h2,h1\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
  \<bar>P'[thin]:"(h1,h2\<triangleright>?h3)" \<Rightarrow> \<open>insert lspasl_p_der[OF P P'], auto\<close>
  \<bar>P''[thin]:"(h2,h1\<triangleright>?h3)" \<Rightarrow> \<open>insert lspasl_p_der2[OF P P''], auto\<close>\<close>,
simp?
)

text {* We restrict that the rule C can't be applied to
two syntactically identical ternary relational atoms. 
Note that we build communtativity in this rule application. *}

method try_lspasl_c = (
match premises in P[thin]:"(h1,h2\<triangleright>h0)" for h0 h1 h2 \<Rightarrow> 
  \<open>match premises in "(h1,h2\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
  \<bar>"(h2,h1\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
  \<bar>P'[thin]:"(h1,?h3\<triangleright>h0)" \<Rightarrow> \<open>insert lspasl_c_der[OF P P'], auto\<close>
  \<bar>P''[thin]:"(?h3,h1\<triangleright>h0)" \<Rightarrow> \<open>insert lspasl_c_der2[OF P P''], auto\<close>
  \<bar>P'''[thin]:"(h2,?h3\<triangleright>h0)" \<Rightarrow> \<open>insert lspasl_c_der3[OF P P'''], auto\<close>
  \<bar>P''''[thin]:"(?h3,h2\<triangleright>h0)" \<Rightarrow> \<open>insert lspasl_c_der4[OF P P''''], auto\<close>\<close>,
simp?
)

text {* We restrict that *R only applies to a pair of 
a ternary relational and a formula once. 
Here, we need to first try simp to simplify situations such as
(h1,h2,h0) and not((A ** B) h3) and (h3 = h0). 
In the end, we try simp\_all to simplify all branches. 
A similar strategy is used in -*L. *}

method try_lspasl_starr = (
simp?,
match premises in P:"(h1,h2\<triangleright>h)" and P':"\<not>(A ** B) (h::'a::heap_sep_algebra)" for h1 h2 h A B \<Rightarrow> 
  \<open>match premises in "starr_applied h1 h2 h (A ** B)" \<Rightarrow> \<open>fail\<close> 
   \<bar>_ \<Rightarrow> \<open>insert lspasl_starr_der[OF P P'], auto\<close>\<close>,
simp_all?
)

method try_lspasl_starr2 = (
simp?,
match premises in P:"(h1,h2\<triangleright>h)" and P':"\<not>(A ** B) (h::'a::heap_sep_algebra)" for h1 h2 h A B \<Rightarrow> 
  \<open>match premises in "starr_applied h1 h2 h (A ** B)" \<Rightarrow> 
    \<open>match premises in "starr_applied h2 h1 h (A ** B)" \<Rightarrow> \<open>fail\<close>
     \<bar>_ \<Rightarrow> \<open>insert lspasl_starr_der2[OF P P'], auto\<close>\<close>     
   \<bar>_ \<Rightarrow> \<open>insert lspasl_starr_der[OF P P'], auto\<close>\<close>,
simp_all?
)

text {* We restrict that -*L only applies to a pair of 
a ternary relational and a formula once. *}

method try_lspasl_magicl = (
simp?,
match premises in P: "(h1,h\<triangleright>h2)" and P':"(A \<longrightarrow>* B) (h::'a::heap_sep_algebra)" for h1 h2 h A B \<Rightarrow> 
  \<open>match premises in "magicl_applied h1 h h2 (A \<longrightarrow>* B)" \<Rightarrow> \<open>fail\<close> 
   \<bar>_ \<Rightarrow> \<open>insert lspasl_magicl_der[OF P P'], auto\<close>\<close>,
simp_all?
)

text {* We build commutativity in the following rule applicaiton. *}

method try_lspasl_magicl2 = (
simp?,
((match premises in P: "(h1,h\<triangleright>h2)" and P':"(A \<longrightarrow>* B) (h::'a::heap_sep_algebra)" for h1 h2 h A B \<Rightarrow> 
  \<open>match premises in "magicl_applied h1 h h2 (A \<longrightarrow>* B)" \<Rightarrow> \<open>fail\<close> 
   \<bar>_ \<Rightarrow> \<open>insert lspasl_magicl_der[OF P P'], auto\<close>\<close>)
|(match premises in P'': "(h,h1\<triangleright>h2)" and P''':"(A \<longrightarrow>* B) (h::'a::heap_sep_algebra)" for h1 h2 h A B \<Rightarrow> 
  \<open>match premises in "magicl_applied h1 h h2 (A \<longrightarrow>* B)" \<Rightarrow> \<open>fail\<close> 
   \<bar>_ \<Rightarrow> \<open>insert lspasl_magicl_der2[OF P'' P'''], auto\<close>\<close>)),
simp_all?
)

text {* We restrict that the U rule is only applicable to a world h
when (h,0,h) is not in the premises. There are two cases:
(1) We pick a ternary relational atom (h1,h2,h0),
and check if (h1,0,h1) occurs in the premises, if not, 
apply U on h1. Otherwise, check other ternary relational atoms.
(2) We pick a labelled formula (A h), 
and check if (h,0,h) occurs in the premises, if not,
apply U on h. Otherwise, check other labelled formulae. *}

method try_lspasl_u_tern = (
match premises in 
  P:"(h1,h2\<triangleright>(h0::'a::heap_sep_algebra))" for h1 h2 h0 \<Rightarrow>
  \<open>match premises in 
    "(h1,0\<triangleright>h1)" \<Rightarrow> \<open>match premises in 
      "(h2,0\<triangleright>h2)" \<Rightarrow> \<open>match premises in 
        I1:"(h0,0\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
        \<bar>_ \<Rightarrow> \<open>insert lspasl_u_der[of h0]\<close>\<close>
      \<bar>_ \<Rightarrow> \<open>insert lspasl_u_der[of h2]\<close>\<close>
    \<bar>_ \<Rightarrow> \<open>insert lspasl_u_der[of h1]\<close>\<close>,
simp?
)

method try_lspasl_u_form = (
match premises in 
  P':"_ (h::'a::heap_sep_algebra)" for h \<Rightarrow>
  \<open>match premises in "(h,0\<triangleright>h)" \<Rightarrow> \<open>fail\<close>
   \<bar>"(0,0\<triangleright>0)" and "h = 0" \<Rightarrow> \<open>fail\<close>
   \<bar>"(0,0\<triangleright>0)" and "0 = h" \<Rightarrow> \<open>fail\<close>
   \<bar>_ \<Rightarrow> \<open>insert lspasl_u_der[of h]\<close>\<close>,
simp?
)

text {* We restrict that the E rule is only applicable to
(h1,h2,h0) when (h2,h1,h0) is not in the premises. *}

method try_lspasl_e = (
match premises in P:"(h1,h2\<triangleright>h0)" for h1 h2 h0 \<Rightarrow> 
  \<open>match premises in "(h2,h1\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
   \<bar>_ \<Rightarrow> \<open>insert lspasl_e_der[OF P], auto\<close>\<close>,
simp?
)

text {* We restrict that the A rule is only applicable to 
(h1,h2,h0) and (h3,h4,h1) when (h3,h,h0) and (h2,h4,h) 
or any commutative variants of the two 
do not occur in the premises, for some h. 
Additionally, we do not allow A to be applied to two identical 
ternary relational atoms. 
We further restrict that the leaves must not be 0, 
because otherwise this application does not gain anything. *}


method try_lspasl_a = (
match premises in "(h1,h2\<triangleright>h0)" for h0 h1 h2 \<Rightarrow> 
  \<open>match premises in 
    "(0,h2\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
   \<bar>"(h1,0\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
   \<bar>"(h1,h2\<triangleright>0)" \<Rightarrow> \<open>fail\<close>
   \<bar>P[thin]:"(h1,h2\<triangleright>h0)" \<Rightarrow> 
    \<open>match premises in
      P':"(h3,h4\<triangleright>h1)" for h3 h4 \<Rightarrow> \<open>match premises in
        "(0,h4\<triangleright>h1)" \<Rightarrow> \<open>fail\<close>
       \<bar>"(h3,0\<triangleright>h1)" \<Rightarrow> \<open>fail\<close>
       \<bar>"(_,h3\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
       \<bar>"(h3,_\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
       \<bar>"(h2,h4\<triangleright>_)" \<Rightarrow> \<open>fail\<close>
       \<bar>"(h4,h2\<triangleright>_)" \<Rightarrow> \<open>fail\<close>       
       \<bar>_ \<Rightarrow> \<open>insert P P', drule lspasl_a_der, auto\<close>\<close>\<close>\<close>,
simp?
)

method try_lspasl_a_full = (
match premises in "(h1,h2\<triangleright>h0)" for h0 h1 h2 \<Rightarrow> 
  \<open>match premises in 
    "(0,h2\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
   \<bar>"(h1,0\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
   \<bar>"(h1,h2\<triangleright>0)" \<Rightarrow> \<open>fail\<close>
   \<bar>P[thin]:"(h1,h2\<triangleright>h0)" \<Rightarrow> 
    \<open>match premises in
      P':"(h3,h4\<triangleright>h1)" for h3 h4 \<Rightarrow> \<open>match premises in
        "(0,h4\<triangleright>h1)" \<Rightarrow> \<open>fail\<close>
       \<bar>"(h3,0\<triangleright>h1)" \<Rightarrow> \<open>fail\<close>
       \<bar>"(h5,h3\<triangleright>h0)" for h5 \<Rightarrow> \<open>match premises in 
         "(h2,h4\<triangleright>h5)" \<Rightarrow> \<open>fail\<close>
        \<bar>"(h4,h2\<triangleright>h5)" \<Rightarrow> \<open>fail\<close>
        \<bar>_ \<Rightarrow> \<open>insert P P', drule lspasl_a_der, auto\<close>\<close>
       \<bar>"(h3,h5\<triangleright>h0)" for h5 \<Rightarrow> \<open>match premises in 
         "(h2,h4\<triangleright>h5)" \<Rightarrow> \<open>fail\<close>
        \<bar>"(h4,h2\<triangleright>h5)" \<Rightarrow> \<open>fail\<close>
        \<bar>_ \<Rightarrow> \<open>insert P P', drule lspasl_a_der, auto\<close>\<close>
       \<bar>"(h2,h4\<triangleright>h5)" for h5 \<Rightarrow> \<open>match premises in 
         "(h3,h5\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
        \<bar>"(h5,h3\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
        \<bar>_ \<Rightarrow> \<open>insert P P', drule lspasl_a_der, auto\<close>\<close>
       \<bar>"(h4,h2\<triangleright>h5)" for h5 \<Rightarrow> \<open>match premises in 
         "(h3,h5\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
        \<bar>"(h5,h3\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
        \<bar>_ \<Rightarrow> \<open>insert P P', drule lspasl_a_der, auto\<close>\<close>       
       \<bar>_ \<Rightarrow> \<open>insert P P', drule lspasl_a_der, auto\<close>\<close>\<close>\<close>,
simp?
)
 
text {* I don't have a good heuristics for CS right now. 
I simply forbid CS to be applied on the same pair twice. *}

(*
method try_lspasl_cs = (
match premises in P[thin]:"(h1,h2\<triangleright>h0)" for h0 h1 h2 \<Rightarrow> 
  \<open>match premises in "(h1,h2\<triangleright>h0)" \<Rightarrow> \<open>fail\<close> 
   \<bar>"(h2,h1\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
   \<bar>"(0,h0\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
   \<bar>"(h0,0\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
   \<bar>P':"(h3,h4\<triangleright>h0)" for h3 h4 \<Rightarrow> \<open>match premises in 
      "(h5,h6\<triangleright>h1)" and "(h7,h8\<triangleright>h2)" and "(h5,h7\<triangleright>h3)" and "(h6,h8\<triangleright>h4)" for h5 h6 h7 h8 \<Rightarrow> \<open>fail\<close>
     \<bar>"(i5,i6\<triangleright>h2)" and "(i7,i8\<triangleright>h1)" and "(i5,i7\<triangleright>h3)" and "(i6,i8\<triangleright>h4)" for i5 i6 i7 i8 \<Rightarrow> \<open>fail\<close>
     \<bar>"(j5,j6\<triangleright>h1)" and "(j7,j8\<triangleright>h2)" and "(j5,j7\<triangleright>h4)" and "(j6,j8\<triangleright>h3)" for j5 j6 j7 j8 \<Rightarrow> \<open>fail\<close>
     \<bar>"(k5,k6\<triangleright>h2)" and "(k7,k8\<triangleright>h1)" and "(k5,k7\<triangleright>h4)" and "(k6,k8\<triangleright>h3)" for k5 k6 k7 k8 \<Rightarrow> \<open>fail\<close>
     \<bar>_ \<Rightarrow> \<open>insert lspasl_cs_der[OF P P'], auto\<close>\<close>\<close>,
simp?
)
*)

method try_lspasl_cs = (
match premises in P[thin]:"(h1,h2\<triangleright>h0)" for h0 h1 h2 \<Rightarrow> 
  \<open>match P in "(0,h0\<triangleright>h0)" \<Rightarrow> \<open>fail\<close> 
   \<bar>"(h0,0\<triangleright>h0)" \<Rightarrow> \<open>fail\<close> 
   \<bar>_ \<Rightarrow> \<open>match premises in P':"(h3,h4\<triangleright>h0)" for h3 h4 \<Rightarrow> 
    \<open>match P' in "(h2,h1\<triangleright>h0)" \<Rightarrow> \<open>fail\<close> 
     \<bar>"(0,h0\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
     \<bar>"(h0,0\<triangleright>h0)" \<Rightarrow> \<open>fail\<close>
     \<bar>_ \<Rightarrow> \<open>insert lspasl_cs_der[OF P P'], auto\<close>\<close>\<close>\<close>,
simp?
)

text {* Note that we build commutativity in the following rule applicaiton. *}

method try_lspasl_starr_guided = (
simp?,
((match premises in P:"(h1,h2\<triangleright>h)" and P':"\<not>(A ** B) (h::'a::heap_sep_algebra)" for h1 h2 h A B \<Rightarrow> 
  \<open>match premises in "starr_applied h1 h2 h (A ** B)" \<Rightarrow> \<open>fail\<close>
   \<bar>"A h1" \<Rightarrow> \<open>insert lspasl_starr_der[OF P P'], auto\<close>
   \<bar>"B h2" \<Rightarrow> \<open>insert lspasl_starr_der[OF P P'], auto\<close>\<close>)
|(match premises in P:"(h1,h2\<triangleright>h)" and P':"\<not>(A ** B) (h::'a::heap_sep_algebra)" for h1 h2 h A B \<Rightarrow> 
  \<open>match premises in "starr_applied h2 h1 h (A ** B)" \<Rightarrow> \<open>fail\<close>
   \<bar>"A h2" \<Rightarrow> \<open>insert lspasl_starr_der2[OF P P'], auto\<close>
   \<bar>"B h1" \<Rightarrow> \<open>insert lspasl_starr_der2[OF P P'], auto\<close>\<close>)),
simp_all?
)

text {* Note that we build commutativity in the following rule applicaiton. *}

method try_lspasl_magicl_guided = (
simp?,
match premises in P: "(h1,h\<triangleright>h2)" and P':"(A \<longrightarrow>* B) (h::'a::heap_sep_algebra)" for h1 h2 h A B \<Rightarrow> 
  \<open>match premises in "magicl_applied h1 h h2 (A \<longrightarrow>* B)" \<Rightarrow> \<open>fail\<close> 
   \<bar>"A h1" \<Rightarrow> \<open>insert lspasl_magicl_der[OF P P'], auto\<close>
   \<bar>"\<not>(B h2)" \<Rightarrow> \<open>insert lspasl_magicl_der[OF P P'], auto\<close>\<close>
\<bar>P'': "(h,h1\<triangleright>h2)" and P''':"(A \<longrightarrow>* B) (h::'a::heap_sep_algebra)" for h1 h2 h A B \<Rightarrow> 
  \<open>match premises in "magicl_applied h1 h h2 (A \<longrightarrow>* B)" \<Rightarrow> \<open>fail\<close> 
   \<bar>"A h1" \<Rightarrow> \<open>insert lspasl_magicl_der2[OF P'' P'''], auto\<close>
   \<bar>"\<not>(B h2)" \<Rightarrow> \<open>insert lspasl_magicl_der2[OF P'' P'''], auto\<close>\<close>,
simp_all?
)

text {* The following rule deals with the meta-language universal quantifier. *}

method try_lsfasl_boxl = (
simp?,
match premises in P[thin]: "\<And>h. ?A (h::'a::heap_sep_algebra)" \<Rightarrow>
  \<open>insert P, drule meta_spec, auto\<close>,
auto? (* Change this line to simp? will raise type errors... *)
)

text {* In case the conclusion is not False, we normalise the goal as below. *}

method norm_goal = (
match conclusion in "False" \<Rightarrow> \<open>fail\<close>
\<bar>_ \<Rightarrow> \<open>rule ccontr\<close>,
simp?
)

text {* The tactic for separata. We first try to simplify the problem
with auto simp add: sep\_conj\_ac, which ought to solve many problems.
Then we apply the "true" invertible rules and structural rules 
which unify worlds as much as possible, followed by auto to simplify the goals. 
Then we apply *R and -*L and other structural rules.
The rule CS is only applied when nothing else is applicable. We try not
to use it. *}

text {* Preparation for the solver. *}

lemma sep_implE2: "(P ** (P \<longrightarrow>* Q)) h \<Longrightarrow> Q h"
using sep_conj_commuteI sep_conj_sep_impl2 by blast

lemma sep_implE3: "(A ** (P ** (P \<longrightarrow>* Q))) h \<Longrightarrow> (A ** Q) h"
using sep_conj_impl sep_implE2 by blast

lemma sep_implE4: "((P ** (P \<longrightarrow>* Q)) ** A) h \<Longrightarrow> (Q ** A) h"
using sep_conj_commuteI sep_implE3 by blast

method prep = ((auto simp add: sep_conj_ac)|norm_goal)+

text {* This part contains invertible rules. 
Apply as often as possible. *}

method invert = (
(try_lspasl_empl 
|try_lspasl_iu
|try_lspasl_d
|try_lspasl_eq     
|try_lspasl_p
|try_lspasl_c
|try_lspasl_starl
|try_lspasl_magicr  
|try_lspasl_starr_guided
|try_lspasl_magicl_guided)+,
auto?)

text {* This part contains structural rules. *}

method struct = (
try_lspasl_u_tern 
|try_lspasl_e
|try_lspasl_a)+

text {* This part contains *R and -*L rules. *}

method noninvert = (
try_lspasl_starr2 
|try_lspasl_magicl2)

text {* This part contains rules that are rarely used. *}

method rare = (
try_lspasl_u_form+ (* This rule is rarely used. *)
|try_lspasl_a_full (* Just in case we need more ternary relational atoms from associativity. *)
|try_lspasl_cs (* Cross-split adds too much complication. Try not to use it. *)
)

method separata =     
(prep
 |(invert
  |try_lsfasl_boxl         
  |struct  
  |noninvert   
 )+
 |rare
)+

end