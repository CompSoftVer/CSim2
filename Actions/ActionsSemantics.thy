(*
    Author:      David Sanan
    Maintainer:  David Sanan, sanan at ntu edu sg
    License:     LGPL
*)

(*  Title:      ActionSemantics.thy
    Author:     David Sanan, NTU

Copyright (C) 2015-2016 David Sanan 
Some rights reserved, NTU
This library is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as
published by the Free Software Foundation; either version 2.1 of the
License, or (at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
USA
*)
theory ActionsSemantics
imports Main "Sep_Prod_Instance" "Sep_Algebra.Sep_Heap_Instance"
        "Sep_Algebra.Sep_Tactics" "Separata.Separata"
begin 
section {* State definition *}
text {* 
The state is defined as a pair $(global variables\times local variables)$. Separation logic 
functions over the state will restrict it to be of type sep\_algebra*}
type_synonym ('a,'b) action_state= "('a \<times> 'b)"
type_synonym ('a,'b) transition = "(('a,'b) action_state \<times> ('a,'b) action_state)"

section{* Separation logic operations over the compound state *}

definition the_set :: "('a \<Rightarrow> bool) \<Rightarrow>
                     ('a set)"  (* ("\<lfloor> _ \<rfloor>"  [60] 89) *)
where
"the_set a \<equiv> {\<sigma>. a \<sigma>}" 

section{* Separation logic actions over transitions*}

definition after :: "(('a,'b) action_state \<Rightarrow>bool) \<Rightarrow> 
                     (('a, 'b) action_state \<Rightarrow>bool) \<Rightarrow> (('a, 'b) transition \<Rightarrow> bool)"
 ("_ \<unrhd> _"  [60,20] 89)
where
"a \<unrhd> b \<equiv> (\<lambda>(\<sigma>,\<sigma>'). (a \<sigma>) \<and> (b \<sigma>'))"

lemma afterD: "(a \<unrhd> b) (\<sigma>1,\<sigma>2) \<Longrightarrow> (a \<sigma>1) \<and> (b \<sigma>2)"
by (auto simp add: after_def)

definition satis :: "(('a, 'b) action_state \<Rightarrow>bool) \<Rightarrow>  
                     (('a, 'b) transition \<Rightarrow> bool)"  ("\<lceil> _ \<rceil>"  [60] 89)
where
"\<lceil> a \<rceil> \<equiv> (\<lambda>(\<sigma>,\<sigma>'). (\<sigma>=\<sigma>') \<and> (a \<sigma>))"

lemma satisD: "((\<lceil> a \<rceil>) (\<sigma>,\<sigma>')) = ((\<sigma>=\<sigma>') \<and> (a \<sigma>))"
by (simp add: satis_def)

lemma satisI: "\<sigma>=\<sigma>' \<Longrightarrow> a \<sigma> \<Longrightarrow> (\<lceil> a \<rceil>) (\<sigma>,\<sigma>')"
by (simp add: satisD)
                               
definition Emp :: "('a::sep_algebra, 'b::sep_algebra) transition \<Rightarrow> bool"
where
"Emp \<equiv> (\<lambda>(a,b). (sep_empty \<unrhd> sep_empty) (a,b))"

lemma Emp_iff_sep_empty:"Emp = sep_empty"
unfolding Emp_def zero_prod_def sep_empty_def after_def by auto

definition tran_True :: "('a::sep_algebra, 'b::sep_algebra) transition \<Rightarrow> bool"
where
"tran_True \<equiv> sep_true \<unrhd> sep_true"

lemma tran_True_true: "tran_True = sep_true"
unfolding tran_True_def sep_empty_def after_def by auto
                
definition tran_Id :: "('a::sep_algebra, 'b::sep_algebra) transition \<Rightarrow> bool"
where 
"tran_Id \<equiv> \<lceil> sep_true \<rceil>" 

lemma tran_Id_eq:"tran_Id (y',y'') = (y' = y'')"
       by (simp add: satis_def tran_Id_def)

lemma tran_Id_idem:"tran_Id y \<Longrightarrow> tran_Id (y + (\<sigma>',\<sigma>'))"
proof -
     assume a1:"tran_Id y"
     obtain y1 y2 where y_val:"y = (y1,y2)" 
       using surjective_pairing by blast     
     then have "y1=y2" using a1 y_val tran_Id_eq by blast     
     then have "y + (\<sigma>',\<sigma>') = ((y1 + \<sigma>'),(y1 + \<sigma>'))" 
       using y_val plus_prod_def by fastforce
     then show "tran_Id (y + (\<sigma>',\<sigma>'))" by (simp add: tran_Id_eq)        
qed

lemma sep_conj_train_Id:"G s \<Longrightarrow> (G\<and>*tran_Id) s"
by (metis sep_add_zero sep_conj_def sep_disj_zero tran_Id_eq zero_prod_def)

lemma sep_conj_train_True:"G s \<Longrightarrow> (G\<and>*tran_True) s"
proof -
  assume a1: "G s"
  have "\<forall>p. tran_True (p::('a \<times> 'b) \<times> _ \<times> _)"
    by (simp add: after_def tran_True_def)
  thus ?thesis
    using a1 by (meson pure_conj_sep_conj pure_split)
qed

definition Satis :: "(('a, 'b) transition \<Rightarrow> bool) \<Rightarrow>
                     (('a,'b) transition set)"  ("\<lfloor> _ \<rfloor>"  [60] 89)
where
"Satis a \<equiv> Collect a"



lemma dist_star_after:"\<forall>t. ((((p ** p') \<unrhd> (q ** q')) t) = (((p \<unrhd> q) ** (p' \<unrhd> q')) t))"
unfolding sep_conj_def after_def
apply (auto simp add:sep_disj_prod_def plus_prod_def)
by blast


lemma imp_after:"(\<forall>t. (p imp p') t) \<Longrightarrow> 
                 (\<forall>t. (q imp q') t) \<Longrightarrow> (\<forall>t. ((p \<unrhd> q) imp (p' \<unrhd> q')) t)"
unfolding after_def
by blast

lemma or_after1: "((p or p') \<unrhd> q) = ((p \<unrhd> q) or (p' \<unrhd> q))"
unfolding after_def
by blast

lemma satis_after: "(\<forall>t. (\<lceil> p \<rceil>) t) \<Longrightarrow> (\<forall>t. (p \<unrhd> p) t)"
unfolding after_def satis_def
by blast


lemma satis_id: "\<forall>t. (\<lceil> p \<rceil>) t \<longrightarrow> tran_Id t"
unfolding satis_def tran_Id_def
by auto

lemma or_after2: "(p \<unrhd> (q or q')) = ((p \<unrhd> q) or (p \<unrhd> q'))"
unfolding after_def
by blast 

lemma satis_emp: " (\<lceil> sep_empty \<rceil>) = Emp"
unfolding Emp_def sep_empty_def after_def  satis_def
by blast

lemma action_true: "a t \<Longrightarrow> tran_True t"
unfolding after_def tran_True_def
by blast                   

lemma or_sep: "(\<forall>t. (a\<^sub>1 imp a\<^sub>1') t) \<Longrightarrow> (\<forall>t. (a\<^sub>2 imp a\<^sub>2') t) \<Longrightarrow> (\<forall>t. ((a\<^sub>1 \<and>* a\<^sub>2) imp (a\<^sub>1' \<and>* a\<^sub>2')) t)"
unfolding sep_conj_def
by auto

lemma empty_neutral1: "(a \<and>* Emp) t \<Longrightarrow> a t"
by (simp_all add: Emp_iff_sep_empty)
(*unfolding  after_def sep_empty_def using Emp_iff_sep_empty
apply (simp only:Emp_iff_sep_empty)
by separata*)
(*unfolding Emp_def after_def sep_empty_def sep_conj_def
apply auto
by (metis sep_add_zero zero_prod_def)*)

lemma empty_neutral2: "a t \<Longrightarrow> (a \<and>* Emp) t"
by (simp_all add: Emp_iff_sep_empty)

(*unfolding  after_def sep_empty_def using Emp_iff_sep_empty
apply (simp only:Emp_iff_sep_empty)
by separata*)

(*proof -
  assume a1: "a t"
  have f2: "t ## (0, 0)"
    by (metis sep_disj_zero zero_prod_def)
  have "t = t + (0, 0)"
    by (metis sep_add_zero zero_prod_def)
  thus "\<exists>p pa. p ## pa \<and> t = p + pa \<and> a p \<and> (case pa of (p, pa) \<Rightarrow> case (p, pa) of (p, pa) \<Rightarrow> p = 0 \<and> pa = 0)"
    using f2 a1 by blast
qed*)

lemma empty_neutral': "(a \<and>* Emp) t = a t"
by (simp add: Emp_iff_sep_empty after_def)
(*by (fastforce intro: empty_neutral1 empty_neutral2)*)

lemma empty_neutral: "(a \<and>* Emp) = a"
by (auto simp add: empty_neutral')

lemma star_op_comm: "(a\<and>*a') = (a'\<and>*a)"
by separata
(*by (simp add: Separation_Algebra.sep.mult.commute)*)

lemma sep_conj_conj1:"((\<lambda>r. (Q r) \<and> (Q' r)) \<and>* P) h \<Longrightarrow> 
                     (((\<lambda>r. Q r)  \<and>* P)  and ((\<lambda>r. Q' r) \<and>* P)) (h::'a::heap_sep_algebra)"
by separata
(*using  Separation_Algebra.sep_algebra_class.sep_conj_conj by auto*)

lemma "(a ** sep_true) h \<Longrightarrow> (h,h'\<triangleright>h'') \<Longrightarrow> (a ** sep_true) h''"
by separata

lemma id_pair_comb: "((x,x),(y,y)\<triangleright>(z,z')) \<Longrightarrow> z = z'"
using disj_union_dist2 tern_rel_def tern_rel_def
by metis

lemma tern_pair: "(\<sigma>1, \<sigma>'\<triangleright> \<sigma>1') \<Longrightarrow> (\<sigma>2, \<sigma>''\<triangleright> \<sigma>2') \<Longrightarrow>
  ((\<sigma>1,\<sigma>2),(\<sigma>',\<sigma>'')\<triangleright>(\<sigma>1',\<sigma>2'))"
using disj_union_dist2 tern_rel_def
proof -
  assume a1: "(\<sigma>1, \<sigma>'\<triangleright> \<sigma>1')"
  assume "(\<sigma>2, \<sigma>''\<triangleright> \<sigma>2')"
  then have "((\<sigma>1,\<sigma>2),(\<sigma>',\<sigma>'')\<triangleright>(\<sigma>1',\<sigma>2'))"
    using a1 by (metis disj_union_dist)
  then show ?thesis
    by (simp add: tern_rel_def)
qed

lemma tern_dist1: "((\<sigma>1, \<sigma>'\<triangleright> \<sigma>1') \<and> (\<sigma>2, \<sigma>''\<triangleright> \<sigma>2')) \<Longrightarrow>
  ((\<sigma>1,\<sigma>2),(\<sigma>',\<sigma>'')\<triangleright>(\<sigma>1',\<sigma>2'))"
using disj_union_dist2 tern_rel_def
by (simp add: tern_pair)

method comb_du_pair = (
match premises in P:"(?h1, ?h'\<triangleright> ?h1') \<and> (?h2, ?h''\<triangleright> ?h2')" \<Rightarrow> 
  \<open>insert P, drule tern_dist1\<close>,
simp?
)

lemma 
  "(a \<and>* tran_Id) (\<sigma>1,\<sigma>2) \<Longrightarrow> 
   ((\<sigma>1,\<sigma>2),(\<sigma>',\<sigma>')\<triangleright>(\<sigma>1',\<sigma>2')) \<Longrightarrow>
   (a \<and>* tran_Id) (\<sigma>1',\<sigma>2')"
apply (simp add: tran_Id_def satis_def)
using id_pair_comb
apply separata
by separata

lemma conj_sep_id: 
assumes a1: "(a \<and>* tran_Id) (\<sigma>1,\<sigma>2)" 
assumes a2: "(\<sigma>1,\<sigma>'\<triangleright>\<sigma>1') \<and> (\<sigma>2,\<sigma>'\<triangleright>\<sigma>2')"
shows "(a \<and>* tran_Id) (\<sigma>1',\<sigma>2')"
proof -
  from a2 have "((\<sigma>1,\<sigma>2),(\<sigma>',\<sigma>')\<triangleright>(\<sigma>1',\<sigma>2'))" 
    by (metis (full_types) tern_dist1)
  then show ?thesis using a1 id_pair_comb
    apply (simp add: tran_Id_def satis_def)
    by separata
qed

(*
lemma conj_sep_id: "(a \<and>* tran_Id) (\<sigma>1,\<sigma>2) \<Longrightarrow> 
  (\<sigma>1 \<uplus>\<^sub>p \<sigma>') \<sigma>1' \<and> (\<sigma>2 \<uplus>\<^sub>p \<sigma>') \<sigma>2' \<Longrightarrow>
  (a \<and>* tran_Id) (\<sigma>1',\<sigma>2')"
unfolding sep_conj_def 
proof -
  assume a1:"\<exists>x y. x ## y \<and> (\<sigma>1, \<sigma>2) = x + y \<and> a x \<and> tran_Id y"
  then obtain x y where 
        unfold_pr:"x ## y \<and> 
         (\<sigma>1, \<sigma>2) = x + y \<and> 
         a x \<and> tran_Id y" by auto
  then have split_x_y:"(x \<uplus>\<^sub>p y) (\<sigma>1,\<sigma>2)" by (simp add: sep_split_def) 
  assume a2:"(\<sigma>1 \<uplus>\<^sub>p \<sigma>') \<sigma>1' \<and> (\<sigma>2 \<uplus>\<^sub>p \<sigma>') \<sigma>2'"
  then have "((\<sigma>1,\<sigma>2) \<uplus>\<^sub>p (\<sigma>',\<sigma>')) (\<sigma>1',\<sigma>2')"
   by (simp add: disj_union_dist1)
  then have new_split:"(x  \<uplus>\<^sub>p (y + (\<sigma>',\<sigma>'))) (\<sigma>1',\<sigma>2')" 
   using sep_split_assoc split_x_y by blast  
  have tran_id_y: "tran_Id (y + (\<sigma>',\<sigma>'))"    
  proof -
     obtain y1 y2 where y_val:"y = (y1,y2)" 
       using surjective_pairing by blast     
     then have "y1=y2" using unfold_pr y_val tran_Id_eq by blast     
     then have "y + (\<sigma>',\<sigma>') = ((y1 + \<sigma>'),(y1 + \<sigma>'))" 
       using y_val plus_prod_def by fastforce
     then show "tran_Id (y + (\<sigma>',\<sigma>'))" by (simp add: tran_Id_eq)       
   qed          
  thus "\<exists>x y. x ## y \<and> (\<sigma>1', \<sigma>2') = x + y \<and> a x \<and> tran_Id y"  
    using new_split sep_split_def unfold_pr by metis
qed
*)

section {* Stability *}

text{* 

 We define an assertion $p$ to be stable with regard an action $a$ if for each $(\sigma,\sigma')$,
$p\ \sigma$ and $a (\sigma,\sigma')$ then $p \sigma$

*}
(*definition Sta :: "(('a, 'b)action_state \<Rightarrow>bool)\<Rightarrow>
                   (('a::sep_algebra, 'b::sep_algebra) transition\<Rightarrow>bool) \<Rightarrow>bool"
where
"Sta p a \<equiv> (\<forall>\<sigma> \<sigma>'. 
            ((p \<sigma>) \<and> (a (\<sigma>,\<sigma>'))) \<longrightarrow> (p \<sigma>'))" *)
definition Sta :: "(('a, 'b)action_state \<Rightarrow>bool)\<Rightarrow>
                   (('a::heap_sep_algebra, 'b::heap_sep_algebra) transition\<Rightarrow>bool) \<Rightarrow>bool"
where
"Sta p a \<equiv> (\<forall>\<sigma> \<sigma>'. 
            ((p \<sigma>) \<and> (a (\<sigma>,\<sigma>'))) \<longrightarrow> (p \<sigma>'))"
text{* 
We prove the following lemmas:
*}

lemma "\<forall>a b. (q \<and>* (\<lambda>s. \<not> (p \<longrightarrow>* (\<lambda>s. \<not> r s)) s \<and> \<box> s)) (a, b) \<longrightarrow> r (a, b) \<Longrightarrow>
       r (a, b) \<Longrightarrow> p (a, b) \<Longrightarrow> q (aa, ba) \<Longrightarrow> (0,0\<triangleright>0) \<Longrightarrow> ((a, b),0\<triangleright>(a, b)) \<Longrightarrow> (0,(a, b)\<triangleright>(a, b)) \<Longrightarrow> r (aa, ba)"
proof -
  assume a0:"\<forall>a b. (q \<and>* (\<lambda>s. \<not> (p \<longrightarrow>* (\<lambda>s. \<not> r s)) s \<and> \<box> s)) (a, b) \<longrightarrow> r (a, b)" and
         a1: "r (a, b)" and 
         a2: "p (a, b)" and 
         a3: "q (aa, ba)" and
         a4:"(0,0\<triangleright>0)" and
         a5:"((a, b),0\<triangleright>(a, b))" and
         a6:" (0,(a, b)\<triangleright>(a, b))"
 then have "(q \<and>* (\<lambda>s. \<not> (p \<longrightarrow>* (\<lambda>s. \<not> r s)) s \<and> \<box> s)) (aa, ba) \<longrightarrow> r (aa, ba)"
 using a0 by auto 
 
 then show "r (aa, ba)"
 using a1 a2 a3 a4 a5 a6
 sorry
qed

lemma lem1: "r (a, b) \<Longrightarrow> p (a, b) \<Longrightarrow> q (aa, ba) \<Longrightarrow> 
(q \<and>* (not (p \<longrightarrow>* (not r)) and \<box>)) ((aa::'a::heap_sep_algebra), (ba::'b::heap_sep_algebra))"
by separata

lemma 
 "Sta r (p \<unrhd> q) = 
 (\<forall>\<sigma>. ((((p  \<longrightarrow>\<oplus> r) and sep_empty) \<and>* q) imp r) \<sigma>)"
unfolding Sta_def after_def satis_def 
apply auto
apply separata
by (auto simp add: lem1)

lemma 
"Sta r ((p \<unrhd> q)\<and>*tran_Id) \<Longrightarrow>
  (((p \<longrightarrow>\<oplus> r) \<and>* q) imp r) \<sigma>"
unfolding Sta_def after_def satis_def tran_Id_def 
proof auto
assume a1: "\<forall>a b aa ba. r (a, b) \<and> ((\<lambda>(\<sigma>, \<sigma>'). p \<sigma> \<and> q \<sigma>') \<and>* (\<lambda>(x, y). x = y)) ((a, b), aa, ba) \<longrightarrow> r (aa, ba)"
assume a2: " ((\<lambda>s. \<not> (p \<longrightarrow>* (\<lambda>s. \<not> r s)) s) \<and>* q) \<sigma>"
show "r \<sigma>" using a1 a2
  sorry
qed

lemma l1:
 "Sta r (p \<unrhd> q) = 
 (\<forall>\<sigma>. ((((p  \<longrightarrow>\<oplus> r) and sep_empty) \<and>* q) imp r) \<sigma>)"
unfolding Sta_def after_def satis_def sep_conj_def sep_impl_def
apply auto
  apply (simp add: sep_empty_def)
by (metis (no_types, lifting) sep_add_zero_sym sep_disj_commuteI sep_disj_zero sep_empty_zero zero_prod_def)



lemma l2:
 "(\<forall>\<sigma>.(((p \<longrightarrow>\<oplus> r) \<and>* q) imp r) \<sigma>) \<Longrightarrow> Sta r (p \<unrhd> q) "
unfolding Sta_def after_def satis_def sep_conj_def sep_impl_def
apply auto
by (metis (no_types, lifting) sep_add_disjI2 sep_add_zero_sym sep_disj_zero  zero_prod_def)

lemma l31:
"Sta r ((p \<unrhd> q)\<and>*tran_Id) \<Longrightarrow>
  (\<forall>\<sigma>.(((p \<longrightarrow>\<oplus> r) \<and>* q) imp r) \<sigma>)"
unfolding Sta_def after_def satis_def sep_conj_def sep_impl_def tran_Id_def sep_disj_prod_def
proof auto
  fix a b aa ba ab bb ac bc 
  assume a1: "q (ab, bb)"
  assume a2: "p (ac, bc)"
  assume a3: "aa ## ab"
  assume a4: "ba ## bb"
  assume a5: "aa ## ac"
  assume a6: "ba ## bc"
  assume a7: "\<forall>a b aa ba.
              r (a, b) \<and>
             (\<exists>ab bb ac bc ad.
                ab ## ad \<and>
                (\<exists>bd. bb ## bd \<and>
                      ac ## ad \<and>
                      bc ## bd \<and>
                      ((a, b), aa, ba) = ((ab, bb), ac, bc) + ((ad, bd), ad, bd) \<and>
                      p (ab, bb) \<and> q (ac, bc))) \<longrightarrow>
             r (aa, ba)"
  assume a8:"r ((aa, ba) + (ac, bc))"
  assume a9: "(a, b) = (aa, ba) + (ab, bb)"  
  then have aa:"(a,b) = (aa + ab, ba + bb)" by (simp add: plus_prod_def)   
  then have bb:"a = aa + ab \<and> b = ba + bb" by force  
  have "(aa+ac, ba+bc) = (aa,ba)+(ac,bc)" by (simp add: plus_prod_def)
  then have "r (aa+ac, ba+bc)" using a8 by auto
  from a8 have na8:"r (aa + ac, ba + bc)" by (simp add: plus_prod_def)
  then have sum:"((aa+ac,ba+bc),aa + ab, ba + bb) =  ((ac,bc),ab,bb) + ((aa,ba),aa,ba)"
    proof -
      have f1: "ba + bc = bc + ba"
        by (metis a6 sep_add_commute)
      have f2: "ba + bb = bb + ba"
        by (metis a4 sep_add_commute)
      have f3: "aa + ac = ac + aa"
        by (metis a5 sep_add_commute)
      have "aa + ab = ab + aa"
        by (meson a3 sep_add_commute)
      thus ?thesis
        using f3 f2 f1 by (simp add: plus_prod_def)
    qed
  have "\<forall>f fa. \<not>f ## fa \<or> fa ## f"
    using sep_disj_commuteI by blast 
  then have "r (aa + ab, ba + bb)"
    using na8 a7 a6 a5 a4 a3 a2 a1 sum by metis
  thus "r ((aa, ba) + (ab, bb))"
    by (simp add: `r (aa + ab, ba + bb)` plus_prod_def sep_add_commute)      
   
qed

lemma l32:
  "(\<forall>\<sigma>.(((p \<longrightarrow>\<oplus> r) \<and>* q) imp r) \<sigma>) \<Longrightarrow>
     Sta r ((p \<unrhd> q)\<and>*tran_Id)"
unfolding Sta_def after_def satis_def sep_conj_def sep_impl_def tran_Id_def
proof (auto) 
  fix a b aa ba ab bb ac bc ad bd 
  assume a1: "p (ab, bb)"
  assume a2: "((ab, bb), ac, bc) ## ((ad, bd), ad, bd)"
  assume a3: "((a, b), aa, ba) = ((ab, bb), ac, bc) + ((ad, bd), ad, bd)"
  assume a4: "q (ac, bc)"
  assume a5: "\<forall>a b. 
             (\<exists>aa ba ab bb. (aa, ba) ## (ab, bb) \<and> 
                            (a, b) = (aa, ba) + (ab, bb) \<and> 
                            (\<exists>a b. (aa, ba) ## (a, b) \<and> 
                                   p (a, b) \<and> r ((aa, ba) + (a, b))) \<and> 
                             q (ab, bb)) \<longrightarrow> 
              r (a, b)"
  assume a6: "r (a, b)"
  have f7: "\<forall>p pa. \<not> (p::('a \<Rightarrow> 'b option) \<times> ('a \<Rightarrow> 'b option)) ## pa \<or> pa ## p"
    using sep_disj_commuteI by blast
  have "(a, b) = (ab, bb) + (ad, bd) \<and> 
        (ab, bb) ## (ad, bd) \<and> (ac, bc) ## (ad, bd) \<and> 
        (aa, ba) = (ac, bc) + (ad, bd)"
    using a3 a2 dis_sep by blast
  thus "r (aa, ba)"
    using f7 a6 a5 a4 a1 by (metis sep_add_commute sep_disj_commuteI)
qed

lemma l3:
 "Sta r ((p \<unrhd> q)\<and>*tran_Id) = 
  (\<forall>\<sigma>.(((p \<longrightarrow>\<oplus> r) \<and>* q) imp r) \<sigma>)"
using l31 l32 by blast

section {* Fence *}
definition Fence::"(('a::heap_sep_algebra, 'b::heap_sep_algebra) action_state \<Rightarrow>bool) \<Rightarrow>  
                     (('a, 'b) transition \<Rightarrow> bool) \<Rightarrow> bool"  ("_ \<bowtie> _"  [60] 89)
where
"I  \<bowtie> a \<equiv> \<forall>\<sigma>1 \<sigma>2. (\<lceil> I \<rceil> imp a)(\<sigma>1,\<sigma>2) \<and> (a imp (I \<unrhd> I))(\<sigma>1,\<sigma>2) \<and> (precise I)
"
lemma fenceD: "(I  \<bowtie> a) \<Longrightarrow> (\<sigma>1,\<sigma>2)=(\<sigma>1,\<sigma>2) \<Longrightarrow> (\<lceil> I \<rceil> imp a)(\<sigma>1,\<sigma>2) \<and> (a imp (I \<unrhd> I))(\<sigma>1,\<sigma>2) \<and> (precise I)"
using Fence_def by (metis (no_types))

lemma fence1: "precise I \<Longrightarrow> I  \<bowtie> \<lceil>I\<rceil>"
by (simp add: Fence_def after_def satis_def)

lemma fence2:"precise I \<Longrightarrow> I  \<bowtie> (I \<unrhd> I)"
by (simp add: Fence_def after_def satis_def)

lemma fence3: "I  \<bowtie> a \<Longrightarrow> I  \<bowtie> a' \<Longrightarrow> I  \<bowtie> (a or a')"
by (simp add: Fence_def)

lemma fence41: " I  \<bowtie> a \<Longrightarrow> I'  \<bowtie> a' \<Longrightarrow>precise (I \<and>* I')"
by (simp add: Fence_def precise_sep_conj)

lemma fence42: 
assumes a1: " I  \<bowtie> a" and
        a2: "I' \<bowtie> a'" 
 shows  "\<forall>\<sigma>1 \<sigma>2. ((a \<and>* a') imp ((I \<and>* I') \<unrhd> (I \<and>* I'))) (\<sigma>1,\<sigma>2)"
proof  (clarsimp)
  fix aa b aaa ba
  have a1e: "\<forall>\<sigma>1 \<sigma>2. (\<lceil> I \<rceil> imp a)(\<sigma>1,\<sigma>2) \<and> (a imp (I \<unrhd> I))(\<sigma>1,\<sigma>2) \<and> (precise I)"
    using a1 by (simp add: Fence_def) 
  have a2e: "\<forall>\<sigma>1 \<sigma>2. (\<lceil> I' \<rceil> imp a')(\<sigma>1,\<sigma>2) \<and> (a' imp (I' \<unrhd> I'))(\<sigma>1,\<sigma>2) \<and> (precise I')"
    using a2 by (simp add: Fence_def)
  assume "(a \<and>* a') ((aa,b), (aaa,ba))"
  then obtain x y where sep_conji:"x ## y \<and> (((aa,b), (aaa,ba)) = x + y) \<and> a x \<and> a' y" 
    using sep_conjD by metis
  then obtain x1 x2 y1 y2 where yv: "x=(x1,x2) \<and> y = (y1,y2)" using surjective_pairing by blast 
  then have hpi: "(a imp (I \<unrhd> I)) (x1,x2)" using a1e sep_conji by blast
  then have hpi': "(a' imp (I' \<unrhd> I')) (y1,y2)" using a2e sep_conji yv by blast 
  thus "((I \<and>* I') \<unrhd> (I \<and>* I')) ((aa,b), (aaa,ba))" 
    using hpi' hpi sep_conji
    by (metis (no_types) dist_star_after sep_conjI yv) 
qed

lemma fence43: 
assumes a1: " I  \<bowtie> a" and
        a2: "I' \<bowtie> a'" 
shows "\<forall>\<sigma>1 \<sigma>2.(\<lceil> (I \<and>* I') \<rceil> imp (a \<and>* a'))(\<sigma>1,\<sigma>2)"
proof  (clarsimp)
  fix aa b aaa ba
  have a1e: "\<forall>\<sigma>1 \<sigma>2. (\<lceil> I \<rceil> imp a)(\<sigma>1,\<sigma>2) \<and> (a imp (I \<unrhd> I))(\<sigma>1,\<sigma>2) \<and> (precise I)"
    using a1 by (simp add: Fence_def) 
  have a2e: "\<forall>\<sigma>1 \<sigma>2. (\<lceil> I' \<rceil> imp a')(\<sigma>1,\<sigma>2) \<and> (a' imp (I' \<unrhd> I'))(\<sigma>1,\<sigma>2) \<and> (precise I')"
    using a2 by (simp add: Fence_def)
  assume ass1: "(\<lceil> (I \<and>* I') \<rceil>) ((aa, b), aaa, ba)"
  then obtain x y where pair_split:"(x,y) = ((aa, b), aaa, ba)"  
    using surjective_pairing by blast
  then have ass1split: "(\<lceil> (I \<and>* I') \<rceil>) (x,y)" using ass1 by auto
  then have satis_I:"x = y \<and> (I \<and>* I') x" using satisD[of "(I \<and>* I')" x y]
    by fastforce
  then obtain x1 y1 where 
  sep_conji:"x1 ## y1 \<and> (x = x1 + y1) \<and> I x1 \<and> I' y1" 
    using sep_conjD by metis
  then have "(x,y) = (x1 + y1, x1 + y1)" using satis_I by blast 
  then have xy_add:"(x,y) = (x1,x1)+(y1,y1)" by (simp add: plus_prod_def)
  have xy_disj:"(x1,x1)##(y1,y1)" using sep_conji by (simp add: sep_disj_prod_def)
  have "(\<lceil> I \<rceil>) (x1,x1) \<and> (\<lceil> I' \<rceil>) (y1,y1)"  
    by (simp add: satisI sep_conji)
  then have "a (x1,x1) \<and> a' (y1,y1)" using a1e a2e by blast  
  thus "(a \<and>* a') ((aa, b), aaa, ba)" 
   using  xy_add xy_disj sep_conj_def pair_split by metis
qed

lemma fence4: " I  \<bowtie> a \<Longrightarrow> I'  \<bowtie> a' \<Longrightarrow> (I \<and>* I')  \<bowtie> (a \<and>* a')"
proof -
  assume a1:"I  \<bowtie> a"
  assume a2: "I'  \<bowtie> a'"  
  have f1: "\<And>u v. (\<forall>a1 a2. u a1 a2) \<and> (\<forall>a1 a2. v a1 a2) \<Longrightarrow>  \<forall>a1 a2. u a1 a2 \<and> v a1 a2"
   by auto  
  have "precise (I \<and>* I')" using a1 a2 fence41 by blast
  moreover have "\<forall>\<sigma>1 \<sigma>2. ((a \<and>* a') imp ((I \<and>* I') \<unrhd> (I \<and>* I'))) (\<sigma>1,\<sigma>2)"
    using a1 a2 fence42 by blast
  moreover have "\<forall>\<sigma>1 \<sigma>2.(\<lceil> (I \<and>* I') \<rceil> imp (a \<and>* a'))(\<sigma>1,\<sigma>2)"
    using a1 a2 fence43 by blast
  ultimately show "(I \<and>* I')  \<bowtie> (a \<and>* a')" using f1
  by (simp add: Fence_def)
qed


lemma "(\<exists>! x. P x) \<Longrightarrow> (P x \<Longrightarrow> (\<And>y. P y \<Longrightarrow> y = x))"
by metis

lemma "P x \<Longrightarrow> (\<And>y. P y \<Longrightarrow> y = x) \<Longrightarrow> (\<exists>! x. P x) "
by auto
  
lemma sub_state_fence_unique:"\<sigma>11 \<preceq> \<sigma> \<and> \<sigma>1 \<preceq> \<sigma> \<and> a (\<sigma>11,\<sigma>12) \<and> I \<sigma>1 \<and> I  \<bowtie> a \<Longrightarrow> \<sigma>1=\<sigma>11"
unfolding Fence_def
proof -
 assume a1:"\<sigma>11 \<preceq> \<sigma> \<and> \<sigma>1 \<preceq> \<sigma> \<and> a (\<sigma>11, \<sigma>12) \<and> I \<sigma>1 \<and>
          (\<forall>\<sigma>1 \<sigma>2.
            ((\<lceil> I \<rceil>) (\<sigma>1, \<sigma>2) \<longrightarrow> a (\<sigma>1, \<sigma>2)) \<and>
            (a (\<sigma>1, \<sigma>2) \<longrightarrow> (I \<unrhd> I) (\<sigma>1, \<sigma>2)) \<and> 
            precise I)"
 then have "precise I" by auto
 then have "(I \<unrhd> I) (\<sigma>11, \<sigma>12)" using a1 by fastforce
 then have "I \<sigma>11" 
   using  surjective_pairing by (simp add: after_def)
 thus "\<sigma>1=\<sigma>11" using a1 precise_def by metis
qed

lemma fence_tran_exists:
  "\<sigma>1##\<sigma>2 \<Longrightarrow> (a \<and>* a') (\<sigma>1+\<sigma>2,\<sigma>') \<Longrightarrow> I \<sigma>1 \<and> I  \<bowtie> a \<Longrightarrow>    
   (\<exists>\<sigma>1' \<sigma>2'.((\<sigma>1', \<sigma>2' \<triangleright> \<sigma>') \<and> a (\<sigma>1,\<sigma>1') \<and> a'(\<sigma>2,\<sigma>2')))"
proof -
  assume a1:"\<sigma>1##\<sigma>2" and
         a2: "(a \<and>* a') (\<sigma>1+\<sigma>2,\<sigma>')" and
         a3: "I \<sigma>1 \<and> I  \<bowtie> a"  
  obtain \<sigma>11 \<sigma>12 \<sigma>'1 \<sigma>'2   
  where sep_split:"((\<sigma>11,\<sigma>'1)+(\<sigma>12,\<sigma>'2)) = (\<sigma>1+\<sigma>2,\<sigma>') \<and> 
         (\<sigma>11,\<sigma>'1)##(\<sigma>12,\<sigma>'2) \<and> a (\<sigma>11,\<sigma>'1) \<and> a'(\<sigma>12,\<sigma>'2) "
  using a2
    by (metis sep_conjE surjective_pairing)  
  then have split_sigma12:"\<sigma>11+\<sigma>12 = \<sigma>1+\<sigma>2 \<and> \<sigma>11##\<sigma>12" 
    by (metis (no_types) dis_sep) 
  then have "\<sigma>11 \<preceq> \<sigma>1+\<sigma>2 \<and> \<sigma>1 \<preceq> \<sigma>1+\<sigma>2" 
    using sep_substate_def sep_split a1 by fastforce
  then have "\<sigma>11=\<sigma>1" 
    using sep_split a3 sub_state_fence_unique by blast
  then have "\<sigma>12 = \<sigma>2"
    by (metis (no_types) split_sigma12 a1 sep_add_cancelD sep_add_commute sep_disj_commute)    
  then have "(\<sigma>'1, \<sigma>'2\<triangleright> \<sigma>') \<and> a (\<sigma>1,\<sigma>'1) \<and> a'(\<sigma>2,\<sigma>'2)"
    by (metis (no_types) `\<sigma>11 = \<sigma>1` dis_sep sep_split tern_rel_def)  
  thus "\<exists>\<sigma>1' \<sigma>2'.(\<sigma>1', \<sigma>2'\<triangleright> \<sigma>') \<and> a (\<sigma>1,\<sigma>1') \<and> a'(\<sigma>2,\<sigma>2')"
    by blast
qed  

lemma fence_tran_exists1:
  "\<sigma>1##\<sigma>2 \<Longrightarrow> (a \<and>* a') (\<sigma>1+\<sigma>2,\<sigma>') \<Longrightarrow> I \<sigma>1 \<and> I  \<bowtie> a \<Longrightarrow>    
   \<exists>\<sigma>1' \<sigma>2'.(\<sigma>1', \<sigma>2'\<triangleright> \<sigma>')"
proof -
  assume a1:"\<sigma>1##\<sigma>2" and
         a2: "(a \<and>* a') (\<sigma>1+\<sigma>2,\<sigma>')" and
         a3: "I \<sigma>1 \<and> I  \<bowtie> a"  
  obtain \<sigma>11 \<sigma>12 \<sigma>'1 \<sigma>'2   
  where sep_split:"((\<sigma>11,\<sigma>'1)+(\<sigma>12,\<sigma>'2)) = (\<sigma>1+\<sigma>2,\<sigma>') \<and> 
         (\<sigma>11,\<sigma>'1)##(\<sigma>12,\<sigma>'2) \<and> a (\<sigma>11,\<sigma>'1) \<and> a'(\<sigma>12,\<sigma>'2) "
  using a2
    by (metis sep_conjE surjective_pairing)  
  then have split_sigma12:"\<sigma>11+\<sigma>12 = \<sigma>1+\<sigma>2 \<and> \<sigma>11##\<sigma>12" 
    by (metis (no_types) dis_sep) 
  then have "\<sigma>11 \<preceq> \<sigma>1+\<sigma>2 \<and> \<sigma>1 \<preceq> \<sigma>1+\<sigma>2" 
    using sep_substate_def sep_split a1 by fastforce
  then have "\<sigma>11=\<sigma>1" 
    using sep_split a3 sub_state_fence_unique by blast
  then have "\<sigma>12 = \<sigma>2"
    by (metis (no_types) split_sigma12 a1 sep_add_cancelD sep_add_commute sep_disj_commute)    
  then have "(\<sigma>'1, \<sigma>'2\<triangleright> \<sigma>') \<and> a (\<sigma>1,\<sigma>'1) \<and> a'(\<sigma>2,\<sigma>'2)"
    by (metis (no_types) `\<sigma>11 = \<sigma>1` dis_sep sep_split tern_rel_def)  
  thus "\<exists>\<sigma>1' \<sigma>2'.(\<sigma>1',\<sigma>2'\<triangleright> \<sigma>')"
    by blast
qed  



lemma fence_tran_unique:
  "(\<sigma>1 ## \<sigma>2) \<Longrightarrow> (a \<and>* a') (\<sigma>1+\<sigma>2,\<sigma>') \<Longrightarrow> I \<sigma>1 \<and> I  \<bowtie> a \<Longrightarrow>    
   (\<exists>!\<sigma>1'. \<exists>!\<sigma>2'. ((\<sigma>1', \<sigma>2' \<triangleright> \<sigma>') \<and> a (\<sigma>1,\<sigma>1') \<and> a'(\<sigma>2,\<sigma>2')))"     
  proof - 
  assume a1:"\<sigma>1##\<sigma>2" and
     a2: "(a \<and>* a') (\<sigma>1+\<sigma>2,\<sigma>')" 
  then obtain \<sigma>11 \<sigma>12 \<sigma>'1 \<sigma>'2   
  where sep_split:"((\<sigma>11,\<sigma>'1)+(\<sigma>12,\<sigma>'2)) = (\<sigma>1+\<sigma>2,\<sigma>') \<and> 
         (\<sigma>11,\<sigma>'1)##(\<sigma>12,\<sigma>'2) \<and> a (\<sigma>11,\<sigma>'1) \<and> a'(\<sigma>12,\<sigma>'2) "
    by (metis sep_conjE surjective_pairing)
  assume   a3: "I \<sigma>1 \<and> I  \<bowtie> a"  
  then 
  obtain \<sigma>1' \<sigma>2' where exists:"(\<sigma>1', \<sigma>2' \<triangleright> \<sigma>') \<and> a (\<sigma>1,\<sigma>1') \<and> a'(\<sigma>2,\<sigma>2')"
    using a1 a2 fence_tran_exists by blast
  then have k1:"(\<sigma>1' , \<sigma>2'\<triangleright> \<sigma>')" by (simp add: tern_rel_def)   
  show "\<exists>!\<sigma>1'. \<exists>!\<sigma>2'. ((\<sigma>1', \<sigma>2' \<triangleright> \<sigma>') \<and> a (\<sigma>1,\<sigma>1') \<and> a'(\<sigma>2,\<sigma>2'))" 
  proof (rule+)
         let ?\<sigma>1' = \<sigma>1'
         let ?\<sigma>2'2 = \<sigma>2'
         show "(?\<sigma>1', ?\<sigma>2'2\<triangleright> \<sigma>')" using k1 by blast
     next
         show "a (\<sigma>1, \<sigma>1') \<and> a' (\<sigma>2, \<sigma>2')" using exists by blast
     next 
         fix \<sigma>2'a
         assume a11:"(\<sigma>1' , \<sigma>2'a\<triangleright> \<sigma>') \<and> a (\<sigma>1, \<sigma>1') \<and> a' (\<sigma>2, \<sigma>2'a)"
         then have "\<exists>!\<sigma>2'.(\<sigma>1' , \<sigma>2'\<triangleright> \<sigma>')" 
           using unique_subheap k1 by blast 
         then show" \<sigma>2'a = \<sigma>2'" using a11 k1 by auto          
     next
         fix \<sigma>1'a
         have f1:"\<And>I a \<sigma>1 \<sigma>1'. I \<bowtie> a \<Longrightarrow>  a (\<sigma>1, \<sigma>1') \<Longrightarrow> I \<sigma>1 \<and> I \<sigma>1'"
           using Fence_def afterD by metis
         assume "\<exists>!\<sigma>2'. (\<sigma>1'a, \<sigma>2'\<triangleright> \<sigma>') \<and> a (\<sigma>1, \<sigma>1'a) \<and> a' (\<sigma>2, \<sigma>2')"
         then obtain \<sigma>2'1 where a12:"(\<sigma>1'a, \<sigma>2'1\<triangleright> \<sigma>') \<and> a (\<sigma>1, \<sigma>1'a) \<and> a' (\<sigma>2, \<sigma>2'1)"
           by auto
         then have prec1:"I \<sigma>1'a" using  a3 f1 by blast
         then have prec2:"I \<sigma>1'" using exists a3 f1 by blast
         have prec:"precise I" using a3 Fence_def
           by (simp add: Fence_def)
         have "\<sigma>1' \<preceq> \<sigma>' \<and> \<sigma>1'a \<preceq> \<sigma>'" 
           using sep_split_substate exists a12 by blast                 
         then show  "\<sigma>1'a = \<sigma>1'" 
             using precise_def  prec1 prec2 prec
             by (metis (no_types))             
  qed
qed

corollary frame_property_a_star_id: 
  "\<sigma>1 ## \<sigma>2 \<and> (a \<and>* tran_Id) (\<sigma>1+\<sigma>2,\<sigma>') \<Longrightarrow> I \<sigma>1 \<and> I  \<bowtie> a \<Longrightarrow>
   \<exists>\<sigma>1'.(\<sigma>1', \<sigma>2\<triangleright> \<sigma>') \<and> (\<sigma>1,\<sigma>1') \<in>\<lfloor>a\<rfloor>" 
  proof -  
   assume a1:"\<sigma>1 ## \<sigma>2 \<and> (a \<and>* tran_Id) (\<sigma>1+\<sigma>2,\<sigma>')" and          
          a:" I \<sigma>1 \<and> I  \<bowtie> a"   
   then 
   have "\<exists>!\<sigma>1'. \<exists>! \<sigma>2'. (\<sigma>1', \<sigma>2'\<triangleright> \<sigma>') \<and> a (\<sigma>1, \<sigma>1') \<and> tran_Id (\<sigma>2, \<sigma>2')"
     using fence_tran_unique[of \<sigma>1 \<sigma>2 a tran_Id \<sigma>' I] a1 by fast
   then obtain \<sigma>1' \<sigma>2' where res:"(\<sigma>1', \<sigma>2'\<triangleright> \<sigma>') \<and> a (\<sigma>1, \<sigma>1') \<and> tran_Id (\<sigma>2, \<sigma>2')" by auto
   then have "\<sigma>2=\<sigma>2'" using tran_Id_def satisD by metis  
   then show "\<exists>\<sigma>1'.(\<sigma>1', \<sigma>2\<triangleright> \<sigma>') \<and> (\<sigma>1,\<sigma>1') \<in>\<lfloor>a\<rfloor>" using Satis_def res  mem_Collect_eq 
     by (metis (no_types))   
qed

lemma sta_fence: 
  "Sta p a \<and> Sta p' a' \<and> (\<forall>\<sigma>. (p imp I) \<sigma>)
 \<and> I  \<bowtie> a \<Longrightarrow> Sta (p \<and>* p') (a \<and>* a') "
  unfolding Sta_def
  proof -
    assume a1:"(\<forall>\<sigma> \<sigma>'. p \<sigma> \<and> a (\<sigma>, \<sigma>') \<longrightarrow> p \<sigma>') \<and>
            (\<forall>\<sigma> \<sigma>'. p' \<sigma> \<and> a' (\<sigma>, \<sigma>') \<longrightarrow> p' \<sigma>') \<and> 
            (\<forall>\<sigma>. p \<sigma> \<longrightarrow> I \<sigma>) \<and> I \<bowtie> a"
    show "\<forall>\<sigma> \<sigma>'. (p \<and>* p') \<sigma> \<and> (a \<and>* a') (\<sigma>, \<sigma>') \<longrightarrow> (p \<and>* p') \<sigma>'"
    proof (rule+)
     fix \<sigma> \<sigma>'
     assume a2:"(p \<and>* p') \<sigma> \<and> (a \<and>* a') (\<sigma>, \<sigma>')"
     then obtain \<sigma>1 \<sigma>2  where split_p:"\<sigma>=\<sigma>1 + \<sigma>2 \<and> \<sigma>1##\<sigma>2 \<and> p \<sigma>1 \<and> p' \<sigma>2"
       using sep_conjD by blast
     then have split1: " \<sigma>1##\<sigma>2" by auto
     then have sig_sum:"(a \<and>* a') (\<sigma>1 + \<sigma>2,\<sigma>')" using split_p a2 by auto
     then have "I \<sigma>1 \<and> I \<bowtie> a" using a1 split_p by blast
     then have "\<exists>! \<sigma>1'. \<exists>! \<sigma>2'. (\<sigma>1', \<sigma>2'\<triangleright> \<sigma>') \<and> a (\<sigma>1,\<sigma>1') \<and> a'(\<sigma>2,\<sigma>2')"
        using  split1  sig_sum fence_tran_unique[of \<sigma>1 \<sigma>2 a a' \<sigma>' I]  
        by fast
     then show "(p \<and>* p') \<sigma>'"
      by (metis (no_types) a1 sep_conjI tern_rel_def split_p)
   qed
qed

 lemma fence_G_id: 
  assumes a0:"(I  \<bowtie> G)" and
          a1:"G (s,y)" 
  shows "G (s,s)"
proof -  
  have "case (s, y) of (p, pa) \<Rightarrow> I p \<and> I pa"     
    using a0 a1 
    unfolding Fence_def satis_def after_def 
    by presburger
  hence "case (s, s) of (p, pa) \<Rightarrow> p = pa \<and> I p"
    by fastforce
  thus ?thesis
    using a0 unfolding Fence_def satis_def after_def by presburger
qed 

lemma fence_I_id: 
  assumes a0:"(I  \<bowtie> G)" and
          a1:"I s" 
  shows "G (s,s)"
using a0 a1 unfolding Fence_def satis_def after_def by blast
 

lemma fence_I_id1:
  assumes a0:"(I  \<bowtie> G)" and
          a1:"\<forall>s t. (p imp I) (s,t)" and
          a2:"p s \<and> s=(s1,s2)"
  shows "G (s,s)"
using a0 a1 a2 fence_I_id by blast

lemma tran_True:"tran_True t"
unfolding tran_True_def after_def by auto

(* declare [[show_types]]
  declare [[show_sorts]]
  declare [[show_consts]] *)
lemma fence_p_I_G:
  assumes a0:"(\<forall>s t. (p imp (I\<and>*sep_true)) (s,t))" and
          a1:"(I \<bowtie> G)" and
          a2: "p s"
  shows "(G\<and>*tran_True) (s,s)"
proof-
  obtain sl sg where s:"s=(sl,sg)" using a2 by (meson surj_pair) 
  then have I_true:"(I\<and>*sep_true) s" using a0 a2 by fastforce
  then obtain s\<^sub>1 s\<^sub>2 where sep: "s\<^sub>1 ## s\<^sub>2 \<and> s = s\<^sub>1 + s\<^sub>2 \<and> I s\<^sub>1 \<and> sep_true s\<^sub>2"
    using sep_conjD by blast
  then obtain sl\<^sub>1 sl\<^sub>2 sg\<^sub>1 sg\<^sub>2 where rel:"sl=sl\<^sub>1+sl\<^sub>2 \<and> sg = sg\<^sub>1 + sg\<^sub>2 \<and> s\<^sub>1=(sl\<^sub>1,sg\<^sub>1) \<and> s\<^sub>2=(sl\<^sub>2,sg\<^sub>2)"
    using s by (metis Pair_inject plus_prod_def surjective_pairing)    
  then have "G ((sl\<^sub>1,sg\<^sub>1),(sl\<^sub>1,sg\<^sub>1))"
    using a1 sep fence_I_id by blast  
  then have "G (s\<^sub>1, s\<^sub>1)" using rel by blast
  then have "(G\<and>*tran_Id)(s\<^sub>1, s\<^sub>1)" using sep_conj_train_Id by blast
  then have G:"(G\<and>*tran_Id)(s,s)" using s sep conj_sep_id unfolding tern_rel_def
    by fastforce
  then have "\<forall>s. tran_Id s \<longrightarrow> tran_True s" using tran_True by blast   
  thus ?thesis  using G sep_conj_commute sep_conj_impl1 by (metis (no_types))    
qed                                                                             


end
