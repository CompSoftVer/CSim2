(*
    Author:      David Sanan
    Maintainer:  David Sanan, sanan at ntu edu sg
    License:     LGPL 
*)

(*  Title:      LocalRG_HoareDef.thy
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
theory LocalRG_HoareDef           
imports "ParComputation" "EmbSimpl.HoarePartialProps" "HOL-Library.Countable"
begin
section \<open>Validity  of Correctness Formulas\<close>

subsection \<open>Aux\<close>

lemmas step_ce_induct = step_ce.induct [split_format (complete), case_names
c_step e_step, induct set]

lemmas step_ce_induct1 = step_ce.induct [ case_names
c_step e_step, induct set]

thm step_ce_induct step_ce_induct1

lemma eq_toParState:"toParState i s = toParState i t \<Longrightarrow>
       s = t"
  apply (auto simp add: toParState_def Let_def split_beta)
  using add.left_commute add_left_imp_eq append_eq_append_conv append_take_drop_id length_Cons 
           length_append length_drop list.inject plus_1_eq_Suc prod_eq_iff
  by smt

lemma eq_toSeqState:"i<length sls \<Longrightarrow> i<length tls \<Longrightarrow> 
       toSeqState i (sg,sls) = toSeqState i (tg,tls) \<Longrightarrow> (sg, sls) = (tg,tls)"
  apply (auto simp add: toSeqState_def Let_def split_beta)
  by (metis append_eq_append_conv id_take_nth_drop length_take less_Suc_eq less_Suc_eq_le min.absorb2)


lemma eq_toSeq:
  "i<length (snd a) \<and> i<length (snd b) \<Longrightarrow>
   toSeqState i a = toSeqState i b \<Longrightarrow>
   a = b"
  by (cases a; cases b; fastforce dest: eq_toSeqState) 


lemma eq_toPar:
    "toParState m a = toParState m b \<Longrightarrow>
       a = b" 
  by (auto simp add:  eq_toParState)

definition related_set::"nat \<Rightarrow>  (('g,'l)c_state set \<times> ('g,'l)par_state set) set"
  where "related_set i \<equiv> {(S,P). (\<forall>s\<in>S. (\<exists>p\<in>P. (s,p)\<in> par_seq_rel i)) \<and> 
                              (\<forall>p\<in>P. (\<exists>s\<in>S. (s,p)\<in> par_seq_rel i)) }"

lemma seq_pred_in_rel:"\<forall>e \<in> P. i<length (snd e) \<Longrightarrow> 
       (Seq_pred i P,  P)\<in>related_set i"
  unfolding Seq_pred_def related_set_def Image_def apply auto
  using toSeqState_in_rel by blast+

lemma par_pred_in_rel:"\<forall>e \<in> P. i\<le>length (snd e) \<Longrightarrow> 
       (P,  Par_pred i P)\<in>related_set i"
  unfolding Par_pred_def related_set_def Image_def apply auto
  using toParState_in_rel by blast+

lemma Seq_related_set:"(S,P)\<in>related_set i \<Longrightarrow>
       S= Seq_pred i P"
  unfolding related_set_def Seq_pred_def Image_def image_def apply auto
  using par_seq_rel_seq apply blast
  using par_seq_rel_seq by blast

lemma Par_related_set:"(S,P)\<in>related_set i \<Longrightarrow>
       P= Par_pred i S"
  unfolding related_set_def Par_pred_def Image_def image_def apply auto
  using par_seq_rel_par by blast+


definition product_related::"nat \<Rightarrow> ((('g,'l)c_state) tran \<times> (('g,'l)par_state) tran) set"
  where "product_related i \<equiv> {(x,y). ((fst x),(fst y))\<in>par_state_rel i  \<and> 
                                   ((snd x),(snd y)) \<in> par_state_rel i}"

lemma  Seq_xstate_product_rel:"(t1,t2) \<in> product_related i \<Longrightarrow>
         t1 = (toSeqState i (fst t2), toSeqState i (snd t2))" 
  unfolding product_related_def
proof -
  assume "(t1, t2) \<in> {(x, y). (fst x, fst y) \<in> par_state_rel i \<and> (snd x, snd y) \<in> par_state_rel i}"
  then have "(fst t1, fst t2) \<in> par_state_rel i \<and> (snd t1, snd t2) \<in> par_state_rel i"
    by force
  then show ?thesis
    by (metis (no_types) par_xstate_rel_seq prod.exhaust_sel)
qed

lemma  Par_xstate_product_rel:
   "(t1,t2) \<in> product_related i \<Longrightarrow>
     t2 = (toParState i (fst t1), toParState i (snd t1))" 
  unfolding product_related_def
proof -
  assume "(t1, t2) \<in> {(x, y). (fst x, fst y) \<in> par_state_rel i \<and> (snd x, snd y) \<in> par_state_rel i}"
  then have "(fst t1, fst t2) \<in> par_state_rel i \<and> (snd t1, snd t2) \<in> par_state_rel i"
    by force
  then show ?thesis
    by (metis par_xstate_rel_par prod.exhaust_sel)

qed

lemma seq_tran_in_product_rel:
  " i<length (snd x) \<and>  i<length (snd y)  \<Longrightarrow> 
       (((toSeqState i x),(toSeqState i y)), (x,y))\<in>product_related i"
  unfolding product_related_def par_state_rel_def    
  by (auto simp add: toSeqState_in_rel)
                            
lemma par_tran_in_product_rel:
  "i\<le>length (snd x) \<and> i\<le>length (snd y)  \<Longrightarrow> 
       ((x,y), ((toParState i x),(toParState i y)))\<in>product_related i"
  unfolding product_related_def 
  by (auto simp add: toPar_state_in_rel)


definition tran_related::"nat \<Rightarrow> ((('g,'l)c_state) tran set \<times> (('g,'l)par_state) tran set) set"
  where "tran_related i \<equiv> {(RS,RP). (\<forall>ps\<in>RS. \<exists>pp\<in>RP. (ps,pp)\<in>  (product_related i)) \<and> 
                                     (\<forall>pp\<in>RP. \<exists>ps\<in>RS. (ps,pp)\<in>  (product_related i))}"

lemma seq_tran_rel:
  "\<forall>(x,y) \<in> Rp. i<length (snd x) \<and>  i<length (snd y)  \<Longrightarrow> 
       (Seq_rel i Rp, Rp)\<in>tran_related i"
  unfolding tran_related_def Seq_rel_def Image_def split_beta apply auto
  apply (metis fst_conv prod.exhaust_sel seq_tran_in_product_rel swap_simp)
  by (metis prod.exhaust_sel seq_tran_in_product_rel)

lemma par_tran_rel:
  "\<forall>(x,y) \<in> Rp. i\<le>length (snd x) \<and> i\<le>length (snd y) \<Longrightarrow> 
       (Rp, Par_rel i Rp)\<in>tran_related i"
  unfolding tran_related_def Par_rel_def Image_def split_beta apply auto
  apply (metis eq_snd_iff fst_conv par_tran_in_product_rel)
  by (metis par_tran_in_product_rel prod.exhaust_sel snd_conv swap_simp)

lemma Seq_xstate_tran_rel:"(Rs,Rp)\<in>tran_related i \<Longrightarrow>
       Rs = Seq_rel i Rp"
  unfolding tran_related_def Seq_rel_def split_beta image_def apply auto  
  using Seq_xstate_product_rel by fastforce+

lemma Par_xstate_tran_rel:"(Rs,Rp)\<in>tran_related i \<Longrightarrow>
       Rp = Par_rel i Rs"
  unfolding tran_related_def Par_rel_def split_beta image_def apply auto  
  using Par_xstate_product_rel by fastforce+        

lemma cptn_length_locs_lesseq_i:
  assumes a0:"(\<Gamma>,ls)\<in>cptn" and
       a1:"i\<le> length (snd (snd(ls!0)))"
     shows"\<forall>j<length ls. i\<le>length (snd (snd (ls!j)))"
  using ComputationConGlob.cptn_length_locs_less_i
proof-
  {
    fix j 
    assume a00:"j<length ls"     
    obtain p g l lss  where ls0:"ls!0 = (p, ((g,l), lss))"
      by (metis (no_types) eq_snd_iff) 
    then have cptni:"(i,\<Gamma>, toParCptn i ls) \<in> cptni" using cptn_cptni[OF a0 _ a1]
      by auto
    moreover have "length ls>0" using a0
      using cptn.simps by blast
    moreover have  eq:"\<forall>j<length ls. snd (toParCptn i ls ! j) = toParState i (snd (ls!j))" 
      unfolding toParCptn_def by auto  
    ultimately have 
      " i < length (snd (snd (toParCptn i ls ! 0)))"
      using  a1 unfolding toParCptn_def apply (auto; cases "snd (ls!0)", auto)
      by(metis Suc_eq_plus1 le_imp_less_Suc len_toParState snd_conv)+
    then have "\<forall>j<length (toParCptn i ls). i< length (snd (snd ((toParCptn i ls)!j)))"
      by (metis cptni gr_implies_not_zero length_0_conv 
              length_greater_0_conv length_locs_less_i prod.exhaust_sel)      
    then have  "i\<le> length (snd  (snd(ls!j)))" using eq
      using a0 a00 a1 cptn_length_locs_less_i ls0 by fastforce
  } then show ?thesis by auto
qed

lemma eq_xstate_related_list:       
  assumes a0:"\<forall>j<length ls. i\<le>length (snd ( snd (ls!j)))" and
          a1:"(b, toParCptn i ls) \<in> par_state_list_rel i" 
  shows "b = ls"
proof-
  have  "length b = length ls" 
    using a1 unfolding par_state_list_rel_def
    by (simp add: list_all2_conv_all_nth toParCptn_def)
  moreover have "\<forall>i<length b. b ! i = ls ! i"
  proof-
    {fix j 
      assume a00:"j<length b"
      then have "fst (b!j) = fst ((toParCptn i ls)!j) \<and> 
                (snd (b!j), snd ((toParCptn i ls)!j))\<in>par_state_rel i"
        using a1 unfolding par_state_list_rel_def 
        by (simp add: list_all2_conv_all_nth) 
      then have "b!j = ls!j"
        by (metis Par2Seq0f a0 a00 calculation fstI par_xstate_rel_seq 
                   prod.collapse sndI toParCptn_j)       
    } then show ?thesis by auto
  qed
  ultimately show ?thesis using list_eq[of b ls] by auto
qed

lemma etran_ctran_False: "\<Gamma>\<turnstile>\<^sub>c (c,toSeq s)  \<rightarrow> (c',toSeq s') \<Longrightarrow>
             \<Gamma>\<turnstile>\<^sub>c (c,s1)  \<rightarrow>\<^sub>e (c', s') \<Longrightarrow>
            False"
proof -
   assume a0: "\<Gamma>\<turnstile>\<^sub>c (c,toSeq s)  \<rightarrow> (c',toSeq s')" and
          a1: "\<Gamma>\<turnstile>\<^sub>c (c,s1)  \<rightarrow>\<^sub>e (c', s')"   
   thus ?thesis using a0 a1 mod_env_not_component
     using env_c_c' by metis
 qed

lemma etran_ctran_eq_p_normal_s: "\<Gamma>\<turnstile>\<^sub>c (c,toSeq s)  \<rightarrow> (c',toSeq s') \<Longrightarrow>
             \<Gamma>\<turnstile>\<^sub>c (c,s1)  \<rightarrow>\<^sub>e (c', s') \<Longrightarrow>
            c = c' \<and> s = s' "
  using etran_ctran_False by blast


lemma "list_all2 P b l \<Longrightarrow>
       length b = length l \<and> (\<forall>i<length l. P (b!i) (l!i))"
  by (simp add: list_all2_conv_all_nth) 

definition final_glob_p:: "('g,'l,'p,'f,'e) gconf \<Rightarrow> bool" where
  "final_glob_p cfg \<equiv>  fst cfg=Skip \<or> (fst cfg=Throw) \<or> fst cfg = Stuck \<or> (\<exists>f. fst cfg =Fault f )"

lemma final_eq:"final_glob_p cfg = final_glob (fst cfg, toSeqState i (snd cfg))"
  unfolding final_glob_p_def final_glob_def
  by auto

lemma par_state_list_rel_eq:
      assumes a01:"(b1,l)\<in> par_state_list_rel i" and
              a02:"(b2,l)\<in> par_state_list_rel i"
            shows "b1 = b2"  
proof-
  have "length b1 = length b2" using a01 a02 unfolding par_state_list_rel_def
    by (simp add: list_all2_conv_all_nth) 
  moreover have "\<forall>j<length b1. b1!j = b2!j"
  proof-
    have "\<forall>j<length l. fst (b1!j) = fst (l!j) \<and> (snd (b1!j), snd (l!j)) \<in> par_state_rel i \<and>
                       fst (b2!j) = fst (l!j) \<and> (snd (b2!j), snd (l!j)) \<in> par_state_rel i"
      using  a01 a02  unfolding par_state_list_rel_def by (auto simp add: list_all2_conv_all_nth)
    thus ?thesis using a01 unfolding par_state_list_rel_def
      by (metis (no_types, lifting) Product_Type.Collect_case_prodD fst_conv list_all2_lengthD 
                par_xstate_rel_seq prod.expand snd_conv)
  qed
  ultimately show ?thesis
    using nth_equalityI by blast
qed


lemma par_xstate_list_rel_dest1:
   "(l',l)\<in>par_state_list_rel i' \<Longrightarrow>
    length l' = length l"
  unfolding par_state_list_rel_def apply auto
  using list_all2_conv_all_nth by blast

lemma par_xstate_list_rel_dest2:
   "(l',l)\<in>par_state_list_rel i' \<Longrightarrow>
    \<forall>i<length l'. (snd (l'!i),snd(l!i))\<in>par_state_rel i'"
  unfolding par_state_list_rel_def apply auto
  by (simp add: list_all2_conv_all_nth)

lemma par_xstate_list_rel_dest3:
"(l',l)\<in>par_state_list_rel i' \<Longrightarrow>
    \<forall>i<length l'. fst (l'!i) = fst(l!i)"
  unfolding par_state_list_rel_def apply auto
  by (simp add: list_all2_conv_all_nth)

lemma par_xstate_rel_dest1:
  assumes a0:"(s,p) \<in> par_state_rel i"
  shows "i< length (snd p)"
  using a0 unfolding par_state_rel_def apply auto
  using par_seq_rel_i_length by fastforce+

lemma par_xstate_list_rel_step_e_s:
   "(s,p) \<in> par_state_list_rel i \<Longrightarrow>
 Suc j<length s \<Longrightarrow>
  \<Gamma>\<turnstile>\<^sub>c(fst(p!j), (toSeqState i (snd (p!j))))  \<rightarrow>\<^sub>e 
       (fst(p!(Suc j)),  (toSeqState i (snd (p!(Suc j))))) \<Longrightarrow>
    \<Gamma>\<turnstile>\<^sub>c(fst(s!j),  ((snd (s!j))))  \<rightarrow>\<^sub>e 
       (fst(s!(Suc j)),  (snd (s!(Suc j))))"
  by (metis Suc_lessD par_xstate_list_rel_dest1 par_xstate_list_rel_dest2 par_xstate_list_rel_dest3 
          par_xstate_rel_seq)
  

lemma par_xstate_list_rel_step_e_p:
   "(s,p) \<in> par_state_list_rel i \<Longrightarrow>
Suc j<length s \<Longrightarrow>
  \<Gamma>\<turnstile>\<^sub>c(fst(s!j),  ((snd (s!j))))  \<rightarrow>\<^sub>e 
       (fst(s!(Suc j)),  (snd (s!(Suc j)))) \<Longrightarrow>
  \<Gamma>\<turnstile>\<^sub>c(fst(p!j), (toSeqState i (snd (p!j))))  \<rightarrow>\<^sub>e 
       (fst(p!(Suc j)),  (toSeqState i (snd (p!(Suc j)))))"
  by (metis Suc_lessD par_xstate_list_rel_dest1 par_xstate_list_rel_dest2
     par_xstate_list_rel_dest3 par_xstate_rel_seq)

lemma par_xstate_list_rel_step_c_s:
  "(s,p) \<in> par_state_list_rel i \<Longrightarrow>
   Suc j<length s \<Longrightarrow>
    \<Gamma>\<turnstile>\<^sub>c(fst(p!j), toSeq (toSeqState i (snd (p!j))))  \<rightarrow> 
       (fst(p!(Suc j)), toSeq (toSeqState i (snd (p!(Suc j))))) \<Longrightarrow>
    \<Gamma>\<turnstile>\<^sub>c(fst(s!j), toSeq ((snd (s!j))))  \<rightarrow> 
       (fst(s!(Suc j)), toSeq (snd (s!(Suc j))))"
  by (metis Suc_lessD par_xstate_list_rel_dest1 par_xstate_list_rel_dest2 
    par_xstate_list_rel_dest3 par_xstate_rel_seq)
  

lemma par_xstate_list_rel_step_c_p:
  "(s,p) \<in> par_state_list_rel i \<Longrightarrow>
   Suc j<length s \<Longrightarrow>
   \<Gamma>\<turnstile>\<^sub>c(fst(s!j), toSeq ((snd (s!j))))  \<rightarrow> 
       (fst(s!(Suc j)), toSeq (snd (s!(Suc j)))) \<Longrightarrow>
    \<Gamma>\<turnstile>\<^sub>c(fst(p!j), toSeq (toSeqState i (snd (p!j))))  \<rightarrow> 
       (fst(p!(Suc j)), toSeq (toSeqState i (snd (p!(Suc j)))))"
  by (metis Suc_lessD par_xstate_list_rel_dest1 par_xstate_list_rel_dest2 
    par_xstate_list_rel_dest3 par_xstate_rel_seq)

lemma par_xstate_list_Fault_i_s:
  "(s,p) \<in> par_state_list_rel i \<Longrightarrow>
   j<length s \<Longrightarrow>
   fst (p!j) \<noteq> Fault F \<Longrightarrow>
   fst (s!j) \<noteq> Fault F "
  by (simp add: par_xstate_list_rel_dest3)


lemma par_xstate_list_Fault_i_p:
  "(s,p) \<in> par_state_list_rel i \<Longrightarrow>
   j<length s \<Longrightarrow>
   fst (s!j) \<noteq> Fault F \<Longrightarrow>
   fst (p!j) \<noteq> Fault F "
by (simp add: par_xstate_list_rel_dest3)


lemma par_xstate_list_Fault_s:
  "(s,p) \<in> par_state_list_rel i \<Longrightarrow>
   s\<noteq>[] \<Longrightarrow>
   fst (last p) \<noteq> Fault F \<Longrightarrow>
   fst (last s) \<noteq> Fault F "
proof -
  assume a1: "s \<noteq> []"
  assume a2: "(s, p) \<in> par_state_list_rel i"
  assume a3: "fst (last p) \<noteq> com.Fault F"
  have "0 < length s"
    using a1 by blast
  then show ?thesis
    using a3 a2 a1 by (simp add: last_conv_nth par_xstate_list_rel_dest1 par_xstate_list_rel_dest3)
qed
  

lemma par_xstate_list_Fault_p:
  "(s,p) \<in> par_state_list_rel i \<Longrightarrow>
   s\<noteq>[] \<Longrightarrow>  
   fst (last s) \<noteq> Fault F \<Longrightarrow> 
    fst (last p) \<noteq> Fault F"
  using par_xstate_list_Fault_i_p
  by (metis diff_less last_conv_nth length_greater_0_conv 
     less_numeral_extra(1) par_xstate_list_rel_dest1)

lemma par_xstate_list_Fault_set_s:
  "(s,p) \<in> par_state_list_rel i \<Longrightarrow>
   s\<noteq>[] \<Longrightarrow>
   fst (last p) \<notin> Fault ` F \<Longrightarrow>
   fst (last s) \<notin> Fault ` F "
  by (simp add: image_iff par_xstate_list_Fault_s)

lemma par_xstate_list_Fault_set_p:
  "(s,p) \<in> par_state_list_rel i \<Longrightarrow>
   s\<noteq>[] \<Longrightarrow>  
   fst (last s) \<notin> Fault ` F \<Longrightarrow> 
    fst (last p) \<notin> Fault ` F"
  by (simp add: image_iff par_xstate_list_Fault_p)

lemma par_xstate_list_final_s:
  "(s,p) \<in> par_state_list_rel i \<Longrightarrow>
   s\<noteq>[] \<Longrightarrow> final_glob_p (last p) \<Longrightarrow>
   final_glob (last s)"
proof-
  assume a0:"(s,p) \<in> par_state_list_rel i" and
         a1:"s\<noteq>[]" and
         a2:"final_glob_p (last p)"
  then  have "length s = length p"
      using  par_xstate_list_rel_dest1 by blast
            
  then show ?thesis
    using  a1 a2 unfolding final_glob_def final_glob_p_def apply auto
       apply (metis a0 diff_less last_conv_nth length_greater_0_conv par_xstate_list_rel_dest3 
                  zero_less_one)
       apply (metis \<open>length s = length p\<close> a0 diff_less last_conv_nth length_greater_0_conv 
                   par_xstate_list_rel_dest3 zero_less_one)
      apply (metis \<open>length s = length p\<close> a0 diff_less last_conv_nth 
                   length_greater_0_conv par_xstate_list_rel_dest3 zero_less_one)
    by (metis \<open>length s = length p\<close> a0 diff_less last_conv_nth 
                  length_greater_0_conv par_xstate_list_rel_dest3 zero_less_one)    
qed

lemma par_xstate_list_final_p:
  "(s,p) \<in> par_state_list_rel i \<Longrightarrow>
   s\<noteq>[] \<Longrightarrow> final_glob (last s) \<Longrightarrow>
   final_glob_p (last p)"
proof-
  assume a0:"(s,p) \<in> par_state_list_rel i" and
         a1:"s\<noteq>[]" and
         a2:"final_glob (last s)"
  then  have "length s = length p"
      using  par_xstate_list_rel_dest1 by blast
  then have  "(snd (last s), snd(last p)) \<in>par_state_rel i"
    by (metis (no_types) a0 a1 diff_less last_conv_nth 
             length_greater_0_conv less_numeral_extra(1) par_xstate_list_rel_dest2)            
  then show ?thesis
    using  a1 a2 unfolding final_glob_def final_glob_p_def apply auto
       apply (metis \<open>length s = length p\<close> a0 diff_less last_conv_nth length_greater_0_conv 
                   par_xstate_list_rel_dest3 zero_less_one)
      apply (metis \<open>length s = length p\<close> a0 diff_less last_conv_nth 
                   length_greater_0_conv par_xstate_list_rel_dest3 zero_less_one)
     apply (metis \<open>length s = length p\<close> a0 diff_less last_conv_nth 
                  length_greater_0_conv par_xstate_list_rel_dest3 zero_less_one)    
    by (metis \<open>length s = length p\<close> a0 diff_less last_conv_nth 
          length_greater_0_conv par_xstate_list_rel_dest3 zero_less_one) 
 
qed

lemma par_xstate_list_rel_program:  
  assumes 
  a0:"(s,p) \<in> par_state_list_rel i" and
  a1:"j<length s"
shows  "fst (p!j) = fst (s!j)"
proof-
  show ?thesis using a0 a1
    using par_xstate_list_rel_dest1 par_xstate_list_rel_dest3 by fastforce
qed                        

lemma par_xstate_list_rel_in_post_p:  assumes 
  a0:"(s,p) \<in> par_state_list_rel i" and
  a1:"s\<noteq>[]" and
  a2:"snd (last s) \<in> Seq_pred i q" and
  a3:"\<forall>e\<in>q. i<length (snd e)"
shows "snd (last p) \<in> q"
proof-
  have "length s = length p"
      using  a0 par_xstate_list_rel_dest1 by blast  
  then have  rel:"(snd (last s), snd(last p)) \<in>par_state_rel i"
    by (metis (no_types) a0 a1 diff_less last_conv_nth 
             length_greater_0_conv less_numeral_extra(1) par_xstate_list_rel_dest2)     
  then show ?thesis
    using a2 a3  rel unfolding Seq_pred_def    
  by (metis Par_Seq_pred_ID Par_pred_def Seq_pred_def imageI par_xstate_rel_par)
                                                           
qed

lemma par_xstate_list_rel_in_post_s:  
  assumes 
  a0:"(s,p) \<in> par_state_list_rel i" and
  a1:"s\<noteq>[]" and
  a2:"snd (last p) \<in> q" 
shows "snd (last s) \<in> Seq_pred i q"
proof-
 have "length s = length p"
      using  a0 par_xstate_list_rel_dest1 by blast  
 then have  rel:"(snd (last s), snd(last p)) \<in>par_state_rel i"
    by (metis (no_types) a0 a1 diff_less last_conv_nth 
             length_greater_0_conv less_numeral_extra(1) par_xstate_list_rel_dest2)
  thus ?thesis using a2 
    using Seq_pred_def par_xstate_rel_seq
    by (metis image_eqI )
qed

lemma par_xstate_list_rel_in_post_p_eq_state:  assumes 
  a0:"(s,p) \<in> par_state_list_rel i" and
  a1:"s\<noteq>[]" and
  a2:"snd (last s) = (toSeqState i ns) \<and> (toSeqState i ns) \<in> Seq_pred i q" and
  a3:"\<forall>e\<in>q. i<length (snd e)" and a4:"i<length (snd ns)"
shows "snd (last p) \<in> q" 
proof-
  have "length s = length p"
      using  a0 par_xstate_list_rel_dest1 by blast  
  then have  rel:"(snd (last s), snd(last p)) \<in>par_state_rel i"
    by (metis (no_types) a0 a1 diff_less last_conv_nth 
             length_greater_0_conv less_numeral_extra(1) par_xstate_list_rel_dest2)     
  then show ?thesis
    using a2 a3 a4 rel unfolding Seq_pred_def
    by (metis (no_types, lifting)  a0 a1 a2 par_xstate_list_rel_in_post_p) 
                                                           
qed


lemma par_xstate_list_rel_in_post_s_state:  
  assumes 
  a0:"(s,p) \<in> par_state_list_rel i" and
  a1:"s\<noteq>[]" and
  a2:"snd (last p)\<in> q" 
shows "snd (last s) =  (toSeqState i (snd (last p))) \<and> toSeqState i  (snd (last p)) \<in> Seq_pred i q"
proof-
 have "length s = length p"
      using  a0 par_xstate_list_rel_dest1 by blast  
 then have  rel:"(snd (last s), snd(last p)) \<in>par_state_rel i"
    by (metis (no_types) a0 a1 diff_less last_conv_nth 
             length_greater_0_conv less_numeral_extra(1) par_xstate_list_rel_dest2)
  thus ?thesis using a2 par_xstate_rel_seq[OF rel]
    unfolding Seq_pred_def by auto
qed

lemma par_xstate_list_rel_in_g_s: 
assumes 
  a0:"(s,p) \<in> par_state_list_rel i" and 
  a2:"Suc j < length s" and
  a3:"(snd (p!j), snd(p!(Suc j))) \<in> G" 
shows "(snd (s!j), snd(s!(Suc j))) \<in> Seq_rel i G"
proof-
  have  rel_j:"(snd (s!j), snd(p!j)) \<in>par_state_rel i" and
        rel_sj:"(snd (s!(Suc j)), snd(p!(Suc j))) \<in>par_state_rel i" 
     by (metis (no_types) Suc_lessD a0 a2 par_xstate_list_rel_dest1 par_xstate_list_rel_dest2)+   
   thus ?thesis using a2 a3 unfolding Seq_rel_def split_beta image_def 
     apply auto
     by (metis fst_conv par_xstate_rel_seq snd_conv)
 qed

lemma par_xstate_list_rel_in_g_p: 
assumes 
  a0:"(s,p) \<in> par_state_list_rel i" and  
  a2:"Suc j < length s" and
  a3:"(snd (s!j), snd(s!(Suc j))) \<in> Seq_rel i G"  and
  a4:"\<forall>(x,y)\<in>G. ( i<length (snd x)) \<and> ( i<length (snd y)) "
shows "(snd (p!j), snd(p!(Suc j))) \<in> G"
proof-
  have  rel_j:"(snd (s!j), snd(p!j)) \<in>par_state_rel i" and
        rel_sj:"(snd (s!(Suc j)), snd(p!(Suc j))) \<in>par_state_rel i" 
     by (metis (no_types) Suc_lessD a0 a2 par_xstate_list_rel_dest1 par_xstate_list_rel_dest2)+   
   thus ?thesis using a2 a3 a4 unfolding Seq_rel_def split_beta image_def 
     apply auto
     by (metis Seq2Par fst_conv par_xstate_rel_par snd_conv)
qed

abbreviation (input)
  set_fun :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"  ("_\<^sub>f") where
  "set_fun s \<equiv> \<lambda>v. v\<in>s"

abbreviation (input)
  fun_set :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set"  ("_\<^sub>s") where
  "fun_set f \<equiv> {\<sigma>. f \<sigma>}"


lemma tl_pair:"Suc (Suc j) < length l \<Longrightarrow>     
       l1 = tl l \<Longrightarrow>
       P (l!(Suc j)) (l!(Suc (Suc j)))=
       P  (l1!j) (l1!(Suc j))"
by (simp add: tl_zero_eq)

lemma for_all_k_sublist:
assumes a0:"Suc (Suc j)<length l" and
      a1:"(\<forall>k < j. P ((tl l)!k) ((tl l)!(Suc k)))" and
      a2:"P (l!0) (l!(Suc 0))" 
shows "(\<forall>k < Suc j.  P (l!k) (l!(Suc k)))"
proof -
  {fix k
   assume aa0:"k < Suc j"
   have "P (l!k) (l!(Suc k))"
   proof (cases k)
     case 0 thus ?thesis using a2 by auto
   next
     case (Suc k1) thus ?thesis using aa0 a0 a1 a2
       by (metis SmallStepCon.nth_tl Suc_less_SucD dual_order.strict_trans length_greater_0_conv nth_Cons_Suc zero_less_Suc)
   qed
  } thus ?thesis by auto
qed


subsection \<open>Validity for Component Programs.\<close>


type_synonym ('g,'l,'p,'f,'e) p_rgformula =  
   "(('g \<times> 'l,'p,'f,'e)com \<times>      
    (('g,'l)par_state set) \<times>         
    ((('g,'l)par_state) tran) set \<times>
    ((('g,'l)par_state) tran) set \<times>
    (('g,'l)par_state set) \<times> 
    (('g,'l)par_state set))" (* A *)
    
type_synonym ('g,'l,'p) p_sextuple =  
   "('p \<times>     
    (('g,'l)par_state set) \<times>         
    ((('g,'l)par_state) tran) set \<times> 
    ((('g,'l)par_state) tran) set \<times> 
    (('g,'l)par_state set) \<times>
    (('g,'l)par_state set))" (* A *) 

type_synonym ('g,'l,'p,'f,'e) c_rgformula =  
   "(('g \<times> 'l,'p,'f,'e)com \<times>      
     ('g,'l) c_state  set \<times>         
    ((('g,'l) c_state) tran) set \<times>
    ( (('g,'l) c_state) tran) set \<times>
    ('g,'l) c_state set \<times> 
    ('g,'l) c_state  set)" (* A *)

type_synonym ('g,'l,'p) c_sextuple =  
   "('p \<times>     
     ('g,'l) c_state set \<times>         
    ((('g,'l) c_state)tran) set \<times>
    ((('g,'l) c_state) tran) set \<times>
    ('g,'l) c_state  set \<times> 
    ('g,'l) c_state  set)" (* A *)    

definition Sta :: "'s set \<Rightarrow> ('s tran) set \<Rightarrow> bool" where
  "Sta \<equiv> \<lambda>f g. (\<forall>x y.  x \<in> f \<longrightarrow>  (x,y)\<in> g \<longrightarrow> y \<in> f)"

lemma Sta_intro:"Sta a R \<Longrightarrow> Sta b R \<Longrightarrow> Sta (a \<inter> b) R"
unfolding Sta_def by fastforce

lemma Sta_assoc:"Sta (a \<inter> (b \<inter> c)) R = Sta ((a\<inter>b)\<inter>c) R"
unfolding Sta_def by blast

lemma Sta_comm:"Sta (a \<inter> b) R = Sta (b \<inter> a) R" 
unfolding Sta_def by blast

lemma Sta_add:"Sta (a \<inter> b) R \<Longrightarrow> Sta (a \<inter> c) R \<Longrightarrow>
       Sta (a \<inter> b \<inter> c) R"
unfolding Sta_def by blast

lemma Sta_tran:"Sta a R \<Longrightarrow> a = b \<Longrightarrow> Sta b R"
by auto

(* definition Norm:: "(('s) tran) set \<Rightarrow> bool" where
  "Norm \<equiv> \<lambda>g. (\<forall>x y. (x, y) \<in> g \<longrightarrow> (\<exists>x' y'. x=Normal x' \<and> y=Normal y'))" *)

definition env_tran::
    "('p \<Rightarrow> ('g\<times>'l, 'p, 'f,'e) LanguageCon.com option)
     \<Rightarrow> (('g,'l) c_state set)
        \<Rightarrow> (('g\<times>'l, 'p, 'f,'e) LanguageCon.com \<times> (('g,'l) c_state)) list
           \<Rightarrow> (('g,'l) c_state) tran set \<Rightarrow> bool"
where
"env_tran \<Gamma> q l rely \<equiv> snd(l!0) \<in>  q \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                  
                   (snd(l!i), snd(l!(Suc i))) \<in> rely)
"

definition env_tran_right::
    "('p \<Rightarrow> ('g\<times>'l, 'p, 'f,'e) LanguageCon.com option)     
        \<Rightarrow> (('g\<times>'l, 'p, 'f,'e) LanguageCon.com \<times> ('g,'l) c_state) list
           \<Rightarrow> (('g,'l) c_state) tran set \<Rightarrow> bool"
where
"env_tran_right \<Gamma> l rely \<equiv> 
   (\<forall>i. Suc i<length l \<longrightarrow> 
        \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                  
        (snd(l!i), snd(l!(Suc i))) \<in> rely)
"

lemma env_tran_tail:"env_tran_right \<Gamma> (x#l) R \<Longrightarrow> env_tran_right \<Gamma> l R"
unfolding env_tran_right_def
by fastforce

lemma env_tran_subr:
assumes a0:"env_tran_right \<Gamma> (l1@l2) R"
shows "env_tran_right \<Gamma> l1 R"
unfolding env_tran_right_def
proof -
  { fix i
    assume a1:"Suc i< length l1"
    assume a2:"\<Gamma>\<turnstile>\<^sub>c (l1 ! i) \<rightarrow>\<^sub>e (l1 ! Suc i)"
    then have "Suc i < length (l1@l2)" using a1 by fastforce
    also then have "\<Gamma>\<turnstile>\<^sub>c ((l1@l2) ! i) \<rightarrow>\<^sub>e ((l1@l2) ! Suc i)" 
      by (simp add: Suc_lessD a1 a2 nth_append)    
    ultimately have f1:"(snd ((l1@l2)! i), snd ((l1@l2) ! Suc i)) \<in> R"
      using a0 unfolding env_tran_right_def by auto
    then have "(snd (l1! i), snd (l1 ! Suc i)) \<in>  R"
      using a1 by (simp add: nth_append)
  } then show 
   "\<forall>i. Suc i < length l1 \<longrightarrow>
        \<Gamma>\<turnstile>\<^sub>c (l1 ! i) \<rightarrow>\<^sub>e (l1 ! Suc i) \<longrightarrow>
        (snd (l1 ! i), snd (l1 ! Suc i)) \<in> R"
   by blast
qed

definition Satis where "Satis \<equiv> True"


lemma env_tran_subl:"env_tran_right \<Gamma> (l1@l2) R \<Longrightarrow> env_tran_right \<Gamma> l2 R"
proof (induct "l1")
  case Nil thus ?case by auto
next
  case (Cons a l1) thus ?case by (fastforce intro:append_Cons env_tran_tail )
qed

lemma env_tran_R_R':"env_tran_right \<Gamma> l R \<Longrightarrow>  
                     (R  \<subseteq> R') \<Longrightarrow>
                     env_tran_right \<Gamma> l R'"
unfolding env_tran_right_def Satis_def 
apply clarify
apply (erule allE)
apply auto
done


lemma env_tran_normal:
assumes a0:"env_tran_right \<Gamma> l rely \<and> Sta q rely \<and>  snd(l!i) \<in>q" and
        a1:"Suc i < length l \<and>  \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))"
shows "snd(l!(Suc i)) \<in>q"
using a0 a1 unfolding env_tran_right_def Sta_def by blast

 
definition assum :: 
  "(('g,'l) c_state set \<times> (('g,'l) c_state) tran set) \<Rightarrow> (('g,'l,'p,'f,'e) confs) set" where
  "assum \<equiv> \<lambda>(pre, rely). 
             {c. snd((snd c)!0) \<in>  pre \<and> 
                 (\<forall>i. Suc i<length (snd c) \<longrightarrow> 
                 (fst c)\<turnstile>\<^sub>c((snd c)!i)  \<rightarrow>\<^sub>e ((snd c)!(Suc i)) \<longrightarrow>                  
                   (snd((snd c)!i), snd((snd c)!(Suc i))) \<in>  rely)}"

definition assum1 :: 
  "(('g,'l) c_state set \<times> (('g,'l) c_state) tran set) \<Rightarrow>
   'f set \<Rightarrow>
     (('g,'l,'p,'f,'e) confs) set" where
  "assum1 \<equiv> \<lambda>(pre, rely) F. 
             {(\<Gamma>,comp). snd(comp!0) \<in>  pre \<and> 
                 (\<forall>i. Suc i<length comp \<longrightarrow> 
                  \<Gamma>\<turnstile>\<^sub>c(comp!i)  \<rightarrow>\<^sub>e (comp!(Suc i)) \<longrightarrow>                  
                   (snd(comp!i), snd(comp!(Suc i))) \<in>  rely)}"


definition assum_p :: 
  "nat \<Rightarrow> (('g,'l) par_state set \<times> (('g,'l) par_state) tran set) \<Rightarrow> 
             (('g,'l,'p,'f,'e) gconfs) set" where
  "assum_p i \<equiv> \<lambda>(pre, rely).                     
     {(s,p). fst s = fst p \<and> (snd s, snd p)\<in>par_state_list_rel i}  `` 
           (assum (Seq_pred i pre, Seq_rel i rely))"

definition assum_p1 :: 
  "nat \<Rightarrow> (('g,'l) par_state set \<times> (('g,'l) par_state) tran set) \<Rightarrow> 
              (('g,'l,'p,'f,'e) gconfs) set" where
  "assum_p1 m \<equiv> \<lambda>(pre, rely). 
             {c. snd((snd c)!0) \<in>  pre \<and> 
                 (\<forall>i. Suc i<length (snd c) \<longrightarrow> 
                 (fst c)\<turnstile>\<^sub>c(fst((snd c)!i), toSeqState m (snd((snd c)!i)))  \<rightarrow>\<^sub>e 
                          (fst((snd c)!(Suc i)), toSeqState m (snd((snd c)!(Suc i))))  \<longrightarrow>                  
                   (snd((snd c)!i), snd((snd c)!(Suc i))) \<in>  rely)}"

lemma p1:"\<forall>e\<in>P::('b\<times>'c list) set. i< length (snd e) \<Longrightarrow>
         \<forall>t\<in>R:: (('b \<times> 'c list)  \<times> ('b \<times> 'c list) ) set. 
                i<length (snd  (fst t)) \<and> i<length (snd (snd t) ) \<Longrightarrow> lp\<noteq>[] \<Longrightarrow> 
          (\<Gamma>,lp) \<in> assum_p i (P,R) \<Longrightarrow> (\<Gamma>,lp) \<in> assum_p1 i (P,R)"
  unfolding assum_p_def assum_p1_def assum_def Let_def split_beta Seq_pred_def   
proof auto
  fix ls  pg pls
  assume a0:"\<forall>e\<in>P. i< length (snd e)" and 
         a1:"(ls, lp) \<in> par_state_list_rel i" and 
          a2:"snd (ls ! 0) =  (toSeqState i (pg, pls))" and  a4:"(pg, pls) \<in> P" and
          a5: "lp\<noteq>[]"   
  have rel:"(snd (ls ! 0), snd (lp ! 0))\<in>par_state_rel i" using a1 a5
    by (metis (no_types, lifting) Product_Type.Collect_case_prodD fst_conv length_greater_0_conv 
              list_all2_conv_all_nth par_state_list_rel_def snd_conv)   
  have "snd (lp ! 0) =   (toParState i (toSeqState i (pg, pls)))" 
    using a2 par_xstate_rel_par rel by fastforce        
  moreover  have len_i:"i< length (pls)" using a0 a4 by auto
  ultimately show "snd (lp ! 0) \<in> P" 
    by (simp add: Seq2Par a4)
next
  fix  ls  j
  assume a0:"\<forall>e\<in>P. i< length (snd e)" and  
        a1:"(ls, lp) \<in> par_state_list_rel i" and
        a2:"\<forall>ia. Suc ia < length ls \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c (ls ! ia) \<rightarrow>\<^sub>e (ls ! Suc ia) \<longrightarrow> 
             (snd (ls ! ia), snd (ls ! Suc ia)) \<in> Seq_rel i R" and        
        a6:"Suc j < length lp" and
        a7:"\<Gamma>\<turnstile>\<^sub>c (fst (lp ! j), toSeqState i (snd (lp ! j))) \<rightarrow>\<^sub>e 
                (fst (lp ! Suc j), toSeqState i (snd (lp ! Suc j)))" and 
        a8:"\<forall>t\<in>R. i < length (snd (fst t)) \<and> i < length (snd (snd t))"
  then have rel:"(snd (ls ! j), snd (lp ! j))\<in>par_state_rel i" and  "fst (ls!j) = fst(lp!j)" and
            relsuc:   "(snd (ls ! Suc j), snd (lp ! Suc j))\<in>par_state_rel i" and "fst (ls!Suc j) = fst(lp!Suc j)"
    unfolding par_state_list_rel_def
    by (auto simp add: a0 a2 a6 Suc_lessD list_all2_conv_all_nth)   
  moreover have  "snd (ls ! j) = toSeqState i (snd (lp ! j))" and                  
              "snd (ls ! (Suc j)) = toSeqState i (snd (lp ! (Suc j)))" 
    using calculation par_xstate_rel_seq  par_xstate_rel_par
    by blast+
  ultimately have "(snd (ls ! j), snd (ls ! Suc j)) \<in> Seq_rel i R" using a2 a7 a1 a6
    unfolding par_state_list_rel_def
    by (metis (no_types, lifting) Product_Type.Collect_case_prodD 
              fst_conv list_all2_lengthD prod.collapse snd_conv)      
  then show "(snd (lp ! j), snd (lp ! Suc j)) \<in> R"
    unfolding Seq_rel_def apply auto using  rel relsuc  par_xstate_rel_par a8
    by (metis Seq2Par fst_conv snd_conv)
qed

  

lemma p2:"\<forall>j<length lp. i<length (snd (snd (lp!j))) \<Longrightarrow> lp\<noteq>[] \<Longrightarrow> 
          (\<Gamma>,lp) \<in> assum_p1 i (P,R) \<Longrightarrow> (\<Gamma>,lp) \<in> assum_p i (P,R)"
proof (auto simp add:  Let_def split_beta Seq_pred_def image_def  assum_p_def assum_p1_def assum_def ) 
  assume a00:"\<forall>j<length lp. i < length (snd (snd (lp ! j)))" and          
         a03:"lp \<noteq> []" and
         a04:"\<forall>ia. Suc ia < length lp \<longrightarrow>
          \<Gamma>\<turnstile>\<^sub>c (fst (lp ! ia), toSeqState i (snd (lp ! ia))) \<rightarrow>\<^sub>e
                (fst (lp ! Suc ia), toSeqState i (snd (lp ! Suc ia))) \<longrightarrow>
          (snd (lp ! ia), snd (lp ! Suc ia)) \<in> R" and
         a05: "snd (lp ! 0) \<in> P" 
  then have xstate_rel:"(toSeqCptn i lp, lp)\<in> (par_state_list_rel i)"
     by (simp add: toSeqCptn_in_rel)
  then have "(toSeqCptn i lp)!0 = (fst (lp!0),toSeqState i (snd (lp!0)))"
    by (simp add: a03 toSeqCptn_j)  
  moreover obtain gs ls lss where "snd ((toSeqCptn i lp)!0) = ((gs,ls),lss)"
    using a00 a03   by (auto simp add: toSeqState_def Let_def split_beta toSeqCptn_j a03) 
  ultimately have "snd (lp ! 0) \<in>P \<and> ((gs,ls),lss) =  toSeqState i (snd (lp ! 0)) \<and> 
                   snd ((toSeqCptn i lp)!0) =((gs,ls),lss)"
    using a05  by auto
  moreover have "(\<forall>ia. Suc ia < length (toSeqCptn i lp) \<longrightarrow>
                   \<Gamma>\<turnstile>\<^sub>c ((toSeqCptn i lp) ! ia) \<rightarrow>\<^sub>e ((toSeqCptn i lp) ! Suc ia) \<longrightarrow> 
                   (snd ((toSeqCptn i lp) ! ia), snd ((toSeqCptn i lp) ! Suc ia)) \<in> Seq_rel i R)"
    by (metis Suc_lessD a04 par_xstate_list_rel_dest1 
                 par_xstate_list_rel_in_g_s toSeqCptn_j xstate_rel)  
  ultimately show "\<exists>b. (\<exists>x\<in>P. snd (b ! 0) = toSeqState i x) \<and>
                      (\<forall>ia. Suc ia < length b \<longrightarrow>
                          \<Gamma>\<turnstile>\<^sub>c (b ! ia) \<rightarrow>\<^sub>e (b ! Suc ia) \<longrightarrow> 
                        (snd (b ! ia), snd (b ! Suc ia)) \<in> Seq_rel i R) \<and>
                        (b, lp) \<in> par_state_list_rel i"
    using xstate_rel by fastforce
  qed

lemma assum_R_R': 
  "(\<Gamma>, l) \<in> assum(p, R) \<Longrightarrow>
    snd(l!0) \<in>  p' \<Longrightarrow>
    R \<subseteq> R'  \<Longrightarrow> 
   (\<Gamma>, l) \<in> assum(p', R')"
proof -
assume a0:"(\<Gamma>, l) \<in> assum(p, R)" and
       a1:"snd(l!0) \<in> p'" and
       a2: " R \<subseteq> R'"
  then have "env_tran_right \<Gamma> l R" 
    unfolding assum_def using env_tran_right_def
    by force
  then have "env_tran_right \<Gamma> l R'" 
    using  a2 env_tran_R_R' by blast
  thus ?thesis using a1 unfolding assum_def unfolding env_tran_right_def
    by fastforce
qed


lemma same_prog_p:
  "(\<Gamma>,(P,s)#(P,t)#l)\<in>cptn \<Longrightarrow>
   (\<Gamma>,(P,s)#(P,t)#l) \<in> assum (p,R) \<Longrightarrow>
   Sta p R  \<Longrightarrow>
   t \<in> p
  " 
proof -
assume a0: "(\<Gamma>,(P,s)#(P,t)#l)\<in>cptn" and
         a1: "(\<Gamma>,(P,s)#(P,t)#l) \<in> assum (p,R)" and
         a2: "Sta p R"
  then have "Suc 0 < length ((P,s)#(P,t)#l)" 
    by fastforce
  then have "\<Gamma>\<turnstile>\<^sub>c (P,s)  \<rightarrow>\<^sub>c\<^sub>e (P,t)" 
    using a0 cptn_stepc_rtran by fastforce 
  then have step_ce:"\<Gamma>\<turnstile>\<^sub>c(((P,s)#(P,t)#l)!0)  \<rightarrow>\<^sub>e (((P,s)#(P,t)#l)!(Suc 0)) \<or>
             \<Gamma>\<turnstile>\<^sub>c (P, toSeq s)  \<rightarrow> (P,toSeq t)"
    using  step_ce_dest by fastforce  
  then have s:"s \<in> p" 
    using a1 unfolding assum_def by fastforce
  have "t \<in> p "
  using step_ce
  proof
    {assume step_e:"\<Gamma>\<turnstile>\<^sub>c ((P, s) # (P, t) # l) ! 0 \<rightarrow>\<^sub>e
          ((P, s) # (P, t) # l) ! Suc 0"
     have ?thesis 
     using a2 a1 s unfolding Sta_def assum_def 
     proof -
       have "(Suc 0 < length ((P, s) # (P, t) # l))"
         by fastforce
       then have assm:"(s, t) \<in> R"
         using s a1 step_e
         unfolding assum_def  by fastforce       
       then have R:"(s,t)\<in>R" 
         using assm  unfolding Satis_def by fastforce
       thus ?thesis 
         using a2 s  R unfolding Sta_def by blast       
     qed thus ?thesis by auto
    } 
    next
    { 
      assume step:"\<Gamma>\<turnstile>\<^sub>c (P, toSeq s) \<rightarrow> (P, toSeq t)"
      then show ?thesis
        by (simp add: mod_env_not_component) 
    } 
  qed
  thus  ?thesis by auto
qed 

lemma tl_of_assum_in_assum:
  "(\<Gamma>,(P,s)#(P,t)#l)\<in>cptn \<Longrightarrow>
   (\<Gamma>,(P,s)#(P,t)#l) \<in> assum (p,R) \<Longrightarrow>
   Sta p R  \<Longrightarrow>
   (\<Gamma>,(P,t)#l) \<in> assum (p,R)
  " 
proof -
  assume a0: "(\<Gamma>,(P,s)#(P,t)#l)\<in>cptn" and
         a1: "(\<Gamma>,(P,s)#(P,t)#l) \<in> assum (p,R)" and
         a2: "Sta p R "
  
  then have t1:"t \<in>p" 
   using same_prog_p by blast
  then have "env_tran_right \<Gamma> ((P,s)#(P,t)#l) R"
    using env_tran_right_def a1 unfolding assum_def
    by force
  then have "env_tran_right \<Gamma> ((P,t)#l) R"
    using env_tran_tail
    by blast
  thus ?thesis using t1 unfolding assum_def env_tran_right_def by auto
qed
 
lemma tl_of_assum_in_assum1:
  "(\<Gamma>,(P,s)#(Q,t)#l)\<in>cptn \<Longrightarrow>
   (\<Gamma>,(P,s)#(Q,t)#l) \<in> assum (p,R) \<Longrightarrow>
   t \<in> q \<Longrightarrow>
   (\<Gamma>,(Q,t)#l) \<in> assum (q,R) 
  " 
proof -
  assume a0: "(\<Gamma>,(P,s)#(Q,t)#l)\<in>cptn" and
         a1: "(\<Gamma>,(P,s)#(Q,t)#l) \<in> assum (p,R)" and
         a2: "t \<in> q"  
  then have "env_tran_right \<Gamma> ((P,s)#(Q,t)#l) R"
    using env_tran_right_def a1 unfolding assum_def
    by force
  then have "env_tran_right \<Gamma> ((Q,t)#l) R"
    using env_tran_tail by blast
  thus ?thesis using a2 unfolding assum_def env_tran_right_def by auto
qed
            
lemma sub_assum:
  assumes a0: "(\<Gamma>,(x#l0)@l1) \<in> assum (p,R)"
  shows "(\<Gamma>,x#l0) \<in> assum (p,R)"    
proof -
  {have p0:"snd x \<in>  p" 
    using a0 unfolding assum_def by force
  then have "env_tran_right \<Gamma> ((x#l0)@l1) R"
    using a0 unfolding assum_def 
    by (auto simp add: env_tran_right_def)
  then have env:"env_tran_right \<Gamma> (x#l0) R" 
    using env_tran_subr by blast 
  also have "snd ((x#l0)!0)  \<in>  p" 
    using p0 by fastforce
  ultimately have "snd ((x#l0)!0)  \<in> p \<and> 
                  (\<forall>i. Suc i<length (x#l0) \<longrightarrow> 
                       \<Gamma>\<turnstile>\<^sub>c((x#l0)!i)  \<rightarrow>\<^sub>e ((x#l0)!(Suc i)) \<longrightarrow>                  
                       (snd((x#l0)!i), snd((x#l0)!(Suc i))) \<in> R)"
   unfolding env_tran_right_def by auto
  }    
  then show ?thesis  unfolding assum_def by auto
qed      

lemma sub_assum_r:
  assumes a0: "(\<Gamma>,l0@x1#l1) \<in> assum (p,R)" and
          a1: "(snd x1) \<in> q"
  shows "(\<Gamma>,x1#l1) \<in> assum (q,R)"
proof -
  have "env_tran_right  \<Gamma> (l0@x1#l1) R"
    using a0 unfolding assum_def env_tran_right_def
    by fastforce
  then have "env_tran_right \<Gamma> (x1#l1) R"
    using env_tran_subl by auto
  thus ?thesis using a1 unfolding assum_def env_tran_right_def by fastforce
qed

definition Pred_wf::"nat \<Rightarrow> (('g,'l) par_state set) \<Rightarrow> bool"
  where "Pred_wf i p \<equiv> \<forall>e\<in>p. i<length (snd e)"

definition Rel_wf::"nat \<Rightarrow> (('g,'l)par_state) tran set \<Rightarrow> bool"
  where "Rel_wf i R \<equiv> \<forall>(x,y)\<in>R. i<length (snd x) \<and> i<length (snd y)"


definition comm :: 
  "((('g,'l) c_state) tran) set \<times> 
   (('g,'l) c_state set \<times> ('g,'l) c_state set) \<Rightarrow>
   'f set \<Rightarrow> 
     (('g,'l,'p,'f,'e) confs) set" where
  "comm \<equiv> \<lambda>(guar, (q,a)) F. 
            {c. 
                (\<forall>i. Suc i<length (snd c) \<longrightarrow> 
                 (fst c)\<turnstile>\<^sub>c(fst ((snd c)!i),toSeq (snd ((snd c)!i)))  \<rightarrow> 
                           (fst ((snd c)!Suc i),toSeq (snd ((snd c)!Suc i))) \<longrightarrow> 
                   ((snd ((snd c)!i)), (snd ((snd c)!Suc i))) \<in> guar) \<and> 
                 (final_glob (last (snd c))  \<longrightarrow>   fst (last (snd c)) \<notin> Fault ` F  \<longrightarrow>                 
                    ((fst (last (snd c)) = Skip \<and> 
                      snd (last (snd c)) \<in> q)) \<or>
                    (fst (last (snd c)) = Throw \<and> 
                      snd (last (snd c)) \<in> a))}"

definition comm_p :: 
  "nat \<Rightarrow> ((('g,'l) par_state) tran) set \<times> 
   (('g,'l) par_state set \<times> ('g,'l) par_state set) \<Rightarrow>
   'f set \<Rightarrow> 
     (('g,'l,'p,'f,'e) gconfs) set" where
  "comm_p i \<equiv> \<lambda>(guar, (q,a)) F. 
            {(s,p). fst s = fst p \<and> (snd s, snd p)\<in>par_state_list_rel i}  `` 
           (comm (Seq_rel i guar, (Seq_pred i q,Seq_pred i a)) F)"

lemma comm_p_dest1: "(\<Gamma>,lsp)\<in>(comm_p i (G,(q,a)) F) \<Longrightarrow> 
                    \<exists>lsc. (lsc, lsp)\<in>par_state_list_rel i \<and> 
                   (\<Gamma>,lsc)\<in>comm (Seq_rel i G, (Seq_pred i q,Seq_pred i a)) F"
  unfolding comm_p_def Image_def by auto

lemma comm_dest:
"(\<Gamma>, l)\<in> comm (G,(q,a)) F \<Longrightarrow> 
 (\<forall>i. Suc i<length l \<longrightarrow>
   \<Gamma>\<turnstile>\<^sub>c(fst (l!i), toSeq(snd (l!i)))  \<rightarrow> (fst (l!(Suc i)), toSeq(snd (l!(Suc i)))) \<longrightarrow> 
    (snd(l!i), snd(l!(Suc i))) \<in>  G)"
unfolding comm_def
  apply clarify
  by auto

lemma comm_dest1:
"(\<Gamma>, l)\<in> comm (G,(q,a)) F \<Longrightarrow>
 Suc i<length l \<Longrightarrow>
 \<Gamma>\<turnstile>\<^sub>c(fst (l!i), toSeq(snd (l!i)))  \<rightarrow> (fst (l!(Suc i)), toSeq(snd (l!(Suc i)))) \<Longrightarrow>
(snd(l!i), snd(l!(Suc i))) \<in> G"
unfolding comm_def
  apply clarify
  by auto

lemma comm_dest2:
  assumes a0: "(\<Gamma>, l)\<in> comm (G,(q,a)) F" and
          a1: "final_glob (last l)" and
          a2: "fst (last l) \<notin> Fault ` F" 
  shows  " ((fst (last l) = Skip \<and> 
            snd (last l) \<in> q)) \<or>
            (fst (last l) = Throw \<and> snd (last l) \<in>  a)"
proof -
  show ?thesis using a0 a1 a2 unfolding comm_def by auto
qed

lemma comm_des3:
  assumes a0: "(\<Gamma>, l)\<in> comm (G,(q,a)) F" and
          a1: "fst (last l) \<notin> Fault ` F"
 shows "final_glob (last l) \<longrightarrow> ((fst (last l) = Skip \<and> 
            snd (last l) \<in>  q)) \<or>
            (fst (last l) = Throw \<and> 
            snd (last l) \<in>  a)"
using a0 a1 unfolding comm_def by auto



lemma comm_pdest1:
  assumes a0:"(\<Gamma>, l)\<in> comm_p i' (G,(q,a)) F" and  
 a2:"Suc i<length l" and
 a3:"\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), fst (toSeqState i' (snd (l ! i)))) \<rightarrow>
     (fst (l ! Suc i), fst (toSeqState i' (snd (l ! Suc i))))" and a4:"Rel_wf i' G"
shows "(snd(l!i), snd(l!(Suc i))) \<in> G"
proof-
  obtain seq_l where  
    seq_l_l:"(seq_l,l)\<in>par_state_list_rel i'" and 
    seq_l_comm:"(\<Gamma>,seq_l)\<in> comm ((Seq_rel i' G ), (Seq_pred i' q), (Seq_pred i' a)) F" 
    using a0 unfolding comm_p_def by auto
  moreover have "Suc i< length seq_l" using calculation
    by (metis (no_types, lifting) Product_Type.Collect_case_prodD a2 
        fst_conv list_all2_conv_all_nth par_state_list_rel_def snd_conv)   
  moreover have "\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq ((snd (seq_l ! i)))) \<rightarrow>
                     (fst (l ! Suc i), toSeq ((snd (seq_l ! Suc i))))"
    using par_xstate_list_rel_step_c_s[OF seq_l_l] a3 calculation(3) 
       par_xstate_list_rel_dest3 seq_l_l by fastforce
  ultimately have  "(snd(seq_l!i), snd(seq_l!(Suc i))) \<in> (Seq_rel i' G )"
    using comm_dest1
    by (metis (mono_tags, lifting) Suc_lessD par_xstate_list_rel_dest3) 
  then show ?thesis 
    using a2 a4 par_xstate_list_rel_in_g_p seq_l_l \<open>Suc i < length seq_l\<close>
    unfolding Rel_wf_def by fastforce        
qed

lemma comm_pdest2:
  assumes a0: "(\<Gamma>, l)\<in> comm_p i' (G,(q,a)) F" and a1:"l\<noteq>[]" and
          a3: "final_glob_p (last l)" and 
          a4: "fst (last l) \<notin> Fault ` F" and 
          a5:"\<forall>e\<in>q. i'<length (snd e)" and a6:"\<forall>e\<in>a. i'<length (snd e)"
  shows  " ((fst (last l) = Skip \<and> 
            snd (last l) \<in> q)) \<or>
            (fst (last l) = Throw \<and> 
            snd (last l) \<in>  a)"
proof-
   obtain seq_l where  
    seq_l_l:"(seq_l,l)\<in>par_state_list_rel i'" and 
    seq_l_comm:"(\<Gamma>,seq_l)\<in> comm ((Seq_rel i' G ), (Seq_pred i' q), (Seq_pred i' a)) F" and
    len:"seq_l \<noteq>[]"
     using a0 par_xstate_list_rel_in_post_p par_xstate_list_rel_dest1 a1
     unfolding comm_p_def by fastforce
  moreover have  "fst (last seq_l) \<notin> Fault ` F"
    using a4 a1 par_xstate_list_Fault_s[OF seq_l_l]
    using par_xstate_list_rel_dest1 seq_l_l by fastforce
  moreover have "final_glob (last seq_l)"
    using a1 a3 par_xstate_list_final_s[OF seq_l_l] par_xstate_list_rel_dest1 seq_l_l by fastforce
  ultimately have  "(fst (last seq_l) = Skip \<and> snd (last seq_l) \<in> (Seq_pred i' q)) \<or>
                     (fst (last seq_l) = Throw \<and> snd (last seq_l) \<in> (Seq_pred i' a))"
    using comm_dest2[of \<Gamma> seq_l "Seq_rel i' G" "Seq_pred i' q" "Seq_pred i' a" F]
    by fastforce
  moreover have "last l =  l!(length l -1) \<and> last seq_l = seq_l ! (length l - 1)"
    by (metis a1 last_conv_nth len par_xstate_list_rel_dest1 seq_l_l)
  ultimately show ?thesis using par_xstate_list_rel_in_post_p[OF seq_l_l len _ a5] 
   par_xstate_list_rel_in_post_p[OF seq_l_l len _ a6] par_xstate_list_rel_program[OF seq_l_l]
    using a1 par_xstate_list_rel_dest1 seq_l_l by force
qed

lemma comm_pdest3:
  assumes a0: "(\<Gamma>, l)\<in> comm_p i' (G,(q,a)) F" and a1:"l\<noteq>[]" and           
          a5:"\<forall>e\<in>q. i'<length (snd e)" and a6:"\<forall>e\<in>a. i'<length (snd e)"
  shows  " final_glob_p (last l) \<longrightarrow> fst (last l) \<notin> Fault ` F \<longrightarrow>((fst (last l) = Skip \<and> 
            snd (last l) \<in>  q)) \<or>
            (fst (last l) = Throw \<and> 
            snd (last l) \<in> a)"
using comm_pdest2[OF a0 a1 _ _  a5 a6] by blast


definition comm_p1::
  "nat \<Rightarrow> ((('g,'l) par_state) tran) set \<times> 
   (('g,'l) par_state set \<times> ('g,'l) par_state set) \<Rightarrow>
   'f set \<Rightarrow> 
     (('g,'l,'p,'f,'e) gconfs) set" where
"comm_p1 i \<equiv> 
  \<lambda>(guar, (q,a)) F. 
  {(\<Gamma>,comp). 
      (\<forall>j. Suc j<length comp \<longrightarrow> 
       \<Gamma>\<turnstile>\<^sub>c(fst(comp!j), toSeq (toSeqState i (snd (comp!j))))  \<rightarrow> 
          (fst(comp!(Suc j)), toSeq (toSeqState i (snd (comp!(Suc j))))) \<longrightarrow>  
         (snd(comp!j), snd(comp!(Suc j))) \<in> guar) \<and> 
       (final_glob (fst (last comp),toSeqState i(snd (last comp)))  \<longrightarrow>  
          fst (last comp) \<notin> Fault ` F  \<longrightarrow>                  
          ((fst (last comp) = Skip \<and> snd (last comp) \<in> q)) \<or>
          (fst (last comp) = Throw \<and> snd (last comp) \<in>  a))}"

lemma c1:"\<forall>e\<in>q. i< length (snd e) \<Longrightarrow> \<forall>e\<in>a. i< length (snd e) \<Longrightarrow> Rel_wf i G \<Longrightarrow> lp\<noteq>[] \<Longrightarrow> 
          (\<Gamma>,lp) \<in> comm_p i (G,(q,a)) F \<Longrightarrow> (\<Gamma>,lp) \<in> comm_p1 i (G,(q,a)) F"
  unfolding comm_p1_def  Let_def split_beta  Seq_rel_def Seq_pred_def 
  apply (auto simp add: comm_pdest1)   
  using LocalRG_HoareDef.final_eq comm_pdest2 by blast+

lemma c2:"\<forall>e\<in>q. i< length (snd e) \<Longrightarrow> \<forall>e\<in>a. i< length (snd e) \<Longrightarrow> lp\<noteq>[] \<Longrightarrow>
         \<forall>j<length lp.  i<length (snd ( snd (lp!j))) \<Longrightarrow>           
          (\<Gamma>,lp) \<in> comm_p1 i (G,(q,a)) F \<Longrightarrow> (\<Gamma>,lp) \<in> comm_p i (G,(q,a)) F"
proof (auto simp add: comm_p_def  Let_def split_beta Image_def   comm_def)
  assume a0:"\<forall>e\<in>q. i < length (snd e)" and a1:"\<forall>e\<in>a. i < length (snd e)" and           
         a2:"lp \<noteq> []" and a3:"(\<Gamma>, lp) \<in> comm_p1 i (G, q, a) F" and
         a5:"\<forall>j<length lp. i < length (snd (snd (lp ! j))) "        
  then have xstate_rel:"(toSeqCptn i lp, lp)\<in> (par_state_list_rel i)"
    by (simp add: toSeqCptn_in_rel)  
  moreover { let ?b = "toSeqCptn i lp"   
    { fix j 
      assume a01:"Suc j < length ?b" and
            a02:"\<Gamma>\<turnstile>\<^sub>c (fst (?b ! j), toSeq (snd (?b ! j))) \<rightarrow> (fst (?b ! Suc j), toSeq (snd (?b ! Suc j)))"
      then have a01':"Suc j < length lp" and "\<Gamma>\<turnstile>\<^sub>c (fst (lp ! j), toSeq (toSeqState i (snd (lp ! j)))) \<rightarrow> 
                      (fst (lp ! Suc j), toSeq (toSeqState i (snd (lp ! Suc j))))"
        using  xstate_rel apply (simp add: par_xstate_list_rel_dest1) 
        using par_xstate_list_rel_step_c_p xstate_rel a01 a02 by blast
      then have "(snd (lp ! j),  snd (lp ! Suc j)) \<in> G" 
        using a3 unfolding comm_p1_def split_beta  by auto
      then have"(snd (?b ! j), snd (?b ! Suc j)) \<in> Seq_rel i G"
        using par_xstate_list_rel_in_g_s[OF xstate_rel a01] by auto
    } note c1 = this
    moreover { 
      assume a01:"ComputationConGlob.final_glob (last ?b)"              
      assume a00:"fst (last ?b) \<notin> Fault ` F"                    
      then have a00':"fst (last lp) \<notin> Fault ` F"
        using par_xstate_list_Fault_set_p[OF xstate_rel _ a00]
            a2 par_xstate_list_rel_dest1 xstate_rel by force
      then have "final_glob_p (last lp)"
        using par_xstate_list_final_p[OF xstate_rel _ a01] a2
        using par_xstate_list_rel_dest1 xstate_rel by fastforce 
      then have "final_glob (fst (last lp), toSeqState i (snd (last lp)))"
        using LocalRG_HoareDef.final_eq \<open>final_glob_p (last lp)\<close> by blast
      then have "fst (last  lp) = LanguageCon.com.Skip \<and> snd (last lp) \<in> q  \<or>
          fst (last lp) = LanguageCon.com.Throw \<and> snd (last lp) \<in> a "
        using a3 unfolding comm_p1_def split_beta using a01 a00
        using LocalRG_HoareDef.final_eq a00' by auto         
       then have "fst (last ?b) = LanguageCon.com.Skip \<and> snd (last ?b) \<in>  Seq_pred i q  \<or>
          fst (last ?b) = LanguageCon.com.Throw \<and> snd (last ?b) \<in>  Seq_pred i a "
         using par_xstate_list_rel_in_post_s[OF xstate_rel _] a2 
         by (auto simp add: last_conv_nth toSeqCptn_def)
    }         
    ultimately have "
         (\<forall>ia. Suc ia < length ?b \<longrightarrow>
               \<Gamma>\<turnstile>\<^sub>c (fst (?b ! ia), toSeq (snd (?b ! ia))) \<rightarrow> (fst (?b ! Suc ia), toSeq (snd (?b ! Suc ia))) \<longrightarrow>
               (snd (?b ! ia), snd (?b ! Suc ia)) \<in>  Seq_rel i G) \<and>
         (ComputationConGlob.final_glob (last ?b) \<longrightarrow> fst (last ?b) \<notin> Fault ` F \<longrightarrow>
          fst (last ?b) = LanguageCon.com.Skip \<and> snd (last ?b) \<in> Seq_pred i q  \<or>
          fst (last ?b) = LanguageCon.com.Throw \<and>  snd (last ?b) \<in>  Seq_pred i a)" 
      by auto
  } ultimately show "\<exists>b. 
         (\<forall>ia. Suc ia < length b \<longrightarrow>
               \<Gamma>\<turnstile>\<^sub>c (fst (b ! ia), fst (snd (b ! ia))) \<rightarrow> (fst (b ! Suc ia), fst (snd (b ! Suc ia))) \<longrightarrow>
               (snd (b ! ia), snd (b ! Suc ia)) \<in> Seq_rel i G) \<and>
         (ComputationConGlob.final_glob (last b) \<longrightarrow> (fst (last b) \<notin> Fault ` F \<longrightarrow>
          fst (last b) = LanguageCon.com.Skip \<and> snd (last b) \<in> Seq_pred i q \<or>
          fst (last b) = LanguageCon.com.Throw \<and> snd (last b) \<in>  Seq_pred i a)) \<and>
        (b, lp) \<in> par_state_list_rel i"
    by fastforce
  
qed

definition comm1 :: 
  "((('g,'l) c_state) tran) set \<times> 
   (('g,'l) c_state set \<times> ('g,'l) c_state set) \<Rightarrow>
   'f set \<Rightarrow> 
     (('g,'l,'p,'f,'e) confs) set" where
  "comm1 \<equiv> \<lambda>(guar, (q,a)) F. 
            {(\<Gamma>,comp).
                (\<forall>i. Suc i<length comp \<longrightarrow> 
                 \<Gamma>\<turnstile>\<^sub>c(fst(comp!i), toSeq (snd (comp!i)))  \<rightarrow> 
                    (fst(comp!(Suc i)), toSeq (snd (comp!(Suc i)))) \<longrightarrow>  
                   (snd(comp!i), snd(comp!(Suc i))) \<in> guar) \<and> 
                 (final_glob (last comp)  \<longrightarrow>  fst (last comp) \<notin> Fault ` F  \<longrightarrow>                   
                    ((fst (last comp) = Skip \<and> snd (last comp) \<in>  q)) \<or>
                    (fst (last comp) = Throw \<and> snd (last comp) \<in>  a))}"


lemma commI:
  assumes a0:"
             (\<forall>i. 
                 Suc i<length l \<longrightarrow> 
                 \<Gamma>\<turnstile>\<^sub>c(fst (l!i), toSeq(snd (l!i)))  \<rightarrow> (fst (l!(Suc i)), toSeq(snd (l!(Suc i)))) \<longrightarrow>                                               
                   (snd(l!i), snd(l!(Suc i))) \<in> G) \<and> 
                 (final_glob (last l)  \<longrightarrow>  fst (last l) \<notin> Fault ` F \<longrightarrow>                 
                    ((fst (last l) = Skip \<and> snd (last l) \<in>  q)) \<or>
                    (fst (last l) = Throw \<and> snd (last l) \<in>  a))"
shows "(\<Gamma>,l)\<in>comm (G, (q,a)) F"
using a0  unfolding comm_def
apply clarify
by simp

lemma comm_conseq:
  "(\<Gamma>,l) \<in> comm(G', (q',a')) F \<Longrightarrow>
       G' \<subseteq> G \<and>
       q' \<subseteq> q \<and>
       a' \<subseteq> a \<Longrightarrow>
      (\<Gamma>,l) \<in> comm (G,(q,a)) F"
proof -
  assume a0:"(\<Gamma>,l) \<in> comm(G', (q',a')) F" and
         a1:" G' \<subseteq> G  \<and>
        q' \<subseteq> q \<and>
        a' \<subseteq> a"
  {    
    have l:"(\<forall>i. 
           Suc i<length l \<longrightarrow> 
           \<Gamma>\<turnstile>\<^sub>c(fst (l!i), toSeq(snd (l!i)))  \<rightarrow> (fst (l!(Suc i)), toSeq(snd (l!(Suc i)))) \<longrightarrow>                                          
             (snd(l!i), snd(l!(Suc i))) \<in> G)"
    proof -
      {fix i ns ns'
      assume a00:"Suc i<length l" and
             a11:"\<Gamma>\<turnstile>\<^sub>c(fst (l!i), toSeq(snd (l!i)))  \<rightarrow> (fst (l!(Suc i)), toSeq(snd (l!(Suc i))))"             
      have "(snd(l!i), snd(l!(Suc i))) \<in>  G" 
      proof -
        have "(snd(l!i), snd(l!(Suc i))) \<in>  G'"
        using comm_dest1 [OF a0  a00 a11]  by auto
        thus ?thesis using a1 unfolding Satis_def by fastforce
      qed
      } thus ?thesis by auto
    qed  
    have "(final_glob (last l)  \<longrightarrow> fst (last l) \<notin> Fault ` F \<longrightarrow>
                    ((fst (last l) = Skip \<and> snd (last l) \<in>  q)) \<or>
                    (fst (last l) = Throw \<and> snd (last l) \<in>  a))"
    proof -
      {assume a33:"final_glob (last l)" and a32: "fst (last l) \<notin> Fault ` F"
      then have "((fst (last l) = Skip \<and> snd (last l) \<in> q')) \<or>
                    (fst (last l) = Throw \<and> snd (last l) \<in>  a')"
      using comm_dest2[OF a0 a33 a32 ] by auto
      then have "((fst (last l) = Skip \<and> snd (last l) \<in>  q)) \<or>
                    (fst (last l) = Throw \<and> snd (last l) \<in> a)"
      using a1 by fastforce
     } thus ?thesis by auto
    qed
    note res1 = conjI[OF l this] 
  } thus ?thesis unfolding comm_def by simp
qed   

lemma  no_comp_tran_no_final_comm:
  assumes a0:"\<forall>i<length l. \<not> final_glob (l!i)" and
          a1:"\<forall>i<length l. fst (l!i) = C" and a2:"length l>0"
        shows "(\<Gamma>,l)\<in>comm(G, (q,a)) F"
proof-
  have n_comp:"\<forall>i. Suc i < length l \<longrightarrow> 
                  \<not> (\<Gamma>\<turnstile>\<^sub>c(fst (l!i), toSeq(snd (l!i)))  \<rightarrow> 
                         (fst (l!(Suc i)), toSeq(snd (l!(Suc i)))))" 
    using a1 by (metis Suc_lessD mod_env_not_component)
  {
    {fix i
      assume "Suc i< length(l)" and 
             "\<Gamma>\<turnstile>\<^sub>c(fst (l!i), toSeq(snd (l!i)))  \<rightarrow> (fst (l!(Suc i)), toSeq(snd (l!(Suc i))))"  
      then have False using n_comp by auto
    }
    moreover {
      assume "final_glob (last l)" and "fst (last l) \<notin> Fault ` F" 
      then have False using a0 a2
        using last_conv_nth by force
      }
      ultimately have ?thesis unfolding comm_def by auto
  } thus ?thesis unfolding comm_def by auto   
qed
  
definition com_validity :: 
  "('g\<times>'l,'p,'f,'e) body \<Rightarrow>  'f set \<Rightarrow> ('g\<times>'l,'p,'f,'e) com \<Rightarrow> 
    ('g,'l) c_state set \<Rightarrow> ((('g,'l) c_state) tran) set \<Rightarrow>  ((('g,'l) c_state) tran) set \<Rightarrow>  
    ('g,'l) c_state set \<Rightarrow>  ('g,'l) c_state set \<Rightarrow>  bool" 
    ("_ \<Turnstile>\<^bsub>'/_\<^esub>/ _ sat [_,_, _, _,_]" [61,61,0,0,0,0,0,0] 25) where
  "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat [p, R, G, q,a] \<equiv> 
   \<forall>s. cp \<Gamma> Pr s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"

definition com_cvalidity::
 "('g\<times>'l,'p,'f,'e) body \<Rightarrow>
    ('g,'l,'p) c_sextuple set \<Rightarrow>
    'f set \<Rightarrow>
    ('g\<times>'l,'p,'f,'e) com \<Rightarrow> 
    ('g,'l) c_state set \<Rightarrow>          
    ((('g,'l) c_state) tran) set \<Rightarrow> 
    ((('g,'l) c_state) tran) set \<Rightarrow>  
    ('g,'l) c_state set \<Rightarrow> 
    ('g,'l) c_state set \<Rightarrow>
      bool" 
    ("_,_ \<Turnstile>\<^bsub>'/_\<^esub>/ _ sat [_,_, _, _,_]" [61,61,0,0,0,0,0,0] 10) where
  "\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> Pr sat [p, R, G, q,a] \<equiv> 
   (\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]) \<longrightarrow> 
     \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat [p, R, G, q,a]"

definition com_validityn :: 
  "('g\<times>'l,'p,'f,'e) body \<Rightarrow> nat \<Rightarrow> 'f set  \<Rightarrow> ('g\<times>'l,'p,'f,'e) com \<Rightarrow> 
    ('g,'l) c_state set \<Rightarrow> ((('g,'l) c_state) tran) set \<Rightarrow>  ((('g,'l) c_state) tran) set \<Rightarrow>  
    ('g,'l) c_state set \<Rightarrow>  ('g,'l) c_state set \<Rightarrow>  bool" 
    ("_ \<Turnstile>_\<^bsub>'/_\<^esub>/ _ sat [_,_, _, _,_]" [61,0,60,0,0,0,0,0,0] 45) where
  "\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> Pr sat [p, R, G, q,a] \<equiv> 
   \<forall>s. cpn n \<Gamma> Pr s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"

definition com_cvalidityn::
 "('g\<times>'l,'p,'f,'e) body \<Rightarrow>
    ('g,'l,'p) c_sextuple set \<Rightarrow> nat \<Rightarrow>
    'f set \<Rightarrow>
    ('g\<times>'l,'p,'f,'e) com \<Rightarrow> 
    ('g,'l) c_state set \<Rightarrow>          
    ((('g,'l) c_state) tran) set \<Rightarrow> 
    ((('g,'l) c_state) tran) set \<Rightarrow>  
    ('g,'l) c_state set \<Rightarrow> 
    ('g,'l) c_state set \<Rightarrow>
      bool" 
    ("_,_ \<Turnstile>_\<^bsub>'/_\<^esub>/ _ sat [_,_, _, _,_]" [61,60,0,0,0,0,0,0,0] 45) where
  "\<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> Pr sat [p, R, G, q,a] \<equiv> 
   (\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]) \<longrightarrow> 
     \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> Pr sat [p, R, G, q,a]"

(* definition comp_validity :: 
  "('g\<times>'l,'p,'f,'e) body \<Rightarrow> 'f set \<Rightarrow> ('g\<times>'l,'p,'f,'e) com \<Rightarrow>  nat \<Rightarrow> 
    ('g,'l) par_state set \<Rightarrow> ((('g,'l) par_state) tran) set \<Rightarrow>  ((('g,'l) par_state) tran) set \<Rightarrow>  
    ('g,'l) par_state set \<Rightarrow>  ('g,'l) par_state set \<Rightarrow>  bool" 
    ("_ \<Turnstile>\<^bsub>'/_\<^esub>/ _ sat _ [_,_, _, _,_]" [61,60,0,0,0,0,0,0] 45) where
  "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat i [p, R, G, q,a] \<equiv> 
   \<forall>s. {(s, p). fst p = fst s \<and>  (snd s, snd p)\<in>par_state_list_rel i} `` (cp \<Gamma> Pr s) \<inter> 
       assum_p i (p, R) \<subseteq> comm_p i (G, (q,a)) F" *)

definition comp_validity :: 
  "('g\<times>'l,'p,'f,'e) body \<Rightarrow> 'f set \<Rightarrow> ('g\<times>'l,'p,'f,'e) com \<Rightarrow>  nat \<Rightarrow> 
    ('g,'l) par_state set \<Rightarrow> ((('g,'l) par_state) tran) set \<Rightarrow>  ((('g,'l) par_state) tran) set \<Rightarrow>  
    ('g,'l) par_state set \<Rightarrow>  ('g,'l) par_state set \<Rightarrow>  bool" 
    ("_ \<Turnstile>\<^bsub>'/_\<^esub>/ _ sat _ [_,_, _, _,_]" [61,60,60,60,60,60,60,60] 25) where
  "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat i [p, R, G, q,a] \<equiv> 
   \<forall>s. {(s, p). fst p = fst s \<and>  (snd s, snd p)\<in>par_state_list_rel i} `` ((cp \<Gamma> Pr s) \<inter> 
       assum (Seq_pred i p, Seq_rel i R)) \<subseteq> comm_p i (G, (q,a)) F"


definition comp_cvalidity::
 "('g\<times>'l,'p,'f,'e) body \<Rightarrow>
    ('g,'l,'p) p_sextuple set \<Rightarrow> 
    'f set \<Rightarrow>
    ('g\<times>'l,'p,'f,'e) com \<Rightarrow> nat \<Rightarrow>
    ('g,'l) par_state set \<Rightarrow> ((('g,'l) par_state) tran) set \<Rightarrow>  
    ((('g,'l) par_state) tran) set \<Rightarrow>  
    ('g,'l) par_state set \<Rightarrow>  ('g,'l) par_state set \<Rightarrow>  bool" 
    ("_,_ \<Turnstile>\<^bsub>'/_\<^esub>/ _ sat _ [_,_, _, _,_]" [61,61,0,0,0,0,0,0] 10) where
  "\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> Pr sat i [p, R, G, q,a] \<equiv> 
   (\<forall>(c,p,R,G,q,a)\<in> \<Theta>. Pred_wf i p \<and> Rel_wf i R \<and>  Rel_wf i G \<and> Pred_wf i q \<and>  Pred_wf i a \<longrightarrow> 
     (\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat i [p, R, G, q,a])) \<longrightarrow> 
     \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat i [p, R, G, q,a]"



definition seq_proc_spec::"nat \<Rightarrow> ('g,'l,'p) p_sextuple set \<Rightarrow> ('g,'l,'p) c_sextuple set"
("\<^sub>_\<^sub>s_" [80,98]) 
where "seq_proc_spec i \<Theta> \<equiv> 
  (\<lambda>(c,p,R,G,q,a).
                  (c, Seq_pred i p, Seq_rel i R, Seq_rel i G, Seq_pred i q, Seq_pred i a)) ` 
                  {(c,p,R,G,q,a). Pred_wf i p \<and> Rel_wf i R \<and> Rel_wf i G \<and> Pred_wf i q \<and> Pred_wf i a \<and> 
                                  (c,p,R,G,q,a)\<in>\<Theta>}" 

definition comp_validityn :: 
  "('g\<times>'l,'p,'f,'e) body \<Rightarrow> nat \<Rightarrow> 'f set  \<Rightarrow> ('g\<times>'l,'p,'f,'e) com \<Rightarrow> nat\<Rightarrow>
   ('g,'l) par_state set \<Rightarrow> ((('g,'l) par_state) tran) set \<Rightarrow>  ((('g,'l) par_state) tran) set \<Rightarrow>  
    ('g,'l) par_state set \<Rightarrow>  ('g,'l) par_state set \<Rightarrow>  bool" 
    ("_ \<Turnstile>_\<^bsub>'/_\<^esub>/ _ sat _ [_,_, _, _,_]" [61,0,60,0,0,0,0,0,0] 45) where
  "\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> Pr sat i [p, R, G, q,a] \<equiv> 
   \<forall>s. {(s, p). fst p = fst s \<and>  (snd s, snd p)\<in>par_state_list_rel i} `` (cpn n \<Gamma> Pr s) \<inter> assum_p i (p, R) \<subseteq> comm_p i (G, (q,a)) F"
                                                                            
definition comp_cvalidityn::
 "('g\<times>'l,'p,'f,'e) body \<Rightarrow>
    ('g,'l,'p) p_sextuple set \<Rightarrow> nat \<Rightarrow>
    'f set \<Rightarrow>
    ('g\<times>'l,'p,'f,'e) com \<Rightarrow> nat \<Rightarrow>
    ('g,'l) par_state set \<Rightarrow> ((('g,'l) par_state) tran) set \<Rightarrow>  
    ((('g,'l) par_state) tran) set \<Rightarrow>  
    ('g,'l) par_state set \<Rightarrow>  ('g,'l) par_state set \<Rightarrow>  bool" 
    ("_,_ \<Turnstile>_\<^bsub>'/_\<^esub>/ _ sat _ [_,_, _, _,_]" [61,60,0,0,0,0,0,0,0] 45) where
  "\<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> Pr sat i [p, R, G, q,a] \<equiv> 
   (\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat i [p, R, G, q,a]) \<longrightarrow> 
     \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> Pr sat i [p, R, G, q,a]"

lemma com_valid_iff_nvalid:"(\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat [p, R, G, q,a]) = (\<forall>n. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> Pr sat [p, R, G, q,a])"
  apply (simp only: com_validity_def com_validityn_def cp_def cpn_def cptn_eq_cptn_mod_nest)
  by fast

lemma com_cnvalid_to_cvalid: 
    "\<forall>n. (\<Gamma>,\<Theta>\<Turnstile>n\<^bsub>/F\<^esub> Pr sat [p, R, G, q,a]) \<Longrightarrow> 
         (\<Gamma>,\<Theta>\<Turnstile>\<^bsub>/F\<^esub> Pr sat [p, R, G, q,a])"
  apply (unfold com_cvalidityn_def com_cvalidity_def com_valid_iff_nvalid [THEN eq_reflection])
  by fast


lemma validityp_to_validity:
      "\<forall>e\<in>p. i< length (snd e) \<Longrightarrow> 
       \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat i [p, R, G, q,a] \<Longrightarrow> 
       \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat [Seq_pred i p, Seq_rel i R, Seq_rel i G, Seq_pred i q, Seq_pred i a]"
  unfolding com_validity_def 
proof-
  assume a00:"\<forall>e\<in>p. i< length (snd e)" and
         a01:"\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat i [p, R, G, q,a]"
  then have a00s:"\<forall>e\<in> Seq_pred i p. i\<le> length (snd e)"
    unfolding Seq_pred_def apply auto
    by (metis Suc_less_eq diff_Suc_1 diff_le_mono len_toSeqState less_Suc_eq_le)
  {fix s ls
    assume a000:"(\<Gamma>,ls) \<in>  cp \<Gamma> Pr s \<and> (\<Gamma>,ls)\<in>assum (Seq_pred i p, Seq_rel i R)"
    then have  "(\<Gamma>,ls)\<in>cptn \<and> ls!0 = (Pr, s) \<and> 
                           (s  \<in> Seq_pred i p \<and> i\<le> length (snd s))"
      unfolding cp_def assum_def Let_def split_beta using a00s by auto
    then have  all:"\<forall>j<length ls. i\<le>length (snd (snd (ls!j)))"       
      using a00 unfolding cp_def
      using cptn_length_locs_lesseq_i by fastforce    
    have "(\<Gamma>, toParCptn i ls)\<in> {(s, p). fst p = fst s \<and>  
       (snd s, snd p)\<in>par_state_list_rel i} `` ((cp \<Gamma> Pr s) \<inter> 
       assum (Seq_pred i p, Seq_rel i R))"
      unfolding Image_def  using toParCptn_in_rel[OF all] a000 apply auto
      by (metis Int_iff fst_conv snd_conv)   
    then have  "(\<Gamma>, toParCptn i ls)\<in> comm_p i (G, (q,a)) F"
      using a01 unfolding comp_validity_def by fastforce
    then have "(\<Gamma>,ls)\<in>  comm (Seq_rel i G, Seq_pred i q, Seq_pred i a) F "
      unfolding comm_p_def Let_def split_beta Image_def apply auto 
      using eq_xstate_related_list all by blast
  } 
  then show "\<forall>s. cp \<Gamma> Pr s \<inter> assum (Seq_pred i p, Seq_rel i R) \<subseteq> 
                 comm (Seq_rel i G, Seq_pred i q, Seq_pred i a) F"    
    by (auto simp add: cp_def)
qed

lemma validity_to_validityp:
     " \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat [Seq_pred i p, Seq_rel i R, Seq_rel i G, Seq_pred i q, Seq_pred i a] \<Longrightarrow>
       \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat i [p, R, G, q,a]"
  unfolding comp_validity_def Image_def comm_p_def
proof(auto)
  fix s \<Gamma>1 ls lsp
  assume  a01:"\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat [Seq_pred i p,Seq_rel i R, Seq_rel i G, Seq_pred i q,Seq_pred i a]" and
         a02:"(\<Gamma>1, ls) \<in> cp \<Gamma> Pr s" and 
         a03:"(\<Gamma>1, ls) \<in> assum (Seq_pred i p, Seq_rel i R)" and
         a04:"(ls, lsp) \<in> par_state_list_rel i"
  moreover have  "(\<Gamma>1, ls) \<in> comm (Seq_rel i G, Seq_pred i q, Seq_pred i a) F" 
    using  calculation unfolding com_validity_def
    by blast
  ultimately show "\<exists>x\<in>comm (Seq_rel i G, Seq_pred i q, Seq_pred i a) F. 
                    fst x = \<Gamma>1 \<and> (snd x, lsp) \<in> par_state_list_rel i"
    by force 
qed

lemma validity_eq_validityp:
     "\<forall>e\<in>p. i< length (snd e) \<Longrightarrow> 
       (\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat [Seq_pred i p, Seq_rel i R, Seq_rel i G, Seq_pred i q, Seq_pred i a]) =
       (\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat i [p, R, G, q,a])"
  using validity_to_validityp validityp_to_validity com_cvalidity_def by auto


lemma sextuple_validity_to_validity_pair:
  assumes 
      a1:"\<forall>(c, p, R, G, q, a)\<in>(seq_proc_spec i \<Theta>). \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> LanguageCon.com.Call c sat [p,R, G, q,a]"
    shows"\<forall>(c, p, R, G, q, a)\<in> \<Theta>. Pred_wf i p \<and> Rel_wf i R \<and> 
                 Rel_wf i G \<and> Pred_wf i q \<and>  Pred_wf i a \<longrightarrow> 
             \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> LanguageCon.com.Call c sat i [p,R, G, q,a]"
proof-
  { fix c p R G q a
    assume a00:"(c, p, R, G, q, a)\<in> \<Theta>" and 
          a01:" Pred_wf i p \<and> Rel_wf i R \<and>  Rel_wf i G \<and> Pred_wf i q \<and>  Pred_wf i a"
    then have  "Pred_wf i p \<and> Rel_wf i R \<and> Rel_wf i G \<and> Pred_wf i q \<and> Pred_wf i a \<and>
                (c, Seq_pred i p, Seq_rel i R, Seq_rel i G, Seq_pred i q, Seq_pred i a)\<in>
                (seq_proc_spec i \<Theta>)" unfolding seq_proc_spec_def
      using image_iff unfolding image_def apply auto by fastforce 
    then have  "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> LanguageCon.com.Call c sat [Seq_pred i p, Seq_rel i R, Seq_rel i G, Seq_pred i q,Seq_pred i a]"
      using a1 a01 by auto
    then have "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> LanguageCon.com.Call c sat i [p,R, G, q,a]"
      using validity_eq_validityp a01 a00 unfolding Pred_wf_def by fastforce
  } thus ?thesis by auto
qed

lemma sextuple_validityp_to_validity:
  assumes 
    a1:"\<forall>(c, p, R, G, q, a)\<in> \<Theta>. Pred_wf i p \<and> Rel_wf i R \<and>  Rel_wf i G \<and> 
                                Pred_wf i q \<and>  Pred_wf i a \<longrightarrow>  
                \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> LanguageCon.com.Call c sat i [p,R, G, q,a]"
    shows"\<forall>(c, p, R, G, q, a)\<in>(seq_proc_spec i \<Theta>). \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> LanguageCon.com.Call c sat [p,R, G, q,a]"
  unfolding seq_proc_spec_def image_def split_beta
proof auto
  {fix c p R G q a
    assume a00':"Pred_wf i p \<and> Rel_wf i R \<and>  Rel_wf i G \<and> Pred_wf i q \<and>  Pred_wf i a" and
                "(c, p, R, G, q, a)\<in>\<Theta>"
    then have  "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> LanguageCon.com.Call c sat i [p, R,  G,  q,  a]"
      using a1  by auto
    then have "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> LanguageCon.com.Call c sat  
           [Seq_pred i p,Seq_rel i R, Seq_rel i G, Seq_pred i q,Seq_pred i a]"
      using validity_eq_validityp a00'
      by (simp add: validity_eq_validityp Pred_wf_def)     
  }
  then show "\<And>ae af ag ah ai ba.
       \<lbrakk>Pred_wf i af; Rel_wf i ag; Rel_wf i ah; Pred_wf i ai; Pred_wf i ba; (ae, af, ag, ah, ai, ba) \<in> \<Theta>\<rbrakk>
       \<Longrightarrow> \<Gamma> \<Turnstile>\<^bsub>/F\<^esub>
           LanguageCon.com.Call ae sat [Seq_pred i af,Seq_rel i ag, Seq_rel i ah, Seq_pred i ai,Seq_pred i ba]"
    by auto
qed

lemma cvalidityp_to_cvalidity: "\<forall>e\<in>p. i< length (snd e) \<Longrightarrow>
       (\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> Pr sat i [p, R, G, q,a]) \<Longrightarrow>
       (\<Gamma>,(seq_proc_spec i \<Theta>) \<Turnstile>\<^bsub>/F\<^esub> Pr sat [Seq_pred i p, Seq_rel i R, Seq_rel i G, Seq_pred i q, Seq_pred i a])" 
  unfolding com_cvalidity_def   
proof(clarify)
  assume a1:"\<forall>e\<in>p. i< length (snd e)" and
         a2:"\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> Pr sat i [p,R, G, q,a]" and
         "\<forall>(c, p, R, G, q, a)\<in>(seq_proc_spec i \<Theta>). \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> LanguageCon.com.Call c sat [p,R, G, q,a]"  
  then have "\<forall>(c, p, R, G, q, a)\<in> \<Theta>.  Pred_wf i p \<and> Rel_wf i R \<and>  Rel_wf i G \<and> Pred_wf i q \<and>  Pred_wf i a \<longrightarrow>
         \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> LanguageCon.com.Call c sat i [p,R, G, q,a]" 
    using sextuple_validity_to_validity_pair by fastforce
  then have  "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat i [p, R, G, q,a]" using a2 unfolding comp_cvalidity_def by auto
  then show "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat [Seq_pred i p,Seq_rel i R, Seq_rel i G, Seq_pred i q,Seq_pred i a]"
    using  validity_eq_validityp[OF a1] by fastforce      
qed

lemma cvalidity_to_cvalidityp: 
      "\<forall>e\<in>p. i< length (snd e) \<Longrightarrow>       
       (\<Gamma>,(seq_proc_spec i \<Theta>) \<Turnstile>\<^bsub>/F\<^esub> Pr sat [Seq_pred i p, Seq_rel i R, Seq_rel i G, Seq_pred i q, Seq_pred i a])  \<Longrightarrow>
       (\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> Pr sat i [p, R, G, q,a])" 
  unfolding comp_cvalidity_def   
proof(clarify)
  assume a0:"\<forall>e\<in>p. i < length (snd e)" and 
         a2:"(\<Gamma>,(seq_proc_spec i \<Theta>) \<Turnstile>\<^bsub>/F\<^esub> Pr sat [Seq_pred i p, Seq_rel i R, Seq_rel i G, Seq_pred i q, Seq_pred i a]) " and
         a3:"\<forall>(c, p, R, G, q, a)\<in>\<Theta>. Pred_wf i p \<and> Rel_wf i R \<and> Rel_wf i G \<and> Pred_wf i q \<and> Pred_wf i a \<longrightarrow> 
                 \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> LanguageCon.com.Call c sat i [p,R, G, q,a]"           
  then have "\<forall>(c, p, R, G, q, a)\<in>(seq_proc_spec i \<Theta>). \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> LanguageCon.com.Call c sat [p,R, G, q,a]" 
    using sextuple_validityp_to_validity[OF a3] by fastforce
  then have  "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat [Seq_pred i p, Seq_rel i R, Seq_rel i G, Seq_pred i q, Seq_pred i a]" 
    using a2 unfolding com_cvalidity_def by fastforce
  then show "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat i [p,R, G, q,a]"
    using a0 validity_eq_validityp by fastforce      
qed

lemma cvalidity_eq_cvalidityp:
 "\<forall>e\<in>p. i< length (snd e) \<Longrightarrow>       
  (\<Gamma>,(seq_proc_spec i \<Theta>) \<Turnstile>\<^bsub>/F\<^esub> Pr sat 
       [Seq_pred i p, Seq_rel i R, Seq_rel i G, Seq_pred i q, Seq_pred i a]) =
  (\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> Pr sat i [p, R, G, q,a])" 
  using cvalidity_to_cvalidityp cvalidityp_to_cvalidity by auto


lemma not_fault_ref:"(par_state_list_rel i)\<inverse> `` {x. x\<noteq>[] \<longrightarrow> fst (last x) \<notin> Fault ` F} \<subseteq> 
                      {x. x\<noteq>[] \<longrightarrow> fst (last x) \<notin> Fault ` F}" 
  unfolding par_state_list_rel_def   
    apply auto
    by (metis (mono_tags, lifting) diff_less image_eqI last_conv_nth length_greater_0_conv 
         list_all2_conv_all_nth  zero_less_one)


lemma not_all_fault_ref:" par_state_list_rel m `` {x. \<forall>i<length x. fst (x ! i) \<notin> Fault ` F}
    \<subseteq> {x. \<forall>i<length x. fst (x ! i) \<notin> Fault ` F}"
  unfolding par_state_list_rel_def
   apply auto
   by (metis (mono_tags, lifting)  list_all2_conv_all_nth rev_image_eqI)

lemma assum_p_in_assum:
      "\<forall>s\<in> (Par_pred m P). m < length (snd s) \<Longrightarrow>
       (par_state_list_rel m)\<inverse> `` 
            {cps. cps\<noteq>[] \<longrightarrow> (\<Gamma>,cps) \<in>(assum_p1 m ((Par_pred m P),((Par_rel m (R)))))} \<subseteq>  
                                      {cps. cps\<noteq>[] \<longrightarrow> (\<Gamma>,cps)\<in>(assum (P,R))}"
  unfolding par_state_list_rel_def 
proof(auto)
  fix x xa
  assume 
    P_less_m:"\<forall>s\<in> (Par_pred m P). m < length (snd s)" and
    list_all:"list_all2 (\<lambda>s p. fst s = fst p \<and> (snd s, snd p) \<in> par_state_rel m) x xa" and 
         a0:"(\<Gamma>, xa) \<in> assum_p1 m (Par_pred m P, Par_rel m R)" and a1:" x \<noteq> []"
  then show "(\<Gamma>, x) \<in> assum (P, R)"
    unfolding assum_def assum_p1_def split_beta
  proof(auto)    
    assume a01:"snd (xa ! 0) \<in> Par_pred m P"
    then have "(snd (x ! 0), snd (xa ! 0)) \<in> par_state_rel m"
      using list_all unfolding par_state_list_rel_def  
      by (auto dest: list_all2_nthD[of _ _ _ 0] simp add: a1)     
    moreover have len:"m<length (snd (snd (xa ! 0)))" 
      using calculation a01 
      unfolding par_state_list_rel_def par_state_rel_def
      using par_seq_rel_i_length par_seq_rel_length
      using P_less_m a01 by auto
    ultimately have"snd(x!0) =  (toSeqState m (snd (xa ! 0)))" 
      using a01   unfolding par_state_rel_def       
      by (fastforce intro: par_seq_rel_seq)
    moreover have "toSeqState m (snd (xa ! 0)) \<in> P" using a01 len unfolding Par_pred_def apply auto
      by (metis Seq2Par eq_toPar prod.exhaust_sel)     
    ultimately show "snd (x ! 0) \<in>  P" using a01  a1 
      unfolding  par_seq_rel_def Par_pred_def toParState_def toSeqState_def split_beta
      by auto    
  next 
    fix  i 
    assume a00:"\<forall>i. Suc i < length xa \<longrightarrow>
                \<Gamma>\<turnstile>\<^sub>c (fst (xa ! i), toSeqState m (snd (xa ! i))) \<rightarrow>\<^sub>e
                  (fst (xa ! Suc i), toSeqState m (snd (xa ! Suc i))) \<longrightarrow>
            (snd (xa ! i), snd (xa ! Suc i)) \<in> Par_rel m R" and           
           a01:"snd (xa ! 0) \<in> Par_pred m P" and 
           a02:"Suc i < length x" and 
           a03:"\<Gamma>\<turnstile>\<^sub>c (x ! i) \<rightarrow>\<^sub>e (x ! Suc i)"
     then have rel_i:"(snd (x ! i), snd (xa ! i)) \<in> par_state_rel m" and "fst (x!i) = fst (xa!i)"
       using list_all unfolding par_state_list_rel_def  
       by (auto dest: list_all2_nthD[of _ _ _ i])
     moreover have rel_suci:"(snd (x ! (Suc i)), snd (xa ! (Suc i))) \<in> par_state_rel m"  and 
                            "fst (x!Suc i) = fst (xa!Suc i)"
       using list_all unfolding par_state_list_rel_def  
       by (auto dest: list_all2_nthD[of _ _ _  "Suc i"] simp add: a02)     
     then have x_toseq:"snd (x ! i) = toSeqState m  (snd (xa ! i))" and 
               x_toseq_Suc:"snd (x !(Suc i)) = toSeqState m (snd (xa!Suc i))" and 
               x_toPar:"snd (xa ! i) = toParState m  (snd (x ! i))" and 
               x_toPar_Suc: "snd (xa !(Suc i)) = toParState m (snd (x!Suc i))" 
       using par_xstate_rel_seq par_xstate_rel_par rel_i by blast+    
    then have "\<Gamma>\<turnstile>\<^sub>c (fst (xa ! i), toSeqState m (snd (xa ! i))) \<rightarrow>\<^sub>e
                  (fst (xa ! Suc i), toSeqState m (snd (xa ! Suc i)))" 
       using a03 x_toseq x_toseq_Suc
       by (metis \<open>fst (x ! Suc i) = fst (xa ! Suc i)\<close> \<open>fst (x ! i) = fst (xa ! i)\<close> prod.exhaust_sel)    
     then have  "(snd (xa ! i), snd (xa ! Suc i)) \<in> Par_rel m R" using a00 a03
       using list_all list_all2_lengthD
       using a02 by fastforce
     then show "(snd (x ! i), snd (x ! Suc i)) \<in> R" 
       using x_toPar x_toPar_Suc 
       unfolding Par_rel_def
       apply auto
       by (metis eq_toPar)
  qed    
qed
  


lemma "(\<lambda>x. \<forall>i<length (x). snd (x ! i) \<notin> Fault ` F) x = (\<forall>i<length (x). snd (x ! i) \<notin> Fault ` F)"
  by auto

definition Pre :: " ('g,'l,'p,'f,'e)c_rgformula \<Rightarrow> (('g,'l) c_state set)" where
  "Pre x \<equiv> fst(snd x)"

definition Post :: " ('g,'l,'p,'f,'e)c_rgformula \<Rightarrow> (('g,'l) c_state set)" where
  "Post x \<equiv>  fst(snd(snd(snd(snd x))))"

definition Abr ::  " ('g,'l,'p,'f,'e)c_rgformula \<Rightarrow> (('g,'l) c_state set)" where
  "Abr x \<equiv> snd(snd(snd(snd(snd x))))"

definition Rely :: "('g,'l,'p,'f,'e) c_rgformula \<Rightarrow> ((('g,'l) c_state) tran) set" where
  "Rely x \<equiv> fst(snd(snd x))"

definition Guar ::  "('g,'l,'p,'f,'e) c_rgformula \<Rightarrow> ((('g,'l) c_state) tran) set" where
  "Guar x \<equiv> fst(snd(snd(snd x)))"


definition Par_Pre :: " ('g,'l,'p,'f,'e)p_rgformula \<Rightarrow> (('g,'l) par_state set)" where
  "Par_Pre x \<equiv> fst(snd x)"

definition Par_Post :: " ('g,'l,'p,'f,'e)p_rgformula \<Rightarrow> (('g,'l) par_state set)" where
  "Par_Post x \<equiv>  fst(snd(snd(snd(snd x))))"

definition Par_Abr ::  " ('g,'l,'p,'f,'e)p_rgformula \<Rightarrow> (('g,'l) par_state set)" where
  "Par_Abr x \<equiv> snd(snd(snd(snd(snd x))))"

definition Par_Rely :: "('g,'l,'p,'f,'e) p_rgformula \<Rightarrow> ((('g,'l) par_state) tran) set" where
  "Par_Rely x \<equiv> fst(snd(snd x))"

definition Par_Guar ::  "('g,'l,'p,'f,'e) p_rgformula \<Rightarrow> ((('g,'l) par_state) tran) set" where
  "Par_Guar x \<equiv> fst(snd(snd(snd x)))"

lemma etran_in_comm:
  "(\<Gamma>,(P, t) # xs) \<in> comm(G, (q,a)) F  \<Longrightarrow> 
    \<not> (\<Gamma>\<turnstile>\<^sub>c((P,toSeq s))  \<rightarrow> ((P,toSeq t))) \<Longrightarrow>
    (\<Gamma>,(P, s) # (P, t) # xs) \<in> cptn \<Longrightarrow>    
   (\<Gamma>,(P, s) # (P, t) # xs) \<in> comm(G, (q,a)) F" 
proof -
  assume a1:"(\<Gamma>,(P, t) # xs) \<in> comm(G, (q,a)) F" and
         a2:"\<not> \<Gamma>\<turnstile>\<^sub>c((P,toSeq s))  \<rightarrow> ((P,toSeq t))" and
         a3:"(\<Gamma>,(P, s) # (P, t) # xs) \<in> cptn"
  show ?thesis using comm_def a1 a2 a3
  proof -
     {
     let ?l1 = "(P, t) # xs"
     let ?l = "(P, s) # ?l1"     
     have concl:"(\<forall>i ns ns'. Suc i<length ?l \<longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c(fst (?l!i), toSeq (snd(?l!i)))  \<rightarrow> 
                     (fst (?l!Suc i), toSeq (snd(?l!Suc i))) \<longrightarrow>                          
                 (snd(?l!i), snd(?l!(Suc i))) \<in>  G)"
     proof -
       {fix i ns ns'
        assume a11:"Suc i < length  ?l" and
               a12:"\<Gamma>\<turnstile>\<^sub>c(fst (?l!i), toSeq (snd(?l!i)))  \<rightarrow> 
                     (fst (?l!Suc i), toSeq (snd(?l!Suc i)))"  
        have "snd (last ?l)  = snd (last ?l1) " by auto
        then have p1:"(\<forall>i. Suc i<length ?l1 \<longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c(fst (?l1!i), toSeq (snd(?l1!i)))  \<rightarrow> 
                     (fst (?l1!Suc i), toSeq (snd(?l1!Suc i))) \<longrightarrow>                             
               (snd(?l1!i), snd(?l1!(Suc i))) \<in>  G)"
          using a1 a3  unfolding comm_def by auto
          
        have "(snd (?l ! i), snd (?l ! Suc i)) \<in>  G"         
        proof (cases i)
          case 0 
          have  "\<Gamma>\<turnstile>\<^sub>c (P, toSeq s) \<rightarrow> (P, toSeq t)" using a12 0 by auto
          thus ?thesis using a2 by auto             
        next
          case (Suc n) thus ?thesis
          proof -
            have f1: "\<Gamma>\<turnstile>\<^sub>c (fst (?l1 ! n), toSeq(snd (?l1 ! n))) \<rightarrow> 
                          (fst (?l1 ! (Suc n)), toSeq(snd (?l1 ! (Suc n))))"
              using Suc a12 by fastforce
            have f2: "Suc n < length ((P, t) # xs)"
              using Suc a11 by fastforce                                  
            hence "(snd (((P, t) # xs) ! n), snd (((P, t) # xs) ! Suc n)) \<in> G"
              using f2 f1 a1 comm_dest1  by blast            
            thus ?thesis
              by (simp add: Suc)
          qed  
        qed
       } thus ?thesis by auto
     qed
     have concr:"(final_glob (last ?l)  \<longrightarrow> fst (last ?l) \<notin> Fault ` F \<longrightarrow>
                    ((fst (last ?l) = Skip \<and> snd (last ?l) \<in>  q)) \<or>
                    (fst (last ?l) = Throw \<and> snd (last ?l) \<in>  a))"
     using a1  unfolding comm_def by auto
     note res1=conjI[OF concl concr] }   
     thus ?thesis unfolding comm_def by auto qed
qed

lemma ctran_in_comm:   
  " (s, s) \<in> G  \<Longrightarrow>
   (\<Gamma>,(Q,  s) # xs) \<in> comm(G, (q,a)) F  \<Longrightarrow>        
   (\<Gamma>,(P,  s) # (Q,  s) # xs) \<in> comm(G, (q,a)) F"
proof -
  assume a1:"( s, s) \<in> G" and
         a2:"(\<Gamma>,(Q,  s) # xs) \<in> comm(G, (q,a)) F"          
  show ?thesis using comm_def a1 a2
  proof -
     {
     let ?l1 = "(Q,  s) # xs"
     let ?l = "(P,  s) # ?l1"     
     have concl:"(\<forall>i. Suc i<length ?l \<longrightarrow> 
              \<Gamma>\<turnstile>\<^sub>c (fst (?l ! i), toSeq(snd (?l ! i))) \<rightarrow> 
                  (fst (?l ! (Suc i)), toSeq(snd (?l ! (Suc i)))) \<longrightarrow>                                              
                 (snd(?l!i), snd(?l!(Suc i))) \<in>  G)"
     proof -
       {fix i ns ns'
        assume a11:"Suc i < length  ?l" and
               a12:"\<Gamma>\<turnstile>\<^sub>c (fst (?l ! i), toSeq(snd (?l ! i))) \<rightarrow> 
                  (fst (?l ! (Suc i)), toSeq(snd (?l ! (Suc i))))" 
        have p1:"(\<forall>i. Suc i<length ?l1 \<longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c (fst (?l1 ! i), toSeq(snd (?l1 ! i))) \<rightarrow> 
                  (fst (?l1 ! (Suc i)), toSeq(snd (?l1 ! (Suc i)))) \<longrightarrow>                              
               (snd(?l1!i), snd(?l1!(Suc i))) \<in>  G)"
        using a2  unfolding comm_def by auto
        have "(snd (?l ! i), snd (?l ! Suc i)) \<in> G"   
        proof (cases i)
          case 0     
          then have "snd (((P,  s) # (Q,  s) # xs) ! i) =  s \<and> 
                     snd (((P,  s) # (Q,  s) # xs) ! (Suc i)) =  s"                
            by fastforce
          also have "( s,  s) \<in> G"
             using Satis_def a1 by blast
          ultimately show  ?thesis using a1 Satis_def by auto            
        next
          case (Suc n) thus ?thesis using p1 a2  a11 a12 
          proof -
            have f1: "\<Gamma>\<turnstile>\<^sub>c (fst (?l1 ! n), toSeq(snd (?l1 ! n))) \<rightarrow> 
                  (fst (?l1 ! (Suc n)), toSeq(snd (?l1 ! (Suc n))))"
              using Suc a12 by fastforce
            have f2: "Suc n < length ((Q,  s) # xs)"
              using Suc a11 by fastforce
            thus ?thesis using Suc f1 nth_Cons_Suc p1 by auto 
          qed  
        qed
       } thus ?thesis by auto
     qed
     have concr:"(final_glob (last ?l)  \<longrightarrow> 
                  fst (last ?l) \<notin> Fault ` F  \<longrightarrow> fst (last ?l) \<notin> Fault ` F \<longrightarrow>
                    ((fst (last ?l) = Skip \<and> 
                      snd (last ?l) \<in>  q)) \<or>
                    (fst (last ?l) = Throw \<and> 
                      snd (last ?l) \<in>  a))"
     using a2 unfolding comm_def by auto
     note res=conjI[OF concl concr]}
     thus ?thesis unfolding comm_def by auto qed
qed

lemma last_not_F:
assumes 
  a0:"(\<Gamma>,xs)\<in>cptn"  
shows "fst (last xs) \<notin> Fault ` F \<Longrightarrow> \<forall>i < length xs. fst (xs!i) \<notin> Fault ` F"
using a0
proof(induct) print_cases
  case (CptnOne \<Gamma> p s) thus ?case by auto
next
  case (Cptn  \<Gamma> P s Q t xs) 
  have "fst (last ((Q, t) # xs)) \<notin> com.Fault ` F"
    using Cptn.prems by auto
  then have "\<forall>i<length ((Q, t) # xs). fst (((Q, t) # xs) ! i) \<notin> com.Fault ` F" 
    using Cptn.hyps by auto
  moreover have "P\<notin> com.Fault ` F " 
    using Cptn(1) fault_no_tran image_iff not_eq_not_env step_ce_dest
    by (metis (mono_tags, lifting) calculation fst_conv length_Cons nth_Cons_0 zero_less_Suc)    
  ultimately show ?case
    using less_Suc_eq_0_disj by auto 
qed


lemma last_F:
assumes 
  a0:"(\<Gamma>,xs)\<in>cptn" and a1:"final_glob (xs!i)" and 
 a2:"j<length xs" and a3:"i\<le>j"
shows "fst (xs!j) = fst(xs!i)"
using a1 a3
proof(induct "j-i" arbitrary:i)
  case 0
  then show ?case by auto
next
  case (Suc x)
  then have i:"i<j" by auto  
  moreover have "fst (xs!(i+1)) = fst (xs!i)"
  proof-
    obtain a as where "xs = a# as" using a0 a2 i  cptn.simps by blast
    then have "\<Gamma>\<turnstile>\<^sub>c (xs!i) \<rightarrow>\<^sub>c\<^sub>e (xs!(i+1))"
      using Suc a0 a2 cptn_stepc_rtran 
      by (metis (no_types, lifting) Suc_eq_plus1 i less_trans_Suc )
    then have step:"\<Gamma>\<turnstile>\<^sub>c (fst(xs!i), snd(xs!i)) \<rightarrow>\<^sub>c\<^sub>e (fst(xs!(i+1)),snd(xs!(i+1)))" by auto
    show ?thesis using step_ce_dest[OF step] 
      ComputationConGlob.final_eq SmallStepCon.no_step_final' Suc.prems(1) env_c_c' 
      by metis
  qed
  ultimately show ?case using Suc(1)   
    by (metis (no_types, lifting) Suc.hyps(2) Suc.prems(1)  Suc_diff_Suc Suc_eq_plus1 
         Suc_leI add_left_cancel final_glob_def  plus_1_eq_Suc)

qed 

lemma not_final_in_comm:
 "(\<Gamma>,(Q,  s) # xs) \<in> comm(G, (q,a)) F \<Longrightarrow>
  \<not> final_glob (last ((Q,  s) # xs)) \<Longrightarrow>
  (\<Gamma>,(Q,  s) # xs) \<in> comm(G, (q',a')) F"
  unfolding comm_def by force

lemma step_guard_concat:
  assumes a0:"\<forall>i. Suc i< length xs \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c (fst (xs ! i), toSeq (snd (xs ! i))) \<rightarrow>
                                  (fst (xs ! Suc i), toSeq (snd (xs ! Suc i))) \<longrightarrow>
                  (snd (xs ! i), snd (xs ! (Suc i)))\<in>G" and
      a1:"\<forall>i. Suc i< length ys \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c (fst (ys ! i), toSeq (snd (ys ! i))) \<rightarrow>
                                  (fst (ys ! Suc i), toSeq (snd (ys ! Suc i))) \<longrightarrow>
                  (snd (ys ! i), snd (ys ! (Suc i)))\<in>G" and
      a2:"(snd (last xs),snd (ys!0))\<in>G"
    shows "\<forall>i. Suc i< length (xs@ys) \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c (fst ((xs@ys) ! i), toSeq (snd ((xs@ys) ! i))) \<rightarrow>
                                  (fst ((xs@ys) ! Suc i), toSeq (snd ((xs@ys) ! Suc i))) \<longrightarrow>
                  (snd ((xs@ys) ! i), snd ((xs@ys) ! (Suc i)))\<in>G" 
proof-
  { fix i
    assume a00:"Suc i< length (xs@ys)" and 
           a01:"\<Gamma>\<turnstile>\<^sub>c (fst ((xs@ys) ! i), toSeq (snd ((xs@ys) ! i))) \<rightarrow>
              (fst ((xs@ys) ! Suc i), toSeq (snd ((xs@ys) ! Suc i)))"
    have all_ys:"\<forall>i\<ge>length xs. (xs@ys)!i = ys!(i-(length xs))"
          by (simp add: nth_append)   
    have all_xs:"\<forall>i<length xs. (xs@ys)!i = xs!i"
            by (simp add: nth_append)
    { assume a000:"Suc i<length xs" 
      then have "(snd ((xs@ys) ! i), snd ((xs@ys) ! (Suc i)))\<in>G"
        using a01 a0
        by (simp add: a00 Suc_lessD nth_append)
    }
    moreover{
      assume a000:"Suc i> length xs"
      then have "Suc (i - (length xs)) < length ys"
        using a00 by auto
      moreover have "\<Gamma>\<turnstile>\<^sub>c (fst (ys ! (i-(length xs))), toSeq (snd (ys ! (i-(length xs))))) \<rightarrow> 
                          (fst (ys ! ((Suc i)-(length xs))), toSeq (snd (ys ! ((Suc i)-(length xs)))))" 
        using a01 all_ys a000 by fastforce       
      ultimately have "(snd ((xs@ys) ! i), snd ((xs@ys) ! (Suc i)))\<in>G"
        using Suc_diff_le a000 a1 all_ys by auto        
    }
    moreover {
      assume a000:"Suc i = length xs"
      then have "(snd ((xs@ys) ! i), snd ((xs@ys) ! (Suc i)))\<in>G"
        by (metis One_nat_def a2 all_xs all_ys cancel_comm_monoid_add_class.diff_cancel 
                   diff_Suc_Suc diff_zero last_conv_nth 
                 length_greater_0_conv lessI order_refl zero_less_Suc)
    }
    ultimately have "(snd ((xs@ys) ! i), snd ((xs@ys) ! (Suc i)))\<in>G"
      using linorder_neqE_nat by blast
  } thus ?thesis by auto
qed

lemma comm_union:
 assumes 
   a0: "(\<Gamma>,xs) \<in> comm(G, (q,a)) F" and
   a1: "(\<Gamma>,ys) \<in> comm(G, (q',a')) F" and
   a2: "xs\<noteq>[] \<and> ys\<noteq>[]" and
   a3: "( snd (last xs),snd (ys!0)) \<in> G" and
   a4: "(\<Gamma>,xs@ys) \<in> cptn"
 shows "(\<Gamma>,xs@ys) \<in> comm(G, (q',a')) F" 
proof -
{
  let ?l="xs@ys"   
  have last_ys:"last (xs@ys) = last ys" using a2 by fastforce
  have concl:"(\<forall>i. Suc i<length ?l \<longrightarrow> 
             \<Gamma>\<turnstile>\<^sub>c (fst (?l ! i), toSeq(snd (?l ! i))) \<rightarrow> 
                  (fst (?l ! (Suc i)), toSeq(snd (?l ! (Suc i)))) \<longrightarrow>                                            
               (snd(?l!i), snd(?l!(Suc i))) \<in> G)"
    using step_guard_concat comm_dest[OF a0] comm_dest[OF a1] a3 by blast
   have concr:"(final_glob (last ?l)  \<longrightarrow> fst (last ?l) \<notin> Fault ` F  \<longrightarrow>            
                  ((fst (last ?l) = Skip \<and> 
                    snd (last ?l) \<in> q')) \<or>
                  (fst (last ?l) = Throw \<and> 
                    snd (last ?l) \<in> a'))"
   using a1 last_ys  a2 comm_des3 by fastforce
   note res=conjI[OF concl concr]}
   thus ?thesis unfolding comm_def by auto 
qed



lemma cpn_rule1:"(\<forall>s. cpn n \<Gamma> P s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F) \<Longrightarrow>
      (\<forall>s l. (\<Gamma>,l)\<in>cpn n \<Gamma> P s \<and> (\<Gamma>,l)\<in> assum (p, R) \<longrightarrow> (\<Gamma>,l) \<in> comm(G, (q,a)) F)"
proof-
  assume a0:"\<forall>s. cpn n \<Gamma> P s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
  {fix s l    
    assume a00:"(\<Gamma>,l)\<in>cpn n \<Gamma> P s \<and> (\<Gamma>,l)\<in> assum (p, R)"    
    then have "cpn n \<Gamma> P s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F" using a0
      by (simp add: a0)    
    then have "(\<Gamma>,l) \<in> comm(G, (q,a)) F" using a00 unfolding cpn_def assum_def comm_def
      by blast
    } then show ?thesis by auto
  qed

lemma cpn_rule2:"(\<forall>s l. (\<Gamma>,l)\<in>cpn n \<Gamma> P s \<and> (\<Gamma>,l)\<in> assum (p, R) \<longrightarrow> (\<Gamma>,l) \<in> comm(G, (q,a)) F) \<Longrightarrow>
                (\<forall>s. cpn n \<Gamma> P s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F)"
proof-
  assume a0:"\<forall>s l. (\<Gamma>,l)\<in>cpn n \<Gamma> P s \<and> (\<Gamma>,l)\<in> assum (p, R) \<longrightarrow> (\<Gamma>,l) \<in> comm(G, (q,a)) F"
  {fix s l
     assume a00:"(\<Gamma>,l)\<in> cpn n \<Gamma> P s \<and> (\<Gamma>,l)\<in>assum(p, R)"        
    then have "(\<Gamma>,l) \<in> comm(G, (q,a)) F" using a0 unfolding cpn_def assum_def comm_def
      by blast
   } then show ?thesis  unfolding cpn_def by fastforce
 qed

lemma cpn_rule:"(\<forall>s l. (\<Gamma>,l)\<in>cpn n \<Gamma> P s \<and> (\<Gamma>,l)\<in> assum (p, R) \<longrightarrow> (\<Gamma>,l) \<in> comm(G, (q,a)) F) =
                (\<forall>s. cpn n \<Gamma> P s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F)"
  using cpn_rule1 cpn_rule2
  by metis

lemma split_list_i:"i<length l \<Longrightarrow>
                    \<exists>l1 l2. l = l1@(l!i#l2)"
proof(induct l arbitrary: i)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case
    using id_take_nth_drop by blast
qed

lemma sub_assum1:
  assumes a0: "(\<Gamma>,l0@l1) \<in> assum (p,R)" and a1:"l0\<noteq>[]"
  shows "(\<Gamma>,l0) \<in> assum (p,R)"
  by (metis a0 a1 append_self_conv2 id_take_nth_drop length_greater_0_conv sub_assum take_0)   
 


(* text{* 
@{text rel_safe} specifies that the relation leaves unmodifed any fragment out of the 
state
*}
definition rel_safe:: "(('l::sep_algebra,'g::sep_algebra) transition \<Rightarrow> bool) \<Rightarrow> bool"
where
"rel_safe R \<equiv> \<forall>h h1 h2 t. R (h1,t) \<and> ((h1 \<uplus>\<^sub>p h2) h) \<longrightarrow> R (h, t \<uplus> h2)"

definition mem_safe::
"(('l::sep_algebra,'g::sep_algebra) state,'p,'f) body \<Rightarrow> 
 (('l,'g) state,'p,'f) com \<Rightarrow> 
 (('l,'g) transition \<Rightarrow> bool) \<Rightarrow> 
   bool"
where
 "mem_safe \<Gamma> f R \<equiv> \<forall>h h1 h2 t1. 
      ((\<forall>c\<in> cp \<Gamma> f (Normal h1). 
        final_valid(last (snd c)) \<and> (Normal t1 =  snd (last (snd c))) \<and>
        (\<forall>i. Suc i<length (snd c) \<longrightarrow> 
                 (fst c)\<turnstile>\<^sub>c((snd c)!i)  \<rightarrow>\<^sub>e ((snd c)!(Suc i)) \<longrightarrow>                  
                   (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> 
                     (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (R))) \<and>      
        (h1 \<uplus>\<^sub>p h2) h \<longrightarrow>
        (\<forall>c\<in> cp \<Gamma> f (Normal h). 
          final_valid(last (snd c)) \<and>
          (\<forall>i. Suc i<length (snd c) \<longrightarrow> 
              (fst c)\<turnstile>\<^sub>c((snd c)!i)  \<rightarrow>\<^sub>e ((snd c)!(Suc i)) \<longrightarrow>                  
              (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> 
                (case_prod (\<lambda>x y. (Normal x, Normal y))) ` (R)) \<longrightarrow>
              (Normal (t1 \<uplus> h2) =  snd (last (snd c)))))     
      "                         
 *)

     
subsection \<open>Validity for Parallel Programs.\<close>

definition All_End :: "('g,'l,'p,'f,'e) par_config \<Rightarrow> bool" where
  "All_End xs \<equiv> fst xs \<noteq>[] \<and> (\<forall>i<length (fst xs). final1 ((fst xs)!i) (snd xs))"

definition par_assum :: 
  "(('g,'l)par_state set \<times>  
   ((('g,'l)par_state) tran) set) \<Rightarrow>
   (('g,'l,'p,'f,'e) par_confs) set" where
  "par_assum \<equiv> 
     \<lambda>(pre, rely). {c. 
       snd((snd c)!0) \<in>  pre \<and> (\<forall>i. Suc i<length (snd c) \<longrightarrow> 
       (fst c)\<turnstile>\<^sub>p((snd c)!i)  \<rightarrow>\<^sub>e ((snd c)!(Suc i)) \<longrightarrow>        
         (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> rely)}"

definition not_fault::"('s, 'p, 'f, 'e) LanguageCon.com list \<Rightarrow> 'f set \<Rightarrow> bool"
  where "not_fault P F \<equiv> \<forall>i<length P. P!i \<notin> Fault ` F"

definition throw_program::"('s, 'p, 'f, 'e) com list \<Rightarrow> bool"
  where "throw_program P \<equiv> (\<forall>i<length P. P!i =Skip \<or> P!i = Throw) \<and> (\<exists>i<length P. P!i =Throw)"

definition skip_program::"('s, 'p, 'f, 'e) com list \<Rightarrow> bool"
  where "skip_program P \<equiv> \<forall>i<length P. P!i =Skip"

definition par_comm :: 
  "(((('g,'l)par_state) tran) set  \<times> 
     (('g,'l)par_state set \<times> ('g,'l)par_state set))  \<Rightarrow> 
    'f set \<Rightarrow>
   (('g,'l,'p,'f,'e) par_confs) set" where
  "par_comm \<equiv> 
     \<lambda>(guar, (q,a)) F. 
     {c.  
         (\<forall>i. 
            Suc i<length (snd c) \<longrightarrow> 
            (fst c)\<turnstile>\<^sub>p((snd c)!i)  \<rightarrow> ((snd c)!(Suc i)) \<longrightarrow>                        
              (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> guar) \<and> 
                (All_End (last (snd c)) \<longrightarrow> not_fault (fst (last (snd c)))  F \<longrightarrow>
                   throw_program (fst (last (snd c))) \<and> snd (last (snd c)) \<in> a \<or>
                   skip_program (fst (last (snd c))) \<and> snd (last (snd c)) \<in> q)}"

definition par_com_validity :: 
  "('g\<times>'l,'p,'f,'e) body \<Rightarrow> 
   'f set \<Rightarrow>
   ('g,'l,'p,'f,'e) par_com \<Rightarrow>  
   (('g,'l)par_state set) \<Rightarrow>         
   (((('g,'l)par_state) tran) set) \<Rightarrow> 
   (((('g,'l)par_state) tran) set) \<Rightarrow> 
   (('g,'l)par_state set) \<Rightarrow>
   (('g,'l)par_state set) \<Rightarrow> 
     bool"  
("_ \<Turnstile>\<^bsub>'/_\<^esub>/ _ SAT [_, _, _, _,_]" [61,60,0,0,0,0,0,0] 45) where
  "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Ps SAT [pre, R, G, q,a] \<equiv> 
   \<forall>s. par_cp  \<Gamma> Ps s \<inter> par_assum(pre, R)  \<subseteq> par_comm(G, (q,a)) F"
   
definition par_com_cvalidity :: 
  "('g\<times>'l,'p,'f,'e) body \<Rightarrow>
    ('g,'l,'p) p_sextuple set \<Rightarrow>
   'f set \<Rightarrow>
  ('g,'l,'p,'f,'e) par_com \<Rightarrow>   
   (('g,'l)par_state set) \<Rightarrow> 
   (((('g,'l)par_state) tran) set) \<Rightarrow> 
   (((('g,'l)par_state) tran) set) \<Rightarrow> 
   (('g,'l)par_state set) \<Rightarrow>
   (('g,'l)par_state set) \<Rightarrow> 
     bool"  
("_,_ \<Turnstile>\<^bsub>'/_\<^esub>/ _ SAT [_, _, _, _,_]" [61,60,0,0,0,0,0,0] 45) where
  "\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> Ps SAT [p,  R, G, q,a] \<equiv> 
  (\<forall>i<length Ps. \<forall>(c,p,R,G,q,a)\<in> \<Theta>. Pred_wf i p \<and> Rel_wf i R \<and>  Rel_wf i G \<and> 
                                     Pred_wf i q \<and>  Pred_wf i a \<longrightarrow>
                     (\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat i [p, R, G, q,a])) \<longrightarrow>
   \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Ps SAT [p, R, G, q,a]"
   
declare Un_subset_iff [simp del] sup.bounded_iff [simp del]

definition N::"('g,'l) c_state set \<Rightarrow> nat set" 
  where "N P \<equiv> {n. (\<exists>x \<in> P. length(snd x) = n)}" 

inductive
lrghoare :: "[('g\<times>'l,'p,'f,'e) body,
             ('g,'l,'p) c_sextuple set,
              'f set,
              ('g\<times>'l,'p,'f,'e) com,  
              (('g,'l) c_state set),  
              ((('g,'l) c_state) tran) set, ((('g,'l) c_state) tran) set,
              ('g,'l) c_state set,
               ('g,'l) c_state set] \<Rightarrow> bool"
    ("_,_ \<turnstile>\<^bsub>'/_\<^esub> _ sat [_, _, _, _,_]" [61,61,60,60,0,0,0,0] 45)
where
 Skip: "\<lbrakk> Sta q R; (\<forall>s. length (snd s) \<in> N q \<longrightarrow> ( s,  s) \<in> G) \<rbrakk> \<Longrightarrow>
         \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> Skip sat [q, R, G, q,a] "

|Spec: "\<lbrakk>Sta p R;Sta q R;
        (\<forall>s t. s\<in>p \<and> (fst s,fst t)\<in>r \<and> (snd s) = (snd t) \<longrightarrow> ( s, t) \<in> G);
         p \<subseteq> {s. (\<forall>t. (fst s,t)\<in>r \<longrightarrow> (t,snd s)\<in> q) \<and> (\<exists>t. (fst s,t) \<in> r)} \<rbrakk> \<Longrightarrow> 
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Spec r e) sat [p, R, G, q,a]"

| Basic: "\<lbrakk> Sta p R;Sta q R;
           (\<forall>s t. s\<in>p \<and> ((fst t)=f (fst s)) \<and> (snd s =  snd t) \<longrightarrow> ( s, t) \<in> G);
            p \<subseteq> {s. (f (fst s),snd s) \<in> q} \<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Basic f e) sat [p, R, G, q,a]"

| If: "\<lbrakk>Sta p R;  (\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G); 
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> {c. (fst c) \<in> b}, R, G, q,a]; 
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [p \<inter> {c. (fst c) \<in> (-b)}, R, G, q,a]\<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Cond b c1 c2) sat [p,  R, G, q,a]"

| While: "\<lbrakk> Sta p R; Sta (p \<inter> {c. (fst c) \<in> (-b)}) R; Sta a R; 
           (\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G);
            \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p \<inter> {c. (fst c) \<in> b}, R, G, p,a]\<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (While b c) sat [p, R, G, p \<inter> {c. (fst c) \<in> (-b)},a]"

| Seq: "\<lbrakk>Sta a R; Sta p R; (\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G); 
         \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [q, R, G, r,a]; \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p, R, G, q,a]\<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Seq c1 c2) sat [p, R, G, r,a]"

| Await: "\<lbrakk> Sta p R; Sta q R; Sta a R; \<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G; 
            p \<subseteq> {s. \<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
                  (b \<inter> {c. c = fst s}) c 
                   {s'. ( s,  (s', snd s)) \<in> G \<and> (s',snd s)\<in> q},
                   {s'. ( s,  (s', snd s)) \<in> G \<and> (s',snd s)\<in> a}} \<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Await b c e) sat [p, R, G, q,a]"

| Guard: "\<lbrakk>Sta (p \<inter> {c. (fst c) \<in> g}) R;  (\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G); 
           \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p \<inter> {c. (fst c) \<in> g}, R, G, q,a]\<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Guard f g c) sat [p \<inter> {c. (fst c) \<in> g}, R, G, q,a]"

| Guarantee:  "\<lbrakk> Sta p R;  (\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G); f\<in>F;
                 \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p \<inter> {c. (fst c) \<in> g}, R, G, q,a] \<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Guard f g c) sat [p, R, G, q,a]"

| CallRec: "\<lbrakk>(c,p,R,G,q,a) \<in> Specs; 
             \<forall>(c,p,R,G,q,a)\<in> Specs. c \<in> dom \<Gamma> \<and> 
              Sta p R \<and>   (\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G) \<and>
             \<Gamma>,\<Theta> \<union> Specs \<turnstile>\<^bsub>/F\<^esub> (the (\<Gamma> c)) sat [p,  R, G, q,a];
            Sta p R; (\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G)\<rbrakk> \<Longrightarrow>
            \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]" 

| Asm: "\<lbrakk>(c,p,R,G,q,a) \<in> \<Theta>\<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]" 

| Call: "\<lbrakk>
         Sta p R;  (\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G);c \<in> dom \<Gamma>; 
         \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (the (\<Gamma> c)) sat [p, R, G, q,a]\<rbrakk>  \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]" 

| DynCom: "\<lbrakk>(Sta p R) \<and> (Sta q R) \<and> (Sta a R) \<and>
             (\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G);
            (\<forall>s \<in> fst ` p. (\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (c s) sat [p, R, G, q,a]))\<rbrakk> \<Longrightarrow>
            \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (DynCom c) sat [p, R, G, q,a]"

| Throw: "\<lbrakk>Sta a R;  (\<forall>s. length (snd s) \<in> N a \<longrightarrow> ( s,  s) \<in> G) \<rbrakk> \<Longrightarrow>
         \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> Throw sat [a,  R, G, q,a] "

| Catch: "\<lbrakk>Sta q R;  (\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G); 
           \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [r, R, G, q,a];
           \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p, R, G, q,r] 
           \<rbrakk> \<Longrightarrow>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Catch c1 c2) sat [p, R, G, q,a]"

| Conseq: "\<forall>s \<in> p. 
             (\<exists>p' R' G' q' a' \<Theta>'.  
             (s\<in> p') \<and>
              R \<subseteq> R' \<and>            
             G' \<subseteq> G \<and>             
             q' \<subseteq> q \<and>
             a' \<subseteq> a \<and> \<Theta>' \<subseteq> \<Theta> \<and>                       
            (\<Gamma>,\<Theta>'\<turnstile>\<^bsub>/F\<^esub> P sat [p', R', G', q',a']) ) 
            \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q,a]"

| Conj_post: " \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q,a] \<Longrightarrow>
                \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q',a'] 
            \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q \<inter> q',a \<inter> a']"
  
| Conj_Inter: "sa\<noteq>({}::nat set) \<Longrightarrow> 
               \<forall>i\<in>sa. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q i,a] \<Longrightarrow>                
               \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G,\<Inter>i\<in>sa. q i,a]" 
| Stuck: "p = {} \<Longrightarrow> \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> Stuck sat [p, R, G, q,a]"
| Fault:  "p = {} \<Longrightarrow> \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (Fault f) sat [p, R, G, q,a]"

  
inductive_cases hoare_elim_cases [cases set]:
 "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> Skip sat [p, R, G, q,a]"

thm hoare_elim_cases
(*
lemma "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> Skip sat [p, R, G, q,a] \<Longrightarrow> 
        \<forall>s \<in> p. 
          (\<exists>p' R' G' q' a'.  
           (s\<in> p') \<and>
            R \<subseteq> R' \<and>            
            G' \<subseteq> G \<and>             
            q' \<subseteq> q \<and>
            a' \<subseteq> a \<and>                        
           (\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p', R', G', q',a']) \<and> p'=q' \<and> Sta q' R' \<and> Norm R' \<and> (\<forall>s. (Normal s, Normal s) \<in> G'))"
proof -
  assume a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> Skip sat [p, R, G, q,a]"  
  {
   fix s
   assume a01:"s\<in>p"
   have "(\<exists>p' R' G' q' a'.  
           (s\<in> p') \<and>
            R \<subseteq> R' \<and>            
            G' \<subseteq> G \<and>             
            q' \<subseteq> q \<and>
            a' \<subseteq> a \<and>                        
           (\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p', R', G', q',a']) \<and> p'=q' \<and> Sta q' R' \<and> Norm R' \<and> (\<forall>s. (Normal s, Normal s) \<in> G'))"
   proof (cases "p=q")
    case True thus ?thesis using hoare_elim_cases   sorry
   next
    case False thus ?thesis sorry
   qed
  } thus ?thesis by fastforce
qed*)

(* lemma "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p, R, G, q,r] \<Longrightarrow>
       c\<noteq>Throw \<Longrightarrow>
       Sta p R"
sorry *)
(*
| Env:  "\<lbrakk>noawaits c; \<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> (p ) (sequential c) q,(a)\<rbrakk> \<Longrightarrow>
         \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> c sat [p, sep_empty, Emp, Emp, q,a]"
        
| Hide: "\<lbrakk>\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p, (I \<and>* I'), (R \<and>* R'), (G \<and>* G'), q,a]; 
         (I  \<triangleright> R); 
         (I  \<triangleright> G)
          \<rbrakk> \<Longrightarrow> 
         \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> c sat [p, I, R, G, q,a]" 

|Frame: "\<lbrakk>
        \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p, I, R, G , q,a]; 
        I'  \<triangleright> R'; I'  \<triangleright> G';
        Sta r (R'\<and>*tran_Id);
        (\<forall>s t. (r imp (I'\<and>*sep_true))(s,t));
        (rel_safe R); (rel_safe (G\<and>*tran_True)) \<rbrakk>  \<Longrightarrow>
        \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> c sat [p\<and>*r, I \<and>* I', R \<and>* R', G \<and>* G', q\<and>*r,a\<and>*r]"
*)



definition Com :: "('g,'l,'p,'f,'e) c_rgformula \<Rightarrow> ('g\<times>'l,'p,'f,'e) com" where
  "Com x \<equiv> fst  x"

definition Par_Com :: "('g,'l,'p,'f,'e) p_rgformula \<Rightarrow> ('g\<times>'l,'p,'f,'e) com" where
  "Par_Com x \<equiv> fst  x"

definition Rel_wf_st::"nat \<Rightarrow> (('g,'l)par_state) tran set \<Rightarrow> bool"
  where "Rel_wf_st i R \<equiv> \<forall>(x,y)\<in>R.  i \<le> length (snd x) \<and> length (snd x) = length (snd y)"
inductive
  par_rghoare ::  "[('g\<times>'l,'p,'f,'e) body,
              ('g,'l,'p) p_sextuple set,
              'f set,                  
              ( ('g,'l,'p,'f,'e) p_rgformula) list,  
              ('g,'l)par_state set,              
              ((('g,'l)par_state) tran) set, ((('g,'l)par_state) tran) set,
              ('g,'l)par_state set,
               ('g,'l)par_state set] \<Rightarrow> bool"
    ("_,_ \<turnstile>\<^bsub>'/_\<^esub> _ SAT [_, _, _, _,_]" [61,60,60,0,0,0,0] 45)
where
  Parallel:
  "\<lbrakk> xs \<noteq>[]; 
     \<forall>i<length xs. \<forall>x\<in> (Par_Post (xs!i)). length (snd x)  = length xs;
     \<forall>i<length xs. \<forall>x\<in> (Par_Abr (xs!i)). length (snd x)  = length xs;
     \<forall>i<length xs. \<forall>x\<in> (Par_Pre(xs!i)). length (snd x)  = length xs;
     \<forall>i<length xs. R \<union> (\<Union>j\<in>{j. j<length xs \<and> j\<noteq>i}. (Par_Guar  (xs!j))) \<subseteq> (Par_Rely (xs!i));
    (\<Union>j<length xs. (Par_Guar  (xs!j))) \<subseteq> G;
     p \<subseteq> (\<Inter>i<length xs. (Par_Pre (xs!i)));
    (\<Inter>i<length xs. (Par_Post (xs!i))) \<subseteq> q;
    (\<Union>i<length xs. (Par_Abr (xs!i))) \<subseteq> a; \<forall>i<length xs. Rel_wf_st (length xs) (Par_Guar  (xs!i));            
    \<forall>i<length xs. \<Gamma>,(seq_proc_spec i \<Theta>) \<turnstile>\<^bsub>/F\<^esub> Par_Com (xs!i) sat [Seq_pred i (Par_Pre (xs!i)),Seq_rel i (Par_Rely (xs!i)),
                                           Seq_rel i (Par_Guar (xs!i)),Seq_pred i (Par_Post (xs!i)),
                                           Seq_pred i (Par_Abr (xs!i))] \<rbrakk>
   \<Longrightarrow>  \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> xs SAT [p, R, G, q,a]" 
 
section {* Soundness *}

lemma skip_suc_i:
  assumes a1:"(\<Gamma>, l) \<in> cptn \<and> fst (l!i) = Skip"   
  assumes a2:"i+1 < length l"
  shows "fst (l!(i+1)) = Skip"
proof -
  from a2 a1 obtain l1 ls where "l=l1#ls" 
    by (metis list.exhaust list.size(3) not_less0) 
  then have "\<Gamma>\<turnstile>\<^sub>c (l!i) \<rightarrow>\<^sub>c\<^sub>e (l!(Suc i))" using cptn_stepc_rtran a1 a2
    by fastforce 
  thus ?thesis using a1 a2 stepc_elim_cases(1) not_eq_not_env step_ce_dest
    by (metis Suc_eq_plus1 prod.exhaust_sel )  
qed 

lemma throw_suc_i:
  assumes a1:"(\<Gamma>, l) \<in> cptn \<and> (fst(l!i) = Throw \<and> snd(l!i) =  s1)"   
  assumes a2:"Suc i < length l"
  assumes a3:"env_tran_right \<Gamma> l rely \<and> Sta q rely \<and> s1 \<in> q"
  shows "fst (l!(Suc i)) =  Throw \<and> (\<exists>s2. snd(l!(Suc i)) =  s2 \<and> s2 \<in>q)"
proof -
  have fin:"final_glob (l!i)" using a1 unfolding final_glob_def by auto 
  from a2 a1 obtain l1 ls where "l=l1#ls" 
    by (metis list.exhaust list.size(3) not_less0) 
  then have "\<Gamma>\<turnstile>\<^sub>c (l!i) \<rightarrow>\<^sub>c\<^sub>e (l!(Suc i))" using cptn_stepc_rtran a1 a2
    by fastforce   
  then have "\<Gamma>\<turnstile>\<^sub>c (fst (l!i), toSeq (snd (l!i)))  \<rightarrow> (fst (l!(Suc i)), toSeq (snd (l!(Suc i)))) \<or> 
             \<Gamma>\<turnstile>\<^sub>c (l!i) \<rightarrow>\<^sub>e (l!(Suc i))"
    using step_ce_dest by (metis prod.collapse)
  thus ?thesis proof                                          
    assume "\<Gamma>\<turnstile>\<^sub>c (fst (l!i), toSeq (snd (l!i)))  \<rightarrow> (fst (l!(Suc i)), toSeq (snd (l!(Suc i))))" 
    thus ?thesis using fin no_step_final'
      using ComputationConGlob.final_eq by blast
  next
    assume "\<Gamma>\<turnstile>\<^sub>c (l!i) \<rightarrow>\<^sub>e (l!(Suc i))" thus ?thesis 
      using a1 a3 a2 env_tran_normal by (metis (no_types, lifting)  env_c_c' prod.collapse) 
  qed 
qed 

lemma final_suc_i:
  assumes a1:"(\<Gamma>, l) \<in> cptn \<and>  final_glob (l!i)"   
  assumes a2:"Suc i < length l"
  assumes a3:"env_tran_right \<Gamma> l rely \<and> Sta q rely \<and> snd (l!i) \<in> q"
  shows "fst (l!(Suc i)) =  fst(l!i) \<and> (snd (l!(Suc i)) \<in>q)"
proof -
  have fin:"final_glob (l!i)" using a1 unfolding final_glob_def by auto 
  from a2 a1 obtain l1 ls where "l=l1#ls" 
    by (metis list.exhaust list.size(3) not_less0) 
  then have "\<Gamma>\<turnstile>\<^sub>c (l!i) \<rightarrow>\<^sub>c\<^sub>e (l!(Suc i))" using cptn_stepc_rtran a1 a2
    by fastforce   
  then have "\<Gamma>\<turnstile>\<^sub>c (fst (l!i), toSeq (snd (l!i)))  \<rightarrow> (fst (l!(Suc i)), toSeq (snd (l!(Suc i)))) \<or> 
             \<Gamma>\<turnstile>\<^sub>c (l!i) \<rightarrow>\<^sub>e (l!(Suc i))"
    using step_ce_dest by (metis prod.collapse)
  thus ?thesis proof                                          
    assume "\<Gamma>\<turnstile>\<^sub>c (fst (l!i), toSeq (snd (l!i)))  \<rightarrow> (fst (l!(Suc i)), toSeq (snd (l!(Suc i))))" 
    thus ?thesis using fin no_step_final'
      using ComputationConGlob.final_eq by blast
  next
    assume "\<Gamma>\<turnstile>\<^sub>c (l!i) \<rightarrow>\<^sub>e (l!(Suc i))" thus ?thesis 
      using a1 a3 a2 env_tran_normal by (metis (no_types, lifting)  env_c_c' prod.collapse) 
  qed 
qed 

lemma stuck_suc_i:
  assumes a1:"(\<Gamma>, l) \<in> cptn \<and> fst(l!i) = Stuck "   
  assumes a2:"Suc i < length l"  
  shows "fst (l!(Suc i)) =  Stuck"
proof -
  have fin:"final_glob (l!i)" using a1 unfolding final_glob_def by auto 
  from a2 a1 obtain l1 ls where "l=l1#ls" 
    by (metis list.exhaust list.size(3) not_less0) 
  then have "\<Gamma>\<turnstile>\<^sub>c (l!i) \<rightarrow>\<^sub>c\<^sub>e (l!(Suc i))" using cptn_stepc_rtran a1 a2
    by fastforce   
  then have "\<Gamma>\<turnstile>\<^sub>c (fst (l!i), toSeq (snd (l!i)))  \<rightarrow> (fst (l!(Suc i)), toSeq (snd (l!(Suc i)))) \<or> 
             \<Gamma>\<turnstile>\<^sub>c (l!i) \<rightarrow>\<^sub>e (l!(Suc i))"
    using step_ce_dest by (metis prod.collapse)
  thus ?thesis proof                                          
    assume "\<Gamma>\<turnstile>\<^sub>c (fst (l!i), toSeq (snd (l!i)))  \<rightarrow> (fst (l!(Suc i)), toSeq (snd (l!(Suc i))))" 
    thus ?thesis using fin no_step_final'
      using ComputationConGlob.final_eq by blast
  next
    assume "\<Gamma>\<turnstile>\<^sub>c (l!i) \<rightarrow>\<^sub>e (l!(Suc i))" thus ?thesis 
      using a1  a2 
      by (metis (no_types, lifting)  env_c_c' prod.collapse) 
  qed 
qed 

lemma fault_suc_i:
  assumes a1:"(\<Gamma>, l) \<in> cptn \<and> fst(l!i) = Fault f "   
  assumes a2:"Suc i < length l"
  shows "fst (l!(Suc i)) =  Fault f"
proof -
  have fin:"final_glob (l!i)" using a1 unfolding final_glob_def by auto 
  from a2 a1 obtain l1 ls where "l=l1#ls" 
    by (metis list.exhaust list.size(3) not_less0) 
  then have "\<Gamma>\<turnstile>\<^sub>c (l!i) \<rightarrow>\<^sub>c\<^sub>e (l!(Suc i))" using cptn_stepc_rtran a1 a2
    by fastforce   
  then have "\<Gamma>\<turnstile>\<^sub>c (fst (l!i), toSeq (snd (l!i)))  \<rightarrow> (fst (l!(Suc i)), toSeq (snd (l!(Suc i)))) \<or> 
             \<Gamma>\<turnstile>\<^sub>c (l!i) \<rightarrow>\<^sub>e (l!(Suc i))"
    using step_ce_dest by (metis prod.collapse)
  thus ?thesis proof                                          
    assume "\<Gamma>\<turnstile>\<^sub>c (fst (l!i), toSeq (snd (l!i)))  \<rightarrow> (fst (l!(Suc i)), toSeq (snd (l!(Suc i))))" 
    thus ?thesis using fin no_step_final'
      using ComputationConGlob.final_eq by blast
  next
    assume "\<Gamma>\<turnstile>\<^sub>c (l!i) \<rightarrow>\<^sub>e (l!(Suc i))" thus ?thesis 
      using a1  a2 
      by (metis (no_types, lifting)  env_c_c' prod.collapse) 
  qed 
qed 

lemma i_skip_all_skip:assumes a1:"(\<Gamma>, l) \<in> cptn \<and> fst (l!i) = Skip"
      assumes a2: "i\<le>j \<and> j < (length l)"      
      (* assumes a4:"env_tran_right \<Gamma> l rely" *)
      shows "fst (l!j) = Skip"
using a1 a2 
proof (induct "j-i" arbitrary: i j)
  case 0
  then have "Suc i = Suc j" by simp  
  thus ?case using "0.prems" skip_suc_i by fastforce
next
  case (Suc n)    
  then have "length l > Suc i" by auto 
  then have "i<j" using Suc by fastforce
  moreover then have "j-1< length l" using Suc by fastforce
  moreover then have "j  - i = Suc n" using Suc by fastforce
  ultimately have "fst (l ! (j)) = LanguageCon.com.Skip" using Suc  skip_suc_i
    by (metis (no_types, lifting) Suc_diff_Suc Suc_eq_plus1 Suc_leI `Suc i < length l` diff_Suc_1)        
  also have "j=j" using Cons using Suc.prems(2) by linarith  
  ultimately show ?case using Suc by (metis (no_types))
qed

lemma i_throw_all_throw:assumes a1:"(\<Gamma>, l) \<in> cptn \<and> (fst (l!i) = Throw \<and> snd (l!i) =  s1)"
      assumes a2: "i\<le>j \<and> j < (length l)"      
      assumes a4:"env_tran_right \<Gamma> l rely \<and> Sta q rely \<and> s1\<in>q" 
      shows "fst (l!j) = Throw \<and> (\<exists>s2. snd(l!j) =  s2  \<and> s2\<in>q)"
using a1 a2 a4
proof (induct "j-i" arbitrary: i j s1)
  case 0
  then have "Suc i = Suc j" by simp  
  thus ?case using "0.prems"  by fastforce
next
  case (Suc n)    
  then have l_suc:"length l > Suc i" by linarith 
  then have "i<j" using Suc.prems(3)
    using Suc.hyps(2) by linarith 
  moreover then have "j-1< length l" by (simp add: Suc.prems(2) less_imp_diff_less)   
  moreover have "n = j - 1 - i"
    using Suc.hyps(2) by auto
  ultimately obtain s2 where "fst (l ! (j-1)) = LanguageCon.com.Throw \<and> snd (l ! (j-1)) =  s2 \<and> s2\<in>q"
    using Suc(1)[of "j-1" i s1] Suc(2) Suc(5)
    by (metis One_nat_def Suc.prems(1) diff_diff_cancel diff_is_0_eq' less_or_eq_imp_le nat_le_linear) 
  also have "Suc (j - 1) < length l" using Suc by arith
  ultimately have "fst (l ! (j)) = LanguageCon.com.Throw \<and> (\<exists>s2. snd(l!j) =  s2 \<and> s2\<in>q)" 
    using Suc(2-5) throw_suc_i[of \<Gamma> l "j-1" s2 rely q] a4
    by fastforce
  also have "j=j" using Cons using Suc.prems(2) by linarith  
  ultimately show ?case using Suc by (metis (no_types))
qed  


lemma i_final_all_stable:assumes a0:"(\<Gamma>, l) \<in> cptn" and a1:"final_glob (l!i)"
      assumes a2: "i\<le>j" and a3:"j < (length l)"      
      assumes a4:"env_tran_right \<Gamma> l rely" and a5: "Sta q rely" and a6:"(snd (l!i))\<in>q" 
      shows "fst (l!j) = fst (l!i) \<and> (snd(l!j) \<in> q)"
using a1 a2 a3 a6
proof (induct "j-i" arbitrary: i j)
  case 0
  then have "Suc i = Suc j" by simp  
  thus ?case using "0.prems"  by fastforce
next
  case (Suc n)  
  then have l_suc:"length l > Suc i" by linarith 
  then have "i<j" using Suc.prems(3)
    using Suc.hyps(2) by linarith 
  moreover then have "j-1< length l" by (simp add: Suc.prems(2,3) less_imp_diff_less)   
  moreover have "n = j - 1 - i"
    using Suc.hyps(2) by auto
  ultimately have "fst (l ! (j-1)) = fst (l!i) \<and> snd (l ! (j-1)) \<in> q"
    using Suc(1)[of "j-1" i] Suc(2) Suc(5)
    using Suc.prems(1) Suc.prems(4) by linarith 
  also have "Suc (j - 1) < length l" using Suc by arith
  ultimately have "fst (l ! (j)) =fst (l !i) \<and> (snd(l!j) \<in> q)" 
    using a0 Suc(2,3) final_suc_i[of \<Gamma> l "j-1"  rely q] a4 a5 unfolding final_glob_def
    by auto
  also have "j=j" using Cons using Suc.prems(2) by linarith  
  ultimately show ?case using Suc by (metis (no_types))
qed  



lemma i_stuck_all_stuck:
  assumes a1:"(\<Gamma>, l) \<in> cptn \<and> (fst (l!i) = Stuck )"
      assumes a2: "i\<le>j \<and> j < (length l)"  
      shows "fst (l!j) = Stuck "
using a1 a2 
proof (induct "j-i" arbitrary: i j )
  case 0
  then have "Suc i = Suc j" by simp  
  thus ?case using "0.prems"  by fastforce
next
  case (Suc n)    
  then have l_suc:"length l > Suc i" by linarith 
  then have "i<j" 
    using Suc.hyps(2) by linarith 
  moreover then have "j-1< length l" by (simp add: Suc.prems(2) less_imp_diff_less)   
  moreover have "n = j - 1 - i"
    using Suc.hyps(2) by auto
  ultimately have "fst (l ! (j-1)) = Stuck"
    using Suc(1)[of "j-1" i ] Suc(2) 
    by (metis One_nat_def Suc.prems(1) diff_diff_cancel diff_is_0_eq' less_or_eq_imp_le nat_le_linear) 
  also have "Suc (j - 1) < length l" using Suc by arith
  ultimately have "fst (l ! (j)) = Stuck" 
    using Suc(2-4) stuck_suc_i[of \<Gamma> l "j-1"  ] 
    by fastforce
  also have "j=j" using Cons using Suc.prems(2) by linarith  
  ultimately show ?case using Suc by (metis (no_types))
qed  

lemma i_fault_all_fault:
  assumes a1:"(\<Gamma>, l) \<in> cptn \<and> fst (l!i) = Fault f"
      assumes a2: "i\<le>j \<and> j < (length l)"  
      shows "fst (l!j) = Fault f "
using a1 a2 
proof (induct "j-i" arbitrary: i j )
  case 0
  then have "Suc i = Suc j" by simp  
  thus ?case using "0.prems"  by fastforce
next
  case (Suc n)    
  then have l_suc:"length l > Suc i" by linarith 
  then have "i<j" 
    using Suc.hyps(2) by linarith 
  moreover then have "j-1< length l" by (simp add: Suc.prems(2) less_imp_diff_less)   
  moreover have "n = j - 1 - i"
    using Suc.hyps(2) by auto
  ultimately have "fst (l ! (j-1)) = Fault f"
    using Suc(1)[of "j-1" i ] Suc(2) 
    by (metis One_nat_def Suc.prems(1) diff_diff_cancel diff_is_0_eq' less_or_eq_imp_le nat_le_linear) 
  also have "Suc (j - 1) < length l" using Suc by arith
  ultimately have "fst (l ! (j)) = Fault f" 
    using Suc(2-4) fault_suc_i[of \<Gamma> l "j-1"  ] 
    by fastforce
  also have "j=j" using Cons using Suc.prems(2) by linarith  
  ultimately show ?case using Suc by (metis (no_types))
qed  


lemma only_one_component_tran_j:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!i) = Skip  \<or> fst (l!i) = Throw \<or> fst (l!i) = Stuck \<or> (\<exists>f. fst (l!i) = Fault f)" and 
         a2: "i\<le>j \<and> Suc j < length l" and
         a3: "\<Gamma>\<turnstile>\<^sub>c (fst (l!j), toSeq (snd (l!j)))  \<rightarrow> (fst (l!(Suc j)), toSeq (snd (l!(Suc j))))"    
   shows "P"
proof -   
   have "fst (l!j) = Skip  \<or> (fst (l!i) = Throw ) \<or> fst (l!i) = Stuck \<or> (\<exists>f. fst (l!i) = Fault f)" 
     using a0 a1  a2 a3  i_skip_all_skip by fastforce  
   moreover { 
     assume "fst (l!j) = Skip"
     then have ?thesis using a3
       using stepc_elim_cases(1) by fastforce
   }
   moreover { 
     assume a00:"fst (l!i) = Throw "
     then have a2:"i\<le>j \<and> j<length l" using a2 by auto
     then have "fst (l!j) = Throw "
       using a0 a00  
       by (metis final_glob_def last_F) 
     then have ?thesis using a3
       using stepc_elim_cases(11) by fastforce
   }    
   moreover { 
     assume a00:"fst (l!i) = Stuck "
     then have a2:"i\<le>j \<and> j<length l" using a2 by auto
     then have "fst (l!j) = Stuck "
       using a0 a00  i_stuck_all_stuck by blast 
     then have ?thesis using a3
       using stepc_elim_cases(14) by fastforce
   }  
   moreover { 
     assume a00:"\<exists>f. fst (l!i) = Fault f "
     then have a2:"i\<le>j \<and> j<length l" using a2 by auto
     then obtain f where "fst (l!j) = Fault f"
       using a0 a00  i_fault_all_fault by fastforce 
     then have ?thesis using a3       
       using stepc_elim_cases(13) by fastforce
   }  
   ultimately show ?thesis by auto  
qed     

lemma only_one_component_tran_all_j:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!i) = Skip  \<or> (fst (l!i) = Throw )" and 
         a1': "snd (l!i) \<in> q" and
         a2: "Suc i<length l" and
         a3: "\<forall>j. i\<le>j \<and> Suc j < length l \<longrightarrow> 
               (\<Gamma>\<turnstile>\<^sub>c (fst (l!j), toSeq (snd (l!j)))  \<rightarrow> 
                   (fst (l!(Suc j)), toSeq (snd (l!(Suc j)))))"  and
         a4: "env_tran_right \<Gamma> l rely \<and> Sta q rely"              
   shows "P" 
using a0 a1 a2 a3 a4 a1' only_one_component_tran_j 
by (metis lessI less_Suc_eq_le) 


lemma zero_skip_all_skip: 
      assumes a1:"(\<Gamma>, l) \<in> cptn \<and> fst (l!0) = Skip \<and>  i < length l"
      shows "fst (l!i) = Skip"
using a1 i_skip_all_skip by blast

lemma all_skip:
   assumes
      a0:"(\<Gamma>,x)\<in>cptn" and
      a1:"x!0 = (Skip,s)"
shows "(\<forall>i<length x. fst(x!i) = Skip)"
using a0 a1 zero_skip_all_skip by fastforce

lemma zero_throw_all_throw:
      assumes a1:"(\<Gamma>, l) \<in> cptn \<and> fst (l!0) = Throw \<and> 
                    i < length l \<and> snd(l!0)\<in>q"
      assumes a2: "env_tran_right \<Gamma> l rely \<and> Sta q rely" 
      shows "fst (l!i) = Throw "
using a1 a2 i_throw_all_throw by (metis le0) 

lemma only_one_component_tran_0:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "(fst (l!0) = Skip) \<or> (fst (l!0) = Throw) \<or>  
             (fst (l!0) = Stuck) \<or> (\<exists>f. fst (l!0) = Fault f)" and                           
         a2: "Suc j < length l" and
         a3: "\<Gamma>\<turnstile>\<^sub>c (fst (l!j), toSeq (snd (l!j)))  \<rightarrow> (fst (l!(Suc j)), toSeq (snd (l!(Suc j))))"              
   shows "P"      
  proof-
   have a2':"0\<le>j \<and> Suc j<length l" using a2 by arith
   show ?thesis 
   using only_one_component_tran_j[OF a0 a1  a2' a3 ] by auto
qed

lemma not_step_comp_step_env:
 assumes a0:  "(\<Gamma>, l) \<in> cptn" and
         a1: "(Suc j<length l)" and 
         a2: "(\<forall>k < j. \<not>(\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                         (fst (l!(Suc k)), toSeq (snd (l!(Suc k))))))"
  shows "(\<forall>k < j. ((\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))))"
proof -
  {fix k
   assume asm: "k<j"
   also then have "Suc k<length l" using a1 a2 by auto
   ultimately have step:"(\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>c\<^sub>e (l!(Suc k)))" 
     using a0 cptn_stepc_rtran 
     apply auto apply (erule cptn.cases, auto)
     using  a0  by fastforce
   also have "\<not>(\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                         (fst (l!(Suc k)), toSeq (snd (l!(Suc k)))))" using a2 asm by auto   
   ultimately have "((\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"      
     using step_ce_dest
     by (metis prod.exhaust_sel)
  } thus ?thesis by auto
qed

lemma cptn_i_env_same_prog:
assumes a0: "(\<Gamma>, l) \<in> cptn" and
        a1:  "\<forall>k < j. k\<ge>i \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))" and
        a2: "i\<le>j \<and> j < length l"
shows "fst (l!j) =  fst (l!i)"
using a0 a1 a2
proof (induct "j-i" arbitrary: l j i)
  case 0 thus ?case by auto    
next
  case (Suc n)     
    then have lenl:"length l>Suc 0" by fastforce    
    have "j>0" using Suc by linarith
    then obtain j1 where prev:"j=Suc j1" 
      using not0_implies_Suc by blast     
    then obtain a0 a1 l1 where l:"l=a0#l1@[a1]" 
    using Suc lenl by (metis add.commute add.left_neutral length_Cons list.exhaust list.size(3) not_add_less1 rev_exhaust)     
    then have al1_cptn:"(\<Gamma>,a0#l1)\<in> cptn"
      using Suc.prems(1) Suc.prems(3) tl_in_cptn cptn_dest_2
      by blast
    have i_j:"i\<le>j1" using Suc prev by auto
    have "\<forall>k < j1. k\<ge>i \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c((a0#l1)!k)  \<rightarrow>\<^sub>e ((a0#l1)!(Suc k)))"
    proof -
       {fix k
        assume a0:"k<j1 \<and> k\<ge>i"
        then have "(\<Gamma>\<turnstile>\<^sub>c((a0#l1)!k)  \<rightarrow>\<^sub>e ((a0#l1)!(Suc k)))" 
        using  l Suc(4) prev lenl Suc(5)
        proof -   
          have suc_k_j:"Suc k < j" using a0 prev by blast
          have j1_l_l1:"j1 < Suc (length l1)" 
            using Suc.prems(3) l prev by auto
          have "k < Suc j1"
            using `k < j1 \<and> i \<le> k` less_Suc_eq by blast
          hence f3: "k < j"
            using prev by blast
          hence ksuc:"k < Suc (Suc j1)"
            using less_Suc_eq prev by blast
          hence f4: "k < Suc (length l1)"
            using  prev Suc.prems(3) l a0 j1_l_l1 less_trans 
            by blast            
          have f6: "\<Gamma>\<turnstile>\<^sub>c l ! k \<rightarrow>\<^sub>e (l ! Suc k)"
            using f3 Suc(4) a0 by blast
          have k_l1:"k < length l1"
            using f3 Suc.prems(3) i_j l suc_k_j  by auto                            
          thus ?thesis
          proof (cases k)
            case 0 thus ?thesis using f6 l  k_l1
                by (simp add: nth_append)
          next  
            case (Suc k1) thus ?thesis 
              using f6  f4 l k_l1 
              by (simp add: nth_append)
          qed
        qed
       }thus ?thesis by auto
    qed
    then have fst:"fst ((a0#l1)!i)=fst ((a0#l1)!j1)"
      using Suc(1)[of j1 i "a0#l1"] 
            Suc(2) Suc(3) Suc(4) Suc(5) prev al1_cptn i_j
      by (metis (mono_tags, lifting) Suc_diff_le Suc_less_eq diff_Suc_1 l length_Cons length_append_singleton)
    have len_l:"length l = Suc (length (a0#l1))" using l by auto
    then have f1:"i<length (a0#l1)" using Suc.prems(3) i_j prev by linarith
    then have f2:"j1<length (a0#l1)" using Suc.prems(3) len_l prev by auto
    have i_l:"fst (l!i) = fst ((a0#l1)!i)" 
      using l prev f1 f2 fst 
      by (metis (no_types) append_Cons nth_append)
    also have j1_l:"fst (l!j1) = fst ((a0#l1)!j1)"
    using l prev f1 f2 fst 
      by (metis (no_types) append_Cons nth_append)
    then have "fst (l!i) = fst (l!j1)" using
      i_l j1_l fst by auto      
    thus ?case using Suc prev by (metis env_c_c' i_j lessI prod.collapse)          
qed  
  

lemma cptn_tran_ce_i: 
   assumes a1:"(\<Gamma>, l) \<in> cptn  \<and>  i + 1 < length l"
   shows "\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>c\<^sub>e (l!(Suc i))"
proof -
  from a1
  obtain a1 l1 where "l=a1#l1" using cptn.simps by blast
  thus  ?thesis using a1 cptn_stepc_rtran by fastforce
qed

lemma zero_final_always_env_0: 
      assumes a1:"(\<Gamma>, l) \<in> cptn" and
              a2: "fst (l!0) = Skip \<or> fst (l!0) = Throw \<or> 
                  fst (l!0) = Stuck \<or> (\<exists>f. fst(l!0) = Fault f)" and
              a2': "snd(l!0) \<in>q" and
              a3: "Suc i < length l" and
              a4: "env_tran_right \<Gamma> l rely \<and> Sta q rely"
      shows "\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))"
proof -
   have "\<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>c\<^sub>e (l!(Suc i))" using a1 a2 a3 cptn_tran_ce_i by auto   
   also have "\<not> (\<Gamma>\<turnstile>\<^sub>c (fst (l!i), toSeq (snd (l!i)))  \<rightarrow> 
                   (fst (l!(Suc i)), toSeq (snd (l!(Suc i)))))" using a1 a2 a3 a4 a2'
     using only_one_component_tran_0 by metis           
   ultimately show ?thesis
     using step_ce_dest
     by (metis prod.exhaust_sel) 
qed

lemma final_always_env_i: 
      assumes a1:"(\<Gamma>, l) \<in> cptn" and
              a2: "fst (l!0) = Skip \<or> fst (l!0) = Throw \<or> 
                  fst (l!0) = Stuck \<or> (\<exists>f. fst(l!0) = Fault f)" and
              a2': "snd(l!0) \<in>q" and
              a3: "j\<ge>i \<and> Suc j<length l" and
              a4: "env_tran_right \<Gamma> l rely \<and> Sta q rely"
      shows "\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j))"
proof -
   have ce_tran:"\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>c\<^sub>e (l!(Suc j))" using a1 a2 a3 a4 cptn_tran_ce_i by auto   
   then have "\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)) \<or> 
              \<Gamma>\<turnstile>\<^sub>c (fst (l!j), toSeq (snd (l!j)))  \<rightarrow> 
                   (fst (l!(Suc j)), toSeq (snd (l!(Suc j))))"      
     using a1 a2 a2' a3 a4 zero_final_always_env_0 by blast
   thus ?thesis
   proof
     assume "\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j))" then show ?thesis by auto
   next
     assume a01:"\<Gamma>\<turnstile>\<^sub>c (fst (l!j), toSeq (snd (l!j)))  \<rightarrow> 
                   (fst (l!(Suc j)), toSeq (snd (l!(Suc j))))"
      then  have "\<not> (\<Gamma>\<turnstile>\<^sub>c (fst (l!j), toSeq (snd (l!j)))  \<rightarrow> 
                   (fst (l!(Suc j)), toSeq (snd (l!(Suc j)))))"   
        using a1 a2 a3 a4 a2' only_one_component_tran_j [OF a1]  
        by blast
      then show ?thesis using a01 ce_tran by (simp add: step_ce.simps) 
   qed
qed


subsection {*Skip Sound*}

lemma stable_q_r_q: 
  assumes a0:"Sta q R"  and       
          a1: "snd(l!i) \<in>  q" and
          a2:"(snd(l!i), snd(l!(Suc i))) \<in> R"
  shows "snd(l!(Suc i)) \<in>  q"
using a0  a1  a2 
unfolding Sta_def  by fastforce 

lemma stability:
assumes   a0:"Sta q R"  and                 
          a1: "snd(l!j) \<in>  q" and
          a2: "j\<le>k \<and> k < (length l)" and
          a3: "n=k-j" and
          a4: "\<forall>i. j\<le>i \<and> i < k \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))" and
          a5:"env_tran_right \<Gamma> l R "
      shows "snd (l!k) \<in> q \<and> fst (l!j) = fst (l!k)"
using a0 a1 a2 a3 a4 a5 
proof (induct n arbitrary: j k)
  case 0
    thus ?case by auto
next
  case (Suc n) 
    then have "length l > j + 1" by arith     
    moreover then have "k-1< length l" using Suc by fastforce    
    moreover then have "(k - 1) - j = n" using Suc by fastforce
    moreover then have  "j\<le>k-1" using Suc by arith 
    moreover have "\<forall>i. j \<le> i \<and> i < k-1 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c (l ! i) \<rightarrow>\<^sub>e (l ! Suc i)"
      using Suc by fastforce    
    ultimately have induct:"snd (l! (k-1)) \<in> q \<and> fst (l!j) = fst (l!(k-1))" using Suc
      by blast      
    also have j_1:"k-1+1=k" using Cons Suc.prems(4) by auto 
    have f1:"\<forall>i. j\<le>i \<and> i < k \<longrightarrow> (snd((snd (\<Gamma>,l))!i), snd((snd (\<Gamma>,l))!(Suc i))) \<in>  R"
    using Suc unfolding env_tran_right_def by fastforce
    have  k1:"k - 1 < k"
      by (metis (no_types) Suc_eq_plus1 j_1 lessI)    
    then have "(snd((snd (\<Gamma>,l))!(k-1)), snd((snd (\<Gamma>,l))!(Suc (k-1)))) \<in>  R"    
    using `j \<le> k - 1` f1 by blast                           
    ultimately have "snd (l!k) \<in>  q" using stable_q_r_q Suc(2)  Suc(5)  by fastforce
    also have "fst (l!j) = fst (l!k)"
    proof -
      have "\<Gamma>\<turnstile>\<^sub>c (l ! (k-1)) \<rightarrow>\<^sub>e (l ! k)" using Suc(6) k1 `j\<le>k-1` by fastforce
      thus ?thesis using k1 prod.collapse env_c_c' induct by metis
    qed
    ultimately show ?case by meson
qed

lemma stable_only_env_i_j: 
  assumes a0:"Sta q R"  and                 
          a1: "snd(l!i) \<in> q" and
          a2: "i<j \<and> j < (length l)" and
          a3: "n=j-i-1" and
          a4: "\<forall>k\<ge>i. k < j \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))" and
          a5: "env_tran_right \<Gamma> l R"
      shows "snd (l!j) \<in>  q"
using a0 a1 a2 a3 a4 a5  by (meson less_imp_le_nat  stability)

  
lemma stable_only_env_1: 
  assumes a0:"Sta q R"  and                 
          a1: "snd(l!i) \<in>  q" and
          a2: "i<j \<and> j < (length l)" and
          a3: "n=j-i-1" and
          a4: "\<forall>i. Suc i < length l \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))" and
          a5: "env_tran_right \<Gamma> l R"
      shows "snd (l!j) \<in>  q"
using a0 a1 a2 a3 a4 a5 
by (meson stable_only_env_i_j less_trans_Suc)


lemma stable_only_env_q: 
  assumes a0:"Sta q R"  and                 
          a1: "\<forall>i. Suc i < length l \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))" and
          a2: "env_tran \<Gamma> q l R"
      shows "\<forall>i. i < length l \<longrightarrow> snd (l!i) \<in>  q"
proof (cases "0 < length l")
  case False thus ?thesis using a2 unfolding env_tran_def by fastforce 
next
  case True 
  thus ?thesis 
  proof - {
    fix i
    assume aa1:"i < length l"
    have post_0:"snd (l ! 0) \<in>  q " 
      using a2 unfolding env_tran_def by auto
    then have "snd (l ! i) \<in>  q"     
    proof (cases i) 
      case 0 thus ?thesis using post_0 by auto
    next
      case (Suc n) 
      
      have "env_tran_right \<Gamma> l R" 
        using a2 env_tran_right_def unfolding env_tran_def by auto
      also have "0<i" using Suc by auto
      ultimately show ?thesis 
        using post_0 stable_only_env_1  a0 a1 a2 aa1  by blast
    qed
  } then show ?thesis by auto qed
qed



lemma Skip_sound1: 
  assumes a0:"Sta q R" and   
   a10:"c \<in> cp \<Gamma> Skip s" and
   a11:"c \<in> assum(q, R)" 
   shows "c \<in> comm (G, (q,a)) F"
proof -  
  obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce  
  {     
    have cp:"l!0=(Skip,s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce   
    have assum:"snd(l!0) \<in> q \<and> (\<forall>i. Suc i<length l \<longrightarrow>
             (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
               (snd(l!i), snd(l!(Suc i))) \<in> R)" 
      using a11 c_prod unfolding assum_def by simp
    have concl:"(\<forall>i. Suc i<length l \<longrightarrow> 
                    \<Gamma>1\<turnstile>\<^sub>c (fst (l!i), toSeq (snd (l!i)))  \<rightarrow> 
                      (fst (l!(Suc i)), toSeq (snd (l!(Suc i)))) \<longrightarrow>                             
             (snd(l!i), snd(l!(Suc i))) \<in> G)"
    proof -
    { fix i
      assume asuc:"Suc i<length l"        
      then have "\<not> (\<Gamma>1\<turnstile>\<^sub>c (fst (l!i), toSeq (snd (l!i)))  \<rightarrow> 
                      (fst (l!(Suc i)), toSeq (snd (l!(Suc i)))))"
        by (metis Suc_lessD cp  prod.sel(1) stepc_elim_cases(1) zero_skip_all_skip)
    } thus ?thesis by auto qed
    have concr:"(final_glob (last l)  \<longrightarrow> fst (last l) \<notin> Fault ` F \<longrightarrow>
               ((fst (last l) = Skip \<and> snd (last l) \<in>  q)) \<or>
                (fst (last l) = Throw \<and> snd (last l) \<in> (a)))"
    proof-
    { 
      assume valid:"final_glob (last l)" and a00:"fst (last l) \<notin> Fault ` F"
      have len_l:"length l > 0" using cp using cptn.simps by blast 
      then obtain a l1 where l:"l=a#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
      have last_l:"last l = l!(length l-1)"
        using last_length [of a l1] l by fastforce
      then have fst_last_skip:"fst (last l) = Skip"             
        by (metis `0 < length l` cp diff_less fst_conv zero_less_one zero_skip_all_skip)                           
      have last_q: "snd (last l) \<in> q"    
      proof -
        have env: "env_tran \<Gamma> q l R" using env_tran_def assum cp by blast
        have env_right:"env_tran_right \<Gamma> l R " using  a0 env_tran_right_def assum cp by metis
        also have "snd(l!0) \<in>q" 
          using assum by auto
        ultimately have all_tran_env: 
          "\<forall>i. Suc i < length l \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))"
          using final_always_env_i cp zero_final_always_env_0 a0
          using all_skip len_l by blast
        then have "\<forall>i. i < length l \<longrightarrow> snd (l!i) \<in> q"
          using stable_only_env_q  a0  env  by fastforce
        thus ?thesis using last_l using len_l by fastforce    
      qed
      note res = conjI [OF fst_last_skip last_q]
    } thus ?thesis by auto 
    qed
    note res = conjI [OF concl concr]               
  } thus ?thesis using c_prod unfolding comm_def by auto 
qed


lemma Skip_sound: 
  "Sta q R \<Longrightarrow>          
   \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> Skip sat [q,R, G, q,a]" 
proof-
  assume
  a0:"Sta q R"      
  {
    fix s
    have ass:"cpn n \<Gamma> Skip s \<inter> assum(q, R) \<subseteq> comm(G, (q,a)) F"
    proof-      
    { fix c
      assume a10:"c \<in> cpn n \<Gamma> Skip s" and a11:"c \<in> assum(q, R)"
      then have a10:"c\<in>cp \<Gamma> Skip s"
        using cp_def cpn_def cptn_if_cptn_mod cptn_mod_nest_cptn_mod by blast
      have "c\<in>comm(G, (q,a)) F" using Skip_sound1[OF a0  a10 a11] by auto      
    } thus ?thesis by auto
    qed 
  } 
  thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed

lemma Throw_sound1: 
  assumes a1:"Sta a R" and  
   a10:"c \<in> cp \<Gamma> Throw s" and
   a11:"c \<in> assum(a, R)"
shows "c \<in> comm (G, (q,a)) F"
proof -  
  obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce     
  {    
    have cp:"l!0=(Throw,s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
    have assum:"snd(l!0) \<in>  a \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
             (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
               (snd(l!i), snd(l!(Suc i))) \<in> (R))" 
      using a11 c_prod unfolding assum_def by simp
    then have env_tran:"env_tran_right \<Gamma> l R" using cp env_tran_right_def by auto
    have a_normal:"snd(l!0)  \<in> a"
      using assum by auto
    have concl:"(\<forall>i. Suc i<length l \<longrightarrow> 
           \<Gamma>1\<turnstile>\<^sub>c (fst (l!i), toSeq (snd (l!i)))  \<rightarrow> 
                      (fst (l!(Suc i)), toSeq (snd (l!(Suc i)))) \<longrightarrow>                                           
             (snd(l!i), snd(l!(Suc i))) \<in>  (G))"
    proof -
    { fix i
      assume asuc:"Suc i<length l"
      then have asuci:"i<length l" by fastforce
      then have "fst (l ! 0) = LanguageCon.com.Throw" using cp by auto     
      then have "fst (l ! i) = Throw "      
        using cp a1 assum a_normal env_tran asuci zero_throw_all_throw
        by fastforce
      then have "\<not> (\<Gamma>1\<turnstile>\<^sub>c (fst (l!i), toSeq (snd (l!i)))  \<rightarrow> 
                      (fst (l!(Suc i)), toSeq (snd (l!(Suc i)))))"        
        using stepc_elim_cases(11) by fastforce            
    } thus ?thesis by auto qed
    have concr:"(final_glob (last l)  \<longrightarrow>fst (last l) \<notin> Fault ` F \<longrightarrow> 
               ((fst (last l) = Skip \<and> snd (last l) \<in>  q)) \<or>
                (fst (last l) = Throw \<and> snd (last l) \<in> a))"
    proof-
    { 
      assume valid:"final_glob (last l)" and a00: "fst (last l) \<notin> Fault ` F"
      have len_l:"length l > 0" using cp using cptn.simps by blast 
      then obtain a1 l1 where l:"l=a1#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
      have last_l:"last l = l!(length l-1)"
        using last_length [of a1 l1] l by fastforce
      then have fst_last_skip:"fst (last l) = Throw"
        by (metis a1 a_normal cp diff_less env_tran fst_conv len_l zero_less_one zero_throw_all_throw)                        
      have last_q: "snd (last l) \<in> a"    
      proof -
        have env: "env_tran \<Gamma> a l R" using env_tran_def assum cp by blast
        have env_right:"env_tran_right \<Gamma> l R" using env_tran_right_def assum cp by metis
        then have all_tran_env: "\<forall>i. Suc i < length l \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i))"
        using final_always_env_i a1 assum cp zero_final_always_env_0 by fastforce            
        then have "\<forall>i. i < length l \<longrightarrow> snd (l!i) \<in> a"
        using stable_only_env_q  a1  env by fastforce
        thus ?thesis using last_l using len_l by fastforce    
      qed                
      note res = conjI [OF fst_last_skip last_q]
    } thus ?thesis by auto qed
    note res = conjI [OF concl concr]               
   }              
   thus ?thesis using c_prod unfolding comm_def by auto 
qed          

lemma Throw_sound: 
  "Sta a R  \<Longrightarrow>   
   \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> Throw sat [a, R, G, q,a]"
proof -  
  assume a1:"Sta a R" 
  {
    fix s
    have ass:"cpn n \<Gamma> Throw s \<inter> assum(a, R) \<subseteq> comm(G, (q,a)) F"
    proof-      
    { fix c
      assume a10:"c \<in> cpn n \<Gamma> Throw s" and a11:"c \<in> assum(a, R)"
      then have a10:"c\<in>cp \<Gamma> Throw s"
        using cp_def cpn_def cptn_if_cptn_mod cptn_mod_nest_cptn_mod by blast
      have "c\<in>comm(G, (q,a)) F" using Throw_sound1[OF a1  a10 a11] by auto      
    } thus ?thesis by auto
    qed 
  } 
  thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed

lemma no_comp_tran_before_i_0_g:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!0) = c " and         
         a2: "Suc i<length l \<and> 
               (\<Gamma>\<turnstile>\<^sub>c (fst (l!i), toSeq (snd (l!i)))  \<rightarrow> 
               (fst (l!(Suc i)), toSeq (snd (l!(Suc i)))))" and
         a3: "j < i \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l!j), toSeq (snd (l!j)))  \<rightarrow> 
                            (fst (l!(Suc j)), toSeq (snd (l!(Suc j)))))" and
         a4: "\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))" and
         a5: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c, s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> 
                         c1=Skip \<or> c1 = Throw \<or> c1 = Stuck \<or> (\<exists>f. c1 = Fault f)"
   shows "P"
  proof -
   have "Suc j < length l" using a0 a1 a2 a3 a4 by fastforce
   then have "fst (l!j) = c" 
     using a0 a1 a2 a3 a4 cptn_env_same_prog[of \<Gamma> l j] by fastforce
   then obtain s s1 c1 where l_0: "l!j = (c, s) \<and> l!(Suc j) = (c1,s1)"  
     by (metis (no_types) prod.collapse)    
  
   then have suc_0_skip: "fst (l!Suc j) = Skip \<or> fst (l!Suc j) = Throw \<or> 
                          fst (l!Suc j) = Stuck \<or> (\<exists>f. fst (l!Suc j) = Fault f)" 
      using a5  a3  \<open>fst (l ! j) = c\<close> a3 a5 by blast 
   thus ?thesis using only_one_component_tran_j
    proof -
      have "\<forall>n na. \<not> n < na \<or> Suc n \<le> na"
        using Suc_leI by satx  
      thus ?thesis using only_one_component_tran_j[OF a0] suc_0_skip  a0 a2 a3
        using imageE by blast          
    qed
qed

lemma no_comp_tran_before_i:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = c" and        
         a2: "Suc i<length l \<and> k\<le>i \<and> 
              (\<Gamma>\<turnstile>\<^sub>c (fst (l!i), toSeq (snd (l!i)))  \<rightarrow> 
                   (fst (l!(Suc i)), toSeq (snd (l!(Suc i)))))" and
         a3: "k\<le>j \<and> j < i \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l!j), toSeq (snd (l!j)))  \<rightarrow> 
                            (fst (l!(Suc j)), toSeq (snd (l!(Suc j)))))" and
         a4: "\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))" and
          a5: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c, s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> 
                        c1=Skip \<or> c1=Throw \<or> c1 = Stuck \<or> (\<exists>f. c1 = Fault f)  "
   shows "P"
using a0 a1 a2 a3 a4 a5 
proof (induct k arbitrary: l i j)
  case 0 thus ?thesis using no_comp_tran_before_i_0_g by blast
next
  case (Suc n) 
  then obtain a1 l1 where l: "l=a1#l1"
    by (metis less_nat_zero_code list.exhaust list.size(3))
  then have l1notempty:"l1\<noteq>[]" using Suc by force    
  then obtain i' where i': "i=Suc i'" using Suc 
    using less_imp_Suc_add by blast
  then obtain j' where j': "j=Suc j'" using Suc
    using Suc_le_D by blast      
  have "(\<Gamma>,l1)\<in>cptn" using Suc l
    using tl_in_cptn l1notempty by blast
  moreover have "fst (l1 ! n) = c"
    using Suc l l1notempty by force  
  moreover have "Suc i' < length l1 \<and> n \<le> i' \<and> \<Gamma>\<turnstile>\<^sub>c (fst (l1!i'), toSeq (snd (l1!i')))  \<rightarrow> 
               (fst (l1!(Suc i')), toSeq (snd (l1!(Suc i'))))"
    using Suc l l1notempty i' by auto
  moreover have "n \<le> j' \<and> j' < i' \<and> \<Gamma>\<turnstile>\<^sub>c (fst (l1!j'), toSeq (snd (l1!j')))  \<rightarrow> 
               (fst (l1!(Suc j')), toSeq (snd (l1!(Suc j'))))"
    using Suc l l1notempty i' j' by auto
  moreover have "\<forall>k<j'. \<Gamma>\<turnstile>\<^sub>c l1 ! k \<rightarrow>\<^sub>e (l1 ! Suc k)"
    using Suc l l1notempty j' by auto    
  ultimately show ?case using Suc(1)[of l1 i' j' ]  Suc(7)   j' l by auto
qed

lemma exists_first_occ: "P (n::nat) \<Longrightarrow> \<exists>m. P m \<and> (\<forall>i<m. \<not> P i)"
proof (induct n)
  case 0 thus ?case by auto
next
  case (Suc n) thus ?case
  by (metis ex_least_nat_le not_less0) 
qed

lemma exist_first_comp_tran':
assumes a1: "Suc i<length l \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l!i), toSeq (snd (l!i)))  \<rightarrow> 
                                     (fst (l!(Suc i)), toSeq (snd (l!(Suc i)))))"      
shows "\<exists>j. (Suc j<length l \<and>  (\<Gamma>\<turnstile>\<^sub>c (fst (l!j), toSeq (snd (l!j)))  \<rightarrow> 
                                   (fst (l!(Suc j)), toSeq (snd (l!(Suc j)))))) \<and> 
           (\<forall>k < j. \<not>(\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                          (fst (l!(Suc k)), toSeq (snd (l!(Suc k))))))"
proof -
  let ?P =  "(\<lambda>n. Suc n<length l \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l!n), toSeq (snd (l!n)))  \<rightarrow> 
                                     (fst (l!(Suc n)), toSeq (snd (l!(Suc n))))))"
  show ?thesis using exists_first_occ[of ?P i] a1 by auto  
qed

lemma exist_first_comp_tran:
assumes a0:"(\<Gamma>, l) \<in> cptn" and
        a1: "Suc i<length l \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l!i), toSeq (snd (l!i)))  \<rightarrow> 
                                   (fst (l!(Suc i)), toSeq (snd (l!(Suc i)))))"      
shows "\<exists>j. j\<le>i \<and>  (\<Gamma>\<turnstile>\<^sub>c (fst (l!j), toSeq (snd (l!j)))  \<rightarrow> 
                    (fst (l!(Suc j)), toSeq (snd (l!(Suc j))))) \<and> 
           (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
proof -
  obtain j where  pj:"(Suc j<length l \<and>  
                       (\<Gamma>\<turnstile>\<^sub>c (fst (l!j), toSeq (snd (l!j)))  \<rightarrow> 
                           (fst (l!(Suc j)), toSeq (snd (l!(Suc j)))))) \<and> 
                      (\<forall>k < j. \<not>(Suc k<length l \<and>  (\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                                  (fst (l!(Suc k)), toSeq (snd (l!(Suc k)))))))"
    using a1 exist_first_comp_tran' by fast
  then have "j\<le>i" using a1 pj by (cases "j\<le>i", auto)
  moreover have "\<Gamma>\<turnstile>\<^sub>c (fst (l!j), toSeq (snd (l!j)))  \<rightarrow> 
                     (fst (l!(Suc j)), toSeq (snd (l!(Suc j))))" using pj by auto
  moreover have "(\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))" 
  proof -
    {fix k
    assume kj:"k<j"
    then have "Suc k \<ge> length l \<or>  
                 \<not> (Suc k<length l \<and>  (\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                 (fst (l!(Suc k)), toSeq (snd (l!(Suc k)))))) " 
      using pj by auto
    then have "(\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))"
    proof
      {assume "length l \<le> Suc k" 
       thus ?thesis using kj pj by auto
      }
      {assume "\<not> (Suc k<length l \<and>  (\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                 (fst (l!(Suc k)), toSeq (snd (l!(Suc k))))))"
       also have "k + 1 < length l" using kj pj by auto
       ultimately show ?thesis
         using a0 cptn_tran_ce_i step_ce_dest
         by (metis Suc_eq_plus1 prod.exhaust_sel)
      }
    qed
    } thus ?thesis by auto
  qed
  ultimately show ?thesis by auto
qed


lemma skip_com_all_skip:
assumes a0:"(\<Gamma>, l) \<in> cptn" and
        a1:"fst (l!i) = Skip" and
        a2:"i<length l" 
   shows "\<forall>j. j\<ge>i \<and> j <length l \<longrightarrow> fst (l!j) = Skip"
using a0 a1 a2
proof (induct "length l - (i + 1)" arbitrary: i)
  case 0  thus ?case by (metis Suc_eq_plus1 Suc_leI diff_is_0_eq nat_less_le zero_less_diff) 
next 
  case (Suc n)
  then have l:"Suc i < length l" by arith
  have n:"n = (length l) - (Suc i + 1)" using Suc by arith
  then have "\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), snd(l!i)) \<rightarrow>\<^sub>c\<^sub>e (fst (l ! Suc i), snd(l ! Suc i))" 
     using cptn_tran_ce_i Suc
     by (metis Suc_eq_plus1 l prod.collapse)
  note x=step_ce_dest[OF this]   
  then have or:"fst(l!Suc i) = Skip" 
  proof
    {assume "\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), snd (l ! i)) \<rightarrow>\<^sub>e (fst (l ! Suc i), snd (l ! Suc i))" 
     thus ?thesis using Suc(4) by (metis env_c_c')
    }
  next
    {assume step:"\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                      (fst (l ! Suc i), toSeq (snd (l ! Suc i)))" 
     {assume "fst(l!i) = Skip" 
      then have ?thesis using step
        using final_glob_def no_step_final'
        using stepc_elim_cases(1) by fastforce
     }note left = this
     {assume "fst(l!i) = Throw"
      then have ?thesis using step stepc_elim_cases
      proof -
        have "\<exists>x. l ! Suc i = (LanguageCon.com.Skip, x)"
          using Suc.prems(2) \<open>fst (l ! i) = LanguageCon.com.Throw\<close> by auto
        then show ?thesis
          by fastforce
      qed      
     } then show ?thesis using Suc(4) left by auto
    }
  qed
  show ?case using Suc(1)[OF n a0 or l] Suc(4) Suc(5) by (metis le_less_Suc_eq not_le) 
qed

lemma terminal_com_all_term:
assumes a0:"(\<Gamma>, l) \<in> cptn" and
        a1:"fst (l!i) = Skip \<or> fst (l!i) = Throw  \<or> 
                 fst (l! i) = Stuck \<or> (\<exists>f. fst (l! i) = Fault f)" and
        a2:"i<length l" 
   shows "\<forall>j. j\<ge>i \<and> j <length l \<longrightarrow> fst (l!j) = Skip \<or> fst (l!j) = Throw  \<or> 
                 fst (l! j) = Stuck \<or> (\<exists>f. fst (l! j) = Fault f)"
using a0 a1 a2
proof (induct "length l - (i + 1)" arbitrary: i)
  case 0  thus ?case by (metis Suc_eq_plus1 Suc_leI diff_is_0_eq nat_less_le zero_less_diff) 
next 
  case (Suc n)
  then have l:"Suc i < length l" by arith
  have n:"n = (length l) - (Suc i + 1)" using Suc by arith
  then have "\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), snd (l ! i)) \<rightarrow>\<^sub>c\<^sub>e (fst (l ! Suc i), snd (l ! Suc i))" 
    using cptn_tran_ce_i Suc
    by (metis Suc_eq_plus1 l prod.collapse)
  then have "\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> (fst (l ! Suc i), toSeq (snd (l ! Suc i))) \<or> 
             \<Gamma>\<turnstile>\<^sub>c (l ! i) \<rightarrow>\<^sub>e (l ! Suc i)" 
    using step_ce_dest by fastforce  
  then have or:"fst(l!Suc i) = Skip \<or> fst(l!Suc i) = Throw  \<or> 
                 fst (l!Suc i) = Stuck \<or> (\<exists>f. fst (l!Suc i) = Fault f)" 
  proof
    {assume "\<Gamma>\<turnstile>\<^sub>c (l ! i) \<rightarrow>\<^sub>e (l ! Suc i)" 
     thus ?thesis using Suc(4) by (metis env_c_c' prod.collapse)
    }
  next
    {assume step:"\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                      (fst (l ! Suc i), toSeq (snd (l ! Suc i)))" 
      show ?thesis using step stepc_elim_cases
      proof -
        obtain dd :: 'd where
          "fst (l ! i) = LanguageCon.com.Throw \<or> fst (l ! i) = com.Stuck \<or> fst (l ! i) = com.Fault dd"
          by (metis (no_types) Suc.prems(2) local.step stepc_elim_cases(1))
        then show ?thesis
          by (metis (full_types) local.step stepc_elim_cases(11) stepc_elim_cases(13) stepc_elim_cases(14))
      qed 
    } 
  qed
  show ?case using Suc(1)[OF n a0 or l] Suc(4) Suc(5) 
    by (metis le_less_Suc_eq not_le) 
qed

lemma only_one_c_comp_tran:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!0) = c" and         
         a2: "Suc i<length l \<and> 
             (\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                  (fst (l ! Suc i), toSeq (snd (l ! Suc i))))" and
         a3: "i < j \<and> Suc j < length l \<and> 
             \<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                 (fst (l ! Suc j), toSeq (snd (l ! Suc j))) \<and> fst (l!j) = c" and
         a4: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c, s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> 
                        ((c1=Skip) \<or> (c1=Throw) \<or> c1 = Stuck \<or> (\<exists>f. c1 = Fault f)) " and
         a5: "(\<forall>k < i. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
   shows "P"
proof - 
  have fst:"fst (l!i) = c" using a0 a1 a5
    by (simp add: a2 cptn_env_same_prog)
  then have suci:"fst (l!Suc i) = Skip \<or> fst (l!Suc i) = Throw \<or> 
                 fst (l!Suc i) = Stuck \<or> (\<exists>f. fst (l!Suc i) = Fault f)" 
    using a4 a2 by metis 
  then have "fst (l!j) = Skip \<or> fst (l!j) = Throw \<or> 
                 fst (l! j) = Stuck \<or> (\<exists>f. fst (l! j) = Fault f)" 
  proof -
    have "Suc i \<le> j"
      using Suc_leI a3 by presburger
    then show ?thesis
      using Suc_lessD  terminal_com_all_term[OF a0 suci] a2 a3
      by blast
  qed 
  moreover {
    assume "fst (l ! j) = Skip"
    then have ?thesis using a3 
      using stepc_elim_cases(1) by fastforce
  }
  moreover
    {assume asm:"fst (l ! j) = Throw"
     then have ?thesis
       using a3 stepc_elim_cases(11) by fastforce              
   } 
  moreover
    {assume asm:"fst (l ! j) = Stuck"
     then have ?thesis
       using a3 stepc_elim_cases(14) by fastforce              
   } 
  moreover
    {assume asm:"\<exists>f. fst (l ! j) = Fault f"
     then have ?thesis
       using a3 stepc_elim_cases(13) by fastforce              
    } ultimately show ?thesis by fastforce
  qed


lemma only_one_component_tran1:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!0) = c" and         
         a2:"Suc i<length l \<and> 
             (\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                  (fst (l ! Suc i), toSeq (snd (l ! Suc i))))" and
         a3: "j \<noteq> i \<and> Suc j < length l \<and> 
                  \<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                 (fst (l ! Suc j), toSeq (snd (l ! Suc j))) \<and> fst (l!j) = c" and
         a4: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c, s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> 
                        ((c1=Skip) \<or> (c1=Throw) \<or> c1 = Stuck \<or> (\<exists>f. c1 = Fault f)) "
   shows "P"
proof (cases "j=i")
  case True thus ?thesis using a3 by auto
next
  case False note j_neq_i=this 
  thus ?thesis
  proof (cases "j<i")
    case True 
    thus ?thesis 
      using a0 a2 a3 a4   True only_one_component_tran_j Suc_leI 
      by blast
  next
    case False 
    obtain j1 
    where all_ev:"j1\<le>i \<and>  
                 \<Gamma>\<turnstile>\<^sub>c (fst (l ! j1), toSeq (snd (l ! j1))) \<rightarrow> 
                 (fst (l ! Suc j1), toSeq (snd (l ! Suc j1))) \<and> 
                 (\<forall>k < j1. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
      using a0 a2 a3 exist_first_comp_tran by blast
    then have fst:"fst (l!j1) = c" 
      using a0 a1 a2 cptn_env_same_prog le_imp_less_Suc less_trans_Suc by blast
    have suc:"Suc j1 < length l \<and> \<Gamma>\<turnstile>\<^sub>c (fst (l ! j1), toSeq (snd (l ! j1))) \<rightarrow> 
                 (fst (l ! Suc j1), toSeq (snd (l ! Suc j1)))" using all_ev a2
       using Suc_lessD le_eq_less_or_eq less_trans_Suc by linarith
    have evs:"(\<forall>k < j1. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))" using all_ev by auto
    have j:"j1 < j \<and> Suc j < length l \<and> 
              \<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
              (fst (l ! Suc j), toSeq (snd (l ! Suc j))) \<and> fst (l ! j) = c"
      using a3 all_ev False by auto
    then show ?thesis 
      using only_one_c_comp_tran[OF a0 a1 suc j a4 evs] by auto   
  qed
qed  
 
lemma only_one_component_tran_i:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = c" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                  (fst (l ! Suc i), toSeq (snd (l ! Suc i))))" and
         a3: "k\<le>j \<and> j \<noteq> i \<and> Suc j < length l \<and> 
                 \<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                 (fst (l ! Suc j), toSeq (snd (l ! Suc j))) \<and> fst (l!j) = c" and
         a4: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c, s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> 
                        ((c1=Skip) \<or> (c1=Throw) \<or> c1 = Stuck \<or> (\<exists>f. c1 = Fault f)) "
   shows "P"
using a0 a1 a2 a3 a4 
proof (induct k arbitrary: l i j )
  case 0 show ?thesis using only_one_component_tran1[OF 0(1) 0(2) ]  0 by blast
next
  case (Suc n) 
   then obtain a1 l1 where l: "l=a1#l1"
    by (metis less_nat_zero_code list.exhaust list.size(3))
  then have l1notempty:"l1\<noteq>[]" using Suc by force    
  then obtain i' where i': "i=Suc i'" using Suc 
    using less_imp_Suc_add using Suc_le_D by meson 
  then obtain j' where j': "j=Suc j'" using Suc
    using Suc_le_D by meson      
  have a0:"(\<Gamma>,l1)\<in>cptn" using Suc l
    using tl_in_cptn l1notempty by meson
  moreover have a1:"fst (l1 ! n) = c"
    using Suc l l1notempty by force  
  moreover have a2:"Suc i' < length l1 \<and> n \<le> i' \<and> \<Gamma>\<turnstile>\<^sub>c (fst (l1!i'), toSeq (snd (l1!i')))  \<rightarrow> 
               (fst (l1!(Suc i')), toSeq (snd (l1!(Suc i'))))"
    using Suc l l1notempty i' by auto
  moreover have a3:"n \<le> j' \<and> j' \<noteq> i' \<and> Suc j' < length l1 \<and> \<Gamma>\<turnstile>\<^sub>c (fst (l1!j'), toSeq (snd (l1!j')))  \<rightarrow> 
               (fst (l1!(Suc j')), toSeq (snd (l1!(Suc j')))) \<and> fst (l1!j') = c"
    using Suc l l1notempty i' j' by auto
  show ?case using Suc(1)[OF a0 a1 a2 a3  a4] by auto
qed

lemma only_one_component_tran:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = c" and         
         a2: "k\<le>i \<and>  i \<noteq> j \<and> Suc i<length l \<and> 
                  (\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                  (fst (l ! Suc i), toSeq (snd (l ! Suc i)))) \<and>   fst (l!i) = c" and
         a3: "k\<le>j \<and> Suc j < length l" and
         a4: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> 
                        ((c1=Skip) \<or> (c1=Throw) \<or> c1 = Stuck \<or> (\<exists>f. c1 = Fault f))" 
   shows "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
using a0 a1 a2 a3 a4  only_one_component_tran_i
proof -
  {assume "\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                (fst (l ! Suc j), toSeq (snd (l ! Suc j)))" 
     then have j:"Suc j<length l \<and> k\<le>j \<and> 
                 (\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                (fst (l ! Suc j), toSeq (snd (l ! Suc j))))" using a3 by auto
     have ?thesis using only_one_component_tran_i[OF a0 a1 j a2 a4 ] 
       by blast 
   }

   moreover 
   { assume "\<not>\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                (fst (l ! Suc j), toSeq (snd (l ! Suc j)))"
     then have ?thesis
       by (metis Suc_eq_plus1 a0 a3 cptn_tran_ce_i prod.collapse step_ce_dest)
   }
   ultimately show ?thesis by auto
qed
  
lemma only_one_component_tran_all_env:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = c" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> 
                (\<Gamma>\<turnstile>\<^sub>c (fst (l!i), toSeq (snd (l!i)))  \<rightarrow> 
                 (fst (l!(Suc i)), toSeq (snd (l!(Suc i))))) \<and> fst (l!i) = c" and
         a3: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> 
                        ((c1=Skip) \<or> (c1=Throw) \<or> c1 = Stuck \<or> (\<exists>f. c1 = Fault f))"
   shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
proof -
  {fix j
  assume ass:"k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l)"
  then have a2:"k \<le> i \<and> i \<noteq> j \<and> Suc i < length l \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l!i), toSeq (snd (l!i)))  \<rightarrow> 
               (fst (l!(Suc i)), toSeq (snd (l!(Suc i))))) \<and> fst (l ! i) = c"
    using a2 by auto
  then have "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))" 
    using only_one_component_tran[OF a0 a1 ] a2 a3 ass  by blast
  } thus ?thesis by auto
qed

lemma only_one_component_tran_all_not_comp:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = c" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> ((\<Gamma>\<turnstile>\<^sub>c (fst (l!i), toSeq (snd (l!i)))  \<rightarrow> 
               (fst (l!(Suc i)), toSeq (snd (l!(Suc i)))))) \<and> fst (l!i) = c" and
         a3: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(c, s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> 
                        ((c1=Skip) \<or> (c1=Throw) \<or> c1 = Stuck \<or> (\<exists>f. c1 = Fault f))"
       shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> 
                   \<not>((\<Gamma>\<turnstile>\<^sub>c (fst (l!j), toSeq (snd (l!j)))  \<rightarrow> 
                      (fst (l!(Suc j)), toSeq (snd (l!(Suc j))))))"
proof -
  {fix j
  assume ass:"k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l)"
  then have "\<not>(\<Gamma>\<turnstile>\<^sub>c (fst (l!j), toSeq (snd (l!j)))  \<rightarrow> 
                      (fst (l!(Suc j)), toSeq (snd (l!(Suc j)))))"    
      using a0 a1 a2 a3  only_one_component_tran_i ass by blast   
  } thus ?thesis by auto             
qed

lemma final_exist_component_tran1:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
          a1: "fst (l!i) = c" and        
          a3: "i\<le>j \<and> j < length l \<and> final_glob (l!j)" and          
          a5: "c\<noteq>Skip \<and> c\<noteq>Throw \<and> c\<noteq>Stuck \<and> (\<forall>f. c\<noteq>Fault f)"
  shows "\<exists>k. k\<ge>i \<and> k<j \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                      (fst (l!(Suc k)), toSeq (snd (l!(Suc k)))))"
proof -
  {assume a00:"\<forall>k. k\<ge>i \<and>  k<j \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                      (fst (l!(Suc k)), toSeq (snd (l!(Suc k)))))" 
    then have "\<forall>k. k\<ge>i \<and>  k<j \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))"
      by (metis (no_types) Suc_eq_plus1 a0 a3 cptn_tran_ce_i less_trans_Suc 
              prod.exhaust_sel step_ce_dest)
   then have "fst (l!j) =  fst (l!i)" using cptn_i_env_same_prog a0 a3 by blast 
   then have False using a3 a1 a5 unfolding final_glob_def by auto
  }  
  thus ?thesis by auto
qed  

lemma final_exist_component_tran:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
          a1: "fst (l!i) = c" and                         
          a2: "i\<le>j \<and> j < length l \<and> final_glob (l!j)" and          
          a3: "c\<noteq>Skip \<and> c\<noteq>Throw \<and> c\<noteq>Stuck \<and> (\<forall>f. c\<noteq>Fault f)"
  shows "\<exists>k. k\<ge>i \<and> k<j \<and> \<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                         (fst (l!(Suc k)), toSeq (snd (l!(Suc k))))"
proof -
  {assume "\<forall>k. k\<ge>i \<and>  k<j \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                                 (fst (l!(Suc k)), toSeq (snd (l!(Suc k)))))" 
    then have "\<forall>k. k\<ge>i \<and>  k<j \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))"
       by (metis (no_types) Suc_eq_plus1 a0 a2 cptn_tran_ce_i less_trans_Suc 
              prod.exhaust_sel step_ce_dest)
   then have "fst (l!j) =  fst (l!i)" using cptn_i_env_same_prog a0 a2 by blast 
   then have False using a2 a1 a3 unfolding final_glob_def by auto
  }  
  thus ?thesis by auto
qed

lemma suc_not_final_final_c_tran:
 assumes a0: "(\<Gamma>, l) \<in> cptn " and 
         a1: "Suc j< length l \<and> \<not>final_glob (l!j) \<and> final_glob (l!Suc j)"
 shows "\<Gamma>\<turnstile>\<^sub>c (fst (l!j), toSeq (snd (l!j)))  \<rightarrow> 
          (fst (l!(Suc j)), toSeq (snd (l!(Suc j))))"
proof -
   obtain x xs where l:"l = x#xs" using a0 cptn.simps by blast
   obtain c1 s1 c2 s2 where l1:"l!j = (c1,s1) \<and> l!(Suc j) = (c2,s2)" using a1
     using prod.exhaust_sel by blast 
   have "\<not> \<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j))" 
   proof -
      { assume a:"\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j))"
        then have eq_fst:"fst (l!j) = fst (l!Suc j)" by (metis env_c_c' prod.collapse)
        { assume "fst (l!Suc j) = Skip"
          then have "False" using a1 eq_fst unfolding final_glob_def by fastforce
        }note p1=this
        { assume "fst (l!Suc j) = Throw " 
          then have "False" using a1 eq_fst unfolding final_glob_def
          by (metis local.l1)
        }
        then have False using a1 p1 eq_fst unfolding final_glob_def
          by (auto simp add: eq_fst)
      } thus ?thesis by auto
   qed
   also have "\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>c\<^sub>e (l!(Suc j))" using l cptn_stepc_rtran a0 a1 by fastforce  
   ultimately show ?thesis using step_ce_not_step_e_step_c local.l1 by fastforce 
qed
 
lemma final_exist_component_tran_final:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and                                  
          a2: "i\<le>j \<and> j < length l \<and> final_glob (l!j)" and                             
          a3: "\<not>final_glob(l!i)" 
  shows "\<exists>k. k\<ge>i \<and> k<j \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                           (fst (l!(Suc k)), toSeq (snd (l!(Suc k))))) \<and> final_glob(l!(Suc k))"
proof -
  let ?P = "\<lambda>j. i\<le>j \<and> j < length l \<and> final_glob (l!j)"
  obtain k where k:"?P k \<and> (\<forall>i<k. \<not> ?P i)" using a2 exists_first_occ[of ?P j] by auto
  then have i_k_not_final:"\<forall>i'<k. i'\<ge>i \<longrightarrow> \<not>final_glob (l!i')" using a2 by fastforce
  have i_eq_j:"i<j" using a2 a3 using le_imp_less_or_eq by auto 
  then obtain pre_k  where pre_k:"Suc pre_k = k" using a2 k
    by (metis a3 eq_iff le0 lessE neq0_conv) 
  then have "\<Gamma>\<turnstile>\<^sub>c (fst (l!pre_k), toSeq (snd (l!pre_k)))  \<rightarrow> 
                    (fst (l!k), toSeq (snd (l!k)))"
  proof -
    have "pre_k \<ge>i" using pre_k i_eq_j using a3 k le_Suc_eq by blast  
    then have "\<not>(final_glob (l!pre_k))" using i_k_not_final pre_k by auto 
    thus ?thesis using suc_not_final_final_c_tran a0 a2 pre_k k by fastforce
  qed
  thus ?thesis using pre_k by (metis a2 a3 i_k_not_final k le_Suc_eq not_less_eq)
qed 


subsection {* Basic Sound *}

lemma basic_skip:
   "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Basic f e, s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> c1=Skip"
proof -
  {fix s1 s2 c1
   assume "\<Gamma>\<turnstile>\<^sub>c(Basic f e,s1)  \<rightarrow> ((c1,s2))"     
   then have "c1=Skip" using stepc_elim_cases(3)
     by fastforce    
  } thus ?thesis by auto 
qed  

lemma no_comp_tran_before_i_basic:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Basic f e" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                                          (fst (l ! Suc i), toSeq (snd (l ! Suc i))))" and
         a3: "k\<le>j \<and> j < i \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                                  (fst (l ! Suc j), toSeq (snd (l ! Suc j))) )" and
         a4: "\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))"        
   shows "P"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Basic f e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  basic_skip by fastforce                  
  thus ?thesis using  a0 a1 a2 a3 a4  no_comp_tran_before_i by blast
qed

lemma only_one_component_tran_i_basic:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Basic f e" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                                          (fst (l ! Suc i), toSeq (snd (l ! Suc i))))" and
         a3: "k\<le>j \<and> j \<noteq> i \<and> Suc j < length l \<and> 
                        (\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                             (fst (l ! Suc j), toSeq (snd (l ! Suc j))) ) \<and> 
              fst (l!j) =  Basic f e"      
   shows "P"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Basic f e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  basic_skip by fastforce
  thus ?thesis using  a0 a1 a2 a3  only_one_component_tran_i[OF a0 a1 a2 ] by blast
qed   

lemma only_one_component_tran_basic:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Basic f e" and         
         a2: " k\<le>i \<and> i \<noteq> j \<and>  Suc i<length l \<and> 
                (\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                (fst (l ! Suc i), toSeq (snd (l ! Suc i)))) \<and> fst (l!i) = Basic f e" and
         a3: "k\<le>j  \<and> Suc j < length l" and
         a4: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!k) \<in>  p \<and> 
                                       Sta q rely \<and> snd (l!Suc i) \<in>  q"       
   shows "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Basic f e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  basic_skip by fastforce
  thus ?thesis using  a0 a1 a2 a3 a4 only_one_component_tran by blast
qed   

lemma only_one_component_tran_all_env_basic:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Basic f e" and         
         a2: "k\<le>i \<and> Suc i<length l \<and> ((\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                                      (fst (l ! Suc i), toSeq (snd (l ! Suc i))))) \<and> 
             fst (l!i) = Basic f e" and        
         a3: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!k) \<in>  p \<and> 
                                       Sta q rely \<and> snd (l!Suc i) \<in>  q"
   shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
proof -
  have b: "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Basic f e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  basic_skip by fastforce
  show ?thesis 
    by (metis (no_types) a0 a1 a2 a3 only_one_component_tran_basic) 
qed   

lemma only_one_component_tran_all_not_comp_basic:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Basic f e" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> ((\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                                          (fst (l ! Suc i), toSeq (snd (l ! Suc i)))))  \<and> fst (l!i) = Basic f e"           
       shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> 
                 \<not>(\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                 (fst (l ! Suc j), toSeq (snd (l ! Suc j))))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Basic f e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  basic_skip by fastforce
  thus ?thesis using  a0 a1 a2  only_one_component_tran_all_not_comp by blast
qed   

lemma l1:"\<Gamma>\<turnstile>\<^sub>c (c, toSeq s)  \<rightarrow> (c', toSeq s')  \<Longrightarrow> 
       \<Gamma>\<turnstile>\<^sub>c (c,  s)  \<rightarrow>\<^sub>c\<^sub>e (c',  s') \<Longrightarrow>
 toSeq s = ns \<Longrightarrow>
 toSeq s' =ns' \<Longrightarrow> 
 \<exists>gl.  s =  (ns, gl) \<and> s' =  (ns',gl)"
  by (metis (mono_tags, lifting) eq_fst_iff sndI step_dest1 toSeq.simps(1) )

lemma one_component_tran_basic_f_q:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!0) = Basic f e" and         
         a2: "Suc j<length l \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l!j), toSeq (snd (l!j)))  \<rightarrow> 
                                   (fst (l!(Suc j)), toSeq (snd (l!(Suc j)))))" and
         a3: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!0) \<in> p \<and> 
                                        Sta q rely" and
         a4:"p \<subseteq> {s. (f (fst s),snd s) \<in> q}"          
       shows "fst (l!j) = Basic f e \<and> fst (l!Suc j) = Skip \<and> 
                     (\<exists>na ng. snd (l!j) = (na,ng) \<and> (na,ng) \<in> p \<and> 
                              snd (l!Suc j) = (f na, ng) \<and> (f na, ng) \<in> q) \<and> 
             (\<forall>k. 0\<le>k \<and> j\<noteq>k \<and> Suc k < (length l) \<longrightarrow> 
                    \<not>(\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                          (fst (l!(Suc k)), toSeq (snd (l!(Suc k))))))"
proof-
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Basic f e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip)" 
    using  basic_skip by fastforce
  also obtain i where first:"Suc i<length l \<and>  
                            (\<Gamma>\<turnstile>\<^sub>c (fst (l!i), toSeq (snd (l!i)))  \<rightarrow> 
                                 (fst (l!(Suc i)), toSeq (snd (l!(Suc i))))) \<and> 
                            (\<forall>k < i. \<not>(\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                                        (fst (l!(Suc k)), toSeq (snd (l!(Suc k))))))"
    by (metis (no_types) a2 exist_first_comp_tran')
  moreover then have prg_j:"fst (l!i) = Basic f e"  using a1 a0
   by (metis cptn_env_same_prog not_step_comp_step_env)
  moreover have sta_j:"snd (l!i) \<in>  p"
  proof -
    have a0':"0\<le>i \<and> i<(length l)" using first by auto
    have a1':"(\<forall>k. 0\<le>k \<and> k < i \<longrightarrow> ((\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))))" 
      using first not_step_comp_step_env a0 by fastforce   
    thus ?thesis using stability first a3 a1'  a0' by blast 
  qed 
  moreover obtain gl sl where lj:"snd (l!i) =  (gl, sl)"
    using sta_j by moura  
  then have "(snd (l!Suc i) \<in>  q) \<and> 
             (snd (l!Suc i) =   (f gl, sl))"     
  proof -
    have "snd (l!i) \<in> p" using sta_j by fastforce
    moreover then have "fst(l!Suc i) = Skip \<and> toSeq(snd(l!Suc i)) =  (f (fst (snd (l!i))))" 
      using first
      by (metis Pair_inject prg_j stepc_elim_cases(3) toSeq.simps)
    moreover have "\<Gamma>\<turnstile>\<^sub>c(l!i) \<rightarrow>\<^sub>c\<^sub>e (l!(Suc i))"
      using a0 cptn_tran_ce_i first by auto     
    then have  "snd (l!Suc i) =   (f (fst (snd (l!i))), snd (snd (l!i)))" 
      using calculation first 
           l1[of \<Gamma> "fst (l ! i)" "snd (l ! i)" "fst (l ! (Suc i))" "snd (l ! (Suc i))"]
      by (metis prod.collapse sndI toSeq.simps(1))      
    ultimately show ?thesis using a4 lj by auto
  qed
  moreover have "\<forall>k. 0\<le>k \<and> k\<noteq>i \<and> Suc k < (length l) \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c(fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                                                       (fst (l!(Suc k)), toSeq (snd (l!(Suc k)))))"
    using only_one_component_tran_all_not_comp_basic[OF a0 a1] first a3 
          a0 a1 only_one_component_tran1 prg_j calculation by blast 
  moreover then have "i=j" using a2 by fastforce
  ultimately show ?thesis using lj by metis
qed

lemma one_component_tran_basic:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!0) = Basic f e" and         
         a2: "Suc k<length l \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                                   (fst (l!(Suc k)), toSeq (snd (l!(Suc k)))))" and
         a3: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!0) \<in> p \<and> 
                                        Sta q rely" and
         a4:"p \<subseteq> {s. (f (fst s),snd s) \<in> q}"           
  shows "\<forall>j. 0\<le>j \<and> j\<noteq>k \<and> Suc j < (length l) \<longrightarrow> 
                    \<not>(\<Gamma>\<turnstile>\<^sub>c (fst (l!j), toSeq (snd (l!j)))  \<rightarrow> 
                          (fst (l!(Suc j)), toSeq (snd (l!(Suc j)))))"
  using one_component_tran_basic_f_q[OF a0 a1 a2 a3 a4] by auto

lemma one_component_tran_basic_env:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!0) = Basic f e" and         
         a2: "Suc k<length l \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                                (fst (l!(Suc k)), toSeq (snd (l!(Suc k)))))" and
         a3: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!0) \<in> p \<and> 
                                        Sta q rely" and
         a4:"p \<subseteq> {s. (f (fst s),snd s) \<in> q}"           
  shows "fst (l!k) = Basic f e \<and> fst (l!Suc k) = Skip \<and> 
                     (\<exists>na ng. snd (l!k) = (na,ng) \<and> (na,ng) \<in> p \<and> 
                              snd (l!Suc k) =  (f na, ng) \<and> (f na, ng) \<in> q) \<and> 
          (\<forall>j. 0\<le>j \<and> j\<noteq>k \<and> Suc j < (length l) \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
proof - 
  show ?thesis using  a0 one_component_tran_basic_f_q[OF a0 a1 a2 a3 a4]
    by (metis Suc_eq_plus1 cptn_tran_ce_i prod.exhaust_sel step_ce_dest)
qed

lemma final_exist_component_tran_basic:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
          a1: "fst (l!i) = Basic f e" and                         
          a3: "i\<le>j \<and> j < length l \<and> final_glob (l!j)" 
  shows "\<exists>k. k\<ge>i \<and> k<j \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                               (fst (l!(Suc k)), toSeq (snd (l!(Suc k)))))"
proof - 
  show ?thesis using  a0 a1  a3 final_exist_component_tran by blast
qed 
  

(*lemma assumes a0:"\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  c sat [p, R, G, q,a]"
      shows "\<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub>  c sat [p, R, G, q,a]"
proof-
  {     
    assume a01:"\<forall>(b,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call b) sat [p, R, G, q,a]"
    have "\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c sat [p, R, G, q,a]"
    proof-
      {fix s l
        assume a02:"(\<Gamma>,l)\<in>cpn n \<Gamma> c s" and
               a03:"(\<Gamma>,l)\<in>assum(p, R)"
        have "(\<Gamma>,l)\<in>comm(G, (q,a)) F"  
        proof-
          have cpn_cp:"(\<Gamma>,l)\<in>cp \<Gamma> c s" using a02
            using cp_def cpn_def cptn_if_cptn_mod cptn_mod_nest_cptn_mod by fastforce
        qed
      } then show ?thesis unfolding  com_validityn_def cpn_def by auto
    qed
  } then show ?thesis unfolding com_cvalidityn_def by auto
qed *)

lemma l2:
  assumes a0:"\<Gamma>\<turnstile>\<^sub>c (c, toSeq s)  \<rightarrow> (c', toSeq s')" and      
a1:"(\<Gamma>, l) \<in> cptn" and a2:"l!i = (c,s)" and a3:"l!(Suc i) = (c', s')" and a4:"Suc i < length l" and
a5:"toSeq s =  ns" and
a6:"toSeq s' =  ns'"
shows"\<exists>gl.  s =  (ns, gl) \<and> s' =  (ns',gl)"
proof-
  have " \<Gamma>\<turnstile>\<^sub>c (c,  s)  \<rightarrow>\<^sub>c\<^sub>e (c',  s')" using a1 a2 a3 a4
    by (metis Suc_eq_plus1 cptn_tran_ce_i)
  thus ?thesis using l1[OF a0 _ a5 a6] by auto
qed

lemma Basic_sound1: 
  assumes a0:"p \<subseteq> {s. (f (fst s), snd s) \<in> q}" and
      a1:"\<forall>s t. s\<in>p \<and> ((fst t)=f (fst s)) \<and> (snd s =  snd t) \<longrightarrow> ( s, t) \<in> G" and
      a2:"Sta p R" and
      a3:"Sta q R" and
      a10:"c \<in> cp \<Gamma> (Basic f e) s" and a11:"c \<in> assum(p, R)"
    shows "c\<in>comm(G, (q,a)) F"
proof -   
  obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
   have cp:"l!0=(Basic f e,s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
   have assum:"snd(l!0) \<in> (p) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
             (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
               (snd(l!i), snd(l!(Suc i))) \<in> R)" 
   using a11 c_prod unfolding assum_def by simp
   have concl:"(\<forall>i. Suc i<length l \<longrightarrow> 
           \<Gamma>1\<turnstile>\<^sub>c(fst (l!i), toSeq(snd (l!i)))  \<rightarrow> (fst (l!Suc i), toSeq(snd (l!Suc i))) \<longrightarrow>                             
           (snd(l!i), snd(l!(Suc i))) \<in> G)"
   proof -
   { fix k
     assume a00:"Suc k<length l" and
            a11:"\<Gamma>1\<turnstile>\<^sub>c(fst (l!k), toSeq(snd (l!k)))  \<rightarrow> (fst (l!Suc k), toSeq(snd (l!Suc k)))"  
     have len_l:"length l > 0" using cp using cptn.simps by blast 
     then obtain a l1 where l:"l=a#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
     have last_l:"last l = l!(length l-1)"
       using last_length [of a l1] l by fastforce
     have env_tran:"env_tran \<Gamma> p l R" using assum env_tran_def cp by blast
     then have env_tran_right: "env_tran_right \<Gamma> l R" 
       using env_tran env_tran_right_def a2 unfolding env_tran_def by auto
     then obtain na ng where 
       all_event:"fst (l!k) = Basic f e \<and> fst (l!Suc k) = Skip \<and> 
                  snd (l!k) = (na,ng) \<and> (na,ng) \<in> p \<and> 
                  snd (l!Suc k) =  (f na, ng) \<and> (f na, ng) \<in> q \<and>
                  (\<forall>j. 0\<le>j \<and> k \<noteq> j \<and> Suc j < length l \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j))))"
       using one_component_tran_basic_env[of \<Gamma> l f e k R p q] a0 a00 a11 a2 a3 assum cp 
             env_tran_right fst_conv by auto 
     then have "(snd(l!k), snd(l!(Suc k))) \<in>  G"
        by (simp add: a1)    
   } thus ?thesis by auto qed
   have concr:"(final_glob (last l)  \<longrightarrow> 
               fst (last l) \<notin> Fault ` F  \<longrightarrow>
               ((fst (last l) = Skip \<and> snd (last l) \<in>  q)) \<or>
                (fst (last l) = Throw \<and>  snd (last l) \<in>  (a)))"
   proof-
   { 
     assume valid:"final_glob (last l)"
     have len_l:"length l > 0" using cp using cptn.simps by blast 
     then obtain a l1 where l:"l=a#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
     have last_l:"last l = l!(length l-1)"
       using last_length [of a l1] l by fastforce
     have env_tran:"env_tran \<Gamma> p l R" using assum env_tran_def cp by blast
     then have env_tran_right: "env_tran_right \<Gamma> l R" 
       using env_tran env_tran_right_def a2 unfolding env_tran_def by auto
     have "\<exists>k. k\<ge>0 \<and> k<((length l) - 1) \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                                                (fst (l!(Suc k)), toSeq (snd (l!(Suc k)))))"
     proof -             
       have "0\<le> (length l-1)" using len_l last_l by auto
       moreover have "(length l-1) < length l" using len_l by auto
       moreover have "final_glob (l!(length l-1))" using valid last_l by auto
       moreover have "fst (l!0) = Basic f e" using cp by auto
       ultimately show ?thesis 
         using cp final_exist_component_tran_basic env_tran a2 by blast 
     qed
     then obtain k where k_comp_tran: "k\<ge>0 \<and> k<((length l) - 1) \<and> 
                                       (\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                                             (fst (l!(Suc k)), toSeq (snd (l!(Suc k)))))"
       by auto
     moreover then have "Suc k < length l" by auto
     ultimately obtain na ng where all_event:"fst (l!k) = Basic f e \<and> fst (l!Suc k) = Skip \<and> 
                          snd (l!k) = (na,ng) \<and> (na,ng) \<in> p \<and> 
                              snd (l!Suc k) =  (f na, ng) \<and> (f na, ng) \<in> q \<and> 
            (\<forall>j. 0\<le>j \<and> j \<noteq> k \<and> Suc j < length l \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j))))"
        using one_component_tran_basic_env[of \<Gamma> l f e k R p q] a0  a11 a2 a3 assum cp 
             env_tran_right fst_conv by auto           
     then have before_k_all_evn:"\<forall>j. 0\<le>j \<and> j < k  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
           using k_comp_tran by fastforce     
     have after_k_all_evn:"\<forall>j. (Suc k)\<le>j \<and> Suc j < (length l)  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
           using all_event k_comp_tran by fastforce                            
     then have fst_last_skip:"fst (last l) = Skip \<and> snd ((last l)) \<in>  q"
     using  a2 last_l len_l cp env_tran_right a3 all_event assum k_comp_tran 
            stability [of q R l "Suc k" "((length l) - 1)" _ \<Gamma>] 
       by fastforce                 
   } thus ?thesis by auto qed
   note res = conjI [OF concl concr]                               
   thus ?thesis using c_prod unfolding comm_def by auto 
 qed


lemma Basic_sound: 
       "p \<subseteq> {s. (f (fst s), snd s) \<in> q} \<Longrightarrow>
       \<forall>s t. s\<in>p \<and> ((fst t)=f (fst s)) \<and> (snd s =  snd t) \<longrightarrow> ( s, t) \<in> G \<Longrightarrow>       
       Sta p R \<Longrightarrow>
       Sta q R \<Longrightarrow>       
       \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub>  (Basic f e) sat [p, R, G, q,a]"
proof -  
 assume
    a0:"p \<subseteq> {s. (f (fst s), snd s) \<in> q}" and
    a1:"\<forall>s t. s\<in>p \<and> ((fst t)=f (fst s)) \<and> (snd s =  snd t) \<longrightarrow> ( s, t) \<in> G" and
    a2:"Sta p R " and
    a3:"Sta q R" 
{
    fix s
    have "cpn n \<Gamma> (Basic f e) s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cpn n \<Gamma> (Basic f e) s" and a11:"c \<in> assum(p, R)"
      then have a10:"c\<in>cp \<Gamma> (Basic f e) s"
        using cp_def cpn_def cptn_if_cptn_mod cptn_mod_nest_cptn_mod by blast
      have "c\<in>comm(G, (q,a)) F" using Basic_sound1[OF a0 a1 a2 a3 a10 a11] by auto      
    } thus ?thesis by auto
    qed 
  } 
  thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed

subsection {* Spec Sound *}

lemma spec_skip:
   "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> c1=Skip \<or> c1 = Stuck"
proof -
  {fix s1 s2 c1
   assume "\<Gamma>\<turnstile>\<^sub>c(Spec r e,s1)  \<rightarrow> ((c1,s2))"     
   then have "c1=Skip \<or> c1=Stuck" using stepc_elim_cases(4)
     by fastforce    
  } thus ?thesis by auto 
qed  


lemma no_comp_tran_before_i_spec:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Spec r e" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                                          (fst (l ! Suc i), toSeq (snd (l ! Suc i))))" and
         a3: "k\<le>j \<and> j < i \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                                  (fst (l ! Suc j), toSeq (snd (l ! Suc j))) )" and
         a4: "\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))" and  
         a5: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!0) \<in>  p \<and> 
                                        Sta q rely \<and> snd (l!Suc j) \<in>  q" 
   shows "P"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip) \<or> c1 =  Stuck" 
    using  spec_skip by fastforce
  thus ?thesis using  a0 a1 a2 a3 a4 a5 no_comp_tran_before_i by blast
qed

lemma only_one_component_tran_i_spec:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Spec r e" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                                          (fst (l ! Suc i), toSeq (snd (l ! Suc i))))" and
         a3: "k\<le>j \<and> j \<noteq> i \<and> Suc j < length l \<and> 
                             ((\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                             (fst (l ! Suc j), toSeq (snd (l ! Suc j))) )) \<and> 
              fst (l!j) =  Spec r e" and
         a4: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!k) \<in>  p \<and> 
                                        Sta q rely \<and> snd (l!Suc j) \<in> q"     
   shows "P"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip \<or> c1 = Stuck)" 
    using  spec_skip by fastforce
  thus ?thesis using  a0 a1 a2 a3 a4 only_one_component_tran_i[OF a0 a1 a2 ] by blast
qed   

lemma only_one_component_tran_spec:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Spec r e" and         
         a2: "k\<le>i  \<and> i \<noteq> j \<and> Suc i<length l \<and> 
             (\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                  (fst (l ! Suc i), toSeq (snd (l ! Suc i)))) \<and> fst (l!i) =  Spec r e" and
         a3: "k\<le>j  \<and> Suc j < length l"        
   shows "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip \<or> c1 = Stuck)"    
    by (simp add: spec_skip)
  thus ?thesis using  a0 a1 a2 a3  only_one_component_tran by blast
qed   

lemma only_one_component_tran_all_env_spec:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Spec r e" and         
         a2: "k\<le>i \<and> Suc i<length l \<and>((\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                                      (fst (l ! Suc i), toSeq (snd (l ! Suc i)))))  \<and> fst (l!i) =  Spec r e"      
   shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip \<or> c1 = Stuck)" 
    by (simp add: spec_skip)
  thus ?thesis by (metis (no_types) a0 a1 a2 only_one_component_tran_spec) 
qed   

lemma only_one_component_tran_all_not_comp_spec:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Spec r e" and         
         a2: "k\<le>i \<and> Suc i<length l \<and> ((\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                                          (fst (l ! Suc i), toSeq (snd (l ! Suc i)))))  \<and> fst (l!i) =  Spec r e" 
       shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> 
                  \<not>(\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                        (fst (l ! Suc j), toSeq (snd (l ! Suc j))))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip \<or> c1 = Stuck)" 
     by (simp add: spec_skip)
  thus ?thesis using  a0 a1 a2  only_one_component_tran_all_not_comp by blast
qed   

lemma one_component_tran_spec:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!0) = Spec r e" and         
         a2: "Suc j<length l \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l!j), toSeq (snd (l!j)))  \<rightarrow> 
                                    (fst (l!(Suc j)), toSeq (snd (l!(Suc j)))))" and
         a3: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!0) \<in>  p \<and> 
                                        Sta q rely" and
         a4:"p \<subseteq> {s. (\<forall>t. (fst s, t)\<in>r \<longrightarrow> ( t, snd s) \<in> q) \<and> (\<exists>t. (fst s,t) \<in> r)}"
           
     shows "fst (l!j) = Spec r e \<and> fst (l!Suc j) = Skip \<and> 
            (\<exists>na ng nb. snd (l!j) = (na,ng) \<and> (na,ng) \<in> p \<and> 
                      snd (l!Suc j) =  (nb, ng) \<and> (na,nb)\<in>r \<and> (nb, ng) \<in> q) \<and>
                (\<forall>k. 0\<le>k \<and> j\<noteq>k \<and> Suc k < (length l) \<longrightarrow> 
                    \<not>(\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                          (fst (l!(Suc k)), toSeq (snd (l!(Suc k))))))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip\<or> c1 = Stuck)" 
     by (simp add: spec_skip)
  also obtain i where first:"Suc i<length l \<and>  
                            (\<Gamma>\<turnstile>\<^sub>c (fst (l!i), toSeq (snd (l!i)))  \<rightarrow> 
                                 (fst (l!(Suc i)), toSeq (snd (l!(Suc i))))) \<and> 
                            (\<forall>k < i. \<not>(\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                                        (fst (l!(Suc k)), toSeq (snd (l!(Suc k))))))"
    by (metis (no_types) a2 exist_first_comp_tran')
  moreover then have prg_j:"fst (l!i) = Spec r e" using a1 a0
   by (metis cptn_env_same_prog not_step_comp_step_env)
  moreover have sta_j:"snd (l!i) \<in> p"
  proof -
    have a0':"0\<le>i \<and> i<(length l)" using first by auto
    have a1':"(\<forall>k. 0\<le>k \<and> k < i \<longrightarrow> ((\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))))" 
      using first not_step_comp_step_env a0 by fastforce   
    thus ?thesis using stability first a3 a1'  a0' by blast 
  qed 
  moreover obtain gl sl where lj:"snd (l!i) =  (gl, sl)"
    using sta_j by moura 
  then  obtain gl' where "(snd (l!Suc i) \<in>  q) \<and> 
                         (snd (l!Suc i) =   (gl', sl)) \<and> (gl, gl')\<in>r"  
  proof -
    { 
      have gl:"toSeq (snd(l!i)) =  gl" using lj by auto
      then obtain t where "(gl, t)\<in>r" using a4 sta_j lj by fastforce
      then obtain gl' where "toSeq(snd (l!Suc i)) =  gl' \<and> (gl, gl')\<in> r"
        using stepc_elim_cases(4) by (metis gl first prg_j snd_conv) 
      moreover  have "\<Gamma>\<turnstile>\<^sub>c(l!i) \<rightarrow>\<^sub>c\<^sub>e (l!(Suc i))"
        using a0 cptn_tran_ce_i first by auto 
      then have "snd (l!Suc i) =  (gl', sl)" 
        using calculation lj first 
             l1[of \<Gamma> "fst (l!i)" "snd (l!i)" "fst (l!(Suc i))" "snd (l!(Suc i))"]
        by (metis gl prod.exhaust_sel snd_conv )        
      moreover have "(gl', sl) \<in>  q" using a4 lj calculation sta_j 
        by fastforce
      then have  "snd (l!Suc i) \<in> q" using calculation by auto         
      ultimately have "\<exists>gl'. (snd (l!Suc i) \<in>  q) \<and> 
                         (snd (l!Suc i) =   (gl', sl)) \<and> (gl, gl')\<in>r" by auto
  } then show "(\<And>gl'. (snd (l!Suc i) \<in>  q) \<and> 
               (snd (l!Suc i) =   (gl', sl)) \<and> (gl, gl')\<in>r \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    ..
  qed    
  moreover have "\<forall>k. 0\<le>k \<and> k\<noteq>i \<and> Suc k < (length l) \<longrightarrow> \<not>(\<Gamma>\<turnstile>\<^sub>c(fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                                                       (fst (l!(Suc k)), toSeq (snd (l!(Suc k)))))"
    using only_one_component_tran_all_not_comp_spec[OF a0 a1] first a3 
          a0 a1 calculation(1) only_one_component_tran1 prg_j calculation by blast
  moreover then have "i=j" using a2 by fastforce
  ultimately show ?thesis using lj
    by (metis fst_conv step_spec_skip_stuck toSeq.simps)
qed   

lemma one_component_tran_spec_env:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!0) = Spec r e" and         
         a2: "Suc k<length l \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                                    (fst (l!(Suc k)), toSeq (snd (l!(Suc k)))))" and
         a3: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!0) \<in> p \<and> 
                                        Sta q rely" and
         a4:"p \<subseteq> {s. (\<forall>t. (fst s, t)\<in>r \<longrightarrow> ( t, snd s) \<in> q) \<and> (\<exists>t. (fst s,t) \<in> r)}"           
  shows "fst (l!k) = Spec r e \<and> fst (l!Suc k) = Skip \<and> 
            (\<exists>na ng nb. snd (l!k) = (na,ng) \<and> (na,ng) \<in> p \<and> 
                      snd (l!Suc k) =  (nb, ng) \<and> (na,nb)\<in>r \<and> (nb, ng) \<in> q) \<and> 
         (\<forall>j. 0\<le>j \<and> j\<noteq>k \<and> Suc j < (length l) \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
proof - 

  show ?thesis using one_component_tran_spec[OF a0 a1 a2 a3 a4]  a0
       by (metis Suc_eq_plus1 cptn_tran_ce_i prod.exhaust_sel step_ce_dest)
qed

lemma final_exist_component_tran_spec:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
          a1: "fst (l!i) = Spec r e" and                        
          a3: "i\<le>j \<and> j < length l \<and> final_glob (l!j)" 
  shows "\<exists>k. k\<ge>i \<and> k<j \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                               (fst (l!(Suc k)), toSeq (snd (l!(Suc k)))))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Spec r e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> (c1=Skip \<or> c1 = Stuck)" 
     by (simp add: spec_skip)
  thus ?thesis using  a0 a1  a3 final_exist_component_tran by blast
qed   

lemma Spec_sound1: 
       "p \<subseteq> {s. (\<forall>t. (fst s, t)\<in>r \<longrightarrow> ( t, snd s) \<in> q) \<and> (\<exists>t. (fst s,t) \<in> r)} \<Longrightarrow>
       (\<forall>s t. s\<in>p \<and> (fst s,fst t)\<in>r \<and> (snd s) = (snd t) \<longrightarrow> ( s, t) \<in> G) \<Longrightarrow>       
       Sta p R \<Longrightarrow>
       Sta q R \<Longrightarrow> 
       c \<in> cp \<Gamma> (Spec r e) s \<Longrightarrow>
       c \<in> assum(p, R) \<Longrightarrow>
       c \<in> comm (G, (q,a)) F"   
proof -  
 assume
  a0:"p \<subseteq> {s. (\<forall>t. (fst s, t)\<in>r \<longrightarrow> ( t, snd s) \<in> q) \<and> (\<exists>t. (fst s,t) \<in> r)}" and
  a1:"(\<forall>s t. s\<in>p \<and> (fst s,fst t)\<in>r \<and> (snd s) = (snd t) \<longrightarrow> ( s, t) \<in> G)" and
  a2:"Sta p R" and
  a3:"Sta q R" and 
  a10:"c \<in> cp \<Gamma> (Spec r e) s" and
  a11:"c \<in> assum(p, R)"

  obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
  have cp:"l!0=(Spec r e,s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
   have assum:"snd(l!0) \<in>  (p) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
             (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
               (snd(l!i), snd(l!(Suc i))) \<in> R)" 
   using a11 c_prod unfolding assum_def by simp
   have concl:"(\<forall>i ns ns'. Suc i<length l \<longrightarrow> 
           \<Gamma>1\<turnstile>\<^sub>c(fst (l!i), toSeq(snd (l!i)))  \<rightarrow> (fst (l!Suc i), toSeq(snd (l!Suc i))) \<longrightarrow>                                       
             (snd(l!i), snd(l!(Suc i))) \<in> G)"
   proof -
   { fix k
     assume a00:"Suc k<length l" and
            a11:"\<Gamma>1\<turnstile>\<^sub>c(fst (l!k), toSeq(snd (l!k)))  \<rightarrow> (fst (l!Suc k), toSeq(snd (l!Suc k)))"                
     obtain ck sk csk ssk where tran_pair:
       "\<Gamma>1\<turnstile>\<^sub>c (ck,sk)  \<rightarrow> (csk, ssk) \<and> (ck = fst (l!k)) \<and> 
        (sk = toSeq(snd (l!k))) \<and> (csk = fst (l!(Suc k))) \<and> (ssk = toSeq(snd (l!(Suc k))))" 
       using a11 by fastforce
     have len_l:"length l > 0" using cp using cptn.simps by blast 
     then obtain a l1 where l:"l=a#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
     have last_l:"last l = l!(length l-1)"
       using last_length [of a l1] l by fastforce
     have env_tran:"env_tran \<Gamma> p l R" using assum env_tran_def cp by blast
     then have env_tran_right: "env_tran_right \<Gamma> l R" 
       using env_tran env_tran_right_def unfolding env_tran_def by auto
     then obtain na nb ng where k_spec:
       "fst (l!k) = Spec r e \<and> fst (l!Suc k) = Skip \<and> 
            (snd (l!k) = (na,ng) \<and> (na,ng) \<in> p \<and> 
                      snd (l!Suc k) =  (nb, ng) \<and> (na,nb)\<in>r \<and> (nb, ng) \<in> q)"
        and all_event:"(\<forall>j. 0\<le>j \<and> k \<noteq> j \<and> Suc j < length l \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j))))"
       using a00 a11   one_component_tran_spec_env[of \<Gamma> l r e k R p q] 
             env_tran_right fst_conv a0 a2 a3 cp len_l assum
       by fastforce
     then have before_k_all_evn:"\<forall>j. 0\<le>j \<and> j < k  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
           using a00 a11  by fastforce                                                                             
     then have "(snd(l!k), snd(l!(Suc k))) \<in> G"
       using k_spec a1 tran_pair
       by (simp add: a1) 
   } thus ?thesis by auto qed
  have concr:"(final_glob (last l)  \<longrightarrow> fst (last l) \<notin> Fault ` F \<longrightarrow>
      ((fst (last l) = Skip \<and> snd (last l) \<in> q)) \<or>
       (fst (last l) = Throw \<and> snd (last l) \<in> (a)))"
   proof-
   { 
     assume valid:"final_glob (last l)" 
     have len_l:"length l > 0" using cp using cptn.simps by blast 
     then obtain a l1 where l:"l=a#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
     have last_l:"last l = l!(length l-1)"
       using last_length [of a l1] l by fastforce
     have env_tran:"env_tran \<Gamma> p l R" using assum env_tran_def cp by blast
     then have env_tran_right: "env_tran_right \<Gamma> l R" 
       using env_tran env_tran_right_def unfolding env_tran_def by auto
     have "\<exists>k. k\<ge>0 \<and> k<((length l) - 1) \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                                                (fst (l!(Suc k)), toSeq (snd (l!(Suc k)))))"
     proof -             
       have "0\<le> (length l-1)" using len_l last_l by auto
       moreover have "(length l-1) < length l" using len_l by auto
       moreover have "final_glob (l!(length l-1))" using valid last_l by auto
       moreover have "fst (l!0) = Spec r e" using cp by auto
       ultimately show ?thesis 
         using cp final_exist_component_tran_spec env_tran  by blast 
     qed
     then obtain k  where k_comp_tran: "k\<ge>0 \<and> k<((length l) - 1) \<and>  
                                         (\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                                            (fst (l!(Suc k)), toSeq (snd (l!(Suc k)))))"
       by auto
     then obtain ck sk csk ssk where tran_pair:
       "\<Gamma>1\<turnstile>\<^sub>c (ck,sk)  \<rightarrow> (csk, ssk) \<and> (ck = fst (l!k)) \<and> 
         (sk = toSeq(snd (l!k))) \<and> (csk = fst (l!(Suc k))) \<and> (ssk = toSeq(snd (l!(Suc k))))" 
       using cp by fastforce
     moreover then have "Suc k < length l" using k_comp_tran by auto
     ultimately obtain na nb ng where k_spec:
       "fst (l!k) = Spec r e \<and> fst (l!Suc k) = Skip \<and> 
            (snd (l!k) = (na,ng) \<and> (na,ng) \<in> p \<and> 
                      snd (l!Suc k) =  (nb, ng) \<and> (na,nb)\<in>r \<and> (nb, ng) \<in> q)"
        and all_event:"(\<forall>j. 0\<le>j \<and> k \<noteq> j \<and> Suc j < length l \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j))))"
       using one_component_tran_spec_env[of \<Gamma> l r e k R p q] 
             env_tran_right  a0 a2 a3 cp assum
       by fastforce                                       
     then have fst_last_skip:"fst (last l) = Skip \<and> 
                         snd ((last l)) \<in>  q"
       using  k_spec a2 last_l len_l cp env_tran_right a3 all_event assum k_comp_tran 
            stability [of q R l "Suc k" "((length l) - 1)" _ \<Gamma>] by fastforce       
   } thus ?thesis by auto qed
   note res = conjI [OF concl concr]                           
   thus ?thesis using c_prod unfolding comm_def by auto 
 qed
 
lemma Spec_sound: 
       "p \<subseteq> {s. (\<forall>t. (fst s, t)\<in>r \<longrightarrow> ( t, snd s) \<in> q) \<and> (\<exists>t. (fst s,t) \<in> r)} \<Longrightarrow>
       (\<forall>s t. s\<in>p \<and> (fst s,fst t)\<in>r \<and> (snd s) = (snd t) \<longrightarrow> ( s, t) \<in> G) \<Longrightarrow>     
       Sta p R \<Longrightarrow>
       Sta q R \<Longrightarrow>    
       \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub>  (Spec r e) sat [p, R, G, q,a]"
proof -  
 assume
    a0:"p \<subseteq> {s. (\<forall>t. (fst s, t)\<in>r \<longrightarrow> ( t, snd s) \<in> q) \<and> (\<exists>t. (fst s,t) \<in> r)}" and
    a1:"(\<forall>s t. s\<in>p \<and> (fst s,fst t)\<in>r \<and> (snd s) = (snd t) \<longrightarrow> ( s, t) \<in> G)" and
    a2:"Sta p R" and
    a3:"Sta q R" 
{
    fix s
    have "cpn n \<Gamma> (Spec r e) s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cpn n \<Gamma> (Spec r e) s" and a11:"c \<in> assum(p, R)"
      then have a10:"c\<in>cp \<Gamma> (Spec r e) s"
        using cp_def cpn_def cptn_if_cptn_mod cptn_mod_nest_cptn_mod by blast
      have "c\<in>comm(G, (q,a)) F" using Spec_sound1[OF a0 a1 a2 a3 a10 a11] by auto      
    } thus ?thesis by auto
    qed 
  } 
  thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed

subsection {* Await Sound *}

lemma await_skip:
   "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> 
            c1=Skip \<or> c1 = Throw \<or> c1 = Stuck \<or> (\<exists>f. c1 = Fault f)"
proof -
  {fix s1 s2 c1
   assume "\<Gamma>\<turnstile>\<^sub>c(Await b c e,s1)  \<rightarrow> ((c1,s2))"     
   then have "c1=Skip \<or>  (c1 = Throw ) \<or>  c1 = Stuck \<or> (\<exists>f. c1 = Fault f)" 
     by  (auto elim: stepc_elim_cases(8) )     
  } thus ?thesis by auto 
qed  

lemma no_comp_tran_before_i_await:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Await b c e" and         
         a2: "Suc i<length l \<and> k\<le>i \<and>  (\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                                          (fst (l ! Suc i), toSeq (snd (l ! Suc i))))" and
         a3: "k\<le>j \<and> j < i \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                                  (fst (l ! Suc j), toSeq (snd (l ! Suc j))) )" and
         a4: "\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))" 
   shows "P"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow>  
          c1=Skip \<or> (c1 = Throw) \<or> c1 = Stuck \<or> (\<exists>f. c1 = Fault f)" 
    by (simp add: await_skip)
  thus ?thesis using  a0 a1 a2 a3 a4  no_comp_tran_before_i by blast
qed

lemma only_one_component_tran_i_await:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Await b c e" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                                  (fst (l ! Suc i), toSeq (snd (l ! Suc i))) )" and
         a3: "k\<le>j \<and> j \<noteq> i \<and> Suc j < length l \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                                  (fst (l ! Suc j), toSeq (snd (l ! Suc j))) ) \<and> fst (l!j) = Await b c e"          
   shows "P"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow>  
          c1=Skip \<or> (c1 = Throw) \<or> c1 = Stuck \<or> (\<exists>f. c1 = Fault f)" 
    by (simp add: await_skip)
  thus ?thesis using  a0 a1 a2 a3  only_one_component_tran_i by blast
qed   

lemma only_one_component_tran_await:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Await b c e" and         
         a2: " k\<le>i \<and> i \<noteq> j \<and>  Suc i<length l \<and> 
                                (\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                                  (fst (l ! Suc i), toSeq (snd (l ! Suc i))) ) \<and> 
               fst (l!i) = Await b c e" and
         a3: "k\<le>j  \<and> Suc j < length l"  
   shows "(\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow>  
          c1=Skip \<or> (c1 = Throw) \<or> c1 = Stuck \<or> (\<exists>f. c1 = Fault f)" 
    by (simp add: await_skip)
  thus ?thesis using  a0 a1 a2 a3  only_one_component_tran by blast
qed   

lemma only_one_component_tran_all_env_await:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Await b c e" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                                  (fst (l ! Suc i), toSeq (snd (l ! Suc i))) )  \<and> 
              fst (l!i) = Await b c e"      
   shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
proof -
 have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow>  
          c1=Skip \<or> (c1 = Throw) \<or> c1 = Stuck \<or> (\<exists>f. c1 = Fault f)" 
    by (simp add: await_skip)
  thus ?thesis by (metis (no_types) a0 a1 a2  only_one_component_tran_await)
qed
   

lemma only_one_component_tran_all_not_comp_await:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!k) = Await b c e" and         
         a2: "Suc i<length l \<and> k\<le>i \<and> 
              (\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                  (fst (l ! Suc i), toSeq (snd (l ! Suc i))) )  \<and> fst (l!i) = Await b c e"          
       shows "\<forall>j. k\<le>j \<and> j\<noteq>i \<and> Suc j < (length l) \<longrightarrow> 
                   \<not>(\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                    (fst (l ! Suc j), toSeq (snd (l ! Suc j))) )"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow>  
          c1=Skip \<or> (c1 = Throw) \<or> c1 = Stuck \<or> (\<exists>f. c1 = Fault f)" 
    by (simp add: await_skip)
  thus ?thesis using  a0 a1 a2 only_one_component_tran_all_not_comp by blast
qed   

lemma one_component_tran_await:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!0) = Await b c e" and         
         a2: "Suc k<length l \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                                  (fst (l ! Suc k), toSeq (snd (l ! Suc k)))) " and
         a3: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!0) \<in>  p \<and> 
                                        Sta q rely \<and>
                                        Sta a rely" and
         a4:"p \<subseteq> {s. \<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
                  (b \<inter> {c. c = fst s}) c 
                   {s'. ( s,  (s', snd s)) \<in> G \<and> (s',snd s)\<in> q},
                   {s'. ( s,  (s', snd s)) \<in> G \<and> (s',snd s)\<in> a}}"          
           
         shows "(\<forall>j. 0\<le>j \<and> j\<noteq>k \<and> Suc j < (length l) \<longrightarrow> 
                     \<not>(\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                      (fst (l ! Suc j), toSeq (snd (l ! Suc j))) )) \<and>
         (\<exists>na na' ng. fst (l!k) = Await b c e  \<and> 
                      snd (l!k) = (na,ng) \<and> (na,ng) \<in> p \<and>
             snd (l!Suc k) =  (na', ng) \<and> 
            (na' \<in> {s'. ( (na, ng),  (s', ng)) \<in> G \<and> (s',ng)\<in>q} \<and> fst (l!Suc k) = Skip \<or> 
             na' \<in> {s'. ( (na, ng),  (s',ng)) \<in> G \<and> (s',ng)\<in>a}\<and> fst (l!Suc k) = Throw \<or> 
             (na' = na \<and> fst (l!Suc k) \<in> Fault ` F)))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow>  
          c1=Skip \<or> (c1 = Throw) \<or> c1 = Stuck \<or> (\<exists>f. c1 = Fault f)" 
    by (simp add: await_skip)
  also obtain j where first:"(Suc j<length l \<and> 
                              (\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                              (fst (l ! Suc j), toSeq (snd (l ! Suc j))) )) \<and> 
                 (\<forall>k < j. \<not> (\<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                                  (fst (l ! Suc k), toSeq (snd (l ! Suc k))) ))"
    by (metis (no_types) a2 exist_first_comp_tran')
  moreover then have prg_j:"fst (l!j) = Await b c e" using a1 a0
   by (metis cptn_env_same_prog not_step_comp_step_env)
  moreover have sta_j:"snd (l!j) \<in>  p"
  proof -
    have a0':"0\<le>j \<and> j<(length l)" using first by auto
    have a1':"(\<forall>k. 0\<le>k \<and> k < j \<longrightarrow> ((\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k)))))" 
      using first not_step_comp_step_env a0 by fastforce   
    thus ?thesis using stability first a3 a1'  a0' by blast 
  qed 
  from sta_j obtain na ng where 
      k_basic:"fst (l!j) = Await b c e \<and> snd (l!j) =  (na, ng) \<and>  (na,ng) \<in> p \<and> snd(l!j) \<in>  p" 
      using sta_j prg_j
      by (metis prod.exhaust_sel)
  obtain na' where conc:
    "snd (l!Suc j) =  (na', ng) \<and> 
     (na' \<in> {s'. ( (na, ng),  (s', ng)) \<in> G \<and> (s',ng)\<in>q} \<and> fst (l!Suc j) = Skip \<or> 
      na' \<in> {s'. ( (na, ng),  (s',ng)) \<in> G  \<and> (s',ng)\<in>a} \<and> fst (l!Suc j) = Throw \<or>  
      (na = na' \<and> fst(l!Suc j) \<in> Fault ` F))" 
  proof -    
    { have "\<Gamma>\<^sub>\<not>\<^sub>a,{}\<Turnstile>\<^bsub>/F\<^esub> 
            (b \<inter> {c. c = na}) c 
             {s'. ( (na,ng),  (s', ng)) \<in> G \<and> (s',ng)\<in> q},
             {s'. ( (na,ng),  (s', ng)) \<in> G \<and> (s',ng)\<in> a}"
        using  a4 hoare_sound k_basic by fastforce
      then have e_auto:"\<Gamma>\<^sub>\<not>\<^sub>a\<Turnstile>\<^bsub>/F\<^esub> 
                (b \<inter> {c. c = na}) c 
                 {s'. ( (na,ng),  (s', ng)) \<in> G \<and> (s',ng)\<in> q},
                 {s'. ( (na,ng),  (s', ng)) \<in> G \<and> (s',ng)\<in> a}" 
      unfolding cvalid_def by auto    
      have f': "\<Gamma>\<turnstile>\<^sub>c(fst (l!j), toSeq(snd(l!j)))  \<rightarrow> (fst(l!(Suc j)), toSeq(snd(l!(Suc j))))"      
        using first by auto
      have step_await:"Suc j<length l \<and> \<Gamma>\<turnstile>\<^sub>c (Await b c e,toSeq(snd(l!j)))  \<rightarrow> (fst(l!(Suc j)), toSeq(snd(l!(Suc j))))"
        using f' k_basic first by fastforce           
      then have s'_in_bp:"na\<in> b \<and> (na,ng) \<in> p"  using k_basic stepc_elim_cases(8)
        by force
      then have na:"na \<in> ((fst ` p)  \<inter> b)"
        by force
      moreover have test:
        "\<exists>t. \<Gamma>\<^sub>\<not>\<^sub>a\<turnstile> \<langle>c, Normal na\<rangle> \<Rightarrow> t \<and> 
          ((\<exists>t'. t =Abrupt t' \<and> toSeq(snd(l!Suc j)) =  t' \<and> fst(l!Suc j) = Throw) \<or>
           (\<exists>t'. t =Normal t' \<and> toSeq(snd(l!Suc j)) =  t' \<and> fst(l!Suc j) = Skip) \<or>
           (\<exists>f. t = xstate.Fault f \<and> toSeq(snd(l!Suc j)) =  na \<and> fst(l!Suc j) = Fault f ) \<or> 
           ( t = xstate.Stuck \<and> toSeq(snd(l!Suc j)) =  na \<and> fst(l!Suc j) = Stuck ))"
      proof -
        fix t 
        { assume a00:"fst(l!Suc j) = Skip"
          have ?thesis
            by (metis a00 fst_conv k_basic step_await stepc_elim_cases_Await_Skip toSeq.simps)          
        } 
        moreover { assume a00:"fst(l!Suc j)= Throw "
          have ?thesis
            by (metis a00 first fst_conv k_basic stepc_elim_cases_Await_Throw toSeq.simps)
        }
        moreover { assume a00:"fst(l!Suc j)= Stuck"
          have ?thesis
            by (metis a00 f' fst_conv k_basic stepc_elim_cases_Await_Stuck toSeq.simps)
        }
        moreover { assume a00:"\<exists>f. fst(l!Suc j)= Fault f"
          have ?thesis
            by (metis a00 f' fst_conv k_basic stepc_elim_cases_Await_Fault toSeq.simps)
        }
        ultimately show ?thesis
          using await_skip step_await by fastforce
      qed
      then obtain nna' where e_step:"\<Gamma>\<^sub>\<not>\<^sub>a\<turnstile> \<langle>c,Normal na\<rangle> \<Rightarrow> nna' \<and> 
               ((\<exists>t'. nna' =Abrupt t' \<and> toSeq(snd(l!Suc j)) =  t' \<and> fst (l ! Suc j) = Throw) \<or>
               (\<exists>t'. nna' =Normal t' \<and> toSeq(snd(l!Suc j)) =  t' \<and> fst(l!Suc j) = Skip) \<or>
              (\<exists>f. nna' = xstate.Fault f \<and> toSeq(snd(l!Suc j)) =  na \<and> fst(l!Suc j) = Fault f ) \<or> 
               ( nna' = xstate.Stuck \<and> toSeq(snd(l!Suc j)) =  na \<and> fst(l!Suc j) = Stuck )) " 
        by fastforce
     
      { assume "nna' \<notin> xstate.Fault ` F"    
        then have t_q_a:
                 "nna' \<in> Normal ` {s'. ( (na, ng),  (s', ng)) \<in> G \<and> (s',ng)\<in>q} \<union> 
                         Abrupt `  {s'. ( (na, ng),  (s',ng)) \<in> G  \<and> (s',ng)\<in>a}"
          using na e_step e_auto unfolding valid_def by auto        
        then obtain na' where  na':"toSeq(snd(l!Suc j)) =  na'" and 
                              "(na' \<in> {s'. ( (na, ng),  (s', ng)) \<in> G \<and> (s',ng)\<in>q} \<and> fst (l ! Suc j) = Skip \<or> 
                              na' \<in> {s'. ( (na, ng),  (s',ng)) \<in> G  \<and> (s',ng)\<in>a} \<and> fst (l ! Suc j) = Throw)"
          using e_step  by blast     
        moreover have "snd (l!Suc j) =  (na', ng)" 
          using  na' step_await s'_in_bp k_basic a0 l2[OF conjunct2[OF step_await] a0]            
          by (auto, metis prod.exhaust_sel)
        ultimately have "\<exists>na'. snd (l!Suc j) =  (na', ng) \<and> 
                 (na' \<in> {s'. ( (na, ng),  (s', ng)) \<in> G \<and> (s',ng)\<in>q} \<and> fst (l ! Suc j) = Skip \<or> 
                  na' \<in> {s'. ( (na, ng),  (s',ng)) \<in> G  \<and> (s',ng)\<in>a} \<and> fst (l ! Suc j) = Throw)"
          by auto
      }
      moreover { assume "nna' \<in> xstate.Fault ` F" 
        then have "\<exists>na'. snd (l!Suc j) =  (na', ng) \<and> na = na' \<and> fst(l!Suc j) \<in> Fault ` F"
          using e_step  step_await k_basic l1 cptn_tran_ce_i a0 apply auto
         by (smt Suc_eq_plus1 cptn_tran_ce_i prod.exhaust_sel step_ce_Normal_eq_l)
      }
      ultimately have 
        "\<exists>na'. snd (l!Suc j) =  (na', ng) \<and> 
               (na' \<in> {s'. ( (na, ng),  (s', ng)) \<in> G \<and> (s',ng)\<in>q} \<and> fst (l ! Suc j) = Skip \<or> 
                na' \<in> {s'. ( (na, ng),  (s',ng)) \<in> G  \<and> (s',ng)\<in>a} \<and> fst (l ! Suc j) = Throw \<or>
                (na = na' \<and> fst(l!Suc j) \<in> Fault ` F))" by auto
    } then show "(\<And>na'. snd (l ! Suc j) =  (na', ng) \<and>
            (na' \<in> {s'. ( (na, ng),  (s', ng)) \<in> G \<and> (s',ng)\<in>q} \<and> fst (l ! Suc j) = Skip \<or> 
             na' \<in> {s'. ( (na, ng),  (s',ng)) \<in> G  \<and> (s',ng)\<in>a} \<and> fst (l ! Suc j) = Throw \<or> 
             (na = na' \<and> fst(l!Suc j) \<in> Fault ` F)) \<Longrightarrow>
            thesis) \<Longrightarrow> thesis " .. 
  qed         
  have "\<forall>i. 0\<le>i \<and> i\<noteq>j \<and> Suc i < (length l) \<longrightarrow> 
                        \<not>((\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                           (fst (l ! Suc i), toSeq (snd (l ! Suc i))) ))"
    using only_one_component_tran_all_not_comp_await[OF a0 a1] first a3 
          a0 a1 calculation(1) only_one_component_tran1 prg_j by blast
  moreover then have k:"k=j" using a2  by fastforce
  ultimately have "(\<forall>j. 0\<le>j \<and> j\<noteq>k \<and> Suc j < (length l) \<longrightarrow> 
                          \<not>((\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                              (fst (l ! Suc j), toSeq (snd (l ! Suc j))))))" by auto 
  also from conc k k_basic have 
     " (\<exists>na na' ng. fst (l!k) = Await b c e \<and> 
                      snd (l!k) = (na,ng) \<and> (na,ng) \<in> p \<and>
             snd (l!Suc k) =  (na', ng) \<and> 
            (na' \<in> {s'. ( (na, ng),  (s', ng)) \<in> G \<and> (s',ng)\<in>q} \<and> fst (l!Suc k) = Skip \<or> 
             na' \<in> {s'. ( (na, ng),  (s',ng)) \<in> G \<and> (s',ng)\<in>a}\<and> fst (l!Suc k) = Throw \<or>
            (na = na' \<and> fst(l!Suc k) \<in> Fault ` F)))"
     by fastforce
  ultimately show ?thesis by auto
qed 

lemma one_component_tran_await_env:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
         a1: "fst (l!0) = Await b c e" and         
         a2: "Suc k<length l \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                                (fst (l ! Suc k), toSeq (snd (l ! Suc k))))" and
         a3: "env_tran_right \<Gamma> l rely \<and> Sta p rely \<and> snd (l!0) \<in>  p \<and> 
                                        Sta q rely \<and>
                                        Sta a rely" and
         a4:"p \<subseteq> {s. \<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
                  (b \<inter> {c. c = fst s}) c 
                   {s'. ( s,  (s', snd s)) \<in> G \<and> (s',snd s)\<in> q},
                   {s'. ( s,  (s', snd s)) \<in> G \<and> (s',snd s)\<in> a}}"           
  shows "(\<forall>j. 0\<le>j \<and> j\<noteq>k \<and> Suc j < (length l) \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))) \<and> 
         (\<exists>na na' ng. fst (l!k) = Await b c e  \<and> 
                    snd (l!k) = (na,ng) \<and> (na,ng) \<in> p \<and>
           snd (l!Suc k) =  (na', ng) \<and> 
          (na' \<in> {s'. ( (na, ng),  (s', ng)) \<in> G \<and> (s',ng)\<in>q} \<and> fst (l!Suc k) = Skip \<or> 
           na' \<in> {s'. ( (na, ng),  (s',ng)) \<in> G \<and> (s',ng)\<in>a}\<and> fst (l!Suc k) = Throw \<or>
           (na = na' \<and> fst(l!Suc k) \<in> Fault ` F)))"  
proof - 
  
  have  "(\<forall>j. 0 \<le> j \<and> j \<noteq> k \<and> Suc j < (length l) \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c (l ! j) \<rightarrow>\<^sub>e (l ! Suc j))"
    using conjunct1[OF  one_component_tran_await[OF a0 a1 a2 a3 a4 ]] 
          a0 Suc_eq_plus1 cptn_tran_ce_i prod.exhaust_sel step_ce_dest by metis    
  then show ?thesis using one_component_tran_await[OF a0 a1 a2 a3 a4 ] by auto  
qed

lemma final_exist_component_tran_await:
  assumes a0:"(\<Gamma>, l) \<in> cptn" and
          a1: "fst (l!i) = Await b c e" and               
          a2: "env_tran \<Gamma> q l R " and
          a3: "i\<le>j \<and> j < length l \<and> final_glob (l!j)" 
  shows "\<exists>k. k\<ge>i \<and> k<j \<and> (\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                               (fst (l!(Suc k)), toSeq (snd (l!(Suc k)))))"
proof -
  have  "\<forall>s1 s2 c1. \<Gamma>\<turnstile>\<^sub>c(Await b c e,s1)  \<rightarrow> ((c1,s2)) \<longrightarrow> 
                (c1=Skip)\<or> c1 = Throw \<or> c1 = Stuck \<or> (\<exists>f. c1 = Fault f)" 
    by (simp add: await_skip)
  thus ?thesis using  a0 a1 a2 a3 final_exist_component_tran by blast
qed   

inductive_cases stepc_elim_cases_Await_Fault:
"\<Gamma>\<turnstile>\<^sub>c (Await b c e,  s) \<rightarrow> (Fault f, s')"

lemma Await_sound1: 
 "p \<subseteq> {s. \<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
                  (b \<inter> {c. c = fst s}) e 
                   {s'. ( s,  (s', snd s)) \<in> G \<and> (s',snd s)\<in> q},
                   {s'. ( s,  (s', snd s)) \<in> G \<and> (s',snd s)\<in> a}} \<Longrightarrow>     
 Sta p R \<Longrightarrow> Sta q R \<Longrightarrow> Sta a R \<Longrightarrow>  (\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G) \<Longrightarrow> 
 c \<in> cp \<Gamma> (Await b e e1) s \<Longrightarrow>
 c \<in> assum(p, R) \<Longrightarrow>
 c \<in> comm (G, (q,a)) F"
proof -  
 assume
  a0: "p \<subseteq> {s. \<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
                  (b \<inter> {c. c = fst s}) e 
                   {s'. ( s,  (s', snd s)) \<in> G \<and> (s',snd s)\<in> q},
                   {s'. ( s,  (s', snd s)) \<in> G \<and> (s',snd s)\<in> a}}" and
  a2:"Sta p R" and
  a3:"Sta q R" and
  a4:"Sta a R" and 
  a10:"c \<in> cp \<Gamma> (Await b e e1) s" and
  a11:"c \<in> assum(p, R)" and a12:"(\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G)"

  obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
  {
   have cp:"l!0=(Await b e e1,s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10 cp_def c_prod by fastforce
   have assum:"snd(l!0) \<in> (p) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
             (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
               (snd(l!i), snd(l!(Suc i))) \<in> R)" 
   using a11 c_prod unfolding assum_def by simp
   have concl:"(\<forall>i. Suc i<length l \<longrightarrow> 
           (\<Gamma>\<turnstile>\<^sub>c (fst (l!i), toSeq (snd (l!i)))  \<rightarrow> 
                (fst (l!(Suc i)), toSeq (snd (l!(Suc i))))) \<longrightarrow>                              
             (snd(l!i), snd(l!(Suc i))) \<in> G)"
   proof -
   { fix k ns ns'
     assume a00:"Suc k<length l" and
            a11:"(\<Gamma>1\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                (fst (l!(Suc k)), toSeq (snd (l!(Suc k)))))"                
     have len_l:"length l > 0" using cp using cptn.simps by blast 
     then obtain a1 l1 where l:"l=a1#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
     have env_tran:"env_tran \<Gamma> p l R" using assum env_tran_def cp by blast
     then have env_tran_right: "env_tran_right \<Gamma> l R" 
       using env_tran env_tran_right_def unfolding env_tran_def by auto     
     then have all_event:
          "(\<exists>na na' ng. fst (l!k) = Await b e e1  \<and> 
                    snd (l!k) = (na,ng) \<and> (na,ng) \<in> p \<and>
           snd (l!Suc k) =  (na', ng) \<and> 
          (na' \<in> {s'. ( (na, ng),  (s', ng)) \<in> G \<and> (s',ng)\<in>q} \<and> fst (l!Suc k) = Skip \<or> 
           na' \<in> {s'. ( (na, ng),  (s',ng)) \<in> G \<and> (s',ng)\<in>a}\<and> fst (l!Suc k) = Throw \<or>
           (na = na' \<and> fst(l!Suc k) \<in> Fault ` F)))"
         using a00 a11  one_component_tran_await_env[of \<Gamma> l b e e1 k R p q a F G] env_tran_right cp len_l
         using a0 a2 a3 a4 assum fst_conv  by auto                                                                          
     then obtain na na' ng where ss:
         "fst (l!k) = Await b e e1  \<and> 
                    snd (l!k) = (na,ng) \<and> (na,ng) \<in> p \<and>
           snd (l!Suc k) =  (na', ng) \<and> 
          (na' \<in> {s'. ( (na, ng),  (s', ng)) \<in> G \<and> (s',ng)\<in>q} \<and> fst (l!Suc k) = Skip \<or> 
           na' \<in> {s'. ( (na, ng),  (s',ng)) \<in> G \<and> (s',ng)\<in>a}\<and> fst (l!Suc k) = Throw \<or>
           (na = na' \<and> fst(l!Suc k) \<in> Fault ` F))"
       by fastforce 
     then have "(snd(l!k), snd(l!(Suc k))) \<in> G"
         using a2 a12 unfolding N_def by fastforce
   } thus ?thesis using cp by blast qed     
   have concr:"(final_glob (last l)  \<longrightarrow> fst (last l) \<notin> Fault ` F \<longrightarrow>
               ((fst (last l) = Skip \<and> snd (last l) \<in> q)) \<or>
                (fst (last l) = Throw \<and> snd (last l) \<in>  (a)))"
   proof-
   { 
     assume valid:"final_glob (last l)" and fault:"fst (last l) \<notin> Fault ` F"       
     have len_l:"length l > 0" using cp using cptn.simps by blast 
     then obtain a1 l1 where l:"l=a1#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
     have last_l:"last l = l!(length l-1)"
       using last_length [of a1 l1] l by fastforce
     have env_tran:"env_tran \<Gamma> p l R" using assum env_tran_def cp by blast
     then have env_tran_right: "env_tran_right \<Gamma> l R" 
       using env_tran env_tran_right_def unfolding env_tran_def by auto
     have "\<exists>k. k\<ge>0 \<and> k<((length l) - 1) \<and> 
                (\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                (fst (l!(Suc k)), toSeq (snd (l!(Suc k)))))"
     proof -             
       have "0\<le> (length l-1)" using len_l last_l by auto
       moreover have "(length l-1) < length l" using len_l by auto
       moreover have "final_glob (l!(length l-1))" using valid last_l by auto
       moreover have "fst (l!0) = Await b e e1" using cp by auto
       ultimately show ?thesis 
         using  cp final_exist_component_tran_await env_tran by blast 
     qed
     then obtain k  where k_comp_tran: "k\<ge>0 \<and> Suc k < length l \<and> 
                (\<Gamma>\<turnstile>\<^sub>c (fst (l!k), toSeq (snd (l!k)))  \<rightarrow> 
                (fst (l!(Suc k)), toSeq (snd (l!(Suc k)))))"
       by fastforce            
     obtain na na' ng where all_event:
          "(\<forall>j. 0\<le>j \<and> j\<noteq>k \<and> Suc j < (length l) \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))) \<and> 
         (fst (l!k) = Await b e e1  \<and> 
           snd (l!k) = (na,ng) \<and> (na,ng) \<in> p \<and>
           snd (l!Suc k) =  (na', ng) \<and> 
          (na' \<in> {s'. ( (na, ng),  (s', ng)) \<in> G \<and> (s',ng)\<in>q} \<and> fst (l!Suc k) = Skip \<or> 
           na' \<in> {s'. ( (na, ng),  (s',ng)) \<in> G \<and> (s',ng)\<in>a}\<and> fst (l!Suc k) = Throw \<or>
           na = na' \<and> fst (l!Suc k) \<in> Fault ` F))"
       using  one_component_tran_await_env[of \<Gamma> l b e e1 k R p q a F G] a0 a11 a2 a3 a4 assum cp 
              env_tran_right  len_l  fst_conv  k_comp_tran  by fastforce
     then have before_k_all_evn:"\<forall>j. 0\<le>j \<and> j < k  \<longrightarrow> (\<Gamma>\<turnstile>\<^sub>c(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)))"
           using k_comp_tran by fastforce
     then have 
          k_basic:" (na, ng) \<in>  (p)" using all_event by blast           
     have after_k_all_evn:"\<forall>i. Suc k \<le> i \<and> i < length l - 1 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c l ! i \<rightarrow>\<^sub>e l ! Suc i"
       using all_event k_comp_tran by fastforce   
     then have stat:"((na',ng)\<in>q \<and> fst (l!Suc k) = Skip) \<or> ((na',ng)\<in>a \<and> fst (l!Suc k) = Throw) \<or>
                      fst (l!Suc k) \<in> Fault ` F"
       using all_event
       by blast
     have k:"Suc k \<le> length l - 1 \<and> length l - 1 < length l"
       using k_comp_tran by linarith   
     have "fst (last l) = Skip \<and> 
                snd ((last l)) \<in> q \<or>
                (fst (last l) = Throw \<and> snd (last l) \<in> (a))"
     proof-
       { assume a00:"((na',ng)\<in>q \<and> fst (l!Suc k) = Skip)"
         then have q:"snd (l ! Suc k) \<in>  q"
           using all_event  by fastforce               
         have ?thesis 
           using stability [OF a3 q k _  after_k_all_evn env_tran_right] using a00
           by (simp add: last_l)
       }
       moreover {
         assume a00:"((na',ng)\<in>a \<and> fst (l!Suc k) = Throw)"
         then have q:"snd (l ! Suc k) \<in> a"
           using all_event  by fastforce
         have ?thesis 
           using stability [OF a4 q k _  after_k_all_evn env_tran_right] using a00
           by (simp add: last_l)
       }
       moreover {
         assume "fst (l!Suc k) \<in> Fault ` F"
         then have ?thesis using fault
           using cp k_comp_tran last_not_F by blast
       }
       ultimately show ?thesis using stat by auto
     qed     
   } thus ?thesis by auto qed
   note res = conjI [OF concl concr]               
  }              
  thus ?thesis using c_prod a10 unfolding comm_def split_beta cp_def by auto 
qed 

lemma Await_sound: 
 "p \<subseteq> {s. \<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
                  (b \<inter> {c. c = fst s}) e 
                   {s'. ( s,  (s', snd s)) \<in> G \<and> (s',snd s)\<in> q},
                   {s'. ( s,  (s', snd s)) \<in> G \<and> (s',snd s)\<in> a}} \<Longrightarrow>     
 Sta p R \<Longrightarrow> Sta q R \<Longrightarrow> Sta a R \<Longrightarrow> (\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G) \<Longrightarrow> 
 \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub>  (Await b e e1) sat [p, R, G, q,a]"
proof -  
 assume
  a0: "p \<subseteq> {s. \<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
                  (b \<inter> {c. c = fst s}) e 
                   {s'. ( s,  (s', snd s)) \<in> G \<and> (s',snd s)\<in> q},
                   {s'. ( s,  (s', snd s)) \<in> G \<and> (s',snd s)\<in> a}}" and
  a2:"Sta p R" and
  a3:"Sta q R" and
  a4:"Sta a R"  and a5:"(\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G)"
{
    fix s
    have "cpn n \<Gamma> (Await b e e1) s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cpn n \<Gamma> (Await b e e1) s" and a11:"c \<in> assum(p, R)"
      then have a10:"c\<in>cp \<Gamma> (Await b e e1) s"
        using cp_def cpn_def cptn_if_cptn_mod cptn_mod_nest_cptn_mod by blast
      have "c\<in>comm(G, (q,a)) F" using Await_sound1[OF a0 a2 a3 a4 a5 a10 a11] by auto      
    } thus ?thesis by auto
    qed 
  } 
  thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed

subsection {* If sound *}


lemma cptn_assum_induct:
assumes
  a0: "(\<Gamma>,l) \<in> (cp \<Gamma> c s) \<and> ((\<Gamma>,l) \<in> assum(p, R))" and
  a1: "k < length l \<and> l!k=(c1, s') \<and> s' \<in> p1"
shows "(\<Gamma>,drop k l)\<in> ((cp \<Gamma> c1 ( s')) \<inter> assum(p1, R) )"
proof -
  have drop_k_s:"(drop k l)!0 = (c1, s')" using a1 by fastforce
  have p1:"s' \<in> p1" using a1 by auto
  have k_l:"k < length l" using a1 by auto
  show ?thesis
  proof
    show "(\<Gamma>, drop k l) \<in> cp \<Gamma> c1 ( s')" 
    unfolding cp_def 
    using  a0 a1 drop_k_s 
    by (simp add: cp_def dropcptn_is_cptn)     
  next
    let ?c= "(\<Gamma>,drop k l)"
    have l:"snd((snd ?c!0)) \<in>  p1"
     using p1 drop_k_s by auto
    {fix i
     assume a00:"Suc i<length (snd ?c)" 
     assume a11:"(fst ?c)\<turnstile>\<^sub>c((snd ?c)!i)  \<rightarrow>\<^sub>e ((snd ?c)!(Suc i))"
     have "(snd((snd ?c)!i), snd((snd ?c)!(Suc i))) \<in> R "
     using a0 unfolding assum_def using a00 a11 by auto
    } thus "(\<Gamma>, drop k l) \<in> assum (p1, R)" 
      using l unfolding assum_def by fastforce  
  qed  
qed

lemma cptn_comm_induct:
assumes
  a0: "(\<Gamma>,l) \<in> (cp \<Gamma> c s)" and
  a1: "l1 = drop j l \<and> (\<Gamma>, l1)\<in> comm(G, (q,a)) F" and
  a2: "k \<ge> j \<and> j < length l" 
shows " ((Suc k < length l \<longrightarrow>
       (\<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
        (fst (l ! Suc k), toSeq (snd (l ! Suc k))) ) \<longrightarrow>        
       (snd(l!k), snd(l!(Suc k))) \<in> G) 
      \<and> (final_glob (last (l))  \<longrightarrow>  fst (last (l)) \<notin> Fault ` F  \<longrightarrow>         
            ((fst (last (l)) = Skip \<and> snd (last (l)) \<in>  q)) \<or>
            (fst (last (l)) = Throw \<and> snd (last (l)) \<in>  (a))))"
proof -  
  have pair_\<Gamma>l:"fst (\<Gamma>,l1) = \<Gamma> \<and> snd (\<Gamma>,l1) = l1" by fastforce  
  have a03:"(\<forall>i.                 
               Suc i<length (snd (\<Gamma>, l1)) \<longrightarrow> 
               (\<Gamma>\<turnstile>\<^sub>c (fst (l1 ! i), toSeq (snd (l1 ! i))) \<rightarrow> 
                    (fst (l1 ! Suc i), toSeq (snd (l1 ! Suc i))) ) \<longrightarrow>                                             
                 (snd((snd (\<Gamma>, l1))!i), snd((snd (\<Gamma>, l1))!(Suc i))) \<in> G) \<and> 
               (final_glob (last (snd (\<Gamma>, l1)))  \<longrightarrow> fst (last (l1)) \<notin> Fault ` F  \<longrightarrow>                 
                  ((fst (last (snd (\<Gamma>, l1))) = Skip \<and> snd (last (snd (\<Gamma>, l1))) \<in>  q)) \<or>
                  (fst (last (snd (\<Gamma>, l1))) = Throw \<and> snd (last (snd (\<Gamma>, l1))) \<in>  (a)))"
  using a1 unfolding comm_def by fastforce
  have last_l:"last l1 = last l" using a1 a2 by fastforce
  show ?thesis  
  proof -
    {       
      { assume "Suc k < length l"
      then have a2: "k \<ge> j \<and> Suc k < length l" using a2 by auto
      have "k \<le> length l" using a2 by fastforce
      then have l1_l:"(l!k = l1! (k - j) ) \<and> (l!Suc k = l1!Suc (k - j))"
        using a1 a2 by fastforce    
      have a00:"Suc (k - j) < length l1" using a1 a2 by fastforce
      have "\<Gamma>\<turnstile>\<^sub>c(fst(l1!(k-j)),toSeq(snd (l1!(k-j))))  \<rightarrow> 
               (fst(l1!(Suc (k-j))),toSeq(snd (l1!(Suc (k-j))))) \<longrightarrow>         
        (snd((snd (\<Gamma>, l1))!(k-j)), snd((snd (\<Gamma>, l1))!(Suc (k-j)))) \<in> G"
      using  pair_\<Gamma>l a00  a03 by presburger
      then have " (\<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                   (fst (l ! Suc k), toSeq (snd (l ! Suc k))) ) \<longrightarrow> 
        (snd (l ! k), snd (l ! Suc k)) \<in> G " 
        using l1_l last_l by auto
    } 
    then have l_side:
       "Suc k < length l \<longrightarrow>
        (\<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
        (fst (l ! Suc k), toSeq (snd (l ! Suc k))) ) \<longrightarrow>   
         (snd (l ! k), snd (l ! Suc k)) \<in> G" 
      by auto 
    { 
      assume a10:"final_glob (last (l))" and  fault:" fst (last l) \<notin> Fault ` F" 
      then have l1_f:"fst (last l1) \<notin> Fault ` F" 
        using a03 a1 a2 by force                 
      then have final_eq: "final_glob (last (l1))"
        using a10 a1 a2 by fastforce
      also have "fst (last (l1)) \<notin> Fault ` F"
        using last_l l1_f by fastforce
      ultimately have "((fst (last (snd (\<Gamma>, l1))) = Skip \<and> snd (last (snd (\<Gamma>, l1))) \<in>  q)) \<or>
                      (fst (last (snd (\<Gamma>, l1))) = Throw \<and> snd (last (snd (\<Gamma>, l1))) \<in>  (a))"
        using pair_\<Gamma>l a03 by presburger
      then have "((fst (last (snd (\<Gamma>, l))) = Skip \<and> snd (last (snd (\<Gamma>, l))) \<in>  q)) \<or>
              (fst (last (snd (\<Gamma>, l))) = Throw \<and> snd (last (snd (\<Gamma>, l))) \<in>  (a))"
        using final_eq a1 a2 by auto 
     } then have 
      r_side: 
      "final_glob (last l) \<longrightarrow>   fst (last l) \<notin> Fault ` F \<longrightarrow>   
      fst (last l) = LanguageCon.com.Skip \<and> snd (last l) \<in>  q \<or>
       fst (last l) = LanguageCon.com.Throw \<and> snd (last l) \<in> a"
       by fastforce
     note res=conjI[OF l_side r_side] 
   } thus ?thesis by auto
   qed
qed

lemma cpn_assum_induct:
assumes
  a0: "(\<Gamma>,l) \<in> (cpn n \<Gamma> c s) \<and> ((\<Gamma>,l) \<in> assum(p, R))" and
  a1: "k < length l \<and> l!k=(c1, s') \<and> s' \<in> p1"
shows "(\<Gamma>,drop k l)\<in> ((cpn n \<Gamma> c1 ( s')) \<inter> assum(p1, R) )"
proof -
  have drop_k_s:"(drop k l)!0 = (c1, s')" using a1 by fastforce
  have p1:"s' \<in> p1" using a1 by auto
  have k_l:"k < length l" using a1 by auto
  show ?thesis
  proof
    show "(\<Gamma>, drop k l) \<in> cpn n \<Gamma> c1 ( s')" 
    unfolding cp_def 
    using  a0 a1  
    by (simp add: cpn_def dropcptn_is_cptn1) 
  next
    let ?c= "(\<Gamma>,drop k l)"
    have l:"snd((snd ?c!0)) \<in>  p1"
     using p1 drop_k_s by auto
    {fix i
     assume a00:"Suc i<length (snd ?c)" 
     assume a11:"(fst ?c)\<turnstile>\<^sub>c((snd ?c)!i)  \<rightarrow>\<^sub>e ((snd ?c)!(Suc i))"
     have "(snd((snd ?c)!i), snd((snd ?c)!(Suc i))) \<in> R "
     using a0 unfolding assum_def using a00 a11 by auto
    } thus "(\<Gamma>, drop k l) \<in> assum (p1, R)" 
      using l unfolding assum_def by fastforce  
  qed  
qed

lemma cpn_comm_induct:
  assumes
  a1: "l1 = drop j l \<and> (\<Gamma>, l1)\<in> comm(G, (q,a)) F" and
  a2: "k \<ge> j \<and> j < length l" 
shows " ((Suc k < length l \<longrightarrow>
       (\<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
        (fst (l ! Suc k), toSeq (snd (l ! Suc k))) ) \<longrightarrow>        
       (snd(l!k), snd(l!(Suc k))) \<in> G) 
      \<and> (final_glob (last (l))  \<longrightarrow>  fst (last (l)) \<notin> Fault ` F  \<longrightarrow>         
            ((fst (last (l)) = Skip \<and> snd (last (l)) \<in>  q)) \<or>
            (fst (last (l)) = Throw \<and> snd (last (l)) \<in> (a))))"
proof -  
  have pair_\<Gamma>l:"fst (\<Gamma>,l1) = \<Gamma> \<and> snd (\<Gamma>,l1) = l1" by fastforce  
  have a03:"(\<forall>i. Suc i<length (snd (\<Gamma>, l1)) \<longrightarrow> 
               (\<Gamma>\<turnstile>\<^sub>c (fst (l1 ! i), toSeq (snd (l1 ! i))) \<rightarrow> 
                    (fst (l1 ! Suc i), toSeq (snd (l1 ! Suc i))) ) \<longrightarrow>                                             
                 (snd((snd (\<Gamma>, l1))!i), snd((snd (\<Gamma>, l1))!(Suc i))) \<in> G) \<and> 
               (final_glob (last (snd (\<Gamma>, l1)))  \<longrightarrow>  fst (last (l1)) \<notin> Fault ` F  \<longrightarrow>               
                  ((fst (last (snd (\<Gamma>, l1))) = Skip \<and> snd (last (snd (\<Gamma>, l1))) \<in> q)) \<or>
                  (fst (last (snd (\<Gamma>, l1))) = Throw \<and>snd (last (snd (\<Gamma>, l1))) \<in> (a)))"
  using a1 unfolding comm_def by fastforce
  have last_l:"last l1 = last l" using a1 a2 by fastforce
  { assume "Suc k < length l"
      then have a2: "k \<ge> j \<and> Suc k < length l" using a2 by auto
      have "k \<le> length l" using a2 by fastforce
      then have l1_l:"(l!k = l1! (k - j) ) \<and> (l!Suc k = l1!Suc (k - j))"
        using a1 a2 by fastforce    
      have a00:"Suc (k - j) < length l1" using a1 a2 by fastforce
      have "\<Gamma>\<turnstile>\<^sub>c(fst(l1!(k-j)),toSeq(snd (l1!(k-j))))  \<rightarrow> 
               (fst(l1!(Suc (k-j))),toSeq(snd (l1!(Suc (k-j))))) \<longrightarrow>         
        (snd((snd (\<Gamma>, l1))!(k-j)), snd((snd (\<Gamma>, l1))!(Suc (k-j)))) \<in> G"
      using  pair_\<Gamma>l a00  a03 by presburger
      then have "(\<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                   (fst (l ! Suc k), toSeq (snd (l ! Suc k))) ) \<longrightarrow> 
        (snd (l ! k), snd (l ! Suc k)) \<in> G " 
        using l1_l last_l by auto
   } then have l_side:"Suc k < length l \<longrightarrow>
    (\<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
         (fst (l ! Suc k), toSeq (snd (l ! Suc k))) ) \<longrightarrow>   
    (snd (l ! k), snd (l ! Suc k)) \<in> G" by auto 
   { 
     assume a10:"final_glob (last (l))"  and l1_f:"fst (last (l)) \<notin> Fault ` F "         
     then have final_eq: "final_glob (last (l1))"
       using a10 a1 a2 by fastforce
     also have "fst (last (l1)) \<notin> Fault ` F"
       using last_l l1_f by fastforce
     ultimately have "((fst (last (snd (\<Gamma>, l1))) = Skip \<and> 
                      snd (last (snd (\<Gamma>, l1))) \<in>  q)) \<or>
                    (fst (last (snd (\<Gamma>, l1))) = Throw \<and> 
                      snd (last (snd (\<Gamma>, l1))) \<in>  (a))"
       using pair_\<Gamma>l a03 by presburger
     then have "((fst (last (snd (\<Gamma>, l))) = Skip \<and> 
            snd (last (snd (\<Gamma>, l))) \<in>  q)) \<or>
            (fst (last (snd (\<Gamma>, l))) = Throw \<and> 
           snd (last (snd (\<Gamma>, l))) \<in> (a))"
       using final_eq a1 a2 by auto 
   } 
   then have 
    r_side: 
    "final_glob (last l) \<longrightarrow>  fst (last (l)) \<notin> Fault ` F \<longrightarrow>
    fst (last l) = LanguageCon.com.Skip \<and> snd (last l) \<in> q \<or>
     fst (last l) = LanguageCon.com.Throw \<and> snd (last l) \<in> a"
     by fastforce     
   note res=conjI[OF l_side r_side]    
   then show ?thesis by auto
 qed




lemma If_sound: 
      "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> {c. (fst c) \<in> b},  R, G, q,a] \<Longrightarrow>
       (\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> {c. (fst c) \<in> b},  R, G, q,a]) \<Longrightarrow>
       \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [p \<inter> {c. (fst c) \<in> (-b)},  R, G, q,a] \<Longrightarrow>
       (\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c2 sat [p \<inter> {c. (fst c) \<in> (-b)},  R, G, q,a]) \<Longrightarrow>      
       Sta p R \<Longrightarrow> (\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G)  \<Longrightarrow> 
       \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (Cond b c1 c2) sat [p, R, G, q,a]"
proof -  
 assume
    a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> {c. (fst c) \<in> b},  R, G, q,a]" and
    a1:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [p \<inter> {c. (fst c) \<in> (-b)}, R, G, q,a]" and    
    a2: "\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> {c. (fst c) \<in> b}, R, G, q,a]" and
    a3: "\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c2 sat [p \<inter> {c. (fst c) \<in> (-b)}, R, G, q,a]" and
    a4: "Sta p R" and
    a5: "(\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G)"
  { 
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"
    then have a3:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c2 sat [p \<inter> {c. (fst c) \<in> (-b)}, R, G, q,a]" 
      using a3 com_cvalidityn_def  by fastforce 
    have a2:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> {c. (fst c) \<in> b}, R, G, q,a]"
      using a2 all_call com_cvalidityn_def  by fastforce 
    have "cpn n \<Gamma> (Cond b c1 c2)  s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cpn n \<Gamma> (Cond b c1 c2) s" and a11:"c \<in> assum(p, R)"
      then have a10':"c \<in> cp \<Gamma> (Cond b c1 c2) s" unfolding cp_def cpn_def
        using cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod by fastforce
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (q,a)) F"      
      proof -         
      {have cp:"l!0=((Cond b c1 c2),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10' cp_def c_prod by fastforce
       have \<Gamma>1:"(\<Gamma>, l) = c" using c_prod cp by blast
       have assum:"snd(l!0) \<in>  (p) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
                   (snd(l!i), snd(l!(Suc i))) \<in> R)" 
       using a11 c_prod unfolding assum_def by simp
       then have env_tran:"env_tran \<Gamma> p l R" using env_tran_def cp by blast
       then have env_tran_right: "env_tran_right \<Gamma> l R" 
         using env_tran env_tran_right_def unfolding env_tran_def by auto
       have concl:"(\<forall>i. Suc i<length l \<longrightarrow> 
               (\<Gamma>1\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                     (fst (l ! Suc i), toSeq (snd (l ! Suc i))) ) \<longrightarrow>               
                 (snd(l!i), snd(l!(Suc i))) \<in> G)"
       proof -
       { fix k ns ns'
         assume a00:"Suc k<length l" and
                a21:"(\<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                          (fst (l ! Suc k), toSeq (snd (l ! Suc k))) )"                                                                           
         obtain j where before_k_all_evnt:
           "j\<le>k \<and>  (\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                         (fst (l ! Suc j), toSeq (snd (l ! Suc j))) ) \<and> 
            (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
           using a00 a21 exist_first_comp_tran cp by blast
         then obtain cj sj csj ssj where pair_j:
              "(\<Gamma>\<turnstile>\<^sub>c(cj,sj)  \<rightarrow> (csj,ssj)) \<and> 
                cj = fst (l!j) \<and> sj = toSeq(snd (l!j)) \<and> csj = fst (l!(Suc j)) \<and> 
                 ssj = toSeq(snd(l!(Suc j)))"
           by fast  
         then have  pair_j1:"(\<Gamma>\<turnstile>\<^sub>c(fst (l!j),toSeq(snd (l!j)))  \<rightarrow> (fst (l!(Suc j)),toSeq(snd(l!(Suc j)))))"
           by auto
         have k_basic1:"cj = (Cond b c1 c2) \<and> snd (l!j) \<in> (p)" 
           using pair_j before_k_all_evnt cp env_tran_right a4 assum a00 stability[of p R l 0 j j \<Gamma>]
         by force
         have k_basic:"cj = (Cond b c1 c2) \<and> sj \<in> (fst` p)" 
           using pair_j before_k_all_evnt cp env_tran_right a4 assum a00 stability[of p R l 0 j j \<Gamma>]
         by force
         then obtain s' where ss:"sj = s' \<and> s'\<in> (fst ` p)" by fastforce 
         moreover have ssj_normal_s:"ssj =  s'" 
           using before_k_all_evnt k_basic pair_j calculation
           by (metis snd_conv stepc_elim_cases(6)) 
         ultimately obtain sl where 
           lj:"snd (l!j) =  (s', sl) \<and> snd (l!(Suc j)) =  (s', sl)"
           using  cp  l2[of \<Gamma> "fst (l!j)" "snd (l!j)" "fst (l!(Suc j))" "snd (l!(Suc j))" ] a00
           using before_k_all_evnt pair_j  cptn_tran_ce_i l1 by fastforce           
         have "(snd(l!k), snd(l!(Suc k))) \<in> G"
           using ss a2 unfolding Satis_def         
         proof (cases "k=j")   
           case True          
             have "( (s', sl),  (s', sl)) \<in> G" 
               using a5 k_basic1 lj unfolding N_def  by fastforce
             thus "(snd (l ! k), snd (l ! Suc k)) \<in> G"
               using pair_j k_basic True ss ssj_normal_s lj by auto
         next
           case False
           have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce 
           have l_suc:"l!(Suc j) = (csj,  (s',sl))" 
             using before_k_all_evnt pair_j lj ssj_normal_s
             by (metis prod.exhaust_sel)
           have l_k:"j<k" using  before_k_all_evnt False by fastforce
           have "s'\<in>b \<or> s'\<notin>b" by auto                         
           thus "(snd (l ! k), snd (l ! Suc k)) \<in> G"
           proof
             assume a000:"s'\<in>b"
             then have cj:"csj=c1" using k_basic pair_j ss 
               by (metis (no_types) fst_conv stepc_elim_cases(6))
             moreover have p1:"(s',sl) \<in> (p \<inter> {c. (fst c) \<in> b})" 
               using a000 ss k_basic1 lj by auto              
             moreover  have "cpn n \<Gamma> csj ( (s',sl)) \<inter> assum((p \<inter> {c. (fst c) \<in> b}), R) \<subseteq> comm(G, (q,a)) F"
               using calculation a2 com_validityn_def cj by blast             
             ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
               using l_suc j_length a10 a11 \<Gamma>1  ssj_normal_s
                     cpn_assum_induct[of \<Gamma> l n "(LanguageCon.com.Cond b c1 c2)" s p R  "Suc j" c1 "(s',sl)" "(p \<inter> {c. (fst c) \<in> b})"]
               by blast                         
             show ?thesis 
               using l_k drop_comm a00 a21  a10 \<Gamma>1   
               cpn_comm_induct
               by fastforce                       
           next
             assume a000:"s'\<notin>b"
             then have cj:"csj=c2" using k_basic pair_j ss 
               by (metis (no_types) fst_conv stepc_elim_cases(6))
             moreover have p1:"(s',sl) \<in> (p \<inter> {c. (fst c) \<in> (-b)})"  
                  using a000 ss ss l_suc k_basic1 lj by auto     
             moreover then have "cpn n \<Gamma> csj ( (s',sl)) \<inter> assum((p \<inter> {c. (fst c) \<in> (-b)}), R)  \<subseteq> comm(G, (q,a)) F"
               using a3 com_validityn_def cj by blast             
             ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
               using l_suc j_length a10 a11 \<Gamma>1  ssj_normal_s
                     cpn_assum_induct[of \<Gamma> l n "(LanguageCon.com.Cond b c1 c2)" s p R  "Suc j" c2 "(s',sl)" "(p \<inter> {c. (fst c) \<in> (-b)})"]
               by fastforce             
             show ?thesis 
               using l_k drop_comm a00 a21 a10 \<Gamma>1 cpn_comm_induct
               unfolding Satis_def by fastforce
           qed
         qed 
       } thus ?thesis by (simp add: c_prod cp) qed
       have concr:"(final_glob (last l)  \<longrightarrow> fst (last l) \<notin> Fault ` F \<longrightarrow>
                   ((fst (last l) = Skip \<and> snd (last l) \<in>  q)) \<or>
                    (fst (last l) = Throw \<and> snd (last l) \<in> (a)))"
       proof-
       { 
         assume valid:"final_glob (last l)" 
         assume not_fault:  "fst (last l) \<notin> Fault ` F"                 
         have "\<exists>k. k\<ge>0 \<and> k<((length l) - 1) \<and> 
                          \<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                          (fst (l ! Suc k), toSeq (snd (l ! Suc k))) \<and> 
                 final_glob (l!(Suc k))"
         proof -             
           have len_l:"length l > 0" using cp using cptn.simps by blast 
           then obtain a1 l1 where l:"l=a1#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
           have last_l:"last l = l!(length l-1)"
             using last_length [of a1 l1] l by fastforce
           have final_0:"\<not>final_glob(l!0)" using cp unfolding final_glob_def by auto
           have "0\<le> (length l-1)" using len_l last_l by auto
           moreover have "(length l-1) < length l" using len_l by auto
           moreover have "final_glob (l!(length l-1))" using valid last_l by auto
           moreover have "fst (l!0) = LanguageCon.com.Cond b c1 c2" using cp by auto
           ultimately show ?thesis 
             using cp final_exist_component_tran_final env_tran_right final_0  
             by blast 
         qed
         then obtain k where a21: "k\<ge>0 \<and> k<((length l) - 1) \<and> 
              \<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                (fst (l ! Suc k), toSeq (snd (l ! Suc k))) \<and> final_glob (l!(Suc k))"
           by auto
        then have a00:"Suc k<length l" by fastforce
        then obtain j where before_k_all_evnt:
          "j\<le>k \<and>  \<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                       (fst (l ! Suc j), toSeq (snd (l ! Suc j))) \<and> (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
           using a00 a21 exist_first_comp_tran cp by blast
         then obtain cj sj csj ssj where 
             pair_j:"\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                          (fst (l ! Suc j), toSeq (snd (l ! Suc j))) \<and> 
                      cj = fst (l!j) \<and> sj = toSeq(snd (l!j)) \<and>  
                      csj = fst (l!(Suc j)) \<and> ssj = toSeq(snd(l!(Suc j)))"
         by fastforce
       have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce                                 
       then have k_basic1:"cj = (Cond b c1 c2) \<and> snd (l!j) \<in>(p)" 
         using  pair_j before_k_all_evnt cp env_tran_right a4 assum a00 stability[of p R l 0 j j \<Gamma>]
         by fastforce
       have k_basic:"cj = (Cond b c1 c2) \<and> sj \<in>  (fst` p)" 
           using pair_j before_k_all_evnt cp env_tran_right a4 assum a00 stability[of p R l 0 j j \<Gamma>]
         by force
       then obtain s' where ss:"sj =  s' \<and> s'\<in> (fst ` p)"
         by blast 
       moreover have ssj_normal_s:"ssj =  s'" using before_k_all_evnt k_basic pair_j
          using before_k_all_evnt k_basic pair_j calculation
           by (metis snd_conv stepc_elim_cases(6)) 
       ultimately obtain sl where 
           lj:"snd (l!j) =  (s', sl) \<and> snd (l!(Suc j)) =  (s', sl)"
           using  cp  l2[of \<Gamma> "fst (l!j)" "snd (l!j)" "fst (l!(Suc j))" "snd (l!(Suc j))"] a00
           using before_k_all_evnt pair_j by fastforce
       have l_suc:"l!(Suc j) = (csj,  (s',sl))" 
             using before_k_all_evnt pair_j lj ssj_normal_s
             by (metis prod.exhaust_sel)
       have "s'\<in>b \<or> s'\<notin>b" by auto 
       then have "((fst (last l) = Skip \<and> snd (last l) \<in>  q)) \<or>
                    (fst (last l) = Throw \<and> snd (last l) \<in>  (a))"
       proof
         assume a000:"s'\<in>b"
         then have cj:"csj=c1" using k_basic pair_j ss 
                  by (metis (no_types) fst_conv stepc_elim_cases(6))
         moreover have p1:"(s',sl) \<in> (p \<inter> {c. (fst c) \<in> b})" using a000 ss  k_basic1 lj by auto 
         moreover then have "cpn n \<Gamma> csj ( (s', sl)) \<inter> assum((p \<inter> {c. (fst c) \<in> b}), R)  \<subseteq> comm(G, (q,a)) F"
           using a2 com_validityn_def cj by blast         
         ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
           using  j_length a10 a11 \<Gamma>1  ssj_normal_s l_suc
                 cpn_assum_induct[of \<Gamma> l n "(LanguageCon.com.Cond b c1 c2)" s p R  "Suc j" c1 "(s',sl)" "(p \<inter> {c. (fst c) \<in> b})"]           
           by blast                   
         thus ?thesis       
           using j_length drop_comm   a10 \<Gamma>1  cpn_comm_induct valid not_fault 
           by blast
       next
         assume a000:"s'\<notin>b"
         then have cj:"csj=c2" using k_basic pair_j ss 
                  by (metis (no_types) fst_conv stepc_elim_cases(6))
         moreover have p1:"(s',sl) \<in>{c. (fst c) \<in> (-b)}" using a000 ss k_basic1 lj by auto 
         moreover then have "cpn n \<Gamma> csj ( (s',sl)) \<inter> assum((p \<inter> {c. (fst c) \<in> (-b)}), R)  \<subseteq> comm(G, (q,a)) F"
           using a3 com_validityn_def cj by blast         
         ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
           using j_length a10 a11 \<Gamma>1  l_suc k_basic1 lj 
                 cpn_assum_induct[of \<Gamma> l n "(LanguageCon.com.Cond b c1 c2)" s p R  "Suc j" c2 "(s',sl)" "(p \<inter> {c. (fst c) \<in> (-b)})"]
           by auto                   
         thus ?thesis       
           using j_length drop_comm a10 \<Gamma>1  cpn_comm_induct valid not_fault 
           by blast
       qed
       } thus ?thesis  by fastforce qed
       note res = conjI [OF concl concr]              
      }             
      thus ?thesis using c_prod  unfolding comm_def by auto  qed      
    } thus ?thesis by auto qed 
} thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed


lemma Asm_sound:
   "(c, p, R, G, q, a) \<in> \<Theta> \<Longrightarrow>    
    \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]
   "
proof -
  assume
   a0:"(c, p, R, G, q, a) \<in> \<Theta>"    
   { fix s
     assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p,  R, G, q,a]"
     then have "\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]" using a0 by auto
   } thus ?thesis unfolding com_cvalidityn_def by auto
qed

lemma events_p:
  assumes  a0:"(\<Gamma>,cfg#l)\<in>cptn" and
   a1:"(\<Gamma>,cfg#l) \<in> assum (p,R)" and
   a2:"i<length (cfg#l)" and
   a3:"\<forall>k\<le>i. fst ((cfg#l)!k) = fst cfg" and
   a4:"Sta p R " 
 shows "\<exists>t1. snd((cfg#l)!i)= t1 \<and> t1 \<in> p" 
  using a2 a3
proof(induct i)
  case 0
  then show ?case using a1 a2 unfolding assum_def by auto
next
  case (Suc n)
  then have "\<exists>t1. snd ((cfg # l) ! n) =  t1 \<and> t1 \<in> p" by auto 
  moreover have "\<Gamma>\<turnstile>\<^sub>c ((cfg#l)!n) \<rightarrow>\<^sub>e ((cfg#l)!(Suc n))" using Suc a0 
    using calculation
    by (metis Suc_eq_plus1 cptn_tran_ce_i le_eq_less_or_eq lessI mod_env_not_component prod.exhaust_sel step_ce_dest)
  then have  "(snd ((cfg#l)!n),snd ((cfg#l)!(Suc n)))\<in>R" using a1 Suc(2) 
    unfolding assum_def by auto
  ultimately show ?case using a4 unfolding Sta_def by blast
qed


lemma not_val_zero:"c \<in> dom \<Gamma> \<Longrightarrow> Sta p R \<Longrightarrow> \<Gamma> \<Turnstile>0\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]"
proof-
  assume a0:" c \<in> dom \<Gamma>"
  assume a1:"Sta p R"
  {fix l s
    assume a01:"(\<Gamma>,l) \<in> cpn 0 \<Gamma> (Call c) s \<and> (\<Gamma>,l)\<in> assum(p, R)"    
    then have "length l \<ge> 1" unfolding cpn_def using CptnEmpty
      by (metis (no_types, lifting) One_nat_def Product_Type.Collect_case_prodD Suc_leI length_greater_0_conv snd_conv)
    moreover {assume a02:"length l = 1"
      then have "l = [(Call c,s)]" 
      proof -
        have "l ! 0 = (LanguageCon.com.Call c, s)" using a01 unfolding cpn_def
          by fastforce
        then show ?thesis using a02
          by (metis One_nat_def Suc_leI impossible_Cons length_greater_0_conv list.size(3) neq_Nil_conv nth_Cons_0 zero_neq_one) 
      qed 
      then have "(\<Gamma>,l) \<in> comm(G, (q,a)) F" unfolding comm_def final_glob_def by auto
    }
    moreover {assume a02:"length l > 1"
      then obtain a1 ls where l:"l =(Call c, s)#a1#ls" using a01 unfolding cpn_def
        apply auto
        by (metis (no_types, hide_lams) One_nat_def Suc_eq_plus1 less_not_refl list.exhaust list.size(3) list.size(4) not_less_zero nth_Cons_0 prod.collapse)   
      have l_cptn:"(\<Gamma>,l)\<in>cptn" using a01 unfolding cpn_def
        using cptn_eq_cptn_mod_nest by blast
      then obtain m where min_call:"min_call m \<Gamma> l"
          using cptn_eq_cptn_mod_set cptn_mod_cptn_mod_nest minimum_nest_call by blast
      { assume a03:"\<forall>i<length l. fst (l!i) = Call c"        
        then have "(\<Gamma>,l) \<in> comm(G, (q,a)) F" 
          using no_comp_tran_no_final_comm[OF _ a03] a02 unfolding final_glob_def
          by fastforce 
      }
      moreover { assume a03:"\<not> (\<forall>i<length l. fst (l!i) = Call c)"
        then obtain i where i:"(i<length l \<and> fst (l!i) \<noteq> Call c)"
          by auto
        then obtain j where cfg_j:"fst (l!j) \<noteq> Call c \<and> (\<forall>k<j. fst (l!k) = Call c)"                     
          by (fast dest: exists_first_occ[of "\<lambda>i. fst (l!i) \<noteq> Call c" i])
        moreover have j:"j>0 \<and> j<length l" using l i calculation
          by (metis (no_types, lifting) Suc_lessD fst_conv less_trans_Suc linorder_neqE_nat nth_non_equal_first_eq)
        ultimately have step:" (\<Gamma>\<turnstile>\<^sub>c (fst (l ! (j-1)), toSeq (snd (l ! (j-1)))) \<rightarrow> 
                    (fst (l! j), toSeq (snd (l ! j))) )"
          using l l_cptn cptn_stepc_rtran not_eq_not_env  step_ce_dest
          by (metis (no_types, lifting) One_nat_def Suc_diff_Suc diff_less diff_zero prod.exhaust_sel zero_less_one)
        moreover obtain s' where j_1_cfg:"snd (l!(j-1)) =  s' \<and> s' \<in> p"
          using cfg_j l a01[simplified l] j[simplified l] i a1 events_p[OF l_cptn[simplified l] _ _ _ a1, of "j-1"]
          by fastforce
        then have j_cfg:"(fst (l! j), toSeq (snd (l ! j)))  = (the (\<Gamma> c),  (fst s'))"
          using cfg_j a0 l l_cptn 
           stepc_elim_cases(9)[of \<Gamma> "c" "fst s'" "(fst (l! j),toSeq (snd (l!j)))"] 
           calculation j 
          by (metis (no_types, lifting) diff_less domIff option.sel toSeq.simps(1) zero_less_one)        
        then have j_cfg_1:"l!j = (the (\<Gamma> c), s')" using l2[OF step l_cptn _ _ ]
          by (metis Suc_diff_1 eq_snd_iff fst_conv j j_1_cfg toSeq.simps(1))
        ultimately have False
        proof-
          have cptn_drop:"(0,\<Gamma>, drop (j-1) l) \<in> cptn_mod_nest_call" 
            using a01 unfolding cpn_def 
            by (simp add: dropcptn_is_cptn1 j less_imp_diff_less)      
          then show ?thesis 
            using  j j_cfg j_1_cfg cfg_j  a0 j_cfg_1 elim_cptn_mod_nest_call_0_False
            by (metis (no_types, lifting) Cons_nth_drop_Suc One_nat_def Suc_diff_Suc Suc_lessD 
                 diff_less diff_zero domIff option.collapse prod.exhaust_sel zero_less_one)               
        qed          
      }
      ultimately have "(\<Gamma>,l) \<in> comm(G, (q,a)) F" by auto
    }
    ultimately have "(\<Gamma>,l)\<in>comm(G, (q,a)) F" by fastforce
  } then show ?thesis unfolding com_validityn_def cpn_def by auto    
qed

lemma Call_sound: 
      "f \<in> dom \<Gamma> \<Longrightarrow>      
       \<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (the (\<Gamma> f)) sat [p, R, G, q,a] \<Longrightarrow>         
       Sta p R \<Longrightarrow> (\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G)  \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (Call f) sat [p, R, G, q,a]"
proof -  
  assume
    a0:"f \<in> dom \<Gamma>" and
    a2:"\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (the (\<Gamma> f)) sat [p, R, G, q,a]" and        
    a3: "Sta p R" and
    a4: "(\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G)"         
  obtain bdy where a0:"\<Gamma> f = Some bdy" using a0 by auto
  { 
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p,  R, G, q,a]"  
    then have a2:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> bdy sat [p, R, G, q,a]" 
      using a0 a2 com_cvalidityn_def by fastforce
    have "cpn n \<Gamma> (Call f)  s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cpn n \<Gamma> (Call f) s" and a11:"c \<in> assum(p, R)"
      then have a10':"c \<in> cp \<Gamma> (Call f) s" 
        unfolding cpn_def cp_def using cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod by fastforce
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (q,a)) F"      
      proof - 
      {       
        have cp:"l!0=((Call f),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10' cp_def c_prod by fastforce
        have \<Gamma>1:"(\<Gamma>, l) = c" using c_prod cp by blast
        have assum:"snd(l!0) \<in>  (p) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
                   (snd(l!i), snd(l!(Suc i))) \<in> R)" 
       using a11 c_prod unfolding assum_def by simp
       then have env_tran:"env_tran \<Gamma> p l R" using env_tran_def cp by blast
       then have env_tran_right: "env_tran_right \<Gamma> l R" 
         using env_tran env_tran_right_def unfolding env_tran_def by auto
       have concl:"(\<forall>i. Suc i<length l \<longrightarrow> 
                (\<Gamma>1\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                    (fst (l ! Suc i), toSeq (snd (l ! Suc i))) ) \<longrightarrow>                              
                 (snd(l!i), snd(l!(Suc i))) \<in> G)"
       proof -
       { fix k
         assume a00:"Suc k<length l" and
                a21:"(\<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                    (fst (l ! Suc k), toSeq (snd (l ! Suc k))) )"                                                      
         obtain j where before_k_all_evnt:"j\<le>k \<and>  
                  (\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                    (fst (l ! Suc j), toSeq (snd (l ! Suc j))) ) \<and> 
                 (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
           using a00 a21 exist_first_comp_tran cp by blast
         then obtain cj sj csj ssj where pair_j:
           "(\<Gamma>\<turnstile>\<^sub>c(cj,sj)  \<rightarrow> (csj,ssj)) \<and> cj = fst (l!j) \<and> sj = toSeq(snd (l!j)) \<and> 
             csj = fst (l!(Suc j)) \<and> ssj = toSeq(snd(l!(Suc j)))"
           by fast              
         have k_basic1:"cj = (Call f) \<and> snd (l!j)  \<in> ( p)" 
           using  pair_j before_k_all_evnt cp env_tran_right a3 assum a00 stability[of p R l 0 j j \<Gamma>]
           by force
         then have k_basic:"cj = (Call f) \<and> sj \<in>  (fst ` p)" 
           using  pair_j toSeq.simps(1) 
           by (metis (no_types, lifting) imageI toSeq.simps(1))
         then obtain s' where ss:"sj =  s' \<and> s'\<in> (fst ` p)" by blast 
         moreover have ssj_normal_s:"ssj =  s'" 
           using before_k_all_evnt k_basic pair_j a0 calculation
           by (metis not_None_eq snd_conv stepc_elim_cases(9))  
         ultimately obtain sl where 
           lj:"snd (l!j) =  (s', sl) \<and> snd (l!(Suc j)) =  (s', sl)"
           using  cp  l2[of \<Gamma> "fst (l!j)" "snd(l!j)" "fst(l!(Suc j))" "snd(l!(Suc j))"] a00
           using before_k_all_evnt pair_j by fastforce 
         have "(snd(l!k), snd(l!(Suc k))) \<in> G"
           using ss a2 
         proof (cases "k=j")   
           case True                                  
           have "( (s',sl),  (s',sl)) \<in> G" 
             using a4 lj k_basic1  unfolding N_def by fastforce
           thus "(snd (l ! k), snd (l ! Suc k)) \<in> G"
             using pair_j k_basic True ss ssj_normal_s lj by auto
         next
           case False   
           have j_k:"j<k" using  before_k_all_evnt False by fastforce                      
           thus "(snd (l ! k), snd (l ! Suc k)) \<in>  G"
           proof -
             have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce
             have cj:"csj=bdy" using k_basic pair_j ss a0
               by (metis fst_conv option.distinct(1) option.sel stepc_elim_cases(9))                
             moreover have p1:"(s',sl)\<in>p" using lj k_basic1
               by auto 
             moreover then have "cpn n \<Gamma> csj ( (s',sl)) \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
               using a2 com_validityn_def cj by blast
             moreover then have "l!(Suc j) = (csj,  (s',sl))" 
               using  pair_j  lj
               by (metis prod.exhaust_sel)
             ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
               using  j_length a10 a11 \<Gamma>1  ssj_normal_s                     
               by (meson contra_subsetD cpn_assum_induct)                                
             then show ?thesis 
             using a00 a21  \<Gamma>1  j_k j_length 
             cptn_comm_induct[of \<Gamma> l "Call f" s _ "Suc j" G q a F k ]             
             Suc_leI a10' by blast                 
          qed            
       qed 
       } thus ?thesis by (simp add: c_prod cp) qed
       have concr:"(final_glob (last l)  \<longrightarrow> fst (last l) \<notin> Fault ` F \<longrightarrow>
                   ((fst (last l) = Skip \<and>  snd (last l) \<in>  q)) \<or>
                    (fst (last l) = Throw \<and> snd (last l) \<in>  (a)))"
       proof-
       { 
         assume valid:"final_glob (last l)"   and  l_f:"fst (last l) \<notin> Fault ` F"                    
         have "\<exists>k. k\<ge>0 \<and> k<((length l) - 1) \<and> 
                \<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                    (fst (l ! Suc k), toSeq (snd (l ! Suc k))) \<and> final_glob (l!(Suc k))"
         proof -             
           have len_l:"length l > 0" using cp using cptn.simps by blast 
           then obtain a1 l1 where l:"l=a1#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
           have last_l:"last l = l!(length l-1)"
            using last_length [of a1 l1] l by fastforce         
           have final_0:"\<not>final_glob(l!0)" using cp unfolding final_glob_def by auto
           have "0\<le> (length l-1)" using len_l last_l by auto
           moreover have "(length l-1) < length l" using len_l by auto
           moreover have "final_glob (l!(length l-1))" using valid last_l by auto
           moreover have "fst (l!0) = Call f" using cp by auto
           ultimately show ?thesis 
             using  cp final_exist_component_tran_final env_tran_right final_0 
             by blast 
          qed
          then obtain k where a21: "k\<ge>0 \<and> k<((length l) - 1) \<and> 
              \<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                (fst (l ! Suc k), toSeq (snd (l ! Suc k))) \<and> final_glob (l!(Suc k))"
           by auto
          then have a00:"Suc k<length l" by fastforce
                  then obtain j where before_k_all_evnt:
          "j\<le>k \<and>  \<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                       (fst (l ! Suc j), toSeq (snd (l ! Suc j))) \<and> (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
           using a00 a21 exist_first_comp_tran cp by blast
         then obtain cj sj csj ssj where 
             pair_j:"\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                          (fst (l ! Suc j), toSeq (snd (l ! Suc j))) \<and> 
                      cj = fst (l!j) \<and> sj = toSeq(snd (l!j)) \<and>  
                      csj = fst (l!(Suc j)) \<and> ssj = toSeq(snd(l!(Suc j)))"
         by fastforce
       have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce         
          have "((fst (last l) = Skip \<and> 
                    snd (last l) \<in>  q)) \<or>
                    (fst (last l) = Throw \<and> 
                    snd (last l) \<in>  (a))"
          proof -
            have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce                                 
            then have k_basic:"cj = (Call f) \<and> sj \<in>  (fst ` p) \<and> snd (l!j) \<in> (p)" 
              using  pair_j before_k_all_evnt cp env_tran_right a3 assum a00 stability[of p R l 0 j j \<Gamma>]
              by force
            then obtain s' where ss:"sj =  s' \<and> s'\<in> (fst  `p)" by blast 
            moreover have ssj_normal_s:"ssj =  s'" 
              using before_k_all_evnt k_basic pair_j a0 calculation
              by (metis not_None_eq snd_conv stepc_elim_cases(9))
            ultimately obtain sl where 
              lj:"snd (l!j) =  (s', sl) \<and> snd (l!(Suc j)) =  (s', sl)"
              using  cp  l2[of \<Gamma> "fst (l!j)" "snd(l!j)" "fst(l!(Suc j))" "snd(l!(Suc j))"] a00
              using before_k_all_evnt pair_j by fastforce
            have cj:"csj=bdy" using k_basic pair_j ss a0
              by (metis fst_conv option.distinct(1) option.sel stepc_elim_cases(9))                
            moreover have p1:"s'\<in>(fst ` p)" using ss by blast 
            moreover then have "cpn n \<Gamma> csj ( (s', sl)) \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
              using a2 com_validityn_def cj by blast
            moreover then have "l!(Suc j) = (csj,  (s', sl))" 
              using before_k_all_evnt pair_j lj ssj_normal_s
              by (metis prod.exhaust_sel)
            ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
              using  j_length   ssj_normal_s   lj   k_basic \<Gamma>1  a10 a11 cpn_assum_induct 
              by fastforce                            
            thus ?thesis       
              using j_length l_f drop_comm a10' \<Gamma>1 cptn_comm_induct[of \<Gamma> l "Call f" s _ "Suc j" G q a F "Suc j"] valid  
              by blast
           qed
         } thus ?thesis by auto 
         qed
       note res = conjI [OF concl concr]}               
       thus ?thesis using  c_prod unfolding comm_def by force qed      
    } thus ?thesis by auto qed 
  } thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed
           
lemma CallRec_sound:
    "(c, p, R, G, q, a) \<in> Specs \<Longrightarrow>
     \<forall>(c, p, R, G, q, a)\<in>Specs.
       c \<in> dom \<Gamma> \<and>
       Sta p R \<and>  (\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G) \<and>      
       \<Gamma>,\<Theta> \<union> Specs \<turnstile>\<^bsub>/F\<^esub> the (\<Gamma> c) sat [p, R, G, q,a] \<and> 
       (\<forall>x. \<Gamma>,\<Theta> \<union> Specs \<Turnstile>x \<^bsub>/F\<^esub> the (\<Gamma> c) sat [p,R, G, q,a]) \<Longrightarrow>
    Sta p R \<Longrightarrow> (\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G) \<Longrightarrow>
     \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]"
proof -
  assume a0: "(c, p, R, G, q, a) \<in> Specs" and
     a1: 
    "\<forall>(c, p, R, G, q, a)\<in>Specs.
       c \<in> dom \<Gamma> \<and> Sta p R \<and> (\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G) \<and>  
       \<Gamma>,\<Theta> \<union> Specs \<turnstile>\<^bsub>/F\<^esub> the (\<Gamma> c) sat [p, R, G, q,a] \<and> 
       (\<forall>x. \<Gamma>,\<Theta> \<union> Specs \<Turnstile>x \<^bsub>/F\<^esub> the (\<Gamma> c) sat [p,R, G, q,a])"
  then have a1': "c \<in> dom \<Gamma>"  and       
       a1'': "\<Gamma>,\<Theta> \<union> Specs \<Turnstile>n \<^bsub>/F\<^esub> the (\<Gamma> c) sat [p,R, G, q,a]" using a0 by auto 
    from a1 have 
      valid_body:
      "\<forall>(c, p, R, G, q, a)\<in>Specs.
       c \<in> dom \<Gamma> \<and>  Sta p R \<and>   (\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G) \<and>    
       (\<forall>x. \<Gamma>,\<Theta> \<union> Specs \<Turnstile>x \<^bsub>/F\<^esub> the (\<Gamma> c) sat [p,R, G, q,a])" by fastforce
  assume a5: "Sta p R" and
         a6: "(\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G)" 
  obtain bdy where \<Gamma>bdy:"\<Gamma> c = Some bdy" using a1' by auto
  have theta_specs: 
         "\<forall>(c, p, R, G, q, a)\<in>\<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a] \<Longrightarrow>
          \<forall>(c, p, R, G, q, a)\<in>Specs. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]"
  proof(induct n)
    case 0    
    show "\<forall>(c, p, R, G, a, d)\<in>Specs. \<Gamma> \<Turnstile>0\<^bsub>/F\<^esub> LanguageCon.com.Call c sat [p,R, G, a,d]"
    proof-
      {fix c p R G a d
        assume a00:"(c, p, R, G, a, d) \<in> Specs"
        then have "c\<in>dom \<Gamma> \<and> Sta p R" using a1 by auto
        then have " \<Gamma> \<Turnstile>0\<^bsub>/F\<^esub> (LanguageCon.com.Call c) sat [p,R, G, a,d]"
          using not_val_zero  by fastforce
      } then show ?thesis by auto 
    qed       
  next
    case (Suc n)
    have hyp:"\<forall>(c, p, R, G, q, a)\<in>\<Theta>.  \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a] \<Longrightarrow>
             \<forall>(c, p, R, G, q, a)\<in>Specs. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]" by fact
    have body:"\<forall>(c, p, R, G, q, a)\<in>\<Theta>.  \<Gamma> \<Turnstile>Suc n\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]" by fact
    then show ?case
    proof-
      { fix c p R G q a
        assume a000:"(c, p, R, G, q, a) \<in> Specs"
        have ctxt_m:"\<forall>(c, p, R, G, q, a)\<in>\<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]"
          using body  cptn_mod_nest_mono  unfolding com_validityn_def cpn_def
          by (fastforce simp add: cpn_rule)
        then have valid_Proc:"\<forall>(c, p, R, G, q, a)\<in>Specs. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]"
          using hyp by auto
        have Sta:"Sta p R" using a1 a000 by auto
        have c_dom:" c \<in> dom \<Gamma>" using a1 a000 by auto
        have guar:"(\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G)" using a1 a000 by auto
        let ?\<Theta>'= "\<Theta> \<union> Specs"
        from valid_Proc ctxt_m
        have "\<forall>(c, p, R, G, q, a)\<in>?\<Theta>'. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]"
          by fastforce
        with valid_body
        have valid_body_m: 
          "\<forall>(c, p, R, G, q, a)\<in>Specs. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (the (\<Gamma> c)) sat [p,R, G, q,a]"
          by (fastforce  simp:com_cvalidityn_def)    
        then have valid_body:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (the (\<Gamma> c)) sat [p,R, G, q,a]" using a000 by auto
        then have "\<Gamma> \<Turnstile>Suc n\<^bsub>/F\<^esub> Call c sat [p,R, G, q,a]"
        proof-
        { fix l s 
          assume a01:"(\<Gamma>,l)\<in>cpn (Suc n) \<Gamma> (Call c) s \<and> (\<Gamma>,l)\<in> assum(p, R)"
          then have "length l \<ge> 1" unfolding cpn_def using CptnEmpty
            by (metis (no_types, lifting) One_nat_def Product_Type.Collect_case_prodD Suc_leI length_greater_0_conv snd_conv)
          moreover {
            assume a02:"length l = 1"
            then have "l = [(Call c,s)]" 
            proof -
              have "l ! 0 = (LanguageCon.com.Call c, s)" using a01 unfolding cpn_def
                by fastforce
              then show ?thesis using a02
                by (metis One_nat_def Suc_leI impossible_Cons 
                     length_greater_0_conv list.size(3) neq_Nil_conv nth_Cons_0 zero_neq_one) 
            qed 
            then have "(\<Gamma>,l) \<in> comm(G, (q,a)) F" unfolding comm_def final_glob_def by auto
          }
          moreover {assume a02:"length l > 1"
            then obtain a1 ls where l:"l =(Call c, s)#a1#ls" using a01 unfolding cpn_def
              apply auto
              by (metis (no_types, hide_lams) One_nat_def Suc_eq_plus1 less_not_refl list.exhaust list.size(3) list.size(4) not_less_zero nth_Cons_0 prod.collapse)   
            have l_cptn:"(\<Gamma>,l)\<in>cptn" using a01 unfolding cpn_def
              using cptn_eq_cptn_mod_nest by blast
            then obtain m where min_call:"min_call m \<Gamma> l"
              using cptn_eq_cptn_mod_set cptn_mod_cptn_mod_nest minimum_nest_call by blast
            { assume a03:"\<forall>i<length l. fst (l!i) = Call c"     
              then have "(\<Gamma>,l) \<in> comm(G, (q,a)) F" 
                using no_comp_tran_no_final_comm[OF _ a03] a02 unfolding final_glob_def
                by fastforce 
            }                                     
            moreover{
              assume a03:"\<not>(\<forall>i<length l. fst (l!i) = Call c)"
              then obtain i where i:"(i<length l \<and> fst (l!i) \<noteq> Call c)"
                by auto
              then obtain j where cfg_j:"fst (l!j) \<noteq> Call c \<and> (\<forall>k<j. fst (l!k) = Call c)"                     
                by (fast dest: exists_first_occ[of "\<lambda>i. fst (l!i) \<noteq> Call c" i])
              moreover have j:"j>0 \<and> j<length l" using l i calculation
                by (metis (no_types) cfg_j fst_conv i l le_less_trans neq0_conv not_le_imp_less nth_Cons_0)
              ultimately have step:" (\<Gamma>\<turnstile>\<^sub>c (fst (l ! (j-1)), toSeq (snd (l ! (j-1)))) \<rightarrow> 
                    (fst (l! j), toSeq (snd (l ! j))) )"
                using l l_cptn cptn_stepc_rtran not_eq_not_env  step_ce_dest
                by (metis (no_types, lifting) One_nat_def Suc_diff_Suc diff_less diff_zero prod.exhaust_sel zero_less_one)
              moreover obtain s' where j_1_cfg:"snd (l!(j-1)) =  s' \<and> s' \<in> p"
                using cfg_j l a01[simplified l] j[simplified l] i Sta events_p[OF l_cptn[simplified l] _ _ _ Sta, of "j-1"]
                by fastforce
              then have j_cfg:"(fst (l! j), toSeq (snd (l ! j)))  = (the (\<Gamma> c),  (fst s'))"
                using cfg_j a0 l l_cptn 
                 stepc_elim_cases(9)[of \<Gamma> "c" "fst s'" "(fst (l! j),toSeq (snd (l!j)))"] 
                 calculation j
                by (metis c_dom diff_less domIff option.sel toSeq.simps(1) zero_less_one)  
              then have j_cfg_1:"l!j = (the (\<Gamma> c), s')" using l2[OF step l_cptn _ _ ]
                by (metis Suc_diff_1 eq_snd_iff fst_conv j j_1_cfg toSeq.simps(1))
              then have suc_n_call:"(Suc n,\<Gamma>, drop (j-1) l) \<in> cptn_mod_nest_call" 
                using a01 unfolding cpn_def
                by (simp add: dropcptn_is_cptn1 j less_imp_diff_less)
              have "(n,\<Gamma>, drop j l) \<in> cptn_mod_nest_call" 
              proof-
                have "\<not> (\<Gamma>\<turnstile>\<^sub>c (l!(j-1)) \<rightarrow>\<^sub>e (l!j))" using step
                  by (metis cfg_j diff_less env_c_c' j prod.exhaust_sel zero_less_one)
                then have "(Suc n,\<Gamma>, (Call c,  s')#(the (\<Gamma> c), s')#(drop (j+1) l)) \<in> cptn_mod_nest_call"
                  using a01 j step cfg_j j_cfg j_1_cfg  suc_n_call j_cfg_1                 
                  by (metis (no_types, lifting) Cons_nth_drop_Suc One_nat_def Suc_eq_plus1 
                    Suc_less_eq Suc_pred diff_less less_SucI prod.collapse zero_less_one)                  
                then have "(n,\<Gamma>, (the (\<Gamma> c), s')#(drop (j+1) l)) \<in> cptn_mod_nest_call"
                  using cfg_j j_cfg  elim_cptn_mod_nest_call_n_dec[of "Suc n" \<Gamma> c s'] c_dom by fastforce
                then show ?thesis
                  by (metis Cons_nth_drop_Suc Suc_eq_plus1 j j_cfg_1)
              qed
              moreover have "(\<Gamma>, drop j l) \<in> assum(p,R)" 
              proof-   
                have "(\<Gamma>, take j l @ l ! j # drop (Suc j) l) \<in> assum (p, R)"
                  using conjunct2[OF a01] id_take_nth_drop[OF conjunct2[OF j]] by auto                             
                then show ?thesis 
                  using sub_assum_r[of \<Gamma> "take j l" "l!j"]  j_1_cfg l  j j_cfg_1 
                  by (metis Int_iff a01 cpn_assum_induct)                  
              qed                              
              ultimately have comm_drop:"(\<Gamma>, drop j l)\<in> comm(G, (q,a)) F"
                using valid_body j_cfg_1 j unfolding com_validityn_def cpn_def 
                by fastforce
              have "(\<Gamma>,l) \<in> comm(G, (q,a)) F" 
              proof-
                have h:"\<forall>j<length (take j l). fst ((take j l)!j) = (Call c)" using j cfg_j by fastforce
                then have comm_take:"(\<Gamma>,take j l) \<in> comm(G, (q,a)) F"
                  using no_comp_tran_no_final_comm[of "take j l" "Call c"] j_1_cfg l j_cfg j cfg_j 
                  unfolding final_glob_def by auto                
                moreover have "(snd (last (take j l)), snd (drop j l ! 0)) \<in> G"
                proof-
                  have "length (take j l) = j"using l j_1_cfg j j_cfg by auto
                  moreover have "(take j l)!(j-1) = l!(j-1)"
                    using l j_1_cfg j j_cfg by auto
                  ultimately have "last (take j l) = l!(j-1)"
                    using  j by (metis last_conv_nth less_numeral_extra(3) list.size(3))
                  moreover have "(s',s')\<in>G" using l j_1_cfg j j_cfg_1 guar unfolding N_def
                    by blast
                  ultimately  show ?thesis using l j_1_cfg j j_cfg_1 
                    by simp
                qed                                 
                ultimately show ?thesis using  j_1_cfg j_cfg j cfg_j j l_cptn
                  comm_union[OF comm_take comm_drop] by fastforce
              qed                 
             } ultimately have "(\<Gamma>,l)\<in>comm(G, (q,a)) F" by auto
           }ultimately  have "(\<Gamma>,l)\<in>comm(G, (q,a)) F" by fastforce         
         } thus ?thesis unfolding com_validityn_def using cpn_rule2 by blast 
       qed
      } thus ?case by fastforce
    qed
  qed 
  then show ?thesis using a0 unfolding com_cvalidityn_def by auto     
qed

lemma Seq_env_P:assumes a0:"\<Gamma>\<turnstile>\<^sub>c(Seq P Q,s) \<rightarrow>\<^sub>e (Seq P Q,t)"
      shows "\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow>\<^sub>e (P,t)"
using a0 
  by (metis env_intro_diff_p)

lemma map_eq_state:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Seq c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) " and
  a2:"l1=map (lift c2) l2"
shows
  "\<forall>i<length l1. snd (l1!i) = snd (l2!i)"
using a0 a1 a2 unfolding cp_def
by (simp add: snd_lift) 

lemma map_eq_seq_c:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Seq c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) " and
  a2:"l1=map (lift c2) l2"
shows
  "\<forall>i<length l1. fst (l1!i) = Seq (fst (l2!i)) c2"
proof -
  {fix i
  assume a3:"i<length l1"
  have "fst (l1!i) = Seq (fst (l2!i)) c2"
  using a0 a1 a2 a3 unfolding lift_def
    by (simp add: case_prod_unfold) 
  }thus ?thesis by auto
qed 


lemma same_env_seq_c:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Seq c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) " and
  a2:"l1=map (lift c2) l2"
shows
"\<forall>i. Suc i<length l2 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l2!i)  \<rightarrow>\<^sub>e (l2!(Suc i)) = 
            \<Gamma>\<turnstile>\<^sub>c(l1!i)  \<rightarrow>\<^sub>e (l1!(Suc i))" 
proof -
  have a0a:"(\<Gamma>,l1) \<in>cptn \<and> l1!0 = ((Seq c1 c2),s)" 
    using a0 unfolding cp_def by blast
  have a1a: "(\<Gamma>,l2) \<in>cptn \<and> l2!0 = (c1,s)"
    using a1 unfolding cp_def by blast
  {
    fix i
    assume a3:"Suc i< length l2"
    have "\<Gamma>\<turnstile>\<^sub>c(l2!i)  \<rightarrow>\<^sub>e (l2!(Suc i)) = 
            \<Gamma>\<turnstile>\<^sub>c(l1!i)  \<rightarrow>\<^sub>e (l1!(Suc i))"
    proof
    {
      assume a4:"\<Gamma>\<turnstile>\<^sub>c l2 ! i \<rightarrow>\<^sub>e l2 ! Suc i"
      obtain c1i s1i c1si s1si where l1prod:"(l1 ! i)=(c1i,s1i) \<and> (l1!Suc i) = (c1si,s1si)"        
        by (meson prod.exhaust_sel)
      obtain c2i s2i c2si s2si where l2prod:"l2 ! i=(c2i,s2i) \<and> l2!Suc i = (c2si,s2si)"
        by (meson prod.exhaust_sel)
      then have "c1i = (Seq c2i c2) \<and> c1si = (Seq c2si c2)"
        using  a0 a1 a2 a3 a4  map_eq_seq_c l1prod
        by (metis Suc_lessD  fst_conv length_map)
      also have "s2i=s1i \<and> s2si=s1si"
        using  a0 a1 a4  a2 a3 l2prod  l1prod
        by (metis Suc_lessD  nth_map snd_conv snd_lift)        
      ultimately show "\<Gamma>\<turnstile>\<^sub>c l1 ! i \<rightarrow>\<^sub>e (l1 ! Suc i)" 
        using a4 l1prod l2prod env_c_c'
        by (metis env_intro_diff_p)
    } 
    { thm prod.exhaust_sel
      assume a4:"\<Gamma>\<turnstile>\<^sub>c l1 ! i \<rightarrow>\<^sub>e l1 ! Suc i"
      obtain c1i s1i c1si s1si where l1prod:"l1 ! i=(c1i,s1i) \<and> l1!Suc i = (c1si,s1si)"
         by (meson prod.exhaust_sel)
      obtain c2i s2i c2si s2si where l2prod:"l2 ! i=(c2i,s2i) \<and> l2!Suc i = (c2si,s2si)"
         by (meson prod.exhaust_sel)
      then have "c1i = (Seq c2i c2) \<and> c1si = (Seq c2si c2)"
        using  a0 a1 a2 a3 a4  map_eq_seq_c l1prod
        by (metis Suc_lessD  fst_conv length_map)
      also have "s2i=s1i \<and> s2si=s1si"
        using  a0 a1 a4  a2 a3 l2prod l1prod
        by (metis Suc_lessD  nth_map snd_conv snd_lift)        
      ultimately show "\<Gamma>\<turnstile>\<^sub>c l2 ! i \<rightarrow>\<^sub>e (l2 ! Suc i)" 
        using a4 l1prod l2prod env_c_c'
        by (metis LanguageCon.com.inject(3) env_intro_diff_p)           
    }
    qed
   } 
  thus ?thesis by auto
qed



lemma same_comp_seq_c:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Seq c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) " and
  a2:"l1=map (lift c2) l2"
shows
"\<forall>i. Suc i<length l2 \<longrightarrow> 
        \<Gamma>\<turnstile>\<^sub>c (fst (l2 ! i), toSeq (snd (l2 ! i))) \<rightarrow> 
            (fst (l2 ! Suc i), toSeq (snd (l2 ! Suc i)))  = 
      \<Gamma>\<turnstile>\<^sub>c (fst (l1 ! i), toSeq (snd (l1 ! i))) \<rightarrow> 
            (fst (l1 ! Suc i), toSeq (snd (l1 ! Suc i)))" 
proof -
  have a0a:"(\<Gamma>,l1) \<in>cptn \<and> l1!0 = ((Seq c1 c2),s)" 
    using a0 unfolding cp_def by blast
  have a1a: "(\<Gamma>,l2) \<in>cptn \<and> l2!0 = (c1,s)"
    using a1 unfolding cp_def by blast
  {
    fix i
    assume a3:"Suc i< length l2"
    have "\<Gamma>\<turnstile>\<^sub>c (fst (l1 ! i), toSeq (snd (l1 ! i))) \<rightarrow> 
            (fst (l1 ! Suc i), toSeq (snd (l1 ! Suc i))) =
       \<Gamma>\<turnstile>\<^sub>c (fst (l2 ! i), toSeq (snd (l2 ! i))) \<rightarrow> 
            (fst (l2 ! Suc i), toSeq (snd (l2 ! Suc i)))"
    proof
    {
      assume a4:"\<Gamma>\<turnstile>\<^sub>c (fst (l2 ! i), toSeq (snd (l2 ! i))) \<rightarrow> 
                (fst (l2 ! Suc i), toSeq (snd (l2 ! Suc i)))"
      obtain c1i s1i c1si s1si where l1prod:"l1 ! i=(c1i,s1i) \<and> l1!Suc i = (c1si,s1si)"
        by (meson prod.exhaust_sel)
      obtain c2i s2i c2si s2si where l2prod:"l2 ! i=(c2i,s2i) \<and> l2!Suc i = (c2si,s2si)"
        by (meson prod.exhaust_sel)
      then have "c1i = (Seq c2i c2) \<and> c1si = (Seq c2si c2)"
        using  a0 a1 a2 a3 a4  map_eq_seq_c l1prod
        by (metis Suc_lessD  fst_conv length_map)
      also have "s2i=s1i \<and> s2si=s1si"
        using  a0 a1 a4  a2 a3 l2prod  l1prod
        by (metis Suc_lessD  nth_map snd_conv snd_lift)        
      ultimately show "\<Gamma>\<turnstile>\<^sub>c (fst (l1 ! i), toSeq (snd (l1 ! i))) \<rightarrow> 
            (fst (l1 ! Suc i), toSeq (snd (l1 ! Suc i)))" 
        using a4 l1prod l2prod
        by (simp add: Seqc)        
    } 
    {
      assume a4:"\<Gamma>\<turnstile>\<^sub>c (fst (l1 ! i), toSeq (snd (l1 ! i))) \<rightarrow> 
            (fst (l1 ! Suc i), toSeq (snd (l1 ! Suc i)))"
      obtain c1i s1i c1si s1si where l1prod:"l1 ! i=(c1i,s1i) \<and> l1!Suc i = (c1si,s1si)"
         by (meson prod.exhaust_sel)
      obtain c2i s2i c2si s2si where l2prod:"l2 ! i=(c2i,s2i) \<and> l2!Suc i = (c2si,s2si)"
         by (meson prod.exhaust_sel)
      then have "c1i = (Seq c2i c2) \<and> c1si = (Seq c2si c2)"
        using  a0 a1 a2 a3 a4  map_eq_seq_c l1prod
        by (metis Suc_lessD  fst_conv length_map)
      also have "s2i=s1i \<and> s2si=s1si"
        using  a0 a1 a4  a2 a3 l2prod  l1prod
        by (metis Suc_lessD  nth_map snd_conv snd_lift)        
      ultimately show "\<Gamma>\<turnstile>\<^sub>c (fst (l2 ! i), toSeq (snd (l2 ! i))) \<rightarrow> 
                (fst (l2 ! Suc i), toSeq (snd (l2 ! Suc i)))"
        using a4 l1prod l2prod stepc_elim_cases_Seq_Seq
      by auto           
    }
    qed
   } 
  thus ?thesis by auto
qed

lemma assum_map:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Seq c1 c2) s) \<and> ((\<Gamma>,l1) \<in> assum(p, R))" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) " and
  a2:"l1=map (lift c2) l2"  
shows
  "((\<Gamma>,l2) \<in> assum(p, R))"
proof -
  have a3: "\<forall>i. Suc i<length l2 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l2!i)  \<rightarrow>\<^sub>e (l2!(Suc i)) = 
            \<Gamma>\<turnstile>\<^sub>c(l1!i)  \<rightarrow>\<^sub>e (l1!(Suc i))" 
    using a0 a1 a2 same_env_seq_c by fastforce
  have pair_\<Gamma>l1:"fst (\<Gamma>,l1) = \<Gamma> \<and> snd (\<Gamma>,l1) = l1" by fastforce
  have pair_\<Gamma>l2:"fst (\<Gamma>,l2) = \<Gamma> \<and> snd (\<Gamma>,l2) = l2" by fastforce
  have drop_k_s:"l2!0 = (c1,s)" using a1 cp_def by blast
  have eq_length:"length l1 = length l2" using a2 by auto  
  then have p1:"s\<in>p" using a0 unfolding cp_def assum_def by fastforce  
  show ?thesis 
  proof -    
    let ?c= "(\<Gamma>,l2)"
    have l:"snd((snd ?c!0)) \<in> (p)"
     using p1 drop_k_s a1  unfolding cp_def by auto
    {fix i
     assume a00:"Suc i<length (snd ?c)" 
     assume a11:"(fst ?c)\<turnstile>\<^sub>c((snd ?c)!i)  \<rightarrow>\<^sub>e ((snd ?c)!(Suc i))"
     have "(snd((snd ?c)!i), snd((snd ?c)!(Suc i))) \<in> R"
     using a0 a1 a2 a3 map_eq_state[OF conjunct1[OF a0]] unfolding assum_def 
     using a00 a11 eq_length by fastforce
    } thus "(\<Gamma>, l2) \<in> assum (p, R)" 
      using l unfolding assum_def by fastforce  
  qed  
qed

lemma comm_map':
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Seq c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) \<and> (\<Gamma>, l2)\<in> comm(G, (q,a)) F" and
  a2:"l1=map (lift c2) l2" 
shows
  "(Suc k < length l1 \<longrightarrow>
       \<Gamma>\<turnstile>\<^sub>c (fst (l1 ! k), toSeq (snd (l1 ! k))) \<rightarrow> 
                (fst (l1 ! Suc k), toSeq (snd (l1 ! Suc k))) \<longrightarrow> 
       (snd(l1!k), snd(l1!(Suc k))) \<in>  G) \<and> 
   (fst (last l1) = (Seq c c2) \<and> final_glob (c, snd (last l1)) \<longrightarrow>  
       c \<notin> Fault ` F  \<longrightarrow>   
      (fst (last l1) = (Seq Skip c2) \<and> (snd (last  l1) \<in> q) \<or>
      (fst (last l1) = (Seq Throw c2) \<and> snd (last l1) \<in>  (a))))
     "
proof -
  have a3:"\<forall>i. Suc i<length l2 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c (fst (l2 ! i), toSeq (snd (l2 ! i))) \<rightarrow> 
                (fst (l2 ! Suc i), toSeq (snd (l2 ! Suc i))) = 
            \<Gamma>\<turnstile>\<^sub>c (fst (l1 ! i), toSeq (snd (l1 ! i))) \<rightarrow> 
                (fst (l1 ! Suc i), toSeq (snd (l1 ! Suc i)))" 
    using a0 a1 a2 same_comp_seq_c
    by fastforce
  have pair_\<Gamma>l1:"fst (\<Gamma>,l1) = \<Gamma> \<and> snd (\<Gamma>,l1) = l1" by fastforce
  have pair_\<Gamma>l2:"fst (\<Gamma>,l2) = \<Gamma> \<and> snd (\<Gamma>,l2) = l2" by fastforce
  have drop_k_s:"l2!0 = (c1,s)" using a1 cp_def by blast
  have eq_length:"length l1 = length l2" using a2 by auto 
  then have len0:"length l1>0" using a0 unfolding cp_def 
    using Collect_case_prodD drop_k_s eq_length by auto
  then have l1_not_empty:"l1\<noteq>[]" by auto
  then have l2_not_empty:"l2 \<noteq> []" using a2 by blast       
   have last_lenl1:"last l1 = l1!((length l1) -1)" 
        using last_conv_nth l1_not_empty by auto
  have last_lenl2:"last l2 = l2!((length l2) -1)" 
       using last_conv_nth l2_not_empty by auto 
  have a03:"(\<forall>i ns ns'.                 
               Suc i<length (snd (\<Gamma>, l2)) \<longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c (fst (l2 ! i), toSeq (snd (l2 ! i))) \<rightarrow> 
                (fst (l2 ! Suc i), toSeq (snd (l2 ! Suc i))) \<longrightarrow>                               
                 (snd((snd (\<Gamma>, l2))!i), snd((snd (\<Gamma>, l2))!(Suc i))) \<in> G) \<and> 
               (final_glob (last (snd (\<Gamma>, l2)))  \<longrightarrow>   fst (last l2) \<notin> Fault ` F  \<longrightarrow>              
                  ((fst (last (snd (\<Gamma>, l2))) = Skip \<and> snd (last (snd (\<Gamma>, l2))) \<in> q)) \<or>
                  (fst (last (snd (\<Gamma>, l2))) = Throw \<and> snd (last (snd (\<Gamma>, l2))) \<in>  (a)))"
  using a1 unfolding comm_def by fastforce
  show ?thesis unfolding comm_def 
  proof -
  { fix k ns ns'    
    assume a00:"Suc k < length l1"    
    then have "k \<le> length l1" using a2 by fastforce    
    have a00:"Suc k < length l2" using eq_length a00 by fastforce
    
    then have " \<Gamma>\<turnstile>\<^sub>c (fst (l1 ! k), toSeq (snd (l1 ! k))) \<rightarrow> 
                (fst (l1 ! Suc k), toSeq (snd (l1 ! Suc k))) \<longrightarrow>       
      (snd((snd (\<Gamma>, l1))!k), snd((snd (\<Gamma>, l1))!(Suc k))) \<in>  G"
    using  pair_\<Gamma>l1 pair_\<Gamma>l2 a00  a03 a3  eq_length 
     by (metis Suc_lessD a0 a1 a2 map_eq_state)
  } note l=this
  {
    assume a00: "fst (last l1) = (Seq c c2) \<and> final_glob (c, snd (last l1))" and
           a01:"c \<notin> Fault ` F "
    then have c:"c=Skip \<or> c = Throw \<or> c = Stuck \<or> (\<exists>f. c = Fault f)"
     unfolding final_glob_def by auto    
    then have fst_last_l2:"fst (last l2) = c"                               
      using  last_lenl1 a00 l1_not_empty eq_length len0 a2 last_conv_nth last_lift 
      by fastforce      
    also have last_eq:"snd (last l2) = snd (last l1)"      
      using l2_not_empty a2 last_conv_nth last_lenl1 last_snd 
      by fastforce
    ultimately have "final_glob (fst (last l2),snd (last l2))" 
     using a00 by auto
    then have "final_glob (last l2)" by auto
    also have "fst (last (l2)) \<notin> Fault ` F"
       using  last_eq a01
       using fst_last_l2 by blast
    ultimately have "(fst (last  l2)) = Skip \<and> snd (last  l2) \<in>  q \<or>
                  (fst (last l2) = Throw \<and> snd (last l2) \<in>  (a))"
    using a03 by auto
    then have "(fst (last l1) = (Seq Skip c2) \<and> snd (last  l1) \<in>  q) \<or>
                  (fst (last l1) = (Seq Throw c2) \<and> 
                    snd (last l1) \<in> (a))"
    using last_eq fst_last_l2 a00 by force
  }
  thus ?thesis using l by auto qed
qed

lemma comm_map'':
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Seq c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) \<and> (\<Gamma>, l2)\<in> comm(G, (q,a)) F" and
  a2:"l1=map (lift c2) l2" 
shows
  "((Suc k < length l1 \<longrightarrow>
       \<Gamma>\<turnstile>\<^sub>c (fst (l1 ! k), toSeq (snd (l1 ! k))) \<rightarrow> 
            (fst (l1 ! Suc k), toSeq (snd (l1 ! Suc k))) \<longrightarrow>        
       (snd(l1!k), snd(l1!(Suc k))) \<in> G) \<and> 
   (final_glob (last l1) \<longrightarrow>  fst (last l1)  \<notin> Fault ` F \<longrightarrow>  
      (fst (last l1) = Skip \<and> (snd (last  l1) \<in>  r) \<or>
      (fst (last l1) = Throw \<and>  snd (last l1) \<in>  (a)))))
     "
proof -
  have a3:"\<forall>i. Suc i<length l2 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c (fst (l2 ! i), toSeq (snd (l2 ! i))) \<rightarrow> 
                (fst (l2 ! Suc i), toSeq (snd (l2 ! Suc i))) = 
            \<Gamma>\<turnstile>\<^sub>c (fst (l1 ! i), toSeq (snd (l1 ! i))) \<rightarrow> 
                (fst (l1 ! Suc i), toSeq (snd (l1 ! Suc i)))" 
    using a0 a1 a2 same_comp_seq_c
    by fastforce
  have pair_\<Gamma>l1:"fst (\<Gamma>,l1) = \<Gamma> \<and> snd (\<Gamma>,l1) = l1" by fastforce
  have pair_\<Gamma>l2:"fst (\<Gamma>,l2) = \<Gamma> \<and> snd (\<Gamma>,l2) = l2" by fastforce
  have drop_k_s:"l2!0 = (c1,s)" using a1 cp_def by blast
  have eq_length:"length l1 = length l2" using a2 by auto 
  then have len0:"length l1>0" using a0 unfolding cp_def 
    using Collect_case_prodD drop_k_s eq_length by auto
  then have l1_not_empty:"l1\<noteq>[]" by auto
  then have l2_not_empty:"l2 \<noteq> []" using a2 by blast       
  have last_lenl1:"last l1 = l1!((length l1) -1)" 
        using last_conv_nth l1_not_empty by auto
  have last_lenl2:"last l2 = l2!((length l2) -1)" 
       using last_conv_nth l2_not_empty by auto 
  have a03:"(\<forall>i ns ns'.                 
               Suc i<length (snd (\<Gamma>, l2)) \<longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c (fst (l2 ! i), toSeq (snd (l2 ! i))) \<rightarrow> 
                (fst (l2 ! Suc i), toSeq (snd (l2 ! Suc i))) \<longrightarrow>                               
                 (snd((snd (\<Gamma>, l2))!i), snd((snd (\<Gamma>, l2))!(Suc i))) \<in> G) \<and> 
               (final_glob (last (snd (\<Gamma>, l2)))  \<longrightarrow>  fst (last l2) \<notin> Fault ` F  \<longrightarrow>               
                  ((fst (last (snd (\<Gamma>, l2))) = Skip \<and> snd (last (snd (\<Gamma>, l2))) \<in>  q)) \<or>
                  (fst (last (snd (\<Gamma>, l2))) = Throw \<and> snd (last (snd (\<Gamma>, l2))) \<in>  (a)))"
  using a1 unfolding comm_def by fastforce
  show ?thesis unfolding comm_def 
  proof -
  { fix k ns ns'    
    assume a00:"Suc k < length l1"    
    then have "k \<le> length l1" using a2 by fastforce    
    have a00:"Suc k < length l2" using eq_length a00 by fastforce   
    then have " \<Gamma>\<turnstile>\<^sub>c (fst (l1 ! k), toSeq (snd (l1 ! k))) \<rightarrow> 
                (fst (l1 ! Suc k), toSeq (snd (l1 ! Suc k))) \<longrightarrow>         
        (snd((snd (\<Gamma>, l1))!k), snd((snd (\<Gamma>, l1))!(Suc k))) \<in> G"
       using  pair_\<Gamma>l1 pair_\<Gamma>l2 a00  a03 a3  eq_length 
      by (metis (no_types,lifting) a2 Suc_lessD nth_map snd_lift)
    } note l= this
    {
     assume a00: "final_glob (last l1)"           
     then have c:"fst (last l1)=Skip \<or> fst (last l1) = Throw \<or> 
                  fst (last l1) = Stuck \<or> (\<exists>f. fst (last l1) =Fault f)"
       unfolding final_glob_def by auto 
     moreover have "fst (last l1) = Seq (fst (last l2)) c2" 
       using a2 last_lenl1 eq_length
      proof -
        have "last l2 = l2 ! (length l2 - 1)"
          using l2_not_empty last_conv_nth by blast
        then show ?thesis
          by (metis One_nat_def a2 l2_not_empty last_lenl1 last_lift)
      qed
      ultimately have False by simp  
    } thus ?thesis using l  by auto qed
qed

lemma comm_map:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Seq c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) \<and> (\<Gamma>, l2)\<in> comm(G, (q,a)) F" and
  a2:"l1=map (lift c2) l2" 
shows
  "(\<Gamma>, l1)\<in> comm(G, (r,a)) F"
proof - 
  {fix i 
    have "(Suc i < length (l1) \<longrightarrow>
         \<Gamma>\<turnstile>\<^sub>c (fst (l1 ! i), toSeq (snd (l1 ! i))) \<rightarrow> 
             (fst (l1 ! Suc i), toSeq (snd (l1 ! Suc i))) \<longrightarrow>       
        (snd (l1 ! i), snd (l1 ! Suc i)) \<in> G) \<and>
        (final_glob (last l1) \<longrightarrow>  fst (last l1) \<notin> Fault ` F  \<longrightarrow>                
                   fst (last l1) = LanguageCon.com.Skip \<and>
                   snd (last l1) \<in>  r \<or>
                   fst (last l1) = LanguageCon.com.Throw \<and>
                   snd (last l1) \<in>  a) "
      using comm_map''[of \<Gamma> l1 c1 c2 s l2 G q a ] a0 a1 a2 
      by fastforce
   }  then show ?thesis using comm_def unfolding comm_def by fastforce       
qed
(* declare[[show_types]]
lemma "(SOME e. e\<in>{1::nat,2,3}) = 1 \<or> (SOME e. e\<in>{1::nat,2,3}) = 2 \<or> (SOME e. e\<in>{1::nat,2,3}) = 3"
  apply auto
  by (metis (mono_tags, lifting) someI)*)


lemma Seq_sound1:
assumes
  a0:"(n,\<Gamma>,x)\<in>cptn_mod_nest_call" and
  a1:"x!0 = ((Seq P Q),s)" and
  a2:"\<forall>i<length x. fst (x!i)\<noteq> Q" and
  a3:"\<not> final_glob (last x)" and
  a4:"env_tran_right \<Gamma> x rely" and
  a5:"snd (x!0)\<in>  p \<and> Sta p rely \<and> Sta a rely " and 
  a6: "\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> P sat [p, rely, G, q,a]" 
shows
  "\<exists>xs. (\<Gamma>,xs) \<in> cpn n \<Gamma> P s \<and> x = map (lift Q) xs"
using a0 a1 a2 a3 a4  a5 a6
proof (induct arbitrary: P s p) 
  case (CptnModNestOne n \<Gamma> C s1)
  then have "(\<Gamma>, [(P,s)]) \<in> cpn n \<Gamma> P s \<and> [(C, s1)] = map (lift Q) [(P,s)]"
    unfolding cpn_def lift_def
    by (simp add: cptn_mod_nest_call.CptnModNestOne) 
  thus ?case by fastforce
next
  case (CptnModNestEnv \<Gamma> C s1 t1 n xsa)
  then have C:"C=Seq P Q" unfolding lift_def by fastforce
  have "\<exists>xs. (\<Gamma>, xs) \<in> cpn n \<Gamma> P t1 \<and> (C, t1) # xsa = map (lift Q) xs"
  proof -
     have "((C, t1) # xsa) ! 0 = (LanguageCon.com.Seq P Q, t1)" using C by auto
     moreover have "\<forall>i<length ((C, t1) # xsa). fst (((C, t1) # xsa) ! i) \<noteq> Q"
       using CptnModNestEnv(5) by fastforce
     moreover have "\<not> final_glob (last ((C, t1) # xsa))" using CptnModNestEnv(6) 
       by fastforce
     moreover have "snd (((C, t1) # xsa) ! 0) \<in> p" 
       using CptnModNestEnv(8) CptnModNestEnv(1) CptnModNestEnv(7)
       unfolding env_tran_right_def Sta_def
       by (metis Suc_less_eq length_Cons nth_Cons_0 nth_Cons_Suc zero_less_Suc) 
     ultimately show ?thesis
       using CptnModNestEnv(3) CptnModNestEnv(7) CptnModNestEnv(8)  CptnModNestEnv(9) env_tran_tail by blast
  qed 
  then obtain xs where hi:"(\<Gamma>, xs) \<in> cpn n \<Gamma> P t1 \<and> (C, t1) # xsa = map (lift Q) xs"
    by fastforce
  have s1_s:"s1=s" using  CptnModNestEnv unfolding cpn_def by auto
  obtain xsa' where xs:"xs=((P,t1)#xsa') \<and> (n, \<Gamma>,((P,t1)#xsa'))\<in>cptn_mod_nest_call \<and> (C, t1) # xsa = map (lift Q) ((P,t1)#xsa')" 
    using hi  unfolding cpn_def by fastforce  
  have env_tran:"\<Gamma>\<turnstile>\<^sub>c(P,s1) \<rightarrow>\<^sub>e (P,t1)" using CptnModNestEnv Seq_env_P by (metis fst_conv nth_Cons_0)  
  then have "(n, \<Gamma>,(P,s1)#(P,t1)#xsa')\<in>cptn_mod_nest_call" 
    using xs env_tran cptn_mod_nest_call.CptnModNestEnv by fastforce  
  then have "(\<Gamma>,(P,s1)#(P,t1)#xsa') \<in> cpn n \<Gamma> P s" 
    using cpn_def s1_s by fastforce
  moreover have "(C,s1)#(C, t1) # xsa = map (lift Q) ((P,s1)#(P,t1)#xsa')"
    using xs C unfolding lift_def by fastforce
  ultimately show ?case by auto
next
  case (CptnModNestSkip)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModNestThrow)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModNestStuck)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next 
  case (CptnModNestFault)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModNestSeq1 n \<Gamma> P0 sa xsa zs P1)
  then have a1:"LanguageCon.com.Seq P Q = LanguageCon.com.Seq P0 P1"
    by fastforce  
  have f1: "sa = s"
    using CptnModNestSeq1.prems(1) by force
  have f2: "P = P0 \<and> Q = P1" using a1 by auto  
  hence "(\<Gamma>, (P0, sa) # xsa) \<in> cpn n \<Gamma> P s"
    using f2 f1 CptnModNestSeq1.hyps(1) by (simp add: cpn_def)
  thus ?case
    using Cons_lift CptnModNestSeq1.hyps(3) a1 by fastforce   
next
  case (CptnModNestSeq2 n \<Gamma> P0 sa xsa P1 ys zs) 
  then have "P0 = P \<and> P1 = Q" by auto
  then obtain i where zs:"fst (zs!i) = Q \<and> (i< (length zs))" using CptnModNestSeq2
    by (metis (no_types, lifting) add_diff_cancel_left' fst_conv length_Cons length_append nth_append_length zero_less_Suc zero_less_diff)    
  then have "Suc i< length ((Seq P0 P1,sa)#zs)" by fastforce
  then have "fst (((Seq P0 P1, sa) # zs)!Suc i) = Q" using zs by fastforce    
  thus ?case using CptnModNestSeq2(8) zs by auto
next
  case (CptnModNestSeq3 n \<Gamma> P1 sa xsa c f s' ys zs Q1 )          
  have "final_glob (last ((c,  s')# ys))"
  proof -
    have cptn_mod:"(n, \<Gamma>, (c,  s') # ys) \<in> cptn_mod_nest_call" 
      using CptnModNestSeq3(5)
      using CptnModNestSeq3.hyps(6) by blast
    then have cptn:"(\<Gamma>, (c,  s') # ys) \<in> cptn"
      using cptn_eq_cptn_mod_nest by auto
    moreover have throw_0:"((c,  s') # ys)!0 = (c,  s') \<and> 0 < length((c,  s') # ys)"
      by force         
    moreover have last:"last ((c,  s') # ys) = ((c,  s') # ys)!((length ((c,  s') # ys)) - 1)"
      using last_conv_nth by auto
    moreover have env_tran:"env_tran_right \<Gamma> ((c,  s') # ys) rely" 
      using  CptnModNestSeq3(12)  CptnModNestSeq3(8) env_tran_subl env_tran_tail  by blast           
    ultimately obtain st' where "fst (last ((c,  s') # ys)) = c \<and>        
                     snd (last ((c,  s') # ys)) =  st'"               
      using term_all_skip[OF cptn _ ]  CptnModNestSeq3.hyps(4) by fastforce      
    thus ?thesis  unfolding final_glob_def using CptnModNestSeq3.hyps(4) by blast
  qed
  thus ?case 
    using CptnModNestSeq3.hyps(8) CptnModNestSeq3.prems(3) by fastforce
qed (auto)

lemma Seq_sound2: 
assumes
  a0:"(\<Gamma>,x)\<in>cptn_mod" and
  a1:"x!0 = ((Seq P Q),s)" and
  a2:"\<forall>i<length x. fst (x!i)\<noteq> Q" and
  a3:"fst (last x) = c \<and> (c =  Throw \<or> c = Stuck \<or> (\<exists>f. c = Fault f) )" and
  a4:"env_tran_right \<Gamma> x rely"
shows
  "\<exists>xs s' ys. (\<Gamma>,xs) \<in> cp \<Gamma> P s \<and> x = ((map (lift Q) xs)@((c, s')#ys))"
using a0 a1 a2 a3 a4
proof (induct arbitrary: P s )
  case (CptnModOne \<Gamma> C s1)
  thus ?case
    by auto
next
  case (CptnModEnv \<Gamma> C s1 t1 xsa)
  then have C:"C=Seq P Q" unfolding lift_def by fastforce
  have "\<exists>xs s' ys. (\<Gamma>, xs) \<in> cp \<Gamma> P t1 \<and> (C, t1) # xsa = map (lift Q) xs@((c,  s')#ys)"
  proof -
     have "((C, t1) # xsa) ! 0 = (LanguageCon.com.Seq P Q, t1)" using C by auto
     moreover have "\<forall>i<length ((C, t1) # xsa). fst (((C, t1) # xsa) ! i) \<noteq> Q"
       using CptnModEnv(5) by fastforce
     moreover have "fst (last ((C, t1) # xsa)) = c " using CptnModEnv(6) 
       by fastforce
     ultimately show ?thesis
       using CptnModEnv(3) CptnModEnv(7) env_tran_tail
       by (simp add: env_tran_tail CptnModEnv.prems(3))     
  qed 
  then obtain xs s'' ys where hi:"(\<Gamma>, xs) \<in> cp \<Gamma> P t1 \<and> (C, t1) # xsa = map (lift Q) xs@((c,  s'')#ys)"
    by fastforce
  have s1_s:"s1=s" using  CptnModEnv unfolding cp_def by auto
  have "\<exists>xsa' s'' ys. xs=((P,t1)#xsa') \<and> (\<Gamma>,((P,t1)#xsa'))\<in>cptn \<and> (C, t1) # xsa = 
             map (lift Q) ((P,t1)#xsa')@((c,  s'')#ys)" 
    using hi  unfolding cp_def
  proof -
      have "(\<Gamma>,xs)\<in>cptn \<and> xs!0 = (P,t1)" using hi unfolding cp_def by fastforce
      moreover then have "xs\<noteq>[]" using cptn.simps by fastforce  
      ultimately obtain xsa' where "xs=((P,t1)#xsa')" using SmallStepCon.nth_tl by fastforce 
      thus ?thesis
        using hi using \<open>(\<Gamma>, xs) \<in> cptn \<and> xs ! 0 = (P, t1)\<close>
        by blast 
  qed
  then obtain xsa' s'' ys where 
    xs:"xs=((P,t1)#xsa') \<and> (\<Gamma>,((P,t1)#xsa'))\<in>cptn \<and> (C, t1) # xsa =  
         map (lift Q) ((P,t1)#xsa')@((c,  s'')#ys)"
    by fastforce
  have env_tran:"\<Gamma>\<turnstile>\<^sub>c(P,s1) \<rightarrow>\<^sub>e (P,t1)" using CptnModEnv Seq_env_P by (metis fst_conv nth_Cons_0)  
  then have "(\<Gamma>,(P,s1)#(P,t1)#xsa')\<in>cptn" using xs env_tran
    using cptn_eq_cptn_mod_set cptn_mod.CptnModEnv by blast  
  then have "(\<Gamma>,(P,s1)#(P,t1)#xsa') \<in> cp \<Gamma> P s" 
    using cp_def s1_s by fastforce
  moreover have "(C,s1)#(C, t1) # xsa = map (lift Q) ((P,s1)#(P,t1)#xsa')@((c,  s'')#ys)"
    using xs C unfolding lift_def by fastforce
  ultimately show ?case by blast
next
  case (CptnModSkip)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModThrow)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModStuck)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModFault)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModSeq1 \<Gamma> P0 sa xsa zs P1)  
  thus ?case    
  proof -
    have a1:"\<forall>c p. fst (case p of (ca::('s, 'a, 'd,'e) LanguageCon.com, x::('s, 'd) xstate) \<Rightarrow> 
                (LanguageCon.com.Seq ca c, x)) = LanguageCon.com.Seq (fst p) c"
      by simp
    then have "[] = xsa"     
    proof -
     have "[] \<noteq> zs"
       using CptnModSeq1 by force
     then show ?thesis
       by (metis CptnModSeq1.hyps(3) CptnModSeq1.prems(3) LanguageCon.com.simps(91) 
                 LanguageCon.com.simps(97) LanguageCon.com.simps(99) One_nat_def 
                 last_ConsR last_conv_nth last_lift)
    qed   
    then have "\<forall>c. Throw = c \<or> [] = zs"
      using CptnModSeq1(3) by fastforce
    then show ?thesis
      using CptnModSeq1.prems(3) by force
  qed   
next
  case (CptnModSeq2 \<Gamma> P0 sa xsa P1 ys zs) 
  then have "P0 = P \<and> P1 = Q" by auto
  then obtain i where zs:"fst (zs!i) = Q \<and> (i< (length zs))" using CptnModSeq2
    by (metis (no_types, lifting) add_diff_cancel_left' fst_conv length_Cons length_append nth_append_length zero_less_Suc zero_less_diff)    
  then have "Suc i< length ((Seq P0 P1,sa)#zs)" by fastforce
  then have "fst (((Seq P0 P1, sa) # zs)!Suc i) = Q" using zs by fastforce    
  thus ?case using CptnModSeq2(8) zs by auto
next 
  case (CptnModSeq3 \<Gamma> P0 sa xsa c1 t s'' ys zs P1)  
  then have P:"P0 = P \<and> P1 = Q \<and> s= sa" by auto  
  moreover then have cp:"(\<Gamma>, (P0,  sa) # xsa)\<in> cp \<Gamma> P s" 
    using CptnModSeq3(1)
    by (simp add: cp_def cptn_eq_cptn_mod_set)            
  ultimately show ?case  
  proof -
    have f1: "(\<Gamma>, (c1, s'') # ys) \<in> cptn_mod"
      using CptnModSeq3.hyps(6) cptn_mod_nest_cptn_mod by blast
    have f2: "0 \<le> length ys"
      by fastforce
    have f3: "c = fst (((c1, s'') # ys) ! length ys)"
      by (metis (no_types) CptnModSeq3.hyps(8) CptnModSeq3.prems(3) 
           append_is_Nil_conv last_ConsR last_appendR last_length list.simps(3))
    have "final_glob (c1, s'')"
      by (metis (no_types) CptnModSeq3.hyps(4) final_glob_def fst_conv)
    then have "final_glob (((c1, s'') # ys) ! 0)"
      by simp
    then show ?thesis
      using f3 f2 f1 by (metis (no_types) Cons_lift_append CptnModSeq3.hyps(8) cp P 
            cptn_if_cptn_mod fst_conv last_F length_Cons lessI nth_Cons_0)
  qed        
qed (force, auto)


lemma Seq_sound2': 
assumes
  a0:"(n,\<Gamma>,x)\<in>cptn_mod_nest_call" and
  a1:"x!0 = ((Seq P Q),s)" and
  a2:"\<forall>i<length x. fst (x!i)\<noteq> Q" and
  a3:"fst (last x) = c \<and> (c = Throw \<or> c = Stuck \<or> (\<exists>f. c = Fault f)) " and
  a4:"env_tran_right \<Gamma> x rely"
shows
  "\<exists>xs s' ys. (\<Gamma>,xs) \<in> cpn n \<Gamma> P s \<and> x = ((map (lift Q) xs)@((c,  s')#ys))"
using a0 a1 a2 a3 a4
proof (induct arbitrary: P s )
  case (CptnModNestOne n \<Gamma> C s1)
  thus ?case by fastforce
next
  case (CptnModNestEnv \<Gamma> C s1 t1 n xsa)
  then have C:"C=Seq P Q" unfolding lift_def by fastforce
  have "\<exists>xs s' ys. (\<Gamma>, xs) \<in> cpn n \<Gamma> P t1 \<and> (C, t1) # xsa = map (lift Q) xs@((c,  s')#ys)"
  proof -
     have "((C, t1) # xsa) ! 0 = (LanguageCon.com.Seq P Q, t1)" using C by auto
     moreover have "\<forall>i<length ((C, t1) # xsa). fst (((C, t1) # xsa) ! i) \<noteq> Q"
       using CptnModNestEnv(5) by fastforce
     moreover have "fst (last ((C, t1) # xsa)) = c" 
       using CptnModNestEnv(6) 
       by fastforce
     ultimately show ?thesis
       using CptnModNestEnv(3) CptnModNestEnv(7) 
       by (auto simp add: env_tran_tail CptnModNestEnv.prems(3))     
  qed 
  then obtain xs s'' ys where 
    hi:"(\<Gamma>, xs) \<in> cpn n \<Gamma> P t1 \<and> 
      (C, t1) # xsa = map (lift Q) xs@((c,  s'')#ys)"
    by fastforce
  have s1_s:"s1=s" using  CptnModNestEnv unfolding cp_def by auto
  have "\<exists>xsa' s'' ys. xs=((P,t1)#xsa') \<and> (n, \<Gamma>,((P,t1)#xsa'))\<in>cptn_mod_nest_call \<and> 
          (C, t1) # xsa = map (lift Q) ((P,t1)#xsa')@((c,  s'')#ys)" 
    using hi  unfolding cp_def
  proof -
      have "(n, \<Gamma>,xs)\<in>cptn_mod_nest_call \<and> xs!0 = (P,t1)" using hi unfolding cpn_def by fastforce
      moreover then have "xs\<noteq>[]" using cptn_mod_nest_call.simps by fastforce  
      ultimately obtain xsa' where "xs=((P,t1)#xsa')" using SmallStepCon.nth_tl by fastforce 
      thus ?thesis
        using hi using \<open>(n, \<Gamma>, xs) \<in> cptn_mod_nest_call \<and> xs ! 0 = (P, t1)\<close> by blast 
  qed
  then obtain xsa' s'' ys where xs:"xs=((P,t1)#xsa') \<and> (n, \<Gamma>,((P,t1)#xsa'))\<in>cptn_mod_nest_call \<and> 
                (C, t1) # xsa = map (lift Q) ((P,t1)#xsa')@((c,  s'')#ys)"
    by fastforce
  have env_tran:"\<Gamma>\<turnstile>\<^sub>c(P,s1) \<rightarrow>\<^sub>e (P,t1)" using CptnModNestEnv Seq_env_P by (metis fst_conv nth_Cons_0)  
  then have "(n, \<Gamma>,(P,s1)#(P,t1)#xsa')\<in>cptn_mod_nest_call" using xs env_tran cptn_mod_nest_call.CptnModNestEnv by blast    
  then have "(\<Gamma>,(P,s1)#(P,t1)#xsa') \<in> cpn n \<Gamma> P s" 
    using cpn_def s1_s by fastforce
  moreover have "(C,s1)#(C, t1) # xsa = map (lift Q) ((P,s1)#(P,t1)#xsa')@((c,  s'')#ys)"
    using xs C unfolding lift_def by fastforce
  ultimately show ?case by blast
next
  case (CptnModNestSkip)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModNestThrow)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
 case (CptnModNestStuck)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModNestFault)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModNestSeq1 n \<Gamma> P0 sa xsa zs P1)  
  thus ?case    
  proof -
    have a1:"\<forall>c p. fst (case p of (ca::('s, 'a, 'd,'e) LanguageCon.com, x::('s, 'd) xstate) \<Rightarrow> 
                (LanguageCon.com.Seq ca c, x)) = LanguageCon.com.Seq (fst p) c"
      by simp
    then have "[] = xsa"     
    proof -
     have "[] \<noteq> zs"
       using CptnModNestSeq1 by force
     then show ?thesis
       by (metis CptnModNestSeq1.hyps(3) CptnModNestSeq1.prems(3) 
                LanguageCon.com.simps(91) LanguageCon.com.simps(97) 
                LanguageCon.com.simps(99) One_nat_def last_ConsR last_conv_nth last_lift) 
    qed   
    then have "\<forall>c. Throw = c \<or> [] = zs"
      using CptnModNestSeq1(3) by fastforce
    then show ?thesis
      using CptnModNestSeq1.prems(3) by force
  qed   
next
  case (CptnModNestSeq2 n \<Gamma> P0 sa xsa P1 ys zs) 
  then have "P0 = P \<and> P1 = Q" by auto
  then obtain i where zs:"fst (zs!i) = Q \<and> (i< (length zs))" using CptnModNestSeq2
    by (metis (no_types, lifting) add_diff_cancel_left' fst_conv length_Cons length_append nth_append_length zero_less_Suc zero_less_diff)    
  then have "Suc i< length ((Seq P0 P1,sa)#zs)" by fastforce
  then have "fst (((Seq P0 P1, sa) # zs)!Suc i) = Q" using zs by fastforce    
  thus ?case using CptnModNestSeq2(8) zs by auto
next 
  case (CptnModNestSeq3 n \<Gamma> P0 sa xsa c1 f  s'' ys zs P1)  
  then have P0:"P0 = P \<and> P1 = Q \<and> s= sa" by auto  
  moreover then have cpn:"(\<Gamma>, (P0,  sa) # xsa)\<in> cpn n \<Gamma> P s" 
    using CptnModNestSeq3(1)
    by (simp add: cpn_def)  
  ultimately show ?case
  proof -
    have f1: "(\<Gamma>, (c1, s'') # ys) \<in> cptn_mod"
      using CptnModNestSeq3.hyps(6) cptn_mod_nest_cptn_mod by blast
    have f2: "0 \<le> length ys"
      by fastforce
    have f3: "c = fst (((c1, s'') # ys) ! length ys)"
      by (metis (no_types) CptnModNestSeq3.hyps(8) CptnModNestSeq3.prems(3) 
           append_is_Nil_conv last_ConsR last_appendR last_length list.simps(3))
    have "final_glob (c1, s'')"
      by (metis (no_types) CptnModNestSeq3.hyps(4) final_glob_def fst_conv)
    then have "final_glob (((c1, s'') # ys) ! 0)"
      by simp
    then show ?thesis
      using f3 f2 f1 by (metis (no_types) Cons_lift_append CptnModNestSeq3.hyps(8) cpn P0 
            cptn_if_cptn_mod fst_conv last_F length_Cons lessI nth_Cons_0)
  qed      
qed (auto)



lemma Last_Skip_Exist_Final: 
assumes
  a0:"(\<Gamma>,x)\<in>cptn" and
  a1:"x!0 = ((Seq P Q),s)" and
  a2:"\<forall>i<length x. fst (x!i)\<noteq> Q" and
  a3:"fst(last x) = Skip"  
shows 
  "\<exists>c s' i. i<length x \<and> x!i = (Seq c Q,s') \<and> final_glob (c,s')"
using a0 a1 a2 a3 
proof (induct arbitrary: P s)
  case (CptnOne \<Gamma> c s1) thus ?case by fastforce 
next
  case (Cptn \<Gamma> C st C' st' xsa) 
  then have "\<Gamma>\<turnstile>\<^sub>c (C, st) \<rightarrow>\<^sub>c\<^sub>e (C', st')" by auto
  then have "\<Gamma>\<turnstile>\<^sub>c (C, st) \<rightarrow>\<^sub>e (C', st') \<or> \<Gamma>\<turnstile>\<^sub>c (C, toSeq st) \<rightarrow> (C', toSeq st')"
    using step_ce_dest by blast
  moreover {assume "\<Gamma>\<turnstile>\<^sub>c (C, st) \<rightarrow>\<^sub>e (C', st')"
   moreover have "LanguageCon.com.Seq P Q = C"
     using Cptn.prems(1) by auto
   moreover have  "C' = C" using env_c_c' calculation Cptn by blast
   ultimately have ?case using Cptn
     by (metis Suc_less_eq last_length length_Cons nth_Cons_0 nth_Cons_Suc)  
  }
  moreover {
    assume  a00:"\<Gamma>\<turnstile>\<^sub>c (C, toSeq st) \<rightarrow> (C', toSeq st')"
    then have c_seq:"C = (Seq P Q) \<and> st = s" using Cptn by force
    from a00 c_seq have ?case 
    proof(cases)
      case (Seqc P1 P1' P2) 
      then have "\<exists>c s' i. i < length ((C', st') # xsa) \<and> 
                        ((C', st') # xsa) ! i = (LanguageCon.com.Seq c Q, s') \<and> 
                        final_glob (c, s')"
        using Cptn last.simps
        by (metis LanguageCon.com.inject(3) Suc_less_eq c_seq 
                 length_Cons list.simps(3) nth_Cons_0 nth_Cons_Suc) 
      thus ?thesis by fastforce 
    next
      case (SeqThrowc C2) 
      thus ?thesis 
      proof -
        have "LanguageCon.com.Seq LanguageCon.com.Throw Q = C"
          using \<open>C = LanguageCon.com.Seq LanguageCon.com.Throw C2\<close> c_seq by blast
        then show ?thesis
          using Cptn unfolding final_glob_def
          by (metis c_seq fst_conv length_Cons local.SeqThrowc(2) zero_less_Suc)
      qed
    next
      case (SeqSkipc ) thus ?thesis
        using Cptn.prems(2) c_seq by auto 
    next case (SeqFaultc f C2) thus ?thesis using Cptn.prems(2) c_seq
        by (metis Cptn.prems(1) LanguageCon.com.inject(3) 
              final_glob_def fst_conv length_Cons zero_less_Suc) 
    next case (SeqStuckc C2) thus ?thesis using Cptn.prems(2) c_seq
        by (metis Cptn.prems(1) LanguageCon.com.inject(3) 
              final_glob_def fst_conv length_Cons zero_less_Suc) 
           
    qed (fastforce, auto)
  } ultimately show ?case by auto
qed

lemma Seq_sound3:                                                       
assumes
  a0:"(n,\<Gamma>,x)\<in>cptn_mod_nest_call" and
  a1:"x!0 = ((Seq P Q),s)" and
  a2:"\<forall>i<length x. fst (x!i)\<noteq> Q" and
  a3:"fst(last x) = Skip" and
  a4:"env_tran_right \<Gamma> x rely " and
  a5:"snd (x!0)\<in>  p \<and> Sta p rely \<and> Sta a rely" and
  a6: "\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> P sat [p, rely, G, q,a]"
shows
  "False"
using a0 a1 a2 a3 a4 a5 a6
proof (induct arbitrary: P s p) (* p) *)
  case (CptnModNestOne n \<Gamma> C s1)  
    thus ?case by fastforce
next
  case (CptnModNestEnv \<Gamma> C s1 t1 n xsa)
  then have C:"C=Seq P Q" unfolding lift_def by fastforce
  thus ?case
  proof -
     have "((C, t1) # xsa) ! 0 = (LanguageCon.com.Seq P Q, t1)" using C by auto
     moreover have "\<forall>i<length ((C, t1) # xsa). fst (((C, t1) # xsa) ! i) \<noteq> Q"
       using CptnModNestEnv(5) by fastforce
     moreover have "fst (last ((C, t1) # xsa)) = LanguageCon.com.Skip" using CptnModNestEnv(6)
       by (simp add: SmallStepCon.final_def)        
     moreover have "snd (((C, t1) # xsa) ! 0) \<in>  p" 
       using CptnModNestEnv(8) CptnModNestEnv(1) CptnModNestEnv(7)
       unfolding env_tran_right_def Sta_def
       by (metis Suc_less_eq length_Cons nth_Cons_0 nth_Cons_Suc zero_less_Suc) 
     ultimately show ?thesis
       using CptnModNestEnv(3) CptnModNestEnv(7) CptnModNestEnv(8)  CptnModNestEnv(9) env_tran_tail
       by blast
  qed  
next
  case (CptnModNestSkip)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModNestThrow)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next 
  case  (CptnModNestStuck)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next 
  case  (CptnModNestFault)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModNestSeq1 n \<Gamma> P0 sa xsa zs P1)
  obtain cl where "fst (last ((LanguageCon.com.Seq P0 P1, sa) # zs)) = Seq cl P1"
    using CptnModNestSeq1(3)
    by (metis Cons_lift last_length length_Cons lessI map_lift_all_seq)
  thus ?case using CptnModNestSeq1(6) by auto
next
 case (CptnModNestSeq2 n \<Gamma> P0 sa xsa P1 ys zs) 
  then have "P0 = P \<and> P1 = Q" by auto
  then obtain i where zs:"fst (zs!i) = Q \<and> (i< (length zs))" using CptnModNestSeq2
    by (metis (no_types, lifting) add_diff_cancel_left' fst_conv length_Cons length_append nth_append_length zero_less_Suc zero_less_diff)        
  thus ?case using CptnModNestSeq2(8) zs by auto 
next
   case (CptnModNestSeq3 n \<Gamma> P1 sa xsa c f s' ys zs Q1 )  
  
  have c:"fst (last ((c,  s') # ys)) = c"
    by (metis CptnModNestSeq3.hyps(4) CptnModNestSeq3.hyps(6) 
    cptn_eq_cptn_mod_nest last_length length_Cons lessI term_all_skip)
  thus ?case using CptnModNestSeq3.hyps(4) apply auto  
    using   CptnModNestSeq3.hyps(8) CptnModNestSeq3.prems(3) by auto
qed(auto)

lemma map_xs_ys:
  assumes
  a0:"(\<Gamma>, (P0, sa) # xsa) \<in> cptn_mod" and    
  a1:"fst (last ((P0, sa) # xsa)) = C" and
  a2:"(\<Gamma>, (P1, snd (last ((P0, sa) # xsa))) # ys) \<in> cptn_mod" and
  a3:"zs = map (lift P1) xsa @ (P1, snd (last ((P0, sa) # xsa))) # ys" and
  a4:"((LanguageCon.com.Seq P0 P1, sa) # zs) ! 0 = (LanguageCon.com.Seq P Q, s)" and
  a5:"i < length ((LanguageCon.com.Seq P0 P1, sa) # zs) \<and> ((LanguageCon.com.Seq P0 P1, sa) # zs) ! i = (Q, sj)" and
  a6:"\<forall>j<i. fst (((LanguageCon.com.Seq P0 P1, sa) # zs) ! j) \<noteq> Q"
shows 
  "\<exists>xs ys. (\<Gamma>, xs) \<in> cp \<Gamma> P s \<and>
            (\<Gamma>, ys) \<in> cp \<Gamma> Q (snd (xs ! (i - 1))) \<and> (LanguageCon.com.Seq P0 P1, sa) # zs = map (lift Q) xs @ ys"
proof -
  let ?P0 = "(P0, sa) # xsa"
  have P_Q:"P=P0 \<and> s=sa \<and> Q = P1" using a4 by force
  have i:"i=(length ((P0, sa) # xsa))"   
  proof (cases "i=(length ((P0, sa) # xsa))")
    case True thus ?thesis by auto
  next
    case False     
    then have i:"i<(length ((P0, sa) # xsa)) \<or> i > (length ((P0, sa) # xsa))" by auto
    {
      assume i:"i<(length ((P0, sa) # xsa))"
      then have eq_map:"((LanguageCon.com.Seq P0 P1, sa) # zs) ! i = map (lift P1) ((P0, sa) # xsa) ! i" 
        using a3 Cons_lift_append by (metis (no_types, lifting) length_map nth_append) 
      then have  "\<exists>ci si. map (lift P1) ((P0, sa) # xsa) ! i = (Seq ci P1,si)" 
        using i unfolding lift_def
        proof -
          have "map (\<lambda>(c, y). (LanguageCon.com.Seq c P1, y)) ((P0, sa) # xsa) ! i = (case ((P0, sa) # xsa) ! i of (c, x) \<Rightarrow> (LanguageCon.com.Seq c P1, x))"
            by (meson \<open>i < length ((P0, sa) # xsa)\<close> nth_map)
          then show "\<exists>c x. map (\<lambda>(c, x). (LanguageCon.com.Seq c P1, x)) ((P0, sa) # xsa) ! i = (LanguageCon.com.Seq c P1, x)"
            by (simp add: case_prod_beta)
        qed 
      then have  "((LanguageCon.com.Seq P0 P1, sa) # zs) ! i \<noteq> (Q, sj)" 
        using P_Q eq_map by fastforce
      then have ?thesis using a5 by auto
    }note l=this
    {
      assume i:"i>(length ((P0, sa) # xsa))"
      have "fst (((LanguageCon.com.Seq P0 P1, sa) # zs) ! (length ?P0)) = Q"
        using a3 P_Q Cons_lift_append by (metis fstI length_map nth_append_length) 
      then have ?thesis using a6 i by auto
    }
    thus ?thesis using l i by auto
   qed
   then have  "(\<Gamma>, (P0, sa) # xsa) \<in> cp \<Gamma> P s" 
    using a0  cptn_eq_cptn_mod P_Q unfolding cp_def by fastforce
  also have "(\<Gamma>, (P1, snd (last ((P0, sa) # xsa))) # ys) \<in> cp \<Gamma> Q (snd (?P0 ! ((length ?P0) -1)))" 
    using a3 cptn_eq_cptn_mod P_Q unfolding cp_def
  proof -
    have "(\<Gamma>, (Q, snd (last ((P0, sa) # xsa))) # ys) \<in> cptn_mod"
      using a2 P_Q by blast
    then have "(\<Gamma>, (Q, snd (last ((P0, sa) # xsa))) # ys) \<in> {(f, ps). ps ! 0 = (Q, snd (((P0, sa) # xsa) ! (Suc (length xsa) - 1))) \<and> (\<Gamma>, ps) \<in> cptn \<and> f = \<Gamma>}"
      by (simp add: cptn_eq_cptn_mod last_length)
    then show "(\<Gamma>, (P1, snd (last ((P0, sa) # xsa))) # ys) \<in> {(f, ps). ps ! 0 = (Q, snd (((P0, sa) # xsa) ! (length ((P0, sa) # xsa) - 1))) \<and> (\<Gamma>, ps) \<in> cptn \<and> f = \<Gamma>}"
      using P_Q by force
  qed 
  ultimately show ?thesis using a3 P_Q i using Cons_lift_append by blast
qed

lemma map_xs_ys':
  assumes
  a0:"(n, \<Gamma>, (P0, sa) # xsa) \<in> cptn_mod_nest_call" and    
  a1:"fst (last ((P0, sa) # xsa)) = C" and
  a2:"(n,\<Gamma>, (P1, snd (last ((P0, sa) # xsa))) # ys) \<in> cptn_mod_nest_call" and
  a3:"zs = map (lift P1) xsa @ (P1, snd (last ((P0, sa) # xsa))) # ys" and
  a4:"((LanguageCon.com.Seq P0 P1, sa) # zs) ! 0 = (LanguageCon.com.Seq P Q, s)" and
  a5:"i < length ((LanguageCon.com.Seq P0 P1, sa) # zs) \<and> ((LanguageCon.com.Seq P0 P1, sa) # zs) ! i = (Q, sj)" and
  a6:"\<forall>j<i. fst (((LanguageCon.com.Seq P0 P1, sa) # zs) ! j) \<noteq> Q"
shows 
  "\<exists>xs ys. (\<Gamma>, xs) \<in> cpn n \<Gamma> P s \<and>
            (\<Gamma>, ys) \<in> cpn n \<Gamma> Q (snd (xs ! (i - 1))) \<and> (LanguageCon.com.Seq P0 P1, sa) # zs = map (lift Q) xs @ ys"
proof -
  let ?P0 = "(P0, sa) # xsa"
  have P_Q:"P=P0 \<and> s=sa \<and> Q = P1" using a4 by force
  have i:"i=(length ((P0, sa) # xsa))"   
  proof (cases "i=(length ((P0, sa) # xsa))")
    case True thus ?thesis by auto
  next
    case False     
    then have i:"i<(length ((P0, sa) # xsa)) \<or> i > (length ((P0, sa) # xsa))" by auto
    {
      assume i:"i<(length ((P0, sa) # xsa))"
      then have eq_map:"((LanguageCon.com.Seq P0 P1, sa) # zs) ! i = map (lift P1) ((P0, sa) # xsa) ! i" 
        using a3 Cons_lift_append by (metis (no_types, lifting) length_map nth_append) 
      then have  "\<exists>ci si. map (lift P1) ((P0, sa) # xsa) ! i = (Seq ci P1,si)" 
        using i unfolding lift_def
        proof -
          have "map (\<lambda>(c, y). (LanguageCon.com.Seq c P1, y)) ((P0, sa) # xsa) ! i = (case ((P0, sa) # xsa) ! i of (c, x) \<Rightarrow> (LanguageCon.com.Seq c P1, x))"
            by (meson \<open>i < length ((P0, sa) # xsa)\<close> nth_map)
          then show "\<exists>c x. map (\<lambda>(c, x). (LanguageCon.com.Seq c P1, x)) ((P0, sa) # xsa) ! i = (LanguageCon.com.Seq c P1, x)"
            by (simp add: case_prod_beta)
        qed 
      then have  "((LanguageCon.com.Seq P0 P1, sa) # zs) ! i \<noteq> (Q, sj)" 
        using P_Q eq_map by fastforce
      then have ?thesis using a5 by auto
    }note l=this
    {
      assume i:"i>(length ((P0, sa) # xsa))"
      have "fst (((LanguageCon.com.Seq P0 P1, sa) # zs) ! (length ?P0)) = Q"
        using a3 P_Q Cons_lift_append by (metis fstI length_map nth_append_length) 
      then have ?thesis using a6 i by auto
    }
    thus ?thesis using l i by auto
   qed
   then have  "(\<Gamma>, (P0, sa) # xsa) \<in> cpn n \<Gamma> P s" 
    using a0  P_Q unfolding cpn_def by fastforce
  also have "(\<Gamma>, (P1, snd (last ((P0, sa) # xsa))) # ys) \<in> cpn n \<Gamma> Q (snd (?P0 ! ((length ?P0) -1)))" 
    using a3 cptn_eq_cptn_mod P_Q unfolding cpn_def
  proof -
    have "(n, \<Gamma>, (Q, snd (last ((P0, sa) # xsa))) # ys) \<in> cptn_mod_nest_call"
      using a2 P_Q by blast
    then have "(\<Gamma>, (Q, snd (last ((P0, sa) # xsa))) # ys) \<in> {(f, ps). ps ! 0 = (Q, snd (((P0, sa) # xsa) ! (Suc (length xsa) - 1))) \<and> 
              (n, \<Gamma>, ps) \<in> cptn_mod_nest_call \<and> f = \<Gamma>}"
      by (simp add: cptn_eq_cptn_mod last_length)
    then show "(\<Gamma>, (P1, snd (last ((P0, sa) # xsa))) # ys) \<in> {(f, ps). ps ! 0 = (Q, snd (((P0, sa) # xsa) ! (length ((P0, sa) # xsa) - 1))) \<and> (n,\<Gamma>, ps) \<in> cptn_mod_nest_call \<and> f = \<Gamma>}"
      using P_Q by force
  qed 
  ultimately show ?thesis using a3 P_Q i using Cons_lift_append by blast
qed



lemma Seq_sound4: 
assumes
  a0:"(n,\<Gamma>,x)\<in>cptn_mod_nest_call" and
  a1:"x!0 = ((Seq P Q),s)" and
  a2:"i<length x \<and> x!i=(Q,sj)" and
  a3:"\<forall>j<i. fst(x!j)\<noteq>Q" and 
  a4:"env_tran_right \<Gamma> x rely" and
  a5:"snd (x!0)\<in>  p \<and> Sta p rely \<and> Sta a rely" and
  a6: "\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> P sat [p, rely, G, q,a]"
shows
  "\<exists>xs ys. (\<Gamma>,xs) \<in> (cpn n \<Gamma> P s) \<and> (\<Gamma>,ys) \<in> (cpn n \<Gamma> Q (snd (xs!(i-1)))) \<and> x = (map (lift Q) xs)@ys"
using a0 a1 a2 a3 a4 a5 a6
proof (induct arbitrary: i sj P s p) 
   case (CptnModNestOne \<Gamma> C s1)  
    thus ?case by fastforce
next
  case (CptnModNestEnv \<Gamma> C st t n xsa)    
  have a1:"Seq P Q \<noteq> Q" by simp    
  then have C_seq:"C=(Seq P Q)" using CptnModNestEnv by fastforce
  then have "fst(((C, st) # (C, t) # xsa)!0) \<noteq>Q" using  a1 by auto
  moreover have  n_q:"fst(((C, st) # (C, t) # xsa)!1) \<noteq>Q" using CptnModNestEnv a1 by auto
  moreover have "fst(((C, st) # (C, t) # xsa)!i) =Q" using CptnModNestEnv by auto
  ultimately have i_suc: "i> (Suc 0)" 
    by (metis Suc_eq_plus1 Suc_lessI add.left_neutral neq0_conv) 
  then obtain i' where i':"i=Suc i'" by (meson lessE) 
  then have i_minus:"i'=i-1" by auto
  have c_init:"((C, t) # xsa) ! 0 = ((Seq P Q), t)"
    using CptnModNestEnv by auto 
  moreover have "i'< length ((C,t)#xsa) \<and> ((C,t)#xsa)!i' = (Q,sj)"
    using i' CptnModNestEnv(5) by force
  moreover have "\<forall>j<i'. fst (((C, t) # xsa) ! j) \<noteq> Q"
    using i' CptnModNestEnv(6) by force
  moreover have "snd (((C, t) # xsa) ! 0) \<in> p" 
       using CptnModNestEnv(8) CptnModNestEnv(1) CptnModNestEnv(7)
       unfolding env_tran_right_def Sta_def
       by (metis Suc_mono length_Cons nth_Cons_0 nth_Cons_Suc zero_less_Suc)  
  ultimately have hyp:"\<exists>xs ys.
     (\<Gamma>, xs) \<in> cpn n \<Gamma> P t \<and>
     (\<Gamma>, ys) \<in> cpn n \<Gamma> Q (snd (xs ! (i'-1))) \<and> (C, t) # xsa = map (lift Q) xs @ ys"
    using CptnModNestEnv(3) env_tran_tail  CptnModNestEnv(8) CptnModNestEnv(9) 
         CptnModNestEnv.prems(4) by blast  
  then obtain xs ys where xs_cp:"(\<Gamma>, xs) \<in> cpn n \<Gamma> P t \<and>
     (\<Gamma>, ys) \<in> cpn n \<Gamma> Q (snd (xs ! (i'-1))) \<and> (C, t) # xsa = map (lift Q) xs @ ys"
    by fast
  have "(\<Gamma>, (P,s)#xs) \<in> cpn n \<Gamma> P s"
  proof -
    have "xs!0 = (P,t)" 
      using xs_cp unfolding cpn_def by blast
    moreover have "xs\<noteq>[]"
      using xs_cp  n_q c_init unfolding cpn_def by auto 
    ultimately obtain xs' where xs':"(n, \<Gamma>, (P,t)#xs') \<in> cptn_mod_nest_call \<and> xs=(P,t)#xs'" 
      using SmallStepCon.nth_tl xs_cp unfolding cpn_def by force
    thus ?thesis 
    proof -
      have "(LanguageCon.com.Seq P Q, s) = (C, st)"
        using CptnModNestEnv.prems(1) by auto
      then have "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow>\<^sub>e (P, t)"
        using Seq_env_P CptnModNestEnv(1) by blast
      then show ?thesis
        by (simp add:xs' cpn_def cptn_mod_nest_call.CptnModNestEnv)
    qed
  qed
  thus  ?case 
    using i_suc Cons_lift_append CptnModNestEnv.prems(1) i' i_minus xs_cp
    by (metis (no_types, lifting) One_nat_def nth_Cons_0 nth_Cons_pos zero_less_diff)
      
next
  case (CptnModNestSkip)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModNestThrow)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModNestFault)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModNestStuck)
  thus ?case by (metis SmallStepCon.redex_not_Seq fst_conv nth_Cons_0)
next
  case (CptnModNestSeq1 n \<Gamma> P0 sa xsa zs P1)  
  then have P1_Q:"P1 = Q" by auto
  let ?x = "(LanguageCon.com.Seq P0 P1, sa) # zs"
  have "\<forall>j<length ?x. \<exists>c s. ?x!j = (Seq c P1,s)" using CptnModNestSeq1(3)
  proof (induct xsa arbitrary: zs P0 P1 sa)
    case Nil thus ?case by auto
  next
    case (Cons a xsa) 
    then obtain ac as where "a=(ac,as)"
      by (meson prod.exhaust_sel)
    then have zs:"zs = (Seq ac P1,as)#(map (lift P1)  xsa)" 
      using Cons(2) 
      unfolding lift_def  by auto
    have zs_eq:"(map (lift P1)  xsa)=(map (lift P1)  xsa)" by auto
    note hyp=Cons(1)[OF zs_eq] 
    note hyp[of ac as]
    thus ?case using zs Cons(2) by (metis One_nat_def diff_Suc_Suc diff_zero length_Cons less_Suc_eq_0_disj nth_Cons') 
  qed  
  thus ?case using P1_Q CptnModNestSeq1(5) using fstI seq_not_eq2 by auto
next
  case (CptnModNestSeq2 n \<Gamma> P0 sa xsa P1 ys zs) 
  then show ?case using map_xs_ys'[OF CptnModNestSeq2(1) CptnModNestSeq2(3) CptnModNestSeq2(4) CptnModNestSeq2(6)
                              CptnModNestSeq2(7) CptnModNestSeq2(8) CptnModNestSeq2(9)] by blast
next 
  case (CptnModNestSeq3 n \<Gamma> P1 sa xsa c f s' ys zs Q1 ) 
  then have P_Q:"P=P1 \<and> Q = Q1" by force  
  thus ?case
  proof (cases "Q1 = Throw \<or> Q1 = Stuck \<or> (\<exists>f. Q1 = Fault f)")
    case True      
    then have cptnmod:" (n,\<Gamma>,((Seq P1 Q1),  s)#zs) \<in> cptn_mod_nest_call"
      using cptn_mod.CptnModSeq3 P_Q
      by (smt CptnModNestSeq3.hyps(1) CptnModNestSeq3.hyps(3) CptnModNestSeq3.hyps(4) 
               CptnModNestSeq3.hyps(5) CptnModNestSeq3.hyps(6) CptnModNestSeq3.hyps(8) 
             CptnModNestSeq3.prems(1) cptn_mod_nest_call.CptnModNestSeq3 nth_Cons_0)
    then have c_Q1:"c = Q1" using CptnModNestSeq3 P_Q True
    proof -      
       have f4: "(\<Gamma>, (c, s') # ys) \<in> cptn"
        using  CptnModNestSeq3(6)
        using cptn_eq_cptn_mod_nest by blast
      have f3:"((LanguageCon.com.Seq P1 Q1, sa) # zs) ! i = (Q1, sj)"
        using P_Q CptnModNestSeq3(10) by fastforce
      then have f5: "final_glob (Q, sj)"
        by (metis P_Q True final_glob_def fst_conv)
      have "final_glob (c, s')"
        using CptnModNestSeq3.hyps(4) final_glob_def prod.collapse by blast
      then show ?thesis
        using f5 f4
        by (metis (no_types, lifting) CptnModNestSeq3.hyps(8) CptnModNestSeq3.prems(1) 
            CptnModNestSeq3.prems(2) f3 append_is_Nil_conv cptn_if_cptn_mod cptn_mod_nest_cptn_mod 
              cptnmod fst_conv last.simps last_F last_appendR last_length length_Cons 
            lessI less_Suc_eq_le list.simps(3) nth_Cons_0 zero_less_Suc)           
    qed       
    then show ?thesis  
      using CptnModNestSeq3  P_Q map_xs_ys'[of n \<Gamma> P1 "sa" xsa Q1 Q1 ys zs P1 Q1 sa i sj]
      by auto        
  next 
    case False note q_not_throw=this
    have "\<forall>x. x< length ((LanguageCon.com.Seq P1 Q1,  sa) # zs) \<longrightarrow>
              ((LanguageCon.com.Seq P1 Q1,  sa) # zs) ! x \<noteq> (Q, sj)"
    proof -
    {
      fix x
      assume x_less:"x< length ((LanguageCon.com.Seq P1 Q1,  sa) # zs)"
      have "((LanguageCon.com.Seq P1 Q1,  sa) # zs) ! x \<noteq> (Q, sj)"
      proof (cases "x < length ((LanguageCon.com.Seq P1 Q1,  sa)#map (lift Q1) xsa)")
        case True 
        then have eq_map:"((LanguageCon.com.Seq P1 Q1,  sa) # zs) ! x = 
                           map (lift Q1) ((P1,  sa) # xsa) ! x"
          by (metis (no_types, lifting) Cons_lift Cons_lift_append CptnModNestSeq3.hyps(8) nth_append)
        then have  "\<exists>ci si. map (lift Q1) ((P1,  sa) # xsa) ! x = (Seq ci Q1,si)" 
          using True unfolding lift_def
        proof -
          have "x < length ((P1,  sa) # xsa)"
            using True by auto
          then have "map (\<lambda>(c, y). (LanguageCon.com.Seq c Q1, y)) ((P1,  sa) # xsa) ! x = 
                      (case ((P1, sa) # xsa) ! x of (c, x) \<Rightarrow> (LanguageCon.com.Seq c Q1, x))"
            using nth_map by blast
          then show "\<exists>c x1. map (\<lambda>(c, x1). (LanguageCon.com.Seq c Q1, x1)) ((P1, sa) # xsa) ! x = 
                       (LanguageCon.com.Seq c Q1, x1)"
            by (simp add: case_prod_beta')
        qed            
        then have  "((LanguageCon.com.Seq P1 Q1,  sa) # zs) ! x \<noteq> (Q, sj)" 
          using P_Q eq_map by fastforce     
        thus ?thesis using CptnModNestSeq3(10) by auto        
      next
        case False        
        have all_throw:"\<forall>i<length ((c,  s')# ys). 
              fst (((c,  s')# ys)!i) = c"
          using CptnModNestSeq3.hyps(4) CptnModNestSeq3.hyps(6) 
            cptn_if_cptn_mod cptn_mod_nest_cptn_mod term_all_skip by blast      
        then have 
          "\<forall>x\<ge> length ((LanguageCon.com.Seq P1 Q1,  sa) # map (lift Q1) xsa). 
           x<length (((LanguageCon.com.Seq P1 Q1,  sa) # zs)) \<longrightarrow>
              fst (((LanguageCon.com.Seq P1 Q1,  sa) # zs) ! x) = c"  
        proof-
        {
          fix x 
          assume a1:"x\<ge> length ((LanguageCon.com.Seq P1 Q1,  sa) # map (lift Q1) xsa)" and
                 a2:"x<length (((LanguageCon.com.Seq P1 Q1,  sa) # zs))"
          then have "((Seq P1 Q1,  sa) # zs) ! x = 
                     ((c,  s')# ys) !(x - (length ((Seq P1 Q1,  sa) # map (lift Q1) xsa)))"
          using CptnModNestSeq3(8) by (metis Cons_lift Cons_lift_append not_le nth_append)
          then have"fst (((LanguageCon.com.Seq P1 Q1,  sa) # zs) ! x) = c" 
            using all_throw a1 a2 CptnModNestSeq3.hyps(8)  by auto 
        } thus ?thesis by auto
        qed       
        thus ?thesis using False CptnModNestSeq3(8) q_not_throw P_Q x_less
          by (metis CptnModNestSeq3.hyps(4) fst_conv not_le_imp_less)
      qed
    } thus ?thesis by auto
    qed
    thus ?thesis using CptnModNestSeq3(10) by fastforce    
  qed
qed(auto)



inductive_cases stepc_elim_cases_Seq_throw:
"\<Gamma>\<turnstile>\<^sub>c(Seq c1 c2,s) \<rightarrow> (Throw,  s1)" 
"\<Gamma>\<turnstile>\<^sub>c(Seq c1 c2,s) \<rightarrow> (Stuck,  s1)" 
"\<Gamma>\<turnstile>\<^sub>c(Seq c1 c2,s) \<rightarrow> (Fault f,  s1)"

inductive_cases stepc_elim_cases_Seq_skip_c2:
"\<Gamma>\<turnstile>\<^sub>c(Seq c1 c2,s) \<rightarrow> (c2,s)"


lemma seq_skip_throw:
 "\<Gamma>\<turnstile>\<^sub>c(Seq c1 c2,s) \<rightarrow> (c2,s)  \<Longrightarrow> c1= Skip \<or> c1=Throw \<or> c1 = Stuck \<or> (\<exists>f. c1 = Fault f)"
apply (rule stepc_elim_cases_Seq_skip_c2)
apply fastforce
  by auto


lemma step_ce_eq:   
  assumes step_m: "\<Gamma>\<turnstile>\<^sub>c (c, s) \<rightarrow>\<^sub>c\<^sub>e (c', s')" and
          step_ce:"\<Gamma>\<turnstile>\<^sub>c (c, toSeq s) \<rightarrow> (c', toSeq s')" and
          eq:"toSeq s = toSeq s'"
   shows "s = s'"
  by (metis  eq l1 step_ce step_m)


lemma Seq_sound: 
      "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p, R, G, q,a] \<Longrightarrow>
       \<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p, R, G, q,a] \<Longrightarrow>
       \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [q, R, G, r,a] \<Longrightarrow>
       \<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c2 sat [q, R, G, r,a] \<Longrightarrow>        
       Sta a R \<and> Sta p R \<Longrightarrow>  \<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (Seq c1 c2) sat [p, R, G, r,a]"
proof -  
  assume
    a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p, R, G, q,a]" and
    a1:"\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p, R, G, q,a]" and
    a2:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [q, R, G, r,a]" and    
    a3: "\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c2 sat [q, R, G, r,a]" and     
    a4: "Sta a R \<and> Sta p R" and
    a5: "\<forall>s. length (snd s) \<in> N p \<longrightarrow> ( s,  s) \<in> G"
  { 
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"
    then have a1:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p, R, G, q,a]" 
      using a1 com_cvalidityn_def by fastforce  
    then have a3: "\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c2 sat [q, R, G, r,a]"
      using a3 com_cvalidityn_def all_call by fastforce 
    have "cpn n \<Gamma> (Seq c1 c2)  s \<inter> assum(p, R) \<subseteq> comm(G, (r,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cpn n \<Gamma> (Seq c1 c2) s" and a11:"c \<in> assum(p, R)"
      then have a10':"c \<in> cp \<Gamma> (Seq c1 c2) s" unfolding cpn_def cp_def
        using cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod by fastforce
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have cp:"l!0=((Seq c1 c2),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10' cp_def c_prod by fastforce
      have cptn_nest:"l!0=((Seq c1 c2),s) \<and> (n,\<Gamma>,l) \<in> cptn_mod_nest_call \<and> \<Gamma>=\<Gamma>1" using a10 cpn_def c_prod by fastforce
      have \<Gamma>1:"(\<Gamma>, l) = c" using c_prod cp by blast
      have "c \<in> comm(G, (r,a)) F"         
      proof - 
      {      
       have assum:"snd(l!0) \<in> (p) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
                 (snd(l!i), snd(l!(Suc i))) \<in> R)" 
       using a11 c_prod unfolding assum_def by simp
       then have env_tran:"env_tran \<Gamma> p l R" using env_tran_def cp by blast
       then have env_tran_right: "env_tran_right \<Gamma> l R" 
         using env_tran env_tran_right_def unfolding env_tran_def by auto       
       have "(\<forall>i. Suc i<length l \<longrightarrow> 
               (\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                    (fst (l ! Suc i), toSeq (snd (l ! Suc i)))) \<longrightarrow>                                             
                 (snd(l!i), snd(l!(Suc i))) \<in> G)\<and>
             (final_glob (last l)  \<longrightarrow>   fst (last l) \<notin> Fault ` F \<longrightarrow>                       
                   ((fst (last l) = Skip \<and> snd (last l) \<in>  r)) \<or>
                    (fst (last l) = Throw \<and> snd (last l) \<in> a))"
       proof (cases "\<forall>i<length l. fst (l!i)\<noteq> c2")
         case True 
         then have no_c2:"\<forall>i<length l. fst (l!i)\<noteq> c2" by assumption          
         show ?thesis
         proof (cases "final_glob (last l)")
           case True
           then have "fst (last l) = Skip \<or> (fst (last l) = Throw \<or> 
                                 fst (last l) = Stuck \<or> (\<exists>f. fst (last l) = Fault f))"  
             using final_glob_def by fast           
           thus ?thesis
           proof
             assume "fst (last l) = LanguageCon.com.Skip" 
             then have "False" 
               using  no_c2 env_tran_right cptn_nest cptn_eq_cptn_mod_set Seq_sound3 a4 a1 assum
               by blast
             thus ?thesis by auto
           next             
             assume asm0:"(fst (last l) = Throw \<or> fst (last l) = Stuck \<or> (\<exists>f. fst (last l) = Fault f))"
             then obtain lc1 s1' ys where cpn_lc1:
             "(\<Gamma>,lc1) \<in> cpn n \<Gamma> c1 s \<and> l = ((map (lift c2) lc1)@((fst (last l),  s1')#ys))"
               using Seq_sound2'[of n \<Gamma> l c1 c2 s]  
                     cptn_nest cptn_eq_cptn_mod_set env_tran_right no_c2 by blast
             then have cp_lc1:"(\<Gamma>,lc1) \<in> cp \<Gamma> c1 s"
               using  cptn_if_cptn_mod cptn_mod_nest_cptn_mod split_conv 
               unfolding cp_def cpn_def by blast
             let ?m_lc1 = "map (lift c2) lc1"
             let ?lm_lc1 = "(length ?m_lc1)"
             let ?last_m_lc1 = "?m_lc1!(?lm_lc1-1)"             
             have lc1_not_empty:"lc1 \<noteq> []"
               using \<Gamma>1 a10  cpn_lc1 cp True unfolding final_glob_def by auto 
             then have map_cpn:"(\<Gamma>,?m_lc1) \<in> cpn n \<Gamma> (Seq c1 c2) s"                  
             proof -
               have f1: "lc1 ! 0 = (c1, s) \<and> (n,\<Gamma>, lc1) \<in> cptn_mod_nest_call \<and> \<Gamma> = \<Gamma>"
                 using cpn_lc1 cpn_def by blast
               then have f2: "(n, \<Gamma>, ?m_lc1) \<in> cptn_mod_nest_call" 
               by (metis (no_types) Cons_lift cptn_mod_nest_call.CptnModNestSeq1 f1 lc1_not_empty list.exhaust nth_Cons_0)                               
               then show ?thesis
                 using f2 f1 lc1_not_empty by (simp add: cpn_def lift_def)
             qed
             then have map_cp:"(\<Gamma>,?m_lc1) \<in> cp \<Gamma> (Seq c1 c2) s"
               by (metis (no_types, lifting) cp_def cp_lc1 cpn_def lift_is_cptn mem_Collect_eq split_conv) 
             also have map_assum:"(\<Gamma>,?m_lc1) \<in> assum (p,R)"
               using sub_assum a10 a11 \<Gamma>1 cpn_lc1 lc1_not_empty 
               by (metis SmallStepCon.nth_tl map_is_Nil_conv)
             ultimately have "((\<Gamma>,lc1) \<in> assum(p, R))"  
               using \<Gamma>1 assum_map cp_lc1 by blast                          
             then have lc1_comm:"(\<Gamma>,lc1) \<in> comm(G, (q,a)) F"  
               using a1  cpn_lc1 unfolding com_validityn_def by blast
             then have m_lc1_comm:"(\<Gamma>,?m_lc1) \<in> comm(G, (q,a)) F"
               using map_cp map_assum comm_map cp_lc1 by fastforce
             then have last_m_lc1:"last (?m_lc1) = (Seq (fst (last lc1)) c2,snd (last lc1))"
             proof -
               have a000:"\<forall>p c. (LanguageCon.com.Seq (fst p) c, snd p) = lift c p"
                 using Cons_lift by force
               then show ?thesis
                 by (simp add: last_map a000 lc1_not_empty)
             qed
             then have last_length:"last (?m_lc1) = ?last_m_lc1"  
               using lc1_not_empty last_conv_nth list.map_disc_iff by blast 
             then have l_map:"l!(?lm_lc1-1)= ?last_m_lc1" 
               using cpn_lc1
               by (metis (no_types) cpn_lc1 diff_less lc1_not_empty length_greater_0_conv length_map nth_append zero_less_one)                                          
             then have lm_lc1:"l!(?lm_lc1) = (fst (last l),  s1')"
               using cpn_lc1
               by (metis nth_append_length) 
             have step_ce:"\<Gamma>\<turnstile>\<^sub>c(l!(?lm_lc1-1)) \<rightarrow>\<^sub>c\<^sub>e (l!(?lm_lc1))"
             proof -
               have f1: "\<forall>n na. \<not> n < na \<or> Suc (na - Suc n) = na - n"
                 by (meson Suc_diff_Suc)
               have "map (lift c2) lc1 \<noteq> []"
                 by (metis lc1_not_empty map_is_Nil_conv)
               then have f2: "0 < length (map (lift c2) lc1)"
                 by (meson length_greater_0_conv)
               then have "length (map (lift c2) lc1) - 1 + 1 < 
                            length (map (lift c2) lc1 @ (fst (last l), s1') # ys)"
                 by simp
               then show ?thesis
                 using f2 f1
                 by (metis Suc_pred' cp cpn_lc1 cptn_tran_ce_i)
             qed
             then have step:"(\<Gamma>\<turnstile>\<^sub>c (fst (l ! (?lm_lc1-1)), toSeq (snd (l ! (?lm_lc1-1)))) \<rightarrow> 
                             (fst (l ! ?lm_lc1), toSeq (snd (l ! (?lm_lc1)))))"
               using l_map last_m_lc1 lm_lc1 local.last_length not_eq_not_env True
                      step_ce_not_step_e_step_c unfolding final_glob_def
               by (metis LanguageCon.com.distinct(5) LanguageCon.com.distinct(79) 
                    LanguageCon.com.distinct(85) LanguageCon.com.distinct(87) fstI sndI) 
             have eq_to_seq:"toSeq (snd (l ! (length (map (lift c2) lc1) - 1))) = 
                               toSeq (snd (l ! (length (map (lift c2) lc1))))"
               using l_map last_m_lc1 lm_lc1 local.last_length local.step 
               apply auto
               by (metis (no_types) stepc_elim_cases_Seq_throw asm0)                             
             then have step':"\<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.Seq (fst (last lc1)) c2,  (fst s1')) \<rightarrow>
                             (fst (last lc1),  (fst s1')) "
               using lm_lc1 asm0 apply auto
               by (smt One_nat_def append_is_Nil_conv cpn_lc1 diff_Suc_less fst_conv l_map 
                           last_conv_nth last_m_lc1 length_greater_0_conv 
                           length_map last_length local.step no_c2 stepc_elim_cases_Seq_throw(1,2,3) 
                            toSeq.simps)+               
             then have snd_l_len:"snd (l ! (length (map (lift c2) lc1) - 1)) =snd (l ! (length (map (lift c2) lc1)))"              
             proof -
               have "\<Gamma>\<turnstile>\<^sub>c (fst (l ! (length (map (lift c2) lc1) - 1)), snd (l ! (length (map (lift c2) lc1) - 1))) \<rightarrow>\<^sub>c\<^sub>e (fst (l ! length (map (lift c2) lc1)), snd (l ! length (map (lift c2) lc1)))"
                 using step_ce by auto
               then show ?thesis
                 using eq_to_seq local.step step_ce_eq by blast
             qed                             
             then have last_lc1_suc:"snd (l!(?lm_lc1-1)) = 
                        snd (l!?lm_lc1) \<and> fst (l!(?lm_lc1-1)) = Seq (fst (last l)) c2"
               using  stepc_elim_cases_Seq_throw  asm0 cpn_lc1 l_map last_m_lc1 local.last_length no_c2
               by (smt fst_conv lm_lc1 local.step step' stepc_elim_cases(1) stepc_elim_cases_Seq_skip(1))                                          
             have concl:"(\<forall>i. Suc i<length l \<longrightarrow> 
                       (\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                        (fst (l ! Suc i), toSeq (snd (l ! Suc i)))) \<longrightarrow>                                           
                 (snd(l!i), snd(l!(Suc i))) \<in> G)"
             proof-
             { fix k 
               assume a00:"Suc k<length l" and
                a21:"(\<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                      (fst (l ! Suc k), toSeq (snd (l ! Suc k))))"   
                then have i_m_l:"\<forall>i <?lm_lc1  . l!i = ?m_lc1!i" 
                  using cp_lc1
                proof -
                  have "map (lift c2) lc1 \<noteq> []"
                    by (meson lc1_not_empty list.map_disc_iff)
                  then show ?thesis
                    by (metis (no_types) cpn_lc1  nth_append)
                qed 
                have "(snd(l!k), snd(l!(Suc k))) \<in> G"
                proof (cases "Suc k< ?lm_lc1")
                  case True 
                  then have a11': "(\<Gamma>\<turnstile>\<^sub>c (fst (?m_lc1 ! k), toSeq (snd (?m_lc1!k))) \<rightarrow> 
                                        (fst (?m_lc1!(Suc k)), toSeq (snd (?m_lc1!(Suc k)))))" 
                    using a11 i_m_l True
                  proof -
                    have "\<forall>n na. \<not> 0 < n - Suc na \<or> na < n "
                      using diff_Suc_eq_diff_pred zero_less_diff by presburger
                    then show ?thesis
                      by (metis (no_types)  True a21 i_m_l  zero_less_diff)
                  qed                  
                  then have "(snd(?m_lc1!k), snd(?m_lc1!(Suc k))) \<in> G"
                  using a11' m_lc1_comm True comm_dest1  last_not_F by fastforce
                  thus ?thesis using i_m_l using  True by fastforce
                next
                  case False 
                  then have "(Suc k=?lm_lc1) \<or> (Suc k>?lm_lc1)" by auto
                  thus ?thesis 
                  proof
                  { assume suck:"(Suc k=?lm_lc1)"
                    then have k:"k=?lm_lc1-1" by auto      
                    then have "length (snd (snd ((l ! k)))) \<in> N p"
                      using cptn_all_len_eq_0 unfolding N_def
                      using a00 assum cp by fastforce 
                    then have G_s1':"( s1',  s1')\<in>G" using a5
                      using k lm_lc1 snd_l_len by fastforce
                    then show "(snd (l!k), snd (l!Suc k)) \<in> G"               
                      proof -
                        have "snd (l!Suc k) =  s1'" 
                          using lm_lc1 suck by fastforce                                
                        then show ?thesis using suck k G_s1'
                          using snd_l_len by auto 
                           
                      qed
                    }
                  next
                  { 
                    assume a001:"Suc k>?lm_lc1"
                    have "\<forall>i. i\<ge>(length lc1) \<and> (Suc i < length l) \<longrightarrow> 
                            \<not>(\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                              (fst (l ! Suc i), toSeq (snd (l ! Suc i))))"
                    using lm_lc1 lc1_not_empty
                    proof -
                      have "env_tran_right \<Gamma> l R"
                        by (metis  env_tran_right)
                      then show ?thesis
                        by (metis a00 a001 a21 asm0 cp fst_conv less_Suc_eq_le lm_lc1 
                              only_one_component_tran_j)
                    qed
                    then have "\<not>(\<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                                (fst (l ! Suc k), toSeq (snd (l ! Suc k))))"
                      using a00 a001  by auto                    
                    then show ?thesis using a21 by fastforce                    
                  }
                  qed 
                qed
              } thus ?thesis by auto 
             qed 
             have concr:"(final_glob (last l)  \<longrightarrow>  fst (last l) \<notin> Fault ` F \<longrightarrow>                       
                   ((fst (last l) = Skip \<and> snd (last l) \<in>  r)) \<or>
                    (fst (last l) = Throw \<and> snd (last l) \<in>  a))" 
             proof -
             { assume a00:"final_glob (last l)" and a01:"fst (last l) \<notin> Fault ` F"
               have "?lm_lc1 \<le> length l -1" using cpn_lc1
                 by (metis (no_types, lifting) One_nat_def Suc_diff_Suc add_diff_cancel_left' 
                   append_is_Nil_conv diff_zero length_append length_greater_0_conv less_Suc_eq_le
                   list.simps(3) zero_less_diff) 
                have last_lc1:"snd (last lc1) =  s1'" 
                 using last_length l_map lm_lc1 last_m_lc1 last_lc1_suc asm0
                 by (metis snd_conv)  
               have "final_glob (last lc1)" 
                 using l_map last_lc1 asm0 last_lc1_suc last_m_lc1 local.last_length
                 unfolding final_glob_def                 
                 by auto                 
               moreover have "fst (last lc1) \<notin> Fault ` F" 
                  using last_lc1
                  using a01 l_map last_lc1_suc last_m_lc1 local.last_length by auto
               ultimately have h:"fst (last lc1) = Skip \<and> snd (last lc1) \<in> q \<or>
                                 fst (last lc1) = Throw \<and> snd (last lc1) \<in> a" 
                 using lc1_comm  unfolding comm_def by force
               { assume "fst (last l) = com.Stuck \<or> (\<exists>f. fst (last l) = com.Fault f)"
                 then have ?thesis using h
                   using l_map last_lc1_suc last_m_lc1 local.last_length by auto                   
               }
               moreover { 
                 assume a00:"fst (last l) = Throw"               
                 have "?lm_lc1 \<le> length l -1" using cpn_lc1
                   by (metis (no_types, lifting) One_nat_def Suc_diff_Suc add_diff_cancel_left' 
                   append_is_Nil_conv diff_zero length_append length_greater_0_conv less_Suc_eq_le
                   list.simps(3) zero_less_diff) 
                 have a_normal:"snd (l!?lm_lc1) \<in> a" using h
                   using a00 l_map last_lc1_suc last_m_lc1 local.last_length by auto                 
                 then have "snd (l ! (length l - 1)) \<in>  a"
                   using  cp  a4  fst_conv  lm_lc1 snd_conv 
                         env_tran_right a00    cp a_normal a4  fst_conv  lm_lc1 snd_conv 
                         env_tran_right i_throw_all_throw[of  \<Gamma> l ?lm_lc1 s1' "(length l -1)" R a ]
                   using cpn_lc1 by auto                               
                 then have ?thesis
                   by (metis a00 append_is_Nil_conv cpn_lc1 last_conv_nth list.distinct(1))
               }
               ultimately have ?thesis using asm0 by auto 
             } thus ?thesis by auto
             qed
             note res = conjI [OF concl concr]
             then show ?thesis using  \<Gamma>1 c_prod unfolding comm_def by auto
           qed                  
         next
           case False
           then obtain lc1 where cpn_lc1:"(\<Gamma>,lc1) \<in> cpn n \<Gamma> c1 s \<and> l = map (lift c2) lc1" 
             using Seq_sound1 assum False no_c2 env_tran_right cptn_nest cptn_eq_cptn_mod_set a4 a1 
             by blast          
           then have cp_lc1:"(\<Gamma>,lc1) \<in> cp \<Gamma> c1 s "
             using  cptn_if_cptn_mod cptn_mod_nest_cptn_mod cptn_eq_cptn_mod_nest
             unfolding cp_def cpn_def  by blast                          
           then have "((\<Gamma>,lc1) \<in> assum(p, R))"  
              using \<Gamma>1  cpn_lc1 a10' a11 assum_map by blast
           then have "(\<Gamma>, lc1)\<in> comm(G, (q,a)) F" using cpn_lc1 a1
             by (meson IntI com_validityn_def contra_subsetD)
           then have "(\<Gamma>, l)\<in> comm(G, (r,a)) F"
             using comm_map a10' \<Gamma>1 cp_lc1 cpn_lc1 by blast
           then show ?thesis  
             unfolding comm_def by auto
         qed
       next         
         case False 
         then obtain k where k_len:"k<length l \<and> fst (l ! k) = c2"
           by blast         
         then have "\<exists>m. (m < length l \<and> fst (l ! m) = c2) \<and>
                   (\<forall>i<m. \<not> (i < length l \<and> fst (l ! i) = c2))"   
           using a0 exists_first_occ[of "(\<lambda>i. i<length l  \<and> fst (l ! i) = c2)" k] 
           by blast
         then obtain i where a0:"i<length l \<and> fst (l !i) = c2 \<and>
                                (\<forall>j<i. (fst (l ! j) \<noteq> c2))"
           by fastforce        
         then obtain s2 where li:"l!i =(c2,s2)" by (meson eq_fst_iff)
         then obtain lc1 lc2 where cp_lc1:"(\<Gamma>,lc1) \<in> (cpn n \<Gamma> c1 s) \<and> 
                                 (\<Gamma>,lc2) \<in> (cpn n \<Gamma> c2 (snd (lc1!(i-1)))) \<and> 
                                 l = (map (lift c2) lc1)@lc2"
           using Seq_sound4[of n \<Gamma> l c1 c2 s] a0 env_tran_right a4 a1 cptn_nest assum by blast  
         then have cp_lc1':"(\<Gamma>,lc1) \<in> (cp  \<Gamma> c1 s) \<and> 
                    (\<Gamma>,lc2) \<in> (cp  \<Gamma> c2 (snd (lc1!(i-1))))"
           unfolding cp_def cpn_def cptn_eq_cptn_mod_nest by fastforce
         (* have "\<forall>i < length l. fst (l!i) \<notin> Fault ` F"
           using cp  last_not_F[of \<Gamma> l F] sorry by auto  
         then have i_not_fault:"fst (l!i) \<notin> Fault ` F" using a0 by blast *)
         have length_c1_map:"length lc1 = length (map (lift c2) lc1)" 
           by fastforce      
         then have i_map:"i=length lc1" 
           using cp_lc1 li a0 unfolding lift_def
         proof -
           assume a1: "(\<Gamma>, lc1) \<in> cpn n \<Gamma> c1 s \<and> (\<Gamma>, lc2) \<in> cpn n \<Gamma> c2 (snd (lc1 ! (i - 1))) \<and> 
                        l = map (\<lambda>(P, s). (LanguageCon.com.Seq P c2, s)) lc1 @ lc2"
            have f2: "i < length l \<and> fst (l ! i) = c2 \<and> (\<forall>n. \<not> n < i \<or> fst (l ! n) \<noteq> c2)"
              using a0 by blast
            have f3: "(LanguageCon.com.Seq (fst (lc1 ! i)) c2, snd (lc1 ! i)) = lift c2 (lc1 ! i)"
              by (simp add: case_prod_unfold lift_def)            
            then have "fst (l ! length lc1) = c2"
              using a1 by (simp add: cpn_def nth_append)
            thus ?thesis
              using f3 f2 by (metis (no_types) nth_append cp_lc1 
                 fst_conv length_map lift_nth linorder_neqE_nat seq_and_if_not_eq(4))
         qed                  
         have lc2_l:"\<forall>j<length lc2. lc2!j=l!(i+j)"
           using cp_lc1 length_c1_map i_map a0
           by (metis nth_append_length_plus)                                                             
         have lc1_not_empty:"lc1 \<noteq> []"
           using cp cp_lc1 unfolding cpn_def by fastforce      
         have lc2_not_empty:"lc2 \<noteq> []"
           using a0 cp_lc1 i_map by auto                      
         have l_is:"s2= snd (last lc1)"
         using cp_lc1 li a0 lc1_not_empty i_map unfolding cpn_def
         by (auto simp add: last_conv_nth lc2_l)       
         let ?m_lc1 = "map (lift c2) lc1"
         (* let ?lm_lc1 = "(length ?m_lc1)"
         let ?last_m_lc1 = "?m_lc1!(?lm_lc1-1)" *)                         
         have last_m_lc1:"l!(i-1) = (Seq (fst (last lc1)) c2,s2)"
         proof -
           have a000:"\<forall>p c. (LanguageCon.com.Seq (fst p) c, snd p) = lift c p"
             using Cons_lift by force
           have "length (map (lift c2) lc1) = i"
               using i_map by fastforce
           then show ?thesis
             by (metis (no_types) One_nat_def l_is a000 cp_lc1 diff_less last_conv_nth last_map 
            lc1_not_empty length_c1_map length_greater_0_conv less_Suc0 nth_append)                       
         qed  
         (* have last_mcl1_not_F:"fst (last ?m_lc1) \<notin> Fault ` F"                 
         proof -
          have "map (lift c2) lc1 \<noteq> []"
            by (metis lc1_not_empty list.map_disc_iff)
          then show ?thesis sorry
            by (metis (full_types) One_nat_def  l_is last_conv_nth last_snd lc1_not_empty li snd_conv)
         qed *)        
         have map_cp:"(\<Gamma>,?m_lc1) \<in> cpn n \<Gamma> (Seq c1 c2) s"               
         proof -
           have f1: "lc1 ! 0 = (c1, s) \<and> (n,\<Gamma>, lc1) \<in> cptn_mod_nest_call \<and> \<Gamma> = \<Gamma>"
             using cp_lc1 cpn_def by blast
           then have f2: "(n,\<Gamma>, ?m_lc1) \<in> cptn_mod_nest_call" using lc1_not_empty
             by (metis Cons_lift SmallStepCon.nth_tl cptn_mod_nest_call.CptnModNestSeq1)
           then show ?thesis
             using f2 f1 lc1_not_empty by (simp add: cpn_def lift_def)
         qed
         then have map_cp':"(\<Gamma>,?m_lc1) \<in> cp \<Gamma> (Seq c1 c2) s"
           unfolding cpn_def cp_def
           using cptn_eq_cptn_mod_nest by fastforce
         also have map_assum:"(\<Gamma>,?m_lc1) \<in> assum (p,R)" 
           using sub_assum a10 a11 \<Gamma>1 cp_lc1 lc1_not_empty 
           by (metis SmallStepCon.nth_tl map_is_Nil_conv)
         ultimately have "((\<Gamma>,lc1) \<in> assum(p, R))"  
           using \<Gamma>1 assum_map using assum_map cp_lc1' by blast                          
         then have lc1_comm:"(\<Gamma>,lc1) \<in> comm(G, (q,a)) F"  
           using a1 cp_lc1 by (meson IntI com_validityn_def contra_subsetD)
         then have m_lc1_comm:"(\<Gamma>,?m_lc1) \<in> comm(G, (q,a)) F"
           using map_cp' map_assum comm_map cp_lc1' by fastforce         
         then have i_step:"(\<Gamma>\<turnstile>\<^sub>c (fst (l ! (i-1)), toSeq (snd (l ! (i-1)))) \<rightarrow> 
                           (fst (l ! i), toSeq (snd (l ! i))))"
         proof -
           have "\<Gamma>\<turnstile>\<^sub>c(l!(i-1)) \<rightarrow>\<^sub>c\<^sub>e (l!(i))"
           proof -
             have f1: "\<forall>n na. \<not> n < na \<or> Suc (na - Suc n) = na - n"
               by (meson Suc_diff_Suc)
             have "map (lift c2) lc1 \<noteq> []"
               by (metis lc1_not_empty map_is_Nil_conv)
             then have f2: "0 < length (map (lift c2) lc1)"
               by (meson length_greater_0_conv)             
             then have "length (map (lift c2) lc1) - 1 + 1 < length (map (lift c2) lc1 @ lc2)"
               using f2 lc2_not_empty by simp
             then show ?thesis
             using f2 f1
              proof -
                have "0 < i"
                  using f2 i_map by blast
                then show ?thesis
                  by (metis (no_types) One_nat_def Suc_diff_1 a0 add.right_neutral add_Suc_right cp cptn_tran_ce_i)
              qed 
           qed 
           moreover have "\<not>\<Gamma>\<turnstile>\<^sub>c(l!(i-1)) \<rightarrow>\<^sub>e (l!i)"           
             using li last_m_lc1
             by (metis (no_types, lifting) env_c_c' seq_and_if_not_eq(4))
           ultimately show ?thesis using step_ce_dest
             by (metis prod.exhaust_sel)
         qed         
         then have step:"\<Gamma>\<turnstile>\<^sub>c(Seq (fst (last lc1)) c2,toSeq s2) \<rightarrow> (c2, toSeq s2)"
           using last_m_lc1  li by fastforce
         then have
           last_lc1:"fst (last lc1) = Skip \<or> 
            fst (last lc1) = Throw \<or> fst (last lc1) = Stuck \<or> (\<exists>f. fst(last lc1) = Fault f)" 
           using seq_skip_throw 
           by (simp add: seq_skip_throw)    
         have final:"final_glob (last lc1)" 
           using last_lc1 l_is unfolding final_glob_def by fastforce
         have Gs2':"(s2, s2)\<in>G" using a5 unfolding N_def
           by (metis (mono_tags, lifting) a0 assum cp cptn_all_len_eq_0 li mem_Collect_eq snd_conv)                     
         have concl:
           "(\<forall>i. Suc i<length l \<longrightarrow> 
             (\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                  (fst (l ! Suc i), toSeq (snd (l ! Suc i)))) \<longrightarrow>                                    
             (snd(l!i), snd(l!(Suc i))) \<in> G)"
         proof-
         { fix k 
           assume a00:"Suc k<length l" and
            a21:"\<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                    (fst (l ! Suc k), toSeq (snd (l ! Suc k)))" 
            have i_m_l:"\<forall>j <i . l!j = ?m_lc1!j"             
            proof -
              have "map (lift c2) lc1 \<noteq> []"
                by (meson lc1_not_empty list.map_disc_iff)
              then show ?thesis 
                using cp_lc1 i_map length_c1_map by (fastforce simp:nth_append)              
            qed 
            have "(snd(l!k), snd(l!(Suc k))) \<in> G"
            proof (cases "Suc k< i")
              case True 
              then have a11': "(\<Gamma>\<turnstile>\<^sub>c (fst (?m_lc1 ! k), toSeq (snd (?m_lc1 ! k))) \<rightarrow> 
                                    (fst (?m_lc1 ! Suc k), toSeq (snd (?m_lc1 ! Suc k))))" 
                using a11 i_m_l True
              proof -
                have "\<forall>n na. \<not> 0 < n - Suc na \<or> na < n "
                  using diff_Suc_eq_diff_pred zero_less_diff by presburger
                then show ?thesis using True a21 i_m_l by force                  
              qed                                                             
              have "Suc k < length ?m_lc1" using True i_map length_c1_map by metis
              then have "(snd(?m_lc1!k), snd(?m_lc1!(Suc k))) \<in> G"              
                using a11' comm_dest1 m_lc1_comm by blast                
              thus ?thesis using i_m_l using True by fastforce 
            next
              case False                                            
              have "(Suc k=i) \<or> (Suc k>i)" using False by auto
              thus ?thesis 
              proof
              { assume suck:"(Suc k=i)" 
                then have k:"k=i-1" by auto                                                            
                then show "(snd (l!k), snd (l!Suc k)) \<in> G"
                  using Gs2' last_m_lc1 li suck by auto
              }
              next
              { 
                assume a001:"Suc k>i"
                then have k:"k\<ge>i" by fastforce
                then obtain k' where k':"k=i+k'" 
                  using add.commute le_Suc_ex by blast               
                {assume throw:"c2=Throw \<or> c2 = Stuck \<or> (\<exists>f. c2 = Fault f)"
                                 
                  have "\<forall>k. k\<ge>i \<and> (Suc k < length l) \<longrightarrow> 
                            \<not>(\<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                                  (fst (l ! Suc k), toSeq (snd (l ! Suc k))))"
                    using li  a21 a001 a00 a4
                        a0 throw  only_one_component_tran_j snd_conv
                    using cp by blast                           
                  then have ?thesis using a21 a001 k a00 by blast                                  
                }  note left=this
                {assume "\<not>(c2=Throw \<or> c2 = Stuck \<or> (\<exists>f. c2 = Fault f))"
                 then have skip:"fst (last lc1) = Skip"
                   using last_m_lc1 last_lc1 step a0 l_is li
                   by (meson stepc_elim_cases_Seq_skip_c2)       
                 then have s2_normal:"s2 \<in>  q" 
                   using l_is li final comm_dest2 lc1_comm by fastforce
                 have length_lc2:"length l=i+length lc2" 
                       using i_map cp_lc1 by fastforce
                 have "(\<Gamma>,lc2) \<in>  assum (q,R)" 
                 proof -
                   have left:"snd (lc2!0) \<in>  q" 
                     using li lc2_l s2_normal lc2_not_empty by fastforce 
                   {
                     fix j
                     assume j_len:"Suc j<length lc2" and
                            j_step:"\<Gamma>\<turnstile>\<^sub>c(lc2!j)  \<rightarrow>\<^sub>e (lc2!(Suc j))"
                     
                     then have suc_len:"Suc (i + j)<length l" using j_len length_lc2
                       by fastforce
                     also then have "\<Gamma>\<turnstile>\<^sub>c(l!(i+j))  \<rightarrow>\<^sub>e (l! (Suc (i+ j)))"
                        using lc2_l j_step j_len by fastforce
                     ultimately have "(snd(lc2!j), snd(lc2!(Suc j))) \<in> R"
                        using assum suc_len lc2_l j_len cp by fastforce 
                   }
                   then show ?thesis using left 
                     unfolding assum_def by fastforce
                 qed
                 also have "(\<Gamma>,lc2) \<in> cpn n \<Gamma> c2 s2"
                   using cp_lc1 i_map l_is last_conv_nth lc1_not_empty by fastforce                 
                 ultimately have comm_lc2:"(\<Gamma>,lc2) \<in>  comm (G, (r,a)) F"
                   using a3 unfolding com_validityn_def by blast
                 (* have lc2_last_f:"fst (last lc2)\<notin> Fault ` F" 
                   using lc2_l lc2_not_empty l_f cp_lc1 by fastforce *)
                 have suck':"Suc k' < length lc2" 
                   using k' a00 length_lc2 by arith
                 moreover then have "(\<Gamma>\<turnstile>\<^sub>c (fst (lc2 ! k'), toSeq (snd (lc2 ! k'))) \<rightarrow> 
                                          (fst (lc2 ! Suc k'), toSeq (snd (lc2 ! Suc k'))))"   
                   using k' lc2_l a21 by fastforce
                 ultimately have "(snd (lc2! k'), snd (lc2 ! Suc k')) \<in> G"
                   using comm_lc2  comm_dest1[of \<Gamma> lc2 G r a F k'] 
                   by blast
                 then have ?thesis using suck' lc2_l k' by fastforce
                }                    
                then show ?thesis using left by auto                 
              }
              qed 
            qed
          } thus ?thesis by auto 
         qed note left=this
         have right:"final_glob (last l)  \<longrightarrow> fst (last l) \<notin> Fault ` F \<longrightarrow>
                    (fst (last l) = Skip \<and> snd (last l) \<in> r) \<or>
                    (fst (last l) = Throw \<and> snd (last l) \<in> a)"
         proof -
         { assume final_l:"final_glob (last l)" and a002:"fst (last l) \<notin> Fault ` F"
           have eq_last_lc2_l:"last l=last lc2" by (simp add: cp_lc1 lc2_not_empty)
           then have final_lc2:"final_glob (last lc2)" using final_l by auto
           {
             assume lst_lc1_throw:"fst (last lc1) = Throw"                        
             then have c2_throw:"c2 = Throw" 
               using lst_lc1_throw step  stepc_elim_cases_Seq_skip_c2
               by fastforce                                                                  
             have s2_a:"s2 \<in> (a)" using lst_lc1_throw lc1_comm unfolding comm_def split_beta
               using final l_is by auto
             have all_ev:"\<forall>k<length l - 1. k\<ge>i \<and> (Suc k < length l) \<longrightarrow> 
                            \<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))"
             proof -
                have "\<forall>k. k\<ge>i \<and> (Suc k < length l) \<longrightarrow> 
                            \<not>(\<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                                  (fst (l ! Suc k), toSeq (snd (l ! Suc k))))"
                 using s2_a li   a4 a0 c2_throw  only_one_component_tran_j  
                 by (metis  cp)  
               thus ?thesis using Suc_eq_plus1 cp cptn_tran_ce_i step_ce_dest
                 by (metis prod.exhaust_sel)      
             qed    
             then have Throw:"fst (l!(length l - 1)) = Throw"
             using cp c2_throw a0 cptn_i_env_same_prog[of \<Gamma> l "((length l)-1)" i] 
               by fastforce                            
             then have "snd (l!(length l - 1)) \<in> a \<and> fst (l!(length l - 1)) = Throw"
               using  all_ev a0 s2_a li a4 env_tran_right stability[of a R l i "(length l) -1" _ \<Gamma>] Throw
               using c2_throw by fastforce                            
             then have "((fst (last l) = Skip \<and> snd (last l) \<in> r)) \<or> 
                       (fst (last l) = Throw \<and> snd (last l) \<in> a)" 
              using a0 by (metis last_conv_nth list.size(3) not_less0)                           
           } 
           moreover {  
             assume "fst (last lc1) = Skip"                 
             then have s2_normal:"s2 \<in>  q"  
               using lc1_comm unfolding comm_def split_beta
               using final l_is by auto
             have length_lc2:"length l=i+length lc2" 
               using i_map cp_lc1 by fastforce
             have "(\<Gamma>,lc2) \<in>  assum (q,R)" 
             proof -
               have left:"snd (lc2!0) \<in>  q" 
                  using li lc2_l s2_normal lc2_not_empty by fastforce               
               {
                 fix j
                 assume j_len:"Suc j<length lc2" and
                      j_step:"\<Gamma>\<turnstile>\<^sub>c(lc2!j)  \<rightarrow>\<^sub>e (lc2!(Suc j))"                 
                 then have suc_len:"Suc (i + j)<length l" using j_len length_lc2
                   by fastforce
                 also then have "\<Gamma>\<turnstile>\<^sub>c(l!(i+j))  \<rightarrow>\<^sub>e (l! (Suc (i+ j)))"
                   using lc2_l j_step j_len by fastforce
                 ultimately have "(snd(lc2!j), snd(lc2!(Suc j))) \<in> R"
                   using assum suc_len lc2_l j_len cp by fastforce 
               }
               then show ?thesis using left 
                 unfolding assum_def by fastforce
            qed
            also have "(\<Gamma>,lc2) \<in> cpn n \<Gamma> c2 s2"
              using cp_lc1 i_map l_is last_conv_nth lc1_not_empty by fastforce
            ultimately have comm_lc2:"(\<Gamma>,lc2) \<in>  comm (G, (r,a)) F"
              using a3 unfolding com_validityn_def split_beta by blast              
            have lc2_last_f:"fst (last lc2)\<notin> Fault ` F" 
              using lc2_l lc2_not_empty cp_lc1
              using a002 by auto             
            then have "((fst (last lc2) = Skip \<and> snd (last lc2) \<in>  r)) \<or>
                    (fst (last lc2) = Throw \<and> snd (last lc2) \<in> a)" 
              using final_lc2 comm_lc2 unfolding comm_def by auto
            then have "((fst (last l) = Skip \<and> snd (last l) \<in> r)) \<or>
                    (fst (last l) = Throw \<and> snd (last l) \<in> a)" 
              using eq_last_lc2_l by auto
           }
           moreover{
             assume "fst (last lc1) = Stuck"             
             then have  "((fst (last l) = Skip \<and> snd (last l) \<in> r)) \<or>
                       (fst (last l) = Throw \<and> snd (last l) \<in>  a)"
               by (metis (no_types) com.distinct(13) com.distinct(145) 
                   com.distinct(147) comm_des3 final image_iff lc1_comm)            
           }
           moreover { 
             assume "(\<exists>f. fst (last lc1) = Fault f)"
             then have  "((fst (last l) = Skip \<and> snd (last l) \<in> r)) \<or>
                       (fst (last l) = Throw \<and> snd (last l) \<in>  a)"
               by (metis LanguageCon.com.distinct(171) LanguageCon.com.distinct(19) a002 
                    comm_dest2 cp final k_len last_not_F lc1_comm step stepc_elim_cases_Seq_skip_c2)              
           }
           ultimately have "((fst (last l) = Skip \<and> snd (last l) \<in> r)) \<or>
                    (fst (last l) = Throw \<and> snd (last l) \<in>  a)" 
             using last_lc1 by blast
         } 
         thus ?thesis by auto qed              
      thus ?thesis using left  \<Gamma>1 unfolding comm_def by force
      qed
    } thus ?thesis using \<Gamma>1 unfolding comm_def by auto qed
  } thus ?thesis by auto qed 
} thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed

lemma Catch_env_P:assumes 
  a0:"\<Gamma>\<turnstile>\<^sub>c(Catch P Q,s) \<rightarrow>\<^sub>e (Catch P Q,t)"
      shows "\<Gamma>\<turnstile>\<^sub>c(P,s) \<rightarrow>\<^sub>e (P,t)"
  using a0 
  by (metis env_intro_diff_p) 

lemma map_catch_eq_state:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Catch c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) " and
  a2:"l1=map (lift_catch c2) l2"
shows
  "\<forall>i<length l1. snd (l1!i) = snd (l2!i)"
using a0 a1 a2 unfolding cp_def
by (simp add: snd_lift_catch) 

lemma map_eq_catch_c:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Catch c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) " and
  a2:"l1=map (lift_catch c2) l2"
shows
  "\<forall>i<length l1. fst (l1!i) = Catch (fst (l2!i)) c2"
proof -
  {fix i
  assume a3:"i<length l1"
  have "fst (l1!i) = Catch (fst (l2!i)) c2"
  using a0 a1 a2 a3 unfolding lift_catch_def
    by (simp add: case_prod_unfold) 
  }thus ?thesis by auto
qed 

lemma same_env_catch_c:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Catch c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) " and
  a2:"l1=map (lift_catch c2) l2"
shows
"\<forall>i. Suc i<length l2 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l2!i)  \<rightarrow>\<^sub>e (l2!(Suc i)) = 
            \<Gamma>\<turnstile>\<^sub>c(l1!i)  \<rightarrow>\<^sub>e (l1!(Suc i))" 
proof -
  have a0a:"(\<Gamma>,l1) \<in>cptn \<and> l1!0 = ((Catch c1 c2),s)" 
    using a0 unfolding cp_def by blast
  have a1a: "(\<Gamma>,l2) \<in>cptn \<and> l2!0 = (c1,s)"
    using a1 unfolding cp_def by blast
  {
    fix i
    assume a3:"Suc i< length l2"
    have "\<Gamma>\<turnstile>\<^sub>c(l2!i)  \<rightarrow>\<^sub>e (l2!(Suc i)) = 
            \<Gamma>\<turnstile>\<^sub>c(l1!i)  \<rightarrow>\<^sub>e (l1!(Suc i))"
    proof
    {
      assume a4:"\<Gamma>\<turnstile>\<^sub>c l2 ! i \<rightarrow>\<^sub>e l2 ! Suc i"
      obtain c1i s1i c1si s1si where l1prod:"l1 ! i=(c1i,s1i) \<and> l1!Suc i = (c1si,s1si)"
        using prod.exhaust_sel by blast
      obtain c2i s2i c2si s2si where l2prod:"l2 ! i=(c2i,s2i) \<and> l2!Suc i = (c2si,s2si)"
        by (meson prod.exhaust_sel)
      then have "c1i = (Catch c2i c2) \<and> c1si = (Catch c2si c2)"
        using  a0 a1 a2 a3 a4  l1prod 
        by (simp add: lift_catch_def)         
      also have "s2i=s1i \<and> s2si=s1si"
        using  a0 a1 a4  a2 a3 l2prod  l1prod
        by (simp add: lift_catch_def)         
      ultimately show "\<Gamma>\<turnstile>\<^sub>c l1 ! i \<rightarrow>\<^sub>e (l1 ! Suc i)" 
        using a4 l1prod l2prod
        by (metis env_c_c' env_intro_diff_p)
    } 
    {
      assume a4:"\<Gamma>\<turnstile>\<^sub>c l1 ! i \<rightarrow>\<^sub>e l1 ! Suc i"
      obtain c1i s1i c1si s1si where l1prod:"l1 ! i=(c1i,s1i) \<and> l1!Suc i = (c1si,s1si)"
        using prod.exhaust_sel by blast
      obtain c2i s2i c2si s2si where l2prod:"l2 ! i=(c2i,s2i) \<and> l2!Suc i = (c2si,s2si)"
        by (meson prod.exhaust_sel)
      then have "c1i = (Catch c2i c2) \<and> c1si = (Catch c2si c2)"
        using  a0 a1 a2 a3 a4  l1prod
        by (simp add: lift_catch_def)
      also have "s2i=s1i \<and> s2si=s1si"
        using  a0 a1 a4  a2 a3 l2prod l1prod
        by (simp add: lift_catch_def)      
      ultimately show "\<Gamma>\<turnstile>\<^sub>c l2 ! i \<rightarrow>\<^sub>e (l2 ! Suc i)" 
        using a4 l1prod l2prod   env_intro
        by (metis LanguageCon.com.inject(10) env_c_c' env_intro_diff_p)
    }
    qed
   } 
  thus ?thesis by auto
qed


lemma same_comp_catch_c:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Catch c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) " and
  a2:"l1=map (lift_catch c2) l2"
shows
"\<forall>i. Suc i<length l2 \<longrightarrow> 
        \<Gamma>\<turnstile>\<^sub>c (fst (l2 ! i), toSeq (snd (l2 ! i))) \<rightarrow> 
            (fst (l2 ! Suc i), toSeq (snd (l2 ! Suc i)))  = 
      \<Gamma>\<turnstile>\<^sub>c (fst (l1 ! i), toSeq (snd (l1 ! i))) \<rightarrow> 
            (fst (l1 ! Suc i), toSeq (snd (l1 ! Suc i)))" 
proof -
  have a0a:"(\<Gamma>,l1) \<in>cptn \<and> l1!0 = ((Catch c1 c2),s)" 
    using a0 unfolding cp_def by blast
  have a1a: "(\<Gamma>,l2) \<in>cptn \<and> l2!0 = (c1,s)"
    using a1 unfolding cp_def by blast
  {
    fix i
    assume a3:"Suc i< length l2"
    have "\<Gamma>\<turnstile>\<^sub>c (fst (l1 ! i), toSeq (snd (l1 ! i))) \<rightarrow> 
            (fst (l1 ! Suc i), toSeq (snd (l1 ! Suc i))) =
       \<Gamma>\<turnstile>\<^sub>c (fst (l2 ! i), toSeq (snd (l2 ! i))) \<rightarrow> 
            (fst (l2 ! Suc i), toSeq (snd (l2 ! Suc i)))"
    proof
    {
      assume a4:"\<Gamma>\<turnstile>\<^sub>c (fst (l2 ! i), toSeq (snd (l2 ! i))) \<rightarrow> 
                (fst (l2 ! Suc i), toSeq (snd (l2 ! Suc i)))"
      obtain c1i s1i c1si s1si where l1prod:"l1 ! i=(c1i,s1i) \<and> l1!Suc i = (c1si,s1si)"
        by (meson prod.exhaust_sel)
      obtain c2i s2i c2si s2si where l2prod:"l2 ! i=(c2i,s2i) \<and> l2!Suc i = (c2si,s2si)"
        using prod.exhaust_sel by blast
      then have "c1i = (Catch c2i c2) \<and> c1si = (Catch c2si c2)"
        using  a0 a1 a2 a3 a4  map_eq_catch_c l1prod
        by (simp add: lift_catch_def)
      also have "s2i=s1i \<and> s2si=s1si"
        using  a0 a1 a4  a2 a3 l2prod map_eq_state l1prod
        by (simp add: lift_catch_def)          
      ultimately show "\<Gamma>\<turnstile>\<^sub>c (fst (l1 ! i), toSeq (snd (l1 ! i))) \<rightarrow> 
            (fst (l1 ! Suc i), toSeq (snd (l1 ! Suc i)))"
        using a4 l1prod l2prod
        by (simp add: Catchc)        
    } 
    {
      assume a4:"\<Gamma>\<turnstile>\<^sub>c (fst (l1 ! i), toSeq (snd (l1 ! i))) \<rightarrow> 
            (fst (l1 ! Suc i), toSeq (snd (l1 ! Suc i)))"
      obtain c1i s1i c1si s1si where l1prod:"l1 ! i=(c1i,s1i) \<and> l1!Suc i = (c1si,s1si)"
        using prod.exhaust_sel by blast
      obtain c2i s2i c2si s2si where l2prod:"l2 ! i=(c2i,s2i) \<and> l2!Suc i = (c2si,s2si)"
        by (meson prod.exhaust_sel)
      then have "c1i = (Catch c2i c2) \<and> c1si = (Catch c2si c2)"
        using  a0 a1 a2 a3 a4  l1prod
       by (simp add: lift_catch_def)          
      also have "s2i=s1i \<and> s2si=s1si"
        using  a0 a1 a4  a2 a3 l2prod  l1prod
        by (simp add: lift_catch_def)          
      ultimately show "\<Gamma>\<turnstile>\<^sub>c (fst (l2 ! i), toSeq (snd (l2 ! i))) \<rightarrow> 
                (fst (l2 ! Suc i), toSeq (snd (l2 ! Suc i)))"
        using a4 l1prod l2prod stepc_elim_cases_Catch_Catch 
        by auto
    }
    qed
   } 
  thus ?thesis by auto
qed

lemma assum_map_catch:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Catch c1 c2) s) \<and> ((\<Gamma>,l1) \<in> assum(p, R))" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) " and
  a2:"l1=map (lift_catch c2) l2"  
shows
  "((\<Gamma>,l2) \<in> assum(p, R))"
proof -
  have a3: "\<forall>i. Suc i<length l2 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c(l2!i)  \<rightarrow>\<^sub>e (l2!(Suc i)) = 
            \<Gamma>\<turnstile>\<^sub>c(l1!i)  \<rightarrow>\<^sub>e (l1!(Suc i))" 
    using a0 a1 a2 same_env_catch_c by fastforce
  have pair_\<Gamma>l1:"fst (\<Gamma>,l1) = \<Gamma> \<and> snd (\<Gamma>,l1) = l1" by fastforce
  have pair_\<Gamma>l2:"fst (\<Gamma>,l2) = \<Gamma> \<and> snd (\<Gamma>,l2) = l2" by fastforce
  have drop_k_s:"l2!0 = (c1,s)" using a1 cp_def by blast
  have eq_length:"length l1 = length l2" using a2 by auto
  then have p1:"s\<in>p" using a0 unfolding cp_def assum_def by fastforce  
  show ?thesis 
  proof -    
    let ?c= "(\<Gamma>,l2)"
    have l:"snd((snd ?c!0)) \<in> p"     
      using p1 drop_k_s a1  unfolding cp_def by auto
    { fix i
      assume a00:"Suc i<length (snd ?c)" 
      assume a11:"(fst ?c)\<turnstile>\<^sub>c((snd ?c)!i)  \<rightarrow>\<^sub>e ((snd ?c)!(Suc i))"
      have "(snd((snd ?c)!i), snd((snd ?c)!(Suc i))) \<in> R"
        using a0 a1 a2 a3 map_catch_eq_state unfolding assum_def split_beta
        using a00 a11 eq_length
        by (auto simp add: snd_lift_catch)
    } thus "(\<Gamma>, l2) \<in> assum (p, R)" 
      using l unfolding assum_def by fastforce  
  qed  
qed

lemma comm_map'_catch:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Catch c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) \<and> (\<Gamma>, l2)\<in> comm(G, (q,a)) F" and
  a2:"l1=map (lift_catch c2) l2" 
shows
  "(Suc k < length l1 \<longrightarrow>
        \<Gamma>\<turnstile>\<^sub>c (fst (l1 ! k), toSeq (snd (l1 ! k))) \<rightarrow> 
                (fst (l1 ! Suc k), toSeq (snd (l1 ! Suc k))) \<longrightarrow>        
       (snd(l1!k), snd(l1!(Suc k))) \<in> G) \<and> 
   (fst (last l1) = (Catch c c2) \<and> final_glob (c, snd (last l1)) \<longrightarrow> c \<notin> Fault ` F  \<longrightarrow>   
      (fst (last l1) = (Catch Skip c2) \<and> 
        (snd (last  l1) \<in>  q) \<or>
      (fst (last l1) = (Catch Throw c2) \<and> 
        snd (last l1) \<in> a)))
     "
proof -
  have a3:"\<forall>i. Suc i<length l2 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c (fst (l2 ! i), toSeq (snd (l2 ! i))) \<rightarrow> 
                (fst (l2 ! Suc i), toSeq (snd (l2 ! Suc i))) = 
            \<Gamma>\<turnstile>\<^sub>c (fst (l1 ! i), toSeq (snd (l1 ! i))) \<rightarrow> 
                (fst (l1 ! Suc i), toSeq (snd (l1 ! Suc i)))" 
    using a0 a1 a2 same_comp_catch_c
    by fastforce
  have pair_\<Gamma>l1:"fst (\<Gamma>,l1) = \<Gamma> \<and> snd (\<Gamma>,l1) = l1" by fastforce
  have pair_\<Gamma>l2:"fst (\<Gamma>,l2) = \<Gamma> \<and> snd (\<Gamma>,l2) = l2" by fastforce
  have drop_k_s:"l2!0 = (c1,s)" using a1 cp_def by blast
  have eq_length:"length l1 = length l2" using a2 by auto
  have len0:"length l2>0" using a1 unfolding cp_def 
      using cptn.simps  by fastforce   
  then have len0:"length l1>0" using eq_length by auto
  then have l1_not_empty:"l1\<noteq>[]" by auto
  then have l2_not_empty:"l2 \<noteq> []" using a2 by blast       
   have last_lenl1:"last l1 = l1!((length l1) -1)" 
        using last_conv_nth l1_not_empty by auto
  have last_lenl2:"last l2 = l2!((length l2) -1)" 
       using last_conv_nth l2_not_empty by auto 
  have a03:"(\<forall>i ns ns'.                 
               Suc i<length (snd (\<Gamma>, l2)) \<longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c (fst (l2 ! i), toSeq (snd (l2 ! i))) \<rightarrow> 
                (fst (l2 ! Suc i), toSeq (snd (l2 ! Suc i))) \<longrightarrow>                               
                 (snd((snd (\<Gamma>, l2))!i), snd((snd (\<Gamma>, l2))!(Suc i))) \<in> G) \<and> 
               (final_glob (last (snd (\<Gamma>, l2)))  \<longrightarrow> fst (last l2) \<notin> Fault ` F  \<longrightarrow>               
                  ((fst (last (snd (\<Gamma>, l2))) = Skip \<and> 
                    snd (last (snd (\<Gamma>, l2))) \<in> q)) \<or>
                  (fst (last (snd (\<Gamma>, l2))) = Throw \<and> 
                    snd (last (snd (\<Gamma>, l2))) \<in> a ))"
  using a1 unfolding comm_def by fastforce
  show ?thesis unfolding comm_def 
  proof -
  { fix k ns ns'    
    assume a00:"Suc k < length l1"    
    then have "k \<le> length l1" using a2 by fastforce    
    have a00:"Suc k < length l2" using eq_length a00 by fastforce
    then have "\<Gamma>\<turnstile>\<^sub>c (fst (l1 ! k), toSeq (snd (l1 ! k))) \<rightarrow> 
                (fst (l1 ! Suc k), toSeq (snd (l1 ! Suc k))) \<longrightarrow>       
      (snd((snd (\<Gamma>, l1))!k), snd((snd (\<Gamma>, l1))!(Suc k))) \<in> G"
    using  pair_\<Gamma>l1 pair_\<Gamma>l2 a00  a03 a3  eq_length 
     by (metis Suc_lessD a0 a1 a2 map_catch_eq_state)
  } note l=this
  {
    assume a00: "fst (last l1) = (Catch c c2) \<and> final_glob (c, snd (last l1))" and
           a01:"c \<notin> Fault ` F"    
    then have c:"c=Skip \<or> c = Throw \<or> c = Stuck \<or> (\<exists>f. c = Fault f)"
      unfolding final_glob_def by auto    
    then have fst_last_l2:"fst (last l2) = c"                               
      using  last_lenl1 a00 l1_not_empty eq_length len0 a2 last_conv_nth last_lift_catch 
      by fastforce      
    also have last_eq:"snd (last l2) = snd (last l1)"      
      using l2_not_empty a2 last_conv_nth last_lenl1 last_snd_catch
      by fastforce
    ultimately have "final_glob (fst (last l2),snd (last l2))" 
     using a00 by auto
    then have "final_glob (last l2)" by auto
    also have "fst (last (l2)) \<notin> Fault ` F"
       using  last_eq a01 a00 a01 c  
       by (auto simp add: fst_last_l2) 
    ultimately have "(fst (last  l2)) = Skip \<and> 
                    snd (last  l2) \<in>  q \<or>
                  (fst (last l2) = Throw \<and> 
                    snd (last l2) \<in> a)"
    using a03 by auto
    then have "(fst (last l1) = (Catch Skip c2) \<and> snd (last  l1) \<in> q) \<or>
                  (fst (last l1) = (Catch Throw c2) \<and>  snd (last l1) \<in> a)"
    using last_eq fst_last_l2 a00 by force
  }
  thus ?thesis using l by auto qed
qed

lemma comm_map''_catch:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Catch c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) \<and> (\<Gamma>, l2)\<in> comm(G, (q,a)) F" and
  a2:"l1=map (lift_catch c2) l2" 
shows
  " ((Suc k < length l1 \<longrightarrow>
       \<Gamma>\<turnstile>\<^sub>c (fst (l1 ! k), toSeq (snd (l1 ! k))) \<rightarrow> 
            (fst (l1 ! Suc k), toSeq (snd (l1 ! Suc k))) \<longrightarrow>        
       (snd(l1!k), snd(l1!(Suc k))) \<in> G) \<and> 
   (final_glob (last l1) \<longrightarrow> fst (last l1) \<notin> Fault ` F \<longrightarrow>  
      fst (last l1) = Skip \<and> snd (last  l1) \<in>  r \<or>
      fst (last l1) = Throw \<and> snd (last l1) \<in>  (a)))"
proof -
  have a3:"\<forall>i. Suc i<length l2 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c (fst (l2 ! i), toSeq (snd (l2 ! i))) \<rightarrow> 
                (fst (l2 ! Suc i), toSeq (snd (l2 ! Suc i))) = 
            \<Gamma>\<turnstile>\<^sub>c (fst (l1 ! i), toSeq (snd (l1 ! i))) \<rightarrow> 
                (fst (l1 ! Suc i), toSeq (snd (l1 ! Suc i)))" 
    using a0 a1 a2 same_comp_catch_c
    by fastforce
  have pair_\<Gamma>l1:"fst (\<Gamma>,l1) = \<Gamma> \<and> snd (\<Gamma>,l1) = l1" by fastforce
  have pair_\<Gamma>l2:"fst (\<Gamma>,l2) = \<Gamma> \<and> snd (\<Gamma>,l2) = l2" by fastforce
  have drop_k_s:"l2!0 = (c1,s)" using a1 cp_def by blast
   have eq_length:"length l1 = length l2" using a2 by auto
  have len0:"length l2>0" using a1 unfolding cp_def 
      using cptn.simps  by fastforce   
  then have len0:"length l1>0" using eq_length by auto
  then have l1_not_empty:"l1\<noteq>[]" by auto
  then have l2_not_empty:"l2 \<noteq> []" using a2 by blast       
  have last_lenl1:"last l1 = l1!((length l1) -1)" 
        using last_conv_nth l1_not_empty by auto
  have last_lenl2:"last l2 = l2!((length l2) -1)" 
       using last_conv_nth l2_not_empty by auto 
  have a03:"(\<forall>i ns ns'.                 
               Suc i<length (snd (\<Gamma>, l2)) \<longrightarrow> 
               \<Gamma>\<turnstile>\<^sub>c (fst (l2 ! i), toSeq (snd (l2 ! i))) \<rightarrow> 
                (fst (l2 ! Suc i), toSeq (snd (l2 ! Suc i))) \<longrightarrow>                               
                 (snd((snd (\<Gamma>, l2))!i), snd((snd (\<Gamma>, l2))!(Suc i))) \<in> G) \<and> 
               (final_glob (last (snd (\<Gamma>, l2)))  \<longrightarrow>  fst (last l2) \<notin> Fault ` F  \<longrightarrow>              
                  ((fst (last (snd (\<Gamma>, l2))) = Skip \<and> snd (last (snd (\<Gamma>, l2))) \<in>  q)) \<or>
                  (fst (last (snd (\<Gamma>, l2))) = Throw \<and> snd (last (snd (\<Gamma>, l2))) \<in>  (a)))"
  using a1 unfolding comm_def by fastforce
  show ?thesis unfolding comm_def 
  proof -
  { fix k ns ns'   
    assume a00:"Suc k < length l1"    
    then have "k \<le> length l1" using a2 by fastforce    
    have a00:"Suc k < length l2" using eq_length a00 by fastforce      
    then have " \<Gamma>\<turnstile>\<^sub>c (fst (l1 ! k), toSeq (snd (l1 ! k))) \<rightarrow> 
                (fst (l1 ! Suc k), toSeq (snd (l1 ! Suc k))) \<longrightarrow>         
        (snd((snd (\<Gamma>, l1))!k), snd((snd (\<Gamma>, l1))!(Suc k))) \<in> G"
      using  pair_\<Gamma>l1 pair_\<Gamma>l2 a00  a03 a3  eq_length        
      by (metis (no_types,lifting) a2 Suc_lessD nth_map snd_lift_catch)
    } note l= this
    {
     assume a00: "final_glob (last l1)" and  a00a:"fst (last l1) \<notin> Fault ` F"           
     then have c:"fst (last l1)=Skip \<or> fst (last l1) = Throw \<or> 
                  fst (last l1) = Stuck \<or> (\<exists>f. fst (last l1) = Fault f)"
       unfolding final_glob_def by auto 
     moreover have "fst (last l1) = Catch (fst (last l2)) c2" 
       using a2 last_lenl1 eq_length
      proof -
        have "last l2 = l2 ! (length l2 - 1)"
          using l2_not_empty last_conv_nth by blast
        then show ?thesis
          by (metis One_nat_def a2 l2_not_empty last_lenl1 last_lift_catch)
      qed
      ultimately have False by simp  
    } thus ?thesis using l  by auto qed
qed

lemma comm_map_catch:
assumes 
  a0:"(\<Gamma>,l1) \<in> (cp \<Gamma> (Catch c1 c2) s)" and
  a1:"(\<Gamma>,l2) \<in> (cp \<Gamma> c1 s) \<and> (\<Gamma>, l2)\<in> comm(G, (q,a)) F" and
  a2:"l1=map (lift_catch c2) l2" 
shows
  "(\<Gamma>, l1)\<in> comm(G, (r,a)) F"
proof - 
  {fix i ns ns'
   have "(Suc i < length (l1) \<longrightarrow>
         \<Gamma>\<turnstile>\<^sub>c (fst (l1 ! i), toSeq (snd (l1 ! i))) \<rightarrow> 
             (fst (l1 ! Suc i), toSeq (snd (l1 ! Suc i))) \<longrightarrow>       
        (snd (l1 ! i), snd (l1 ! Suc i)) \<in> G) \<and>
        (final_glob (last l1) \<longrightarrow> fst (last l1) \<notin> Fault ` F  \<longrightarrow>                 
                   fst (last l1) = LanguageCon.com.Skip \<and> snd (last l1) \<in> r \<or>
                   fst (last l1) = LanguageCon.com.Throw \<and> snd (last l1) \<in>  a) "
      using comm_map''_catch[of \<Gamma> l1 c1 c2 s l2 G q a F i r] a0 a1 a2 
      by fastforce
   }  then show ?thesis using comm_def unfolding comm_def by force       
qed

lemma Catch_sound1: 
assumes
  a0:"(n,\<Gamma>,x)\<in>cptn_mod_nest_call" and
  a1:"x!0 = ((Catch P Q),s)" and
  a2:"\<forall>i<length x. fst (x!i)\<noteq> Q" and
  a3:"\<not> final_glob (last x)" and
  a4:"env_tran_right \<Gamma> x rely"
shows
  "\<exists>xs. (\<Gamma>,xs) \<in> cpn n \<Gamma> P s \<and> x = map (lift_catch Q) xs"
using a0 a1 a2 a3 a4
proof (induct arbitrary: P s)
  case (CptnModNestOne n \<Gamma> C s1)
  then have "(\<Gamma>, [(P,s)]) \<in> cpn n \<Gamma> P s \<and> [(C, s1)] = map (lift_catch Q) [(P,s)]"
    unfolding cpn_def lift_catch_def
    by (simp add: cptn_mod_nest_call.CptnModNestOne) 
  thus ?case by fastforce
next
  case (CptnModNestEnv \<Gamma> C s1 t1 n xsa)
  then have C:"C=Catch P Q" unfolding lift_catch_def by fastforce
  have "\<exists>xs. (\<Gamma>, xs) \<in> cpn n \<Gamma> P t1 \<and> (C, t1) # xsa = map (lift_catch Q) xs"
  proof -
     have "((C, t1) # xsa) ! 0 = (Catch P Q, t1)" using C by auto
     moreover have "\<forall>i<length ((C, t1) # xsa). fst (((C, t1) # xsa) ! i) \<noteq> Q"
       using CptnModNestEnv(5) by fastforce
     moreover have "\<not> final_glob (last ((C, t1) # xsa))" using CptnModNestEnv(6) 
       by fastforce
     ultimately show ?thesis
       using CptnModNestEnv(3) CptnModNestEnv(7) env_tran_tail by blast     
  qed 
  then obtain xs where hi:"(\<Gamma>, xs) \<in> cpn n \<Gamma> P t1 \<and> (C, t1) # xsa = map (lift_catch Q) xs"
    by fastforce
  have s1_s:"s1=s" using  CptnModNestEnv unfolding cpn_def by auto
  obtain xsa' where xs:"xs=((P,t1)#xsa') \<and> (n,\<Gamma>,((P,t1)#xsa'))\<in>cptn_mod_nest_call \<and> 
                  (C, t1) # xsa = map (lift_catch Q) ((P,t1)#xsa')" 
    using hi  unfolding cpn_def by fastforce
  
  have env_tran:"\<Gamma>\<turnstile>\<^sub>c(P,s1) \<rightarrow>\<^sub>e (P,t1)" using CptnModNestEnv Catch_env_P by (metis fst_conv nth_Cons_0)  
  then have "(n,\<Gamma>,(P,s1)#(P,t1)#xsa')\<in>cptn_mod_nest_call" using xs env_tran 
    using cptn_mod_nest_call.CptnModNestEnv by blast 
  then have "(\<Gamma>,(P,s1)#(P,t1)#xsa') \<in> cpn n \<Gamma> P s" 
    using cpn_def s1_s by fastforce
  moreover have "(C,s1)#(C, t1) # xsa = map (lift_catch Q) ((P,s1)#(P,t1)#xsa')"
    using xs C unfolding lift_catch_def by fastforce
  ultimately show ?case by auto
next
  case (CptnModNestSkip)
  thus ?case by (metis SmallStepCon.redex_not_Catch fst_conv nth_Cons_0)
next
  case (CptnModNestStuck)
  thus ?case by (metis SmallStepCon.redex_not_Catch fst_conv nth_Cons_0)
next
  case (CptnModNestFault)
  thus ?case by (metis SmallStepCon.redex_not_Catch fst_conv nth_Cons_0)
next
  case (CptnModNestThrow)
  thus ?case by (metis SmallStepCon.redex_not_Catch fst_conv nth_Cons_0)
next
  case (CptnModNestCatch1 n \<Gamma> P0 sa xsa zs P1)
  then have a1:"LanguageCon.com.Catch P Q = LanguageCon.com.Catch P0 P1"
    by fastforce  
  have f1: "sa = s"
    using CptnModNestCatch1.prems(1) by force
  have f2: "P = P0 \<and> Q = P1" using a1 by auto
  have "(n,\<Gamma>, (P0, sa) # xsa) \<in> cptn_mod_nest_call"
    by (metis CptnModNestCatch1.hyps(1))
  hence "(\<Gamma>, (P0, sa) # xsa) \<in> cpn n \<Gamma> P s"
    using f2 f1 by (simp add: cpn_def)
  thus ?case
    using Cons_lift_catch CptnModNestCatch1.hyps(3) a1 by blast   
next
 case (CptnModNestCatch2 n \<Gamma> P1 sa xsa c f  ys zs Q1)
  have "final_glob (last ((c, sa)# ys))" 
    using CptnModNestCatch2(4) unfolding final_glob_def apply auto
    by (metis (no_types, lifting) CptnModNestCatch2.hyps(5)
         cptn_if_cptn_mod cptn_mod_nest_cptn_mod  last_ConsR last_length 
       length_Cons lessI term_all_skip)+
  thus ?case
    by (metis (no_types, hide_lams) CptnModNestCatch2.hyps(7) CptnModNestCatch2.prems(3) 
           append_is_Nil_conv final_glob_def fst_conv last.simps 
          last_appendR list.distinct(1))
next
  case (CptnModNestCatch3 n \<Gamma> P0 sa xsa sa' P1 ys zs)
  then have "P0 = P \<and> P1 = Q" by auto
  then obtain i where zs:"fst (zs!i) = Q \<and> (i< (length zs))" 
    using CptnModNestCatch3
    by (metis (no_types, lifting) add_diff_cancel_left' fst_conv length_Cons length_append nth_append_length zero_less_Suc zero_less_diff)    
  then have "Suc i< length ((Catch P0 P1, sa)#zs)" by fastforce
  then have "fst (((Catch P0 P1,  sa) # zs)!Suc i) = Q" using zs by fastforce    
  thus ?case using CptnModNestCatch3(9) zs by auto
qed (auto)

lemma Catch_sound2: 
assumes
  a0:"(n,\<Gamma>,x)\<in>cptn_mod_nest_call" and
  a1:"x!0 = ((Catch P Q),s)" and
  a2:"\<forall>i<length x. fst (x!i)\<noteq> Q" and
  a3:"fst (last x) = c \<and> (c = Skip \<or> c = Stuck \<or> c = Fault f)" and
  a4:"env_tran_right \<Gamma> x rely"
shows
  "\<exists>xs ys. (\<Gamma>,xs) \<in> cpn n \<Gamma> P s \<and> x = ((map (lift_catch Q) xs)@((c,snd(last xs))#ys))"
using a0 a1 a2 a3 a4
proof (induct arbitrary: P s)
  case (CptnModNestOne n \<Gamma> C s1)  
  thus ?case by fastforce
next
  case (CptnModNestEnv \<Gamma> C s1 t1 n xsa)
  then have C:"C=Catch P Q" unfolding lift_catch_def by fastforce
  have "\<exists>xs ys. (\<Gamma>, xs) \<in> cpn n \<Gamma> P t1 \<and> (C, t1) # xsa = 
                map (lift_catch Q) xs@((c, snd(last xs))#ys)"
  proof -
     have "((C, t1) # xsa) ! 0 = (LanguageCon.com.Catch P Q, t1)" using C by auto
     moreover have "\<forall>i<length ((C, t1) # xsa). fst (((C, t1) # xsa) ! i) \<noteq> Q"
       using CptnModNestEnv(5) by fastforce
     moreover have h:"fst (last ((C, t1) # xsa)) = c" using CptnModNestEnv(6) 
       by fastforce
     ultimately show ?thesis    
       using CptnModNestEnv(3) CptnModNestEnv(7) 
       by (auto simp add: env_tran_tail CptnModNestEnv.prems(3))
  qed 
  then obtain xs ys where hi:
    "(\<Gamma>, xs) \<in> cpn n \<Gamma> P t1 \<and> (C, t1) # xsa = map (lift_catch Q) xs@
            ((c,snd(last ((P, t1)#xs)))#ys)"
    by fastforce
  have s1_s:"s1=s" using  CptnModNestEnv unfolding cp_def by auto
  have "\<exists>xsa' ys. xs=((P,t1)#xsa') \<and> (n,\<Gamma>,((P,t1)#xsa'))\<in>cptn_mod_nest_call \<and> 
         (C, t1) # xsa = map (lift_catch Q) ((P,t1)#xsa')@((c, snd(last xs))#ys)" 
    using hi  unfolding cp_def
  proof -
    have "(n,\<Gamma>,xs)\<in>cptn_mod_nest_call \<and> xs!0 = (P,t1)" 
      using hi unfolding cpn_def by fastforce
    moreover then have "xs\<noteq>[]" using CptnEmpty calculation by blast      
    moreover  obtain xsa' where "xs=((P,t1)#xsa')" using SmallStepCon.nth_tl calculation by fastforce 
    ultimately show ?thesis
      using hi by auto
  qed
  then obtain xsa' ys where xs:"xs=((P,t1)#xsa') \<and> (n,\<Gamma>,((P,t1)#xsa'))\<in>cptn_mod_nest_call \<and> (C, t1) # xsa = 
                                    map (lift_catch Q) ((P,t1)#xsa')@((c,snd(last ((P,s1)#(P,t1)#xsa')))#ys)"
    by fastforce
  have env_tran:"\<Gamma>\<turnstile>\<^sub>c(P,s1) \<rightarrow>\<^sub>e (P,t1)" 
    using CptnModNestEnv Catch_env_P by (metis fst_conv nth_Cons_0)  
  then have "(n,\<Gamma>,(P,s1)#(P,t1)#xsa')\<in>cptn_mod_nest_call" using xs env_tran     
    by (simp add: cptn_mod_nest_call.CptnModNestEnv)   
  then have "(\<Gamma>,(P,s1)#(P,t1)#xsa') \<in> cpn n \<Gamma> P s" 
    using cpn_def s1_s by fastforce
  moreover have "(C,s1)#(C, t1) # xsa = map (lift_catch Q) ((P,s1)#(P,t1)#xsa')@
                                         ((c,snd(last ((P,s1)#(P,t1)#xsa')))#ys)"
    using xs C unfolding lift_catch_def
    by auto
  ultimately show ?case by fastforce 
next
  case (CptnModNestSkip)
  thus ?case by (metis SmallStepCon.redex_not_Catch fst_conv nth_Cons_0)
next
  case (CptnModNestThrow)
  thus ?case by (metis SmallStepCon.redex_not_Catch fst_conv nth_Cons_0)
next
  case (CptnModNestStuck)
  thus ?case by (metis SmallStepCon.redex_not_Catch fst_conv nth_Cons_0)
next
  case (CptnModNestFault)
  thus ?case by (metis SmallStepCon.redex_not_Catch fst_conv nth_Cons_0)
next
  case (CptnModNestCatch1 n \<Gamma> P0 sa xsa zs P1)  
  thus ?case
  proof -
    have "\<forall>c x. (LanguageCon.com.Catch c P1, x) # zs = map (lift_catch P1) ((c, x) # xsa)"
      using Cons_lift_catch CptnModNestCatch1.hyps(3) by blast
    then have "(P0, sa) # xsa = []"
      by (metis CptnModNestCatch1.prems(3) LanguageCon.com.distinct(149) 
           LanguageCon.com.distinct(173) LanguageCon.com.distinct(23) 
         last_length length_Cons lessI map_lift_catch_all_catch)     
    then show ?thesis
      by force
  qed 
next
  case (CptnModNestCatch2 n \<Gamma> P1 sa xsa c1 f  ys zs Q1) 
  then have P0:"P1 = P \<and> Q1 = Q \<and> sa = s" by auto  
  moreover then have cpn:"(\<Gamma>, (P1,sa) # xsa)\<in> cpn n \<Gamma> P s" 
    using CptnModNestCatch2(1)
    by (simp add: cpn_def cptn_eq_cptn_mod_set)  
  ultimately show ?case
  proof -
    have f1: "(\<Gamma>, (c1, snd(last ((P1, sa)#xsa))) # ys) \<in> cptn_mod"
      using  cptn_mod_nest_cptn_mod CptnModNestCatch2.hyps(5) by blast
    have f2: "0 \<le> length ys"
      by fastforce
    have f3: "c = fst (((c1, snd(last ((P1, sa)#xsa))) # ys) ! length ys)"
      by (metis (no_types) CptnModNestCatch2.hyps(7) CptnModNestCatch2.prems(3) 
           append_is_Nil_conv last_ConsR last_appendR last_length list.simps(3))
    have "final_glob (c1, snd(last ((P1, sa)#xsa)))"
      by (metis (no_types) CptnModNestCatch2.hyps(4) final_glob_def fst_conv)
    then have "final_glob (((c1,snd(last ((P1, sa)#xsa))) # ys) ! 0)"
      by simp
    then show ?thesis  using f1 f2 f3
      by (metis (no_types, lifting) Cons_lift_catch_append CptnModNestCatch2.hyps(7) P0 cpn 
       cptn_eq_cptn_mod_set fst_conv last_F length_Cons lessI nth_Cons_0)
  qed     
next 
  case (CptnModNestCatch3 n \<Gamma> P0 sa xsa sa' P1 ys zs)   
  then have "P0 = P \<and> P1 = Q \<and> s= sa" by auto
  then obtain i where zs:"fst (zs!i) = Q \<and> (i< (length zs))" 
    using CptnModNestCatch3    
    by (metis (no_types, lifting) add_diff_cancel_left' fst_conv length_Cons 
        length_append nth_append_length zero_less_Suc zero_less_diff)    
  then have si:"Suc i< length ((Catch P0 P1, sa)#zs)" by fastforce
  then have "fst (((Seq P0 P1,  sa) # zs)!Suc i) = Q" using zs by fastforce    
  thus ?case using CptnModNestCatch3(9) zs
     by (metis si nth_Cons_Suc)
qed (auto)

lemma Catch_sound3: 
assumes
  a0:"(\<Gamma>,x)\<in>cptn" and
  a1:"x!0 = ((Catch P Q),s)" and
  a2:"\<forall>i<length x. fst (x!i)\<noteq> Q" and
  a3:"fst(last x) = Throw" and
  a4:"env_tran_right \<Gamma> x rely "
shows
  "False"
  using a0 a1 a2 a3 a4
  proof (induct arbitrary: P s)
    case (CptnOne \<Gamma> C s1) thus ?case by auto
  next
    case (Cptn \<Gamma> C st C' st' xsa)
    then have "\<Gamma>\<turnstile>\<^sub>c (C, st) \<rightarrow>\<^sub>c\<^sub>e (C', st')" by auto
    then have "\<Gamma>\<turnstile>\<^sub>c (C, st) \<rightarrow>\<^sub>e (C', st') \<or> \<Gamma>\<turnstile>\<^sub>c (C, toSeq st) \<rightarrow> (C', toSeq st')"
      using step_ce_dest by blast
    moreover {assume "\<Gamma>\<turnstile>\<^sub>c (C, st) \<rightarrow>\<^sub>e (C', st')"
    moreover have "LanguageCon.com.Catch P Q = C"
      using Cptn.prems(1) by auto
    moreover have  "C' = C" using env_c_c' calculation Cptn by blast
    ultimately have ?case using Cptn
      by (metis Suc_less_eq env_tran_tail last_length length_Cons nth_Cons_0 nth_Cons_Suc)
  }
  moreover {
    assume a00:"\<Gamma>\<turnstile>\<^sub>c (C, toSeq st) \<rightarrow> (C', toSeq st')"
    then have c_catch:"C = (Catch P Q) \<and> st = s" using Cptn by force
    from a00 c_catch have ?case
    proof(cases)
      case (Catchc P1 P1' P2) thus ?thesis
      proof -
        have f1: "env_tran_right \<Gamma> ((C', st') # xsa) rely"
          using Cptn env_tran_tail by blast
        have "Q = P2"
          using c_catch Catchc(1)  by blast
        then show ?thesis
          using f1 Cptn Catchc(2) by moura
      qed
    next
      case  (CatchSkipc) thus ?thesis
      proof -
        have "fst (((C', st') # xsa) ! 0) = LanguageCon.com.Skip"
          by (simp add: local.CatchSkipc(2))
        then show ?thesis
          by (metis (no_types) Cptn.hyps(2) Cptn.prems(3) LanguageCon.com.distinct(21) last.simps 
              last_length length_Cons lessI list.distinct(1) zero_skip_all_skip)
      qed    
    next
      case (CatchThrowc)
      thus ?thesis using Cptn by auto   
    next
      case (CatchStuckc C2) thus ?thesis
        by (metis LanguageCon.com.simps(159) last_ConsR last_length length_Cons lessI 
              list.distinct(1) local.Cptn(2) local.Cptn(6) term_all_skip) 
    next
      case (CatchFaultc C2) thus ?thesis
        by (metis LanguageCon.com.distinct(171) last_ConsR last_length length_Cons lessI 
             list.simps(3) local.Cptn(2) local.Cptn(6) term_all_skip) 
    qed (fastforce,auto)     
  } ultimately show ?case by auto
qed

lemma catch_map_xs_ys':
  assumes
  a0:"(n, \<Gamma>, (P0, sa) # xsa) \<in> cptn_mod_nest_call" and    
  a1:"fst (last ((P0, sa) # xsa)) = C" and
  a2:"(n,\<Gamma>, (P1, snd (last ((P0, sa) # xsa))) # ys) \<in> cptn_mod_nest_call" and
  a3:"zs = map (lift_catch P1) xsa @ (P1, snd (last ((P0, sa) # xsa))) # ys" and
  a4:"((LanguageCon.com.Catch P0 P1, sa) # zs) ! 0 = (LanguageCon.com.Catch P Q, s)" and
  a5:"i < length ((LanguageCon.com.Catch P0 P1, sa) # zs) \<and> ((LanguageCon.com.Catch P0 P1, sa) # zs) ! i = (Q, sj)" and
  a6:"\<forall>j<i. fst (((LanguageCon.com.Catch P0 P1, sa) # zs) ! j) \<noteq> Q"
shows 
  "\<exists>xs ys. (\<Gamma>, xs) \<in> cpn n \<Gamma> P s \<and>
            (\<Gamma>, ys) \<in> cpn n \<Gamma> Q (snd (xs ! (i - 1))) \<and> (LanguageCon.com.Catch P0 P1, sa) # zs = map (lift_catch Q) xs @ ys"
proof -
  let ?P0 = "(P0, sa) # xsa"
  have P_Q:"P=P0 \<and> s=sa \<and> Q = P1" using a4 by force
  have i:"i=(length ((P0, sa) # xsa))"   
  proof (cases "i=(length ((P0, sa) # xsa))")
    case True thus ?thesis by auto
  next
    case False     
    then have i:"i<(length ((P0, sa) # xsa)) \<or> i > (length ((P0, sa) # xsa))" by auto
    {
      assume i:"i<(length ((P0, sa) # xsa))"
      then have eq_map:"((LanguageCon.com.Catch P0 P1, sa) # zs) ! i = map (lift_catch P1) ((P0, sa) # xsa) ! i" 
        using a3 Cons_lift_catch_append
        by (metis (no_types, lifting) length_map nth_append) 
      then have  "\<exists>ci si. map (lift_catch P1) ((P0, sa) # xsa) ! i = (Catch ci P1,si)" 
        using i unfolding lift_catch_def
        by (metis a5 eq_map fst_conv length_map map_lift_catch_all_catch)
      then have  "((LanguageCon.com.Catch P0 P1, sa) # zs) ! i \<noteq> (Q, sj)" 
        using P_Q eq_map by fastforce
      then have ?thesis using a5 by auto
    }note l=this
    {
      assume i:"i>(length ((P0, sa) # xsa))"
      have "fst (((LanguageCon.com.Catch P0 P1, sa) # zs) ! (length ?P0)) = Q"
        using a3 P_Q Cons_lift_catch_append by (metis fstI length_map nth_append_length) 
      then have ?thesis using a6 i by auto
    }
    thus ?thesis using l i by auto
   qed
   then have  "(\<Gamma>, (P0, sa) # xsa) \<in> cpn n \<Gamma> P s" 
    using a0  P_Q unfolding cpn_def by fastforce
  also have "(\<Gamma>, (P1, snd (last ((P0, sa) # xsa))) # ys) \<in> cpn n \<Gamma> Q (snd (?P0 ! ((length ?P0) -1)))" 
    using a3 cptn_eq_cptn_mod P_Q unfolding cpn_def
  proof -
    have "(n, \<Gamma>, (Q, snd (last ((P0, sa) # xsa))) # ys) \<in> cptn_mod_nest_call"
      using a2 P_Q by blast
    then have "(\<Gamma>, (Q, snd (last ((P0, sa) # xsa))) # ys) \<in> {(f, ps). ps ! 0 = (Q, snd (((P0, sa) # xsa) ! (Suc (length xsa) - 1))) \<and> 
              (n, \<Gamma>, ps) \<in> cptn_mod_nest_call \<and> f = \<Gamma>}"
      by (simp add: cptn_eq_cptn_mod last_length)
    then show "(\<Gamma>, (P1, snd (last ((P0, sa) # xsa))) # ys) \<in> {(f, ps). ps ! 0 = (Q, snd (((P0, sa) # xsa) ! (length ((P0, sa) # xsa) - 1))) \<and> (n,\<Gamma>, ps) \<in> cptn_mod_nest_call \<and> f = \<Gamma>}"
      using P_Q by force
  qed 
  ultimately show ?thesis using a3 P_Q i using Cons_lift_catch_append by blast
qed


lemma Catch_sound4: 
assumes
  a0:"(n,\<Gamma>,x)\<in>cptn_mod_nest_call" and
  a1:"x!0 = ((Catch P Q),s)" and
  a2:"i<length x \<and> x!i=(Q,sj)" and
  a3:"\<forall>j<i. fst(x!j)\<noteq>Q" and 
  a4:"env_tran_right \<Gamma> x rely "
shows
  "\<exists>xs ys. (\<Gamma>,xs) \<in> (cpn n \<Gamma> P s) \<and> (\<Gamma>,ys) \<in> (cpn n \<Gamma> Q (snd (xs!(i-1)))) \<and> x = (map (lift_catch Q) xs)@ys"
using a0 a1 a2 a3 a4
proof (induct arbitrary: i sj P s)
  case (CptnModNestEnv \<Gamma> C st t n xsa)  
  have a1:"Catch P Q \<noteq> Q" by simp    
  then have C_catch:"C=(Catch P Q)" using CptnModNestEnv by fastforce
  then have "fst(((C, st) # (C, t) # xsa)!0) \<noteq>Q" using Cptn a1 by auto
  moreover have  "fst(((C, st) # (C, t) # xsa)!1) \<noteq>Q" using CptnModNestEnv a1 by auto
  moreover have "fst(((C, st) # (C, t) # xsa)!i) =Q" using CptnModNestEnv by auto
  ultimately have i_suc: "i> (Suc 0)" using CptnModNestEnv 
    by (metis Suc_eq_plus1 Suc_lessI add.left_neutral neq0_conv) 
  then obtain i' where i':"i=Suc i'" by (meson lessE) 
  then have i_minus:"i'=i-1" by auto  
  have "((C, t) # xsa) ! 0 = ((Catch P Q), t)"
    using CptnModNestEnv by auto 
  moreover have "i'< length ((C,t)#xsa) \<and> ((C,t)#xsa)!i' = (Q,sj)"
    using i' CptnModNestEnv(5) by force
  moreover have "\<forall>j<i'. fst (((C, t) # xsa) ! j) \<noteq> Q"
    using i' CptnModNestEnv(6) by force
  ultimately have hyp:"\<exists>xs ys.
     (\<Gamma>, xs) \<in> cpn n \<Gamma> P t \<and>
     (\<Gamma>, ys) \<in> cpn n \<Gamma> Q (snd (xs ! (i'-1))) \<and> (C, t) # xsa = map (lift_catch Q) xs @ ys"
    using CptnModNestEnv(3) env_tran_tail CptnModNestEnv.prems(4)  by blast 
  then obtain xs ys where xs_cp:"(\<Gamma>, xs) \<in> cpn n \<Gamma> P t \<and>
     (\<Gamma>, ys) \<in> cpn n \<Gamma> Q (snd (xs ! (i'-1))) \<and> (C, t) # xsa = map (lift_catch Q) xs @ ys"
    by fast
  have "(\<Gamma>, (P, s)#xs) \<in> cpn n \<Gamma> P s"
  proof -
    have "xs!0 = (P,t)" 
      using xs_cp unfolding cpn_def by blast
    moreover have "xs\<noteq>[]"
      using cpn_def CptnEmpty xs_cp by blast 
    ultimately obtain xs' where xs':"(n,\<Gamma>, (P,t)#xs') \<in> cptn_mod_nest_call \<and> xs=(P,t)#xs'" 
      using SmallStepCon.nth_tl xs_cp unfolding cpn_def by force
    thus ?thesis using cpn_def  
    proof -
      have "(Catch P Q, s) = (C, st)"
        using CptnModNestEnv.prems(1) by auto
      then have "\<Gamma>\<turnstile>\<^sub>c (P, s) \<rightarrow>\<^sub>e (P, t)"
        using Catch_env_P CptnModNestEnv(1) by blast
      then show ?thesis
        by (simp add: cpn_def cptn_mod_nest_call.CptnModNestEnv xs')
    qed
  qed
  thus  ?case 
    using i_suc Cons_lift_catch_append CptnModNestEnv.prems(1) i' i_minus xs_cp
    by (metis (no_types, lifting) Suc_less_SucD nth_Cons_0 nth_Cons_pos)    
next
  case (CptnModNestSkip \<Gamma> P s t n xs)
  then show ?case
    by (metis (no_types) fst_conv nth_Cons_0 redex_not_Catch)
next
  case (CptnModNestThrow \<Gamma> P s t n xs)
  then show ?case  
    by (metis (no_types)  fst_conv nth_Cons_0 redex_not_Catch)
next
case (CptnModNestStuck \<Gamma> P s t n xs)
  then show ?case  
    by (metis (no_types) fst_conv nth_Cons_0 redex_not_Catch)
next
case (CptnModNestFault \<Gamma> P s t n xs)
  then show ?case  
    by (metis (no_types)  fst_conv nth_Cons_0 redex_not_Catch)
next
  case (CptnModNestCatch1 n \<Gamma> P0 s xs zs P1)
  then show ?case
    by (metis Catch_not_c Cons_lift_catch LanguageCon.com.inject(10) fst_conv 
          map_lift_catch_all_catch nth_Cons_0)
next
  case (CptnModNestCatch2 n \<Gamma> P1 sa xsa c1 f ys zs Q1) 
  then have P_Q:"P=P1 \<and> Q = Q1" by force
  thus ?case
  proof (cases "Q1 = Skip \<or> Q1 = Stuck \<or> (\<exists>f. Q1 = Fault f)")
    case True 
    then have cptnmod:" (n,\<Gamma>,((Catch P1 Q1),  s)#zs) \<in> cptn_mod_nest_call "
      using  cptn_mod.CptnModSeq3 P_Q apply auto
      by (smt CptnModNestCatch2.hyps(1) CptnModNestCatch2.hyps(3) CptnModNestCatch2.hyps(4) 
                CptnModNestCatch2.hyps(5) CptnModNestCatch2.hyps(7) CptnModNestCatch2.prems(1) 
              cptn_mod_nest_call.CptnModNestCatch2 nth_Cons_0)+
    then have "c1 = Q1" 
    proof -      
     have f4: "(\<Gamma>, (c1, snd (last ((P1, sa) # xsa))) # ys) \<in> cptn"
      using  CptnModNestCatch2(5)
      using cptn_eq_cptn_mod_nest by blast
    have f3:"((Catch P1 Q1, sa) # zs) ! i = (Q1, sj)"
      using P_Q CptnModNestCatch2(9) by fastforce
    then have f5: "final_glob (Q, sj)"
      by (metis P_Q True final_glob_def fst_conv)
    have "final_glob (c1, snd (last ((P1, sa) # xsa)))"
      using CptnModNestCatch2.hyps(4) final_glob_def prod.collapse by blast
    then show ?thesis
      using f5 f4
      by (smt CptnModNestCatch2.hyps(7) CptnModNestCatch2.prems(1) CptnModNestCatch2.prems(2)
             append_is_Nil_conv cptn_if_cptn_mod cptn_mod_nest_cptn_mod cptnmod f3 fst_conv 
         last.simps last_F last_appendR last_length length_Cons lessI less_Suc_eq_le list.distinct(1)
             nth_Cons_0 zero_less_Suc)            
    qed 
    thus ?thesis using P_Q catch_map_xs_ys'[of n \<Gamma> P1 "sa" xsa Q1 Q1 ys zs P1 Q1 sa i sj]
      CptnModNestCatch2 by auto
  next 
    case asm0:False note q_not_throw=this
    have "\<forall>x. x< length ((LanguageCon.com.Catch P1 Q1, sa) # zs) \<longrightarrow>
              ((LanguageCon.com.Catch P1 Q1,  sa) # zs) ! x \<noteq> (Q, sj)" using CptnModNestCatch2
    proof -
    {
      fix x
      assume x_less:"x< length ((LanguageCon.com.Catch P1 Q1,  sa) # zs)"
      have "((LanguageCon.com.Catch P1 Q1,  sa) # zs) ! x \<noteq> (Q, sj)"
      proof (cases "x < length ((LanguageCon.com.Catch P1 Q1, sa)#map (lift_catch Q1) xsa)")
        case True 
        then have eq_map:"((LanguageCon.com.Catch P1 Q1, sa) # zs) ! x = 
                     map (lift_catch Q1) ((P1, sa) # xsa) ! x"
          by (metis (no_types, lifting) Cons_lift_catch Cons_lift_catch_append 
               CptnModNestCatch2.hyps(7) nth_append)           
        then have  "\<exists>ci si. map (lift_catch Q1) ((P1, sa) # xsa) ! x = (Catch ci Q1,si)" 
          using True unfolding lift_catch_def
          by (metis Cons_lift_catch True eq_map map_lift_catch_all_catch surjective_pairing)
        then have  "((LanguageCon.com.Catch P1 Q1, sa) # zs) ! x \<noteq> (Q, sj)" 
          using P_Q eq_map by fastforce     
        thus ?thesis using CptnModNestCatch2(10) by auto        
      next
        case False 
        let ?s' = "snd (last ((P1, sa) # xsa))"        
        have all_throw:"\<forall>i<length ((c1, ?s')# ys). 
              fst (((c1, ?s')# ys)!i) = c1" using CptnModNestCatch2  term_all_skip
          by (metis cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod)         
        then have 
          "\<forall>x\<ge> length ((LanguageCon.com.Catch P1 Q1,  sa) # map (lift_catch Q1) xsa). 
           x<length (((LanguageCon.com.Catch P1 Q1, sa) # zs)) \<longrightarrow>
              fst (((LanguageCon.com.Catch P1 Q1, sa) # zs) ! x) = c1"            
        proof-
        {
          fix x 
          assume a1:"x\<ge> length ((Catch P1 Q1, sa) # map (lift_catch Q1) xsa)" and
                 a2:"x<length (((Catch P1 Q1, sa) # zs))"
          then have "((Catch P1 Q1, sa) # zs) ! x = 
                     ((c1, ?s')# ys) !(x - (length ((Catch P1 Q1, sa) # map (lift_catch Q1) xsa)))"
          using CptnModNestCatch2(6) 
          by (metis (no_types, lifting) Cons_lift_catch Cons_lift_catch_append CptnModNestCatch2.hyps(7) 
                    diff_is_0_eq' less_numeral_extra(3) nth_append zero_less_diff)
          then have"fst (((Catch P1 Q1, sa) # zs) ! x) = c1" 
            using all_throw a1 a2 CptnModNestCatch2.hyps(6) 
            by (simp add: CptnModNestCatch2.hyps(7)) 
         } thus ?thesis by auto
         qed       
         thus ?thesis using False    P_Q x_less asm0  CptnModNestCatch2(3,4)
           by (metis fst_conv not_le_imp_less)
    qed
    } thus ?thesis by auto
    qed
    thus ?thesis using CptnModNestCatch2.prems(2) by blast 
  qed     
next
  case (CptnModNestCatch3 n \<Gamma> P1 sa xsa  ys zs Q1)
  then show ?case using catch_map_xs_ys'[OF CptnModNestCatch3(1) CptnModNestCatch3(3) CptnModNestCatch3(5)
                                            CptnModNestCatch3(7) CptnModNestCatch3(8) CptnModNestCatch3(9)] 
     by blast
qed(auto) 

inductive_cases stepc_elim_cases_Catch_throw:
"\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,s) \<rightarrow> (Throw, s1)" 

inductive_cases stepc_elim_cases_Catch_skip_c2:
"\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,s) \<rightarrow> (c2,s)"

inductive_cases stepc_elim_cases_Catch_skip_2:
"\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,s) \<rightarrow> (Skip,  s1)"
"\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,s) \<rightarrow> (Throw,  s1)"
"\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,s) \<rightarrow> (Stuck,  s1)" 
"\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,s) \<rightarrow> (Fault f,  s1)"


lemma catch_skip_throw:
 "\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,s) \<rightarrow> (c2,s)  \<Longrightarrow> (c1= Skip \<and> c2= Skip) \<or> (c1=Throw ) \<or> 
                                    (c1 = Stuck \<and> c2=Stuck) \<or> (\<exists>f. c1 = Fault f \<and> c2=Fault f)"
apply (rule stepc_elim_cases_Catch_skip_c2)
apply fastforce
apply (auto)+
done

thm stepc_elim_cases_Catch_skip_2
lemma catch_skip_throw1:
 "\<Gamma>\<turnstile>\<^sub>c(Catch c1 c2,s) \<rightarrow> (Skip,s)  \<Longrightarrow> (c1=Skip) \<or> (c1=Throw \<and> c2 = Skip)"
apply (rule stepc_elim_cases_Catch_skip_2)
using redex_not_Catch by auto


lemma Catch_sound: 
      "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p,  R, G, q,r] \<Longrightarrow>
       \<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p,  R, G, q,r] \<Longrightarrow>
       \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [r,  R, G, q,a] \<Longrightarrow>
       \<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c2 sat [r,  R, G, q,a] \<Longrightarrow>        
       Sta q R  \<Longrightarrow>  \<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G \<Longrightarrow> 
       \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (Catch c1 c2) sat [p, R, G, q,a]"
proof -  
  assume
    a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p, R, G, q,r]" and
    a1:"\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p, R, G, q,r]" and
    a2:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c2 sat [r, R, G, q,a]" and    
    a3: "\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c2 sat [r, R, G, q,a]" and     
    a4: "Sta q R " and
    a5: "\<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G"       
  { 
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"
    then have a1:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p, R, G, q,r]" 
      using a1 com_cvalidityn_def by fastforce  
    then have a3: "\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c2 sat [r, R, G, q,a]"
      using a3 com_cvalidityn_def all_call by fastforce 
    have "cpn n \<Gamma> (Catch c1 c2)  s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cpn n \<Gamma> (Catch c1 c2) s" and a11:"c \<in> assum(p, R)"
      then have a10':"c \<in> cp \<Gamma> (Catch c1 c2) s"
        unfolding cpn_def cp_def
        using cptn_if_cptn_mod cptn_mod_nest_cptn_mod by blast
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have cp:"l!0=((Catch c1 c2),s) \<and> (n,\<Gamma>,l) \<in> cptn_mod_nest_call \<and> \<Gamma>=\<Gamma>1" 
        using a10 cpn_def c_prod by fastforce
      then have cp':"l!0=((Catch c1 c2),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1"
        using cptn_eq_cptn_mod_nest by auto         
      have \<Gamma>1:"(\<Gamma>, l) = c" using c_prod cp by blast
      have "c \<in> comm(G, (q,a)) F"         
      proof - 
      {       
       have assum:"snd(l!0) \<in> p \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
                 (snd(l!i), snd(l!(Suc i))) \<in> R)" 
       using a11 c_prod unfolding assum_def by simp
       then have env_tran:"env_tran \<Gamma> p l R" using env_tran_def cp by blast
       then have env_tran_right: "env_tran_right \<Gamma> l R" 
         using env_tran env_tran_right_def unfolding env_tran_def by auto       
       have "(\<forall>i. Suc i<length l \<longrightarrow> 
               (\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                    (fst (l ! Suc i), toSeq (snd (l ! Suc i)))) \<longrightarrow>                                             
                 (snd(l!i), snd(l!(Suc i))) \<in> G)\<and>
             (final_glob (last l)  \<longrightarrow> fst (last l) \<notin> Fault ` F \<longrightarrow>                   
                   ((fst (last l) = Skip \<and> snd (last l) \<in> q)) \<or>
                    (fst (last l) = Throw \<and> snd (last l) \<in>  a))"
       proof (cases "\<forall>i<length l. fst (l!i)\<noteq> c2")
         case True 
         then have no_c2:"\<forall>i<length l. fst (l!i)\<noteq> c2" by assumption
         show ?thesis
         proof (cases "final_glob (last l)")
           case True
           then have  "fst (last l) = Throw \<or> fst (last l) = Skip \<or> fst (last l) = Stuck \<or> (\<exists>f. fst (last l) = Fault f)  "  
             using final_glob_def by fast           
           thus ?thesis
           proof
             assume "fst (last l)= LanguageCon.com.Throw" 
             then have "False" using  no_c2 env_tran_right cp' cptn_eq_cptn_mod_set Catch_sound3
               by blast
             thus ?thesis by auto
           next             
             assume asm0:"fst (last l) = Skip \<or> fst (last l) = Stuck \<or> (\<exists>f. fst (last l) = Fault f) "             
             then obtain lc1 ys where 
               cp_lc1:"(\<Gamma>,lc1) \<in> cpn n \<Gamma> c1 s \<and> l = 
                       ((map (lift_catch c2) lc1)@((fst (last l),snd(last lc1))#ys))"
               using Catch_sound2[of n \<Gamma> l c1 c2 s _ _ R] 
                     cp cptn_eq_cptn_mod_set env_tran_right no_c2
               by force
             then have cp_lc1':"(\<Gamma>,lc1) \<in> cp \<Gamma> c1 s"
               unfolding cpn_def cp_def
               using cptn_if_cptn_mod cptn_mod_nest_cptn_mod by fastforce 
             let ?m_lc1 = "map (lift_catch c2) lc1"
             let ?lm_lc1 = "(length ?m_lc1)"
             let ?last_m_lc1 = "?m_lc1!(?lm_lc1-1)"              
             have lc1_not_empty:"lc1 \<noteq> []"
               using \<Gamma>1 a10' cpn_def cp_lc1 cp asm0 by force                 
             then have map_cp:"(\<Gamma>,?m_lc1) \<in> cpn n \<Gamma> (Catch c1 c2) s"               
             proof -
               have f1: "lc1 ! 0 = (c1, s) \<and> (n, \<Gamma>, lc1) \<in> cptn_mod_nest_call \<and> \<Gamma> = \<Gamma>"
                 using cp_lc1 unfolding cpn_def by blast
               then have f2: "(n,\<Gamma>, ?m_lc1) \<in> cptn_mod_nest_call" using lc1_not_empty
                 by (metis Cons_lift_catch SmallStepCon.nth_tl cptn_mod_nest_call.CptnModNestCatch1)
               then show ?thesis
                 using f2 f1 lc1_not_empty by (simp add: cpn_def lift_catch_def)
             qed
             then have map_cp':"(\<Gamma>,?m_lc1) \<in> cp \<Gamma> (Catch c1 c2) s" 
               unfolding cp_def cpn_def
               using cp_lc1' lift_catch_is_cptn asm0 unfolding cp_def
               by auto
             also have map_assum:"(\<Gamma>,?m_lc1) \<in> assum (p,R)"
               using sub_assum a10 a11 \<Gamma>1 cp_lc1 lc1_not_empty 
               by (metis SmallStepCon.nth_tl map_is_Nil_conv)
             ultimately have "((\<Gamma>,lc1) \<in> assum(p, R))"  
               using \<Gamma>1 assum_map_catch cp_lc1' by blast                          
             then have lc1_comm:"(\<Gamma>,lc1) \<in> comm(G, (q,r)) F"  
               using a1 cp_lc1 by (meson IntI com_validityn_def contra_subsetD)
             then have m_lc1_comm:"(\<Gamma>,?m_lc1) \<in> comm(G, (q,r)) F"
               using map_cp map_assum comm_map_catch cp_lc1' map_cp' by blast
             then have last_m_lc1:"last (?m_lc1) = (Catch (fst (last lc1)) c2,snd (last lc1))"
             proof -
               have a000:"\<forall>p c. (LanguageCon.com.Catch (fst p) c, snd p) = lift_catch c p"
                 using Cons_lift_catch by force
               then show ?thesis
                 by (simp add: last_map a000 lc1_not_empty)
             qed
             then have last_length:"last (?m_lc1) = ?last_m_lc1"  
               using lc1_not_empty last_conv_nth list.map_disc_iff by blast 
             then have l_map:"l!(?lm_lc1-1)= ?last_m_lc1" 
               using cp_lc1 
               by (metis (no_types, lifting) diff_less lc1_not_empty length_greater_0_conv 
                   map_is_Nil_conv nth_append zero_less_one)               
             then have lm_lc1:"l!(?lm_lc1) = (fst(last l), snd (last lc1))"
               using cp_lc1
               by (metis nth_append_length) 
             have step_ce:"\<Gamma>\<turnstile>\<^sub>c(l!(?lm_lc1-1)) \<rightarrow>\<^sub>c\<^sub>e (l!(?lm_lc1))"
             proof -
               have f1: "0 \<le> length ys"
                 by blast
               moreover have  "Suc (length (map (lift_catch c2) lc1) + length ys) = 
                    length (map (lift_catch c2) lc1 @ (fst(last l), snd (last lc1)) # ys)"
                 by force
               ultimately show ?thesis
                 by (metis (no_types) Suc_diff_1 Suc_eq_plus1 cp' cp_lc1 cptn_tran_ce_i 
                            lc1_not_empty le_add_same_cancel1 length_greater_0_conv 
                  less_Suc_eq_le list.map_disc_iff)
             qed 
             then have step:"(\<Gamma>\<turnstile>\<^sub>c (fst (l ! (?lm_lc1-1)), toSeq (snd (l ! (?lm_lc1-1)))) \<rightarrow> 
                             (fst (l ! ?lm_lc1), toSeq (snd (l ! (?lm_lc1)))))"
               using l_map last_m_lc1 lm_lc1 local.last_length 
                     not_eq_not_env step_ce_dest asm0 
               by (metis LanguageCon.com.distinct(149) LanguageCon.com.distinct(173)
                         LanguageCon.com.distinct(23)  fstI sndI)
             have last_lc1_suc:"snd (l!(?lm_lc1-1)) = snd (l!?lm_lc1)"
               using l_map  last_m_lc1 lm_lc1 local.last_length by force
             then have eq_to_seq:"toSeq (snd (l ! (length (map (lift_catch c2) lc1) - 1))) = 
                                  toSeq (snd (l ! (length (map (lift_catch c2) lc1))))"
               by simp
             then have step':"\<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.Catch (fst (last lc1)) c2, toSeq (snd (l ! (?lm_lc1-1)))) \<rightarrow>
                             (fst (last l), toSeq (snd (l ! (?lm_lc1)))) "
               using lm_lc1 step
               using l_map last_m_lc1 local.last_length by auto
             then have eq_l:"snd (l ! (length (map (lift c2) lc1) - 1)) =snd (l ! (length (map (lift c2) lc1)))"
               using step_ce_Normal_eq_l step_ce step' step_ce_eq  eq_to_seq 
                     l_map last_m_lc1 lm_lc1 local.last_length by fastforce                
             then have step_catch:"\<Gamma>\<turnstile>\<^sub>c(Catch (fst (last lc1)) c2,toSeq (snd (last lc1))) \<rightarrow> (fst (last l), toSeq(snd (last lc1)))"               
               using l_map last_m_lc1 lm_lc1 local.last_length local.step'
               by auto 
             then have 
               last_lc1:"(fst (last lc1) = Skip \<and> fst (last l) = Skip) \<or>                          
                         (fst (last lc1) = Stuck \<and> fst (last l) = Stuck) \<or> 
                          (\<exists>f. fst (last lc1) = Fault f \<and> fst (last l) = Fault f)"
               using asm0 
               apply (cases "fst (last l)", auto) 
               using stepc_elim_cases_Catch_skip_2(1) no_c2
                 apply (metis One_nat_def append_is_Nil_conv cp_lc1 diff_Suc_less 
                        last_conv_nth length_greater_0_conv list.distinct(1)) 
                using stepc_elim_cases_Catch_skip_2(3) no_c2
                 apply (metis One_nat_def append_is_Nil_conv cp_lc1 diff_Suc_less last_conv_nth 
                        length_greater_0_conv list.distinct(1)) 
                using stepc_elim_cases_Catch_skip_2(4) no_c2 
                by (metis One_nat_def append_is_Nil_conv cp_lc1 diff_Suc_less last_conv_nth 
                        length_greater_0_conv list.distinct(1))                 
             have concl:"(\<forall>i. Suc i<length l \<longrightarrow> 
               (\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
               (fst (l ! Suc i), toSeq (snd (l ! Suc i)))) \<longrightarrow>              
                 (snd(l!i), snd(l!(Suc i))) \<in> G)"
             proof-
             { fix k ns ns'
               assume a00:"Suc k<length l" and
                a21:"(\<Gamma>\<turnstile>\<^sub>c (fst (l !k), toSeq (snd (l ! k))) \<rightarrow> 
                        (fst (l ! Suc k), toSeq (snd (l ! Suc k))))"   
                then have i_m_l:"\<forall>i <?lm_lc1  . l!i = ?m_lc1!i" 
                  using cp_lc1
                proof -
                  have "map (lift c2) lc1 \<noteq> []"
                    by (meson lc1_not_empty list.map_disc_iff)
                  then show ?thesis
                    by (metis (no_types) cp_lc1  nth_append)
                qed                                                         
                have "(snd(l!k), snd(l!(Suc k))) \<in> G"
                proof (cases "Suc k< ?lm_lc1")
                  case True 
                  then have a11': "(\<Gamma>\<turnstile>\<^sub>c (fst (?m_lc1!k), toSeq (snd (?m_lc1!k))) \<rightarrow> 
                                    (fst (?m_lc1!(Suc k)), toSeq (snd (?m_lc1!(Suc k)))))" 
                    using a11 i_m_l True
                  proof -
                    have "\<forall>n na. \<not> 0 < n - Suc na \<or> na < n "
                      using diff_Suc_eq_diff_pred zero_less_diff by presburger
                    then show ?thesis
                      by (metis (no_types) True a21 i_m_l zero_less_diff)
                  qed                 
                  then have "(snd(?m_lc1!k), snd(?m_lc1!(Suc k))) \<in> G"
                  using a11' m_lc1_comm True comm_dest1  last_not_F by fastforce
                  thus ?thesis using i_m_l True by auto  
                next
                  case False 
                  then have "(Suc k=?lm_lc1) \<or> (Suc k>?lm_lc1)" by auto
                  thus ?thesis 
                  proof
                    {assume suck:"(Suc k=?lm_lc1)"
                     then have k:"k=?lm_lc1-1" by auto
                     (* then obtain s1' where s1'_normal:"snd(l!?lm_lc1) = Normal s1'"
                       using q_normal by fastforce
                     have G_s1':"(Normal s1', Normal s1')\<in> G" using a5 by blast *)
                     then show "(snd (l!k), snd (l!Suc k)) \<in> G" using a5 k last_lc1_suc 
                       unfolding N_def
                       by (metis (mono_tags, lifting) a00 assum cp' 
                           cptn_all_len_eq_0 mem_Collect_eq suck)                        
                    }
                  next
                  { 
                    assume a001:"Suc k>?lm_lc1"
                    have "\<forall>i. i\<ge>(length lc1) \<and> (Suc i < length l) \<longrightarrow> 
                            \<not>((\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                              (fst (l ! Suc i), toSeq (snd (l ! Suc i)))))"
                    using lm_lc1 lc1_not_empty
                    proof -
                      have "env_tran_right \<Gamma>1 l R"
                        by (metis cp env_tran_right)
                      then show ?thesis 
                        using  cp' fst_conv length_map lm_lc1 a001 a21 a00 a4
                        by (metis asm0 cp' fst_conv length_map lm_lc1 only_one_component_tran_j) 

                    qed
                    then have "\<not>((\<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                              (fst (l ! Suc k), toSeq (snd (l ! Suc k)))))"
                      using a00 a001 by auto                    
                    then show ?thesis using a21 by fastforce                    
                  }
                  qed 
                qed
              } thus ?thesis by auto 
             qed 
             have concr:"(final_glob (last l)  \<longrightarrow>    fst (last l) \<notin> Fault ` F \<longrightarrow>                  
                   ((fst (last l) = Skip \<and> snd (last l) \<in> q)) \<or>
                    (fst (last l) = Throw \<and> snd (last l) \<in> a))" 
             proof -
               { assume a00:"final_glob (last l)" and a01:"fst (last l)\<notin> Fault ` F" 
               (* have l_t:"fst (last l) = Skip" 
                 using lm_lc1 by (simp add: asm0) *)
                 have lm_lc1_len:"?lm_lc1 \<le> length l -1" using cp_lc1
                   by (metis (no_types, hide_lams) Ex_list_of_length Suc_pred' add_diff_cancel_left' append_is_Nil_conv 
                         diff_is_0_eq' leI length_Cons length_append length_greater_0_conv 
                    less_Suc_eq_le less_irrefl)  
                 have f_lc1:"final_glob (last lc1)"
                   using final_glob_def last_lc1 by blast
                 moreover have "fst (last lc1) \<notin> Fault ` F"
                   using a01 last_lc1 by auto 
                 moreover have eq:"(l ! length (map (lift_catch c2) lc1)) = last lc1"
                   using last_lc1 lm_lc1 
                   by (metis lm_lc1 prod.exhaust_sel)
                 ultimately have h:"fst (last lc1) = Skip \<and> snd (last lc1) \<in> q \<or>
                                 fst (last lc1) = Throw \<and> snd (last lc1) \<in> a" 
                   using lc1_comm  unfolding comm_def
                   using last_lc1 by auto
                 { assume "fst (last l) = com.Stuck \<or> (\<exists>f. fst (last l) = com.Fault f)"
                   then have False
                     using h last_lc1 by auto
                   then have "(fst (last l) = Skip \<and> snd (last l) \<in> q) \<or>
                            (fst (last l) = Throw \<and> snd (last l) \<in> a)"
                     by blast                   
                 }
                 moreover { assume "fst (last l) = Skip"
                   then have a_normal:"snd (l!?lm_lc1) \<in> q" using h
                     using a00 l_map last_lc1_suc last_lc1 last_m_lc1 local.last_length
                     by auto 
                   then have "snd (l ! (length l - 1)) \<in>  q" using   a4     
                           f_lc1[simplified eq[THEN sym]] lm_lc1_len    cp'  
                           i_final_all_stable[OF _ _ lm_lc1_len _ env_tran_right a4 a_normal]
                     by force                                 
                   then have "(fst (last l) = Skip \<and> snd (last l) \<in> q) \<or>
                            (fst (last l) = Throw \<and> snd (last l) \<in> a)"
                     using h lm_lc1_len last_m_lc1
                   proof -
                     have "snd (last l) \<in> q"
                       by (metis \<open>snd (l ! (length l - 1)) \<in> q\<close> append_is_Nil_conv cp_lc1 last_conv_nth list.simps(3))
                     then show ?thesis
                       using \<open>fst (last l) = LanguageCon.com.Skip\<close> by presburger
                   qed
                 }                             
                 ultimately have "(fst (last l) = Skip \<and> snd (last l) \<in> q) \<or>
                            (fst (last l) = Throw \<and> snd (last l) \<in> a)" 
                   using asm0 by auto
             } thus ?thesis by auto
             qed
             note res = conjI [OF concl concr]
             then show ?thesis using  \<Gamma>1 c_prod unfolding comm_def by auto
           qed                  
         next
           case False
           then obtain lc1 where cp_lc1:"(\<Gamma>,lc1) \<in> cpn n \<Gamma> c1 s \<and> l = map (lift_catch c2) lc1" 
             using Catch_sound1 False no_c2 env_tran_right cp cptn_eq_cptn_mod_set 
             by blast 
           then have cp_lc1':"(\<Gamma>,lc1) \<in> cp \<Gamma> c1 s" 
             unfolding cpn_def cp_def
             using cptn_eq_cptn_mod_nest by fastforce
           then have "((\<Gamma>,lc1) \<in> assum(p, R))"  
              using \<Gamma>1  a10' a11 assum_map_catch cp_lc1
              by blast
           then have "(\<Gamma>, lc1)\<in> comm(G, (q,r)) F" using cp_lc1 a1
             by (meson IntI com_validityn_def contra_subsetD)
           then have "(\<Gamma>, l)\<in> comm(G, (q,r)) F"
             using comm_map_catch a10' \<Gamma>1 cp_lc1 cp_lc1' by fastforce
           then show ?thesis using  False
             unfolding comm_def by force
         qed
       next         
         case False 
         then obtain k where k_len:"k<length l \<and> fst (l ! k) = c2"
           by blast         
         then have "\<exists>m. (m < length l \<and> fst (l ! m) = c2) \<and>
                   (\<forall>i<m. \<not> (i < length l \<and> fst (l ! i) = c2))"   
           using a0 exists_first_occ[of "(\<lambda>i. i<length l  \<and> fst (l ! i) = c2)" k] 
           by blast
         then obtain i where a0:"i<length l \<and> fst (l !i) = c2 \<and>
                                (\<forall>j<i. (fst (l ! j) \<noteq> c2))"
           by fastforce        
         then obtain s2 where li:"l!i =(c2,s2)" by (meson eq_fst_iff)
         then obtain lc1 lc2 where cp_lc1:"(\<Gamma>,lc1) \<in> (cpn n \<Gamma> c1 s) \<and> 
                                 (\<Gamma>,lc2) \<in> (cpn n \<Gamma> c2 (snd (lc1!(i-1)))) \<and> 
                                 l = (map (lift_catch c2) lc1)@lc2"
           using Catch_sound4 a0 cp env_tran_right by blast       
         then have cp_lc1':"(\<Gamma>,lc1) \<in> (cp \<Gamma> c1 s) \<and> 
                            (\<Gamma>,lc2) \<in> (cp \<Gamma> c2 (snd (lc1!(i-1))))"
           unfolding cp_def cpn_def  using cptn_eq_cptn_mod_nest by fastforce         
         have length_c1_map:"length lc1 = length (map (lift_catch c2) lc1)" 
           by fastforce      
         then have i_map:"i=length lc1" 
           using cp_lc1 li a0 unfolding lift_catch_def 
         proof -
           assume a1: "(\<Gamma>, lc1) \<in> cpn n \<Gamma> c1 s \<and> (\<Gamma>, lc2) \<in> cpn n \<Gamma> c2 (snd (lc1 ! (i - 1))) \<and> 
                      l = map (\<lambda>(P, s). (Catch P c2, s)) lc1 @ lc2"
            have f2: "i < length l \<and> fst (l ! i) = c2 \<and> (\<forall>n. \<not> n < i \<or> fst (l ! n) \<noteq> c2)"
              using a0 by blast
            have f3: "(Catch (fst (lc1 ! i)) c2, snd (lc1 ! i)) = lift_catch c2 (lc1 ! i)"
              by (simp add: case_prod_unfold lift_catch_def)            
            then have "fst (l ! length lc1) = c2"
              using a1 by (simp add: cpn_def nth_append)
            thus ?thesis
              using f3 f2
              by (metis (no_types, lifting) Pair_inject a0 cp_lc1 f3 
                   length_c1_map li linorder_neqE_nat nth_append nth_map seq_and_if_not_eq(12))
         qed                  
         have lc2_l:"\<forall>j<length lc2. lc2!j=l!(i+j)"
           using cp_lc1 length_c1_map i_map a0
           by (metis nth_append_length_plus)                                                             
         have lc1_not_empty:"lc1 \<noteq> []"
           using cp cp_lc1 unfolding cpn_def by fastforce      
         have lc2_not_empty:"lc2 \<noteq> []"
           using cpn_def cp_lc1 a0 i_map by force              
         have l_is:"s2= snd (last lc1)"
         using cp_lc1 li a0 lc1_not_empty unfolding cpn_def
         by (auto simp add: i_map last_conv_nth lc2_l)
         let ?m_lc1 = "map (lift_catch c2) lc1"
         (* let ?lm_lc1 = "(length ?m_lc1)"
         let ?last_m_lc1 = "?m_lc1!(?lm_lc1-1)" *)                         
         have last_m_lc1:"l!(i-1) = (Catch (fst (last lc1)) c2,s2)"
           using i_map  cp_lc1 l_is last_lift_catch last_snd_catch lc1_not_empty length_c1_map           
           by (metis (no_types, lifting) One_nat_def diff_Suc_less last_conv_nth 
                  length_greater_0_conv nth_append prod.collapse)
         (* have last_mcl1_not_F:"snd (last ?m_lc1) \<notin> Fault ` F"
           by (metis One_nat_def i_not_fault l_is last_conv_nth last_snd_catch li list.map_disc_iff snd_conv) *)
         have map_cp:"(\<Gamma>,?m_lc1) \<in> cpn n \<Gamma> (Catch c1 c2) s"               
         proof -
           have f1: "lc1 ! 0 = (c1, s) \<and> (n,\<Gamma>, lc1) \<in> cptn_mod_nest_call \<and> \<Gamma> = \<Gamma>"
             using cp_lc1 cpn_def by blast
           then have f2: "(n, \<Gamma>, ?m_lc1) \<in> cptn_mod_nest_call" using lc1_not_empty
             by (metis Cons_lift_catch SmallStepCon.nth_tl cptn_mod_nest_call.CptnModNestCatch1)                           
           then show ?thesis
             using f2 f1 lc1_not_empty by (simp add: cpn_def lift_catch_def)
         qed
         then have map_cp':"(\<Gamma>,?m_lc1) \<in> cp \<Gamma> (Catch c1 c2) s"
           unfolding cp_def cpn_def using cptn_eq_cptn_mod_nest by fastforce
         also have map_assum:"(\<Gamma>,?m_lc1) \<in> assum (p,R)"
           using sub_assum a10 a11 \<Gamma>1 cp_lc1 lc1_not_empty 
           by (metis SmallStepCon.nth_tl map_is_Nil_conv)
         ultimately have "((\<Gamma>,lc1) \<in> assum(p, R))"  
           using \<Gamma>1 assum_map_catch using assum_map cp_lc1 cp_lc1' by blast                          
         then have lc1_comm:"(\<Gamma>,lc1) \<in> comm(G, (q,r)) F"  
           using a1 cp_lc1 by (meson IntI com_validityn_def contra_subsetD)
         then have m_lc1_comm:"(\<Gamma>,?m_lc1) \<in> comm(G, (q,r)) F"
           using map_cp' map_assum comm_map_catch cp_lc1 cp_lc1'  by blast         
         then have i_step:"(\<Gamma>\<turnstile>\<^sub>c (fst (l ! (i-1)), toSeq (snd (l ! (i-1)))) \<rightarrow> 
                         (fst (l ! i), toSeq (snd (l ! i))))"
         proof -
           have "\<Gamma>\<turnstile>\<^sub>c(l!(i-1)) \<rightarrow>\<^sub>c\<^sub>e (l!(i))"
             by (metis Suc_eq_plus1 Suc_pred' a0 cp' cptn_tran_ce_i i_map 
                  lc1_not_empty length_greater_0_conv)
           moreover have "\<not>\<Gamma>\<turnstile>\<^sub>c(l!(i-1)) \<rightarrow>\<^sub>e (l!i)"           
             using li last_m_lc1
             by (metis (no_types, lifting) env_c_c' seq_and_if_not_eq(12))
           ultimately show ?thesis using step_ce_dest
             by (metis prod.exhaust_sel)
         qed         
         then have step:"\<Gamma>\<turnstile>\<^sub>c(Catch (fst (last lc1)) c2,toSeq s2) \<rightarrow> (c2, toSeq s2)"
           using last_m_lc1  li by fastforce
         then have
           last_lc1:"fst (last lc1) = Skip \<or> 
            fst (last lc1) = Throw \<or> fst (last lc1) = Stuck \<or> (\<exists>f. fst(last lc1) = Fault f)"            
           by (meson catch_skip_throw)   
         have final:"final_glob (last lc1)" 
           using last_lc1 l_is unfolding final_glob_def by fastforce        
         have Gs2':" (s2, s2)\<in>G" using a5 unfolding N_def
           by (metis (mono_tags, lifting) a0 assum cp' cptn_all_len_eq_0 li mem_Collect_eq snd_conv)               
         have concl:
           "(\<forall>i. Suc i<length l \<longrightarrow> 
           (\<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                 (fst (l ! (Suc i)), toSeq (snd (l ! (Suc i))))) \<longrightarrow>                              
             (snd(l!i), snd(l!(Suc i))) \<in> G)"
         proof-
         { fix k ns ns'
           assume a00:"Suc k<length l" and
            a21:"(\<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                      (fst (l !(Suc k)), toSeq (snd (l ! (Suc k)))))"   
            have i_m_l:"\<forall>j <i . l!j = ?m_lc1!j"             
            proof -
              have "map (lift c2) lc1 \<noteq> []"
                by (meson lc1_not_empty list.map_disc_iff)
              then show ?thesis 
                using cp_lc1 i_map length_c1_map by (fastforce simp:nth_append)              
            qed 
            have "(snd(l!k), snd(l!(Suc k))) \<in> G"
            proof (cases "Suc k< i")
              case True 
              then have a11': "(\<Gamma>\<turnstile>\<^sub>c (fst (?m_lc1 ! k), toSeq (snd (?m_lc1 ! k))) \<rightarrow> 
                                    (fst (?m_lc1 ! Suc k), toSeq (snd (?m_lc1 ! Suc k))))" 
                using a11 i_m_l True
              proof -
                have "\<forall>n na. \<not> 0 < n - Suc na \<or> na < n "
                  using diff_Suc_eq_diff_pred zero_less_diff by presburger
                then show ?thesis using True a21 i_m_l by force                  
              qed                                                             
              have "Suc k < length ?m_lc1" using True i_map length_c1_map by metis
              then have "(snd(?m_lc1!k), snd(?m_lc1!(Suc k))) \<in> G"
              using a11'  m_lc1_comm True i_map length_c1_map comm_dest1[of \<Gamma>] 
                by blast
              thus ?thesis using i_m_l True by auto  
            next
              case False                                            
              have "(Suc k=i) \<or> (Suc k>i)" using False by auto
              thus ?thesis 
              proof
              { assume suck:"(Suc k=i)" 
                then have k:"k=i-1" by auto                                                            
                then show "(snd (l!k), snd (l!Suc k)) \<in> G"
                  using Gs2'  last_m_lc1 li suck by auto               
              }
              next
              { 
                assume a001:"Suc k>i"
                then have k:"k\<ge>i" by fastforce
                then obtain k' where k':"k=i+k'" 
                  using add.commute le_Suc_ex by blast
                {assume skip:"c2=Skip  \<or> c2 = Stuck \<or> (\<exists>f. c2 = Fault f)"
                 then have "\<forall>k. k\<ge>i \<and> (Suc k < length l) \<longrightarrow> 
                            \<not>(\<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                                  (fst (l ! Suc k), toSeq (snd (l ! Suc k))))"
                  using  li  a21 a001 a00 a4
                        a0 skip env_tran_right cp'
                  using only_one_component_tran_j by blast                                      
                 then have ?thesis using a21 a001 k a00 by blast
                }  note left=this
                {assume "\<not>(c2=Skip  \<or> c2 = Stuck \<or> (\<exists>f. c2 = Fault f))"
                 then have "fst (last lc1) = Throw"
                   using last_m_lc1 last_lc1
                   by (meson catch_skip_throw local.step)                                     
                 then have s2_normal:"s2 \<in>  r" 
                   using l_is li final comm_dest2 lc1_comm by fastforce                                      
                 have length_lc2:"length l=i+length lc2" 
                       using i_map cp_lc1 by fastforce
                 have "(\<Gamma>,lc2) \<in>  assum (r,R)" 
                 proof -
                   have left:"snd (lc2!0) \<in>  r" 
                     using li lc2_l s2_normal lc2_not_empty by fastforce 
                   {
                     fix j
                     assume j_len:"Suc j<length lc2" and
                            j_step:"\<Gamma>\<turnstile>\<^sub>c(lc2!j)  \<rightarrow>\<^sub>e (lc2!(Suc j))"                     
                     then have suc_len:"Suc (i + j)<length l" using j_len length_lc2
                       by fastforce
                     also then have "\<Gamma>\<turnstile>\<^sub>c(l!(i+j))  \<rightarrow>\<^sub>e (l! (Suc (i+ j)))"
                        using lc2_l j_step j_len by fastforce
                     ultimately have "(snd(lc2!j), snd(lc2!(Suc j))) \<in> R"
                        using assum suc_len lc2_l j_len cp by fastforce 
                   }
                   then show ?thesis using left 
                     unfolding assum_def by fastforce
                 qed
                 also have "(\<Gamma>,lc2) \<in> cpn n \<Gamma> c2 s2"
                   using cp_lc1 i_map l_is last_conv_nth lc1_not_empty by fastforce                 
                 ultimately have comm_lc2:"(\<Gamma>,lc2) \<in>  comm (G, (q,a)) F"
                   using a3 unfolding com_validityn_def by blast
                 (* have lc2_last_f:"snd (last lc2)\<notin> Fault ` F" 
                   using lc2_l lc2_not_empty l_f cp_lc1 by fastforce *)
                 have suck':"Suc k' < length lc2" 
                   using k' a00 length_lc2 by arith
                 moreover then have "(\<Gamma>\<turnstile>\<^sub>c (fst (lc2 ! k'), toSeq (snd (lc2 ! k'))) \<rightarrow> 
                                          (fst (lc2 ! Suc k'), toSeq (snd (lc2 ! Suc k'))))"  
                   using k' lc2_l a21 by fastforce                 
                 ultimately have "(snd (lc2! k'), snd (lc2 ! Suc k')) \<in> G"
                   using comm_lc2  comm_dest1[of \<Gamma> lc2 G q a F k'] 
                   by blast
                 then have ?thesis using suck' lc2_l k' by fastforce
                }                    
                then show ?thesis using left by auto                 
              }
              qed 
            qed
          } thus ?thesis by auto 
         qed note left=this
         have right:"(final_glob (last l)  \<longrightarrow>    fst (last l) \<notin> Fault ` F \<longrightarrow>              
                   ((fst (last l) = Skip \<and> snd (last l) \<in>  q)) \<or>
                    (fst (last l) = Throw \<and> snd (last l) \<in> (a)))"
         proof -
         { assume final_l:"final_glob (last l)" and a002:"fst (last l) \<notin> Fault ` F "
           have eq_last_lc2_l:"last l=last lc2" by (simp add: cp_lc1 lc2_not_empty)
           then have final_lc2:"final_glob (last lc2)" using final_l by auto
           {
             assume lst_lc1_skip:"fst (last lc1) = Skip"                        
             then have c2_skip:"c2 = Skip" 
               using  step  LanguageCon.com.distinct(17) last_lc1
               using catch_skip_throw by force 
                                          
             have Skip:"fst (l!(length l - 1)) = Skip"
             using li   env_tran_right cp' c2_skip a0
                     i_skip_all_skip[of \<Gamma> l i "(length l) - 1"] 
                by fastforce                       
             have s2_a:"s2 \<in>  q"
               using comm_des3 final l_is lc1_comm lst_lc1_skip by fastforce
             then have "\<forall>ia. i \<le> ia \<and> ia < length l - 1 \<longrightarrow> \<Gamma>\<turnstile>\<^sub>c (l ! ia) \<rightarrow>\<^sub>e (l ! Suc ia)"
               using c2_skip li  a0 cp' env_tran_right  
                     cptn_tran_ce_i i_skip_all_skip  step_ce_dest 
               unfolding final_glob_def
               by (metis (no_types, lifting) Suc_eq_plus1 Suc_lessD 
                    less_diff_conv prod.exhaust_sel stepc_elim_cases(1))                                       
             then have "snd (l!(length l - 1)) \<in>  q \<and> fst (l!(length l - 1)) = Skip"               
               using a0 s2_a li a4 env_tran_right stability[of q R l i "(length l) -1" _ \<Gamma>] Skip
               using c2_skip by fastforce
             then have "((fst (last l) = Skip \<and> snd (last l) \<in> q)) \<or>
                    (fst (last l) = Throw \<and>  snd (last l) \<in>  a)" 
              using a0 by (metis last_conv_nth list.size(3) not_less0)                           
          } 
          moreover {  assume "fst (last lc1) = Throw"                 
             then have s2_normal:"s2 \<in>  r"
               using comm_dest2 final l_is lc1_comm by fastforce
             have length_lc2:"length l=i+length lc2" 
                   using i_map cp_lc1 by fastforce
             have "(\<Gamma>,lc2) \<in>  assum (r,R)" 
             proof -
               have left:"snd (lc2!0) \<in> r" 
                 using li lc2_l s2_normal lc2_not_empty by fastforce 
               {
                 fix j
                 assume j_len:"Suc j<length lc2" and
                        j_step:"\<Gamma>\<turnstile>\<^sub>c(lc2!j)  \<rightarrow>\<^sub>e (lc2!(Suc j))"
                 
                 then have suc_len:"Suc (i + j)<length l" using j_len length_lc2
                   by fastforce
                 also then have "\<Gamma>\<turnstile>\<^sub>c(l!(i+j))  \<rightarrow>\<^sub>e (l! (Suc (i+ j)))"
                    using lc2_l j_step j_len by fastforce
                 ultimately have "(snd(lc2!j), snd(lc2!(Suc j))) \<in> R"
                    using assum suc_len lc2_l j_len cp by fastforce 
               }
               then show ?thesis using left 
                 unfolding assum_def by fastforce
             qed
             also have "(\<Gamma>,lc2) \<in> cpn n \<Gamma> c2 s2"
               using cp_lc1 i_map l_is last_conv_nth lc1_not_empty by fastforce
             ultimately have comm_lc2:"(\<Gamma>,lc2) \<in>  comm (G, (q,a)) F"
               using a3 unfolding com_validityn_def
               by blast
             have lc2_last_f:"fst (last lc2)\<notin> Fault ` F"                
               using a002 eq_last_lc2_l by force             
             then have "((fst (last lc2) = Skip \<and> snd (last lc2) \<in> q)) \<or>
                    (fst (last lc2) = Throw \<and> snd (last lc2) \<in> a)" 
             using final_lc2 comm_lc2 unfolding comm_def by auto
             then have "((fst (last l) = Skip \<and> snd (last l) \<in>  q)) \<or>
                    (fst (last l) = Throw \<and> snd (last l) \<in> a)" 
             using eq_last_lc2_l by auto
          }
          moreover{
             assume "fst (last lc1) = Stuck"             
             then have  "((fst (last l) = Skip \<and> snd (last l) \<in> q)) \<or>
                       (fst (last l) = Throw \<and> snd (last l) \<in>  a)"
               by (metis (no_types) com.distinct(13) com.distinct(145) 
                   com.distinct(147) comm_des3 final image_iff lc1_comm)            
           }
           moreover { 
             assume "(\<exists>f. fst (last lc1) = Fault f)"
             then have  "((fst (last l) = Skip \<and> snd (last l) \<in> q)) \<or>
                       (fst (last l) = Throw \<and> snd (last l) \<in>  a)"
               by (metis LanguageCon.com.distinct(171) LanguageCon.com.simps(31) 
                     LocalRG_HoareDef.stepc_elim_cases_Catch_skip_c2 a0 a002 comm_dest2 cp' 
                   final last_not_F lc1_comm local.step)
           }
           ultimately have "((fst (last l) = Skip \<and> snd (last l) \<in>  q)) \<or>
                    (fst (last l) = Throw \<and> snd (last l) \<in> a)" 
           using last_lc1 by blast
        } thus ?thesis by auto qed         
     thus ?thesis using left  \<Gamma>1 unfolding comm_def by force       
       qed             
     } thus ?thesis using \<Gamma>1 unfolding comm_def by auto qed
   } thus ?thesis by auto qed 
 } thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed



lemma DynCom_sound: 
      "(\<forall>s \<in> fst ` p. ((\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (c1 s) sat [p, R, G, q,a]) \<and> 
                 (\<forall>n. (\<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (c1 s) sat [p,R, G, q,a])))) \<Longrightarrow>
       \<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G \<Longrightarrow>
       (Sta p R) \<and> (Sta q R) \<and> (Sta a R) \<Longrightarrow>        
        \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (DynCom c1) sat [p,  R, G, q,a]"
proof -  
  assume
    a0:"(\<forall>s \<in> fst ` p. ((\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (c1 s) sat [p, R, G, q,a]) \<and> 
                 (\<forall>n. (\<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (c1 s) sat [p, R, G, q,a]))))" and    
    a1:"\<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G" and  
    a2: "(Sta p R) \<and> (Sta q R) \<and> (Sta a R)"               
  { 
    fix s
    assume all_DynCom:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"     
    then have a0:"(\<forall>s \<in> fst ` p. (\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (c1 s) sat [p, R, G, q,a]))"
      using a0 unfolding com_cvalidityn_def by fastforce     
    have "cpn n \<Gamma>(DynCom c1) s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cpn n \<Gamma> (DynCom c1) s" and a11:"c \<in> assum(p, R)"
      then have a10':"c \<in> cp \<Gamma> (DynCom c1) s"
        unfolding cp_def cpn_def
        using cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod by fastforce
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (q,a)) F"      
      proof - 
        {       
        have cp:"l!0=(DynCom c1,s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" 
          using a10' cp_def c_prod by fastforce
        have \<Gamma>1:"(\<Gamma>, l) = c" using c_prod cp by blast
        have assum:"snd(l!0) \<in>  (p) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
                   (snd(l!i), snd(l!(Suc i))) \<in> R)" 
       using a11 c_prod unfolding assum_def by simp
       then have env_tran:"env_tran \<Gamma> p l R" using env_tran_def cp by blast
       then have env_tran_right: "env_tran_right \<Gamma> l R" 
         using env_tran env_tran_right_def unfolding env_tran_def by auto
       have s_normal:"s \<in> p" 
         using cp assum by fastforce       
       have concl:"(\<forall>i. Suc i<length l \<longrightarrow> 
               (\<Gamma>1\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                  (fst (l ! Suc i), toSeq (snd (l ! Suc i)))) \<longrightarrow>             
                 (snd(l!i), snd(l!(Suc i))) \<in> G)"
       proof -
       { fix k 
         assume a00:"Suc k<length l" and
                a21:"\<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                    (fst (l ! Suc k), toSeq (snd (l ! Suc k)))"                                     
         obtain j where before_k_all_evnt:"j\<le>k \<and>  (\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                                                        (fst (l ! Suc j), toSeq (snd (l ! Suc j)))) \<and> 
                                            (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
           using a00 a21 exist_first_comp_tran cp by blast
         then obtain cj sj csj ssj where 
            pair_j:"(\<Gamma>\<turnstile>\<^sub>c(cj,sj)  \<rightarrow> (csj,ssj)) \<and> 
                     cj = fst (l!j) \<and> sj = toSeq (snd (l!j)) \<and> 
                     csj = fst (l!(Suc j)) \<and> ssj = toSeq(snd(l!(Suc j)))"
           by fast      
         have k_basic1:"cj = (DynCom c1) \<and> snd(l!j) \<in> (p)" 
           using  pair_j before_k_all_evnt a2 cp env_tran_right  assum a00 stability[of p R l 0 j j \<Gamma>]
           by force
         have k_basic:"cj = (DynCom c1) \<and> sj \<in> (fst ` p)" 
           using  pair_j before_k_all_evnt a2 cp env_tran_right  assum a00 stability[of p R l 0 j j \<Gamma>]
           by force
         then have ss:"sj \<in> (fst ` p)" by auto 
         moreover have ssj_normal_s:"ssj = sj" 
           using before_k_all_evnt k_basic pair_j a0 calculation
           by (metis snd_conv stepc_elim_cases(10))      
         ultimately obtain sl where 
           lj:"snd (l!j) =  (sj, sl) \<and> snd (l!(Suc j)) =  (sj, sl)"
           using  cp  l2[of \<Gamma> "fst (l ! j)" "snd (l ! j)" "fst (l ! Suc j)" "snd (l ! Suc j)"] a00
           using before_k_all_evnt pair_j  by fastforce           
         have "(snd(l!k), snd(l!(Suc k))) \<in> G"
           using ss a2 unfolding Satis_def
         proof (cases "k=j")   
           case True                                  
           have "((sj,sl),  (sj,sl))\<in>G" using a1 unfolding N_def
             using k_basic1 lj by fastforce
           thus "(snd (l ! k), snd (l ! Suc k)) \<in>  G"
             using pair_j k_basic True ss ssj_normal_s lj  True         
             by fastforce           
         next
           case False   
           have j_k:"j<k" using  before_k_all_evnt False by fastforce                      
           thus "(snd (l ! k), snd (l ! Suc k)) \<in> G"
           proof -
             have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce
             have p1:"sj\<in>fst ` p \<and> ssj= sj" using ss ssj_normal_s by fastforce
             then have c1_valid:"(\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (c1 sj) sat [p, R, G, q,a])"
               using a0 by fastforce
             have cj:"csj= (c1 sj)" using k_basic pair_j ss a0 s_normal
             proof -
               have "\<Gamma>\<turnstile>\<^sub>c (LanguageCon.com.DynCom c1, sj) \<rightarrow> (csj, ssj)"
                 using k_basic pair_j ss by force
               then have "(csj, ssj) = (c1 sj, sj)"
                 by (meson stepc_elim_cases(10))
               then show ?thesis
                 by blast
             qed                                                       
             moreover then have "cpn n \<Gamma> csj ((sj, sl)) \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
               using a2 com_validityn_def cj p1 c1_valid by blast             
             moreover then have "l!(Suc j) = (csj,  (sj,sl))" 
               using before_k_all_evnt pair_j cj ssj_normal_s lj
               by (metis prod.exhaust_sel)                
             ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
               using  p1 j_length  a11 \<Gamma>1  ssj_normal_s a10 k_basic1 lj
               cpn_assum_induct[of \<Gamma> l n "LanguageCon.com.DynCom c1" s p R "Suc j" "c1 sj" "(sj,sl)" p]
                by auto                           
             then show ?thesis 
             using a00 a21  a10' \<Gamma>1  j_k j_length  
             cptn_comm_induct[of \<Gamma> l "DynCom c1" s _ "Suc j" G q a F k ]
             unfolding Satis_def by fastforce                         
          qed            
       qed 
       } thus ?thesis by (simp add: c_prod cp) qed
       have concr:"(final_glob (last l)  \<longrightarrow> fst (last l) \<notin> Fault ` F \<longrightarrow>                   
                   ((fst (last l) = Skip \<and> snd (last l) \<in> q)) \<or>
                    (fst (last l) = Throw \<and> snd (last l) \<in>  (a)))"
       proof-
       { 
         assume valid:"final_glob (last l)"  and final_fault: "fst (last l) \<notin> Fault ` F"                     
         have "\<exists>k. k\<ge>0 \<and> k<((length l) - 1) \<and> 
                      \<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                          (fst (l ! Suc k), toSeq (snd (l ! Suc k))) \<and> 
                   final_glob (l!(Suc k))"
         proof -             
           have len_l:"length l > 0" using cp using cptn.simps by blast 
           then obtain a1 l1 where l:"l=a1#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
           have last_l:"last l = l!(length l-1)"
            using last_length [of a1 l1] l by fastforce         
           have final_0:"\<not>final_glob(l!0)" using cp unfolding final_glob_def by auto
           have "0\<le> (length l-1)" using len_l last_l by auto
           moreover have "(length l-1) < length l" using len_l by auto
           moreover have "final_glob (l!(length l-1))" using valid last_l by auto
           moreover have "fst (l!0) = DynCom c1" using cp by auto
           ultimately show ?thesis 
             using a2 cp final_exist_component_tran_final env_tran_right final_0 
             by blast 
          qed
          then obtain k where 
                a21: "k\<ge>0 \<and> k<((length l) - 1) \<and> 
                      \<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                          (fst (l ! Suc k), toSeq (snd (l ! Suc k))) \<and> 
                      final_glob (l!(Suc k))"
            by auto
          then have a00:"Suc k<length l" by fastforce
          then obtain j where 
             before_k_all_evnt:"j\<le>k \<and>  \<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                                           (fst (l ! Suc j), toSeq (snd (l ! Suc j))) \<and> 
                                (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
            using a00 a21 exist_first_comp_tran cp by blast
          then obtain cj sj csj ssj where 
            pair_j:"(\<Gamma>\<turnstile>\<^sub>c(cj,sj)  \<rightarrow> (csj,ssj)) \<and> 
                     cj = fst (l!j) \<and> sj = toSeq (snd (l!j)) \<and> 
                     csj = fst (l!(Suc j)) \<and> ssj = toSeq(snd(l!(Suc j)))"
            by fast         
          have "((fst (last l) = Skip \<and> snd (last l) \<in> q)) \<or>
                    (fst (last l) = Throw \<and> snd (last l) \<in> (a))"
          proof -
            have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce 
            then have k_basic1:"cj = (DynCom c1) \<and> snd(l!j) \<in>  p" 
              using a2 pair_j before_k_all_evnt cp env_tran_right assum stability[of p R l 0 j j \<Gamma>]
              by force
            then have k_basic:"cj = (DynCom c1) \<and> sj \<in>  (fst ` p)" 
              using a2 pair_j before_k_all_evnt cp env_tran_right assum stability[of p R l 0 j j \<Gamma>]
              by force
            then have ss:"sj \<in> (fst ` p)" by auto 
            moreover  have ssj_normal_s:"ssj = sj" 
              using before_k_all_evnt k_basic pair_j a0 calculation
              by (metis snd_conv stepc_elim_cases(10))
            ultimately obtain sl where
              lj: "snd (l!j) =(sj, sl) \<and> snd (l!(Suc j)) = (sj, sl)"
              using  cp  l2[of \<Gamma> "fst (l ! j)" "snd (l ! j)" "fst (l ! (Suc j))" "snd (l ! (Suc j))"] a00
              using before_k_all_evnt pair_j by fastforce
            have cj:"csj=c1 sj" using k_basic pair_j ss a0
              by (metis fst_conv stepc_elim_cases(10))                
            moreover have p1:"(sj,sl)\<in>p" using  k_basic1 cj lj by auto 
            moreover then have "cpn n \<Gamma> csj ((sj, sl)) \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
              using a0 com_validityn_def cj lj k_basic1 ss by blast
            moreover then have "l!(Suc j) = (csj, (sj, sl))" 
              using before_k_all_evnt pair_j cj ssj_normal_s cj
              by (metis lj prod.exhaust_sel)              
            ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
              using  j_length a10 a11 \<Gamma>1  ssj_normal_s lj k_basic1        
              by (meson contra_subsetD cpn_assum_induct)               
            thus ?thesis       
              using j_length drop_comm a10' \<Gamma>1 
                cptn_comm_induct[of \<Gamma> l "DynCom c1" s _ "Suc j" G q a F "Suc j"] valid  final_fault 
              by blast
           qed
         } thus ?thesis by auto 
         qed
       note res = conjI [OF concl concr]}               
       thus ?thesis using  c_prod unfolding comm_def by force qed      
    } thus ?thesis by auto qed 
  } thus ?thesis by (auto simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed

lemma Guard_sound:
  "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> {c. (fst c) \<in> g}, R, G, q,a] \<Longrightarrow>
   (\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> {c. (fst c) \<in> g}, R, G, q,a]) \<Longrightarrow>   
   Sta (p \<inter> {c. (fst c) \<in> g}) R \<Longrightarrow> \<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G \<Longrightarrow>
    \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (Guard f g c1) sat [p \<inter> {c. (fst c) \<in> g}, R, G, q,a]"
proof -  
  assume
    a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [(p \<inter> {c. (fst c) \<in> g}) , R, G, q,a]" and
    a1:"(\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> {c. (fst c) \<in> g}, R, G, q,a])" and        
    a2: "Sta (p \<inter> {c. (fst c) \<in> g}) R" and
    a3: "\<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G"
  { 
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"  
    then have a1:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> {c. (fst c) \<in> g}, R, G, q,a]" 
      using a1 com_cvalidityn_def by fastforce
    have "cpn n \<Gamma> (Guard f g c1)  s \<inter> assum(p \<inter> {c. (fst c) \<in> g}, R) \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cpn n \<Gamma> (Guard f g c1) s" and a11:"c \<in> assum(p \<inter> {c. (fst c) \<in> g}, R)"
      then have a10':"c \<in> cp \<Gamma> (Guard f g c1) s" 
        unfolding cpn_def cp_def using cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod by fastforce
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (q,a)) F"      
      proof - 
        {      
        have cp:"l!0=((Guard f g c1),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10' cp_def c_prod by fastforce
        have \<Gamma>1:"(\<Gamma>, l) = c" using c_prod cp by blast
        have assum:"snd(l!0) \<in> (p \<inter> {c. (fst c) \<in> g}) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
                   (snd(l!i), snd(l!(Suc i))) \<in> R)" 
       using a11 c_prod unfolding assum_def by simp
       then have env_tran:"env_tran \<Gamma> (p \<inter> {c. (fst c) \<in> g}) l R" using env_tran_def cp by blast
       then have env_tran_right: "env_tran_right \<Gamma> l R" 
         using env_tran env_tran_right_def unfolding env_tran_def by auto
       have concl:"(\<forall>i. Suc i<length l \<longrightarrow> 
               (\<Gamma>1\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                     (fst (l ! Suc i), toSeq (snd (l ! Suc i))) ) \<longrightarrow>                                            
                 (snd(l!i), snd(l!(Suc i))) \<in> G)"
       proof -
       { fix k ns ns'
         assume a00:"Suc k<length l" and
                a21:"(\<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                          (fst (l ! Suc k), toSeq (snd (l ! Suc k))) )"                                                        
         obtain j where before_k_all_evnt:
           "j\<le>k \<and>  (\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                         (fst (l ! Suc j), toSeq (snd (l ! Suc j))) ) \<and> 
            (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
           using a00 a21 exist_first_comp_tran cp by blast
         then obtain cj sj csj ssj where pair_j:
              "(\<Gamma>\<turnstile>\<^sub>c(cj,sj)  \<rightarrow> (csj,ssj)) \<and> 
                cj = fst (l!j) \<and> sj = toSeq(snd (l!j)) \<and> csj = fst (l!(Suc j)) \<and> 
                 ssj = toSeq(snd(l!(Suc j)))"
           by fast     
         then have  pair_j1:"(\<Gamma>\<turnstile>\<^sub>c(fst (l!j),toSeq(snd (l!j)))  \<rightarrow> (fst (l!(Suc j)),toSeq(snd(l!(Suc j)))))"
           by auto
         have k_basic1:"cj =(Guard f g c1) \<and> snd (l!j) \<in>  (p \<inter>  {c. (fst c) \<in> g})" 
           using  pair_j before_k_all_evnt cp env_tran_right a2 assum a00 
                  stability[of "p \<inter> {c. (fst c) \<in> g}" R l 0 j j \<Gamma>]
           by force
         have k_basic:"cj =(Guard f g c1) \<and> sj \<in> ((fst ` p) \<inter> g)" 
           using  pair_j before_k_all_evnt cp env_tran_right a2 assum a00 
                 stability[of "p \<inter> {c. (fst c) \<in> g}" R l 0 j j \<Gamma>]
           by force
         then have ss:"sj \<in> ((fst`p)\<inter> g)" by auto 
         moreover have ssj_normal_s:"ssj = sj" 
           using before_k_all_evnt k_basic pair_j a0 stepc_elim_cases(2) calculation
           by (metis (no_types, lifting)  IntD2 prod.inject)
         ultimately obtain sl where 
           lj:"snd (l!j) = (sj, sl) \<and> snd (l!(Suc j)) = (sj, sl)"
           using  cp l2[of \<Gamma> "fst (l ! j)" "snd (l ! j)" "fst (l ! (Suc j))" "snd (l ! (Suc j))"] 
                 a00 before_k_all_evnt pair_j by fastforce 
         have "(snd(l!k), snd(l!(Suc k))) \<in> G"
           using ss a2 unfolding Satis_def
         proof (cases "k=j")   
           case True                                  
           have " ( (sj, sl),  (sj, sl))\<in>G" using a3 unfolding N_def using k_basic1 lj by fastforce 
           thus "(snd (l ! k), snd (l ! Suc k)) \<in>  G"
             using pair_j k_basic True ss ssj_normal_s lj by fastforce
         next
           case False   
           have j_k:"j<k" using  before_k_all_evnt False by fastforce                      
           thus "(snd (l ! k), snd (l ! Suc k)) \<in>  G"
           proof -
             have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce
             have cj:"csj=c1" using k_basic pair_j ss a0
               by (metis (no_types, lifting) IntD2 fst_conv stepc_elim_cases(2))                             
             moreover have p1:"sj \<in> (fst ` p \<inter> g)" using ss by blast 
             moreover then have 
               "cpn n \<Gamma> csj ((sj,sl)) \<inter> assum(p \<inter> {c. (fst c) \<in> g}, R) \<subseteq> comm(G, (q,a)) F"
               using a1 com_validityn_def cj lj by blast
             moreover then have "l!(Suc j) = (csj, (sj,sl))" 
               using before_k_all_evnt pair_j cj ssj_normal_s lj
               by (metis prod.exhaust_sel)
             ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
               using  j_length a10 a11 \<Gamma>1  ssj_normal_s  k_basic1 
                     cpn_assum_induct[of \<Gamma> l n "Guard f g c1" s "p \<inter> {c. (fst c) \<in> g}" R 
                               "Suc j" c1 "(sj,sl)" "p \<inter> {c. (fst c) \<in> g}" ] lj
               by auto               
             then show ?thesis 
             using a00 a21  a10' \<Gamma>1  j_k j_length 
             cptn_comm_induct[of \<Gamma> l "(Guard f g c1)" s _ "Suc j" G q a F k ]
             unfolding Satis_def by fastforce                         
          qed            
       qed 
       } thus ?thesis by (simp add: c_prod cp) qed
       have concr:"(final_glob (last l)  \<longrightarrow>   fst (last l) \<notin> Fault ` F \<longrightarrow>                  
                   ((fst (last l) = Skip \<and> snd (last l) \<in>  q)) \<or>
                    (fst (last l) = Throw \<and> snd (last l) \<in>  (a)))"
       proof-
       { 
         assume valid:"final_glob (last l)" and final_fault:" fst (last l) \<notin> Fault ` F"             
         have "\<exists>k. k\<ge>0 \<and> k<((length l) - 1) \<and> 
                      \<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                          (fst (l ! Suc k), toSeq (snd (l ! Suc k))) \<and> final_glob (l!(Suc k))"
         proof -             
           have len_l:"length l > 0" using cp using cptn.simps by blast 
           then obtain a1 l1 where l:"l=a1#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
           have last_l:"last l = l!(length l-1)"
            using last_length [of a1 l1] l by fastforce         
           have final_0:"\<not>final_glob(l!0)" using cp unfolding final_glob_def by auto
           have "0\<le> (length l-1)" using len_l last_l by auto
           moreover have "(length l-1) < length l" using len_l by auto
           moreover have "final_glob (l!(length l-1))" using valid last_l by auto
           moreover have "fst (l!0) = (Guard f g c1)" using cp by auto
           ultimately show ?thesis 
             using  cp final_exist_component_tran_final env_tran_right final_0 
             by blast 
          qed
          then obtain k where a21: "k\<ge>0 \<and> k<((length l) - 1) \<and> 
            \<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                (fst (l ! Suc k), toSeq (snd (l ! Suc k))) \<and> final_glob (l!(Suc k))"
            by auto
          then have a00:"Suc k<length l" by fastforce
          then obtain j where before_k_all_evnt:"j\<le>k \<and>  
               \<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                   (fst (l ! Suc j), toSeq (snd (l ! Suc j))) \<and> (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
            using a00 a21 exist_first_comp_tran cp by blast
          then obtain cj sj csj ssj where 
             pair_j:"\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                          (fst (l ! Suc j), toSeq (snd (l ! Suc j))) \<and> 
                      cj = fst (l!j) \<and> sj = toSeq(snd (l!j)) \<and>  
                      csj = fst (l!(Suc j)) \<and> ssj = toSeq(snd(l!(Suc j)))"
          by fastforce        
          have "((fst (last l) = Skip \<and> snd (last l) \<in>  q)) \<or>
                    (fst (last l) = Throw \<and> snd (last l) \<in>  (a))"
          proof -
            have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce    
            then have k_basic1:"cj = (Guard f g c1) \<and> snd (l!j) \<in> (p \<inter> {c. fst c \<in> g})" 
              using  pair_j before_k_all_evnt cp
                    env_tran_right a2 assum a00 stability[of "p \<inter> {c. fst c \<in> g}" R l 0 j j \<Gamma>]
              by force
            then have k_basic:"cj = (Guard f g c1) \<and> sj \<in> ((fst`p) \<inter> g)" 
              using  pair_j before_k_all_evnt cp env_tran_right a2 assum a00 
                     stability[of "p \<inter> {c. fst c \<in> g}" R l 0 j j \<Gamma>]
              by force
            then have ss:"sj \<in> ((fst`p) \<inter> g)" by auto 
            moreover have ssj_normal_s:"ssj = sj" 
              using before_k_all_evnt k_basic pair_j a1 calculation
              by (metis (no_types, lifting) IntD2 Pair_inject stepc_elim_cases(2))
            ultimately obtain sl where 
              lj:"snd (l!j) = (sj, sl) \<and> snd (l!(Suc j)) = (sj, sl)"
              using  cp  l2[of \<Gamma> "fst (l ! j)" "snd (l ! j)" "fst (l ! (Suc j))" "snd (l ! (Suc j))" ] a00
              using before_k_all_evnt pair_j by fastforce
            have cj:"csj=c1" using k_basic pair_j ss a0
              by (metis (no_types, lifting) fst_conv IntD2 stepc_elim_cases(2))                              
            moreover have p1:"sj \<in> ((fst`p) \<inter> g)" using ss by blast 
            moreover then have 
              "cpn n \<Gamma> csj ((sj,sl)) \<inter> assum((p \<inter> {c. fst c \<in> g}), R) \<subseteq> comm(G, (q,a)) F"
              using a1 com_validityn_def cj by blast
            moreover then have "l!(Suc j) = (csj, (sj,sl))" 
              using before_k_all_evnt pair_j cj ssj_normal_s k_basic1 lj
              by (metis prod.exhaust_sel)
            ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
              using  j_length a10 a11 \<Gamma>1  ssj_normal_s 
                      cpn_assum_induct[of \<Gamma> l n "(LanguageCon.com.Guard f g c1)" s "p \<inter> {c. fst c \<in> g}" R] k_basic1 lj
              by fastforce    
            thus ?thesis       
              using j_length  drop_comm a10' \<Gamma>1 
                    cptn_comm_induct[of \<Gamma> l "(Guard f g c1)" s _ "Suc j" G q a F "Suc j"] valid final_fault
              by blast
           qed
         } thus ?thesis by auto 
         qed
       note res = conjI [OF concl concr]}               
       thus ?thesis using  c_prod unfolding comm_def by force qed      
    } thus ?thesis by auto qed 
  } thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed


lemma Guarantee_sound:
  "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [(p \<inter> {c. (fst c) \<in> g}),  R, G, q,a] \<Longrightarrow>
   \<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> {c. (fst c) \<in> g}, R, G, q,a] \<Longrightarrow>  
   Sta p R \<Longrightarrow> 
   f\<in>F \<Longrightarrow>
   \<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G \<Longrightarrow> 
   \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (Guard f g c1) sat [p, R, G, q,a]"
proof -  
  assume
    a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> {c. (fst c) \<in> g}, R, G, q,a]" and
    a1:"\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> {c. (fst c) \<in> g}, R, G, q,a]" and      
    a2: "Sta p R" and
    a3: "\<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G" and
    a4: "f\<in>F"    
  { 
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"  
    then have a1:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> {c. (fst c) \<in> g}, R, G, q,a]" 
      using a1 com_cvalidityn_def by fastforce
    have "cpn n \<Gamma> (Guard f g c1)  s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
    proof -
    {   
      fix c     
      assume a10:"c \<in> cpn n \<Gamma> (Guard f g c1) s" and a11:"c \<in> assum(p, R)"
      then have a10':"c \<in> cp \<Gamma> (Guard f g c1) s"
        unfolding cp_def cpn_def using cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod by fast
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have "c \<in> comm(G, (q,a)) F"      
      proof - 
        {       
        have cp:"l!0=((Guard f g c1),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10' cp_def c_prod by fastforce
        have \<Gamma>1:"(\<Gamma>, l) = c" using c_prod cp by blast
        have assum:"snd(l!0) \<in>  (p) \<and> (\<forall>i. Suc i<length l \<longrightarrow> 
                 (\<Gamma>1)\<turnstile>\<^sub>c(l!i)  \<rightarrow>\<^sub>e (l!(Suc i)) \<longrightarrow>                 
                   (snd(l!i), snd(l!(Suc i))) \<in> R)" 
       using a11 c_prod unfolding assum_def by simp
       then have env_tran:"env_tran \<Gamma> p l R" using env_tran_def cp by blast
       then have env_tran_right: "env_tran_right \<Gamma> l R" 
         using env_tran env_tran_right_def unfolding env_tran_def by auto                     
       have concl:"(\<forall>i. Suc i<length l \<longrightarrow> 
               (\<Gamma>1\<turnstile>\<^sub>c (fst (l ! i), toSeq (snd (l ! i))) \<rightarrow> 
                     (fst (l ! Suc i), toSeq (snd (l ! Suc i))) ) \<longrightarrow>                                            
                 (snd(l!i), snd(l!(Suc i))) \<in> G)"
       proof -
       { fix k ns ns'
         fix k ns ns'
         assume a00:"Suc k<length l" and
                a21:"(\<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                          (fst (l ! Suc k), toSeq (snd (l ! Suc k))) )"                                          
         obtain j where before_k_all_evnt:
           "j\<le>k \<and>  (\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                         (fst (l ! Suc j), toSeq (snd (l ! Suc j))) ) \<and> 
            (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
           using a00 a21 exist_first_comp_tran cp by blast
         then obtain cj sj csj ssj where pair_j:
              "(\<Gamma>\<turnstile>\<^sub>c(cj,sj)  \<rightarrow> (csj,ssj)) \<and> 
                cj = fst (l!j) \<and> sj = toSeq(snd (l!j)) \<and> csj = fst (l!(Suc j)) \<and> 
                 ssj = toSeq(snd(l!(Suc j)))"
           by fast   
         then have  pair_j1:"(\<Gamma>\<turnstile>\<^sub>c(fst (l!j),toSeq(snd (l!j)))  \<rightarrow> (fst (l!(Suc j)),toSeq(snd(l!(Suc j)))))"
           by auto
         have k_basic1:"cj =(Guard f g c1) \<and> snd(l!j) \<in> (p)" 
           using  pair_j before_k_all_evnt cp env_tran_right a2 assum a00 stability[of p R l 0 j j \<Gamma>]
           by force
         have k_basic:"cj =(Guard f g c1) \<and> sj \<in>  (fst`p)" 
           using  pair_j before_k_all_evnt cp env_tran_right a2 assum a00 stability[of p R l 0 j j \<Gamma>]
           by force
         then have ss:"sj \<in> (fst`p)" by auto                 
         have or:"sj\<in> (g \<union> (-g))" by fastforce
         {assume a000:"sj \<in> g"
          then have k_basic:"cj =(Guard f g c1) \<and> sj \<in>  (fst`p \<inter> g)" 
            using ss k_basic by fastforce
          have k_basic1:"cj =(Guard f g c1) \<and> snd(l!j) \<in> (p \<inter> {c. fst c \<in>g})" 
            using a000 k_basic1
            using pair_j ss by auto
          then have ss: "sj \<in>  (fst`p \<inter> g)"
            using ss k_basic by fastforce
          moreover have ssj_normal_s:"ssj = sj" 
            using ss before_k_all_evnt k_basic pair_j a0 stepc_elim_cases(2) calculation
            by (metis a000 snd_conv)   
          ultimately obtain sl where 
           lj:"snd (l!j) = (sj, sl) \<and> snd (l!(Suc j)) = (sj, sl)" 
           using  cp  l2[of \<Gamma> "fst (l ! j)" "snd (l ! j)" "fst (l ! (Suc j))" "snd (l ! (Suc j))"] a00
           using before_k_all_evnt pair_j by fastforce 
          have "(snd(l!k), snd(l!(Suc k))) \<in> G"
            using ss a2 unfolding Satis_def
           proof (cases "k=j")   
             case True                                               
             thus "(snd (l ! k), snd (l ! Suc k)) \<in>  G"
               using pair_j k_basic True ss ssj_normal_s lj a3 unfolding N_def
               using k_basic1 by fastforce
           next
             case False   
             have j_k:"j<k" using  before_k_all_evnt False by fastforce                      
             thus "(snd (l ! k), snd (l ! Suc k)) \<in>  G"
             proof -
               have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce
               have cj:"csj=c1" using k_basic pair_j ss a0
                 by (metis (no_types, lifting) fst_conv IntD2 stepc_elim_cases(2))                             
               moreover have p1:"sj \<in> (fst`p \<inter> g)" using ss by blast 
               moreover then have "cpn n \<Gamma> csj ((sj,sl)) \<inter> assum((p \<inter> {c. fst c \<in>g}), R) \<subseteq> comm(G, (q,a)) F"
                 using a1 com_validityn_def cj by blast
               moreover then have "l!(Suc j) = (csj,  (sj,sl))" 
                 using before_k_all_evnt pair_j cj ssj_normal_s lj k_basic1
                 by (metis prod.exhaust_sel)
               ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
                 using  j_length a10 a11 \<Gamma>1  ssj_normal_s k_basic1 
                     cpn_assum_induct[of \<Gamma> l n "Guard f g c1" s p R "Suc j" c1 "(sj,sl)" "p \<inter> {c. (fst c) \<in> g}"] lj imageE subset_eq
                 by force                     
                then show ?thesis 
                using a3 a00 a21  a10' \<Gamma>1  j_k j_length 
                 cptn_comm_induct[of \<Gamma> l "(Guard f g c1)" s _ "Suc j" G q a F k]
                unfolding Satis_def by fastforce                         
              qed            
          qed
         } note p1=this
         {(* assume "s' \<in> (Collect (not (set_fun g)))"
          then have "s'\<notin>g" by fastforce *)
          assume "sj\<notin>g"
          then have csj_skip:"csj= Fault f \<and> ssj=sj" using k_basic ss pair_j 
            by (meson Pair_inject stepc_elim_cases(2))
          moreover have "j+1<(length l )"
            using a00 before_k_all_evnt  by linarith
          ultimately have "fst (last l) = Fault f" 
            using pair_j i_fault_all_fault[of \<Gamma> l "j+1" f "(length l)-1"]
            by (metis Suc_eq_plus1 Suc_leI cp diff_less last_conv_nth length_greater_0_conv 
                 less_diff_conv list.size(3) not_less0 zero_less_one)      
          then have "(snd(l!k), snd(l!(Suc k))) \<in> G"          
            using ss a2 unfolding Satis_def
           proof (cases "k=j")   
             case True                                               
             thus "(snd (l ! k), snd (l ! Suc k)) \<in>  G"
               using pair_j k_basic True ss   a3 unfolding N_def
               by (metis (mono_tags, lifting) \<open>j + 1 < length l\<close> cp cptn_tran_ce_i csj_skip 
                     k_basic1 mem_Collect_eq prod.exhaust_sel step_ce_eq)               
           next
             case False   
             have j_k:"j<k" using  before_k_all_evnt False by fastforce                      
             thus "(snd (l ! k), snd (l ! Suc k)) \<in>  G"               
               by (metis Suc_leI a00 a21 cp csj_skip only_one_component_tran_j pair_j)                         
          qed         
         }
         then have "(snd(l!k), snd(l!(Suc k))) \<in> G"
           using p1 or by fastforce         
       } thus ?thesis by (simp add: c_prod cp) qed
       have concr:"(final_glob (last l)  \<longrightarrow> fst (last l) \<notin> Fault ` F \<longrightarrow>                  
                   ((fst (last l) = Skip \<and> snd (last l) \<in>  q)) \<or>
                    (fst (last l) = Throw \<and> snd (last l) \<in>  (a)))"
       proof-
       { 
         assume valid:"final_glob (last l)"  and final_fault:"fst (last l) \<notin> Fault ` F"                   
         have "\<exists>k. k\<ge>0 \<and> k<((length l) - 1) \<and>  \<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                          (fst (l ! Suc k), toSeq (snd (l ! Suc k))) \<and> final_glob (l!(Suc k))"
         proof -             
           have len_l:"length l > 0" using cp using cptn.simps by blast 
           then obtain a1 l1 where l:"l=a1#l1" by (metis SmallStepCon.nth_tl length_greater_0_conv)
           have last_l:"last l = l!(length l-1)"
            using last_length [of a1 l1] l by fastforce         
           have final_0:"\<not>final_glob(l!0)" using cp unfolding final_glob_def by auto
           have "0\<le> (length l-1)" using len_l last_l by auto
           moreover have "(length l-1) < length l" using len_l by auto
           moreover have "final_glob (l!(length l-1))" using valid last_l by auto
           moreover have "fst (l!0) = (Guard f g c1)" using cp by auto
           ultimately show ?thesis 
             using  cp final_exist_component_tran_final env_tran_right final_0 
             by blast 
          qed
          then obtain k where a21: "k\<ge>0 \<and> k<((length l) - 1) \<and> 
            \<Gamma>\<turnstile>\<^sub>c (fst (l ! k), toSeq (snd (l ! k))) \<rightarrow> 
                (fst (l ! Suc k), toSeq (snd (l ! Suc k))) \<and> final_glob (l!(Suc k))"
            by auto
          then have a00:"Suc k<length l" by fastforce
          then obtain j where before_k_all_evnt:"j\<le>k \<and>  
               \<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                   (fst (l ! Suc j), toSeq (snd (l ! Suc j))) \<and> (\<forall>k < j. (\<Gamma>\<turnstile>\<^sub>c(l!k)  \<rightarrow>\<^sub>e (l!(Suc k))))"
            using a00 a21 exist_first_comp_tran cp by blast
          then obtain cj sj csj ssj where 
             pair_j:"\<Gamma>\<turnstile>\<^sub>c (fst (l ! j), toSeq (snd (l ! j))) \<rightarrow> 
                          (fst (l ! Suc j), toSeq (snd (l ! Suc j))) \<and> 
                      cj = fst (l!j) \<and> sj = toSeq(snd (l!j)) \<and>  
                      csj = fst (l!(Suc j)) \<and> ssj = toSeq(snd(l!(Suc j)))"
          by fastforce         
          have "((fst (last l) = Skip \<and> snd (last l) \<in>  q)) \<or>
                    (fst (last l) = Throw \<and> snd (last l) \<in> (a))"
          proof -
            have j_length:"Suc j < length l" using a00 before_k_all_evnt by fastforce    
            have k_basic1:"cj =(Guard f g c1) \<and> snd (l!j) \<in>  (p)" 
              using  pair_j before_k_all_evnt cp env_tran_right a2 assum a00 stability[of p R l 0 j j \<Gamma>]
              by force
            have k_basic:"cj =(Guard f g c1) \<and> sj \<in> (fst`p)" 
             using  pair_j before_k_all_evnt cp env_tran_right a2 assum a00 stability[of p R l 0 j j \<Gamma>]
             by force
            then have ss:"sj \<in> (fst`p)" by auto 
            have or:"sj\<in> (g \<union> (-g))" by fastforce
            { assume a000:"sj \<in> g"
              then have k_basic:"cj =(Guard f g c1) \<and> sj \<in> (fst`p \<inter> g)" 
                using ss k_basic by fastforce
              have k_basic1:"cj =(Guard f g c1) \<and> snd(l!j) \<in> (p \<inter> {c. fst c \<in>g})" 
                using a000 k_basic1
                using pair_j ss by auto
              then have k_basic:"cj =(Guard f g c1) \<and> sj \<in> (fst`p \<inter> g)" 
                using ss k_basic by fastforce
              then have ss: "sj \<in> (fst`p \<inter> g)"
                using ss by fastforce
              moreover have ssj_normal_s:"ssj = sj" 
                using before_k_all_evnt k_basic pair_j a1 calculation
                by (metis (no_types, lifting) Pair_inject IntD2 stepc_elim_cases(2))               
              ultimately obtain sl where 
                lj:"snd (l!j) = (sj, sl) \<and> snd (l!(Suc j)) = (sj, sl)"
                using  cp  
                   l2[of \<Gamma> "fst (l ! j)" "snd (l ! j)" "fst (l ! (Suc j))" "snd (l ! (Suc j))"] a00
                using before_k_all_evnt pair_j by fastforce
              have cj:"csj=c1" using k_basic pair_j ss a0
                by (metis (no_types, lifting) fst_conv IntD2 stepc_elim_cases(2))                              
              moreover have p1:"sj\<in>(fst`p \<inter> g)" using ss by blast 
              moreover then have "cpn n \<Gamma> csj ( (sj,sl)) \<inter> assum((p \<inter> {c. fst c\<in>g}), R)  \<subseteq> comm(G, (q,a)) F"
                using a1 com_validityn_def cj by blast
             moreover then have "l!(Suc j) = (csj,  (sj,sl))" 
               using before_k_all_evnt pair_j cj ssj_normal_s k_basic1 lj
              by (metis prod.exhaust_sel)
             ultimately have drop_comm:"((\<Gamma>, drop (Suc j) l))\<in> comm(G, (q,a)) F"
              using  j_length a10 a11 \<Gamma>1  ssj_normal_s cpn_assum_induct[of \<Gamma> l n "Guard f g c1" s] k_basic1 lj
              by fastforce                
            then have ?thesis       
              using j_length  drop_comm a10' \<Gamma>1 
                     cptn_comm_induct[of \<Gamma> l "(Guard f g c1)" s _ "Suc j" G q a F "Suc j"]
                    valid final_fault  
              by blast
           }note left=this        
           {
            (* assume "s' \<in> (Collect (not (set_fun g)))"
            then have "s'\<notin>g" by fastforce *)
             assume "sj\<notin>g"
             then have "csj= Fault f \<and> ssj=sj" using k_basic ss pair_j
               by (metis prod.inject stepc_elim_cases(2))
             then have "fst (last l) = Fault f" using pair_j a4 cp imageI j_length last_not_F
               by (metis final_fault)                 
             then have False using a4 final_fault by auto           
           }
           thus ?thesis using or left by auto qed
         } thus ?thesis by auto 
         qed
       note res = conjI [OF concl concr]}               
       thus ?thesis using  c_prod unfolding comm_def by force qed      
    } thus ?thesis by auto qed 
  } thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def) 
qed

lemma WhileNone:   
   "\<Gamma>\<turnstile>\<^sub>c (While b c1, toSeq s1) \<rightarrow> (LanguageCon.com.Skip, toSeq t1) \<Longrightarrow>   
    snd s1 = snd t1 \<Longrightarrow>
    (n,\<Gamma>, (Skip, t1) # xsa) \<in> cptn_mod_nest_call \<Longrightarrow>  
    \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> {c. fst c \<in> b},R, G, p,a] \<Longrightarrow>
    Sta p R \<Longrightarrow>
    Sta (p \<inter> ({c. fst c \<in> -b})) R \<Longrightarrow>
    Sta a R \<Longrightarrow>
    \<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G \<Longrightarrow>            
    (\<Gamma>, (While b c1, s1) # (LanguageCon.com.Skip, t1) # xsa) \<in> assum (p, R) \<Longrightarrow>    
    (\<Gamma>, (While b c1, s1) # (LanguageCon.com.Skip, t1) # xsa) \<in> comm (G,(p \<inter> {c. fst c \<in> -b}),a) F"
proof -
  assume a0:"\<Gamma>\<turnstile>\<^sub>c (While b c1, toSeq s1) \<rightarrow> (LanguageCon.com.Skip, toSeq t1)" and 
         a0':"snd s1 = snd t1" and
         a1:"(n,\<Gamma>, (Skip, t1) # xsa) \<in> cptn_mod_nest_call" and
         a2:" \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> {c. fst c \<in> b},R, G, p,a]" and
         a3:"Sta p R" and
         a4:"Sta (p \<inter> ({c. fst c \<in> -b})) R" and
         a5:"Sta a R" and
         a6:"\<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G" and
         a7:"(\<Gamma>, (While b c1, s1) # (LanguageCon.com.Skip, t1) # xsa) \<in> assum (p, R)"         
  have ps1N:"s1 \<in> p" using a7 unfolding assum_def by fastforce
  then have "toSeq s1 \<in> fst ` p"
    by simp    
  then have s1_t1:"toSeq s1 \<notin> b \<and> toSeq t1=toSeq s1" using a0
    using LanguageCon.com.distinct(5) prod.inject
    by (metis stepc_elim_cases(7))    
  have eq_t1_s1:"s1\<notin> {c. fst c \<in> b} \<and> t1 = s1" using a0'
    by (metis s1_t1 mem_Collect_eq prod_eqI  toSeq.simps(1) ) 
  then have st1_Normal_post:"t1\<in>  (p \<inter> {c. fst c \<in> -b})"
    by (simp add: ps1N)
  also have "(\<Gamma>, (While b c1, s1) # (LanguageCon.com.Skip, t1) # xsa)\<in>cptn"
    using a1 a0 cptn.simps             
    using cptn_eq_cptn_mod_set  a0' cptn_onlyif_cptn_mod_aux[OF _ _ a0 a0' cptn_mod_nest_cptn_mod[OF a1]]
    by fastforce
  ultimately have assum_skip:
    "(\<Gamma>,(LanguageCon.com.Skip, t1) # xsa) \<in> assum (( p \<inter> {c. fst c \<in> -b}), R)"
    using a1 a7 tl_of_assum_in_assum1 st1_Normal_post by fastforce
  have skip_comm:"(\<Gamma>,(LanguageCon.com.Skip, t1) # xsa) \<in> 
               comm (G,(( p \<inter> {c. fst c \<in> -b}),a)) F" 
  proof- 
    obtain \<Theta> where  "(\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p , R, G, q,a])" by auto
    moreover have "\<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> Skip sat [( p \<inter> {c. fst c \<in> -b}), R, G, ( p \<inter> {c. fst c \<in> -b}),a]"
      using Skip_sound[of "(p \<inter> {c. fst c \<in> -b})"]  a4 a6   by blast
    ultimately have "\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> LanguageCon.com.Skip sat [p \<inter> {c. fst c \<in> - b},R, G, p \<inter> {c. fst c \<in> - b},a]"
      unfolding com_cvalidityn_def by fastforce
    then show ?thesis
      using assum_skip  a1  unfolding  com_validityn_def  cpn_def 
      by fastforce
  qed    
  have G_ref:"( s1,  s1)\<in>G" using a6 unfolding N_def
    using ps1N by blast
  thus ?thesis using skip_comm ctran_in_comm[of s1]  
    using eq_t1_s1 ps1N by blast
qed 

lemma while1:
   "(n,\<Gamma>, ((c,  s1) # xs1)) \<in> cptn_mod_nest_call \<Longrightarrow>        
    s1 \<in> {c. fst c \<in> b} \<Longrightarrow>
    xsa = map (lift (While b c)) xs1 \<Longrightarrow>
    \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c sat [p \<inter>{c. fst c \<in> b},R, G, p,a] \<Longrightarrow>    
    (\<Gamma>, (While b c,  s1) #
        (Seq c (LanguageCon.com.While b c),  s1) # xsa)
       \<in> assum (p, R)  \<Longrightarrow>               
    \<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G \<Longrightarrow> 
     (\<Gamma>, (LanguageCon.com.While b c,  s1) #
         (LanguageCon.com.Seq c (LanguageCon.com.While b c),  s1) # xsa)
    \<in> comm (G, p\<inter>{c. fst c \<in> -b}, a) F"
proof -
assume   
  a0:"(n,\<Gamma>, ((c,  s1) # xs1)) \<in> cptn_mod_nest_call" and  
  a1:"s1 \<in>{c. fst c \<in> b}" and
  a2:"xsa = map (lift (While b c)) xs1" and
  a3:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c sat [p \<inter> {c. fst c \<in> b},R, G, p,a]" and
  a4:"(\<Gamma>, (While b c,  s1) #
        (Seq c (While b c),  s1) # xsa)
       \<in> assum (p, R) " and  
  a5:"\<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G" 
  have seq_map:"(Seq c (While b c),  s1) # xsa=
           map (lift (While b c)) ((c, s1)#xs1)"
  using a2 unfolding lift_def by fastforce
  have step:"\<Gamma>\<turnstile>\<^sub>c(While b c,toSeq ( s1)) \<rightarrow> (Seq c (While b c),toSeq( s1))" using a1
    WhileTruec by force
  have s1_normal:"s1 \<in> p \<and> s1 \<in> {c. fst c \<in> b} " using a4 a1 unfolding assum_def by fastforce
  then have G_ref:"( s1,  s1) \<in> G"  using a5 unfolding N_def by fastforce 
  have s1_collect_p: " s1\<in>  (p \<inter> {c. fst c \<in> b})" using s1_normal by fastforce
  have "(\<Gamma>, map (lift (While b c)) ((c, s1)#xs1))\<in>cptn" 
    using a2 cptn_eq_cptn_mod_nest lift_is_cptn a0  by blast 
  then have cptn_seq:"(\<Gamma>,(Seq c (While b c),  s1) # xsa) \<in>cptn" 
    using seq_map by auto
  moreover have "fst s1 \<in> b" using a1 by force
  ultimately have "(\<Gamma>, (While b c,  s1) # (Seq c (While b c),  s1) # xsa) \<in> cptn"
    by (metis (no_types) a0 a2 cptn_eq_cptn_mod_set cptn_mod.CptnModWhile1 cptn_mod_nest_cptn_mod)
  then have assum_seq:"(\<Gamma>,(Seq c (While b c),  s1) # xsa)\<in>assum (p, R)"
    using a4 tl_of_assum_in_assum1 s1_collect_p by fast
  have cp_c:"(\<Gamma>, ((c,  s1) # xs1)) \<in> (cpn n \<Gamma> c ( s1))"
    using a0 unfolding cpn_def by fastforce
  then have cp_c':"(\<Gamma>, ((c,  s1) # xs1)) \<in> (cp \<Gamma> c ( s1))"
    unfolding cp_def cpn_def using cptn_eq_cptn_mod_nest by fastforce    
  also have cp_seq:"(\<Gamma>, (Seq c (While b c),  s1) # xsa) \<in> (cp \<Gamma> (Seq c (While b c)) ( s1))"
    using cptn_seq unfolding cp_def by fastforce
  ultimately have "(\<Gamma>, ((c,  s1) # xs1)) \<in> assum(p,R)"  
    using assum_map assum_seq seq_map by fastforce  
  then have "(\<Gamma>, ((c,  s1) # xs1)) \<in> assum((p \<inter> {c. fst c \<in> b}),R)"
    unfolding assum_def using s1_collect_p by fastforce
  then have "(\<Gamma>, ((c,  s1) # xs1)) \<in> comm(G,(p,a)) F"
    using a3 cp_c unfolding com_validityn_def by fastforce
  then have "(\<Gamma>, (Seq c (While b c),  s1) # xsa) \<in> comm(G,(p,a)) F"
    using cp_seq cp_c' comm_map seq_map by fastforce
  then have "(\<Gamma>, (While b c,  s1) # (Seq c (While b c),  s1) # xsa) \<in> comm(G,(p,a)) F"
    using G_ref ctran_in_comm
    by (simp add: ctran_in_comm)
  also have "\<not> final_glob (last ((While b c,  s1) # (Seq c (While b c),  s1) # xsa))"
    using seq_map unfolding final_glob_def lift_def  by (simp add: case_prod_beta' last_map)  
  ultimately show ?thesis using not_final_in_comm[of \<Gamma>] by blast
qed

lemma while2:
   " (n,\<Gamma>, (While b c,  s1) #
         (Seq c (While b c),  s1) # xsa) \<in>cptn_mod_nest_call \<Longrightarrow>
    (n, \<Gamma>, (c,  s1) # xs1) \<in> cptn_mod_nest_call \<Longrightarrow>
    fst (last ((c,  s1) # xs1)) = LanguageCon.com.Skip \<Longrightarrow>
    s1 \<in> {c. fst c \<in> b} \<Longrightarrow>
    xsa = map (lift (While b c)) xs1 @
    (While b c, snd (last ((c,  s1) # xs1))) # ys \<Longrightarrow>
    (n, \<Gamma>, (While b c, snd (last ((c,  s1) # xs1))) # ys)
      \<in> cptn_mod_nest_call \<Longrightarrow>
     (\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c sat [p \<inter> {c. fst c \<in> b}, R, G, p,a] \<Longrightarrow>    
       (\<Gamma>, (While b c, snd (last ((c,  s1) # xs1))) # ys)
         \<in> assum (p, R) \<Longrightarrow>
       (\<Gamma>, (While b c, snd (last ((c,  s1) # xs1))) # ys)
          \<in> comm (G, p \<inter> {c. fst c \<in> -b}, a) F) \<Longrightarrow>
    \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c sat [ p \<inter> {c. fst c \<in> b}, R, G, p,a] \<Longrightarrow>
    (\<Gamma>, (While b c,  s1) #
      (Seq c (While b c),  s1) # xsa)
      \<in> assum (p, R)  \<Longrightarrow>
     \<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G  \<Longrightarrow>     
    (\<Gamma>, (While b c,  s1) #
         (Seq c (While b c),  s1) # xsa)
      \<in> comm (G,( p \<inter> {c. fst c \<in> -b}, a)) F"
proof -
assume a00:"(n, \<Gamma>, (While b c,  s1) #
         (Seq c (While b c),  s1) # xsa) \<in>cptn_mod_nest_call" and
       a0:"(n,\<Gamma>, (c,  s1) # xs1) \<in> cptn_mod_nest_call" and
       a1:" fst (last ((c,  s1) # xs1)) = LanguageCon.com.Skip" and
       a2:"s1 \<in> {c. fst c \<in> b}" and
       a3:"xsa = map (lift (While b c)) xs1 @
            (While b c, snd (last ((c,  s1) # xs1))) # ys" and
       a4:"(n,\<Gamma>, (While b c, snd (last ((c,  s1) # xs1))) # ys)
            \<in> cptn_mod_nest_call" and
       a5:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c sat [p \<inter> {c. fst c \<in> b}, R, G, p,a]" and       
       a6:"(\<Gamma>, (While b c,  s1) #
               (Seq c (While b c),  s1) # xsa)
             \<in> assum (p, R)" and
       a7:"(\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c sat [p \<inter> {c. fst c \<in> b}, R, G, p,a] \<Longrightarrow>    
           (\<Gamma>, (While b c, snd (last ((c,  s1) # xs1))) # ys)
             \<in> assum (p, R) \<Longrightarrow>
           (\<Gamma>, (While b c, snd (last ((c,  s1) # xs1))) # ys)
             \<in> comm (G,p \<inter> {c. fst c \<in> -b}, a) F)" and
       a8:"\<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G" 
  let ?l= "(While b c,  s1) #
           (Seq c (While b c),  s1) # xsa"
  let ?sub_l="((While b c,  s1) # 
                 (Seq c (While b c),  s1) # 
                 map (lift (While b c)) xs1)"  
  have a0':"(\<Gamma>, (c,  s1) # xs1) \<in> cptn"
    using cptn_eq_cptn_mod_nest using a0 by auto
  have a4:"(\<Gamma>, (While b c, snd (last ((c,  s1) # xs1))) # ys) \<in> cptn" 
    using cptn_eq_cptn_mod_nest using a4 by blast
  have seq_map:"(Seq c (While b c),  s1) # map (lift (While b c)) xs1=
           map (lift (While b c)) ((c, s1)#xs1)"
  using a2 unfolding lift_def by fastforce
  have step:"\<Gamma>\<turnstile>\<^sub>c(While b c,toSeq ( s1)) \<rightarrow> (Seq c (While b c),toSeq ( s1))" using a2
    WhileTruec by fastforce
  have s1_normal:"s1\<in>p \<and> s1 \<in> {c. fst c \<in> b} " using a6 a2 unfolding assum_def by fastforce
  then have G_ref:"( s1,  s1)\<in>G" using a8  unfolding N_def by blast
  have s1_collect_p: " s1\<in>  (p \<inter> {c. fst c \<in> b})" using s1_normal by fastforce
  have "(\<Gamma>, map (lift (While b c)) ((c, s1)#xs1))\<in>cptn" 
    using a2 cptn_eq_cptn_mod lift_is_cptn a0' by fastforce
  then have cptn_seq:"(\<Gamma>,(Seq c (While b c),  s1) # map (lift (While b c)) xs1) \<in>cptn" 
    using seq_map by auto
  then have "(\<Gamma>, (While b c,  s1) # 
                 (Seq c (While b c),  s1) # 
                  map (lift (While b c)) xs1) \<in> cptn"
    using step
    by (metis (no_types) LanguageCon.com.distinct(5) a0' cptn_eq_cptn_mod_set cptn_mod.CptnModWhile1 
             local.step prod.inject stepc_elim_cases(7) toSeq.simps(1)) 
  also have "(\<Gamma>, (While b c,  s1) #
                 (Seq c (While b c),  s1) #
                  map (lift (While b c)) xs1)
          \<in> assum (p, R)"
    using a6 a3 sub_assum
    by (metis append_Cons) 
  ultimately have assum_seq:"(\<Gamma>,(Seq c (While b c),  s1)  # 
                       map (lift (While b c)) xs1) \<in> assum (p, R)"
    using a6 tl_of_assum_in_assum1 s1_collect_p 
          tl_of_assum_in_assum   by fast
  have cpn_c:"(\<Gamma>, ((c,  s1) # xs1)) \<in> (cpn n \<Gamma> c ( s1))"
    using a0 unfolding cpn_def by fastforce
  have cp_c:"(\<Gamma>, ((c,  s1) # xs1)) \<in> (cp \<Gamma> c ( s1))"
    using a0' unfolding cp_def by fastforce  
  also have cp_seq:"(\<Gamma>, (Seq c (While b c),  s1) # map (lift (While b c)) xs1) \<in> 
                      (cp \<Gamma> (Seq c (While b c)) ( s1))"
    using cptn_seq unfolding cp_def by fastforce
  ultimately have "(\<Gamma>, ((c,  s1) # xs1)) \<in> assum(p,R) "  
    using assum_map assum_seq seq_map  by fastforce  
  then have "(\<Gamma>, ((c,  s1) # xs1)) \<in> assum((p \<inter> {c. fst c \<in> b}),R) "
    unfolding assum_def using s1_collect_p by fastforce
  then have c_comm:"(\<Gamma>, ((c,  s1) # xs1)) \<in> comm(G,(p,a)) F"
    using a5 cpn_c unfolding com_validityn_def by fastforce
  then have "(\<Gamma>, (Seq c (While b c),  s1) # map (lift (While b c)) xs1) \<in> comm(G,(p,a)) F"
    using cp_seq cp_c comm_map seq_map by fastforce
  then have comm_while:"(\<Gamma>, (While b c,  s1) # 
                            (Seq c (While b c),  s1) # 
                            map (lift (While b c)) xs1) \<in> comm(G,(p,a)) F"
    using G_ref 
    by (simp add: ctran_in_comm)
  have final_last_c:"final_glob (last ((c, s1)#xs1))"
    using a1 a3 unfolding final_glob_def by fastforce
  have last_while1:"snd (last (map (lift (While b c)) ((c, s1)#xs1))) = snd (last ((c,  s1) # xs1))"
    unfolding lift_def by (simp add: case_prod_beta' last_map)
  have last_while2:"(last (map (lift (While b c)) ((c, s1)#xs1))) =
           last ((While b c,  s1) # (Seq c (While b c),  s1) # map (lift (While b c)) xs1)"
    using seq_map by fastforce 
  then have last_c_normal:"snd (last ( (c, s1)#xs1)) \<in>  p"
    using c_comm a1 unfolding comm_def final_glob_def by fastforce    
  then obtain sl where sl:"snd (last ( (c, s1)#xs1)) =  sl" by fastforce
  have while_comm:"(\<Gamma>, (While b c, snd (last ((c, s1) # xs1))) # ys) \<in> comm(G,(p\<inter>({c. fst c \<in> -b}),a)) F"
  proof -
    have assum_while: "(\<Gamma>, (While b c, snd (last ((c,  s1) # xs1))) # ys)
             \<in> assum (p, R)"
      using last_c_normal a3 a6 sub_assum_r[of \<Gamma> ?sub_l "(While b c, snd (last ((c,  s1) # xs1)))"  ys p R p] 
      by fastforce
    thus ?thesis using a5 a7 by fastforce
  qed      
  have "sl\<in>p" using last_c_normal sl by fastforce
  then have G1_ref:"( sl,  sl)\<in>G" using a8 unfolding N_def by blast
  also have "snd (last ?sub_l) =  sl"
    using last_while1 last_while2 sl by fastforce
  ultimately show ?thesis 
    using  cptn_eq_cptn_mod_nest a00 a3 sl while_comm comm_union[OF comm_while]  
    by fastforce     
qed

lemma while3:
   "(n, \<Gamma>, (c,  s1) # xs1) \<in> cptn_mod_nest_call \<Longrightarrow>    
    fst (last ((c,  s1) # xs1)) = Throw \<Longrightarrow>
    s1 \<in> {c. fst c \<in> b} \<Longrightarrow>
    snd (last ((c,  s1) # xs1)) =  sl \<Longrightarrow>
    (n,\<Gamma>, (Throw, sl) # ys) \<in> cptn_mod_nest_call   \<Longrightarrow>
    \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c sat [p \<inter> {c. fst c \<in> b},R, G, p,a] \<Longrightarrow>    
    (\<Gamma>, (While b c,  s1) #
         (Seq c (While b c),  s1) #  
         (map (lift (While b c)) xs1 @
           (Throw,  sl) # ys))
       \<in> assum (p, R)  \<Longrightarrow>        
     Sta p R \<Longrightarrow>
     Sta a R \<Longrightarrow> \<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G \<Longrightarrow> 
    (\<Gamma>, (While b c,  s1) #
         (Seq c (While b c),  s1) #          
         ((map (lift (While b c)) xs1 @
           (Throw,  sl) # ys))) \<in> comm (G, p\<inter> ({c. fst c \<in> -b}), a) F
"
proof -
assume a0:"(n,\<Gamma>, (c,  s1) # xs1) \<in> cptn_mod_nest_call" and
       a1:"fst (last ((c,  s1) # xs1)) = Throw" and
       a2:"s1 \<in> {c. fst c \<in> b}" and
       a3:"snd (last ((c,  s1) # xs1)) = sl" and
       a4:"(n,\<Gamma>, (Throw,  sl) # ys) \<in> cptn_mod_nest_call" and
       a5:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c sat [p \<inter> {c. fst c \<in> b}, R, G, p,a]" and
       a6:"(\<Gamma>, (While b c,  s1) #
           (Seq c (While b c),  s1) #  
           (map (lift (While b c)) xs1 @
             (Throw,  sl) # ys)) \<in> assum (p, R)" and      
       a7: "Sta p R" and
       a8: "Sta a R" and       
       a10:"\<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G"  
  have seq_map:"(Seq c (While b c),  s1) # map (lift (While b c)) xs1=
           map (lift (While b c)) ((c, s1)#xs1)"
  using a2 unfolding lift_def by fastforce
  have step:"\<Gamma>\<turnstile>\<^sub>c(While b c,toSeq( s1)) \<rightarrow> (Seq c (While b c),toSeq( s1))" 
    using a2 WhileTruec by fastforce
  have s1_normal:"s1\<in>p \<and> s1 \<in> {c. fst c \<in> b} " using a6 a2 unfolding assum_def by fastforce
  then have G_ref:"( s1,  s1)\<in>G" using a10 unfolding N_def by blast
  have s1_collect_p: " s1\<in>  (p \<inter>{c. fst c \<in> b})" using s1_normal by fastforce
  have "(n, \<Gamma>, map (lift (While b c)) ((c, s1)#xs1))\<in>cptn_mod_nest_call" 
    using a2  a0
    by (metis cptn_mod_nest_call.CptnModNestSeq1 seq_map) 
  then have cptn_seq:"(n,\<Gamma>,(Seq c (While b c),  s1) # map (lift (While b c)) xs1) \<in>cptn_mod_nest_call" 
    using seq_map by auto
  then have cptn:"(n,\<Gamma>, (While b c,  s1) # (Seq c (While b c),  s1) # 
                    map (lift (While b c)) xs1) \<in> cptn_mod_nest_call"
    using a0 a2 cptn_mod_nest_call.CptnModNestWhile1
    by blast 
  also have "(\<Gamma>, (LanguageCon.com.While b c,  s1) #
         (LanguageCon.com.Seq c (LanguageCon.com.While b c),  s1) #
         map (lift (LanguageCon.com.While b c)) xs1)
          \<in> assum (p, R) "
    using a6 sub_assum
    by (metis append_Cons) 
  ultimately have assum_seq:"(\<Gamma>,(Seq c (While b c),  s1)  # 
                       map (lift (While b c)) xs1) \<in> assum (p, R)"
    using a6 tl_of_assum_in_assum1 s1_collect_p 
          tl_of_assum_in_assum cptn_eq_cptn_mod_nest  by fast
  have cpn_c:"(\<Gamma>, ((c,  s1) # xs1)) \<in> (cpn n \<Gamma> c ( s1))"
    using a0 unfolding cpn_def by fastforce
  then have cp_c:"(\<Gamma>, ((c,  s1) # xs1)) \<in> (cp \<Gamma> c ( s1))"
    unfolding cp_def cpn_def using cptn_eq_cptn_mod_nest by auto
  moreover have cp_seq:"(\<Gamma>, (Seq c (While b c),  s1) # map (lift (While b c)) xs1) \<in> 
           (cpn n \<Gamma> (Seq c (While b c)) ( s1))"
    using cptn_seq unfolding cpn_def by fastforce
  then have cp_seq':"(\<Gamma>, (Seq c (While b c),  s1) # map (lift (While b c)) xs1) \<in> 
            (cp \<Gamma> (Seq c (While b c)) ( s1))"
    unfolding cp_def cpn_def using cptn_eq_cptn_mod_nest by auto
  ultimately have "(\<Gamma>, ((c,  s1) # xs1)) \<in> assum(p,R)"  
    using assum_map assum_seq seq_map  by fastforce
  then have "(\<Gamma>, ((c,  s1) # xs1)) \<in> assum((p \<inter> {c. fst c \<in> b}),R)"
    unfolding assum_def using s1_collect_p by fastforce
  then have c_comm:"(\<Gamma>, ((c,  s1) # xs1)) \<in> comm(G,(p,a)) F"
    using a5 cpn_c unfolding com_validityn_def by fastforce
  then have "(\<Gamma>, (Seq c (While b c),  s1) # map (lift (While b c)) xs1) \<in> comm(G,(p,a)) F"
    using cp_seq' cp_c comm_map seq_map by fastforce
  then have comm_while:"(\<Gamma>, (While b c,  s1) # (Seq c (While b c),  s1) # 
         map (lift (While b c)) xs1) \<in> comm(G,(p,a)) F"
    using G_ref ctran_in_comm by blast
  have final_last_c:"final_glob (last ((c, s1)#xs1))"
    using a1 a3 unfolding final_glob_def by fastforce
  have not_fault_final_last_c:
    "fst (last ( (c, s1)#xs1)) \<notin> Fault ` F"
    using a3 a1 by auto
  then have sl_a:" sl \<in>  (a)"  
    using final_last_c a1 c_comm unfolding comm_def
    using  a3 comm_dest2   
    by auto
  have last_while1:"snd (last (map (lift (While b c)) ((c, s1)#xs1))) = snd (last ((c,  s1) # xs1))"
    unfolding lift_def by (simp add: case_prod_beta' last_map)
  have last_while2:"(last (map (lift (While b c)) ((c, s1)#xs1))) =
           last ((While b c,  s1) # (Seq c (While b c),  s1) # map (lift (While b c)) xs1)"
    using seq_map by fastforce
  have throw_comm:"(\<Gamma>, (Throw,  sl) # ys) \<in> comm(G,(p\<inter>({c. fst c \<in> -b}),a)) F"
  proof -
    have assum_throw: "(\<Gamma>, (Throw,  sl) # ys) \<in> assum (a,R)"
      using sl_a a6 sub_assum_r[of _ "(LanguageCon.com.While b c,  s1) #
         (LanguageCon.com.Seq c (LanguageCon.com.While b c),  s1) #
         map (lift (LanguageCon.com.While b c)) xs1" "(Throw,  sl)" ] 
      by fastforce
    also have "(\<Gamma>,(Throw,  sl) # ys) \<in> cpn n \<Gamma> Throw ( sl)" 
      unfolding cpn_def using a4 by fastforce
    ultimately show ?thesis using Throw_sound[of a R ]  a8   
      unfolding com_cvalidityn_def com_validityn_def by fast
  qed  
  have p1:"(LanguageCon.com.While b c,  s1) #
    (LanguageCon.com.Seq c (LanguageCon.com.While b c),  s1) #
    map (lift (LanguageCon.com.While b c)) xs1 \<noteq> [] \<and>
    (LanguageCon.com.Throw,  sl) # ys \<noteq> []" by auto  
  have "sl \<in> a" using sl_a by fastforce
  then have G1_ref:"( sl,  sl) \<in> G" 
    using a0 a10 a3 cp_c s1_normal cptn_all_len_eq_0  cptn_if_cptn_mod cptn_mod_nest_cptn_mod
    unfolding N_def cp_def
    by (smt last_length length_Cons lessI mem_Collect_eq nth_Cons_0 snd_conv)
  moreover have "snd (last ((While b c,  s1) # 
                  (Seq c (While b c),  s1) # 
                  map (lift (While b c)) xs1)) =  sl"
    using last_while1 last_while2 a3 by fastforce
  moreover have "snd (((LanguageCon.com.Throw,  sl) # ys) ! 0) =  sl"
    by (metis nth_Cons_0 snd_conv)
  ultimately have G:"(snd (last ((While b c,  s1) # 
                  (Seq c (While b c),  s1) # 
                  map (lift (While b c)) xs1)),
                  snd (((LanguageCon.com.Throw,  sl) # ys) ! 0)) \<in> G" by auto
  have cptn:"(\<Gamma>, ((LanguageCon.com.While b c,  s1) #
          (LanguageCon.com.Seq c (LanguageCon.com.While b c),  s1) #
          map (lift (LanguageCon.com.While b c)) xs1) @
         (LanguageCon.com.Throw,  sl) # ys)
    \<in> cptn" using cptn a4  a0 a1 a3 a4 cptn_eq_cptn_mod_set cptn_mod.CptnModWhile3 s1_normal 
             cptn_eq_cptn_mod_nest
    by (metis append_Cons mem_Collect_eq) 
  show ?thesis using a0  comm_union[OF comm_while throw_comm p1 G cptn] by auto       
qed


lemma while4:
   "(n, \<Gamma>, (c,  s1) # xs1) \<in> cptn_mod_nest_call \<Longrightarrow>    
    fst (last ((c,  s1) # xs1)) = Stuck \<Longrightarrow>
    s1 \<in> {c. fst c \<in> b} \<Longrightarrow>
    snd (last ((c,  s1) # xs1)) =  sl \<Longrightarrow>
    (n,\<Gamma>, (Stuck, sl) # ys) \<in> cptn_mod_nest_call   \<Longrightarrow>
    \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c sat [p \<inter> {c. fst c \<in> b},R, G, p,a] \<Longrightarrow>    
    (\<Gamma>, (While b c,  s1) #
         (Seq c (While b c),  s1) #  
         (map (lift (While b c)) xs1 @
           (Stuck,  sl) # ys))
       \<in> assum (p, R)  \<Longrightarrow>        
     Sta p R \<Longrightarrow>
     Sta a R \<Longrightarrow> \<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G \<Longrightarrow> 
    (\<Gamma>, (While b c,  s1) #
         (Seq c (While b c),  s1) #          
         ((map (lift (While b c)) xs1 @
           (Stuck,  sl) # ys))) \<in> comm (G, p\<inter> ({c. fst c \<in> -b}), a) F
"
proof -
assume a0:"(n,\<Gamma>, (c,  s1) # xs1) \<in> cptn_mod_nest_call" and
       a1:"fst (last ((c,  s1) # xs1)) = Stuck" and
       a2:"s1 \<in> {c. fst c \<in> b}" and
       a3:"snd (last ((c,  s1) # xs1)) = sl" and
       a4:"(n,\<Gamma>, (Stuck,  sl) # ys) \<in> cptn_mod_nest_call" and
       a5:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c sat [p \<inter> {c. fst c \<in> b}, R, G, p,a]" and
       a6:"(\<Gamma>, (While b c,  s1) #
           (Seq c (While b c),  s1) #  
           (map (lift (While b c)) xs1 @
             (Stuck,  sl) # ys)) \<in> assum (p, R)" and      
       a7: "Sta p R" and
       a8: "Sta a R" and       
       a10:"\<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G"  
  have seq_map:"(Seq c (While b c),  s1) # map (lift (While b c)) xs1=
           map (lift (While b c)) ((c, s1)#xs1)"
  using a2 unfolding lift_def by fastforce
  have step:"\<Gamma>\<turnstile>\<^sub>c(While b c,toSeq( s1)) \<rightarrow> (Seq c (While b c),toSeq( s1))" 
    using a2 WhileTruec by fastforce
  have s1_normal:"s1\<in>p \<and> s1 \<in> {c. fst c \<in> b} " using a6 a2 unfolding assum_def by fastforce
  then have G_ref:"( s1,  s1)\<in>G" using a10 unfolding N_def by blast
  have s1_collect_p: " s1\<in>  (p \<inter>{c. fst c \<in> b})" using s1_normal by fastforce
  have "(n, \<Gamma>, map (lift (While b c)) ((c, s1)#xs1))\<in>cptn_mod_nest_call" 
    using a2  a0
    by (metis cptn_mod_nest_call.CptnModNestSeq1 seq_map) 
  then have cptn_seq:"(n,\<Gamma>,(Seq c (While b c),  s1) # map (lift (While b c)) xs1) \<in>cptn_mod_nest_call" 
    using seq_map by auto
  then have cptn:"(n,\<Gamma>, (While b c,  s1) # (Seq c (While b c),  s1) # 
                    map (lift (While b c)) xs1) \<in> cptn_mod_nest_call"
    using a0 a2 cptn_mod_nest_call.CptnModNestWhile1
    by blast 
  also have "(\<Gamma>, (LanguageCon.com.While b c,  s1) #
         (LanguageCon.com.Seq c (LanguageCon.com.While b c),  s1) #
         map (lift (LanguageCon.com.While b c)) xs1)
          \<in> assum (p, R) "
    using a6 sub_assum
    by (metis append_Cons) 
  ultimately have assum_seq:"(\<Gamma>,(Seq c (While b c),  s1)  # 
                       map (lift (While b c)) xs1) \<in> assum (p, R)"
    using a6 tl_of_assum_in_assum1 s1_collect_p 
          tl_of_assum_in_assum cptn_eq_cptn_mod_nest  by fast
  have cpn_c:"(\<Gamma>, ((c,  s1) # xs1)) \<in> (cpn n \<Gamma> c ( s1))"
    using a0 unfolding cpn_def by fastforce
  then have cp_c:"(\<Gamma>, ((c,  s1) # xs1)) \<in> (cp \<Gamma> c ( s1))"
    unfolding cp_def cpn_def using cptn_eq_cptn_mod_nest by auto
  moreover have cp_seq:"(\<Gamma>, (Seq c (While b c),  s1) # map (lift (While b c)) xs1) \<in> 
           (cpn n \<Gamma> (Seq c (While b c)) ( s1))"
    using cptn_seq unfolding cpn_def by fastforce
  then have cp_seq':"(\<Gamma>, (Seq c (While b c),  s1) # map (lift (While b c)) xs1) \<in> 
            (cp \<Gamma> (Seq c (While b c)) ( s1))"
    unfolding cp_def cpn_def using cptn_eq_cptn_mod_nest by auto
  ultimately have "(\<Gamma>, ((c,  s1) # xs1)) \<in> assum(p,R)"  
    using assum_map assum_seq seq_map  by fastforce
  then have "(\<Gamma>, ((c,  s1) # xs1)) \<in> assum((p \<inter> {c. fst c \<in> b}),R)"
    unfolding assum_def using s1_collect_p by fastforce
  then have c_comm:"(\<Gamma>, ((c,  s1) # xs1)) \<in> comm(G,(p,a)) F"  
    using a5 cpn_c unfolding com_validityn_def by fastforce
  then have False unfolding comm_def split_beta  final_glob_def using a1 by auto
  thus ?thesis by auto       
qed

lemma while5:
   "(n, \<Gamma>, (c,  s1) # xs1) \<in> cptn_mod_nest_call \<Longrightarrow>    
    fst (last ((c,  s1) # xs1)) = Fault f \<Longrightarrow>
    s1 \<in> {c. fst c \<in> b} \<Longrightarrow>
    snd (last ((c,  s1) # xs1)) =  sl \<Longrightarrow>
    (n,\<Gamma>, (Fault f, sl) # ys) \<in> cptn_mod_nest_call   \<Longrightarrow>
    \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c sat [p \<inter> {c. fst c \<in> b},R, G, p,a] \<Longrightarrow>    
    (\<Gamma>, (While b c,  s1) #
         (Seq c (While b c),  s1) #  
         (map (lift (While b c)) xs1 @
           (Fault f,  sl) # ys))
       \<in> assum (p, R)  \<Longrightarrow>        
     Sta p R \<Longrightarrow>
     Sta a R \<Longrightarrow> \<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G \<Longrightarrow> 
    (\<Gamma>, (While b c,  s1) #
         (Seq c (While b c),  s1) #          
         ((map (lift (While b c)) xs1 @
           (Fault f,  sl) # ys))) \<in> comm (G, p\<inter> ({c. fst c \<in> -b}), a) F
"
proof -
assume a0:"(n,\<Gamma>, (c,  s1) # xs1) \<in> cptn_mod_nest_call" and
       a1:"fst (last ((c,  s1) # xs1)) = Fault f" and
       a2:"s1 \<in> {c. fst c \<in> b}" and
       a3:"snd (last ((c,  s1) # xs1)) = sl" and
       a4:"(n,\<Gamma>, (Fault f,  sl) # ys) \<in> cptn_mod_nest_call" and
       a5:"\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c sat [p \<inter> {c. fst c \<in> b}, R, G, p,a]" and
       a6:"(\<Gamma>, (While b c,  s1) #
           (Seq c (While b c),  s1) #  
           (map (lift (While b c)) xs1 @
             (Fault f,  sl) # ys)) \<in> assum (p, R)" and      
       a7: "Sta p R" and
       a8: "Sta a R" and       
       a10:"\<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G"  
  let ?c = "(While b c,  s1) # (Seq c (While b c),  s1) # map (lift (While b c)) xs1 "  
  let ?c' ="(com.Fault f, sl) # ys"
  let ?c'' = "?c @ ?c'"
  have seq_map:"(Seq c (While b c),  s1) # map (lift (While b c)) xs1=
           map (lift (While b c)) ((c, s1)#xs1)"
  using a2 unfolding lift_def by fastforce
  have step:"\<Gamma>\<turnstile>\<^sub>c(While b c,toSeq( s1)) \<rightarrow> (Seq c (While b c),toSeq( s1))" 
    using a2 WhileTruec by fastforce
  have s1_normal:"s1\<in>p \<and> s1 \<in> {c. fst c \<in> b} " using a6 a2 unfolding assum_def by fastforce
  then have G_ref:"( s1,  s1)\<in>G" using a10 unfolding N_def by blast
  have s1_collect_p: " s1\<in>  (p \<inter>{c. fst c \<in> b})" using s1_normal by fastforce
  have "(n, \<Gamma>, map (lift (While b c)) ((c, s1)#xs1))\<in>cptn_mod_nest_call" 
    using a2  a0
    by (metis cptn_mod_nest_call.CptnModNestSeq1 seq_map) 
  then have cptn_seq:"(n,\<Gamma>,(Seq c (While b c),  s1) # map (lift (While b c)) xs1) \<in>cptn_mod_nest_call" 
    using seq_map by auto
  then have cptn:"(n,\<Gamma>, ?c) \<in> cptn_mod_nest_call"
    using a0 a2 cptn_mod_nest_call.CptnModNestWhile1
    by blast 
  also have "(\<Gamma>, ?c) \<in> assum (p, R) "
    using a6 sub_assum
    by (metis append_Cons) 
  ultimately have assum_seq:"(\<Gamma>,(Seq c (While b c),  s1)  # 
                       map (lift (While b c)) xs1) \<in> assum (p, R)"
    using a6 tl_of_assum_in_assum1 s1_collect_p 
          tl_of_assum_in_assum cptn_eq_cptn_mod_nest  by fast  
  have cpn_c:"(\<Gamma>, ((c,  s1) # xs1)) \<in> (cpn n \<Gamma> c ( s1))"
    using a0 unfolding cpn_def by fastforce
  then have cp_c:"(\<Gamma>, ((c,  s1) # xs1)) \<in> (cp \<Gamma> c ( s1))"
    unfolding cp_def cpn_def using cptn_eq_cptn_mod_nest by auto
  moreover have cp_seq:"(\<Gamma>, (Seq c (While b c),  s1) # map (lift (While b c)) xs1) \<in> 
           (cpn n \<Gamma> (Seq c (While b c)) ( s1))"
    using cptn_seq unfolding cpn_def by fastforce
  then have cp_seq':"(\<Gamma>, (Seq c (While b c),  s1) # map (lift (While b c)) xs1) \<in> 
            (cp \<Gamma> (Seq c (While b c)) ( s1))"
    unfolding cp_def cpn_def using cptn_eq_cptn_mod_nest by auto
  ultimately have "(\<Gamma>, ((c,  s1) # xs1)) \<in> assum(p,R)"  
    using assum_map assum_seq seq_map  by fastforce
  then have "(\<Gamma>, ((c,  s1) # xs1)) \<in> assum((p \<inter> {c. fst c \<in> b}),R)"
    unfolding assum_def using s1_collect_p by fastforce
  then have c_comm:"(\<Gamma>, ((c,  s1) # xs1)) \<in> comm(G,(p,a)) F"  
    using a5 cpn_c unfolding com_validityn_def by fastforce
  then have "(\<Gamma>, (Seq c (While b c),  s1) # map (lift (While b c)) xs1) \<in> comm(G,(p,a)) F"
    using cp_seq' cp_c comm_map seq_map by fastforce
  then have comm_while:"(\<Gamma>, ?c) \<in> comm(G,(p,a)) F"
    using G_ref ctran_in_comm by blast   
  then have "\<forall>i. Suc i < length ?c \<longrightarrow> 
                     \<Gamma>\<turnstile>\<^sub>c (fst (?c ! i), toSeq (snd (?c ! i))) \<rightarrow>
                         (fst (?c ! Suc i), toSeq (snd (?c ! Suc i))) \<longrightarrow>
                    (snd (?c !i), snd(?c !(Suc i))) \<in> G"
    using comm_dest by fastforce
  moreover have "\<forall>i. Suc i < length ?c' \<longrightarrow> \<not> \<Gamma>\<turnstile>\<^sub>c (fst (?c' ! i), toSeq (snd (?c' ! i))) \<rightarrow>
                                    (fst (?c' ! Suc i), toSeq (snd (?c' ! Suc i)))"
    by (metis (no_types) a4 cptn_if_cptn_mod cptn_mod_nest_cptn_mod 
              fst_conv nth_Cons_0 only_one_component_tran_0)
  then have "\<forall>i. Suc i < length ?c' \<longrightarrow> 
                     \<Gamma>\<turnstile>\<^sub>c (fst (?c' ! i), toSeq (snd (?c' ! i))) \<rightarrow>
                         (fst (?c' ! Suc i), toSeq (snd (?c' ! Suc i))) \<longrightarrow>
                    (snd (?c' !i), snd(?c' !(Suc i))) \<in> G"
    by auto
  moreover have "(snd (last ?c), snd (?c' ! 0))\<in>G" using a10 a1 a3 unfolding N_def
    by (smt a0 cptn_all_len_eq_0 cptn_if_cptn_mod cptn_mod_nest_cptn_mod last.simps last_length 
            last_map length_Cons length_map 
            lessI list.simps(3) list.size(3) mem_Collect_eq nth_Cons_0 s1_normal snd_conv snd_lift)   
  ultimately have 
   "\<forall>i. Suc i < length ?c'' \<longrightarrow> 
          \<Gamma>\<turnstile>\<^sub>c (fst (?c'' ! i), toSeq (snd (?c'' ! i))) \<rightarrow>
              (fst (?c'' ! Suc i), toSeq (snd (?c'' ! Suc i))) \<longrightarrow> 
        (snd (?c'' !i), snd(?c'' !(Suc i))) \<in> G"
    using step_guard_concat by blast  
  moreover have " (final_glob (last ?c'')  \<longrightarrow>   
                 fst (last ?c'') \<notin> Fault ` F  \<longrightarrow>                 
                    ((fst (last ?c'') = Skip \<and> snd (last ?c'') \<in> p\<inter> ({c. fst c \<in> -b}))) \<or>
                    (fst (last ?c'') = Throw \<and> snd (last ?c'') \<in> a))"
    apply (cases "f\<in>F")    
     apply (metis (no_types, lifting) LanguageCon.com.distinct(171)
           LanguageCon.com.distinct(19) a1 a3 a4 c_comm 
           comm_dest2 cptn_if_cptn_mod cptn_mod_nest_cptn_mod 
           final_glob_def last_appendR last_not_F length_Cons list.simps(3) nth_Cons_0 
           prod.collapse zero_less_Suc)     
    by (metis (no_types, lifting)  a1 a3 a4 LanguageCon.com.distinct(171) LanguageCon.com.distinct(19)
            c_comm comm_dest2 cptn_if_cptn_mod cptn_mod_nest_cptn_mod final_glob_def last_appendR 
             last_not_F length_Cons list.simps(3) nth_Cons_0 prod.collapse zero_less_Suc)    
  ultimately show ?thesis
    by (simp add: commI) 
qed


inductive_cases stepc_elim_cases_while_throw [cases set]:
 "\<Gamma>\<turnstile>\<^sub>c(While b c, s) \<rightarrow> (Throw, t)"

inductive_cases stepc_elim_cases_while_Stuck [cases set]:
 "\<Gamma>\<turnstile>\<^sub>c(While b c, s) \<rightarrow> (Stuck, t)"

inductive_cases stepc_elim_cases_while_Fault [cases set]:
 "\<Gamma>\<turnstile>\<^sub>c(While b c, s) \<rightarrow> (Fault f, t)"


lemma WhileSound_aux:
 "\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> {c. fst c \<in> b}, R, G, p,a] \<Longrightarrow>
  Sta p R \<Longrightarrow>
  Sta  (p \<inter> ({c. fst c \<in> -b})) R \<Longrightarrow> 
  Sta a R \<Longrightarrow>    
  (n, \<Gamma>,x)\<in> cptn_mod_nest_call \<Longrightarrow> 
  \<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G \<Longrightarrow>
  \<forall>s xs. x = ((While b c1),s)#xs \<longrightarrow> 
     (\<Gamma>,x)\<in>assum(p,R) \<longrightarrow> 
     (\<Gamma>,x) \<in> comm (G,(( p \<inter> ({c. fst c \<in> -b})),a)) F"
proof -
  assume a0: "\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> {c. fst c \<in> b}, R, G, p,a] " and
         a1: "Sta p R" and
         a2: "Sta  (p \<inter> ({c. fst c \<in> -b})) R" and
         a3: "Sta a R" and
         a4: "(n,\<Gamma>,x)\<in> cptn_mod_nest_call" and
         a5: "\<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G" 
   {fix xs s 
   assume while_xs:"x=((While b c1),s)#xs" and
          x_assum:"(\<Gamma>,x)\<in>assum(p,R)"
   have "(\<Gamma>,x) \<in> comm (G,(( p \<inter> {c. fst c \<in> -b}),a)) F"
   using a4 a0  while_xs x_assum
   proof (induct arbitrary: xs s c1 rule:cptn_mod_nest_call.induct)
     case (CptnModNestOne  \<Gamma> C s1) thus ?case 
       using CptnModOne unfolding comm_def final_glob_def
       by auto
   next
     case (CptnModNestEnv  \<Gamma> C s1 t1 n xsa) 
     then have c_while:"C = While b c1" by fastforce
     have "(\<Gamma>, (C, t1) # xsa) \<in> assum (p, R) \<longrightarrow>
                (\<Gamma>, (C, t1) # xsa) \<in> comm (G, p \<inter> {c. fst c \<in> -b}, a) F"  
     using CptnModNestEnv by fastforce  
     moreover have"(n,\<Gamma>,(C, s1)#(C, t1) # xsa) \<in> cptn_mod_nest_call"
       using CptnModNestEnv(1,2) CptnModNestEnv.hyps(1) CptnModNestEnv.hyps(2)
       using cptn_mod_nest_call.CptnModNestEnv by blast
     then have  cptn_mod:"(\<Gamma>,(C, s1)#(C, t1) # xsa) \<in> cptn"    
       using cptn_eq_cptn_mod_nest by blast  
     then have "(\<Gamma>, (C, t1) # xsa) \<in> assum (p, R)"   
       using tl_of_assum_in_assum CptnModNestEnv(6) a1 a2 a3 a4 a5
       by blast
     ultimately have "(\<Gamma>, (C, t1) # xsa) \<in> comm (G, p \<inter> {c. fst c \<in> -b}, a) F"
       by auto
     also have " \<not> (\<Gamma>\<turnstile>\<^sub>c((C,toSeq s1))  \<rightarrow> ((C,toSeq t1)))"
       by (simp add: mod_env_not_component)      
     ultimately show ?case 
       using cptn_mod etran_in_comm by blast
   next 
     case (CptnModNestSkip \<Gamma> C s1 t1 n xsa) 
     then have "C=While b c1" by auto
     also have "(n,\<Gamma>, (LanguageCon.com.Skip, t1) # xsa) \<in> cptn_mod_nest_call"
       using cptn_eq_cptn_mod_set CptnModNestSkip(4)
       using CptnModNestSkip.hyps(5) by blast
     thus ?case using WhileNone CptnModNestSkip a1 a2 a3 a4 a5  by blast
   next
     case (CptnModNestThrow  \<Gamma> C s1 t1 n xsa) 
     then have "C = While b c1" by auto 
       thus ?case using stepc_elim_cases_while_throw CptnModNestThrow(1) 
         by fastforce
   next
     case (CptnModNestStuck  \<Gamma> C s1 t1 n xsa) 
     then have "C = While b c1" by auto 
       thus ?case using stepc_elim_cases_while_Stuck CptnModNestStuck(1) 
         by fastforce
   next
     case (CptnModNestFault  \<Gamma> C s1 t1 n xsa) 
     then have "C = While b c1" by auto 
       thus ?case using stepc_elim_cases_while_Fault CptnModNestFault(1) 
         by fastforce
   next 
     case (CptnModNestWhile1  n \<Gamma> c s1 xs1 b1 xsa zs) 
     then have "b=b1 \<and> c=c1 \<and> s= s1" by auto      
     thus ?case
     using a4 a5 CptnModNestWhile1 while1[of n \<Gamma>] by blast
   next 
     case (CptnModNestWhile2 n \<Gamma> c s1 xs1 b1 xsa ys zs)
     then have a00: "(n,\<Gamma>, (While b c,  s1) #
         (Seq c (While b c),  s1) # xsa)\<in>cptn_mod_nest_call" 
       using cptn_mod_nest_call.CptnModNestWhile2 by fast   
     then have eqs:"b=b1 \<and> c=c1 \<and> s= s1"using CptnModNestWhile2 by auto
     thus ?case using  a00 a4 a5 CptnModNestWhile2 while2[of n \<Gamma> b c s1 xsa xs1 ys F p R G a] 
       by blast        
   next
     case (CptnModNestWhile3 n \<Gamma> c s1 xs1 t f b1 sl ys zs)  
     then have eqs:"b=b1 \<and> c=c1 \<and> s= s1" by auto 
     then have "(\<Gamma>, (While b c,  s1) #
         (Seq c (While b c),  s1) #          
         ((map (lift (While b c)) xs1 @
           (t,  sl) # ys))) \<in> comm (G, p\<inter>{c. fst c \<in> -b}, a) F"        
     proof(cases t)      
       case Stuck
       then show ?thesis using a1 a3 a4 a5 CptnModNestWhile3 while4[of n \<Gamma> c s1 xs1 b sl ys F p R G a] 
         by fastforce    
     next
       case (Fault x11)
       then show ?thesis  
         using a1 a3 a4 a5 CptnModNestWhile3 while5[of n \<Gamma> c s1 xs1 x11 b sl ys F p R G a] 
         by fastforce
     next
       case Throw
       then show ?thesis 
         using a1 a3 a4 a5 CptnModNestWhile3 while3[of n \<Gamma> c s1 xs1 b sl ys F p R G a] 
         by fastforce
     qed(insert CptnModNestWhile3(4), auto)
     thus ?case using eqs CptnModNestWhile3 by auto
   qed (auto)
  }
  then show ?thesis by auto    
qed


lemma While_sound: 
      "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> {c. fst c \<in> b}, R, G, p,a] \<Longrightarrow>
       (\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> {c. fst c \<in> b}, R, G, p,a]) \<Longrightarrow>       
       Sta p R \<Longrightarrow>     
       Sta (p \<inter> {c. fst c \<in> -b}) R \<Longrightarrow> Sta a R \<Longrightarrow> \<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G  \<Longrightarrow>
       \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> (While b c1) sat [p, R, G, p \<inter> {c. fst c \<in> -b},a]"
proof -  
  assume
    a0:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p \<inter> {c. fst c \<in> b}, R, G, p,a]" and
    a1:"\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n \<^bsub>/F\<^esub> c1 sat [p \<inter> {c. fst c \<in> b}, R, G, p,a]" and    
    a2: "Sta p R" and
    a3: "Sta (p \<inter> {c. fst c \<in> -b}) R" and
    a4: "Sta a R" and
    a5: "\<forall>s. length (snd s) \<in> N p  \<longrightarrow> ( s,  s) \<in> G" 
  { 
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"  
    then have a1:"(\<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> c1 sat [p \<inter> {c. fst c \<in> b}, R, G, p,a])" 
      using a1 com_cvalidityn_def by fastforce
    have "cpn n \<Gamma> (While b c1)  s \<inter> assum(p, R) \<subseteq> comm(G, (p \<inter> {c. fst c \<in> -b},a)) F"
    proof-
      {fix c     
        assume a10:"c \<in> cpn n \<Gamma> (While b c1) s" and a11:"c \<in> assum(p, R)"
        then have a10': "c \<in> cp  \<Gamma> (While b c1) s"
          unfolding cp_def cpn_def using cptn_eq_cptn_mod_set cptn_mod_nest_cptn_mod by fastforce
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have cp:"l!0=((While b c1),s) \<and> (\<Gamma>,l) \<in> cptn \<and> \<Gamma>=\<Gamma>1" using a10' cp_def c_prod by fastforce      
      have \<Gamma>1:"(\<Gamma>, l) = c" using c_prod cp by blast
      obtain xs where "l=((While b c1),s)#xs" using cp
      proof -
        assume a1: "\<And>xs. l = (LanguageCon.com.While b c1, s) # xs \<Longrightarrow> thesis"
        have "[] \<noteq> l"
          using cp cptn.simps
          by blast
        then show ?thesis
          using a1 by (metis (full_types) SmallStepCon.nth_tl cp)
      qed 
      moreover have "(n,\<Gamma>,l)\<in>cptn_mod_nest_call" using a10
        using \<Gamma>1 cpn_def by fastforce  
      ultimately have "c \<in> comm(G, (p \<inter> {c. fst c \<in> -b},a)) F"
      using a1 a2 a3 a4   WhileSound_aux a11 \<Gamma>1 a5 
        by blast
      } thus ?thesis by auto qed
  }
  thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def)  
qed


lemma Conseq_sound:
  "(\<forall>s\<in> p.
       \<exists>p' R' G' q' a' I' \<Theta>'.
          s \<in> p' \<and>
          R \<subseteq> R' \<and>            
          G' \<subseteq> G \<and>             
          q' \<subseteq> q \<and>
          a' \<subseteq> a \<and> \<Theta>' \<subseteq> \<Theta> \<and>
          \<Gamma>,\<Theta>' \<turnstile>\<^bsub>/F\<^esub> P sat [p',R', G', q',a'] \<and> 
          (\<forall>n. \<Gamma>,\<Theta>' \<Turnstile>n\<^bsub>/F\<^esub> P sat [p', R', G', q',a'])) \<Longrightarrow>
  \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> P sat [p,R, G, q,a]" 
proof -
  assume 
  a0: "(\<forall>s\<in> p.
       \<exists>p' R' G' q' a' I' \<Theta>'.
          s \<in> p' \<and>
          R \<subseteq> R' \<and>            
          G' \<subseteq> G \<and>             
          q' \<subseteq> q \<and>
          a' \<subseteq> a \<and> \<Theta>' \<subseteq> \<Theta> \<and>
          \<Gamma>,\<Theta>' \<turnstile>\<^bsub>/F\<^esub> P sat [p',R', G', q',a'] \<and> 
          (\<forall>n. \<Gamma>,\<Theta>' \<Turnstile>n\<^bsub>/F\<^esub> P sat [p', R', G', q',a']))"
  {
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"
    have "cpn n \<Gamma> P  s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
    proof -
    {
      fix c
      assume a10:"c \<in> cpn n \<Gamma> P s" and a11:"c \<in> assum(p, R)"
      then have a10':"c\<in>cp \<Gamma> P s" unfolding cp_def cpn_def cptn_eq_cptn_mod_nest by auto
      obtain \<Gamma>1 l where c_prod:"c=(\<Gamma>1,l)" by fastforce
      have cp:"l!0=(P,s) \<and> (n,\<Gamma>,l) \<in> cptn_mod_nest_call \<and> \<Gamma>=\<Gamma>1" using a10 cpn_def c_prod by fastforce
      have \<Gamma>1:"(\<Gamma>, l) = c" using c_prod cp by blast 
      obtain xs where "l=(P,s)#xs" using cp
      proof -
        assume a1: "\<And>xs. l = (P, s) # xs \<Longrightarrow> thesis"
        have "[] \<noteq> l"
          using cp cptn.simps
          using CptnEmpty by force
        then show ?thesis
          using a1 by (metis (full_types) SmallStepCon.nth_tl cp)
      qed      
      then have "s \<in> p" using a10 a11 unfolding assum_def cpn_def by fastforce
      then have ns:"s\<in>p" by auto
      then have
      "\<forall>s. s \<in> p \<longrightarrow> (\<exists>p' R' G' q' a' \<Theta>'. (s\<in>p') \<and>
        R \<subseteq> R' \<and>            
        G' \<subseteq> G \<and>             
        q' \<subseteq> q \<and>
        a' \<subseteq> a \<and> \<Theta>' \<subseteq> \<Theta> \<and>
        (\<Gamma>,\<Theta>' \<turnstile>\<^bsub>/F\<^esub> P sat [p',R', G', q',a']) \<and> 
        (\<forall>n. \<Gamma>,\<Theta>' \<Turnstile>n\<^bsub>/F\<^esub> P sat [p', R', G', q',a']))" using a0 by auto
      then have 
       "s \<in> p \<longrightarrow> (\<exists>p' R' G' q' a' \<Theta>'. (s \<in> p' ) \<and>
        R \<subseteq> R' \<and>            
        G' \<subseteq> G \<and>             
        q' \<subseteq> q \<and>
        a' \<subseteq> a \<and> \<Theta>' \<subseteq> \<Theta> \<and>
        (\<Gamma>,\<Theta>' \<turnstile>\<^bsub>/F\<^esub> P sat [p',R', G', q',a']) \<and> 
        (\<forall>n. \<Gamma>,\<Theta>' \<Turnstile>n\<^bsub>/F\<^esub> P sat [p', R', G', q',a']))" apply (rule allE) by auto     
     then obtain p' R' G' q' a' \<Theta>'   where
     rels:
       "s \<in> p' \<and>
        R \<subseteq> R' \<and>            
        G' \<subseteq> G \<and>             
        q' \<subseteq> q \<and>
        a' \<subseteq> a \<and> \<Theta>' \<subseteq> \<Theta> \<and>       
        (\<forall>n. \<Gamma>,\<Theta>' \<Turnstile>n\<^bsub>/F\<^esub> P sat [p', R', G', q',a'])" using ns by auto
      then have "s \<in> p'"  by fastforce
      then have "(\<Gamma>,l) \<in> assum(p', R')"
        using a11 rels cp a11 c_prod assum_R_R'[of \<Gamma> l p R p' R'] 
        by fastforce
      then have "(\<Gamma>,l) \<in> comm(G',(q',a')) F" 
        using rels all_call a10 c_prod cp unfolding com_cvalidityn_def com_validityn_def 
        by blast
      then have "(\<Gamma>,l) \<in> comm(G, (q,a)) F" 
        using c_prod cp comm_conseq[of \<Gamma> l G' q' a' F G q a] rels by fastforce
      then have "c \<in> comm(G, (q,a)) F" using c_prod cp by fastforce
    }                 
    thus ?thesis unfolding comm_def by force qed      
  } thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def)  
qed   

lemma Conj_post_sound:
  "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P sat [p,R, G, q,a] \<and> 
   (\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> P sat [p, R, G, q,a]) \<Longrightarrow> 
   \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P sat [p,R, G, q',a'] \<and> 
   (\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n \<^bsub>/F\<^esub> P sat [p, R, G, q',a']) \<Longrightarrow>
  \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> P sat [p,R, G, q \<inter> q' ,a \<inter> a']" 
proof -
assume a0: "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P sat [p,R, G, q,a] \<and> 
   (\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> P sat [p, R, G, q,a])" and
       a1: " \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P sat [p,R, G, q',a'] \<and> 
   (\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n \<^bsub>/F\<^esub> P sat [p, R, G, q',a'])"
{
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"
    with a0 have a0:"cpn n \<Gamma> P  s \<inter> assum(p, R) \<subseteq> comm(G, (q,a)) F"
      unfolding com_cvalidityn_def com_validityn_def by blast
    with a1 all_call have a1:"cpn n \<Gamma> P  s \<inter> assum(p, R) \<subseteq> comm(G, (q',a')) F"
      unfolding com_cvalidityn_def com_validityn_def by blast
    have "cpn n \<Gamma> P  s \<inter> assum(p, R) \<subseteq> comm(G, (q\<inter>q',a\<inter>a')) F"
    proof -
    {
      fix c
      assume a10:"c \<in> cpn n \<Gamma> P s" and a11:"c \<in> assum(p, R)"
      then have "c \<in> comm(G,(q,a)) F \<and> c \<in> comm(G,(q',a')) F"
        using a0 a1 by auto
      then have  "c\<in>comm(G, (q\<inter>q',a\<inter>a')) F"
        unfolding comm_def by force
    }               
    thus ?thesis unfolding comm_def by force qed      
  } thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def)  
qed  
  
lemma x91:"sa\<noteq>{} \<Longrightarrow> c\<in>comm(G, (\<Inter>i\<in>sa. q i,a)) F  = (\<forall>i\<in>sa. c\<in>comm(G, q i,a) F)"    
  unfolding comm_def by (auto simp add: Ball_def) 

    
lemma conj_inter_sound:
"sa \<noteq> {} \<Longrightarrow> 
 \<forall>i\<in>sa. \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q i,a] \<and> (\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> P sat [p,R, G, q i,a]) \<Longrightarrow> 
 \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> P sat [p,R, G, \<Inter>i\<in>sa. q i,a]"
proof -
  assume a0':"sa\<noteq>{}" and 
         a0: "\<forall>i\<in>sa. \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q i,a] \<and> 
              (\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n\<^bsub>/F\<^esub> P sat [p,R, G, q i,a])" 
{
    fix s
    assume all_call:"\<forall>(c,p,R,G,q,a)\<in> \<Theta>. \<Gamma> \<Turnstile>n\<^bsub>/F\<^esub> (Call c) sat [p, R, G, q,a]"
    with a0 have a0:"\<forall>i\<in>sa. cpn n \<Gamma> P  s \<inter> assum(p, R) \<subseteq> comm(G, (q i,a)) F"
      unfolding com_cvalidityn_def com_validityn_def by fast    
    have "cpn n \<Gamma> P  s \<inter> assum(p, R) \<subseteq> comm(G, (\<Inter>i\<in>sa. q i,a)) F"
    proof -
    {
      fix c
      assume a10:"c \<in> cpn n \<Gamma> P s" and a11:"c \<in> assum(p, R)"        
      then have  "(\<forall>i\<in>sa. c\<in>comm(G, q i,a) F)"        
        using a0 by fastforce
      then have "c\<in>comm(G, (\<Inter>i\<in>sa. q i,a)) F" using x91[OF a0'] by blast
    }               
    thus ?thesis unfolding comm_def by force qed      
  } thus ?thesis by (simp add: com_validityn_def[of \<Gamma>] com_cvalidityn_def)  
qed     

lemma empty_p_valid:"\<Gamma>,\<Theta> \<Turnstile>n \<^bsub>/F\<^esub> c sat [{}, R, G, q,a]"
  unfolding com_cvalidityn_def com_validityn_def assum_def  by auto

lemma localRG_sound: "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p, R, G, q,a] \<Longrightarrow> (\<And>n. \<Gamma>,\<Theta> \<Turnstile>n \<^bsub>/F\<^esub> c sat [p, R, G, q,a])"
proof (induct rule:lrghoare.induct)
  case Skip 
    thus ?case  by (simp add: Skip_sound)
next
  case Spec
    thus ?case  by (simp add: Spec_sound)
next
  case Basic
    thus ?case by (simp add: Basic_sound)
next
  case Await
    thus ?case by (simp add: Await_sound)
next
  case Throw thus ?case by (simp add: Throw_sound)
next 
  case If thus ?case using If_sound by (simp add: If_sound)
next
  case Asm thus ?case by (simp add: Asm_sound)
next 
  case CallRec thus ?case  by (simp add: CallRec_sound)
next
  case Call thus ?case using Call_sound  by (simp add: Call_sound)
next
  case Seq thus ?case by (simp add: Seq_sound)
next
  case Catch thus ?case by (simp add: Catch_sound)
next
  case DynCom thus ?case by (simp add: DynCom_sound)
next
  case Guard thus ?case by (simp add: Guard_sound)
next
  case Guarantee thus ?case by (simp add: Guarantee_sound)
next
  case (While p R b a G \<Gamma> \<Theta> F c)
  thus ?case using While_sound[of \<Gamma>] by simp
next
  case (Conseq p R G q a \<Gamma> \<Theta> F P) thus ?case 
    using Conseq_sound by simp
next 
  case (Conj_post \<Gamma> \<Theta> F P p' R' G' q a q' a') thus ?case
    using Conj_post_sound[of \<Gamma> \<Theta>] by simp
next
  case (Conj_Inter sa \<Gamma> \<Theta> F P p' R' G' q a ) 
  thus ?case using conj_inter_sound[of sa \<Gamma> \<Theta>] by simp 
next 
  case (Stuck p) thus ?case using empty_p_valid by auto
next 
  case (Fault) thus ?case using empty_p_valid by auto
qed   


definition ParallelCom :: "('g,'l,'p,'f,'e) p_rgformula list \<Rightarrow> ('g,'l,'p,'f,'e) par_com"
where
"ParallelCom Ps \<equiv> map fst Ps"

lemma ParallelCom_Com:"i<length xs \<Longrightarrow> (ParallelCom xs)!i = Par_Com (xs!i)"
  unfolding ParallelCom_def Par_Com_def by fastforce

lemma step_e_step_c_eq:"\<lbrakk> 
  (\<Gamma>,l) \<propto> clist;
  Suc m < length l;
  i < length clist; 
  (fst (clist!i))\<turnstile>\<^sub>c(fst ((snd (clist!i))!m),  toSeqState i (snd((snd (clist!i))!m))) \<rightarrow>\<^sub>e  
                   (fst ((snd (clist!i))!(Suc m)), toSeqState  i (snd((snd (clist!i))!(Suc m))));         
  (fst (clist!i))\<turnstile>\<^sub>c(fst ((snd (clist!i))!m),  toSeq (toSeqState i (snd((snd (clist!i))!m)))) \<rightarrow>  
                   (fst ((snd (clist!i))!(Suc m)), toSeq (toSeqState  i (snd((snd (clist!i))!(Suc m)))));
  (\<forall>l<length clist. 
     l\<noteq>i \<longrightarrow>  (fst (clist!l))\<turnstile>\<^sub>c(fst ((snd (clist!l))!m),  toSeqState l (snd((snd (clist!l))!m))) \<rightarrow>\<^sub>e  
                   (fst ((snd (clist!l))!(Suc m)), toSeqState  l (snd((snd (clist!l))!(Suc m)))))
  \<rbrakk> \<Longrightarrow> 
  l!m = l!(Suc m)"
  using etran_ctran_False by blast


lemma takecptni_is_cptni [rule_format, elim!]:
  "\<forall>j. (i',\<Gamma>,c) \<in> cptni \<longrightarrow> (i',\<Gamma>, take (Suc j) c) \<in> cptni"
apply(induct "c")
 apply(force elim: cptn.cases)
apply clarify
apply(case_tac j)
 apply simp
  apply (simp add: cptni.CptnOnei)
apply simp
apply(force intro:cptni.intros elim:cptni.cases)
done



lemma dropcptni_is_cptni [rule_format,elim!]:
  "\<forall>j<length c. (i',\<Gamma>,c) \<in> cptni \<longrightarrow> (i',\<Gamma>, drop j c) \<in> cptni"
apply(induct "c")
 apply(force elim: cptni.cases)
apply clarify
apply(case_tac j,simp+)
apply(erule cptni.cases)
  apply simp
 apply force
  done

lemma  wf_local_vars:"(\<Gamma>,l) \<propto> clist \<Longrightarrow> 
        i<length clist \<Longrightarrow> 
        j<length (snd (clist!i)) \<Longrightarrow> (\<Gamma>,l) \<in> par_cp  \<Gamma> (ParallelCom xs) s \<Longrightarrow>
        i<length (snd (snd(snd (clist!i)!j)))"
proof-
  assume a0:"(\<Gamma>,l) \<propto> clist" and
        a1:"i<length clist" and
        a2:"j<length (snd (clist!i))" and 
        a3:"(\<Gamma>,l) \<in> par_cp  \<Gamma> (ParallelCom xs) s"
  then have len0:" length (fst (l!0))\<le> length (snd (snd(l!0)))"
    using a0 unfolding conjoin_def same_length_state_program_def same_length_def
    by auto  
  {
    have j_len:"j<length l" using a2 a0  conjoin_same_length unfolding conjoin_def same_length_def
      by (simp add: a1)
    moreover have j_v:"snd (l!j) = snd(snd (clist!i)!j) " using  a0 unfolding par_cp_def
      using a1 conjoin_def j_len same_state_def calculation by fastforce
    ultimately have "i<length (snd (snd(snd (clist!i)!j)))" using len0 a0 a3 all_same_length_state_program[OF _ _ j_len ] 
      unfolding par_cp_def conjoin_def
      using a0 a1 conjoin_same_length
      by fastforce 
  } thus ?thesis by auto  
qed

lemma cpi_par_state_image_cp:
  assumes a0:"(\<Gamma>1,l) \<in> cpi i \<Gamma> C s" and 
          a1:"i< length (snd s)"
      shows "(\<Gamma>1,l) \<in>({(s, p). fst p = fst s \<and>  (snd s, snd p)\<in>par_state_list_rel i} `` 
                (cp \<Gamma> C ((toSeqState i s))))"
  using a0  unfolding cp_def cpi_def Image_def
proof(auto)
  assume a01:"l!0=(C,s)" and
         a02:"(i, \<Gamma>, l) \<in> cptni"    
  then obtain g ls where  s:"s = (g, ls)" by fastforce
  then have  "(\<Gamma>, toSeqCptn i l) \<in> cptn"
    using cptni_cptn[OF a02] a1 s a01 by auto
  moreover have "length (toSeqCptn i l)>0" 
     using cptn.cases calculation  unfolding toSeqCptn_def by blast
  then have  " toSeqCptn i l  ! 0 = (C, toSeqState i s)"
     using a01 unfolding toSeqCptn_def  by auto
   moreover have  "(toSeqCptn i l , l) \<in> par_state_list_rel i"
     using toSeqCptn_in_rel a1 s a02  a01 length_locs_less_i
     by (metis neq0_conv not_less0 snd_conv)
   ultimately show "\<exists>b. b ! 0 = (C, toSeqState i s) \<and> (\<Gamma>, b) \<in> cptn \<and> (b, l) \<in> par_state_list_rel i"
     by auto    
qed


lemma assum_cpi_in_rel_image:
  assumes 
  a0:"(\<Gamma>, l) \<in> assum_p i (P, R)" and
  a1:"(\<Gamma>, l) \<in> cpi i \<Gamma> C s" and
  a2:"i< length (snd s)"
shows "(\<Gamma>, l)\<in> ({(s, p). fst p = fst s \<and>  (snd s, snd p)\<in>par_state_list_rel i} `` ((cp \<Gamma> C (toSeqState i s)) \<inter> 
                  assum (Seq_pred i P, Seq_rel i R)))"
proof-
  have  "cpi i \<Gamma> C s \<subseteq> ({(s, p). fst p = fst s \<and>  (snd s, snd p)\<in>par_state_list_rel i} `` 
         (cp \<Gamma> C ((toSeqState i s))))"    
  proof-
    {fix l1 \<Gamma>1
      assume a01:"(\<Gamma>1,l1)\<in>cpi i \<Gamma> C s"
      have "(\<Gamma>1,l1)\<in> {(s, p). fst p = fst s \<and>  (snd s, snd p)\<in>par_state_list_rel i} `` 
         (cp \<Gamma> C ((toSeqState i s)))"
        using cpi_par_state_image_cp[OF a01 a2] by auto
    } thus ?thesis by auto
  qed        
  then have "(\<Gamma>, l) \<in> ({(s, p). fst p = fst s \<and>  (snd s, snd p)\<in>par_state_list_rel i} `` 
         (cp \<Gamma> C ((toSeqState i s))))" using a1 by fastforce
  moreover have  "assum_p i (P, R) = {(s, p). fst p = fst s \<and>  (snd s, snd p)\<in>par_state_list_rel i} `` 
                                    assum (Seq_pred i P, Seq_rel i R)"
    unfolding assum_p_def Let_def split_beta  by force
  then have "(\<Gamma>, l) \<in>{(s, p). fst p = fst s \<and>  (snd s, snd p)\<in>par_state_list_rel i} `` 
                                    assum (Seq_pred i P, Seq_rel i R)" using a0 by fastforce
  ultimately show ?thesis unfolding Image_def apply auto
    by (metis IntI fst_conv par_state_list_rel_eq snd_conv)
qed

lemma assum_p_cpi_in_com_p:
  assumes a0: "(\<Gamma>, l) \<in> assum_p i (P, R)" and
    a1:"(\<Gamma>, l) \<in> cpi i \<Gamma> C s" and 
    a1':"i< length (snd s)" and
    a2:"\<forall>(c, p, R, G, q, a)\<in>\<Theta>.
          Pred_wf i p \<and> Rel_wf i R \<and> Rel_wf i G \<and> Pred_wf i q \<and> Pred_wf i a \<longrightarrow> \<Gamma> \<Turnstile>\<^bsub>/F\<^esub>
          LanguageCon.com.Call c sat i [p,R, G, q,a]" and
    a3:"\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> C sat i [P,R, G, Q,A]" 
shows " (\<Gamma>, l) \<in> comm_p i (G, Q, A) F"
proof-
  have "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> C sat i [P,R, G, Q,A]"
    using a2 a3 unfolding comp_cvalidity_def by auto
  moreover have "(\<Gamma>, l)\<in> ({(s, p). fst p = fst s \<and>  (snd s, snd p)\<in>par_state_list_rel i} `` 
                   ((cp \<Gamma> C (toSeqState i s)) \<inter> 
                  assum (Seq_pred i P, Seq_rel i R)))"
    using assum_cpi_in_rel_image[OF a0 a1 a1'] by fastforce
  ultimately show ?thesis unfolding comp_validity_def by fastforce
qed



lemma cptni_wf:
  assumes a0:"(i,\<Gamma>,cpt)\<in>cptni" and
   a1:"snd (cpt ! 0) \<in>  P" and
   a2:"Pred_wf i P" 
  shows "\<forall>j<length cpt. i<length (snd (snd(cpt!j)))"
proof-
  have "snd(cpt!0)  \<in> P"
    using a1 by auto
  then have "i<length (snd (snd(cpt!0)))" 
    using a2 unfolding Pred_wf_def by auto
  then show ?thesis using a0
    by (metis length_greater_0_conv length_locs_less_i list.size(3) not_less0 prod.exhaust_sel)
qed


lemma two': 
  "\<lbrakk> \<forall>i<length xs. R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Par_Guar (xs ! j)))
       \<subseteq> (Par_Rely (xs ! i));
   p \<subseteq> (\<Inter>i<length xs. (Par_Pre (xs ! i)));
   \<forall>i<length xs.
    \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  Par_Com (xs ! i) sat i [Par_Pre (xs!i), Par_Rely (xs ! i), 
                                 Par_Guar (xs ! i), Par_Post (xs ! i),Par_Abr (xs ! i)];
   length xs=length clist; (\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s; (\<Gamma>,l)\<in>par_assum (p, R) ;
  \<forall>i<length clist. clist!i\<in>cpi  i \<Gamma> (Par_Com(xs!i)) s; (\<Gamma>,l) \<propto> clist;
  (\<forall>i<length xs.\<forall>(c,p,R,G,q,a)\<in> \<Theta>.  Pred_wf i p \<and> Rel_wf i R \<and>  Rel_wf i G \<and> Pred_wf i q \<and>  Pred_wf i a \<longrightarrow> 
    \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat i [p, R, G, q,a]); \<forall>i<length xs. Rel_wf i (Par_Guar(xs!i));  
   \<forall>i<length xs. Pred_wf i p\<rbrakk>
  \<Longrightarrow> \<forall>i j. i<length clist \<and> Suc j<length l \<longrightarrow> 
      \<Gamma>\<turnstile>\<^sub>c(fst ((snd (clist!i))!j),  toSeqState i (snd((snd (clist!i))!j))) \<rightarrow>\<^sub>e  
         (fst ((snd (clist!i))!(Suc j)), toSeqState  i (snd((snd (clist!i))!(Suc j)))) \<longrightarrow> 
      (snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in> Par_Rely(xs!i)"
proof -
  assume a0:"\<forall>i<length xs. R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Par_Guar (xs ! j)))
       \<subseteq> (Par_Rely (xs ! i))" and
         a1:" p \<subseteq> (\<Inter>i<length xs. (Par_Pre (xs ! i)))" and
         a2:"\<forall>i<length xs. \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  Par_Com (xs ! i) sat i [Par_Pre (xs!i), Par_Rely (xs ! i), 
                                 Par_Guar (xs ! i), Par_Post (xs ! i),Par_Abr (xs ! i)]" and
         a3: "length xs=length clist" and
         a4: "(\<Gamma>,l) \<in> par_cp  \<Gamma> (ParallelCom xs) s" and
         a5: "(\<Gamma>,l)\<in>par_assum (p, R)" and
         a6: " \<forall>i<length clist. clist!i\<in>cpi  i \<Gamma> (Par_Com(xs!i)) s" and
         a7: "(\<Gamma>,l) \<propto> clist" and
         a8: "\<forall>i<length xs.(\<forall>(c,p,R,G,q,a)\<in> \<Theta>.  Pred_wf i p \<and> Rel_wf i R \<and>  Rel_wf i G \<and> 
                     Pred_wf i q \<and>  Pred_wf i a \<longrightarrow>
                   \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat i [p, R, G, q,a])" and 
         a9':"\<forall>i<length xs. Rel_wf i (Par_Guar(xs!i))" and
         a9'':"\<forall>i<length xs. Pred_wf i p" 
{
  assume a10:"\<exists>i j. 
              i<length clist \<and> Suc j<length l \<and> 
              \<Gamma>\<turnstile>\<^sub>c(fst ((snd (clist!i))!j),  toSeqState i (snd((snd (clist!i))!j))) \<rightarrow>\<^sub>e  
                   (fst ((snd (clist!i))!(Suc j)), toSeqState  i (snd((snd (clist!i))!(Suc j)))) \<and> 
              \<not>(snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in> Par_Rely(xs!i)"
  then obtain j where 
    a10:"\<exists>i ns ns'. 
       i<length clist \<and> Suc j<length l \<and> 
       \<Gamma>\<turnstile>\<^sub>c(fst ((snd (clist!i))!j),  toSeqState i (snd((snd (clist!i))!j))) \<rightarrow>\<^sub>e  
              (fst ((snd (clist!i))!(Suc j)), toSeqState  i (snd((snd (clist!i))!(Suc j)))) \<and>
       \<not>(snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in> Par_Rely(xs!i)" by fastforce
   let ?P = "\<lambda>j. \<exists>i. i<length clist \<and> Suc j<length l \<and>
      \<Gamma>\<turnstile>\<^sub>c(fst ((snd (clist!i))!j),  toSeqState i (snd((snd (clist!i))!j))) \<rightarrow>\<^sub>e  
              (fst ((snd (clist!i))!(Suc j)), toSeqState  i (snd((snd (clist!i))!(Suc j)))) \<and>       
      (\<not> (snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in> Par_Rely(xs!i))"        
   obtain m where fist_occ:"(?P m) \<and> (\<forall>i<m. \<not> ?P i)" using exists_first_occ[of ?P j] a10 by blast
     then have "?P m" by fastforce
     then obtain i where
      fst_occ:"i<length clist \<and> Suc m<length l \<and>
               \<Gamma>\<turnstile>\<^sub>c(fst ((snd (clist!i))!m),  toSeqState i (snd((snd (clist!i))!m))) \<rightarrow>\<^sub>e  
                 (fst ((snd (clist!i))!(Suc m)), toSeqState  i (snd((snd (clist!i))!(Suc m)))) \<and>       
      (\<not> (snd((snd (clist!i))!m), snd((snd (clist!i))!Suc m)) \<in> Par_Rely(xs!i))"
     by fastforce
    have notP:"(\<forall>i<m. \<not> ?P i)" using fist_occ by blast     
    have fst_clist_\<Gamma>:"\<forall>i<length clist. fst(clist!i) = \<Gamma>" 
      using a7 unfolding conjoin_def same_functions_def by fastforce
    have compat:"(\<Gamma>\<turnstile>\<^sub>p(l!m)  \<rightarrow> (l!(Suc m))) \<and> 
            (\<exists>i<length clist. 
               ((fst (clist!i))\<turnstile>\<^sub>c(fst ((snd (clist!i))!m),  toSeq (toSeqState i (snd((snd (clist!i))!m)))) \<rightarrow>  
                   (fst ((snd (clist!i))!(Suc m)), toSeq (toSeqState  i (snd((snd (clist!i))!(Suc m))))))  \<and> 
            (\<forall>l<length clist. 
               l\<noteq>i \<longrightarrow>  (fst (clist!l))\<turnstile>\<^sub>c (fst ((snd (clist!l))!m),  toSeqState l (snd((snd (clist!l))!m))) \<rightarrow>\<^sub>e  
                         (fst ((snd (clist!l))!(Suc m)), toSeqState  l (snd((snd (clist!l))!(Suc m)))))) \<or> 
         (\<Gamma>\<turnstile>\<^sub>p(l!m)  \<rightarrow>\<^sub>e (l!(Suc m)) \<and> 
          (\<forall>i<length clist. (fst (clist!i))\<turnstile>\<^sub>c (fst ((snd (clist!i))!m),  toSeqState i (snd((snd (clist!i))!m))) \<rightarrow>\<^sub>e  
                                               (fst ((snd (clist!i))!(Suc m)), toSeqState  i (snd((snd (clist!i))!(Suc m))))))"
     using a7 fst_occ unfolding conjoin_def compat_label_def by simp
     {
       assume a20: "(\<Gamma>\<turnstile>\<^sub>p(l!m)  \<rightarrow>\<^sub>e (l!(Suc m)) \<and> 
          (\<forall>i<length clist.  (fst (clist!i))\<turnstile>\<^sub>c (fst ((snd (clist!i))!m),  toSeqState i (snd((snd (clist!i))!m))) \<rightarrow>\<^sub>e  
                             (fst ((snd (clist!i))!(Suc m)), toSeqState  i (snd((snd (clist!i))!(Suc m))))))"
       then have "(snd (l!m),snd (l!(Suc m))) \<in> R"       
       using fst_occ a5  unfolding par_assum_def by fastforce
       then have "(snd(l!m), snd(l!(Suc m))) \<in>  Par_Rely(xs!i)"
       using fst_occ a3 a0 by fastforce
       then have "(snd ((snd (clist!i))!m), snd ((snd (clist!i))!(Suc m)) ) \<in>  Par_Rely(xs!i)" 
       using a7 fst_occ unfolding conjoin_def same_state_def by fastforce        
       then have False using fst_occ by auto
     }note l = this
     {
      assume a20:"(\<Gamma>\<turnstile>\<^sub>p(l!m)  \<rightarrow> (l!(Suc m))) \<and> 
            (\<exists>i<length clist. 
               ((fst (clist!i))\<turnstile>\<^sub>c(fst ((snd (clist!i))!m),  toSeq (toSeqState i (snd((snd (clist!i))!m)))) \<rightarrow>  
                   (fst ((snd (clist!i))!(Suc m)), toSeq (toSeqState  i (snd((snd (clist!i))!(Suc m)))))) \<and> 
            (\<forall>l<length clist. 
               l\<noteq>i \<longrightarrow>  (fst (clist!l))\<turnstile>\<^sub>c (fst ((snd (clist!l))!m),  toSeqState l (snd((snd (clist!l))!m))) \<rightarrow>\<^sub>e  
                         (fst ((snd (clist!l))!(Suc m)), toSeqState  l (snd((snd (clist!l))!(Suc m))))))"
      then obtain i'  
      where i':"i'<length clist \<and> 
               ((fst (clist!i'))\<turnstile>\<^sub>c(fst ((snd (clist!i'))!m),  toSeq (toSeqState i' (snd((snd (clist!i'))!m)))) \<rightarrow>  
                   (fst ((snd (clist!i'))!(Suc m)), toSeq (toSeqState  i' (snd((snd (clist!i'))!(Suc m)))))) \<and> 
               (\<forall>l<length clist. 
                 l\<noteq>i' \<longrightarrow>  (fst (clist!l))\<turnstile>\<^sub>c (fst ((snd (clist!l))!m),  toSeqState l (snd((snd (clist!l))!m))) \<rightarrow>\<^sub>e  
                         (fst ((snd (clist!l))!(Suc m)), toSeqState  l (snd((snd (clist!l))!(Suc m)))))"
      by fast
      then have eq_\<Gamma>:"\<Gamma> = fst (clist!i')" using a7 unfolding conjoin_def same_functions_def by fastforce
      obtain fp fs sp ss 
      where prod_step: " 
               \<Gamma>\<turnstile>\<^sub>c (fp, fs) \<rightarrow> (sp,ss) \<and> 
              fp = fst (((snd (clist!i'))!m)) \<and> fs = toSeq (toSeqState i' (snd((snd (clist!i'))!m))) \<and> 
              sp = fst ((snd (clist!i'))!(Suc m)) \<and> ss =toSeq (toSeqState  i' (snd((snd (clist!i'))!(Suc m)))) \<and>
              \<Gamma> = fst (clist!i') "
      using eq_\<Gamma> a7 i' unfolding conjoin_def same_functions_def by fast            
      then have False
      proof (cases "i = i'")
        case True       
        then have "l!m = l!(Suc m) "
          using step_e_step_c_eq[OF a7] i' fst_occ eq_\<Gamma> by blast
        then have "\<Gamma>\<turnstile>\<^sub>p(l!m)  \<rightarrow>\<^sub>e (l!(Suc m))" 
          using step_pe.ParEnv
          by (metis prod_cases3)           
        then have "(snd (l ! m), snd (l ! Suc m)) \<in> R "
          using fst_occ  a5 unfolding par_assum_def by fastforce
        then have "(snd (l ! m), snd (l ! Suc m)) \<in> Par_Rely (xs ! i)"
          using a0 a3 fst_occ by fastforce
        then show ?thesis using fst_occ a7
          unfolding conjoin_def same_state_def  
          by fastforce         
      next
        case False  note not_eq = this       
        thus ?thesis 
        proof (cases "fp = sp")
          case True 
          thus ?thesis using prod_step  prod_step
            using step_change_p_or_eq_s by fastforce                               
        next
          case False                    
          let ?l1 = "take (Suc (Suc m)) (snd(clist!i'))"
          have clist_cptni:"(i', \<Gamma>,snd(clist!i')) \<in> cptni" 
            using a6 i' unfolding cpi_def by fastforce
          moreover have i'_inlist:"i' < length (snd (snd (snd (clist ! i') ! 0)))"  
          proof-
            have "i' < length (snd (snd (l!0)))"
              using a9'' a5 unfolding par_assum_def  Pred_wf_def split_beta 
              apply auto
              using a3 i' by fastforce
            moreover have "snd(snd (clist !i')!0) = snd (l!0)" using a7 unfolding conjoin_def same_state_def
              using a10 i' by fastforce 
            ultimately show ?thesis by auto
          qed                                    
          ultimately have clist_cptn:"( \<Gamma>,toSeqCptn i' (snd(clist!i'))) \<in> cptn" using cptni_cptn
            by (metis prod.exhaust_sel)
          have sucm_len:"Suc m < length (snd (clist!i'))" 
            using i' fst_occ a7 unfolding conjoin_def same_length_def by fastforce          
          then have summ_lentake:"Suc m < length ?l1" by fastforce
          have len_l: "0<length l" using fst_occ by fastforce
          also then have cpt_not_empty:"snd (clist!i')\<noteq>[]" 
            using i' a7 unfolding conjoin_def same_length_def by fastforce
          ultimately have "fst (last (snd (clist ! i'))) = (fst (last l))!i'"
            using a7 i' conjoin_same_program_i[OF a7]
            by (simp add: conjoin_def last_conv_nth same_length_def)          
          have  i'_lt_len:"\<forall>j<length (snd (clist ! i')). i'< length (snd (snd ((snd (clist ! i'))!j)))"   
            using i'_inlist a6 unfolding cpi_def
            using clist_cptni
            by (meson a4 a7 i' wf_local_vars)                               
          have not_env_step:"\<not> \<Gamma>\<turnstile>\<^sub>c (fst (snd (clist ! i') ! m), toSeqState i' (snd (snd (clist ! i') ! m))) \<rightarrow>\<^sub>e 
                                   (fst (snd (clist ! i') ! (Suc m)), toSeqState i' (snd (snd (clist ! i') ! (Suc m))))"
            using False etran_ctran_eq_p_normal_s i' prod_step by blast           
          then have "snd ((snd(clist!i'))!0)\<in> p" 
            using len_l a7 i' a5 unfolding conjoin_def same_state_def par_assum_def by fastforce
          then have "snd ((snd(clist!i'))!0)\<in> Par_Pre (xs ! i')"
            using a1 i' a3 by fastforce
          then have clist_0_in_pre:"snd ((take (Suc (Suc m)) (snd(clist!i')))!0)\<in> (Par_Pre (xs ! i'))" 
            by fastforce       
          moreover have 
          "\<forall>j. Suc j < Suc (Suc m) \<longrightarrow>
                \<Gamma>\<turnstile>\<^sub>c (fst (snd (clist ! i') ! j), toSeqState i' (snd (snd (clist ! i') ! j))) \<rightarrow>\<^sub>e 
                    (fst (snd (clist ! i') ! (Suc j)), toSeqState i' (snd (snd (clist ! i') ! (Suc j)))) \<longrightarrow>
                (snd (snd (clist ! i') ! j), snd (snd (clist ! i') ! Suc j)) \<in> Par_Rely (xs ! i')" 
            using not_env_step fst_occ Suc_less_eq fist_occ i' less_SucE less_trans_Suc by auto
          then have "\<forall>j. Suc j < length (take (Suc (Suc m)) (snd(clist!i'))) \<longrightarrow>
                \<Gamma>\<turnstile>\<^sub>c (fst (snd (clist ! i') ! j), toSeqState i' (snd (snd (clist ! i') ! j))) \<rightarrow>\<^sub>e 
                    (fst (snd (clist ! i') ! (Suc j)), toSeqState i' (snd (snd (clist ! i') ! (Suc j)))) \<longrightarrow>
                (snd (snd (clist ! i') ! j), snd (snd (clist ! i') ! Suc j)) \<in> Par_Rely (xs ! i')"
            by fastforce 
          ultimately have assum_p1:"(\<Gamma>, (take (Suc (Suc m)) (snd(clist!i')))) \<in> 
                             assum_p1 i' (Par_Pre (xs ! i'),Par_Rely (xs!i'))"
            unfolding assum_p1_def by fastforce
          have clist_comm:"(\<Gamma>,take (Suc (Suc m)) (snd(clist!i'))) \<in> 
                              comm_p i' (Par_Guar (xs ! i'), 
                                       (Par_Post (xs ! i'),Par_Abr (xs ! i'))) F "            
          proof-
            have "(\<Gamma>, (take (Suc (Suc m)) (snd(clist!i')))) \<in> 
                             assum_p i' ((Par_Pre (xs ! i')),Par_Rely (xs ! i'))"
              using assum_p1 p2[of "take (Suc (Suc m)) (snd (clist ! i'))" i' \<Gamma> "Par_Pre (xs ! i')" "Par_Rely (xs ! i')"] 
                   i'_lt_len cpt_not_empty by auto         
            moreover have "(i', \<Gamma>,snd(clist!i')) \<in> cptni" using a6 i' unfolding cpi_def by fastforce
            then have "(i',\<Gamma>,take (Suc (Suc m)) (snd(clist!i'))) \<in> cptni"
              by (simp add: takecptni_is_cptni)              
            then have "(\<Gamma>,take (Suc (Suc m)) (snd(clist!i'))) \<in> cpi  i' \<Gamma> (Par_Com(xs!i')) s"
              using i' a3 a6 unfolding cpi_def by fastforce   
            moreover have "\<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  Par_Com (xs ! i') sat i' [Par_Pre (xs!i'), Par_Rely (xs ! i'), 
                                 Par_Guar (xs ! i'), Par_Post (xs ! i'),Par_Abr (xs ! i')]"
              by (simp add: a2 a3 i')
            moreover have "\<forall>(c,p,R,G,q,a)\<in> \<Theta>.  Pred_wf i' p \<and> Rel_wf i' R \<and>  Rel_wf i' G \<and> 
                                  Pred_wf i' q \<and>  Pred_wf i' a \<longrightarrow> 
                \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat i' [p, R, G, q,a]" 
              using a8  a3 i'
              by simp
            moreover have  "i' < length (snd s)"
            proof-
              have  "s=snd (take (Suc (Suc m)) (snd(clist!i'))!0)" 
                using calculation unfolding cpi_def by auto
              moreover  have "s  \<in> Par_Pre(xs!i')"              
                using clist_0_in_pre calculation 
                by blast 
              ultimately show ?thesis
                by (simp add: i'_inlist)
            qed
            ultimately show ?thesis by (auto intro:  assum_p_cpi_in_com_p)
          qed
          have "(snd(take (Suc (Suc m)) (snd(clist!i'))!m), 
                        snd(take (Suc (Suc m)) (snd(clist!i'))!(Suc m))) \<in> Par_Guar (xs ! i')"
            using comm_pdest1[OF clist_comm ]  summ_lentake eq_\<Gamma>  i' clist_comm  
                  a9' a3 summ_lentake by force
          then have "(snd( (snd(clist!i'))!m), 
                        snd((snd(clist!i'))!(Suc m))) \<in> Par_Guar (xs ! i')"
          by fastforce
          then have "(snd( (snd(clist!i))!m), 
                      snd((snd(clist!i))!(Suc m))) \<in> Par_Guar (xs ! i')"
           using a7 fst_occ unfolding conjoin_def same_state_def by (metis Suc_lessD i' snd_conv) 
          then have "(snd( (snd(clist!i))!m), 
                      snd((snd(clist!i))!(Suc m))) \<in> Par_Rely (xs ! i)"
          using not_eq a0 i' a3 fst_occ by auto          
          then have "False" using fst_occ by auto
          then show ?thesis by auto
        qed
      qed
     }  
  then have False using compat l by auto
} thus ?thesis by auto
qed

lemma ppp:"\<forall>i<length l. P (l!i) \<Longrightarrow>
       n>0 \<Longrightarrow>
       \<forall>i<length (take n l). P ((take n l)!i)"
  by simp

lemma comm_pdest:
   "(\<Gamma>, l)\<in> comm_p i' (G,(q,a)) F \<Longrightarrow> 
              Rel_wf i' G \<Longrightarrow>
        \<forall>i. Suc i<length l \<longrightarrow>
       \<Gamma>\<turnstile>\<^sub>c (fst (l ! i), toSeq (toSeqState i' (snd (l ! i)))) \<rightarrow>
        (fst (l ! Suc i), toSeq (toSeqState i' (snd (l ! Suc i)))) \<longrightarrow> 
       (snd(l!i), snd(l!(Suc i))) \<in> G"
  using comm_pdest1 by auto

lemma par_cp_not_empty:"\<not> (length xs\<le>length (snd s) ) \<Longrightarrow>
     par_cp  \<Gamma> xs s = {}"
  unfolding par_cp_def wf_state_def by auto

lemma par_cp_dest:
   "par_cp  \<Gamma> xs s\<noteq>{} \<Longrightarrow> 
    length xs \<le>length (snd s) "
  unfolding par_cp_def wf_state_def by auto

lemma two: 
  "\<lbrakk> \<forall>i<length xs. R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Par_Guar (xs ! j)))
       \<subseteq> (Par_Rely (xs ! i));
   p \<subseteq> (\<Inter>i<length xs. (Par_Pre (xs ! i)));
   \<forall>i<length xs.
    \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  Par_Com (xs ! i) sat i [Par_Pre (xs!i), Par_Rely (xs ! i), 
                                        Par_Guar (xs ! i), Par_Post (xs ! i),Par_Abr (xs ! i)];
   length xs=length clist; (\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s; (\<Gamma>,l)\<in>par_assum (p, R);
  \<forall>i<length clist. clist!i\<in>cpi  i \<Gamma> (Par_Com (xs!i)) s; (\<Gamma>,l) \<propto> clist;
  (\<forall>i<length xs.\<forall>(c,p,R,G,q,a)\<in> \<Theta>.  Pred_wf i p \<and> Rel_wf i R \<and>  Rel_wf i G \<and> Pred_wf i q \<and>  Pred_wf i a \<longrightarrow> 
    \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat i [p, R, G, q,a]); \<forall>i<length xs. Rel_wf i (Par_Guar(xs!i)); 
   \<forall>i<length xs. Pred_wf i p\<rbrakk>
  \<Longrightarrow> \<forall>j i. i<length clist \<and> Suc j<length l \<longrightarrow> 
       \<Gamma>\<turnstile>\<^sub>c(fst ((snd (clist!i))!j),  toSeq(toSeqState i (snd((snd (clist!i))!j)))) \<rightarrow>  
         (fst ((snd (clist!i))!(Suc j)), toSeq(toSeqState  i (snd((snd (clist!i))!(Suc j))))) \<longrightarrow>       
        (snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in> Par_Guar(xs!i) "
proof -
  assume a0:"\<forall>i<length xs. R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Par_Guar (xs ! j)))
       \<subseteq> (Par_Rely (xs ! i))" and
         a1:" p \<subseteq> (\<Inter>i<length xs. (Par_Pre (xs ! i)))" and
         a2:"\<forall>i<length xs. \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  Par_Com (xs ! i) sat i [Par_Pre (xs!i), Par_Rely (xs ! i), 
                                 Par_Guar (xs ! i), Par_Post (xs ! i),Par_Abr (xs ! i)]" and
         a3: "length xs=length clist" and
         a4: "(\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s" and
         a5: "(\<Gamma>,l)\<in>par_assum (p, R)" and
         a6: " \<forall>i<length clist. clist!i\<in>cpi  i \<Gamma> (Par_Com(xs!i)) s" and
         a7: "(\<Gamma>,l) \<propto> clist" and
         a8: "\<forall>i<length xs.(\<forall>(c,p,R,G,q,a)\<in> \<Theta>.  Pred_wf i p \<and> Rel_wf i R \<and>  Rel_wf i G \<and> 
                     Pred_wf i q \<and>  Pred_wf i a \<longrightarrow>
                   \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat i [p, R, G, q,a])" and 
         a9':"\<forall>i<length xs. Rel_wf i (Par_Guar(xs!i))" and 
         a9'':"\<forall>i<length xs. Pred_wf i p" 
  {
     assume a10:"(\<exists>i j. i<length clist \<and> Suc j<length l \<and>  
      \<Gamma>\<turnstile>\<^sub>c(fst ((snd (clist!i))!j),  toSeq(toSeqState i (snd((snd (clist!i))!j)))) \<rightarrow>  
         (fst ((snd (clist!i))!(Suc j)), toSeq(toSeqState  i (snd((snd (clist!i))!(Suc j))))) \<and> 
       \<not> (snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in> Par_Guar(xs!i)) "
     then obtain j where a10: "\<exists>i. i<length clist \<and> Suc j<length l \<and>
      \<Gamma>\<turnstile>\<^sub>c(fst ((snd (clist!i))!j),  toSeq(toSeqState i (snd((snd (clist!i))!j)))) \<rightarrow>  
         (fst ((snd (clist!i))!(Suc j)), toSeq(toSeqState  i (snd((snd (clist!i))!(Suc j))))) \<and>        
      \<not> (snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in> Par_Guar(xs!i)"
     by fastforce
     let ?P = "\<lambda>j. \<exists>i. i<length clist \<and> Suc j<length l \<and>
      \<Gamma>\<turnstile>\<^sub>c(fst ((snd (clist!i))!j),  toSeq(toSeqState i (snd((snd (clist!i))!j)))) \<rightarrow>  
         (fst ((snd (clist!i))!(Suc j)), toSeq(toSeqState  i (snd((snd (clist!i))!(Suc j))))) \<and>       
      \<not> (snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in> Par_Guar(xs!i)"     
     obtain m where fist_occ:"?P m \<and> (\<forall>i<m. \<not> ?P i)" using exists_first_occ[of ?P j] a10 by blast
     then have P:"?P m" by fastforce
     then have notP:"(\<forall>i<m. \<not> ?P i)" using fist_occ by blast
     obtain i ns ns' where fst_occ:"i<length clist \<and> Suc m<length l \<and> 
      \<Gamma>\<turnstile>\<^sub>c(fst ((snd (clist!i))!m),  toSeq(toSeqState i (snd((snd (clist!i))!m)))) \<rightarrow>  
         (fst ((snd (clist!i))!(Suc m)), toSeq(toSeqState  i (snd((snd (clist!i))!(Suc m))))) \<and>      
      (\<not> (snd((snd (clist!i))!m), snd((snd (clist!i))!Suc m)) \<in>  Par_Guar(xs!i))"
       using P by fastforce
     have fst_clist_i: "fst (clist!i) = \<Gamma>" 
         using a7 fst_occ unfolding conjoin_def same_functions_def 
         by fastforce
     have "clist!i\<in>cpi i \<Gamma> (Par_Com(xs!i)) s" using a6 fst_occ by fastforce
     then have clistcp:"(\<Gamma>, snd (clist!i))\<in>cpi  i \<Gamma> (Par_Com(xs!i)) s" 
       using  fst_occ a7 unfolding conjoin_def same_functions_def by fastforce   
     moreover have i'_inlist:"i < length (snd (snd (snd (clist ! i) ! 0) ))"  
     proof-
       have "i < length (snd (snd (l!0)))"
         using a3 fst_occ a9'' a5 unfolding par_assum_def  Pred_wf_def split_beta 
         by fastforce
       moreover have "snd(snd (clist !i)!0) = snd (l!0)" using a7 unfolding conjoin_def same_state_def
         using a10 fst_occ by fastforce 
       ultimately show ?thesis by auto
     qed   
     ultimately have clisti_wf:"\<forall>j<length (snd (clist !i)).  i < length (snd (snd (snd (clist ! i) ! j)))"
       unfolding cpi_def using a4 a7 fst_occ wf_local_vars by blast     
     let ?li="take (Suc (Suc m)) (snd (clist!i))"     
     have "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub>  Par_Com (xs ! i) sat i [Par_Pre (xs!i), Par_Rely (xs ! i), 
                Par_Guar (xs ! i), Par_Post (xs ! i),Par_Abr (xs ! i)]"
       using a8 a2 a3 fst_occ unfolding comp_cvalidity_def by fastforce
     have clist_take_wf: "\<forall>j<length ?li.  i < length (snd (snd (?li ! j)))" 
       using clisti_wf by auto
     moreover have take_in_ass:"(\<Gamma>, take (Suc (Suc m)) (snd (clist!i))) \<in> assum_p i (Par_Pre(xs!i), Par_Rely(xs!i))"      
     proof -
       have length_take_length_l:"length (take (Suc (Suc m)) (snd (clist!i))) \<le> length l"
         using a7 fst_occ unfolding conjoin_def same_length_def by auto
       have "snd((?li!0)) \<in> Par_Pre(xs!i)" 
       proof -
         have "(take (Suc (Suc m)) (snd (clist!i)))!0 = (snd (clist!i))!0" by fastforce
         moreover have "snd (snd(clist!i)!0) = snd (l!0)" 
           using a7 fst_occ unfolding conjoin_def same_state_def by fastforce
         moreover have "snd (l!0) \<in>  p" 
           using a5 unfolding par_assum_def by fastforce
         ultimately show ?thesis using a1 a3 fst_occ by fastforce 
       qed note left=this
       then have p1:"(\<Gamma>, take (Suc (Suc m)) (snd (clist!i))) \<in> assum_p1 i (Par_Pre(xs!i), Par_Rely(xs!i))"   
         using two'[OF a0 a1 a2 a3 a4 a5 a6 a7 a8 a9' a9'' ] fst_occ 
         unfolding assum_p1_def split_beta Image_def assum_def image_def by auto                          
       then have "(\<Gamma>, take (Suc (Suc m)) (snd (clist!i))) \<in> assum_p i (Par_Pre(xs!i), Par_Rely(xs!i))" 
         using  p2[OF clist_take_wf _ p1]
         by (metis a7 conjoin_def fst_occ list.size(3) nat.distinct(1) 
                   not_less0 same_length_def snd_conv take_eq_Nil)                                   
       then show ?thesis by auto
     qed     
     moreover have take_cpi:"(\<Gamma>,take (Suc (Suc m)) (snd (clist!i))) \<in> cpi  i \<Gamma> (Par_Com(xs!i)) s"
       using  clistcp unfolding cpi_def by fastforce      
     ultimately have comm:"(\<Gamma>, take (Suc (Suc m)) (snd (clist!i)))\<in>
                               comm_p i (Par_Guar(xs!i),(Par_Post (xs ! i),Par_Abr (xs ! i))) F"       
       using assum_p_cpi_in_com_p[OF take_in_ass take_cpi,of \<Theta> F "Par_Guar(xs!i)" 
                                        "Par_Post(xs!i)" "Par_Abr(xs!i)"] a2 a8 unfolding cpi_def       
       using a3 fst_occ i'_inlist by auto     
     (* also have not_fault:"fst (last (take (Suc (Suc m)) (snd (clist!i))))  \<notin> Fault ` F"
     proof -      
       have last_fault:"fst (last (snd (clist!i))) \<notin> Fault ` F" 
         using a9 unfolding not_fault_def
         by (smt a7 conjoin_def conjoin_same_length conjoin_same_program_i 
              diff_Suc_1 fst_occ last_conv_nth 
               lessI less_imp_Suc_add list.size(3) not_less0 same_length_def snd_conv)         
       have sucm:"Suc m < length (snd (clist!i))" 
         using fst_occ a7 unfolding conjoin_def same_length_def by fastforce      
       then have sucm_not_fault:"fst ((snd (clist!i))!(Suc m)) \<notin> Fault ` F"
         using a3 a9' comm comm_pdest1 fst_occ by fastforce
       have "length (take (Suc (Suc m)) (snd (clist!i))) = Suc (Suc m)" 
         using sucm by fastforce
       then have "last (take (Suc (Suc m)) (snd (clist!i))) =  (take (Suc (Suc m)) (snd (clist!i)))!(Suc m)" 
         by (metis Suc_diff_1 Suc_inject last_conv_nth list.size(3) old.nat.distinct(2) zero_less_Suc)
       moreover have "(take (Suc (Suc m)) (snd (clist!i)))!(Suc m) = (snd (clist!i))!(Suc m)" 
         by fastforce      
       ultimately show ?thesis using sucm_not_fault by fastforce
     qed *)
     then have " Suc m < length (snd (clist ! i))  \<longrightarrow>
                 \<Gamma>\<turnstile>\<^sub>c (fst ((snd (clist!i))!m),  toSeq(toSeqState i (snd((snd (clist!i))!m)))) \<rightarrow>
                     (fst ((snd (clist!i))!(Suc m)),  toSeq(toSeqState i (snd((snd (clist!i))!(Suc m))))) \<longrightarrow>                      
                    (snd ((snd (clist ! i)) ! m), snd ((snd (clist ! i)) ! Suc m)) \<in> Par_Guar(xs!i)"
       using comm_pdest [OF comm ]
       using a3 a9' fst_occ by auto     
     then have "False" using fst_occ using a7 unfolding conjoin_def same_length_def by fastforce
  } thus ?thesis by fastforce
qed

lemma par_cptn_env_comp:
  "(\<Gamma>,l) \<in> par_cptn \<and> Suc i<length l \<Longrightarrow> 
   \<Gamma>\<turnstile>\<^sub>p l!i \<rightarrow>\<^sub>e (l!(Suc i)) \<or> \<Gamma> \<turnstile>\<^sub>p l!i \<rightarrow> (l!(Suc i))"
proof -
  assume a0:"(\<Gamma>,l) \<in> par_cptn \<and> Suc i<length l"         
  then obtain c1 s1 c2 s2 where li:"l!i=(c1,s1) \<and> l!(Suc i) = (c2,s2)"
    using prod.exhaust_sel by blast 
  obtain xs ys where l:"l= xs@((l!i)#(l!(Suc i))#ys)" using a0
    by (metis Cons_nth_drop_Suc Suc_less_SucD id_take_nth_drop less_SucI)
  moreover then have "(drop (length xs) l) = ((l!i)#(l!(Suc i))#ys)"
    by (metis append_eq_conv_conj) 
  moreover then have "length xs < length l" using leI by fastforce 
  ultimately have "(\<Gamma>,((l!i)#(l!(Suc i))#ys))\<in>par_cptn" 
    using a0 droppar_cptn_is_par_cptn by fastforce
  also then have "(\<Gamma>,(l!(Suc i))#ys)\<in>par_cptn" using par_cptn_dest li by fastforce
  ultimately show ?thesis using li par_cptn_elim_cases(2)
    by metis
qed


lemma three:
  "\<lbrakk>xs\<noteq>[]; 
   \<forall>i<length xs. R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Par_Guar (xs ! j)))
       \<subseteq> (Par_Rely (xs ! i));
   p \<subseteq> (\<Inter>i<length xs. (Par_Pre (xs ! i)));
   \<forall>i<length xs.
    \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  Par_Com (xs ! i) sat i [Par_Pre (xs!i), Par_Rely (xs ! i), 
                                        Par_Guar (xs ! i), Par_Post (xs ! i),Par_Abr (xs ! i)];
   length xs=length clist; (\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s; (\<Gamma>,l)\<in>par_assum (p, R);
     \<forall>i<length clist. clist!i\<in>cpi i \<Gamma> (Par_Com (xs!i)) s; (\<Gamma>,l) \<propto> clist;
    \<forall>i<length xs.\<forall>(c,p,R,G,q,a)\<in> \<Theta>.  Pred_wf i p \<and> Rel_wf i R \<and>  Rel_wf i G \<and> Pred_wf i q \<and>  Pred_wf i a \<longrightarrow> 
    \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat i [p, R, G, q,a]; \<forall>i<length xs. Rel_wf i (Par_Guar(xs!i)); 
   \<forall>i<length xs. Pred_wf i p\<rbrakk>
  \<Longrightarrow>  \<forall>i j. i<length clist \<and> Suc j<length l \<longrightarrow> 
      \<Gamma>\<turnstile>\<^sub>c(fst ((snd (clist!i))!j),  toSeqState i (snd((snd (clist!i))!j))) \<rightarrow>\<^sub>e  
         (fst ((snd (clist!i))!(Suc j)), toSeqState  i (snd((snd (clist!i))!(Suc j)))) \<longrightarrow> 
      (snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j))  \<in>          
             (R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Par_Guar (xs ! j))))"
proof -
 assume a0:"xs\<noteq>[]" and
        a1:"\<forall>i<length xs. R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Par_Guar (xs ! j)))
              \<subseteq> (Par_Rely (xs ! i))" and
        a2: "p \<subseteq> (\<Inter>i<length xs. (Par_Pre (xs ! i)))" and
        a3: "\<forall>i<length xs. \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  Par_Com (xs ! i) sat i [Par_Pre (xs!i), Par_Rely (xs ! i), 
                                        Par_Guar (xs ! i), Par_Post (xs ! i),Par_Abr (xs ! i)]" and
        a4: "length xs=length clist" and
        a5: "(\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s" and
        a6: "(\<Gamma>,l) \<in> par_assum(p, R)" and
        a7: "\<forall>i<length clist. clist!i\<in>cpi i \<Gamma> (Par_Com (xs!i)) s" and
        a8: "(\<Gamma>,l) \<propto> clist" and
        a9: "\<forall>i<length xs.\<forall>(c,p,R,G,q,a)\<in> \<Theta>.  
                   Pred_wf i p \<and> Rel_wf i R \<and>  Rel_wf i G \<and> Pred_wf i q \<and>  Pred_wf i a \<longrightarrow> 
                       \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat i [p, R, G, q,a]" and        
        a10':"\<forall>i<length xs. Rel_wf i (Par_Guar(xs!i))" and 
        a12:"\<forall>i<length xs. Pred_wf i p"
  {
  fix j i ns ns'
  assume a00:"i<length clist \<and> Suc j<length l" and
         a11: " \<Gamma>\<turnstile>\<^sub>c(fst ((snd (clist!i))!j),  toSeqState i (snd((snd (clist!i))!j))) \<rightarrow>\<^sub>e  
                   (fst ((snd (clist!i))!(Suc j)), toSeqState  i (snd((snd (clist!i))!(Suc j))))"         
  then have two:"\<forall>j i. i<length clist \<and> Suc j<length l \<longrightarrow> 
       \<Gamma>\<turnstile>\<^sub>c(fst ((snd (clist!i))!j),  toSeq(toSeqState i (snd((snd (clist!i))!j)))) \<rightarrow>  
         (fst ((snd (clist!i))!(Suc j)), toSeq(toSeqState  i (snd((snd (clist!i))!(Suc j))))) \<longrightarrow>       
        (snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in> Par_Guar(xs!i) "
     using two[OF a1 a2 a3 a4 a5 a6 a7 a8 a9 a10' a12]  by auto
  then have j_lenl:"Suc j<length l" using a00 by fastforce
  have i_lj:"i<length (fst (l!j)) \<and> i<length (fst (l!(Suc j)))" 
            using conjoin_same_length a00 a8 by fastforce 
  have fst_clist_\<Gamma>:"\<forall>i<length clist. fst(clist!i) = \<Gamma>" using a8 unfolding conjoin_def same_functions_def by fastforce
  have "\<Gamma>\<turnstile>\<^sub>p(l!j)  \<rightarrow> (l!(Suc j)) \<and> 
            (\<exists>i<length clist. 
               (fst (clist!i))\<turnstile>\<^sub>c(fst ((snd (clist!i))!j),  toSeq (toSeqState i (snd((snd (clist!i))!j)))) \<rightarrow>  
                   (fst ((snd (clist!i))!(Suc j)), toSeq (toSeqState  i (snd((snd (clist!i))!(Suc j))))) \<and> 
            (\<forall>l<length clist.                                           
               l\<noteq>i \<longrightarrow>  (fst (clist!l))\<turnstile>\<^sub>c(fst ((snd (clist!l))!j),  toSeqState l (snd((snd (clist!l))!j))) \<rightarrow>\<^sub>e  
                        (fst ((snd (clist!l))!(Suc j)), toSeqState  l (snd((snd (clist!l))!(Suc j))))  )) \<or> 
         (\<Gamma>\<turnstile>\<^sub>p(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)) \<and> 
          (\<forall>i<length clist. (fst (clist!i))\<turnstile>\<^sub>c(fst ((snd (clist!i))!j),  toSeqState i (snd((snd (clist!i))!j))) \<rightarrow>\<^sub>e  
                            (fst ((snd (clist!i))!(Suc j)), toSeqState  i (snd((snd (clist!i))!(Suc j))))))"      
  using a8 a00 unfolding conjoin_def compat_label_def split_beta by simp
  then have compat_label:"\<Gamma>\<turnstile>\<^sub>p(l!j)  \<rightarrow> (l!(Suc j)) \<and> 
            (\<exists>i<length clist. 
               \<Gamma>\<turnstile>\<^sub>c(fst ((snd (clist!i))!j),  toSeq (toSeqState i (snd((snd (clist!i))!j)))) \<rightarrow>  
                   (fst ((snd (clist!i))!(Suc j)), toSeq (toSeqState  i (snd((snd (clist!i))!(Suc j))))) \<and> 
            (\<forall>l<length clist.                                           
               l\<noteq>i \<longrightarrow>  \<Gamma>\<turnstile>\<^sub>c(fst ((snd (clist!l))!j),  toSeqState l (snd((snd (clist!l))!j))) \<rightarrow>\<^sub>e  
                        (fst ((snd (clist!l))!(Suc j)), toSeqState  l (snd((snd (clist!l))!(Suc j))))  )) \<or> 
         (\<Gamma>\<turnstile>\<^sub>p(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)) \<and> 
          (\<forall>i<length clist. \<Gamma>\<turnstile>\<^sub>c(fst ((snd (clist!i))!j),  toSeqState i (snd((snd (clist!i))!j))) \<rightarrow>\<^sub>e  
                            (fst ((snd (clist!i))!(Suc j)), toSeqState  i (snd((snd (clist!i))!(Suc j))))))"
  using fst_clist_\<Gamma> by blast
  then have "(snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in>            
               (R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. Par_Guar (xs ! j)))" 
  proof        
    assume a10:"\<Gamma>\<turnstile>\<^sub>p(l!j)  \<rightarrow> (l!(Suc j)) \<and> 
            (\<exists>i<length clist. 
               \<Gamma>\<turnstile>\<^sub>c(fst ((snd (clist!i))!j),  toSeq (toSeqState i (snd((snd (clist!i))!j)))) \<rightarrow>  
                   (fst ((snd (clist!i))!(Suc j)), toSeq (toSeqState  i (snd((snd (clist!i))!(Suc j))))) \<and> 
            (\<forall>l<length clist.                                           
               l\<noteq>i \<longrightarrow>  \<Gamma>\<turnstile>\<^sub>c(fst ((snd (clist!l))!j),  toSeqState l (snd((snd (clist!l))!j))) \<rightarrow>\<^sub>e  
                        (fst ((snd (clist!l))!(Suc j)), toSeqState  l (snd((snd (clist!l))!(Suc j))))))" 
    then obtain i' where 
            a20:"\<Gamma>\<turnstile>\<^sub>c(fst ((snd (clist!i'))!j),  toSeq (toSeqState i' (snd((snd (clist!i'))!j)))) \<rightarrow>  
                   (fst ((snd (clist!i'))!(Suc j)), toSeq (toSeqState  i' (snd((snd (clist!i'))!(Suc j))))) \<and> 
            (\<forall>l<length clist.                                           
               l\<noteq>i' \<longrightarrow>  \<Gamma>\<turnstile>\<^sub>c(fst ((snd (clist!l))!j),  toSeqState l (snd((snd (clist!l))!j))) \<rightarrow>\<^sub>e  
                        (fst ((snd (clist!l))!(Suc j)), toSeqState  l (snd((snd (clist!l))!(Suc j)))))" 
      by blast    
    thus ?thesis 
    proof (cases "i'=i")
      case True note eq_i = this      
      then obtain P S1 S2 where P:"(snd (clist!i'))!j=(P,S1) \<and> ((snd (clist!i'))!(Suc j)) = (P,S2)"   
        using a11
        using a20 etran_ctran_False by blast
      then have allP:"\<forall>l< length clist. fst ((snd (clist!l))!j) = fst ((snd (clist!l))!(Suc j))"
        using a20  by (simp add: P mod_env_not_component) 
      thus ?thesis 
      proof (cases "S1 = S2")
        case True 
        have snd_lj:"(snd (l!j)) = snd ((snd (clist!i'))!j)"
            using eq_i a8 a20 a00 unfolding conjoin_def same_state_def
            by auto
        have all_e:"\<forall>l<length clist. \<Gamma>\<turnstile>\<^sub>c(fst ((snd (clist!l))!j),  toSeqState l (snd((snd (clist!l))!j))) \<rightarrow>\<^sub>e  
                        (fst ((snd (clist!l))!(Suc j)), toSeqState  l (snd((snd (clist!l))!(Suc j))))"
          using a11 a20 eq_i by fastforce
        then have "fst (l!j) = (fst (l!(Suc j)))"
          using allP a8 conjoin_same_program_i_j [of "(\<Gamma>,l)"] a00 by fastforce
        also have "snd (l!j) = snd (l!(Suc j))"
        proof -              
          have "(snd (l!Suc j)) = snd ((snd (clist!i'))!(Suc j))"
            using a8 a20 a00
            using a11 eq_i etran_ctran_False by blast 
          then show ?thesis using snd_lj P True by auto
        qed 
        ultimately have "l!j = l!(Suc j)" by (simp add: prod_eq_iff) 
                           
        then have "\<Gamma>\<turnstile>\<^sub>p(l!j)  \<rightarrow>\<^sub>e (l!(Suc j))" 
          using P step_pe.ParEnv snd_lj by (metis prod.collapse)          
        then have "(snd (l ! j), snd (l ! Suc j)) \<in> R "
          using a00 a6 unfolding par_assum_def by fastforce
        then show ?thesis using a8 a00 
          unfolding conjoin_def same_state_def  
         by fastforce
      next
        case False thus ?thesis 
          using a20 P a11 step_change_p_or_eq_s by force
      qed
    next
      case False 
      have i'_clist:"i' < length clist" using a20
        using a10 etran_ctran_False by blast 
      then have clist_i'_Guardxs:"(snd((snd (clist!i'))!j), snd((snd (clist!i'))!Suc j)) \<in> Par_Guar(xs!i')"
        using two a00 False a8 unfolding conjoin_def same_state_def
        by (metis a20)
      have "snd((snd (clist!i))!j) = snd (l!j) \<and> snd((snd (clist!i))!Suc j) = snd (l!Suc j)" 
        using a00 a20 a8 unfolding conjoin_def same_state_def by fastforce
      also have "snd((snd (clist!i'))!j) = snd (l!j) \<and> snd((snd (clist!i'))!Suc j) = snd (l!Suc j)"
        using i'_clist j_lenl a20 a8 unfolding conjoin_def same_state_def
        by auto
      ultimately have "snd((snd (clist!i))!j) = snd((snd (clist!i'))!j) \<and> 
                    snd((snd (clist!i))!Suc j) = snd((snd (clist!i'))!Suc j)" 
        by fastforce
      then have clist_i_Guardxs:
        "(snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in> 
            Par_Guar(xs!i')"  
        using  clist_i'_Guardxs by fastforce     
      then show ?thesis  
        using False a4 i'_clist by fastforce        
    qed
  next
    assume a10:"\<Gamma>\<turnstile>\<^sub>p(l!j)  \<rightarrow>\<^sub>e (l!(Suc j)) \<and> 
          (\<forall>i<length clist. \<Gamma>\<turnstile>\<^sub>c(fst ((snd (clist!i))!j),  toSeqState i (snd((snd (clist!i))!j))) \<rightarrow>\<^sub>e  
                            (fst ((snd (clist!i))!(Suc j)), toSeqState  i (snd((snd (clist!i))!(Suc j)))))"      
    then have "(snd (l ! j), snd (l ! Suc j)) \<in> R"
      using a00 a10 a6 unfolding par_assum_def by fastforce
    then show ?thesis using a8 a00 
      unfolding conjoin_def same_state_def
      by fastforce
  qed
  }  thus ?thesis by blast
qed

definition tran_True where "tran_True \<equiv> True"

definition after where "after \<equiv> True"

lemma four:
  "\<lbrakk>xs\<noteq>[]; \<forall>i<length xs. R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Par_Guar (xs ! j)))
       \<subseteq> (Par_Rely (xs ! i));
   (\<Union>j<length xs.  (Par_Guar (xs ! j))) \<subseteq> (G);
   p \<subseteq> (\<Inter>i<length xs. (Par_Pre (xs ! i)));
   \<forall>i<length xs.
    \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  Par_Com (xs ! i) sat i [Par_Pre (xs!i), Par_Rely (xs ! i), 
                                        Par_Guar (xs ! i), Par_Post (xs ! i),Par_Abr (xs ! i)];
    (\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s; (\<Gamma>,l) \<in> par_assum(p, R); Suc i < length l;
   \<Gamma>\<turnstile>\<^sub>p (l!i) \<rightarrow> (l!(Suc i));
   \<forall>i<length xs.\<forall>(c,p,R,G,q,a)\<in> \<Theta>.  Pred_wf i p \<and> Rel_wf i R \<and>  Rel_wf i G \<and> Pred_wf i q \<and>  Pred_wf i a \<longrightarrow> 
    \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat i [p, R, G, q,a]; \<forall>i<length xs. Rel_wf i (Par_Guar(xs!i));  
    \<forall>i<length xs. Pred_wf i p\<rbrakk>
  \<Longrightarrow> (snd (l ! i), snd (l ! Suc i)) \<in> G"
proof -
  assume a0:"xs\<noteq>[]" and
         a1:"\<forall>i<length xs. R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Par_Guar (xs ! j))) \<subseteq> 
               (Par_Rely (xs ! i))" and
         a2:"(\<Union>j<length xs.  (Par_Guar (xs ! j))) \<subseteq> (G)" and
         a3:"p \<subseteq> (\<Inter>i<length xs.  (Par_Pre (xs ! i)))" and
         a4:"\<forall>i<length xs. \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  Par_Com (xs ! i) sat i [Par_Pre (xs!i), Par_Rely (xs ! i), 
                                        Par_Guar (xs ! i), Par_Post (xs ! i),Par_Abr (xs ! i)]" and
         a5:"(\<Gamma>,l) \<in> par_cp  \<Gamma> (ParallelCom xs) s" and
         a6:"(\<Gamma>,l) \<in> par_assum(p, R)" and
         a7: "Suc i < length l" and
         a8:"\<Gamma>\<turnstile>\<^sub>p (l!i) \<rightarrow> (l!(Suc i))" and         
         a10:"\<forall>i<length xs.\<forall>(c,p,R,G,q,a)\<in> \<Theta>.  
                Pred_wf i p \<and> Rel_wf i R \<and>  Rel_wf i G \<and> Pred_wf i q \<and>  Pred_wf i a \<longrightarrow> 
                \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat i [p, R, G, q,a]" and
          a12:"\<forall>i<length xs. Rel_wf i (Par_Guar(xs!i))" 
           and a13:" \<forall>i<length xs. Pred_wf i p"
   have i_len:"i<length l" using a7 by auto
   have length_par_xs:"length (ParallelCom xs) = length xs" unfolding ParallelCom_def  by fastforce   
   then have par:"(ParallelCom xs)\<noteq>[]" using a0 by fastforce 
   
   then have "(\<Gamma>,l) \<in>{(\<Gamma>1,c). \<exists>clist. (length clist)=(length (ParallelCom xs)) \<and> 
               (\<forall>i<length clist. (clist!i) \<in> cpi  i \<Gamma> ((ParallelCom xs)!i) s) \<and> (\<Gamma>,c) \<propto> clist \<and> \<Gamma>1=\<Gamma>}"
     using one[OF par] a5 length_par_xs by auto
   then obtain clist where cpi:"(length clist)=(length xs) \<and> 
               (\<forall>i<length clist. (clist!i) \<in> cpi  i \<Gamma> ((ParallelCom xs)!i) s) \<and> (\<Gamma>,l) \<propto> clist"
     using length_par_xs by auto
   then have conjoin:"(length clist)=(length xs) \<and> 
               (\<forall>i<length clist. (clist!i) \<in> cpi i \<Gamma> (Par_Com (xs ! i)) s) \<and> (\<Gamma>,l) \<propto> clist"
     using ParallelCom_Com by fastforce
   then have length_xs_clist:"length xs = length clist" by auto 
   have clist_cp:"\<forall>i<length clist. (clist!i) \<in> cpi i \<Gamma>  (Par_Com (xs ! i)) s" 
     using conjoin by auto
   have conjoin:"(\<Gamma>,l) \<propto> clist" using conjoin by auto     
   have l_not_empty:"l\<noteq>[]" using a5 par_cptn.simps unfolding par_cp_def by fastforce
   then have l_g0:"0<length l" by fastforce  
   then have last_l:"last l = l!((length l) - 1)" by (simp add: last_conv_nth)    
   have "\<forall>i< length l. fst (l!i) = map (\<lambda>x. fst ((snd x)!i)) clist"
     using conjoin unfolding conjoin_def same_program_def by fastforce
   obtain Ps si Ps' ssi where li:"l!i = (Ps,si) \<and> l!(Suc i) = (Ps', ssi)"
     using prod.exhaust_sel by blast 
   then obtain j r s' where  
        step_c:"l ! i = (Ps, si) \<and> l ! Suc i = (Ps[j := r], toPar j s' si) \<and> j < length Ps \<and>
         \<Gamma>\<turnstile>\<^sub>c (Ps ! j, toSeqPar j si) \<rightarrow> (r, s')"
     using par_ctranE[OF a8]   by fastforce            
   have length_Ps_clist:
     "length Ps = length clist \<and> length Ps = length Ps'" 
     using conjoin a7 conjoin_same_length li step_c  by fastforce
   then have j_len:"j<length clist" and j_xs:" j<length xs"
     using step_c length_xs_clist length_Ps_clist by auto
   have from_step:"(snd (clist!j))!i = ((Ps!j),si) \<and> (snd (clist!j))!(Suc i) = (Ps'!j,ssi)"  
   proof -     
     have f2: "Ps = fst (snd (\<Gamma>, l) ! i)" and f2':"Ps' = fst (snd (\<Gamma>, l) ! (Suc i))"
       using li by auto
     have f3:"si = snd (snd (\<Gamma>, l) ! i) \<and> ssi = snd (snd (\<Gamma>, l) ! (Suc i))"
       by (simp add: li)
     then have "(snd (clist!j))!i = ((Ps!j),si)"
       using f2 conjoin  step_c unfolding conjoin_def same_program_def same_state_def
       using  conjoin_same_program_i[OF conjoin _ j_len] i_len
       by (metis j_len prod.collapse snd_conv)            
     moreover have "(snd (clist!j))!(Suc i) = (Ps'!j,ssi)"
       using f2' f3 conjoin a7 step_c length_Ps_clist 
      unfolding conjoin_def same_program_def same_state_def
      using  conjoin_same_program_i[OF conjoin _ j_len] i_len
      by (metis eq_snd_iff fst_conv)     
     ultimately show ?thesis by auto
   qed                      
   then have step_clist:" \<Gamma>\<turnstile>\<^sub>c (fst (snd (clist ! j) ! i), toSeq(toSeqState j (snd((snd (clist!j))!i)))) \<rightarrow> 
                           (fst (snd (clist ! j) ! (Suc i)), toSeq(toSeqState j (snd((snd (clist!j))!(Suc i)))))"
   proof-
     have len_clist_0:"length xs \<le> length (snd (snd ((snd (clist!j))!0) ))"
       using conjoin conjoin_def conjoin_same_length j_len l_not_empty 
            length_xs_clist unfolding same_length_state_program_def same_state_def by fastforce       
     then have len_clist_j:"length xs \<le> length (snd (snd ((snd (clist!j))!i)))"
     proof-
       have cptni:"(j, \<Gamma>, snd (clist ! j)) \<in> cptni" using cpi j_len
         unfolding cpi_def by auto
       show ?thesis 
         using  i_len cptni len_clist_0 cptni_i_normal_len j_len conjoin a7 l_g0 
         unfolding same_length_def conjoin_def apply auto         
         by (smt One_nat_def cptni_i_normal_len i_len l_g0 less_Suc_eq_le less_trans_Suc 
            prod.collapse zero_less_Suc) 
     qed   
     have len_si:"length Ps \<le> length (snd si)"
       using from_step  length_Ps_clist length_xs_clist len_clist_j by auto 
     then show ?thesis using step_p_elim_toseqpar[OF a8[simplified from_step li]  ] 
       by (metis from_step fst_conv li nth_list_update sndI step_c 
                 step_change_p_or_eq_Ns toSeqPar_eq_toSeq)
   qed
   have 
     "\<forall>j i. i<length clist \<and> Suc j<length l \<longrightarrow> 
       \<Gamma>\<turnstile>\<^sub>c(fst ((snd (clist!i))!j),  toSeq(toSeqState i (snd((snd (clist!i))!j)))) \<rightarrow>  
         (fst ((snd (clist!i))!(Suc j)), toSeq(toSeqState  i (snd((snd (clist!i))!(Suc j))))) \<longrightarrow>       
        (snd((snd (clist!i))!j), snd((snd (clist!i))!Suc j)) \<in> Par_Guar(xs!i) "
    using two[OF a1 a3 a4 length_xs_clist a5 a6 clist_cp conjoin a10 a12 a13] by auto
   then have "(snd (snd (clist ! j) ! i), snd (snd (clist ! j) ! Suc i)) \<in> Par_Guar (xs ! j)"
     using a7 step_c length_Ps_clist step_clist by metis     
   then have "(snd (l!i), snd (l!(Suc i)))\<in> Par_Guar (xs ! j)"
      using from_step a2 length_xs_clist step_c li by fastforce
   then show ?thesis using a2 j_xs
     unfolding  tran_True_def after_def Satis_def by fastforce
qed


lemma same_program_last:"l\<noteq>[] \<Longrightarrow> (\<Gamma>,l) \<propto> clist  \<Longrightarrow> i<length clist \<Longrightarrow>fst (last (snd (clist!i))) = fst (last l) ! i" 
proof -
   assume l_not_empty:"l\<noteq>[]" and
          conjoin: "(\<Gamma>,l) \<propto> clist" and
          i_clist: "i<length clist"
   have last_clist_eq_l:"\<forall>i<length clist. last (snd (clist!i)) = (snd (clist!i))!((length l) - 1)"
          using conjoin  last_conv_nth l_not_empty 
          unfolding conjoin_def same_length_def
          by (metis length_0_conv snd_eqD) 
   then have last_l:"last l = l!((length l)-1)" using l_not_empty by (simp add: last_conv_nth)
   have "fst (last l) = map (\<lambda>x. fst (snd x ! ((length l)-1))) clist"
     using l_not_empty last_l conjoin unfolding conjoin_def same_program_def  by auto
   also have "(map (\<lambda>x. fst (snd x ! ((length l)-1))) clist)!i = 
            fst ((snd (clist!i))! ((length l)-1))" using i_clist by fastforce
   also have  "fst ((snd (clist!i))! ((length l)-1)) = 
             fst ((snd (clist!i))! ((length (snd (clist!i)))-1))" 
     using conjoin i_clist unfolding conjoin_def same_length_def by fastforce
   also then have "fst ((snd (clist!i))! ((length (snd (clist!i)))-1)) = fst (last (snd (clist!i)))"
     using i_clist l_not_empty conjoin last_clist_eq_l last_conv_nth unfolding conjoin_def same_length_def
     by presburger
   finally show ?thesis by auto
qed



lemma five:
  "\<lbrakk>xs\<noteq>[];  \<forall>i<length xs.  R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Par_Guar (xs ! j)))
       \<subseteq> (Par_Rely (xs ! i));
   p \<subseteq> (\<Inter>i<length xs. (Par_Pre (xs ! i)));
   (\<Inter>i<length xs. (Par_Post (xs ! i))) \<subseteq> q;
   (\<Union>i<length xs. (Par_Abr (xs ! i))) \<subseteq> a ;
   \<forall>i < length xs.
    \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  Par_Com (xs ! i) sat i [Par_Pre (xs!i), Par_Rely (xs ! i), Par_Guar (xs ! i), Par_Post (xs ! i),Par_Abr (xs ! i)];
    (\<Gamma>,l) \<in> par_cp \<Gamma> (ParallelCom xs) s; (\<Gamma>,l) \<in> par_assum(p, R);
   All_End (last l); not_fault (fst (last l)) F;
   \<forall>i<length xs.\<forall>(c,p,R,G,q,a)\<in> \<Theta>.  Pred_wf i p \<and> Rel_wf i R \<and>  Rel_wf i G \<and> Pred_wf i q \<and>  Pred_wf i a \<longrightarrow> 
    \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat i [p, R, G, q,a]; \<forall>i<length xs. Rel_wf i (Par_Guar(xs!i));  
    \<forall>i<length xs. Pred_wf i p;
    \<forall>i<length xs. Pred_wf i (Par_Post (xs ! i));
    \<forall>i<length xs.  Pred_wf i (Par_Abr (xs ! i))\<rbrakk> \<Longrightarrow> 
                   (throw_program (fst (last l)) \<and> 
                        snd (last l) \<in> (a)) \<or>
                   (skip_program (fst (last l)) \<and>
                        snd (last l) \<in>  q)"
proof-
  assume a0:"xs\<noteq>[]" and 
         a1:"\<forall>i<length xs.  R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Par_Guar (xs ! j)))
                            \<subseteq> (Par_Rely (xs ! i))" and
         a2:"p \<subseteq> (\<Inter>i<length xs. (Par_Pre (xs ! i)))" and
         a3:"(\<Inter>i<length xs. (Par_Post (xs ! i))) \<subseteq> q" and
         a4:" (\<Union>i<length xs. (Par_Abr (xs ! i))) \<subseteq> a " and
         a5:" \<forall>i < length xs.  \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>  Par_Com (xs ! i) sat i 
                                       [Par_Pre (xs!i), Par_Rely (xs ! i), Par_Guar (xs ! i), 
                                        Par_Post (xs ! i),Par_Abr (xs ! i)]" and
         a6:"(\<Gamma>,l) \<in> par_cp  \<Gamma> (ParallelCom xs) s" and
         a7:"(\<Gamma>,l) \<in> par_assum(p, R)"and
         a8:"All_End (last l)" and
         a9:"not_fault (fst (last l)) F" and
         a10:"\<forall>i<length xs.\<forall>(c,p,R,G,q,a)\<in> \<Theta>. 
                 Pred_wf i p \<and> Rel_wf i R \<and>  Rel_wf i G \<and> Pred_wf i q \<and>  Pred_wf i a \<longrightarrow> 
                   \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat i [p, R, G, q,a]" and
        a11:"\<forall>i<length xs. Rel_wf i (Par_Guar(xs!i))" and 
        a12:" \<forall>i<length xs. Pred_wf i p" and 
        a13:"\<forall>i<length xs.  Pred_wf i (Par_Post (xs ! i))" and
        a14:"\<forall>i<length xs.  Pred_wf i (Par_Abr (xs ! i))"
   have length_par_xs:"length (ParallelCom xs) = length xs" unfolding ParallelCom_def  by fastforce   
   moreover have "(ParallelCom xs)\<noteq>[]" using a0 calculation by fastforce
   ultimately have "(\<Gamma>,l) \<in>{(\<Gamma>1,c). \<exists>clist. (length clist)=(length (ParallelCom xs)) \<and> 
             (\<forall>i<length clist. (clist!i) \<in> cpi  i \<Gamma> ((ParallelCom xs)!i) s) \<and> 
             (\<Gamma>,c) \<propto> clist \<and> \<Gamma>1=\<Gamma>}"
     using one a6  by blast 
   then obtain clist where "(length clist)=(length xs) \<and> 
               (\<forall>i<length clist. (clist!i) \<in> cpi  i 
                                                  \<Gamma> ((ParallelCom xs)!i) s) \<and> (\<Gamma>,l) \<propto> clist"
     using length_par_xs ParallelCom_Com by auto
   then have conjoin:"(length clist)=(length xs) \<and> 
               (\<forall>i<length clist. (clist!i) \<in> cpi i  \<Gamma> (Par_Com (xs ! i)) s) \<and> 
                                 (\<Gamma>,l) \<propto> clist"
     using ParallelCom_Com by fastforce
   then have length_xs_clist:"length xs = length clist" by auto   
   have clist_cp:"\<forall>i<length clist. (clist!i) \<in> cpi i \<Gamma> (Par_Com (xs ! i)) s" 
     using conjoin
     by (simp add: length_par_xs)
   have clist_cp_unfold:"\<forall>i<length clist. (\<Gamma>, snd (clist!i)) \<in> cpi  i \<Gamma> (Par_Com (xs ! i)) s"
     using conjoin length_par_xs unfolding conjoin_def same_functions_def by auto     
   have conjoin:"(\<Gamma>,l) \<propto> clist" using conjoin by auto
   have l_not_empty:"l\<noteq>[]" using a6 par_cptn.simps unfolding par_cp_def by fastforce
   then have l_g0:"0<length l" by fastforce  
   then have last_l:"last l = l!((length l) - 1)" by (simp add: last_conv_nth) 
   have "\<forall>i<length clist. (clist!i) \<in> assum_p i (Par_Pre (xs!i),Par_Rely (xs!i))"     
   proof -
   { fix i
     assume i_length:"i<length clist"
     obtain \<Gamma>1 li where clist:"clist!i=(\<Gamma>1,li)" by fastforce    
     then have \<Gamma>eq:"\<Gamma>1=\<Gamma>" 
       using conjoin i_length unfolding conjoin_def same_functions_def by fastforce
     have "(\<Gamma>1,li) \<in> assum_p i (Par_Pre (xs!i),Par_Rely (xs!i))"
     proof-
       have l:"snd (li!0) \<in>  ( (Par_Pre (xs!i)))"
       proof -  
         have snd_l:"snd (\<Gamma>,l) = l" by fastforce       
         have "snd (l!0) \<in> (p)" 
         using a7 unfolding par_assum_def by fastforce         
         also have "snd (l!0) = snd (li!0)"           
           using i_length conjoin l_g0 clist 
           unfolding conjoin_def same_state_def by fastforce
         finally show ?thesis using a2 i_length length_xs_clist
            by auto 
       qed              
       have r:"(\<forall>j. Suc j < length li \<longrightarrow> 
                    \<Gamma>\<turnstile>\<^sub>c(fst (li!j), toSeqState i (snd (li!j)))  \<rightarrow>\<^sub>e 
                       (fst (li!(Suc j)), toSeqState i (snd (li!(Suc j)))) \<longrightarrow>                 
                    (snd(li!j), snd(li!(Suc j))) \<in> Par_Rely (xs!i))"        
         using three[OF a0 a1 a2 a5 length_xs_clist a6 a7 clist_cp conjoin a10 a11 a12 ]  
                i_length conjoin a1 length_xs_clist clist                     
         unfolding assum_def conjoin_def same_length_def  by fastforce 
       then have  a_p1:"(\<Gamma>1,li) \<in>assum_p1 i (Par_Pre (xs!i),Par_Rely (xs!i))"
         using l r \<Gamma>eq unfolding assum_p1_def by fastforce
       moreover have all_wf:"\<forall>j < length (snd (clist ! i)).
                               i < length (snd (snd (snd (clist ! i) ! j)))"
         using  wf_local_vars[OF conjoin i_length _ a6 ] by auto
       moreover have clist_i_ne:"snd (clist ! i)\<noteq>[]"
         using conjoin conjoin_def i_length l_not_empty same_length_def by fastforce
       ultimately show ?thesis using p2
         by (simp add: clist)
     qed 
     then have "clist!i \<in>  assum_p i (Par_Pre (xs ! i), Par_Rely (xs ! i))" using clist by auto            
   } thus ?thesis by auto
 qed
  then have clist_assum:"\<forall>i<length clist. (\<Gamma>, snd (clist!i)) \<in> assum_p i (Par_Pre (xs!i),Par_Rely (xs!i))"
    using conjoin unfolding conjoin_def same_functions_def by auto
  have "\<forall>i<length clist. i< length (snd  s)"
    using wf_local_vars[OF conjoin _ _ a6 ] a1 clist_cp length_xs_clist unfolding cpi_def  wf_state_def
    by fastforce    
  then have clist_com:"\<forall>i<length clist.(\<Gamma>, snd (clist!i)) \<in> 
                         comm_p i (Par_Guar (xs!i),(Par_Post(xs!i),Par_Abr (xs!i))) F"
    apply auto 
    apply (rule assum_p_cpi_in_com_p[where ?s = s and ?\<Theta> = \<Theta>])
    using length_xs_clist a5 a10 clist_cp_unfold clist_assum by auto                    
   have last_clist_eq_l:"\<forall>i<length clist. last (snd (clist!i)) = (snd (clist!i))!((length l) - 1)"
     using conjoin  last_conv_nth l_not_empty 
     unfolding conjoin_def same_length_def
     by (metis length_0_conv snd_eqD) 
   then have last_clist_l:"\<forall>i<length clist. snd (last (snd (clist!i))) = snd (last l)"
     using last_l conjoin l_not_empty unfolding conjoin_def same_state_def same_length_def 
     by simp
   show ?thesis
   proof(cases "skip_program (fst (last l))")
     assume "skip_program (fst (last l))"
     then have ac1:"\<forall>i<length (fst (last l)). fst (last l)!i = Skip"
       unfolding skip_program_def by auto
     have "(\<forall>j<length (fst (last l)). fst (last l) ! j = LanguageCon.com.Skip) \<and> snd (last l) \<in>  q"
     proof -
       {fix j
        assume aj:"j<length (fst (last l))"         
        have "\<forall>i<length clist. snd (last (snd (clist!i))) \<in> Par_Post(xs!i)"
        proof-
          {fix i 
           assume a20:"i<length clist"
           then have snd_last:"snd (last (snd (clist!i))) = snd (last l)" 
             using last_clist_l by fastforce
           have last_clist_not_F:"fst (last (snd (clist!i)))\<notin> Fault ` F"
              using a9 last_clist_l a20 unfolding not_fault_def
              by (metis conjoin conjoin_same_length diff_less l_g0 l_not_empty 
                   last_l same_program_last snd_conv zero_less_one) 
           have "fst (last l) ! i = Skip" 
             using a20 ac1 conjoin_same_length[OF conjoin]
             by (simp add: l_not_empty last_l )                       
           also have "fst (last l) ! i=fst (last (snd (clist!i)))"
             using same_program_last[OF l_not_empty conjoin a20]  by auto
           finally have skip:"fst (last (snd (clist!i))) = Skip" .
           moreover have  comm_pi:"(\<Gamma>, snd (clist!i)) \<in> comm_p i (Par_Guar (xs!i),(Par_Post(xs!i),Par_Abr (xs!i))) F"
             using a20 clist_com by auto
           moreover have "snd (clist ! i) \<noteq> []"
             by (metis (no_types) a20 conjoin conjoin_def l_g0 list.size(3) 
                       not_less0 same_length_def snd_conv)
           moreover have " final_glob_p (last (snd (clist ! i)))"
             using skip unfolding final_glob_p_def by auto  
           moreover have " \<forall>e\<in>Par_Post(xs!i). i < length (snd e)" 
             using a13 unfolding Pred_wf_def
             by (simp add: a20 length_xs_clist)
           moreover have " \<forall>e\<in>Par_Abr(xs!i). i < length (snd e)" 
             using a14 unfolding Pred_wf_def
             by (simp add: a20 length_xs_clist) 
           ultimately have "snd (last (snd (clist!i))) \<in>  Par_Post(xs!i)" 
             using comm_pdest2[OF _ _ _ last_clist_not_F ] by auto 
          }  thus ?thesis by auto 
        qed             
        then have "\<forall>i<length xs. snd (last l) \<in> Par_Post(xs!i)" 
          using last_clist_l length_xs_clist by fastforce        
        moreover have "\<forall>t. (\<forall>i<length xs. t\<in> Par_Post (xs ! i))\<longrightarrow> t\<in> q" using a3
          by fastforce        
        ultimately have "(\<exists>x\<in> q. snd (last l) =  x)" using a0 by blast
        then have "snd (last l) \<in>  q" by fastforce          
        then have "fst (last l) ! j = LanguageCon.com.Skip \<and> snd (last l) \<in> q"
          using aj ac1 by fastforce
        } thus ?thesis
          using All_End_def a8 by blast
     qed      
     thus ?thesis unfolding skip_program_def  by fastforce
   next
     assume a00:"\<not> skip_program (fst (last l))"    
     have skip_throw:
       "\<forall>i<length (fst (last l)). fst (last l)!i = Skip \<or> fst (last l)!i = Throw"
     proof-
     { fix i 
       assume a00:"i<length (fst (last l))"
       have "length (fst (last l)) =  length clist" 
         using conjoin_same_length[OF conjoin] l_not_empty last_l
         by simp
       then have i_length:"i<length clist" using a00 by fastforce
       then have snd_last:"snd (last (snd (clist!i))) = snd (last l)" 
         using last_clist_l by fastforce
       have last_clist_not_F:"fst (last (snd (clist!i)))\<notin> Fault ` F"
         using a9 last_clist_l i_length
         by (metis \<open>length (fst (last l)) = length clist\<close> conjoin 
           l_not_empty not_fault_def same_program_last)
       then have "fst (last (snd (clist!i))) = fst (last l) ! i" 
         using i_length same_program_last [OF l_not_empty conjoin] by fastforce
       moreover have  comm_pi:"(\<Gamma>, snd (clist!i)) \<in> comm_p i (Par_Guar (xs!i),(Par_Post(xs!i),Par_Abr (xs!i))) F"
         using i_length clist_com by auto
       moreover have "snd (clist ! i) \<noteq> []"
         by (metis (no_types) i_length conjoin conjoin_def l_g0 list.size(3) 
                       not_less0 same_length_def snd_conv)
       moreover have " final_glob_p (last (snd (clist ! i)))"
         using a8 a00 snd_last Throw  unfolding All_End_def final1_def unfolding final_glob_p_def
         using calculation(1) by auto  
       moreover have " \<forall>e\<in>Par_Post(xs!i). i < length (snd e)" 
         using a13 unfolding Pred_wf_def
         by (simp add: i_length length_xs_clist)
       moreover have " \<forall>e\<in>Par_Abr(xs!i). i < length (snd e)" 
         using a14 unfolding Pred_wf_def
         by (simp add: i_length length_xs_clist)
       ultimately have "fst (last l) ! i = LanguageCon.com.Skip \<and> snd (last l) \<in> Par_Post(xs!i) \<or> 
                        fst (last l) ! i = LanguageCon.com.Throw \<and> snd (last l) \<in> Par_Abr(xs!i)" 
          using comm_pdest2[OF _ _ _ last_clist_not_F ]
          using snd_last by auto          
     } then show ?thesis by auto
     qed     
     obtain i where a20:"i< length (fst (last l)) \<and>  fst (last l)!i \<noteq> Skip" 
       using a00 unfolding skip_program_def
       by fastforce
     then have last_i_throw:"fst (last l)!i = Throw" 
       using skip_throw by fastforce     
     have "length (fst (last l)) =  length clist" 
       using conjoin_same_length[OF conjoin] l_not_empty last_l
       by simp
     then have i_length:"i<length clist" using a20 by fastforce
     then have snd_last:"snd (last (snd (clist!i))) = snd (last l)" 
       using last_clist_l by fastforce
     have last_clist_not_F:"fst (last (snd (clist!i)))\<notin> Fault ` F"
       using a9 last_clist_l i_length
       by (metis \<open>length (fst (last l)) = length clist\<close> conjoin 
           l_not_empty not_fault_def same_program_last)
     then have "fst (last (snd (clist!i))) = fst (last l) ! i" 
       using i_length same_program_last [OF l_not_empty conjoin] by fastforce          
     then have Throw:"fst (last (snd (clist!i))) = Throw \<or> fst (last (snd (clist!i))) = Stuck \<or>
                     (\<exists>f. fst (last (snd (clist!i))) = Fault f)"
       using last_i_throw by fastforce
     moreover have  comm_pi:"(\<Gamma>, snd (clist!i)) \<in> comm_p i (Par_Guar (xs!i),(Par_Post(xs!i),Par_Abr (xs!i))) F"
       using i_length clist_com by auto
     moreover have "snd (clist ! i) \<noteq> []"
             by (metis (no_types) i_length conjoin conjoin_def l_g0 list.size(3) 
                       not_less0 same_length_def snd_conv)
     moreover have " final_glob_p (last (snd (clist ! i)))"
       using last_i_throw snd_last Throw unfolding final_glob_p_def
       by auto 
     moreover have " \<forall>e\<in>Par_Post(xs!i). i < length (snd e)" 
       using a13 unfolding Pred_wf_def
       by (simp add: i_length length_xs_clist)
     moreover have " \<forall>e\<in>Par_Abr(xs!i). i < length (snd e)" 
       using a14 unfolding Pred_wf_def
       by (simp add: i_length length_xs_clist) 
     ultimately have "snd (last (snd (clist!i))) \<in> Par_Abr(xs!i)" 
        using comm_pdest2[OF _ _ _ last_clist_not_F ]
        using \<open>fst (last (snd (clist ! i))) = fst (last l) ! i\<close> a20 by auto 
     then have "snd (last l)\<in>  Par_Abr(xs!i)" using last_clist_l i_length
       by fastforce
     then have "snd (last l)\<in>  (a)" using a4 a0 i_length length_xs_clist by fastforce
     then have "\<exists>j<length (fst (last l)).
        fst (last l) ! j = LanguageCon.com.Throw \<and> snd (last l) \<in> a"
     using last_i_throw a20 by auto
     thus ?thesis using skip_throw unfolding throw_program_def by auto
   qed 
qed


lemma ParallelEmpty [rule_format]:
  "\<forall>i s. (\<Gamma>,l) \<in> par_cp  \<Gamma> (ParallelCom []) s \<longrightarrow>
  Suc i < length l \<longrightarrow> \<not> (\<Gamma> \<turnstile>\<^sub>p (l!i) \<rightarrow> (l!Suc i))"
apply(induct_tac l)
 apply simp
apply clarify
apply(case_tac list,simp,simp)
apply(case_tac i)
 apply(simp add:par_cp_def ParallelCom_def) 
 apply(erule par_ctranE,simp)
apply(simp add:par_cp_def ParallelCom_def)
apply clarify
apply(erule par_cptn.cases,simp)
 apply simp  
by (metis list.inject list.size(3) not_less0 step_p_pair_elim_cases)

lemma ParallelEmpty2:
  assumes a0:"(\<Gamma>,l) \<in> par_cp  \<Gamma> (ParallelCom []) s" and
         a1: "i < length l" 
  shows "fst (l!i) = []"
proof -
  have paremp:"ParallelCom [] = []" unfolding ParallelCom_def by auto
  then have l0:"l!0 =([],s)" using a0 unfolding par_cp_def by auto
  then have "(\<Gamma>,l) \<in> par_cptn" using a0 unfolding par_cp_def by fastforce
  thus ?thesis using l0 a1
  proof (induct arbitrary: i s) 
    case ParCptnOne thus ?case by auto
  next
    case (ParCptnEnv \<Gamma> P s1 t xs i s)
    thus ?case
    proof -
      have f1: "i < Suc (Suc (length xs))"
        using ParCptnEnv.prems(2) by auto
      have "(P, s1) = ([], s)"
        using ParCptnEnv.prems(1) by auto
      then show ?thesis
        using f1 by (metis (no_types) ParCptnEnv.hyps(3) diff_Suc_1 fst_conv length_Cons less_Suc_eq_0_disj nth_Cons')
    qed    
  next
    case (ParCptnComp \<Gamma> P s1 Q t xs)   
    have "(\<Gamma>, (P,s1)#(Q, t) # xs) \<in> par_cp  \<Gamma> (ParallelCom []) s1" 
        using ParCptnComp(4) ParCptnComp(1) step_p_elim_cases by fastforce
      then have "\<not> \<Gamma>\<turnstile>\<^sub>p (P, s1) \<rightarrow> (Q, t)" using ParallelEmpty ParCptnComp by fastforce
    thus ?case using ParCptnComp by auto
  qed
qed  



lemma Rel_wf_st:assumes a0:"\<forall>i<length xs. Rel_wf_st (length xs) (Par_Guar (xs ! i))"
  shows" \<forall>i<length xs. Rel_wf i (Par_Guar (xs ! i))"  
proof-                      
  {fix i x y
    assume a00:"i<length xs" and
          a01:"(x,y)\<in>Par_Guar (xs!i)"
    then have len:"length xs \<le> length (snd x) \<and> length (snd x) = length (snd y)"
      using a0 unfolding Rel_wf_st_def split_beta by fastforce
    then have "( i < length (snd x)) \<and> i < length (snd y)" using a00 len by auto
  }  thus ?thesis unfolding Rel_wf_def by auto
qed

lemma parallel_sound: 
  "\<forall>i<length xs.
       R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Par_Guar (xs ! j)))
       \<subseteq> (Par_Rely (xs ! i)) \<Longrightarrow>
    (\<Union>j<length xs. (Par_Guar (xs ! j))) \<subseteq> G \<Longrightarrow>
    p \<subseteq> (\<Inter>i<length xs. (Par_Pre (xs ! i))) \<Longrightarrow>
    (\<Inter>i<length xs. (Par_Post (xs ! i))) \<subseteq> q \<Longrightarrow>
    (\<Union>i<length xs. (Par_Abr (xs ! i))) \<subseteq> a \<Longrightarrow> 
    \<forall>x\<in>p. length xs = length (snd x) \<Longrightarrow>
     \<forall>i<length xs. \<forall>x\<in> (Par_Post (xs!i)). length (snd x) = length xs \<Longrightarrow>
     \<forall>i<length xs. \<forall>x\<in> (Par_Abr (xs!i)). length (snd x) = length xs \<Longrightarrow>
 \<forall>i<length xs. Rel_wf_st (length xs) (Par_Guar (xs ! i)) \<Longrightarrow>
    \<forall>i<length xs.
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> Par_Com (xs !i) sat i [Par_Pre (xs !i), Par_Rely (xs ! i), Par_Guar (xs ! i), Par_Post (xs ! i),Par_Abr (xs ! i)] \<Longrightarrow>
  \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> ParallelCom xs SAT [p, R, G, q,a]
  "
proof -
  assume 
  a0:"\<forall>i<length xs.
       R \<union> (\<Union>j\<in>{j. j < length xs \<and> j \<noteq> i}. (Par_Guar (xs ! j)))
       \<subseteq> (Par_Rely (xs ! i))" and
   a1:"(\<Union>j<length xs. (Par_Guar (xs ! j))) \<subseteq> G" and
   a2:"p \<subseteq> (\<Inter>i<length xs. (Par_Pre (xs ! i)))" and
   a3:"(\<Inter>i<length xs. (Par_Post (xs ! i))) \<subseteq> q" and
   a4:" (\<Union>i<length xs. Par_Abr (xs ! i)) \<subseteq> a" and
   a5:"\<forall>i<length xs. \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub>
      Par_Com
       (xs ! i) sat i [Par_Pre (xs ! i),Par_Rely (xs ! i), Par_Guar (xs ! i), Par_Post (xs ! i),Par_Abr (xs ! i)]" and
   a6:"\<forall>x\<in>p. length xs = length (snd x)" and
     a7:"\<forall>i<length xs. \<forall>x\<in>Par_Post (xs ! i). length (snd x) = length xs" and
     a8:" \<forall>i<length xs. \<forall>x\<in>Par_Abr (xs ! i). length (snd x) = length xs" and 
     a9:" \<forall>i<length xs. Rel_wf_st (length xs) (Par_Guar (xs ! i))" 
  { 
    assume a00:"\<forall>i<length (ParallelCom xs). 
                    \<forall>(c,p,R,G,q,a)\<in> \<Theta>. Pred_wf i p \<and> Rel_wf i R \<and>  Rel_wf i G \<and> 
                                       Pred_wf i q \<and>  Pred_wf i a \<longrightarrow>
                     (\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (Call c) sat i [p, R, G, q,a])"    
    have p_wf:"\<forall>i<length xs. Pred_wf i p" using a6 unfolding Pred_wf_def by auto
    have q_wf:"\<forall>i<length xs. Pred_wf i (Par_Post (xs!i))" using a7 unfolding Pred_wf_def 
      by auto
    have a_wf:"\<forall>i<length xs. Pred_wf i (Par_Abr (xs!i))" using a8 unfolding Pred_wf_def 
      by auto
    have a9:" \<forall>i<length xs. Rel_wf i (Par_Guar (xs ! i))"
      using a9 Rel_wf_st by auto
     { fix s l 
       assume a10: "(\<Gamma>,l) \<in> par_cp  \<Gamma> (ParallelCom xs) s \<and> (\<Gamma>,l) \<in> par_assum(p, R)"       
       then have c_par_cp:"(\<Gamma>,l) \<in> par_cp  \<Gamma> (ParallelCom xs) s" by auto
       have c_par_assum: "(\<Gamma>,l) \<in> par_assum(p, R)" using a10 by auto
       have lengthxscom:"(length (ParallelCom xs)) = length xs"
         unfolding ParallelCom_def by auto
       { fix i         
         {
            assume a30:"Suc i<length l"  and
                   a31: "\<Gamma>\<turnstile>\<^sub>p(l!i)  \<rightarrow> (l!(Suc i))"                   
            have xs_not_empty:"xs\<noteq>[]" 
            proof -
            {
              assume "xs = []"
              then have "\<not> (\<Gamma> \<turnstile>\<^sub>p (l!i) \<rightarrow> (l!Suc i))" 
                using a30 a10 ParallelEmpty by fastforce
              then have False using a31 by auto
            } thus ?thesis by auto
            qed            
            then have "(snd(l!i), snd(l!(Suc i))) \<in>  G"
            using four[OF xs_not_empty a0 a1 a2 a5 c_par_cp c_par_assum a30 a31 a00[simplified lengthxscom] a9 p_wf ] by blast
            
         } then have "Suc i<length l \<longrightarrow> 
                     \<Gamma>\<turnstile>\<^sub>p(l!i)  \<rightarrow> (l!(Suc i)) \<longrightarrow>                      
                     (snd(l!i), snd(l!(Suc i))) \<in> G " by auto 
            note l = this
         { assume a30:"All_End (last l)" and not_fault:"not_fault (fst (last l)) F"
           then have xs_not_empty:"xs\<noteq>[]" 
           proof - 
           { assume xs_emp:"xs=[]"
             have lenl:"0<length l" using a10 unfolding par_cp_def using par_cptn.simps by fastforce
             then have "(length l) - 1 < length l" by fastforce
             then have "fst(l!((length l) - 1)) = []" using ParallelEmpty2 a10 xs_emp by fastforce
             then have False using a30 lenl unfolding All_End_def
               by (simp add: last_conv_nth )              
           } thus ?thesis by auto
           qed
           then have "throw_program (fst (last l)) \<and> snd (last l) \<in> a \<or>
                      skip_program (fst (last l)) \<and> snd (last l) \<in> q"
             using five[OF xs_not_empty a0 a2 a3 a4 a5 c_par_cp c_par_assum 
               a30 not_fault a00[simplified lengthxscom] a9 p_wf q_wf a_wf] by blast
         } then have "All_End (last l) \<longrightarrow> not_fault (fst (last l)) F \<longrightarrow>
                      throw_program (fst (last l)) \<and> snd (last l) \<in> a \<or>
                      skip_program (fst (last l)) \<and> snd (last l) \<in> q" by auto 
           note res1 = conjI[OF l this] 
       }
       then have  "(\<Gamma>,l) \<in> par_comm(G, (q,a)) F" unfolding par_comm_def by auto       
     } 
     then have "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (ParallelCom xs) SAT [p, R, G, q,a]" 
       unfolding par_com_validity_def par_cp_def by fastforce
  } thus ?thesis using par_com_cvalidity_def by fastforce
qed

theorem  
 par_rgsound:"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> Ps SAT [p, R, G, q,a] \<Longrightarrow>
  \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> (ParallelCom Ps) SAT [p, R, G, q,a]"
proof (induction rule:par_rghoare.induct)
  case (Parallel  xs R G  p q a \<Gamma> \<Theta> F)
  then have "\<forall>i<length xs. \<Gamma>,(seq_proc_spec i \<Theta>) \<Turnstile>\<^bsub>/F\<^esub> Par_Com (xs ! i) sat [Seq_pred i (Par_Pre (xs ! i)), 
                                                        Seq_rel i (Par_Rely (xs ! i)), 
                                                        Seq_rel i (Par_Guar (xs ! i)), 
                                                        Seq_pred i (Par_Post (xs ! i)),
                                                        Seq_pred i (Par_Abr (xs ! i))]"
    using localRG_sound com_cnvalid_to_cvalid by fast
  moreover have  "\<forall>i<length xs. \<forall>x\<in> (Par_Pre(xs!i)). i < length (snd x)" using Parallel(4) by auto
  ultimately have "\<forall>i<length xs.
       \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> Par_Com (xs !i) sat i [Par_Pre (xs !i), Par_Rely (xs ! i), Par_Guar (xs ! i), Par_Post (xs ! i),Par_Abr (xs ! i)]"    
    using cvalidity_eq_cvalidityp by fastforce
  moreover have  "\<forall>x\<in>p. length xs = length (snd x)" using Parallel(4,7,1) by fastforce    
  ultimately show ?case using Parallel parallel_sound[of xs R G p q a \<Gamma> \<Theta> F] 
      by fast
  qed

lemma Conseq':"\<forall>s. s\<in>p \<longrightarrow>
              (\<exists>p' q' a' R' G'. 
                (\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [(p' Z), (R' Z), (G' Z), (q' Z),(a' Z)]) \<and>
                   (\<exists> Z. s\<in>p' Z \<and> (q' Z \<subseteq> q) \<and> (a' Z \<subseteq> a) \<and> (G' Z \<subseteq> G) \<and> (R \<subseteq> R' Z)))
              \<Longrightarrow>
              \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q,a]"
  apply (rule Conseq)
  by (meson order_refl)

lemma conseq:"\<lbrakk>\<forall>Z. \<Gamma>,\<Theta>'\<turnstile>\<^bsub>/F\<^esub> P sat [(p' Z), (R' Z), (G' Z), (q' Z),(a' Z)]; \<Theta>' \<subseteq> \<Theta> ;
              \<forall>s. s \<in> p \<longrightarrow> (\<exists> Z. s\<in>p' Z \<and> (q' Z \<subseteq> q) \<and> (a' Z \<subseteq> a) \<and> (G' Z \<subseteq> G) \<and> (R \<subseteq> R' Z))\<rbrakk>
              \<Longrightarrow>
               \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q,a]"
by (rule Conseq) (meson order_refl)

lemma conseqPrePost[trans]:
 "\<Gamma>,\<Theta>'\<turnstile>\<^bsub>/F\<^esub> P sat [p', R', G', q',a'] \<Longrightarrow> \<Theta>' \<subseteq> \<Theta> \<Longrightarrow>
  p\<subseteq>p' \<Longrightarrow> q' \<subseteq> q \<Longrightarrow> a' \<subseteq> a \<Longrightarrow> G' \<subseteq> G \<Longrightarrow> R \<subseteq> R' \<Longrightarrow> 
  \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q,a]"  
by (rule conseq) auto

lemma conseqPre[trans]:
 "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p', R, G, q,a] \<Longrightarrow>
  p\<subseteq>p' \<Longrightarrow>
  \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q,a]"
by (rule conseq) auto

lemma conseqPost[trans]:
 "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q',a'] \<Longrightarrow>
  q'\<subseteq>q \<Longrightarrow>  a'\<subseteq>a \<Longrightarrow>
  \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q,a]"
  by (rule conseq) auto
  
lemma shows x:"\<exists>(sa'::nat set). (\<forall>x. (x\<in> sa) = ((to_nat x) \<in> sa'))"
  by (metis (mono_tags, hide_lams) from_nat_to_nat imageE image_eqI)


lemma not_empty_set_countable: 
  assumes a0:"sa\<noteq>({}::('a::countable) set)" 
  shows "{i. ((\<lambda>i. i\<in> sa) o from_nat) i}\<noteq>{}"
  by (metis (full_types) Collect_empty_eq_bot assms comp_apply empty_def equals0I from_nat_to_nat)

lemma eq_set_countable:"(\<Inter>i\<in>{i. ((\<lambda>i. i\<in> sa) o from_nat) i}. (q o from_nat) i) = ((\<Inter>i\<in>sa. q i))"     
  apply auto
  by (metis (no_types) from_nat_to_nat)
  
lemma conj_inter_countable[trans]: 
  assumes a0:"sa\<noteq>({}::('a::countable) set)" and
          a1:"\<forall>i\<in>sa. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G, q i,a]"
  shows"\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G,(\<Inter>i\<in>sa. q i),a]"  
proof-
  have "\<forall>i\<in>{i. ((\<lambda>i. i\<in> sa) o from_nat) i}. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G,(q o from_nat) i,a]"    
    using a1 by auto
  then have "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P sat [p, R, G,\<Inter>i\<in>{i. ((\<lambda>i. i\<in> sa) o from_nat) i}. (q o from_nat) i,a]"
    using Conj_Inter[OF not_empty_set_countable[OF a0]]   by auto    
  thus ?thesis  using eq_set_countable
    by metis    
qed
  
lemma all_Post[trans]:
  assumes a0:"\<forall>p_n::('a::countable). \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> C sat [P, R, G, Q p_n, Qa]" 
  shows"\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> C sat [P, R, G,{s. \<forall>p_n. s\<in>Q p_n},Qa]"      
proof-  
  have "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> C sat [P, R, G,(\<Inter>p_n. Q  p_n),Qa]"
     using a0 conj_inter_countable[of UNIV]  by auto 
  moreover have s1:"\<forall>P. {s. \<forall>p_n. s\<in>P p_n} = (\<Inter>p_n. P p_n)"
    by auto   
  ultimately show ?thesis
   by (simp add: s1)
qed    
  
lemma all_Pre[trans]:
  assumes a0:"\<forall>p_n. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> C sat [P p_n, R, G, Q, Qa]" 
  shows"\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> C sat [{s. \<forall>p_n. s\<in>P p_n}, R, G,Q,Qa]"
proof-
   {fix p_n     
    have "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> C sat [{s. \<forall>p_n. s\<in>P p_n}, R, G,Q,Qa]" 
    proof-
      have "{v. \<forall>n. v \<in> P n} \<subseteq> P p_n" by force
      then show ?thesis by (meson a0 LocalRG_HoareDef.conseqPrePost subset_eq)
    qed
  } thus ?thesis by auto 
qed
    
lemma Pre_Post_all:
  assumes a0:"\<forall>p_n::('a::countable). \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> C sat [P p_n, R, G, Q p_n, Qa]" 
  shows"\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> C sat [{s. \<forall>p_n. s\<in>P p_n}, R, G,{s. \<forall>p_n. s\<in>Q p_n},Qa]"    
proof-
  {fix p_n
     
    have "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> C sat [{s. \<forall>p_n. s\<in>P p_n}, R, G,Q p_n,Qa]" 
    proof-
      have "{v. \<forall>n. v \<in> P n} \<subseteq> P p_n" by force
      then show ?thesis by (meson a0 LocalRG_HoareDef.conseqPrePost subset_eq)
    qed
  }
  then have f3:"\<forall>p_n. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> C sat [{s. \<forall>p_n. s\<in>P p_n}, R, G,Q p_n,Qa]"
    by auto
  then have "\<forall>p_n. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> C sat [{s. \<forall>p_n. s\<in>P p_n}, R, G,{s. \<forall>p_n. s\<in>Q p_n},Qa]"    
    using all_Post by auto
  moreover have s1:"\<forall>P. {s. \<forall>p_n. s\<in>P p_n} = (\<Inter>p_n. P p_n)"
    by auto   
  ultimately show ?thesis
   by (simp add: s1)
qed  
  
  
inductive_cases hoare_elim_skip_cases [cases set]:
"\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> Skip sat [p, R, G, q,a]"



(* abbreviation 
 "stepc_rtrancl" :: "[('s,'p,'f,'e) body,('s,'p,'f) config,('s,'p,'f) config] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c (_ \<rightarrow>\<^sup>*/ _)" [81,81,81] 100)
 where                                
  "\<Gamma>\<turnstile>\<^sub>c cf0 \<rightarrow>\<^sup>* cf1 \<equiv> ((CONST stepc \<Gamma>))\<^sup>*\<^sup>* cf0 cf1" *)


end

