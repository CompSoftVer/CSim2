theory ComputationConGlob imports "ComputationCon"
begin
section \<open>Auxiliary lemmas\<close>

lemma eq_list_i:
  assumes a0:"length ba = length b" and a1:"\<forall>j. j \<noteq> i \<longrightarrow> ba ! j = b ! j" and 
          a3:"i < length b" 
        shows " take i b @ drop (Suc i) b = take i ba @ drop (Suc i) ba"
proof-
  have "b=  take i b @ b!i # drop (Suc i) b" and "ba =  take i ba @ ba!i # drop (Suc i) ba"
    using  a0 a3 by (auto simp add: id_take_nth_drop) 
  then have  "\<forall>j<i. take i b = take i ba" using a0 a1 a3
    by (metis less_imp_le_nat less_irrefl_nat nth_take_lemma)
  moreover have  "\<forall>j< length ( drop (Suc i) ba).  drop (Suc i) b!j = drop (Suc i) ba!j"
    using a0 a1 a3
    by simp
  ultimately show ?thesis using a0 a3
    by (metis append_Nil append_eq_conv_conj length_drop linorder_neqE_nat list.size(3) not_less_zero nth_equalityI)
qed   

section \<open>Computation: @{text "\<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sub>i\<^sub>c\<^sub>e  (c', s')"}\<close>

type_synonym ('g,'l) par_state = "('g \<times> 'l list)"
type_synonym ('g,'l,'p,'f,'e) gconf = "('g \<times> 'l,'p,'f,'e)com  \<times> ('g,'l)par_state"
type_synonym ('g,'l,'p,'f,'e) gconfs = "('g\<times>'l,'p,'f,'e) body \<times> (('g,'l,'p,'f,'e) gconf) list"
type_synonym ('s) tran = "'s \<times> 's"
type_synonym ('s1,'s2) rel = "('s1 \<times> 's2) set"


definition toParState::"nat \<Rightarrow> ('g\<times>'l)\<times>('l list) \<Rightarrow>   ('g,'l)par_state"
  where "toParState i s \<equiv> let ((g,l),ls) = s in
             (g, (take i ls)@ (l#(drop i ls)))"

lemma toPar_li:"i \<le> length ls  \<Longrightarrow>
       (g',ls') = toParState i ((g,l),ls) \<Longrightarrow>
       ls' ! i = l"
  unfolding toParState_def 
  by (auto, metis (no_types) length_take min.absorb2 nth_append_length)

lemma toPar_gi:"
       (g',ls') = toParState i ((g,l),ls) \<Longrightarrow>
       g' = g"
  unfolding toParState_def Let_def by auto

lemma toPar_ljlti:assumes a0:"i \<le> length ls" and a1:"j< i" and
       a2:"(g',ls') = toParState i ((g,l),ls)"
     shows" ls' ! j = ls!j"
proof -
  have "\<forall>as. take i as = take i ls \<or> ls' \<noteq> as"
    using a2 a0 
    unfolding toParState_def by (simp add: append_eq_conv_conj min.absorb2)
  then show ?thesis
    using a2
    by (metis a1 nth_take)
qed 


lemma toPar_ljgti:assumes a0:"i \<le> length ls" and a1:"j > i" and a1': "j< length ls'" and
       a2:"(g',ls') = toParState i ((g,l),ls)"
     shows" ls' ! j = ls!(j-1)" 
proof-  
  have ls':"ls' = take i ls @ l # drop i ls" using a2 unfolding toParState_def by auto
  then have "length ls' = length ls+1"
    by auto
  have j:"j < Suc (min (length ls) i + length ls - i)"
    using a0 a1 a1' a2 unfolding toParState_def by auto  
  moreover { assume "(length ls) \<le> i + length ls - i"    
    then have ?thesis using ls' a0 a1 ls'
      by (auto simp add: min.absorb2 nth_append)
  }
  moreover
  {assume "(length ls) > i + length ls - i"    
    then have ?thesis using ls' a0 a1 ls'
      using diff_add_inverse min.strict_order_iff by auto
  }
  ultimately show ?thesis by auto
qed 

lemma len_toParState:"length (snd (toParState i s )) = length (snd s) +1"
  unfolding toParState_def Let_def split_beta
  by simp

definition toSeqState::"nat \<Rightarrow>  ('g,'l)par_state \<Rightarrow> ('g\<times>'l)\<times>('l list)"
  where "toSeqState i s \<equiv> let (g,ls) = s in ((g,ls!i), take i ls @ drop (i+1) ls)"

lemma len_toSeqState:"i<length (snd s) \<Longrightarrow> length (snd (toSeqState i s)) = length (snd s) -1"
  unfolding toSeqState_def Let_def split_beta
  by simp

lemma i_less_toSeq:"i<length (snd (toSeqState i s)) \<Longrightarrow> i<length (snd s)"
  unfolding toSeqState_def Let_def split_beta
  by (metis Suc_eq_plus1 append_Nil2 drop_all 
       less_imp_le_nat not_le_imp_less not_less_eq snd_conv take_all)

lemma Par2Seq0:"i\<le>length ls \<Longrightarrow> toSeqState i (toParState i ((g,l),ls)) = ((g,l),ls)"
proof (induct  rule: rev_induct)
  case Nil
  then show ?case  unfolding toSeqState_def toParState_def
    by (simp add: split_beta)
next
  case (snoc x xs)
  then show ?case unfolding toSeqState_def toParState_def Let_def
  proof(auto simp add: split_beta)
    assume "i \<le> Suc (length xs)"    
    then show "(take i xs @ take (i - length xs) [x] @ l # drop i xs @ drop (i - length xs) [x]) ! i = l"      
      by (metis append_assoc   length_append_singleton 
          length_take min.absorb2 nth_append_length take_append)
  next
    assume a0:"i \<le> length xs \<Longrightarrow>
     (take i xs @ l # drop i xs) ! i = l \<and>
     take i xs @ drop (Suc i - min (length xs) i) (l # drop i xs) = xs" and
        a1:"i \<le> Suc (length xs)"
    show "take i xs @
        take (min (i - min (length xs) i) (i - length xs)) [x] @
        drop (Suc i - (min (length xs) i + min (Suc 0) (i - length xs)))
         (l # drop i xs @ drop (i - length xs) [x]) =
        xs @ [x]"
      using a0 a1
      by (simp add: Suc_diff_le drop_Cons' min_def not_less_eq_eq)       
  qed
qed

lemma Par2Seq0f:"i\<le>length (snd s) \<Longrightarrow> toSeqState i (toParState i s) = s"
  using Par2Seq0
  by (metis snd_conv surj_pair) 

lemma Par2Seq1:"i=length ls \<Longrightarrow> toSeqState i (toParState i (g,ls)) = (g,ls)"
  unfolding toSeqState_def toParState_def Let_def split_beta
  by auto

lemma Par2Seq1f:"i=length (snd s) \<Longrightarrow> toSeqState i (toParState i s) = s"
  using Par2Seq1 
  by (metis snd_conv surj_pair) 

lemma Par2Seq:"i\<le>length ls \<Longrightarrow> toSeqState i (toParState i (g,ls)) = (g,ls)"
  using Par2Seq0 
  by (metis surj_pair)

lemma len_toParState_list:"(g',ls') = toParState i ((g,l),ls) \<Longrightarrow> length ls' = length ls +1"
  unfolding toParState_def by auto

lemma len_toSeqState_list:"i<length ls \<Longrightarrow> ((g',l),ls') = toSeqState i (g,ls) \<Longrightarrow> length ls = length ls' +1"
  unfolding toSeqState_def
  by auto

lemma Seq2Par:"i<length ls \<Longrightarrow> toParState i (toSeqState i (g,ls)) = (g,ls)"
proof (induct  rule: rev_induct)
  case Nil
  then show ?case unfolding toSeqState_def toParState_def Let_def
    by auto    
next
  case (snoc x xs)
  then show ?case unfolding toSeqState_def toParState_def Let_def 
    apply (auto simp add: split_beta)
    by (metis butlast_snoc drop_append id_take_nth_drop snoc.prems take_butlast)    
qed


(* lemma assumes a0:"i<length sl" and
       a1:"length (snd (toParState (toSeqState i (sg, sl)) i)) =
       length (snd (toParState (toSeqState i (sg', sl')) i))"
     shows "length sl = length sl'"
proof-
  have "toParState (toSeqState i (sg, sl)) i = (sg, sl)"
    using a0
    by (simp add: Seq2Par)
qed *)
 
(* typedef ('g,'l) global_s = "{(i,g::('g\<times>'l)\<times>('l list)).  i \<le> length (snd g)  \<and> (\<exists>g'. g' = toParState i g)}"
  unfolding toParState_def
  by auto *)

typedef ('g,'l) global_s = "{(i,g::('g\<times>'l)\<times>('l list)).  i \<le> length (snd g)  \<and> (\<exists>g'. g' = toParState i g)}"
  unfolding toParState_def
  by auto


typedef ('g,'l) global_s1 = "{(g'::('g\<times>'l list)).  (\<exists>i g. i \<le> length (snd g')  \<and> (g' = toParState i g))}"
  unfolding toParState_def
  by auto

setup_lifting type_definition_global_s 

lift_definition global_s_of_local::"(nat\<times>('g\<times>'l)\<times>('l list)) \<Rightarrow> ('g,'l) global_s"
  is "\<lambda>l. (((fst l) mod (length (snd (snd l)) +1), snd l))"
  by auto


(*
definition global_s_of_local::"(nat\<times>('g\<times>'l)\<times>('l list)) \<Rightarrow> ('g,'l) global_s"
  where "global_s_of_local l \<equiv> Abs_global_s (((fst l) mod length (snd (snd l)), snd l))"
 *)
definition transfer_global_s ::"(nat\<times>('g\<times>'l)\<times>('l list)) \<Rightarrow>('g,'l) global_s \<Rightarrow> bool"
  where "transfer_global_s l g \<equiv> g = global_s_of_local l"

print_theorems


typedef ('g,'l) type_global = "{g::('g,'l)par_state. \<forall>i<length (snd g). (\<exists>g'. g = toParState i g')}"
  unfolding toParState_def Let_def split_beta 
  by fastforce

print_theorems 

thm Abs_type_global_inject Rep_type_global Abs_type_global_inverse Rep_type_global_inverse

term Rep_type_global 
term Abs_type_global


definition toSeqCptn:: "nat \<Rightarrow> (('g,'l,'p,'f,'e) gconf list) \<Rightarrow> ('g, 'l,  'p,'f,'e) config_gs list"
  where "toSeqCptn p cpt \<equiv>                                                                
     map (\<lambda>cfg. (fst cfg, toSeqState p (snd cfg))) cpt
"

lemma toSeqCptn_simp:"toSeqCptn i (x#xs) = (fst x, toSeqState i (snd x)) # (toSeqCptn i xs)"
  by (simp add: toSeqCptn_def)

lemma toSeqCptn_j:"j<length cpt \<Longrightarrow> (toSeqCptn p cpt)!j = (fst (cpt!j), toSeqState p (snd (cpt!j)))"
  unfolding toSeqCptn_def by auto


definition toParCptn::"nat \<Rightarrow> ('g, 'l,  'p,'f,'e) config_gs list \<Rightarrow> (('g,'l,'p,'f,'e) gconf list)"
  where "toParCptn p cpt \<equiv>
   map (\<lambda>cfg. (fst cfg, toParState p (snd cfg))) cpt
"

lemma toParCptn_simp:"toParCptn i (x#xs) = (fst x, toParState i (snd x)) # (toParCptn i xs)"
  by (simp add: toParCptn_def)

lemma toParCptn_j:"j<length cpt \<Longrightarrow> (toParCptn p cpt)!j = (fst (cpt!j), toParState p (snd (cpt!j)))"
  unfolding toParCptn_def by auto

definition Par_pred::"nat \<Rightarrow> (('g,'l) c_state)  set  \<Rightarrow> (('g,'l) par_state set)"
  where "Par_pred i p \<equiv> (toParState i) ` p"

definition Par_rel::"nat \<Rightarrow> (('g1,'l1) c_state, ('g2,'l2) c_state) rel  \<Rightarrow> 
                      (('g1,'l1) par_state, ('g2,'l2) par_state) rel"
  where "Par_rel i r \<equiv> (\<lambda>(x,y). ((toParState i x), (toParState i y))) ` r"

definition Seq_pred::"nat \<Rightarrow> (('g,'l) par_state set) \<Rightarrow> (('g,'l) c_state)  set"
  where "Seq_pred i p \<equiv> (toSeqState i) ` p"

definition Seq_rel::"nat \<Rightarrow> (('g1,'l1) par_state, ('g2,'l2) par_state) rel \<Rightarrow> (('g1,'l1) c_state, ('g2,'l2) c_state) rel"
  where "Seq_rel i r \<equiv> (\<lambda>(x,y). ((toSeqState i x), (toSeqState i y))) ` r"

lemma Seq_Par_pred_ID:"\<forall>s\<in>p. i\<le>length (snd s) \<Longrightarrow> Seq_pred i (Par_pred i p) = p "
  unfolding Seq_pred_def Par_pred_def apply auto
  apply (simp add: Ball_def_raw Par2Seq0)
  by (metis Par2Seq0 rev_image_eqI snd_conv)

lemma Par_Seq_pred_ID:"\<forall>s\<in>p. i<length (snd s) \<Longrightarrow> Par_pred i (Seq_pred i p) = p "
  unfolding Seq_pred_def Par_pred_def apply auto
  apply (metis Seq2Par snd_conv)
  by (metis Seq2Par image_eqI snd_conv)

lemma Seq_Par_rel_ID:"\<forall>(x,y)\<in>(r::((('a,'b) c_state ) tran) set). 
                     i\<le>length (snd x) \<and> i\<le>length (snd y) \<Longrightarrow> 
                  Seq_rel i (Par_rel i r) =r"
  unfolding Seq_rel_def Par_rel_def split_beta image_def apply auto
  by (metis Par2Seq0 fst_conv  prod.exhaust_sel snd_conv)+

   


lemma Par_Seq_rel_ID:"\<forall>(x,y)\<in>(r::((('a,'b) par_state) tran) set).
                      i<length (snd x) \<and>  i<length (snd y) \<Longrightarrow> 
                  Par_rel i (Seq_rel i r) =r"
  unfolding Seq_rel_def Par_rel_def split_beta image_def apply auto
   apply (metis Seq2Par fst_conv snd_conv)
  by (metis Seq2Par fst_conv  prod.exhaust_sel snd_conv)   



lemma eq_toParSeqCptn:
   "\<forall>j<length ls. i< length (snd (snd (ls!j))) \<Longrightarrow>
        toParCptn i (toSeqCptn i ls) = ls"
  unfolding toParCptn_def toSeqCptn_def
  apply (rule nth_equalityI, auto) using Seq2Par
  by (metis Seq2Par prod.collapse)
                          

lemma eq_toSeqParCptn:
   "\<forall>j<length ls.  i\<le> length (snd (snd (ls!j))) \<Longrightarrow>
        toSeqCptn i (toParCptn i ls) = ls"
  unfolding toParCptn_def toSeqCptn_def
  apply (rule nth_equalityI, auto) using Par2Seq
  by (metis prod.exhaust_sel)



inductive
 "step_cei"::"[('g\<times>'l,'p,'f,'e) body,nat,('g, 'l, 'p,'f,'e) gconf,('g, 'l, 'p,'f,'e) gconf] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c\<^sub>_ (_ \<rightarrow>\<^sub>c\<^sub>e/ _)" [81,81,81,81] 100)  
  for \<Gamma>::"('g\<times>'l,'p,'f,'e) body"
  where
c_stepi: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c,sg) \<rightarrow>\<^sub>c\<^sub>e (c',sg')\<rbrakk> \<Longrightarrow>
          \<Gamma>\<turnstile>\<^sub>c\<^sub>i (c,toParState i sg ) \<rightarrow>\<^sub>c\<^sub>e (c', toParState i sg')"
                                              
inductive_cases step_cei:
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>i cfg \<rightarrow>\<^sub>c\<^sub>e cfg'"

inductive_set cptni :: "(nat\<times>('g,'l,'p,'f,'e) gconfs) set"
where
  CptnOnei: " (i,\<Gamma>, [(P,s)]) \<in> cptni"
| Cptni: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c\<^sub>i(P,s) \<rightarrow>\<^sub>c\<^sub>e (Q,t); (i,\<Gamma>,(Q, t)#xs) \<in> cptni \<rbrakk> \<Longrightarrow>
             (i,\<Gamma>,(P,s)#(Q,t)#xs) \<in> cptni"

inductive_cases cptni_cases:
"(i,\<Gamma>, [(P,s)]) \<in> cptni"
"(i,\<Gamma>,(P,s)#(Q,t)#xs) \<in> cptni"

lemma step_cei_ce: assumes a0:"i<length (snd s)" and
              a1:"\<Gamma>\<turnstile>\<^sub>c\<^sub>i(P,s) \<rightarrow>\<^sub>c\<^sub>e (Q,t)"
  shows "\<Gamma>\<turnstile>\<^sub>c(P,toSeqState i s) \<rightarrow>\<^sub>c\<^sub>e (Q,toSeqState i t)"
proof-
  obtain ss st where ce:"\<Gamma>\<turnstile>\<^sub>c(P,ss) \<rightarrow>\<^sub>c\<^sub>e (Q,st)" and 
                  s1:"s=toParState i ss" and
                  s2:"t=toParState i st"
    by (auto intro:step_cei[OF a1])  
  then have "length (snd s) = length (snd ss) + 1" 
    using  s1 a0 len_toParState_list[of "fst s" "snd s" _ "fst (fst ss)" "snd (fst ss)" "snd ss"]
    by auto
  then have len_i:"i\<le> length (snd ss)"
    using a0 by linarith 
  show ?thesis
    by (metis Par2Seq0 ce ce_eq_length len_i prod.exhaust_sel s1 s2)
qed


lemma step_cei_normal_normal_same_len:
  assumes  a0:"\<Gamma>\<turnstile>\<^sub>c\<^sub>i(P, s) \<rightarrow>\<^sub>c\<^sub>e (Q,t)"  
  shows "length (snd s) = length (snd t)"
proof-
  obtain ssj ssj1 where "s = toParState i ssj" and "t = toParState i ssj1" and
                                 "\<Gamma>\<turnstile>\<^sub>c (P,ssj) \<rightarrow>\<^sub>c\<^sub>e (Q,ssj1)"
    using  step_cei.simps a0 by blast  
  moreover  have "length (snd ssj) = length (snd ssj1)"
    using calculation ce_eq_length by blast   
  ultimately show ?thesis  
    by (metis  eq_snd_iff len_toParState_list)
qed


lemma step_ce_to_step_cei2:
  assumes a0:"i<length (snd s)"  and
          a2:"length (snd s) = length (snd t)" and
          a1:"\<Gamma>\<turnstile>\<^sub>c(P,toSeqState i s) \<rightarrow>\<^sub>c\<^sub>e (Q,toSeqState i t)"
        shows "\<Gamma>\<turnstile>\<^sub>c\<^sub>i(P, s) \<rightarrow>\<^sub>c\<^sub>e (Q,t)"
 using c_stepi[OF a1, of i] using a0  a1  a2
  by (metis Seq2Par prod.exhaust_sel)


lemma same_local_sublist_toSeq_State: 
  assumes a0:"(\<forall>j\<noteq>i. (snd s)!j = (snd t)!j)" and a1:"length (snd s) = length (snd t)" and    
          a2:" i<length (snd s)" 
        shows  "snd(toSeqState i s) = snd (toSeqState i t)"
  using a0 a1 a2  unfolding toSeqState_def Let_def split_beta eq_list_i 
  apply simp 
  by (metis append_eq_append_conv eq_list_i  length_take)
  
  

lemma step_cei_i1:
  assumes a0:"(\<forall>j\<noteq>i. (snd s)!j = (snd t)!j) \<and> length (snd s) = length (snd t)" and    
          a1:"i<length (snd s)" and
          a2:"\<Gamma>\<turnstile>\<^sub>c (c, toSeq (toSeqState i s)) \<rightarrow> (c', toSeq (toSeqState i t))"
        shows "\<Gamma>\<turnstile>\<^sub>c\<^sub>i(c,s) \<rightarrow>\<^sub>c\<^sub>e (c',t)"
proof-
  have a1': "i<length (snd t)"
    using a0 a1 by auto  
  have "snd (toSeqState i s) = snd (toSeqState i t)" 
    using same_local_sublist_toSeq_State
    by (simp add: same_local_sublist_toSeq_State a0 a1')    
  then have  c:"\<Gamma>\<turnstile>\<^sub>c (c, toSeqState i s) \<rightarrow>\<^sub>c\<^sub>e (c', toSeqState i t)"
    using c_step[OF a2]  by auto
  show ?thesis using c_stepi[OF c] a1 a1'
    by (simp add: a0 c step_ce_to_step_cei2)
qed


lemma step_cei_i2:
  assumes a0:"length (snd s) = length (snd t)" and    
          a1:"i<length (snd s)" and
          a2:"\<Gamma>\<turnstile>\<^sub>c (c, toSeqState i s) \<rightarrow>\<^sub>e (c, toSeqState i t)"
        shows "\<Gamma>\<turnstile>\<^sub>c\<^sub>i(c,s) \<rightarrow>\<^sub>c\<^sub>e (c,t)" using a0 a1 a2
  by (simp add: e_step step_ce_to_step_cei2)


lemma sublist:"j<(length c)-1 \<Longrightarrow> \<exists>c' c''. c = c'@([c!j,c!(j+1)]@c'')"
proof (induct j arbitrary: c)
  case 0
  then show ?case
    by (metis One_nat_def Suc_less_eq add.left_neutral append.assoc append_Cons append_Nil 
               id_take_nth_drop less_Suc_eq take_Suc_conv_app_nth zero_less_diff)
next
  case (Suc j)
  then have "j<length c - 1 -1"
    by simp
  then show ?case using Suc
    by (metis Suc_eq_plus1 Suc_lessD append.assoc append_Cons append_Nil 
             id_take_nth_drop less_diff_conv take_Suc_conv_app_nth)
qed

lemma cptni_dest:"(i,\<Gamma>,(P,s)#(Q,t)#xs) \<in> cptni \<Longrightarrow> (i,\<Gamma>,(Q,t)#xs)\<in> cptni"
by (auto dest: cptni_cases)

lemma cptni_dest_pair:"(i,\<Gamma>,x#x1#xs) \<in> cptni \<Longrightarrow> (i,\<Gamma>,x1#xs)\<in> cptni"
proof -
  assume "(i,\<Gamma>,x#x1#xs) \<in> cptni"
  thus ?thesis using cptni_dest prod.collapse by metis
qed

lemma cptni_dest1:"(i,\<Gamma>,(P,s)#(Q,t)#xs) \<in> cptni \<Longrightarrow> (i,\<Gamma>,(P,s)#[(Q,t)])\<in> cptni"
proof -
  assume a1: "(i,\<Gamma>, (P, s) # (Q, t) # xs) \<in> cptni"
  have "(i,\<Gamma>, [(Q, t)]) \<in> cptni"
    by (meson cptni.CptnOnei)
  thus ?thesis
    using a1 cptni.Cptni cptni_cases(2) by blast
qed

lemma cptni_dest1_pair:"(i,\<Gamma>,x#x1#xs) \<in> cptni \<Longrightarrow> (i,\<Gamma>,x#[x1])\<in> cptni"
proof -
  assume "(i,\<Gamma>,x#x1#xs) \<in> cptni"
  thus ?thesis using cptni_dest1 prod.collapse by metis
qed

lemma cptni_append_is_cptni [rule_format]: 
 "\<forall>b a. (i,\<Gamma>,b#c1)\<in>cptni \<longrightarrow>  (i,\<Gamma>,a#c2)\<in>cptni \<longrightarrow> (b#c1)!length c1=a \<longrightarrow> (i,\<Gamma>,b#c1@c2)\<in>cptni"
apply(induct c1)
 apply simp
apply clarify
apply(erule cptni.cases,simp_all)
  using cptni.Cptni by blast
(* apply (simp add: cptn.CptnEnv)
by (simp add: cptn.CptnComp) *)

lemma cptni_dest_2:
  "(i,\<Gamma>,a#xs@ys) \<in> cptni  \<Longrightarrow> (i,\<Gamma>,a#xs)\<in> cptni"
proof (induct "xs" arbitrary: a)
  case Nil thus ?case using cptni.simps
    by (smt cptnip.CptnOnei cptnip_cptni_eq surj_pair) 
next
  case (Cons x xs') 
  then have "(i,\<Gamma>,a#[x])\<in>cptni" by (simp add: cptni_dest1_pair)
  also have "(i,\<Gamma>, x # xs') \<in> cptni"
    using Cons.hyps Cons.prems cptni_dest_pair by fastforce    
  ultimately show ?case using cptni_append_is_cptni [of i \<Gamma> a "[x]" x xs']
    by force    
qed   

lemma tl_in_cptni: "\<lbrakk> (i,g,a#xs) \<in>cptni; xs\<noteq>[] \<rbrakk> \<Longrightarrow> (i,g,xs)\<in>cptni"
  by (force elim: cptni.cases)

lemma sublist_in_cptni:"(i,\<Gamma>, ys@ xs) \<in> cptni \<Longrightarrow> xs\<noteq> [] \<Longrightarrow> (i,\<Gamma>, xs) \<in> cptni"
proof(induct ys)
  case Nil
  then show ?case by auto
next
  case (Cons a ys)
  then have "(i,\<Gamma>, a # (ys @ xs)) \<in> cptni" by auto
  then show ?case using cptni_cases
    by (metis Cons.hyps Cons.prems(2) Nil_is_append_conv tl_in_cptni)  
qed

lemma cptni_step_cei:
  assumes a0:"(i,\<Gamma>,c) \<in> cptni" and a1:"j<(length c)-1"
  shows "\<Gamma>\<turnstile>\<^sub>c\<^sub>i (c!j) \<rightarrow>\<^sub>c\<^sub>e (c!(j+1))"
proof-
 obtain c' c'' where "c = c'@([c!j,c!(j+1)]@c'')" using sublist[OF a1] by auto
  then have "(i,\<Gamma>,c!j#(c!(j+1))#c'') \<in>cptni" using a0 sublist_in_cptni
    by (metis append_Cons append_Nil list.distinct(1))
  then obtain pj sj pj1 sj1 
    where cptni:"(i,\<Gamma>,(pj,sj)#(pj1,sj1)#c'') \<in>cptni" and 
          cj:"c!j = (pj,sj)" and cj1:"c!(j+1) =(pj1,sj1)"
    by (metis prod.exhaust_sel)     
  then show ?thesis using cptni_cases(2)[OF cptni] by auto  
qed


lemma step_cei_notNormal:
  assumes a0:"(i,\<Gamma>,c) \<in> cptni" and a1:"j<(length c)-1" and 
    a2:"fst (c!j) = Skip \<or> fst (c!j) = Throw \<or> fst (c!j) = Stuck \<or> (\<exists>f. fst (c!j) = Fault f)"        
  shows "fst (c!j) = fst (c!(j+1))"
proof- 
  obtain ca ca' sj sj' where 
    "\<Gamma>\<turnstile>\<^sub>c (ca, sj) \<rightarrow>\<^sub>c\<^sub>e (ca', sj')" and
    "(c!j) = (ca, toParState i sj)" and "(c!(j+1)) = (ca', toParState i sj')"
    using step_cei[OF cptni_step_cei[OF a0 a1]]
    by metis
  moreover have "\<Gamma>\<turnstile>\<^sub>c (ca, (toSeq sj)) \<rightarrow> (ca', toSeq  sj') \<or> 
             \<Gamma>\<turnstile>\<^sub>c (ca, sj) \<rightarrow>\<^sub>e (ca', sj')"    
    using step_ce_dest calculation by blast 
  ultimately show ?thesis apply auto using a2
    apply (fastforce elim:  stepc_elim_cases)
    by (drule stepe_elim_cases1, auto) 
qed

lemma "i<length ls \<Longrightarrow> (gs,lss) = toParState i ((g,l),ls) \<Longrightarrow> lss!i = l"
  by (meson less_le toPar_li)

lemma step_cei_end_local_i:
  assumes a0:"(i,\<Gamma>,c) \<in> cptni" and a1:"j<(length c)-1" and            
          a2:"c!j = (p, (g,l))" and a2':"c!(j+1) = (p', (g',l'))" and
         a3:"i < length l" and a4:"p = Skip \<or> p = Throw \<or> p = Stuck \<or> (\<exists>f. p = Fault f)"        
  shows "l!i = l'!i"
proof-
  obtain ca ca' sj sj' where 
    "\<Gamma>\<turnstile>\<^sub>c (ca, sj) \<rightarrow>\<^sub>c\<^sub>e (ca', sj')" and
    cj:"(c!j) = (ca, toParState i sj)" and cj':"(c!(j+1)) = (ca', toParState i sj')"
    using step_cei[OF cptni_step_cei[OF a0 a1]]
    by metis
  moreover obtain sjg sjl sjls  sjg' sjl' sjls' where 
    sj:"sj = ((sjg,sjl), sjls)" and sj':"sj' = ((sjg',sjl'), sjls')" 
    using calculation
    by (metis prod.exhaust_sel) 
  moreover have step:"\<Gamma>\<turnstile>\<^sub>c (ca, (toSeq sj)) \<rightarrow> (ca', toSeq  sj') \<or> 
             \<Gamma>\<turnstile>\<^sub>c (ca, sj) \<rightarrow>\<^sub>e (ca', sj')"    
    using step_ce_dest calculation by blast 
  have isjls:"i\<le> length sjls" using a3 sj a2 cj
    by (metis Suc_eq_plus1 Suc_leI len_toParState not_less snd_conv)     
  then have isjls':"i\<le>length sjls'" 
    using a3 sj a2 cj len_toParState
    using calculation(1) ce_eq_length isjls sj' by fastforce
          
  { assume "\<Gamma>\<turnstile>\<^sub>c (ca, (toSeq sj)) \<rightarrow> (ca', toSeq  sj')"
    then have ?thesis apply auto using a2 a2'
      by (metis SmallStepCon.final_def SmallStepCon.no_step_final a4 calculation(2) fst_conv)
  } 
  moreover { assume "\<Gamma>\<turnstile>\<^sub>c (ca, sj) \<rightarrow>\<^sub>e (ca', sj')"
    then have "sjl = sjl'" using sj sj'
      by (simp add: env_normal_same_local)
    moreover have "l!i = sjl" using sj cj a2 toPar_li[OF isjls, of g l sjg sjl] by auto
    moreover have "l'!i = sjl'" using sj' cj' a2' toPar_li[OF isjls', of g' l' sjg' sjl'] by auto
    ultimately have ?thesis using a2 a2' sj sj' cj cj' by auto
  } 
  ultimately show ?thesis using step by auto
qed


lemma cptni_normal_normal_same_length:
  assumes a0:"(i,\<Gamma>,c) \<in> cptni" and a1:"j<(length c)-1" and a2:"(c!j) = (p,(g,l))" and
       a3:"(c!(j+1)) = (p',(g',l'))"
     shows "length l = length l'"
  using cptni_step_cei[OF a0 a1] a2 a3 step_cei_normal_normal_same_len
  by fastforce

lemma cptni_i_normal_len:
    "(i,\<Gamma>,c) \<in> cptni \<Longrightarrow>  length c > 1 \<Longrightarrow> j<length c \<Longrightarrow> j'<length c \<Longrightarrow> j'\<ge>j \<Longrightarrow>
      (c!j) = (p,(g,l))  \<Longrightarrow> c!j' = (p',(g',l')) \<Longrightarrow>
      length l = length l'"
proof (induct "j'-j" arbitrary: j p p' g' g l l')
  case 0
  then show ?case by auto
next
  case (Suc x)
  {assume "x = 0"
    then have ?case using Suc step_cei_notNormal[OF Suc(3)] 
   cptni_normal_normal_same_length[OF  Suc(3)]
      by (metis (no_types, lifting) One_nat_def le_add_diff_inverse less_diff_conv)
  }
  moreover { assume "x\<noteq>0"   
    then have j:"j<(length c)-1" using Suc
      by linarith      
    have x:"x=j' - (j+1)"
        by (metis (no_types) Suc.hyps(2) diff_Suc_1 diff_diff_add)
    moreover have j1_len:"j+1 < length c"        
      using \<open>j < length c - 1\<close> less_diff_conv by blast
    moreover have  j_j':"j+1 \<le> j'"
      using \<open>x \<noteq> 0\<close> calculation(1) by auto
    ultimately have ?case using Suc  x j1_len j_j' j Suc(1)[OF x Suc(3,4) j1_len Suc(6) j_j']
               cptni_normal_normal_same_length[OF  Suc(3)]  by (metis prod_cases3)
  }
  ultimately show ?case by auto
qed



lemma length_locs_less_i:
  assumes a0:"(i,\<Gamma>,c) \<in> cptni" and
       a1:"length c > 0" and a2:"c!0 = (p, (g,l))" and
       a3:"i< length l" 
     shows "\<forall>j<length c. i< length (snd (snd (c!j)))"
proof (cases "length c = 1")
  assume "length c = 1"
  then show ?thesis using a0 a1 a2 a3 by auto
next
  assume "length c\<noteq>1"
  then have l0:"length c>1" using a1 by linarith
  { fix j 
    assume a00:"j<length c"    
    have "0 \<le> j"
     by blast
   then have "i< length (snd (snd (c!j)))"
     using cptni_i_normal_len[OF a0 l0 a1 a00]  a2 a3
     by (metis prod.exhaust_sel)
  } thus ?thesis by auto
qed



lemma cptni_cptn:
 "(i,\<Gamma>,c) \<in> cptni \<Longrightarrow> 
  c!0 = (p,(g,ls))   \<Longrightarrow> i< length ls \<Longrightarrow>
 (\<Gamma>, toSeqCptn i c) \<in> cptn"
proof (induct arbitrary: p g ls rule:cptni.induct)
  case (CptnOnei i \<Gamma> P s)
  then show ?case unfolding toSeqCptn_def 
    by (simp add: cptn.CptnOne)
next
  case (Cptni \<Gamma> i P s Q t xs)  
  have f1: "s = snd (p, g, ls)"
    using Cptni.prems(1) by fastforce
  then have f2: "(\<Gamma>, toSeqCptn i ((Q, t) # xs)) \<in> cptn"
    by (metis (no_types) Cptni.hyps(1) Cptni.hyps(3) Cptni.prems(2) eq_snd_iff 
              nth_Cons_0 step_cei_normal_normal_same_len)
  have "\<Gamma>\<turnstile>\<^sub>c\<^sub>i (fst (P, s), snd (p, g, ls)) \<rightarrow>\<^sub>c\<^sub>e (fst (Q, t), t)"
    using Cptni.hyps(1) Cptni.prems(1) by auto
  then show ?case
    using f2 f1 by (simp add: Cptni.prems(2) cptn.Cptn step_cei_ce toSeqCptn_simp)   
qed




lemma cptn_cptni:
 "(\<Gamma>,c) \<in> cptn \<Longrightarrow> 
  c!0 = (p, ((g,l), ls))   \<Longrightarrow> i\<le> length ls \<Longrightarrow>
 (i,\<Gamma>, toParCptn i c) \<in> cptni"
proof (induct arbitrary: p g l ls rule:cptn.induct)
  case (CptnOne \<Gamma> P s)
  then show ?case unfolding toParCptn_def 
    by (simp add: cptni.CptnOnei)
next
  case (Cptn \<Gamma> P s Q t xs)
  then have  "\<Gamma>\<turnstile>\<^sub>c\<^sub>i(P,toParState i s) \<rightarrow>\<^sub>c\<^sub>e (Q,toParState i t)"
    using c_stepi by blast
  moreover have " (i,\<Gamma>, toParCptn i ((Q, t) # xs)) \<in> cptni" 
    using Cptn.hyps(3) Cptn.prems(2) using Cptn.hyps(1) Cptn.hyps(3) Cptn.prems(2)  ce_eq_length
    by (metis Cptn.prems(1) nth_Cons_0 prod.exhaust_sel snd_conv)
  ultimately show ?case using toParCptn_simp
    by (simp add: toParCptn_simp cptni.Cptni)
qed

 
lemma cptn_length_locs_less_i:
     assumes a0:"(\<Gamma>,c) \<in> cptn" and       
       a1:"c!0= (p, ((g,l), ls))" and a2:"i\<le> length ls" 
     shows "\<forall>j<length c. i\<le> length (snd (snd (c!j)))"
proof(cases "length c")
  case 0
  then show ?thesis by auto
next
  case (Suc nat)
  then have len:"length c>0" by auto
  have  cptni:"(i,\<Gamma>, toParCptn i c) \<in> cptni" using cptn_cptni[OF a0 a1 a2] by auto  
  moreover obtain p' g' ls' where "toParCptn i c!0 = (p',(g',ls'))"
    by (metis surj_pair)
  ultimately have " i< length ls'"
    using a1 a2 len unfolding toParCptn_def
    unfolding toParState_def by auto
  then have "\<forall>j<length (toParCptn i c).                 
                          i<length (snd (snd ((toParCptn i c)!j)))"
    using \<open>toParCptn i c ! 0 = (p', g', ls')\<close> cptni length_locs_less_i by fastforce 
  then show ?thesis using len unfolding toParCptn_def
    by (simp add: len_toParState less_Suc_eq_le)     
qed


(* definition toParPred:: "(((('g, 'l, 'p,'f,'e) config_gs) list) \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> ((('g,'l,'p,'f,'e) gconf list) \<Rightarrow> bool)"
  where "toParPred Q i \<equiv> (\<lambda>x. Q (toSeqCptn i x) )"

lemma "(\<Gamma>,c) \<in> cptn \<Longrightarrow> P c \<Longrightarrow> \<forall>sn. snd(c!0) = Normal sn \<or> snd(c!0) = Abrupt sn \<longrightarrow>  i\<le> length (snd sn) \<Longrightarrow>       
       (\<lambda>x. P (toSeqCptn i x)) (toParCptn i c)" *)


definition final_glob:: "('g,'l,'p,'f,'e) config_gs \<Rightarrow> bool" where
  "final_glob cfg \<equiv>  fst cfg=Skip \<or> (fst cfg=Throw) \<or> (\<exists>f. fst cfg= Fault f ) \<or> (fst cfg = Stuck)"
                                           
lemma final_eq:"final_glob cfg = SmallStepCon.final (fst cfg, toSeq (snd cfg))"
  unfolding final_def final_glob_def SmallStepCon.final_def
  by (cases "snd cfg",auto)

definition cpi1 :: "nat \<Rightarrow> ('g\<times>'l,'p,'f,'e) body \<Rightarrow> ('g\<times>'l,'p,'f,'e)com  \<Rightarrow>
                   ('g,'l)par_state \<Rightarrow> (nat \<times>('g,'l,'p,'f,'e) gconfs) set" where
  "cpi1 i \<Gamma> P s \<equiv> {(i1,\<Gamma>1,l). l!0=(P,s) \<and> (i,\<Gamma>,l) \<in> cptni \<and> \<Gamma>1=\<Gamma>}"  

 

lemma cpi1_sub: 
  assumes a0: "(i,\<Gamma>,(x#l0)@l1) \<in> cpi1 i \<Gamma> P s"
  shows "(i,\<Gamma>,(x#l0)) \<in> cpi1 i \<Gamma> P s"
proof -    
  show ?thesis using a0 unfolding cpi1_def
    using cptni_dest_2 by fastforce
qed

definition wf_state:: "nat \<Rightarrow> ('g,'l)par_state \<Rightarrow> bool"
  where "wf_state i s \<equiv> i < length (snd s)"

definition cpi :: "nat \<Rightarrow> ('g\<times>'l,'p,'f,'e) body \<Rightarrow> ('g\<times>'l,'p,'f,'e)com  \<Rightarrow>
                   ('g,'l)par_state \<Rightarrow> (('g,'l,'p,'f,'e) gconfs) set" where
  "cpi i \<Gamma> P s \<equiv> {(\<Gamma>1,l). l!0=(P,s) \<and> (i,\<Gamma>,l) \<in> cptni \<and> \<Gamma>1=\<Gamma> \<and> wf_state i s}"  


lemma cpi_sub: 
  assumes a0: "(\<Gamma>,(x#l0)@l1) \<in> cpi  i \<Gamma> P s"
  shows "(\<Gamma>,(x#l0)) \<in> cpi  i \<Gamma> P s"
proof -    
  show ?thesis using a0 unfolding cpi_def
    using cptni_dest_2 by fastforce
qed

end