theory Sim_Rules
imports CRef "CSimpl.SmallStepCon"
begin
section \<open>Operational rules for CSimpRGSim\<close>

lemma conjId: "\<lbrakk>Q; P\<rbrakk> \<Longrightarrow> P \<and> Q" by (rule conjI)


definition eq_rel:: "'a set \<Rightarrow> 'b set  \<Rightarrow>('a\<times>'b) set" 
  ("_ \<rightleftharpoons> / _" [81,81] 100) 
  where
"eq_rel s1 s2   \<equiv> {(a,b).  (a \<in> s1) = (b \<in> s2)}"

definition and_rel:: "'a set \<Rightarrow> 'b set  \<Rightarrow>('a\<times>'b) set" 
  ("_ \<odot> / _" [81,81] 100) 
  where
"and_rel s1 s2   \<equiv> {(a,b). (a \<in> s1) \<and> (b \<in> s2)}"

definition ext_set:: "('a\<times>'b) set  \<Rightarrow>(('a\<times>'a1) \<times>('b\<times>'b1)) set"  ("(\<up>_)" [1000] 999)
  where
"ext_set s1  \<equiv> {(a,b).  (fst a, fst b)\<in>s1}"

lemma same_set: 
  "(\<sigma>, \<Sigma>) \<in> \<xi> \<Longrightarrow>
   \<xi> \<subseteq> \<up>(b\<^sub>c \<rightleftharpoons>  b\<^sub>s) \<Longrightarrow> 
   (fst \<sigma> \<in> b\<^sub>c) = (fst \<Sigma> \<in> b\<^sub>s)" 
  unfolding eq_rel_def ext_set_def  by auto
 
definition Sta\<^sub>s :: "('s,'s1) rel \<Rightarrow> 
                   ('s tran, 's1 tran) rel \<Rightarrow> bool" where
  "Sta\<^sub>s f R \<equiv>  (\<forall>x x1 y y1. (x,y) \<in> f \<and>  ((x, x1),y, y1)\<in> R \<longrightarrow> 
                (x1,y1)\<in> f)"


lemma alpha_id_G:assumes 
  a0:"(\<sigma>,\<Sigma>) \<in> \<alpha>" and  
  a1:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>) \<in> G\<^sub>c"
shows "((\<sigma>, \<sigma>), \<Sigma>, \<Sigma>) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
 using a0 a1 unfolding  related_transitions_def Id_def  by fastforce
  

lemma skip3:
  assumes a0:"(\<sigma>, \<Sigma>) \<in> \<xi>" and                    
          a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>) \<in> G\<^sub>c" 
        shows 
           "(\<exists>\<Sigma>'. ((\<sigma>, \<sigma>), \<Sigma>, \<Sigma>') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
            (\<sigma>, \<Sigma>') \<in> \<xi> \<and>           
            \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Skip,  \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>*
                    (LanguageCon.com.Skip, \<Sigma>'))"  
  using a0 a1  a2  unfolding related_transitions_def Id_def 
  by fast

lemma skip4:
  assumes a0:"(\<sigma>, \<Sigma>) \<in> \<alpha>" and a1:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>) \<in> G\<^sub>c" 
        shows 
           "(\<exists>\<Sigma>'. ((\<sigma>, \<sigma>), \<Sigma>, \<Sigma>') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>                       
            \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Fault f,  \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, \<Sigma>'))"  
  using a0 a1   unfolding related_transitions_def Id_def 
  by fast



lemma Fault_sim:
  assumes  a1:"(\<sigma>, \<Sigma>) \<in> \<alpha>" and a2:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" 
  shows
   "(\<Gamma>\<^sub>c,(Fault f, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Fault f, \<Sigma>),R\<^sub>s,G\<^sub>s)" using skip4 
  using a1    
  apply(coinduction arbitrary: \<sigma> \<Sigma>)
  apply clarsimp
  apply (rule conjId)+
     apply (auto simp add: related_transitions_def)
  by (auto simp add: no_step_Fault a2 Domain.DomainI)
  

lemma Stuck_sim:
  assumes  a1:"(\<sigma>, \<Sigma>) \<in> \<alpha>" and a2:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" 
  shows
   "(\<Gamma>\<^sub>c,(Stuck, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Stuck, \<Sigma>),R\<^sub>s,G\<^sub>s)" using skip4 
  using a1    
  apply(coinduction arbitrary: \<sigma> \<Sigma>)
  apply clarsimp
  apply (rule conjId)+
     apply (auto simp add: related_transitions_def)
  by (auto simp add: no_step_Stuck a2 Domain.DomainI)


lemma sim_env:
  assumes 
 a0:"(\<sigma>, \<Sigma>) \<in> \<xi>" and
 a1:"Sta\<^sub>s \<xi> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>" and
 a2:" (((\<sigma>, \<sigma>'), \<Sigma>, \<Sigma>') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" 
shows" (\<sigma>', \<Sigma>') \<in> \<xi>"
  using a0 a1 a2  unfolding Sta\<^sub>s_def  by fastforce

lemma "\<xi> \<subseteq> \<alpha> \<Longrightarrow> (((a, b), ba), (aa, bb), bc) \<in> \<xi> \<Longrightarrow> Sta\<^sub>s \<xi> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow>
        \<forall>a b ba. (((a, b), ba), (a, b), ba) \<in> G\<^sub>c 
       \<Longrightarrow> \<forall>ab bd be ac bf bg.
              ((((a, b), ba), (ab, bd), be), ((aa, bb), bc), (ac, bf), bg) \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<longrightarrow>
              (((ab, bd), be), (ac, bf), bg) \<in> \<xi> \<or> (\<Gamma>\<^sub>c,(LanguageCon.com.Skip, (ab, bd), be),R\<^sub>c,G\<^sub>c)
              \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(LanguageCon.com.Skip, (ac, bf), bg),R\<^sub>s,G\<^sub>s)"
  using sim_env by auto
  
lemma skip_step: "\<xi> \<subseteq> \<alpha> \<Longrightarrow> (((a, b), ba), (aa, bb), bc) \<in> \<xi> \<Longrightarrow> Sta\<^sub>s \<xi> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow>
        \<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c \<Longrightarrow>
           \<exists>ab bd.
              ((((a, b), ba), (a, b), ba), ((aa, bb), bc), (ab, bd), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
              (((a, b), ba), (ab, bd), bc) \<in> \<xi> \<and>
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Skip, CRef.toSeq ((aa, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                      (LanguageCon.com.Skip, CRef.toSeq ((ab, bd), bc))"
  using related_transition_intro
  by (smt in_mono rtrancl.rtrancl_refl rtrancl_idemp rtranclp.rtrancl_refl Domain.DomainI)

 lemma Skip_sim:
  assumes a1:"\<xi> \<subseteq> \<alpha>" and
          a2: "(\<sigma>,\<Sigma>)\<in>\<xi>" and
          a3: "Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
          a5: "\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>) \<in> G\<^sub>c"  
  shows
   "(\<Gamma>\<^sub>c,(Skip, \<sigma>),R\<^sub>c,G\<^sub>c)
           \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Skip, \<Sigma>),R\<^sub>s,G\<^sub>s)" using  a1 a2 a3  a5 
  apply (coinduction arbitrary: \<sigma> \<Sigma>)
   apply (clarsimp)   
   apply (rule conjI,blast intro: skip1)+
   apply (rule conjI)
   apply (simp add: sim_env) 
   by (fast intro: skip_step)
 
lemma Skip_sound: 
  "\<xi> \<subseteq> \<alpha> \<Longrightarrow> Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow> \<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c \<Longrightarrow> 
    (\<Gamma>\<^sub>c,Skip,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,Skip,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def by (simp add: Skip_sim) 
        
 
lemma throw3:
  assumes a0:"(\<sigma>, \<Sigma>) \<in> \<xi>" and          
          a2:"\<xi> \<subseteq> \<alpha>" and a3:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>) \<in> G\<^sub>c" 
        shows 
           "(\<exists>\<Sigma>'. ((\<sigma>, \<sigma>), \<Sigma>, \<Sigma>') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
            (\<sigma>, \<Sigma>') \<in> \<xi> \<and> snd \<Sigma> = snd \<Sigma>' \<and>          
            \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Throw, toSeq \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, toSeq \<Sigma>'))"  
  using a0 a2 a3 unfolding related_transitions_def Id_def by fast   
  
lemma Throw_sim:
  assumes  a0:"\<xi> \<subseteq> \<alpha>" and
          a1: "(\<sigma>,\<Sigma>)\<in>\<xi>" and 
          a2: "Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
          a4: "\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" 
  shows
   "(\<Gamma>\<^sub>c,(Throw, \<sigma>),R\<^sub>c,G\<^sub>c)
           \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>) (\<Gamma>\<^sub>s,(Throw, \<Sigma>),R\<^sub>s,G\<^sub>s)" using  a0 a1 a2  a4
  apply (coinduction arbitrary: \<sigma> \<Sigma>)
  apply (clarsimp)
   apply (rule conjI,blast)
   apply (rule conjI, fastforce intro: throw1)        
  apply (rule conjI, metis (no_types, lifting) SmallStepCon.stepc_elim_cases(11) stepce_stepc)   
  apply (rule conjI, simp add:  sim_env)  
  by (frule throw3, auto)


        
lemma Throw_sound: 
  "\<xi> \<subseteq> \<alpha> \<Longrightarrow> Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow>  \<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>) \<in> G\<^sub>c \<Longrightarrow> 
   (\<Gamma>\<^sub>c,Throw,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>) (\<Gamma>\<^sub>s,Throw,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def by (simp add: Throw_sim )    
  
 lemma env_sim:
   assumes
     a0:" (\<Gamma>\<^sub>c,(c1\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and
     a1:"((\<sigma>, s1), \<Sigma>, s1') \<in> ((R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" 
     shows"
          (\<Gamma>\<^sub>c,(c1\<^sub>c, s1),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1\<^sub>s, s1'),R\<^sub>s,G\<^sub>s)  \<or> P"   
using  dest_sim_env_step[OF a0 a1 ] by fastforce

lemma seq_ev_comp_step:
  assumes a0:"(\<Gamma>\<^sub>c,(c1\<^sub>c, (a, b), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1\<^sub>s, (aa, bb), bc),R\<^sub>s,G\<^sub>s)" and
        a1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Seq c1\<^sub>c c2\<^sub>c, toSeq ((a, b), ba)) \<rightarrow>(c\<^sub>c', toSeq ((ab, bd), ba))"
      shows "\<exists>c\<^sub>s' ac be.
              (\<exists>a ab b.
                  \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq c1\<^sub>s c2\<^sub>s, toSeq ((aa, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, (ab, b)) \<and>
                  (\<exists>aa ad ba.
                      \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, ab, b) \<rightarrow> (aa, ad, ba) \<and>
                      \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ad, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((ac, be), bc)))) \<and>
              (((ab, bd), ba), (ac, be), bc) \<in> \<alpha> \<and>
              ((((a, b), ba), (ab, bd), ba), ((aa, bb), bc), (ac, be), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
              ((\<exists>a b bb c1\<^sub>c.
                   c\<^sub>c' = Seq c1\<^sub>c c2\<^sub>c \<and>
                   (\<exists>c1\<^sub>s.
                       c\<^sub>s' = Seq c1\<^sub>s c2\<^sub>s \<and>
                       ac = a \<and>
                       be = b \<and>
                       bc = bb \<and> (\<Gamma>\<^sub>c,(c1\<^sub>c, (ab, bd), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) 
                               (\<Gamma>\<^sub>s,(c1\<^sub>s, (a, b), bb),R\<^sub>s,G\<^sub>s))) \<or>
               (\<Gamma>\<^sub>c,(c\<^sub>c', (ab, bd), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (ac, be), bc),R\<^sub>s,G\<^sub>s))"  
proof-
  have "c1\<^sub>c\<noteq>Skip \<and> c1\<^sub>c\<noteq>Throw" 
    using not_seq_skip_throw_ev  a1  by fast
  then obtain c1'
    where stepc1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (c1\<^sub>c, toSeq ((a, b), ba)) \<rightarrow> (c1', toSeq ((ab, bd), ba))" and 
          seq:    "(c\<^sub>c', ((ab, bd), ba))= (Seq c1' c2\<^sub>c,  ((ab, bd), ba))" 
    using stepc_elim_cases1(7)[OF a1, of "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (c1\<^sub>c, toSeq ((a, b), ba)) \<rightarrow> 
                                                      (c1', toSeq ((ab, bd), ba)) \<and> 
                                          (c\<^sub>c', toSeq ((ab, bd), ba))= 
                                          (Seq c1' c2\<^sub>c, toSeq ((ab, bd), ba))"]
    by fastforce
  thus ?thesis 
    using  seq_ev_plus stepc1 seq  dest_sim_ev_step[OF a0 stepc1]
    by fastforce
qed    

   (*if c1\<^sub>c = Skip and \<sigma> is not normal we cannot get  (\<Gamma>\<^sub>c,c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c2\<^sub>s,R\<^sub>s,G\<^sub>s) 
   since we don't get (\<sigma>,\<Sigma>)\<in>\<gamma>\<^sub>r in that case we need to prove that (c2\<^sub>c,\<sigma>) *)
lemma seq_no_ev_comp_step: assumes 
  a2:"(\<Gamma>\<^sub>c,(c1\<^sub>c, (a, b), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1\<^sub>s, (aa, bb), bc),R\<^sub>s,G\<^sub>s)" and
  a3:"(\<Gamma>\<^sub>c,c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c2\<^sub>s,R\<^sub>s,G\<^sub>s)" and a4:"Sta\<^sub>s \<gamma>\<^sub>a (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>" and
  a5:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and 
  a8:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Seq c1\<^sub>c c2\<^sub>c, CRef.toSeq ((a, b), ba)) \<rightarrow> (c\<^sub>c', CRef.toSeq ((ab, bd), ba))"
shows"\<exists>c\<^sub>s' ac be.
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq c1\<^sub>s c2\<^sub>s, CRef.toSeq ((aa, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                      (c\<^sub>s', CRef.toSeq ((ac, be), bc)) \<and>
              (((ab, bd), ba), (ac, be), bc) \<in> \<alpha> \<and>
              ((((a, b), ba), (ab, bd), ba), ((aa, bb), bc), (ac, be), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
              ((\<exists>a b bb c1\<^sub>c.
                   c\<^sub>c' = LanguageCon.com.Seq c1\<^sub>c c2\<^sub>c \<and>
                   (\<exists>c1\<^sub>s.
                       c\<^sub>s' = LanguageCon.com.Seq c1\<^sub>s c2\<^sub>s \<and>
                       ac = a \<and>
                       be = b \<and>
                       bc = bb \<and> (\<Gamma>\<^sub>c,(c1\<^sub>c, (ab, bd), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                       (\<Gamma>\<^sub>s,(c1\<^sub>s, (a, b), bb),R\<^sub>s,G\<^sub>s))) \<or>
               (\<Gamma>\<^sub>c,(c\<^sub>c', (ab, bd), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (ac, be), bc),R\<^sub>s,G\<^sub>s))"
proof(cases "c1\<^sub>c = Skip \<or> c1\<^sub>c = Throw \<or> (\<exists>f. c1\<^sub>c = Fault f) \<or> (c1\<^sub>c = Stuck)")
  let ?\<sigma> = "((a, b), ba)" and ?\<Sigma> = "((aa, bb), bc)" and ?\<sigma>' = "((ab, bd), ba)"
  case True 
  { assume a00:"c1\<^sub>c = Skip"         
    then have step_seq:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Seq c1\<^sub>c c2\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (c2\<^sub>c,toSeq ?\<sigma>)"
      using SeqSkipc by auto     
    then have alpha:"c\<^sub>c'=c2\<^sub>c \<and> toSeq ?\<sigma>' = toSeq ?\<sigma> " 
      using stepc_elim_cases1(1) a8 prod.inject stepce_stepc[OF step_seq]
      by (metis a00 stepc_elim_seq_skip(1))       
    obtain s1 s2 where  
      in_alpha:"((?\<sigma>, ?\<sigma>), ?\<Sigma>, ((s1,s2), bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c1\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeq ((s1,s2), bc)) \<and> 
                  (?\<sigma>,  ((s1,s2), bc)) \<in> \<gamma>\<^sub>r \<and> \<gamma>\<^sub>r \<subseteq> \<alpha>" 
      by (insert a2[simplified a00], erule sim_elim_cases_c(1), auto) 
    let ?\<Sigma>' = "((s1,s2), bc)"
    have sim: "(\<Gamma>\<^sub>c,(c2\<^sub>c, ?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c2\<^sub>s,  ?\<Sigma>'),R\<^sub>s,G\<^sub>s)"
      using a3 in_alpha unfolding RGSim_pre_def by auto
    have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c2\<^sub>s, toSeq ?\<Sigma>')"    
      using seq_ev_s SeqSkipc in_alpha
      by (metis (no_types, hide_lams) rtranclp.simps)   
    then have ?thesis using in_alpha sim alpha 
      unfolding toSeq_def by auto    
  }
  moreover { assume a00:"c1\<^sub>c = Throw" 
    then have step_seq:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Seq c1\<^sub>c c2\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (Throw, toSeq ?\<sigma>)"
      using SeqThrowc by auto
    then have alpha:"c\<^sub>c'=Throw \<and> toSeq ?\<sigma>' = toSeq ?\<sigma> \<and> ?\<sigma>' = ?\<sigma>"  
      using a00 Pair_inject a8 stepc_elim_seq_skip(2) throw1 fst_conv unfolding toSeq_def
      by metis
    obtain s1 s2 where in_alpha:"((?\<sigma>, ?\<sigma>), ?\<Sigma>, ((s1,s2),bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c1\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, toSeq ((s1,s2),bc))" 
           and r:"(?\<sigma>,  ((s1,s2),bc)) \<in> \<gamma>\<^sub>a" and gamm_subset:"\<gamma>\<^sub>a \<subseteq> \<alpha>"
      by (insert a2[simplified a00], erule sim_elim_cases_c(2), auto)
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, toSeq ((s1,s2),bc))" 
      using seq_ev_s SeqThrowc  
      by (metis (no_types, hide_lams) rtranclp.simps) 
    then have ?thesis using   r step_seq alpha 
      in_alpha Throw_sim[OF  gamm_subset r a4   a5] gamm_subset  a00  unfolding toSeq_def
      by fast
  }
  moreover { 
    fix f assume a00:"c1\<^sub>c = Fault f"
    then have step_seq:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Seq c1\<^sub>c c2\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (Fault f, toSeq ?\<sigma>)"
      using SeqFaultc by auto
    then have alpha:"c\<^sub>c'=Fault f \<and> toSeq ?\<sigma>' = toSeq ?\<sigma> \<and> ?\<sigma>' = ?\<sigma>"  
      using a00 Pair_inject a8 stepc_elim_seq_skip(4) Fault_ev fst_conv unfolding toSeq_def
      by metis
    obtain s1 s2 where in_alpha:" ((?\<sigma>, ?\<sigma>), ?\<Sigma>, ((s1,s2),bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c1\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq ((s1,s2),bc))" 
           and r:"(?\<sigma>,  ((s1,s2),bc)) \<in> \<alpha>" 
      by (insert a2[simplified a00], erule sim_elim_cases_c(3), auto)
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq ((s1,s2),bc))" 
      using seq_ev_s SeqFaultc  
      by (metis (no_types, hide_lams) rtranclp.simps) 
    then have ?thesis using   r step_seq alpha 
      in_alpha    a00 Fault_sim[OF r a5]  unfolding toSeq_def
      by fastforce      
  }
  moreover { 
    assume a00:"c1\<^sub>c = Stuck"
    then have step_seq:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Seq c1\<^sub>c c2\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (Stuck, toSeq ?\<sigma>)"
      using SeqStuckc by auto
    then have alpha:"c\<^sub>c'=Stuck \<and> toSeq ?\<sigma>' = toSeq ?\<sigma> \<and> ?\<sigma>' = ?\<sigma>"  
      using a00 Pair_inject a8 stepc_elim_seq_skip(3) Stuck_ev fst_conv unfolding toSeq_def
      by metis
    obtain s1 s2 where in_alpha:" ((?\<sigma>, ?\<sigma>), ?\<Sigma>, ((s1,s2),bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c1\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, toSeq ((s1,s2),bc))" 
           and r:"(?\<sigma>,  ((s1,s2),bc)) \<in> \<alpha>" 
      by (insert a2[simplified a00], erule sim_elim_cases_c(4), auto)
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, toSeq ((s1,s2),bc))" 
      using seq_ev_s SeqStuckc  
      by (metis (no_types, hide_lams) rtranclp.simps) 
    then have ?thesis using   r step_seq alpha 
      in_alpha    a00 Stuck_sim[OF r a5]  unfolding toSeq_def
      by fastforce
  }
  ultimately show ?thesis using True by fast       
next
  let ?\<sigma> = "((a, b), ba)" and ?\<Sigma> = "((aa, bb), bc)" and ?\<sigma>' = "((ab, bd), ba)"
  case False 
  then obtain c1'
    where stepc1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c1\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (c1', toSeq ?\<sigma>')" and 
          seq:    "(c\<^sub>c', toSeq ?\<sigma>')= (Seq c1' c2\<^sub>c, toSeq ?\<sigma>')"
    using  SmallStepCon.redex_not_Seq 
           stepc_elim_cases1(7)[OF a8, of "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c1\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (c1', toSeq ?\<sigma>') \<and> 
                                           (c\<^sub>c',toSeq ?\<sigma>')= (Seq c1' c2\<^sub>c,toSeq ?\<sigma>')"]
    by fastforce
  thus ?thesis 
    using  seq_ev_s stepc1 seq  
    dest_sim_tau_step[of \<Gamma>\<^sub>c c1\<^sub>c ?\<sigma> R\<^sub>c G\<^sub>c \<alpha> \<gamma>\<^sub>r \<gamma>\<^sub>a \<Gamma>\<^sub>s c1\<^sub>s ?\<Sigma> R\<^sub>s G\<^sub>s  _ ?\<sigma>', OF a2 stepc1] 
    unfolding RGSim_pre_def by fastforce    
qed

 lemma Seq_sim:  
  "\<gamma>\<^sub>a\<subseteq>\<alpha> \<Longrightarrow>
   (\<Gamma>\<^sub>c,(c1\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
   (\<Gamma>\<^sub>c,c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c2\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow> Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow>
   \<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>) \<in> G\<^sub>c \<Longrightarrow>
   (\<Gamma>\<^sub>c,(Seq c1\<^sub>c c2\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq c1\<^sub>s c2\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s)"
apply(coinduction arbitrary: \<sigma> \<Sigma> c1\<^sub>c c1\<^sub>s)
  apply clarsimp
   apply (rule conjId)+   
   apply (simp add: env_sim)
     apply (rule, rule, rule, rule, rule, fast intro: seq_ev_comp_step)      
   apply(rule, rule, rule, rule) apply(auto intro: seq_no_ev_comp_step)
   by (simp add: dest_sim_alpha)
   
    
    
 lemma Seq_sound:
  "\<gamma>\<^sub>a\<subseteq>\<alpha> \<Longrightarrow>  Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow>   \<forall>sn. (sn, sn)\<in>G\<^sub>c \<Longrightarrow> 
  (\<Gamma>\<^sub>c,c1\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>r\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c1\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow>
  (\<Gamma>\<^sub>c,c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c2\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow>
  (\<Gamma>\<^sub>c,Seq c1\<^sub>c c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,Seq c1\<^sub>s c2\<^sub>s,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def apply (auto, rule Seq_sim, auto)
  unfolding RGSim_pre_def by auto


lemma catch_no_ev_comp_step:
  assumes 
   a0:"(\<Gamma>\<^sub>c,(c1\<^sub>c, (a, b), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>) (\<Gamma>\<^sub>s,(c1\<^sub>s, (aa, bb), bc),R\<^sub>s,G\<^sub>s)" and
   a2:"(\<Gamma>\<^sub>c,c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c2\<^sub>s,R\<^sub>s,G\<^sub>s)" and   
   a4:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and
   a5:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Catch c1\<^sub>c c2\<^sub>c, CRef.toSeq ((a, b), ba)) \<rightarrow> (c\<^sub>c', CRef.toSeq ((ab, bd), ba))" and
   a6:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
   shows
       "\<exists>c\<^sub>s' ac be.
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Catch c1\<^sub>s c2\<^sub>s, CRef.toSeq ((aa, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                      (c\<^sub>s', CRef.toSeq ((ac, be), bc)) \<and>
              (((ab, bd), ba), (ac, be), bc) \<in> \<alpha> \<and>
              ((((a, b), ba), (ab, bd), ba), ((aa, bb), bc), (ac, be), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
              ((\<exists>a b bb c1\<^sub>c.
                   c\<^sub>c' = LanguageCon.com.Catch c1\<^sub>c c2\<^sub>c \<and>
                   (\<exists>c1\<^sub>s.
                       c\<^sub>s' = LanguageCon.com.Catch c1\<^sub>s c2\<^sub>s \<and>
                       ac = a \<and>
                       be = b \<and>
                       bc = bb \<and> (\<Gamma>\<^sub>c,(c1\<^sub>c, (ab, bd), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>)
                       (\<Gamma>\<^sub>s,(c1\<^sub>s, (a, b), bb),R\<^sub>s,G\<^sub>s))) \<or>
               (\<Gamma>\<^sub>c,(c\<^sub>c', (ab, bd), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (ac, be), bc),R\<^sub>s,G\<^sub>s))"
 unfolding RGSim_pre_def 
proof(cases "c1\<^sub>c = Skip \<or> c1\<^sub>c = Throw \<or> (\<exists>f. c1\<^sub>c = Fault f) \<or> (c1\<^sub>c = Stuck)")
  let ?\<sigma> = "((a, b), ba)" and ?\<Sigma> = "((aa, bb), bc)" and ?\<sigma>' = "((ab, bd), ba)"
  case True
  {assume a00:"c1\<^sub>c = Skip"         
   then have step_catch:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Catch c1\<^sub>c c2\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (Skip,toSeq ?\<sigma>)"
     using CatchSkipc by auto     
   then have alpha:"c\<^sub>c'=Skip \<and> toSeq ?\<sigma>' = toSeq ?\<sigma>" using a00
     by (metis SmallStepCon.stepc_elim_cases(1) a5 prod.inject 
         stepc_elim_cases_Catch_skip(1) stepce_stepc)         
   obtain s1 s2 where  
      in_alpha:"((?\<sigma>, ?\<sigma>), ?\<Sigma>, ((s1,s2), bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c1\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeq ((s1,s2), bc)) \<and> 
                  (?\<sigma>,  ((s1,s2), bc)) \<in> \<gamma>\<^sub>n" and \<alpha>:"\<gamma>\<^sub>n \<subseteq> \<alpha>"            
     by (insert a0[simplified a00], erule sim_elim_cases_c(1), auto)
   let ?\<Sigma>' = "((s1,s2), bc)"   
   have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Catch c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeq ?\<Sigma>')"    
     using catch_ev_s CatchSkipc in_alpha
     by (metis (no_types, hide_lams) rtranclp.simps) 
   then have ?thesis using in_alpha alpha[simplified  toSeq.simps] Skip_sound[OF \<alpha> a6 a4] \<alpha>
      unfolding toSeq_def RGSim_pre_def by(auto, blast)               
  } 
  moreover { 
    assume a00:"c1\<^sub>c = Throw" 
    then have a00:"c1\<^sub>c = Throw" by auto
    then have step_seq:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Catch c1\<^sub>c c2\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (c2\<^sub>c,toSeq ?\<sigma>)"
      using CatchThrowc by auto 
    then have alpha:"c\<^sub>c'=c2\<^sub>c \<and> toSeq ?\<sigma>' = toSeq ?\<sigma>" using a00
               a5 fst_conv                
      by (metis snd_conv stepc_elim_seq_skip(6) throw1)
    obtain s1 s2 where in_alpha:"((?\<sigma>, ?\<sigma>), ?\<Sigma>,((s1,s2), bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c1\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, toSeq ((s1,s2), bc))" 
         and r:"(?\<sigma>, ((s1,s2), bc)) \<in> \<gamma>\<^sub>r"  and \<alpha>:"\<gamma>\<^sub>r \<subseteq> \<alpha>"       
      by (insert a0[simplified a00], erule sim_elim_cases_c(2), auto)        
    let ?\<Sigma>' = "((s1,s2), bc)"
    have sim: "(\<Gamma>\<^sub>c,(c2\<^sub>c, ?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c2\<^sub>s, ?\<Sigma>'),R\<^sub>s,G\<^sub>s)"
      using a2 in_alpha a00 r unfolding RGSim_pre_def by auto
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Catch c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c2\<^sub>s, toSeq ?\<Sigma>')"       
      by (meson catch_ev_s in_alpha rtranclp.rtrancl_into_rtrancl stepce.CatchThrowc)
    then have ?thesis using a00 alpha in_alpha alpha sim r \<alpha> unfolding toSeq_def by auto 
  }
  moreover { 
    fix f assume a00:"c1\<^sub>c = Fault f"
    then have step_seq:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Catch c1\<^sub>c c2\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (Fault f, toSeq ?\<sigma>)"
      using CatchFaultc by auto
    then have alpha:"c\<^sub>c'=Fault f \<and> toSeq ?\<sigma>' = toSeq ?\<sigma> \<and> ?\<sigma>' = ?\<sigma>"  
      using a00 Pair_inject a5 stepc_elim_seq_skip(8) Fault_ev fst_conv unfolding toSeq_def
      by metis
    obtain s1 s2 where in_alpha:" ((?\<sigma>, ?\<sigma>), ?\<Sigma>, ((s1,s2),bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c1\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq ((s1,s2),bc))" 
           and r:"(?\<sigma>,  ((s1,s2),bc)) \<in> \<alpha>" 
      by (insert a0[simplified a00], erule sim_elim_cases_c(3), auto)
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Catch c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq ((s1,s2),bc))" 
      using catch_ev_s CatchFaultc  
      by (metis (no_types, hide_lams) rtranclp.simps) 
    then have ?thesis using   r step_seq alpha 
      in_alpha    a00 Fault_sim[OF r a4]  unfolding toSeq_def
      by fastforce    
  }
  moreover { 
    assume a00:"c1\<^sub>c = Stuck"
    then have step_seq:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Catch c1\<^sub>c c2\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (Stuck, toSeq ?\<sigma>)"
      using CatchStuckc by auto
    then have alpha:"c\<^sub>c'=Stuck \<and> toSeq ?\<sigma>' = toSeq ?\<sigma> \<and> ?\<sigma>' = ?\<sigma>"  
      using a00 Pair_inject a5 stepc_elim_seq_skip(7) Stuck_ev fst_conv unfolding toSeq_def
      by metis
    obtain s1 s2 where in_alpha:" ((?\<sigma>, ?\<sigma>), ?\<Sigma>, ((s1,s2),bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c1\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, toSeq ((s1,s2),bc))" 
           and r:"(?\<sigma>,  ((s1,s2),bc)) \<in> \<alpha>" 
      by (insert a0[simplified a00], erule sim_elim_cases_c(4), auto)
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Catch c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, toSeq ((s1,s2),bc))" 
      using catch_ev_s CatchStuckc  
      by (metis (no_types, hide_lams) rtranclp.simps) 
    then have ?thesis using   r step_seq alpha 
      in_alpha    a00 Stuck_sim[OF r a4]  unfolding toSeq_def
      by fastforce 
  }
  ultimately show ?thesis using  True by auto       
next
  let ?\<sigma> = "((a, b), ba)" and ?\<Sigma> = "((aa, bb), bc)" and ?\<sigma>' = "((ab, bd), ba)"
  case False 
  then obtain c1'
    where stepc1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c1\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (c1', toSeq ?\<sigma>')" and 
          catch:    "(c\<^sub>c', toSeq ?\<sigma>')= (Catch c1' c2\<^sub>c, toSeq ?\<sigma>')"
    using  SmallStepCon.redex_not_Catch 
           stepc_elim_cases1(14)[OF a5, of "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c1\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (c1', toSeq ?\<sigma>') \<and> 
                                            (c\<^sub>c', toSeq ?\<sigma>')= (Catch c1' c2\<^sub>c,toSeq ?\<sigma>')"]
    by fastforce 
  thus ?thesis 
    using  catch_ev_s stepc1 catch  
    dest_sim_tau_step[of \<Gamma>\<^sub>c c1\<^sub>c ?\<sigma> R\<^sub>c G\<^sub>c \<alpha> \<gamma>\<^sub>n \<gamma>\<^sub>r \<Gamma>\<^sub>s c1\<^sub>s ?\<Sigma> R\<^sub>s G\<^sub>s  _ ?\<sigma>', OF a0 stepc1] 
    unfolding RGSim_pre_def by fastforce
qed  
    
lemma catch_ev_comp_step:
  assumes a0:"(\<Gamma>\<^sub>c,(c1\<^sub>c, (a, b), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>) (\<Gamma>\<^sub>s,(c1\<^sub>s, (aa, bb), bc),R\<^sub>s,G\<^sub>s)" and
        a1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Catch c1\<^sub>c c2\<^sub>c, toSeq ((a, b), ba)) \<rightarrow> (c\<^sub>c', toSeq ((ab, bd), ba))"
      shows "\<exists>c\<^sub>s' ac be.
              (\<exists>a ab b.
                  \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Catch c1\<^sub>s c2\<^sub>s, toSeq ((aa, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                  (\<exists>aa ad ba.
                      \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, ab, b) \<rightarrow> (aa, ad, ba) \<and>
                      \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ad, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((ac, be), bc)))) \<and>
              (((ab, bd), ba), (ac, be), bc) \<in> \<alpha> \<and>
              ((((a, b), ba), (ab, bd), ba), ((aa, bb), bc), (ac, be), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
              ((\<exists>a b bb c1\<^sub>c.
                   c\<^sub>c' = Catch c1\<^sub>c c2\<^sub>c \<and>
                   (\<exists>c1\<^sub>s.
                       c\<^sub>s' = Catch c1\<^sub>s c2\<^sub>s \<and>
                       ac = a \<and>
                       be = b \<and>
                       bc = bb \<and> (\<Gamma>\<^sub>c,(c1\<^sub>c, (ab, bd), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>)
                       (\<Gamma>\<^sub>s,(c1\<^sub>s, (a, b), bb),R\<^sub>s,G\<^sub>s))) \<or>
               (\<Gamma>\<^sub>c,(c\<^sub>c', (ab, bd), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (ac, be), bc),R\<^sub>s,G\<^sub>s))"  
proof-
  have "c1\<^sub>c\<noteq>Skip \<and> c1\<^sub>c\<noteq>Throw" 
    using not_catch_skip_throw_ev a1 by fastforce
  then obtain c1'
     where stepc1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (c1\<^sub>c, toSeq ((a, b), ba)) \<rightarrow> (c1', toSeq ((ab, bd), ba))" and 
          catch:    "(c\<^sub>c', ((ab, bd), ba))= (Catch c1' c2\<^sub>c,  ((ab, bd), ba))" 
    using stepc_elim_cases1(14)[OF a1, of "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (c1\<^sub>c, toSeq ((a, b), ba)) \<rightarrow> 
                                                      (c1', toSeq ((ab, bd), ba)) \<and> 
                                          (c\<^sub>c', toSeq ((ab, bd), ba))= 
                                          (Catch c1' c2\<^sub>c, toSeq ((ab, bd), ba))"]
    by fastforce
  thus ?thesis 
    using  catch_ev_plus stepc1 catch a0
    dest_sim_ev_step[OF a0 stepc1] 
    by fastforce
qed     
  
 lemma Catch_sim:  
  "(\<Gamma>\<^sub>c,(c1\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>) (\<Gamma>\<^sub>s,(c1\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
   (\<Gamma>\<^sub>c,c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c2\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow> Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow>   
   \<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c \<Longrightarrow>
   (\<Gamma>\<^sub>c,(Catch c1\<^sub>c c2\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
   (\<Gamma>\<^sub>s,(Catch c1\<^sub>s c2\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s)"
apply(coinduction arbitrary: \<sigma> \<Sigma> c1\<^sub>c c1\<^sub>s)
  apply clarsimp
   apply (rule conjId)+    
   apply (simp add: env_sim)
   apply (rule, rule, rule, rule, rule) apply(fast intro: catch_ev_comp_step)      
   apply(rule, rule, rule, rule) apply(auto intro: catch_no_ev_comp_step)
  by (simp add: dest_sim_alpha)
    
lemma Catch_sound:
  "\<xi> \<subseteq> \<alpha> \<Longrightarrow> Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow>  \<forall>sn. (sn, sn)\<in>G\<^sub>c \<Longrightarrow> 
  (\<Gamma>\<^sub>c,c1\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>) (\<Gamma>\<^sub>s,c1\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow>
  (\<Gamma>\<^sub>c,c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c2\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow> Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow> 
  (\<Gamma>\<^sub>c,Catch c1\<^sub>c c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,Catch c1\<^sub>s c2\<^sub>s,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def apply (auto, rule Catch_sim, auto)
  unfolding RGSim_pre_def by auto
    
lemma env:
  assumes 
    a1: "(\<sigma>n, \<Sigma>n) \<in> \<xi>" and
    a2: "Sta\<^sub>s \<xi> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>" and  
    a3:"(((\<sigma>n, \<sigma>'), \<Sigma>n, \<Sigma>') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
  shows"(\<sigma>', \<Sigma>') \<in> \<xi> \<or>
        (\<Gamma>\<^sub>c,(c\<^sub>c, \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>'),R\<^sub>s,G\<^sub>s) "
  using sim_env[OF a1 a2 a3] by fastforce
 
 
lemma If_sim:
  assumes 
  a1:"\<xi> \<subseteq> \<alpha>" and 
  a2:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and 
  a3:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and  
  a5:" \<xi> \<subseteq> \<up>((b\<^sub>c \<rightleftharpoons> b\<^sub>s))" and a6:"\<xi>\<^sub>1 = \<xi> \<inter> \<up>(b\<^sub>c \<odot> b\<^sub>s)" and 
  a7:"\<xi>\<^sub>2 = \<xi> \<inter> \<up>((-b\<^sub>c) \<odot> (-b\<^sub>s) )" and  
  a8:"(\<sigma>,\<Sigma>)\<in>\<xi>" and
  a9:"(\<Gamma>\<^sub>c,c1\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c1\<^sub>s,R\<^sub>s,G\<^sub>s)" and 
  a10:"(\<Gamma>\<^sub>c,c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>2\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c2\<^sub>s,R\<^sub>s,G\<^sub>s)"
shows  
  "(\<Gamma>\<^sub>c,(Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Cond b\<^sub>s c1\<^sub>s c2\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s)"
using  a1 a2 a3  a5 a6 a7  a8 a9 a10
  apply(coinduction arbitrary: \<sigma> \<Sigma>)   
proof(clarsimp)
  fix a b ba aa bb bc
  let ?\<sigma> = "((a::'a,b::'b),ba::'b list)" and ?\<Sigma> = "((aa::'c,bb::'d),bc::'d list)"
    assume 
       a0:"(?\<sigma>, ?\<Sigma>) \<in> \<xi>" and              
       a3:"Sta\<^sub>s \<xi> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>" and                            
       a8:"\<xi> \<subseteq> \<alpha>" and                     
       a13:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c"     
    have \<alpha>:"(?\<sigma>, ?\<Sigma>) \<in> \<alpha>" using a0 a8 by fastforce 
    moreover have "\<forall>\<sigma>' \<Sigma>'.
           (((?\<sigma>, \<sigma>'), ?\<Sigma>, \<Sigma>') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>)  \<longrightarrow>
           (\<sigma>', \<Sigma>') \<in> \<xi> \<or>
           (\<Gamma>\<^sub>c,(Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
           (\<Gamma>\<^sub>s,(Cond b\<^sub>s c1\<^sub>s c2\<^sub>s, \<Sigma>'),R\<^sub>s,G\<^sub>s)" 
      using env[OF a0 a3 ] by blast
    moreover have "\<forall>v c\<^sub>c' \<sigma>'.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (c\<^sub>c', toSeq \<sigma>')  \<and> ba = snd \<sigma>' \<longrightarrow>
           (\<exists>c\<^sub>s' \<Sigma>'.
               (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Cond b\<^sub>s c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                      (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq \<Sigma>'))) \<and>
               (\<sigma>', \<Sigma>') \<in> \<alpha> \<and> bc = snd \<Sigma>' \<and>
               (((?\<sigma>, \<sigma>'), ?\<Sigma>,  \<Sigma>') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (c\<^sub>c' = Cond b\<^sub>c c1\<^sub>c c2\<^sub>c \<and>
                c\<^sub>s' = Cond b\<^sub>s c1\<^sub>s c2\<^sub>s \<and> (\<sigma>', \<Sigma>') \<in> \<xi> \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)))"
      by (meson option.discI stepc_elim_cases2(1))
    moreover have "\<forall>c\<^sub>c' \<sigma>'.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (c\<^sub>c', toSeq \<sigma>') \<and> ba = snd \<sigma>' \<longrightarrow>
           (\<exists>c\<^sub>s' \<Sigma>'.
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Cond b\<^sub>s c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq \<Sigma>') \<and>
               (\<sigma>', \<Sigma>') \<in> \<alpha> \<and> bc = snd \<Sigma>' \<and>
               (((?\<sigma>, \<sigma>'), ?\<Sigma>, \<Sigma>') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (c\<^sub>c' = Cond b\<^sub>c c1\<^sub>c c2\<^sub>c \<and>
                c\<^sub>s' = Cond b\<^sub>s c1\<^sub>s c2\<^sub>s \<and> (\<sigma>', \<Sigma>') \<in> \<xi> \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)))"
    proof -
    { fix c\<^sub>c' \<sigma>'
      assume  a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (c\<^sub>c',  toSeq \<sigma>')" and a01:"ba = snd \<sigma>'"
      then have eqs:"?\<sigma> = \<sigma>'"
        using stepc_elim_cases2(1) unfolding toSeq_def
        by (metis prod.exhaust_sel snd_conv) 
      have guar:"((?\<sigma>, ?\<sigma>), ?\<Sigma>, ?\<Sigma>) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
        using  a13 a0 a8  unfolding related_transitions_def Id_def by blast
      have h:"(c\<^sub>c'=c1\<^sub>c \<and> toSeq \<sigma>'\<in>b\<^sub>c) \<or> (c\<^sub>c'=c2\<^sub>c \<and> toSeq \<sigma>'\<in> -b\<^sub>c)"  
        using stepc_elim_cases2(1)[OF a00] eqs unfolding toSeq_def by auto        
      {
        assume c:"c\<^sub>c' = c1\<^sub>c \<and> toSeq \<sigma>' \<in> b\<^sub>c"
        then have sig1:"(\<sigma>',  ?\<Sigma>) \<in> \<xi>\<^sub>1"
          using a0 a5 a6 a7 eqs unfolding eq_rel_def and_rel_def ext_set_def toSeq_def by auto
        then have sn_inb:"toSeq ?\<Sigma> \<in> b\<^sub>s" 
          using a6 unfolding and_rel_def toSeq_def ext_set_def by auto
        then have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Cond b\<^sub>s c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c1\<^sub>s, toSeq ?\<Sigma>)"          
          by (simp add: sn_inb r_into_rtranclp stepce.CondTruec)        
        have x:"(\<Gamma>\<^sub>c,(c1\<^sub>c, \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1\<^sub>s,  ?\<Sigma>),R\<^sub>s,G\<^sub>s)" 
          using a9  sig1
          unfolding RGSim_pre_def
        by blast
        note l = conjI[OF x steps]
      }         
      moreover {
        assume c:"c\<^sub>c' = c2\<^sub>c \<and> toSeq \<sigma>' \<in> -b\<^sub>c"
        then have sig1:"(\<sigma>', ?\<Sigma>) \<in> \<xi>\<^sub>2"
          using a0 a5 a6 a7 eqs unfolding eq_rel_def  and_rel_def ext_set_def toSeq_def by auto
        then have sn_inb:"toSeq ?\<Sigma>\<in>-b\<^sub>s" using a7 unfolding and_rel_def toSeq_def ext_set_def by auto
        then have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Cond b\<^sub>s c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c2\<^sub>s, toSeq ?\<Sigma>)"          
          by (simp add: sn_inb r_into_rtranclp stepce.CondFalsec)        
        have x:"(\<Gamma>\<^sub>c,(c2\<^sub>c, \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c2\<^sub>s, ?\<Sigma>),R\<^sub>s,G\<^sub>s)" 
          using a10  sig1
          unfolding RGSim_pre_def by blast
        note l = conjI[OF x steps]
      } 
      ultimately have "\<exists>c\<^sub>s' \<Sigma>'.
             \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Cond b\<^sub>s c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq \<Sigma>') \<and> snd ?\<Sigma> = snd \<Sigma>' \<and>
             (\<sigma>', \<Sigma>') \<in> \<alpha> \<and>
             (((?\<sigma>, \<sigma>'), ?\<Sigma>, \<Sigma>') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (c\<^sub>c' = Cond b\<^sub>c c1\<^sub>c c2\<^sub>c \<and>
              c\<^sub>s' = Cond b\<^sub>s c1\<^sub>s c2\<^sub>s \<and> (\<sigma>', \<Sigma>') \<in> \<xi> \<or>
              (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s))" 
        using guar  h  eqs \<alpha> by auto   
     } then show ?thesis by auto
   qed     
   ultimately show 
    "(((a, b), ba), (aa, bb), bc) \<in> \<alpha> \<and>
           (\<forall>c\<^sub>c' ab bd.
               \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, CRef.toSeq ((a, b), ba)) \<rightarrow>
                        (c\<^sub>c', CRef.toSeq ((ab, bd), ba)) \<longrightarrow>
               (\<exists>c\<^sub>s' ac be.
                   \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Cond b\<^sub>s c1\<^sub>s c2\<^sub>s, CRef.toSeq ((aa, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                           (c\<^sub>s', CRef.toSeq ((ac, be), bc)) \<and>
                   (((ab, bd), ba), (ac, be), bc) \<in> \<alpha> \<and>
                   ((((a, b), ba), (ab, bd), ba), ((aa, bb), bc), (ac, be), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                   (c\<^sub>c' = LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c \<and>
                    c\<^sub>s' = LanguageCon.com.Cond b\<^sub>s c1\<^sub>s c2\<^sub>s \<and> (((ab, bd), ba), (ac, be), bc) \<in> \<xi> \<or>
                    (\<Gamma>\<^sub>c,(c\<^sub>c', (ab, bd), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                    (\<Gamma>\<^sub>s,(c\<^sub>s', (ac, be), bc),R\<^sub>s,G\<^sub>s)))) \<and>
           (\<forall>v c\<^sub>c' ab bd.
               \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>Some v (LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, CRef.toSeq ((a, b), ba)) \<rightarrow>
                              (c\<^sub>c', CRef.toSeq ((ab, bd), ba)) \<longrightarrow>
               (\<exists>c\<^sub>s' ac be.
                   (\<exists>a ab b.
                       \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Cond b\<^sub>s c1\<^sub>s c2\<^sub>s, CRef.toSeq ((aa, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                               (a, ab, b) \<and>
                       (\<exists>aa ad ba.
                           \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, ab, b) \<rightarrow> (aa, ad, ba) \<and>
                           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ad, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', CRef.toSeq ((ac, be), bc)))) \<and>
                   (((ab, bd), ba), (ac, be), bc) \<in> \<alpha> \<and>
                   ((((a, b), ba), (ab, bd), ba), ((aa, bb), bc), (ac, be), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                   (c\<^sub>c' = LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c \<and>
                    c\<^sub>s' = LanguageCon.com.Cond b\<^sub>s c1\<^sub>s c2\<^sub>s \<and> (((ab, bd), ba), (ac, be), bc) \<in> \<xi> \<or>
                    (\<Gamma>\<^sub>c,(c\<^sub>c', (ab, bd), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                    (\<Gamma>\<^sub>s,(c\<^sub>s', (ac, be), bc),R\<^sub>s,G\<^sub>s)))) \<and>
           (\<forall>ab bd be ac bf bg.
               ((((a, b), ba), (ab, bd), be), ((aa, bb), bc), (ac, bf), bg) \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<longrightarrow>
               (((ab, bd), be), (ac, bf), bg) \<in> \<xi> \<or>
               (\<Gamma>\<^sub>c,(LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, (ab, bd), be),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
               (\<Gamma>\<^sub>s,(LanguageCon.com.Cond b\<^sub>s c1\<^sub>s c2\<^sub>s, (ac, bf), bg),R\<^sub>s,G\<^sub>s))" 
      by auto
  qed    


 
lemma If_sound:
  "\<xi> \<subseteq> \<alpha>  \<Longrightarrow> Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow> 
  \<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c  \<Longrightarrow>
   \<xi> \<subseteq> \<up>(b\<^sub>c \<rightleftharpoons> b\<^sub>s) \<Longrightarrow> \<xi>\<^sub>1= \<xi> \<inter> \<up>(b\<^sub>c \<odot> b\<^sub>s) \<Longrightarrow> \<xi>\<^sub>2= \<xi> \<inter> \<up>((-b\<^sub>c) \<odot> (-b\<^sub>s) ) \<Longrightarrow>
  (\<Gamma>\<^sub>c,c1\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c1\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow> 
  (\<Gamma>\<^sub>c,c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>2\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c2\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow> 
  (\<Gamma>\<^sub>c,Cond b\<^sub>c c1\<^sub>c c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,Cond b\<^sub>s c1\<^sub>s c2\<^sub>s,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def apply (auto,rule If_sim, auto)
  unfolding RGSim_pre_def by auto+

definition coPre 
where 
"coPre \<xi> b\<^sub>c b\<^sub>s \<Gamma>\<^sub>c c1\<^sub>c R\<^sub>c G\<^sub>c \<alpha> \<gamma>\<^sub>n \<gamma>\<^sub>a \<Gamma>\<^sub>s c1\<^sub>s R\<^sub>s G\<^sub>s \<Gamma>\<^sub>c' csc R\<^sub>c' G\<^sub>c' \<alpha>' \<gamma>\<^sub>n' \<gamma>\<^sub>a' \<Gamma>\<^sub>s' css R\<^sub>s' G\<^sub>s' \<equiv>
 \<exists>\<sigma> \<Sigma> c\<^sub>c c\<^sub>s.
   \<Gamma>\<^sub>c' = \<Gamma>\<^sub>c \<and>
   ( (csc = (Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c),  \<sigma>) \<and> 
      css = (Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s),  \<Sigma>) \<and>      
     (\<Gamma>\<^sub>c,(c\<^sub>c,  \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,  \<Sigma>),R\<^sub>s,G\<^sub>s)) \<or>     
    ((csc = (While b\<^sub>c c1\<^sub>c, \<sigma>) \<and> 
     css = (While b\<^sub>s c1\<^sub>s, \<Sigma>) \<and> (\<sigma>,\<Sigma>) \<in>\<xi>)) \<or>
    (csc = (Skip, \<sigma>) \<and> 
     css = (Skip, \<Sigma>) \<and> (\<sigma>,\<Sigma>) \<in> \<xi> \<and> (fst \<sigma>)\<in> (- b\<^sub>c))  \<or>
    (csc = (Throw, \<sigma>) \<and> 
     css = (Throw, \<Sigma>) \<and> (\<sigma>,\<Sigma>) \<in>\<gamma>\<^sub>a ) \<or> 
    (\<exists>f. csc = (Fault f, \<sigma>) \<and> css = (Fault f, \<Sigma>) \<and> (\<sigma>,\<Sigma>) \<in> \<alpha> ) \<or> 
    (csc = (Stuck, \<sigma>) \<and> css = (Stuck,\<Sigma>) \<and> (\<sigma>,\<Sigma>) \<in> \<alpha>)  ) \<and>
   R\<^sub>c' = R\<^sub>c \<and> G\<^sub>c' = G\<^sub>c \<and> \<alpha>' = \<alpha> \<and> \<gamma>\<^sub>n' = \<gamma>\<^sub>n \<and> \<gamma>\<^sub>a' = \<gamma>\<^sub>a \<and> \<Gamma>\<^sub>s' = \<Gamma>\<^sub>s \<and> R\<^sub>s' = R\<^sub>s \<and> G\<^sub>s' = G\<^sub>s "


lemma while_seq_alpha:
  "  \<xi> \<subseteq> \<alpha> \<Longrightarrow> \<gamma>\<^sub>a \<subseteq> \<alpha> \<Longrightarrow> 
    (\<exists>c\<^sub>c. a = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
               aa = ad \<and> b = bd \<and> ba = be \<and>
               (\<exists>c\<^sub>s. ab = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> 
               (\<Gamma>\<^sub>c,(c\<^sub>c, (ad, bd), be),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ae, bf), bg),R\<^sub>s,G\<^sub>s))) \<or>
        a =While b\<^sub>c c1\<^sub>c \<and> aa = ad \<and> b = bd \<and> ba = be \<and> 
          ab = While b\<^sub>s c1\<^sub>s \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<or>
        a = Skip \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Skip \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> 
          (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<and> (ad, bd) \<notin> b\<^sub>c \<or>
        a = Throw \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Throw \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> 
          (((ad, bd), be), (ae, bf), bg) \<in> \<gamma>\<^sub>a \<or>
        (\<exists>f. a = Fault f \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Fault f \<and> 
             ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>) \<or>
        a = Stuck \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Stuck \<and> 
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha> \<Longrightarrow> 
 (((aa, b), ba), (ac, bb), bc) \<in> \<alpha> "  
  by (auto dest: dest_sim_alpha)

lemma while_seq_no_ev1:
  assumes 
  a0:"(\<exists>c\<^sub>c. a = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
               (\<exists>c\<^sub>s. ab = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and>
               (\<Gamma>\<^sub>c,(c\<^sub>c, (aa, b), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ac, bb), bc),R\<^sub>s,G\<^sub>s)))" and
  a1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (a, toSeq ((aa, b), ba)) \<rightarrow> (c\<^sub>c', CRef.toSeq ((af, bh), ba))"
  shows "\<exists>c\<^sub>s' a bd.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((a, bd), bc)) \<and>
          (((af, bh), ba), (a, bd), bc) \<in> \<alpha> \<and>
          (((((aa, b), ba), (af, bh), ba), ((ac, bb), bc), (a, bd), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          ((\<exists>aa b bb ab be bf.
               (\<exists>c\<^sub>c. c\<^sub>c' = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
                      af = aa \<and> bh = b \<and> ba = bb \<and>
                      (\<exists>c\<^sub>s. c\<^sub>s' = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                      (\<Gamma>\<^sub>c,(c\<^sub>c, (aa, b), bb),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ab, be), bf),R\<^sub>s,G\<^sub>s))) \<or>
               c\<^sub>c' = While b\<^sub>c c1\<^sub>c \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                 c\<^sub>s' = While b\<^sub>s c1\<^sub>s \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<or>
               c\<^sub>c' = Skip \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Skip \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<and> (aa, b) \<notin> b\<^sub>c \<or>
               c\<^sub>c' = Throw \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Throw \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<gamma>\<^sub>a \<or>
               (\<exists>f. c\<^sub>c' = Fault f \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                    c\<^sub>s' = Fault f \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                   (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
               c\<^sub>c' = Stuck \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Stuck \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', (af, bh), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (a, bd), bc),R\<^sub>s,G\<^sub>s))" 
proof -
  let ?\<sigma> = "((aa, b), ba)" and ?\<Sigma> = "((ac, bb), bc)" and ?\<sigma>' = "((af, bh), ba)"
  obtain c\<^sub>c c\<^sub>s where 
    a0:"a = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c)  \<and> 
         ab = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and>
         (\<Gamma>\<^sub>c,(c\<^sub>c, ?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, ?\<Sigma>),R\<^sub>s,G\<^sub>s)" 
    using a0 by auto
  then have a14a:"Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) = a" and
            a14c:"ab = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s)"  and
            a14e:"(\<Gamma>\<^sub>c,(c\<^sub>c, ?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, ?\<Sigma>),R\<^sub>s,G\<^sub>s)" and 
            a15:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c), toSeq ?\<sigma>) \<rightarrow> (c\<^sub>c', toSeq ?\<sigma>')" using a1 by auto
  thus ?thesis 
  proof (cases "c\<^sub>c = Skip \<or> c\<^sub>c = Throw \<or> (\<exists>f. c\<^sub>c = Fault f) \<or>  c\<^sub>c = Stuck")
    case True
    {assume a00:"c\<^sub>c = Skip"
      then have step_seq:
        "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c), toSeq ?\<sigma>) \<rightarrow> ((While b\<^sub>c c1\<^sub>c), toSeq ?\<sigma>)"
        using SeqSkipc by auto
      then have alpha:"c\<^sub>c'= (While b\<^sub>c c1\<^sub>c) \<and> ?\<sigma>' = ?\<sigma>" using a00 a0  a1 unfolding toSeq_def
        by (metis fst_conv snd_conv stepc_elim_cases1(1) stepc_elim_seq_skip(1))         
      have ?thesis 
      proof -        
       obtain a1 a2  where 
           in_alpha:"((?\<sigma>, ?\<sigma>), ?\<Sigma>, ((a1,a2),bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
                     \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeq ((a1,a2),bc)) \<and> bc = snd ((a1,a2),bc) \<and> 
                     (?\<sigma>, ((a1,a2),bc)) \<in> \<xi>"       
         using sim_elim_cases_c(1)[OF a14e[simplified a00]] snd_conv apply auto
         by metis
         then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s), toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* ((While b\<^sub>s c1\<^sub>s), toSeq((a1,a2),bc) )"    
           using seq_ev_s SeqSkipc in_alpha
           by (metis (no_types, hide_lams) rtranclp.simps)          
         then show ?thesis using in_alpha  alpha  a14c  
           unfolding related_transitions_def toSeq_def by blast        
      qed        
    } note l1=this  
    moreover {
      assume a00:"c\<^sub>c = Throw"      
      then have step_seq:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c),toSeq ?\<sigma>) \<rightarrow> (Throw, toSeq ?\<sigma>)"
        using SeqThrowc by auto          
      then have alpha:"c\<^sub>c'=Throw \<and> ?\<sigma>' = ?\<sigma>" 
        using a00 a0 a15  
               stepc_elim_cases1(7)[OF a15, of "c\<^sub>c'=Throw \<and> ?\<sigma>' = ?\<sigma>"] a00
        unfolding toSeq_def 
        by (auto dest:stepc_elim_cases1(13))                 
      then obtain s1 s2 where in_alpha:"((?\<sigma>, ?\<sigma>), ?\<Sigma>, ((s1,s2),bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, toSeq ((s1,s2),bc)) " and 
         r:"(?\<sigma>, ((s1,s2),bc)) \<in> \<gamma>\<^sub>a"               
        using a00 a0 sim_elim_cases_c(2)[OF a14e[simplified a00]] snd_conv apply auto
         by metis
      then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s),toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, toSeq ((s1,s2),bc))"         
        using seq_ev_s SeqThrowc            
        by (metis (no_types, hide_lams) rtranclp.simps)           
      then have ?thesis
        using a14c alpha in_alpha r unfolding related_transitions_def toSeq_def by blast           
    }
    moreover {
      assume a00:"c\<^sub>c = Stuck"      
      then have step_seq:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c),toSeq ?\<sigma>) \<rightarrow> (Stuck, toSeq ?\<sigma>)"
        using SeqStuckc by auto          
      then have alpha:"c\<^sub>c'=Stuck \<and> ?\<sigma>' = ?\<sigma>" 
        using a00 a0 a15  
               stepc_elim_cases1(7)[OF a15, of "c\<^sub>c'=Stuck \<and> ?\<sigma>' = ?\<sigma>"] a00
        unfolding toSeq_def 
        by (auto dest:stepc_elim_cases1(3))                 
      then obtain s1 s2 where in_alpha:"((?\<sigma>, ?\<sigma>), ?\<Sigma>, ((s1,s2),bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, toSeq ((s1,s2),bc)) " and 
         r:"(?\<sigma>, ((s1,s2),bc)) \<in> \<alpha>"               
        using a00 a0 sim_elim_cases_c(4)[OF a14e[simplified a00]] snd_conv apply auto
         by metis
      then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s),toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, toSeq ((s1,s2),bc))"         
        using seq_ev_s SeqStuckc            
        by (metis (no_types, hide_lams) rtranclp.simps)           
      then have ?thesis
        using a14c alpha in_alpha r unfolding related_transitions_def toSeq_def by auto           
    }
    moreover { fix f
      assume a00:"c\<^sub>c = Fault f"      
      then have step_seq:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c),toSeq ?\<sigma>) \<rightarrow> (Fault f, toSeq ?\<sigma>)"
        using SeqFaultc by auto          
      then have alpha:"c\<^sub>c'=Fault f \<and> ?\<sigma>' = ?\<sigma>" 
        using a00 a0 a15  
               stepc_elim_cases1(7)[OF a15, of "c\<^sub>c'=Fault f \<and> ?\<sigma>' = ?\<sigma>"] a00
        unfolding toSeq_def 
        by (auto dest:stepc_elim_cases1(2))                 
      then obtain s1 s2 where in_alpha:"((?\<sigma>, ?\<sigma>), ?\<Sigma>, ((s1,s2),bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq ((s1,s2),bc)) " and 
         r:"(?\<sigma>, ((s1,s2),bc)) \<in> \<alpha>"               
        using a00 a0 sim_elim_cases_c(3)[OF a14e[simplified a00]] snd_conv apply auto
         by metis
      then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s),toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq ((s1,s2),bc))"         
        using seq_ev_s SeqFaultc            
        by (metis (no_types, hide_lams) rtranclp.simps)           
      then have ?thesis
        using a14c alpha in_alpha r unfolding related_transitions_def toSeq_def by auto           
    }
    ultimately show ?thesis using l1 True by fastforce
  next
    case False       
    then obtain c\<^sub>c1' 
    where stepc1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (c\<^sub>c1', toSeq ?\<sigma>')" and 
          seq:    "(c\<^sub>c', toSeq ?\<sigma>')= (Seq c\<^sub>c1' (While b\<^sub>c c1\<^sub>c), toSeq ?\<sigma>')"
    using  SmallStepCon.redex_not_Seq 
           stepc_elim_cases1(7)[OF a15, 
             of "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (c\<^sub>c1', toSeq ?\<sigma>') \<and> (c\<^sub>c', ?\<sigma>')= (Seq c\<^sub>c1' (While b\<^sub>c c1\<^sub>c), ?\<sigma>')"]
    by fastforce
  thus ?thesis 
    using  seq_ev_s stepc1 seq a0 
    dest_sim_tau_step[of \<Gamma>\<^sub>c c\<^sub>c ?\<sigma> R\<^sub>c G\<^sub>c \<alpha> \<xi> \<gamma>\<^sub>a \<Gamma>\<^sub>s c\<^sub>s ?\<Sigma> R\<^sub>s G\<^sub>s  _ ?\<sigma>', OF a14e stepc1] 
    unfolding RGSim_pre_def toSeq_def by fastforce      
  qed        
qed    

lemma while_seq_no_ev2:
  assumes 
  a0:"(\<Gamma>\<^sub>c,c1\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c1\<^sub>s,R\<^sub>s,G\<^sub>s)" and    
  a3:"\<xi> \<subseteq> \<alpha>" and a4:" aa = ad \<and> b = bd \<and> ba = be \<and> ac = ae \<and> bb = bf \<and> bc = bg" and 
  a9:"\<xi> \<subseteq> \<up>(b\<^sub>c \<rightleftharpoons> b\<^sub>s)" and
  a10:"\<xi>\<^sub>1 = \<xi> \<inter> \<up>(b\<^sub>c \<odot>  b\<^sub>s)" and
  a13:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and
  a14:"(((aa, b), ba), (ac, bb), bc) \<in> \<xi>" and
  a15:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (While b\<^sub>c c1\<^sub>c,toSeq ((aa, b), ba)) \<rightarrow> (c\<^sub>c', toSeq ((af, bh), ba))"
shows "\<exists>c\<^sub>s' a bd.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.While b\<^sub>s c1\<^sub>s , toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((a, bd), bc)) \<and>
          (((af, bh), ba), (a, bd), bc) \<in> \<alpha> \<and>
          (((((aa, b), ba), (af, bh), ba), ((ac, bb), bc), (a, bd), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          ((\<exists>aa b bb ab be bf.
               (\<exists>c\<^sub>c. c\<^sub>c' = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
                      af = aa \<and> bh = b \<and> ba = bb \<and>
                      (\<exists>c\<^sub>s. c\<^sub>s' = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                      (\<Gamma>\<^sub>c,(c\<^sub>c, (aa, b), bb),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ab, be), bf),R\<^sub>s,G\<^sub>s))) \<or>
               c\<^sub>c' = While b\<^sub>c c1\<^sub>c \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                 c\<^sub>s' = While b\<^sub>s c1\<^sub>s \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<or>
               c\<^sub>c' = Skip \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Skip \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<and> (aa, b) \<notin> b\<^sub>c \<or>
               c\<^sub>c' = Throw \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Throw \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<gamma>\<^sub>a \<or>
               (\<exists>f. c\<^sub>c' = Fault f \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                    c\<^sub>s' = Fault f \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                   (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
               c\<^sub>c' = Stuck \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Stuck \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', (af, bh), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (a, bd), bc),R\<^sub>s,G\<^sub>s))" 
proof-        
  let ?\<sigma> = "((aa, b), ba)" and ?\<Sigma> = "((ac, bb), bc)" and ?\<sigma>' = "((af, bh), ba)"
  { 
    assume sigb:"fst ?\<sigma> \<in> b\<^sub>c" 
    then have s1c1:"?\<sigma>' =  ?\<sigma> \<and> c\<^sub>c' = Seq c1\<^sub>c (LanguageCon.com.While b\<^sub>c c1\<^sub>c)"
      using dest_while a15 unfolding toSeq_def
      by (metis ComplD fst_conv )
    moreover have Sigb:"fst ?\<Sigma> \<in> b\<^sub>s" using calculation sigb same_set a14 a9  by fastforce
    ultimately have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (While b\<^sub>s c1\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Seq c1\<^sub>s (While b\<^sub>s c1\<^sub>s), toSeq ?\<Sigma>)" 
      unfolding toSeq_def 
      by (simp add: r_into_rtranclp stepce.WhileTruec) 
    moreover have "((?\<sigma>, ?\<sigma>'), ?\<Sigma>,  ?\<Sigma>) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>" 
      using a14 a13 s1c1 a3  unfolding related_transitions_def by blast
    moreover have "(\<Gamma>\<^sub>c,(c1\<^sub>c, ?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1\<^sub>s, ?\<Sigma>),R\<^sub>s,G\<^sub>s)"
      using sigb Sigb a14 a0 a10   unfolding RGSim_pre_def and_rel_def ext_set_def  by blast
    ultimately have ?thesis using s1c1  unfolding related_transitions_def by blast  
  } 
  moreover {    
    assume a00: "fst ?\<sigma> \<in> -b\<^sub>c" 
    then have a00':"fst ?\<Sigma> \<in> -b\<^sub>s" using a14 a9 same_set by blast
    then have ?thesis    
    proof -      
      have f5:"(?\<sigma>,?\<Sigma>)\<in>\<alpha>" 
        using a14  a3 by force      
      then have f4: "\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (While b\<^sub>s c1\<^sub>s, fst ?\<Sigma>) \<rightarrow> (Skip, fst ?\<Sigma>)"
        using  stepce.WhileFalsec a00'  unfolding toSeq_def
        by fast         
      have f6: "?\<sigma>' = ?\<sigma> \<and> (fst ?\<sigma> \<in> - b\<^sub>c \<and> c\<^sub>c' = LanguageCon.com.Skip \<or> 
                fst ?\<sigma> \<in> b\<^sub>c \<and> c\<^sub>c' = LanguageCon.com.Seq c1\<^sub>c (LanguageCon.com.While b\<^sub>c c1\<^sub>c))"
        using a15 dest_while unfolding toSeq_def
        by fastforce
      then have "(( ?\<sigma>, ?\<sigma>'), ?\<Sigma>, ?\<Sigma>) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
        using f5 a13 by (simp add:  a13 related_transitions_def Domain.DomainI)
      then show ?thesis
        using a14 f6 f4 a00 unfolding related_transitions_def toSeq_def
        by auto
    qed      
  }
  ultimately show ?thesis by auto
qed

  lemma while_seq_no_ev3:
"a = Skip \<Longrightarrow>
 \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (a, toSeq ((aa, b), ba)) \<rightarrow> (c\<^sub>c',toSeq ((af, bh), ba)) \<Longrightarrow>
  \<exists>c\<^sub>s' a bd.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((a, bd), bc)) \<and>
          (((af, bh), ba), (a, bd), bc) \<in> \<alpha> \<and>
          (((((aa, b), ba), (af, bh), ba), ((ac, bb), bc), (a, bd), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          ((\<exists>aa b bb ab be bf.
               (\<exists>c\<^sub>c. c\<^sub>c' = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
                      af = aa \<and> bh = b \<and> ba = bb \<and>
                      (\<exists>c\<^sub>s. c\<^sub>s' = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                      (\<Gamma>\<^sub>c,(c\<^sub>c, (aa, b), bb),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ab, be), bf),R\<^sub>s,G\<^sub>s))) \<or>
               c\<^sub>c' = While b\<^sub>c c1\<^sub>c \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                 c\<^sub>s' = While b\<^sub>s c1\<^sub>s \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<or>
               c\<^sub>c' = Skip \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Skip \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<and> (aa, b) \<notin> b\<^sub>c \<or>
               c\<^sub>c' = Throw \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Throw \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<gamma>\<^sub>a \<or>
               (\<exists>f. c\<^sub>c' = Fault f \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                    c\<^sub>s' = Fault f \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                   (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
               c\<^sub>c' = Stuck \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Stuck \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', (af, bh), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (a, bd), bc),R\<^sub>s,G\<^sub>s))"  
    using skip1 by auto
            
lemma while_seq_no_ev4:     
 "a = Throw \<Longrightarrow> 
 \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (a, toSeq ((aa, b), ba)) \<rightarrow> (c\<^sub>c',toSeq ((af, bh), ba)) \<Longrightarrow>
  \<exists>c\<^sub>s' a bd.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((a, bd), bc)) \<and>
          (((af, bh), ba), (a, bd), bc) \<in> \<alpha> \<and>
          (((((aa, b), ba), (af, bh), ba), ((ac, bb), bc), (a, bd), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          ((\<exists>aa b bb ab be bf.
               (\<exists>c\<^sub>c. c\<^sub>c' = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
                      af = aa \<and> bh = b \<and> ba = bb \<and>
                      (\<exists>c\<^sub>s. c\<^sub>s' = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                      (\<Gamma>\<^sub>c,(c\<^sub>c, (aa, b), bb),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ab, be), bf),R\<^sub>s,G\<^sub>s))) \<or>
               c\<^sub>c' = While b\<^sub>c c1\<^sub>c \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                 c\<^sub>s' = While b\<^sub>s c1\<^sub>s \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<or>
               c\<^sub>c' = Skip \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Skip \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<and> (aa, b) \<notin> b\<^sub>c \<or>
               c\<^sub>c' = Throw \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Throw \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<gamma>\<^sub>a \<or>
               (\<exists>f. c\<^sub>c' = Fault f \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                    c\<^sub>s' = Fault f \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                   (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
               c\<^sub>c' = Stuck \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Stuck \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', (af, bh), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (a, bd), bc),R\<^sub>s,G\<^sub>s))"  
    using throw1 by auto


lemma while_seq_no_ev5:
  "a = Fault f \<Longrightarrow> 
 \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (a, toSeq ((aa, b), ba)) \<rightarrow> (c\<^sub>c',toSeq ((af, bh), ba)) \<Longrightarrow>
  \<exists>c\<^sub>s' a bd.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((a, bd), bc)) \<and>
          (((af, bh), ba), (a, bd), bc) \<in> \<alpha> \<and>
          (((((aa, b), ba), (af, bh), ba), ((ac, bb), bc), (a, bd), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          ((\<exists>aa b bb ab be bf.
               (\<exists>c\<^sub>c. c\<^sub>c' = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
                      af = aa \<and> bh = b \<and> ba = bb \<and>
                      (\<exists>c\<^sub>s. c\<^sub>s' = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                      (\<Gamma>\<^sub>c,(c\<^sub>c, (aa, b), bb),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ab, be), bf),R\<^sub>s,G\<^sub>s))) \<or>
               c\<^sub>c' = While b\<^sub>c c1\<^sub>c \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                 c\<^sub>s' = While b\<^sub>s c1\<^sub>s \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<or>
               c\<^sub>c' = Skip \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Skip \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<and> (aa, b) \<notin> b\<^sub>c \<or>
               c\<^sub>c' = Throw \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Throw \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<gamma>\<^sub>a \<or>
               (\<exists>f. c\<^sub>c' = Fault f \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                    c\<^sub>s' = Fault f \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                   (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
               c\<^sub>c' = Stuck \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Stuck \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', (af, bh), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (a, bd), bc),R\<^sub>s,G\<^sub>s))"  
    using Fault_ev by auto

lemma while_seq_no_ev6:
  "a = Stuck \<Longrightarrow>
 \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (a, toSeq ((aa, b), ba)) \<rightarrow> (c\<^sub>c',toSeq ((af, bh), ba)) \<Longrightarrow>
  \<exists>c\<^sub>s' a bd.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((a, bd), bc)) \<and>
          (((af, bh), ba), (a, bd), bc) \<in> \<alpha> \<and>
          (((((aa, b), ba), (af, bh), ba), ((ac, bb), bc), (a, bd), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          ((\<exists>aa b bb ab be bf.
               (\<exists>c\<^sub>c. c\<^sub>c' = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
                      af = aa \<and> bh = b \<and> ba = bb \<and>
                      (\<exists>c\<^sub>s. c\<^sub>s' = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                      (\<Gamma>\<^sub>c,(c\<^sub>c, (aa, b), bb),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ab, be), bf),R\<^sub>s,G\<^sub>s))) \<or>
               c\<^sub>c' = While b\<^sub>c c1\<^sub>c \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                 c\<^sub>s' = While b\<^sub>s c1\<^sub>s \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<or>
               c\<^sub>c' = Skip \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Skip \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<and> (aa, b) \<notin> b\<^sub>c \<or>
               c\<^sub>c' = Throw \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Throw \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<gamma>\<^sub>a \<or>
               (\<exists>f. c\<^sub>c' = Fault f \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                    c\<^sub>s' = Fault f \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                   (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
               c\<^sub>c' = Stuck \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Stuck \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', (af, bh), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (a, bd), bc),R\<^sub>s,G\<^sub>s))"  
    using Stuck_ev by auto

lemma while_seq_no_ev:
  assumes 
  a0:"(\<Gamma>\<^sub>c,c1\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c1\<^sub>s,R\<^sub>s,G\<^sub>s)" and    
  a3:"\<xi> \<subseteq> \<alpha>" and a4':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and  
  a5:"Sta\<^sub>s \<gamma>\<^sub>a (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>" and    
  a8:"\<xi> \<subseteq> \<up>(b\<^sub>c \<rightleftharpoons>  b\<^sub>s)" and
  a9:"\<xi>\<^sub>1 = \<xi> \<inter> \<up>(b\<^sub>c \<odot>  b\<^sub>s)" and    
  a12:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and
  a13:"(\<exists>c\<^sub>c. a = LanguageCon.com.Seq c\<^sub>c (LanguageCon.com.While b\<^sub>c c1\<^sub>c) \<and>
               aa = ad \<and>
               b = bd \<and>
               ba = be \<and>
               (\<exists>c\<^sub>s. ab = LanguageCon.com.Seq c\<^sub>s (LanguageCon.com.While b\<^sub>s c1\<^sub>s) \<and>
                      ac = ae \<and>
                      bb = bf \<and>
                      bc = bg \<and> (\<Gamma>\<^sub>c,(c\<^sub>c, (ad, bd), be),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                      (\<Gamma>\<^sub>s,(c\<^sub>s, (ae, bf), bg),R\<^sub>s,G\<^sub>s))) \<or>
        a = LanguageCon.com.While b\<^sub>c c1\<^sub>c \<and>
        aa = ad \<and>
        b = bd \<and>
        ba = be \<and>
        ab = LanguageCon.com.While b\<^sub>s c1\<^sub>s \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<or>
        a = LanguageCon.com.Skip \<and>
        aa = ad \<and>
        b = bd \<and>
        ba = be \<and>
        ab = LanguageCon.com.Skip \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<and> (ad, bd) \<notin> b\<^sub>c \<or>
        a = LanguageCon.com.Throw \<and>
        aa = ad \<and>
        b = bd \<and>
        ba = be \<and>
        ab = LanguageCon.com.Throw \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<gamma>\<^sub>a \<or>
        (\<exists>f. a = com.Fault f \<and>
             aa = ad \<and>
             b = bd \<and>
             ba = be \<and>
             ab = com.Fault f \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>) \<or>
        a = com.Stuck \<and>
        aa = ad \<and>
        b = bd \<and>
        ba = be \<and> ab = com.Stuck \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>" and
  a14:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (a, toSeq ((aa, b), ba)) \<rightarrow> (c\<^sub>c',toSeq ((af, bh), ba))"
  shows "\<exists>c\<^sub>s' a bd.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((a, bd), bc)) \<and>
          (((af, bh), ba), (a, bd), bc) \<in> \<alpha> \<and>
          (((((aa, b), ba), (af, bh), ba), ((ac, bb), bc), (a, bd), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          ((\<exists>aa b bb ab be bf.
               (\<exists>c\<^sub>c. c\<^sub>c' = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
                      af = aa \<and> bh = b \<and> ba = bb \<and>
                      (\<exists>c\<^sub>s. c\<^sub>s' = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                      (\<Gamma>\<^sub>c,(c\<^sub>c, (aa, b), bb),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ab, be), bf),R\<^sub>s,G\<^sub>s))) \<or>
               c\<^sub>c' = While b\<^sub>c c1\<^sub>c \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                 c\<^sub>s' = While b\<^sub>s c1\<^sub>s \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<or>
               c\<^sub>c' = Skip \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Skip \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<and> (aa, b) \<notin> b\<^sub>c \<or>
               c\<^sub>c' = Throw \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Throw \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<gamma>\<^sub>a \<or>
               (\<exists>f. c\<^sub>c' = Fault f \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                    c\<^sub>s' = Fault f \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                   (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
               c\<^sub>c' = Stuck \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Stuck \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', (af, bh), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (a, bd), bc),R\<^sub>s,G\<^sub>s))"  
  
proof- 
  show ?thesis using a13 a14 apply auto 
    using while_seq_no_ev1[OF _  a14, of b\<^sub>c c1\<^sub>c ab b\<^sub>s c1\<^sub>s ] apply auto[1]    
    apply (auto  intro: while_seq_no_ev2[OF a0 a3 _  a8 a9 a12 _] simp: a14)
       apply (frule  while_seq_no_ev3[OF  _ a14, of \<Gamma>\<^sub>s ab ac bb bc \<alpha> G\<^sub>c G\<^sub>s b\<^sub>c c1\<^sub>c b\<^sub>s c1\<^sub>s R\<^sub>c \<xi> \<gamma>\<^sub>a R\<^sub>s], simp)
    apply (frule while_seq_no_ev4[OF  _ a14, of \<Gamma>\<^sub>s ab ac bb bc \<alpha> G\<^sub>c G\<^sub>s b\<^sub>c c1\<^sub>c b\<^sub>s c1\<^sub>s R\<^sub>c \<xi> \<gamma>\<^sub>a R\<^sub>s], simp)
 apply (frule while_seq_no_ev5[OF  _ a14, of _ \<Gamma>\<^sub>s ab ac bb bc \<alpha> G\<^sub>c G\<^sub>s b\<^sub>c c1\<^sub>c b\<^sub>s c1\<^sub>s R\<^sub>c \<xi> \<gamma>\<^sub>a R\<^sub>s],simp)
    by(frule  while_seq_no_ev6[OF  _ a14, of \<Gamma>\<^sub>s ab ac bb bc \<alpha> G\<^sub>c G\<^sub>s b\<^sub>c c1\<^sub>c b\<^sub>s c1\<^sub>s R\<^sub>c \<xi> \<gamma>\<^sub>a R\<^sub>s],simp)
qed

lemma while_seq_ev:
   assumes
 a12:"(\<exists>c\<^sub>c. a = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
               aa = ad \<and> b = bd \<and> ba = be \<and>
               (\<exists>c\<^sub>s. ab = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and>
                      ac = ae \<and>
                      bb = bf \<and>
                      bc = bg \<and> (\<Gamma>\<^sub>c,(c\<^sub>c, (ad, bd), be),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                      (\<Gamma>\<^sub>s,(c\<^sub>s, (ae, bf), bg),R\<^sub>s,G\<^sub>s))) \<or>
        a = While b\<^sub>c c1\<^sub>c \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = While b\<^sub>s c1\<^sub>s \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<or>
        a = Skip \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Skip \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<and> (ad, bd) \<notin> b\<^sub>c \<or>
        a = Throw \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Throw \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> 
            (((ad, bd), be), (ae, bf), bg) \<in> \<gamma>\<^sub>a \<or>
        (\<exists>f. a = Fault f \<and> aa = ad \<and> b = bd \<and> ba = be \<and>
             ab = Fault f \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>) \<or>
        a = Stuck \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Stuck \<and> 
             ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>"
 shows "\<forall>v c\<^sub>c' ad bd.
       \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>Some v (a, toSeq ((aa, b), ba)) \<rightarrow> (c\<^sub>c', toSeq ((ad, bd), ba)) \<longrightarrow>
       (\<exists>c\<^sub>s' a be.
           (\<exists>aa ad b.
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (aa, ad, b) \<and>
               (\<exists>ab ac ba.
                   \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (aa, ad, b) \<rightarrow> (ab, ac, ba) \<and>
                   \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, ac, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((a, be), bc)))) \<and>
           (((ad, bd), ba), (a, be), bc) \<in> \<alpha> \<and>
           ((((aa, b), ba), (ad, bd), ba), ((ac, bb), bc), (a, be), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
           ((\<exists>aa b bb ab bf bg.
                (\<exists>c\<^sub>c. c\<^sub>c' = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and> ad = aa \<and> bd = b \<and> ba = bb \<and>
                     (\<exists>c\<^sub>s. c\<^sub>s' = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and> a = ab \<and> be = bf \<and> bc = bg \<and> 
                      (\<Gamma>\<^sub>c,(c\<^sub>c, (aa, b), bb),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ab, bf), bg),R\<^sub>s,G\<^sub>s))) \<or>
                c\<^sub>c' = While b\<^sub>c c1\<^sub>c \<and> ad = aa \<and> bd = b \<and> ba = bb \<and> 
                c\<^sub>s' = While b\<^sub>s c1\<^sub>s \<and> a = ab \<and> be = bf \<and> bc = bg \<and> 
                  (((aa, b), bb), (ab, bf), bg) \<in> \<xi> \<or>
                c\<^sub>c' = Skip \<and> ad = aa \<and> bd = b \<and> ba = bb \<and>
                c\<^sub>s' = Skip \<and> a = ab \<and> be = bf \<and> bc = bg \<and> 
                   (((aa, b), bb), (ab, bf), bg) \<in> \<xi> \<and> (aa, b) \<notin> b\<^sub>c \<or>
                c\<^sub>c' = Throw \<and> ad = aa \<and> bd = b \<and> ba = bb \<and>
                c\<^sub>s' = Throw \<and> a = ab \<and> be = bf \<and> bc = bg \<and> (((aa, b), bb), (ab, bf), bg) \<in> \<gamma>\<^sub>a \<or>
                (\<exists>f. c\<^sub>c' = Fault f \<and> ad = aa \<and> bd = b \<and> ba = bb \<and>
                     c\<^sub>s' = Fault f \<and> a = ab \<and> be = bf \<and> bc = bg \<and> 
                     (((aa, b), bb), (ab, bf), bg) \<in> \<alpha>) \<or>
                c\<^sub>c' = Stuck \<and> ad = aa \<and> bd = b \<and> ba = bb \<and>
                c\<^sub>s' = Stuck \<and> a = ab \<and> be = bf \<and> bc = bg \<and> (((aa, b), bb), (ab, bf), bg) \<in> \<alpha>) \<or>
            (\<Gamma>\<^sub>c,(c\<^sub>c', (ad, bd), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (a, be), bc),R\<^sub>s,G\<^sub>s)))" (is ?goal)     
   using a12 
 proof (auto)
   fix v c\<^sub>c' ada bda  c\<^sub>c c\<^sub>s
   assume a0:"(\<Gamma>\<^sub>c,(c\<^sub>c, (ad, bd), be),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ae, bf), bg),R\<^sub>s,G\<^sub>s)" and
            a1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c), toSeq ((ad, bd), be)) \<rightarrow> (c\<^sub>c', toSeq ((ada, bda), be))"     
   have "c\<^sub>c \<noteq> Throw \<and> c\<^sub>c \<noteq> Skip" 
    using a1 not_seq_skip_throw_ev by fastforce
   then obtain c1'
    where stepc1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) ( c\<^sub>c, toSeq ((ad, bd), be)) \<rightarrow> (c1', toSeq ((ada, bda), be))" and 
          seq:    "(c\<^sub>c',toSeq ((ada, bda), be))= (Seq c1' (While b\<^sub>c c1\<^sub>c),toSeq ((ada, bda), be))" 
     using stepc_elim_cases1(7)[OF a1[simplified ], of "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) ( c\<^sub>c, toSeq ((ad, bd), be)) \<rightarrow> 
                  (c1', toSeq ((ada, bda), be)) \<and> 
                 (c\<^sub>c',toSeq ((ada, bda), be))= (Seq c1' (While b\<^sub>c c1\<^sub>c),toSeq ((ada, bda), be))"]
     by fastforce    
    then show " \<exists>c\<^sub>s' a bea.
              (\<exists>aa ad b.
                  \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq c\<^sub>s (LanguageCon.com.While b\<^sub>s c1\<^sub>s),
                           CRef.toSeq ((ae, bf), bg)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                          (aa, ad, b) \<and>
                  (\<exists>ab ac ba.
                      \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (aa, ad, b) \<rightarrow> (ab, ac, ba) \<and>
                      \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, ac, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', CRef.toSeq ((a, bea), bg)))) \<and>
              (((ada, bda), be), (a, bea), bg) \<in> \<alpha> \<and>
              ((((ad, bd), be), (ada, bda), be), ((ae, bf), bg), (a, bea), bg) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
              ((\<exists>aa b bb ab bf bga.
                   (\<exists>c\<^sub>c. c\<^sub>c' = LanguageCon.com.Seq c\<^sub>c (LanguageCon.com.While b\<^sub>c c1\<^sub>c) \<and>
                          ada = aa \<and>
                          bda = b \<and>
                          be = bb \<and>
                          (\<exists>c\<^sub>s. c\<^sub>s' = LanguageCon.com.Seq c\<^sub>s (LanguageCon.com.While b\<^sub>s c1\<^sub>s) \<and>
                                 a = ab \<and>
                                 bea = bf \<and>
                                 bg = bga \<and> (\<Gamma>\<^sub>c,(c\<^sub>c, (aa, b), bb),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                                 (\<Gamma>\<^sub>s,(c\<^sub>s, (ab, bf), bga),R\<^sub>s,G\<^sub>s))) \<or>
                   c\<^sub>c' = LanguageCon.com.While b\<^sub>c c1\<^sub>c \<and>
                   ada = aa \<and>
                   bda = b \<and>
                   be = bb \<and>
                   c\<^sub>s' = LanguageCon.com.While b\<^sub>s c1\<^sub>s \<and>
                   a = ab \<and> bea = bf \<and> bg = bga \<and> (((aa, b), bb), (ab, bf), bga) \<in> \<xi> \<or>
                   c\<^sub>c' = LanguageCon.com.Skip \<and>
                   ada = aa \<and>
                   bda = b \<and>
                   be = bb \<and>
                   c\<^sub>s' = LanguageCon.com.Skip \<and>
                   a = ab \<and> bea = bf \<and> bg = bga \<and> (((aa, b), bb), (ab, bf), bga) \<in> \<xi> \<and> (aa, b) \<notin> b\<^sub>c \<or>
                   c\<^sub>c' = LanguageCon.com.Throw \<and>
                   ada = aa \<and>
                   bda = b \<and>
                   be = bb \<and>
                   c\<^sub>s' = LanguageCon.com.Throw \<and>
                   a = ab \<and> bea = bf \<and> bg = bga \<and> (((aa, b), bb), (ab, bf), bga) \<in> \<gamma>\<^sub>a \<or>
                   (\<exists>f. c\<^sub>c' = com.Fault f \<and>
                        ada = aa \<and>
                        bda = b \<and>
                        be = bb \<and>
                        c\<^sub>s' = com.Fault f \<and>
                        a = ab \<and> bea = bf \<and> bg = bga \<and> (((aa, b), bb), (ab, bf), bga) \<in> \<alpha>) \<or>
                   c\<^sub>c' = com.Stuck \<and>
                   ada = aa \<and>
                   bda = b \<and>
                   be = bb \<and>
                   c\<^sub>s' = com.Stuck \<and> a = ab \<and> bea = bf \<and> bg = bga \<and> (((aa, b), bb), (ab, bf), bga) \<in> \<alpha>) \<or>
               (\<Gamma>\<^sub>c,(c\<^sub>c', (ada, bda), be),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
               (\<Gamma>\<^sub>s,(c\<^sub>s', (a, bea), bg),R\<^sub>s,G\<^sub>s))"
      using  seq_ev_plus stepc1 seq a0 dest_sim_ev_step[OF a0 stepc1] apply auto
      by fast
  qed(auto elim:  stepc_elim_cases1(9) intro: skip1 throw1 Fault_ev Stuck_ev)

  
lemma dest_sta:"Sta\<^sub>s r R \<Longrightarrow> ((x1,y1),(x2,y2))\<in>R \<Longrightarrow> (x1,x2) \<in> r \<Longrightarrow> (y1,y2)\<in> r"
  unfolding Sta\<^sub>s_def by auto

lemma not_stable_false: assumes a0:"Sta\<^sub>s (\<xi> \<inter> \<up>((- b\<^sub>c) \<odot>  (- b\<^sub>s))) (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>" and
         a2:"\<xi> \<subseteq> \<up>(b\<^sub>c \<rightleftharpoons>  b\<^sub>s)" and
     a3:"((((ad, bd), be), (af, bh), bi), ((ae, bf), bg), (ag, bj), bk) \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>"
    and a4:"(((ad, bd), be), (ae, bf), bg) \<in> \<xi>" and a5:"(ad, bd) \<notin> b\<^sub>c" and a6:"(af, bh) \<in> b\<^sub>c"
  shows "False"
proof-
  have "(ae,bf) \<notin> b\<^sub>s" using a5 a4 a2 unfolding eq_rel_def ext_set_def by auto
  then have d:"(((ad, bd), be), (ae, bf), bg)\<in> (\<xi> \<inter> \<up>((- b\<^sub>c) \<odot>  (- b\<^sub>s)))" 
    using a4 a5 unfolding  and_rel_def ext_set_def by fastforce
  then have "(((af, bh), bi),  (ag, bj), bk) \<in> (\<xi> \<inter> \<up>((- b\<^sub>c) \<odot>  (- b\<^sub>s)))"
    using dest_sta[OF a0 a3 d] by auto
  thus ?thesis using a6 unfolding and_rel_def ext_set_def by auto
qed


lemma while_seq_env:"
       \<xi> \<subseteq> \<alpha> \<Longrightarrow> \<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c \<Longrightarrow>
       Sta\<^sub>s \<xi> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow>
       Sta\<^sub>s \<gamma>\<^sub>a (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow>
       Sta\<^sub>s (\<xi> \<inter> \<up>((- b\<^sub>c) \<odot>  (- b\<^sub>s))) (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow> 
       \<xi>1 = (\<xi> \<inter> \<up>((- b\<^sub>c) \<odot>  (- b\<^sub>s))) \<Longrightarrow>     
       \<xi> \<subseteq> \<up>(b\<^sub>c \<rightleftharpoons>  b\<^sub>s) \<Longrightarrow>             
       (\<exists>c\<^sub>c. a = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
               aa = ad \<and> b = bd \<and> ba = be \<and>
               (\<exists>c\<^sub>s. ab = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and>
                      ac = ae \<and>
                      bb = bf \<and>
                      bc = bg \<and> (\<Gamma>\<^sub>c,(c\<^sub>c, (ad, bd), be),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                      (\<Gamma>\<^sub>s,(c\<^sub>s, (ae, bf), bg),R\<^sub>s,G\<^sub>s))) \<or>
        a = While b\<^sub>c c1\<^sub>c \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = While b\<^sub>s c1\<^sub>s \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<or>
        a = Skip \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Skip \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<and> (ad, bd) \<notin> b\<^sub>c \<or>
        a = Throw \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Throw \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> 
            (((ad, bd), be), (ae, bf), bg) \<in> \<gamma>\<^sub>a \<or>
        (\<exists>f. a = Fault f \<and> aa = ad \<and> b = bd \<and> ba = be \<and>
             ab = Fault f \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>) \<or>
        a = Stuck \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Stuck \<and> 
             ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha> \<Longrightarrow> 
   ((((aa, b), ba), (af, bh), bi), ((ac, bb), bc), (ag, bj), bk) \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow>
    (\<exists>aa b ba ac bb bc.
               (\<exists>c\<^sub>c. a = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and> af = aa \<and> bh = b \<and>
                      bi = ba \<and>
                      (\<exists>c\<^sub>s. ab = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and> ag = ac \<and> bj = bb \<and> bk = bc \<and> 
                      (\<Gamma>\<^sub>c,(c\<^sub>c, (aa, b), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ac, bb), bc),R\<^sub>s,G\<^sub>s))) \<or>
               a = While b\<^sub>c c1\<^sub>c \<and> af = aa \<and>
               bh = b \<and> bi = ba \<and> ab = While b\<^sub>s c1\<^sub>s \<and>
               ag = ac \<and> bj = bb \<and> bk = bc \<and> (((aa, b), ba), (ac, bb), bc) \<in> \<xi> \<or>
               a = Skip \<and> af = aa \<and> bh = b \<and> bi = ba \<and>
               ab = Skip \<and>
               ag = ac \<and> bj = bb \<and> bk = bc \<and> (((aa, b), ba), (ac, bb), bc) \<in> \<xi> \<and> (aa, b) \<notin> b\<^sub>c \<or>
               a = Throw \<and> af = aa \<and> bh = b \<and> bi = ba \<and> ab = Throw \<and>
               ag = ac \<and> bj = bb \<and> bk = bc \<and> (((aa, b), ba), (ac, bb), bc) \<in> \<gamma>\<^sub>a \<or>
               (\<exists>f. a = Fault f \<and> af = aa \<and> bh = b \<and> bi = ba \<and>
                    ab = Fault f \<and> ag = ac \<and> bj = bb \<and> bk = bc \<and> (((aa, b), ba), (ac, bb), bc) \<in> \<alpha>) \<or>
               a = Stuck \<and> af = aa \<and> bh = b \<and> bi = ba \<and>
               ab = Stuck \<and> ag = ac \<and> bj = bb \<and> bk = bc \<and> (((aa, b), ba), (ac, bb), bc) \<in> \<alpha>) \<or>
       (\<Gamma>\<^sub>c, (a, (af, bh), bi),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>1\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(ab, (ag, bj), bk),R\<^sub>s,G\<^sub>s)"  
  apply auto 
        apply (metis dest_sim_env_step) 
     apply (auto dest:sim_env intro: not_stable_false)            
  by (auto simp add:  related_transitions_def)
  

lemma while_seq_skip: 
assumes        
       a3:"\<xi> \<subseteq> \<alpha>" and                            
       a8:"\<xi> \<subseteq>  \<up>(b\<^sub>c \<rightleftharpoons>  b\<^sub>s)" and       
       a12:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and
       a13:"(\<exists>c\<^sub>c. a = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
               aa = ad \<and> b = bd \<and> ba = be \<and>
               (\<exists>c\<^sub>s. ab = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and>
                      ac = ae \<and>
                      bb = bf \<and>
                      bc = bg \<and> (\<Gamma>\<^sub>c,(c\<^sub>c, (ad, bd), be),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                      (\<Gamma>\<^sub>s,(c\<^sub>s, (ae, bf), bg),R\<^sub>s,G\<^sub>s))) \<or>
        a = While b\<^sub>c c1\<^sub>c \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = While b\<^sub>s c1\<^sub>s \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<or>
        a = Skip \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Skip \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<and> (ad, bd) \<notin> b\<^sub>c \<or>
        a = Throw \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Throw \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> 
            (((ad, bd), be), (ae, bf), bg) \<in> \<gamma>\<^sub>a \<or>
        (\<exists>f. a = Fault f \<and> aa = ad \<and> b = bd \<and> ba = be \<and>
             ab = Fault f \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>) \<or>
        a = Stuck \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Stuck \<and> 
             ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>" and
      a14:"a = Skip "
       shows
        " \<exists>a bd.
              ((((aa, b), ba), (aa, b), ba), ((ac, bb), bc), (a, bd), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
              (((aa, b), ba), (a, bd), bc) \<in> \<xi> \<and>
              (((aa, b), ba), (a, bd), bc) \<in> \<up>((- b\<^sub>c) \<odot>  (- b\<^sub>s)) \<and>
              \<xi> \<inter> \<up>((- b\<^sub>c) \<odot>  (- b\<^sub>s)) \<subseteq> \<alpha> \<and>
              (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeq ((a, bd), bc)))"        
proof -       
  have "a = LanguageCon.com.Skip \<and>
        ab = LanguageCon.com.Skip \<and>
      (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<and> (ad, bd) \<notin> b\<^sub>c "
    using a14 a13 by auto
 
  have "((((ad, bd), be), ((ad, bd), be)),(((ae, bf), bg), ((ae, bf), bg))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>" 
  proof -
    have "(((ad, bd), be), (ae, bf), bg) \<in> \<alpha>"
      using a3 a14 a13  by auto    
    then show ?thesis
      by (simp add:a12 alpha_id_G  related_transitions_def Domain.DomainI)
  qed  
  moreover have "(((ad, bd), be), (ae, bf), bg) \<in> \<up>((- b\<^sub>c) \<odot>  (- b\<^sub>s))"
     using a8 calculation a13 a14   unfolding and_rel_def ext_set_def eq_rel_def 
     by fastforce   
  ultimately show  " \<exists>a bd.
              ((((aa, b), ba), (aa, b), ba), ((ac, bb), bc), (a, bd), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
              (((aa, b), ba), (a, bd), bc) \<in> \<xi> \<and>
              (((aa, b), ba), (a, bd), bc) \<in> \<up>((- b\<^sub>c) \<odot>  (- b\<^sub>s)) \<and>
              \<xi> \<inter> \<up>((- b\<^sub>c) \<odot>  (- b\<^sub>s)) \<subseteq> \<alpha> \<and>
              (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeq ((a, bd), bc)))"   
     using a3 a13 a14  by auto
 qed        

lemma while_seq_throw: 
assumes        
       a3:"\<xi> \<subseteq> \<alpha>" and a3':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and                            
       a12:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and
       a13:"(\<exists>c\<^sub>c. a = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
               aa = ad \<and> b = bd \<and> ba = be \<and>
               (\<exists>c\<^sub>s. ab = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and>
                      ac = ae \<and>
                      bb = bf \<and>
                      bc = bg \<and> (\<Gamma>\<^sub>c,(c\<^sub>c, (ad, bd), be),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                      (\<Gamma>\<^sub>s,(c\<^sub>s, (ae, bf), bg),R\<^sub>s,G\<^sub>s))) \<or>
        a = While b\<^sub>c c1\<^sub>c \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = While b\<^sub>s c1\<^sub>s \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<or>
        a = Skip \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Skip \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<and> (ad, bd) \<notin> b\<^sub>c \<or>
        a = Throw \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Throw \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> 
            (((ad, bd), be), (ae, bf), bg) \<in> \<gamma>\<^sub>a \<or>
        (\<exists>f. a = Fault f \<and> aa = ad \<and> b = bd \<and> ba = be \<and>
             ab = Fault f \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>) \<or>
        a = Stuck \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Stuck \<and> 
             ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>" and 
     a14:"a = LanguageCon.com.Throw "
       shows
        "\<exists>a bd.
                ((((aa, b), ba), (aa, b), ba), ((ac, bb), bc), (a, bd), bc) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                (((aa, b), ba), (a, bd), bc) \<in> \<gamma>\<^sub>a \<and>
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, CRef.toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                        (LanguageCon.com.Throw, CRef.toSeq ((a, bd), bc))"
        
proof -  
  
  have "((((ad, bd), be), ((ad, bd), be)),(((ae, bf), bg), ((ae, bf), bg))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>" 
  proof -
    have "(((ad, bd), be), (ae, bf), bg) \<in> \<alpha>"
      using a3' a14 a13  by auto    
    then show ?thesis
      by (simp add:a12 alpha_id_G  related_transitions_def DomainI)
   qed    
   then show "\<exists>a bd.
                ((((aa, b), ba), (aa, b), ba), ((ac, bb), bc), (a, bd), bc) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                (((aa, b), ba), (a, bd), bc) \<in> \<gamma>\<^sub>a \<and>
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, CRef.toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                        (LanguageCon.com.Throw, CRef.toSeq ((a, bd), bc))" 
     using a3 a3' a14 a13   by fastforce 
 qed        


lemma while_seq_fault: 
assumes                                           
       a12:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and
       a13:"(\<exists>c\<^sub>c. a = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
               aa = ad \<and> b = bd \<and> ba = be \<and>
               (\<exists>c\<^sub>s. ab = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and>
                      ac = ae \<and>
                      bb = bf \<and>
                      bc = bg \<and> (\<Gamma>\<^sub>c,(c\<^sub>c, (ad, bd), be),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                      (\<Gamma>\<^sub>s,(c\<^sub>s, (ae, bf), bg),R\<^sub>s,G\<^sub>s))) \<or>
        a = While b\<^sub>c c1\<^sub>c \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = While b\<^sub>s c1\<^sub>s \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<or>
        a = Skip \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Skip \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<and> (ad, bd) \<notin> b\<^sub>c \<or>
        a = Throw \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Throw \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> 
            (((ad, bd), be), (ae, bf), bg) \<in> \<gamma>\<^sub>a \<or>
        (\<exists>f. a = Fault f \<and> aa = ad \<and> b = bd \<and> ba = be \<and>
             ab = Fault f \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>) \<or>
        a = Stuck \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Stuck \<and> 
             ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>" and 
     a14:"a = Fault f "
       shows
        "\<exists>a bd.
              ((((aa, b), ba), (aa, b), ba), ((ac, bb), bc), (a, bd), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, CRef.toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (com.Fault f, CRef.toSeq ((a, bd), bc)) \<and>
              (((aa, b), ba), (a, bd), bc) \<in> \<alpha>"
        
proof -  
  
  have "((((ad, bd), be), ((ad, bd), be)),(((ae, bf), bg), ((ae, bf), bg))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>" 
  proof -
    have "(((ad, bd), be), (ae, bf), bg) \<in> \<alpha>"
      using  a14 a13  by auto    
    then show ?thesis
      by (simp add:a12 alpha_id_G  related_transitions_def DomainI)
   qed    
   then show "\<exists>a bd.
              ((((aa, b), ba), (aa, b), ba), ((ac, bb), bc), (a, bd), bc) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, CRef.toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq ((a, bd), bc)) \<and>
              (((aa, b), ba), (a, bd), bc) \<in> \<alpha>" 
     using a14 a13  by fast 
 qed  

lemma while_seq_stuck: 
assumes                                           
       a12:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and
       a13:"(\<exists>c\<^sub>c. a = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
               aa = ad \<and> b = bd \<and> ba = be \<and>
               (\<exists>c\<^sub>s. ab = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and>
                      ac = ae \<and>
                      bb = bf \<and>
                      bc = bg \<and> (\<Gamma>\<^sub>c,(c\<^sub>c, (ad, bd), be),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                      (\<Gamma>\<^sub>s,(c\<^sub>s, (ae, bf), bg),R\<^sub>s,G\<^sub>s))) \<or>
        a = While b\<^sub>c c1\<^sub>c \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = While b\<^sub>s c1\<^sub>s \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<or>
        a = Skip \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Skip \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<and> (ad, bd) \<notin> b\<^sub>c \<or>
        a = Throw \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Throw \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> 
            (((ad, bd), be), (ae, bf), bg) \<in> \<gamma>\<^sub>a \<or>
        (\<exists>f. a = Fault f \<and> aa = ad \<and> b = bd \<and> ba = be \<and>
             ab = Fault f \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>) \<or>
        a = Stuck \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Stuck \<and> 
             ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>" and 
     a14:"a = Stuck"
       shows
        "\<exists>a bd.
              ((((aa, b), ba), (aa, b), ba), ((ac, bb), bc), (a, bd), bc) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck,toSeq ((a, bd), bc)) \<and>
              (((aa, b), ba), (a, bd), bc) \<in> \<alpha>"
        
proof -  
  
  have "((((ad, bd), be), ((ad, bd), be)),(((ae, bf), bg), ((ae, bf), bg))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>" 
  proof -
    have "(((ad, bd), be), (ae, bf), bg) \<in> \<alpha>"
      using  a14 a13  by auto    
    then show ?thesis
      by (simp add:a12 alpha_id_G  related_transitions_def DomainI)
   qed    
   then show "\<exists>a bd.
              ((((aa, b), ba), (aa, b), ba), ((ac, bb), bc), (a, bd), bc) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck,toSeq ((a, bd), bc)) \<and>
              (((aa, b), ba), (a, bd), bc) \<in> \<alpha>"
     using a14 a13  by fast 
 qed   

lemma while_sim:
  "(\<Gamma>\<^sub>c,c1\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c1\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow>
   (\<sigma>,\<Sigma>)\<in>\<xi> \<Longrightarrow>   
   \<xi> \<subseteq> \<alpha> \<Longrightarrow> \<gamma>\<^sub>a\<subseteq>\<alpha> \<Longrightarrow>
  Sta\<^sub>s \<xi> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow>
  Sta\<^sub>s \<gamma>\<^sub>a (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow> 
  Sta\<^sub>s \<gamma>\<^sub>n (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow> 
  \<xi> \<subseteq>  \<up>(b\<^sub>c \<rightleftharpoons>  b\<^sub>s) \<Longrightarrow>
   \<xi>\<^sub>1 = \<xi> \<inter>  \<up>(b\<^sub>c \<odot>  b\<^sub>s) \<Longrightarrow>
   \<gamma>\<^sub>n = \<xi> \<inter>  \<up>((- b\<^sub>c) \<odot>  (- b\<^sub>s)) \<Longrightarrow>   
   \<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c \<Longrightarrow> 
   (\<Gamma>\<^sub>c,(While b\<^sub>c c1\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(While b\<^sub>s c1\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s)"
apply (coinduct taking:"coPre \<xi> b\<^sub>c b\<^sub>s \<Gamma>\<^sub>c c1\<^sub>c R\<^sub>c G\<^sub>c \<alpha> \<gamma>\<^sub>n \<gamma>\<^sub>a \<Gamma>\<^sub>s c1\<^sub>s R\<^sub>s G\<^sub>s"  rule:RGSim.coinduct) 
   apply (simp add:coPre_def, clarsimp simp add:coPre_def)
  apply (rule conjI, rule while_seq_alpha[of \<xi> \<alpha> \<gamma>\<^sub>a], assumption+)
  apply (rule conjI, rule, rule, rule, rule, rule while_seq_no_ev, simp+)    
  apply (rule conjI, rule while_seq_ev, assumption+)   
  apply (rule conjI, rule, rule,rule, rule, rule, rule, rule, rule while_seq_env, assumption+, simp+)      
  apply (rule conjI, rule, rule while_seq_skip, assumption+)   
  apply (rule conjI, rule, rule while_seq_throw, assumption+) 
  apply (rule conjI,rule, rule, rule while_seq_fault, assumption+) 
  by (rule, rule while_seq_stuck, assumption+)
        
    
lemma While_sound:    
    "\<xi> \<subseteq> \<alpha> \<Longrightarrow> Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow> \<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c \<Longrightarrow> 
     \<xi> \<subseteq> \<up>(b\<^sub>c \<rightleftharpoons> b\<^sub>s) \<Longrightarrow> \<xi>\<^sub>1= \<xi> \<inter> \<up>(b\<^sub>c \<odot> b\<^sub>s) \<Longrightarrow> \<gamma>\<^sub>n= \<xi> \<inter> \<up>((-b\<^sub>c) \<odot> (-b\<^sub>s) ) \<Longrightarrow>
  (\<Gamma>\<^sub>c,c\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow> Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow> Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow> \<gamma>\<^sub>a\<subseteq>\<alpha> \<Longrightarrow>
  (\<Gamma>\<^sub>c,While b\<^sub>c c\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,While b\<^sub>s c\<^sub>s,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def apply (simp, rule, rule,rule,rule, rule,rule,rule)
  apply (rule while_sim[of \<Gamma>\<^sub>c c\<^sub>c R\<^sub>c G\<^sub>c \<alpha> \<xi>\<^sub>1 \<xi> \<gamma>\<^sub>a \<Gamma>\<^sub>s c\<^sub>s R\<^sub>s G\<^sub>s])
  unfolding RGSim_pre_def by fastforce+


lemma DynCom_sim:    
  assumes
     a1:"\<xi> \<subseteq> \<alpha>" and 
   a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and 
   a6:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and
   a7:"\<forall>\<sigma> \<Sigma>. (\<sigma>,\<Sigma>)\<in> \<xi> \<longrightarrow> (\<Gamma>\<^sub>c,(f\<^sub>c (fst \<sigma>),\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(f\<^sub>s (fst \<Sigma>), \<Sigma>),R\<^sub>s,G\<^sub>s)" and
   a8:"(\<sigma>,\<Sigma>)\<in> \<xi>" 
 shows "(\<Gamma>\<^sub>c,(DynCom f\<^sub>c,  \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(DynCom f\<^sub>s,  \<Sigma>),R\<^sub>s,G\<^sub>s)" 
   using  a1   a3  a6 a7 a8        
    apply(coinduction arbitrary: \<sigma> \<Sigma>)
      apply(clarsimp)
   apply (rule conjId)+
(* not Normal transition*)
   apply (meson sim_env)                    
(* Event Component transition *)
      apply (rule, rule, rule, rule,rule)     
      apply (auto elim: ev_stepc_normal_elim_cases)     
      (* silent component transition *)        
    apply (auto     elim:stepc_elim_cases1(12))
   apply (erule stepc_elim_cases1(12), auto)   
   using a7 DomainI unfolding toSeq_def apply auto
   by (smt Domain.DomainI r_into_rtranclp related_transition_intro rtrancl.rtrancl_refl 
          rtrancl_idemp stepce.DynComc subsetD) 

                   
lemma DynCom_sound:    
    "\<xi> \<subseteq> \<alpha>  \<Longrightarrow>
   Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow>  
    \<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c \<Longrightarrow> 
   \<forall>\<sigma> \<Sigma>. (\<sigma>,\<Sigma>)\<in>\<xi> \<longrightarrow> (\<Gamma>\<^sub>c,(f\<^sub>c (fst \<sigma>),\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(f\<^sub>s (fst \<Sigma>), \<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>  
  (\<Gamma>\<^sub>c,DynCom f\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,DynCom f\<^sub>s,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def apply (rule, rule, rule)
  apply (rule DynCom_sim)
  unfolding RGSim_pre_def by blast+

inductive_cases stepc_guard_cases:
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Guard f g c, s) \<rightarrow> (c', s')"

lemma Guard_sim:
  assumes 
  a1:"\<xi> \<subseteq> \<alpha> " and 
  a2:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and 
  a3:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and  
  a5:"\<xi> \<subseteq> \<up>(b\<^sub>c \<rightleftharpoons> b\<^sub>s)" and a6:"\<xi>\<^sub>1 = \<xi> \<inter> \<up>(b\<^sub>c \<odot> b\<^sub>s)" and
  a8:"(\<sigma>,\<Sigma>)\<in>\<xi>" and
  a9:"(\<Gamma>\<^sub>c,c\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c\<^sub>s,R\<^sub>s,G\<^sub>s)"
shows  
  "(\<Gamma>\<^sub>c,(Guard f b\<^sub>c c\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Guard f b\<^sub>s c\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s)"
  using a1 a2 a3  a6  a8 a9 
proof(coinduction arbitrary: \<sigma>  \<Sigma>,clarsimp)         
  fix \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls 
  let ?s1 = "(\<forall>c\<^sub>c' \<sigma>g' \<sigma>l'.
               \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Guard f b\<^sub>c c\<^sub>c, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow>
                        (c\<^sub>c', CRef.toSeq ((\<sigma>g', \<sigma>l'), \<sigma>ls)) \<longrightarrow>
               (\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
                   \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Guard f b\<^sub>s c\<^sub>s, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                           (c\<^sub>s', toSeq ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<and>
                   (((\<sigma>g', \<sigma>l'), \<sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> \<alpha> \<and>
                   ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g', \<sigma>l'), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                   (c\<^sub>c' = Guard f b\<^sub>c c\<^sub>c \<and>
                    c\<^sub>s' = Guard f b\<^sub>s c\<^sub>s \<and> (((\<sigma>g', \<sigma>l'), \<sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> \<xi> \<or>
                    (\<Gamma>\<^sub>c,(c\<^sub>c', (\<sigma>g', \<sigma>l'), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (\<Sigma>g', \<Sigma>l'), \<Sigma>ls),R\<^sub>s,G\<^sub>s))))"
    assume 
       a0:"(((\<sigma>g,\<sigma>l), \<sigma>ls), ((\<Sigma>g,\<Sigma>l), \<Sigma>ls)) \<in> \<xi>" and              
       a3:"Sta\<^sub>s \<xi> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>" and                           
       a8:"\<xi> \<subseteq> \<alpha>" and              
       a12:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c"    
    have alpha:"(((\<sigma>g,\<sigma>l), \<sigma>ls), ((\<Sigma>g,\<Sigma>l), \<Sigma>ls)) \<in> \<alpha>" 
      using a0 a8  by auto
    moreover have "\<forall>\<sigma>g' \<sigma>l' \<sigma>ls' \<Sigma>g' \<Sigma>l' \<Sigma>ls'.
           ((((\<sigma>g,\<sigma>l), \<sigma>ls),((\<sigma>g',\<sigma>l'), \<sigma>ls')), 
               (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls'))) \<in> ((R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<longrightarrow>
           ((((\<sigma>g',\<sigma>l'), \<sigma>ls'), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls')) \<in> \<xi>) \<or>
           (\<Gamma>\<^sub>c,(LanguageCon.com.Guard f b\<^sub>c c\<^sub>c, ((\<sigma>g',\<sigma>l'), \<sigma>ls')),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
           (\<Gamma>\<^sub>s,(LanguageCon.com.Guard f b\<^sub>s c\<^sub>s, ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls')),R\<^sub>s,G\<^sub>s)" 
      using env[OF a0 a3] by blast
    moreover have "
           \<forall>v c\<^sub>c' \<sigma>g' \<sigma>l'.
               \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Guard f b\<^sub>c c\<^sub>c, toSeq ((\<sigma>g,\<sigma>l), \<sigma>ls)) \<rightarrow>
                              (c\<^sub>c', toSeq ((\<sigma>g',\<sigma>l'), \<sigma>ls)) \<longrightarrow>
               (\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
                   (\<exists>a ab b.
                       \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Guard f b\<^sub>s c\<^sub>s, toSeq ((\<Sigma>g,\<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                       (\<exists>aa ad ba.
                           \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, ab, b) \<rightarrow> (aa, ad, ba) \<and>
                           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ad, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)))) \<and>
                   (((\<sigma>g',\<sigma>l'), \<sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)) \<in> \<alpha> \<and>
                   ((((\<sigma>g,\<sigma>l), \<sigma>ls),((\<sigma>g',\<sigma>l'), \<sigma>ls)), 
                       (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls))) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                   (c\<^sub>c' = Guard f b\<^sub>c c\<^sub>c \<and>
                    c\<^sub>s' = Guard f b\<^sub>s c\<^sub>s \<and> (((\<sigma>g',\<sigma>l'), \<sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)) \<in> \<xi> \<or>
                    (\<Gamma>\<^sub>c,(c\<^sub>c', ((\<sigma>g',\<sigma>l'), \<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)),R\<^sub>s,G\<^sub>s)))"
      by (fastforce elim: stepc_guard_cases)            
    moreover have ?s1      
    proof -
    {
      fix c\<^sub>c' \<sigma>g' \<sigma>l'
      assume  a00:" \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Guard f b\<^sub>c c\<^sub>c, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((\<sigma>g', \<sigma>l'), \<sigma>ls))"      
      have guar1:"((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), 
                    ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (\<Sigma>g, \<Sigma>l), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
        using a12  a0 a8  unfolding related_transitions_def Id_def by blast             
      have h:"((c\<^sub>c'=c\<^sub>c \<and> (\<sigma>g', \<sigma>l')\<in>b\<^sub>c) \<or> (c\<^sub>c' = Fault f \<and> (\<sigma>g', \<sigma>l')\<notin> b\<^sub>c)) \<and> \<sigma>g'= \<sigma>g \<and> \<sigma>l'= \<sigma>l"
        using stepc_elim_cases2(2)[OF a00] unfolding toSeq_def by auto
      { assume a000:" (\<sigma>g, \<sigma>l)\<in>b\<^sub>c"
        then have step:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Guard f b\<^sub>c c\<^sub>c, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<and> 
                         \<sigma>g'= \<sigma>g \<and> \<sigma>l'= \<sigma>l"
          using a00 h by auto
        then have sig1:"c\<^sub>c'=c\<^sub>c \<and> ((((\<sigma>g,\<sigma>l), \<sigma>ls), ((\<Sigma>g,\<Sigma>l), \<Sigma>ls))) \<in> \<xi>\<^sub>1"
          using a0 a5 a6 h a000   unfolding eq_rel_def  and_rel_def ext_set_def by auto
        then have sn_inb:"c\<^sub>c'=c\<^sub>c \<and> (\<Sigma>g,\<Sigma>l)\<in>b\<^sub>s" 
          using a6 a5 a0 unfolding and_rel_def eq_rel_def ext_set_def by auto
        then have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Guard f b\<^sub>s c\<^sub>s, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s, (\<Sigma>g,\<Sigma>l))" 
          using sn_inb stepce.Guardc GuardFaultc
          by fast                 
        have "(\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Guard f b\<^sub>s c\<^sub>s, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                   (c\<^sub>s', CRef.toSeq ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<and>
           (((\<sigma>g', \<sigma>l'), \<sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> \<alpha> \<and>
           ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g', \<sigma>l'), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
           (c\<^sub>c' = LanguageCon.com.Guard f b\<^sub>c c\<^sub>c \<and>
            c\<^sub>s' = LanguageCon.com.Guard f b\<^sub>s c\<^sub>s \<and> (((\<sigma>g', \<sigma>l'), \<sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> \<xi> \<or>
            (\<Gamma>\<^sub>c,(c\<^sub>c', (\<sigma>g', \<sigma>l'), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (\<Sigma>g', \<Sigma>l'), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))"
            using  steps guar1  a9  sig1 step a3 
            unfolding related_transitions_def RGSim_pre_def toSeq_def
            by fastforce
      }
      moreover { assume a000:"(\<sigma>g, \<sigma>l)\<notin>b\<^sub>c"
        then have sig1:"c\<^sub>c' = Fault f \<and> ((((\<sigma>g,\<sigma>l), \<sigma>ls), ((\<Sigma>g,\<Sigma>l), \<Sigma>ls))) \<notin> \<xi>\<^sub>1"
          using a0 a5 a6 h  unfolding eq_rel_def  and_rel_def ext_set_def by auto
        then have sn_inb:"c\<^sub>c' = Fault f \<and>(\<Sigma>g,\<Sigma>l)\<notin>b\<^sub>s" 
          using a6 a5 a0 unfolding and_rel_def eq_rel_def ext_set_def by auto
        then have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Guard f b\<^sub>s c\<^sub>s, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, (\<Sigma>g,\<Sigma>l))" 
          using sn_inb  GuardFaultc h a000
          by fast                 
        have "(\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Guard f b\<^sub>s c\<^sub>s, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                   (c\<^sub>s', CRef.toSeq ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<and>
           (((\<sigma>g', \<sigma>l'), \<sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> \<alpha> \<and>
           ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g', \<sigma>l'), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
           (c\<^sub>c' = LanguageCon.com.Guard f b\<^sub>c c\<^sub>c \<and>
            c\<^sub>s' = LanguageCon.com.Guard f b\<^sub>s c\<^sub>s \<and> (((\<sigma>g', \<sigma>l'), \<sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> \<xi> \<or>
            (\<Gamma>\<^sub>c,(c\<^sub>c', (\<sigma>g', \<sigma>l'), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (\<Sigma>g', \<Sigma>l'), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))"
          using  h steps guar1  a9  sig1 Fault_sim[OF alpha assms(3)] alpha  
          unfolding related_transitions_def RGSim_pre_def toSeq_def by fastforce                                    
      } ultimately have "(\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Guard f b\<^sub>s c\<^sub>s, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                   (c\<^sub>s', CRef.toSeq ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<and>
           (((\<sigma>g', \<sigma>l'), \<sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> \<alpha> \<and>
           ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g', \<sigma>l'), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
           (c\<^sub>c' = LanguageCon.com.Guard f b\<^sub>c c\<^sub>c \<and>
            c\<^sub>s' = LanguageCon.com.Guard f b\<^sub>s c\<^sub>s \<and> (((\<sigma>g', \<sigma>l'), \<sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> \<xi> \<or>
            (\<Gamma>\<^sub>c,(c\<^sub>c', (\<sigma>g', \<sigma>l'), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (\<Sigma>g', \<Sigma>l'), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))" by auto      
     } thus ?thesis by auto
   qed     
   ultimately show "(((\<sigma>g,\<sigma>l), \<sigma>ls), ((\<Sigma>g,\<Sigma>l), \<Sigma>ls)) \<in> \<alpha> \<and> ?s1 \<and>
           (\<forall>v c\<^sub>c' \<sigma>g' \<sigma>l'.
               \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Guard f b\<^sub>c c\<^sub>c, toSeq ((\<sigma>g,\<sigma>l), \<sigma>ls)) \<rightarrow>
                              (c\<^sub>c', toSeq ((\<sigma>g',\<sigma>l'), \<sigma>ls)) \<longrightarrow>
               (\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
                   (\<exists>a ab b.
                       \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Guard f b\<^sub>s c\<^sub>s, toSeq ((\<Sigma>g,\<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                       (\<exists>aa ad ba.
                           \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, ab, b) \<rightarrow> (aa, ad, ba) \<and>
                           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ad, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)))) \<and>
                   (((\<sigma>g',\<sigma>l'), \<sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)) \<in> \<alpha> \<and>
                   ((((\<sigma>g,\<sigma>l), \<sigma>ls),((\<sigma>g',\<sigma>l'), \<sigma>ls)), 
                       (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls))) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                   (c\<^sub>c' = Guard f b\<^sub>c c\<^sub>c \<and>
                    c\<^sub>s' = Guard f b\<^sub>s c\<^sub>s \<and> (((\<sigma>g',\<sigma>l'), \<sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)) \<in> \<xi> \<or>
                    (\<Gamma>\<^sub>c,(c\<^sub>c', ((\<sigma>g',\<sigma>l'), \<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)),R\<^sub>s,G\<^sub>s)))) \<and>
           (\<forall>\<sigma>g' \<sigma>l' \<sigma>ls' \<Sigma>g' \<Sigma>l' \<Sigma>ls'.
           ((((\<sigma>g,\<sigma>l), \<sigma>ls),((\<sigma>g',\<sigma>l'), \<sigma>ls')), 
               (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls'))) \<in> ((R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<longrightarrow>
           ((((\<sigma>g',\<sigma>l'), \<sigma>ls'), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls')) \<in> \<xi>) \<or>
           (\<Gamma>\<^sub>c,(LanguageCon.com.Guard f b\<^sub>c c\<^sub>c, ((\<sigma>g',\<sigma>l'), \<sigma>ls')),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
           (\<Gamma>\<^sub>s,(LanguageCon.com.Guard f b\<^sub>s c\<^sub>s, ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls')),R\<^sub>s,G\<^sub>s)) "
      by auto
  qed    
   
                       
lemma Guard_sound:    
 " \<xi> \<subseteq> \<alpha> \<Longrightarrow> Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow> \<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c \<Longrightarrow> 
   \<xi> \<subseteq> \<up>(b\<^sub>c \<rightleftharpoons> b\<^sub>s) \<Longrightarrow> \<xi>\<^sub>1= \<xi> \<inter> \<up>(b\<^sub>c \<odot> b\<^sub>s) \<Longrightarrow>  
  (\<Gamma>\<^sub>c,c\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow>  
  (\<Gamma>\<^sub>c,Guard f b\<^sub>c c\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,Guard f b\<^sub>s c\<^sub>s,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def apply (rule, rule, rule)
  apply (rule Guard_sim)
  unfolding RGSim_pre_def by blast+
    
definition f_equiv  ("_ \<rightleftharpoons>\<^sub>f / _" [81,81] 100) 
where
"
f_equiv \<Gamma>\<^sub>c \<Gamma>\<^sub>s \<equiv>  (\<Gamma>\<^sub>c =None \<and> \<Gamma>\<^sub>s = None) \<or> ((\<exists>pc. \<Gamma>\<^sub>c = Some pc) \<and> (\<exists>ps. \<Gamma>\<^sub>s = Some ps))
"

inductive_cases stepc_call_cases:
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Call ps, s) \<rightarrow> (c', s')"

lemma Call_sim:
  assumes 
  a1:"\<xi> \<subseteq> \<alpha> " and 
  a2:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and 
  a3:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and   
  a5:"(\<Gamma>\<^sub>c pc) \<rightleftharpoons>\<^sub>f (\<Gamma>\<^sub>s ps)" and 
  a6:"(\<forall>c\<^sub>c c\<^sub>s. \<Gamma>\<^sub>c pc = Some c\<^sub>c \<and> \<Gamma>\<^sub>s ps = Some c\<^sub>s \<longrightarrow> (\<Gamma>\<^sub>c,c\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c\<^sub>s,R\<^sub>s,G\<^sub>s))" and
  a8:"(\<sigma>,\<Sigma>)\<in>\<xi>" 
shows  
  "(\<Gamma>\<^sub>c,(Call pc, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Call ps, \<Sigma>),R\<^sub>s,G\<^sub>s)" 
using a1 a2    a5 a6  a8 
proof(coinduction arbitrary: \<sigma> \<Sigma>,clarsimp)  
  fix  \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls 
    assume  
       a0:"(((\<sigma>g,\<sigma>l), \<sigma>ls), ((\<Sigma>g,\<Sigma>l), \<Sigma>ls)) \<in> \<xi>" and              
       a2:"Sta\<^sub>s \<xi> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>" and                           
       a8:"\<xi> \<subseteq> \<alpha>"  
    have alpha:"(((\<sigma>g,\<sigma>l), \<sigma>ls), ((\<Sigma>g,\<Sigma>l), \<Sigma>ls)) \<in> \<alpha>" 
      using a0 a8  by auto    
    moreover have "\<forall>a b ba aa bb bc.
            ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), ba), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, bb), bc) \<in> ((R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<longrightarrow>
            (((a, b), ba), (aa, bb), bc) \<in> \<xi> \<or> (\<Gamma>\<^sub>c,(LanguageCon.com.Call pc, (a, b), ba),R\<^sub>c,G\<^sub>c)
            \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(LanguageCon.com.Call ps, (aa, bb), bc),R\<^sub>s,G\<^sub>s)" 
      using env[OF a0 a2] by blast    
    moreover have "\<forall>v c\<^sub>c' a b.
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Call pc,toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((a, b), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                (\<exists>a ab b.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Call ps, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                    (\<exists>ac ad bb.
                        \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, ab, b) \<rightarrow> (ac, ad, bb) \<and>
                        \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ac, ad, bb) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', CRef.toSeq ((aa, ba), \<Sigma>ls)))) \<and>
                (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                (c\<^sub>c' = Call pc \<and>
                 c\<^sub>s' = Call ps \<and> (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))"
      by (fastforce elim: stepc_call_cases) 
    moreover have "\<forall>c\<^sub>c' \<sigma>g' \<sigma>l'.
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Call pc, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((\<sigma>g', \<sigma>l'), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Call ps, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',  toSeq ((aa, ba), \<Sigma>ls)) \<and>
                (((\<sigma>g', \<sigma>l'), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g', \<sigma>l'), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                (c\<^sub>c' = Call pc \<and>
                 c\<^sub>s' = Call ps \<and> (((\<sigma>g', \<sigma>l'), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', (\<sigma>g', \<sigma>l'), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))"
    proof -
      {fix c\<^sub>c' \<sigma>g' \<sigma>l'
        assume  a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Call pc,  toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c',   toSeq ((\<sigma>g', \<sigma>l'), \<sigma>ls))"
        have guar1:"((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), 
                    ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (\<Sigma>g, \<Sigma>l), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
        using a3  a0 a8  unfolding related_transitions_def Id_def by blast              
        have h:"((\<exists>c\<^sub>c. \<Gamma>\<^sub>c pc = Some c\<^sub>c) \<and> c\<^sub>c' = the (\<Gamma>\<^sub>c pc) \<or> 
              \<not>(\<exists>c\<^sub>c. \<Gamma>\<^sub>c pc = Some c\<^sub>c) \<and> c\<^sub>c' = Stuck ) \<and>  \<sigma>g'= \<sigma>g \<and> \<sigma>l'= \<sigma>l" 
          using stepc_elim_cases1(11)[OF a00, 
             of "((\<exists>c\<^sub>c. \<Gamma>\<^sub>c pc = Some c\<^sub>c) \<and> c\<^sub>c' = the (\<Gamma>\<^sub>c pc) \<or> 
                \<not>(\<exists>c\<^sub>c. \<Gamma>\<^sub>c pc = Some c\<^sub>c) \<and> c\<^sub>c' = Stuck ) \<and>  \<sigma>g'= \<sigma>g \<and> \<sigma>l'= \<sigma>l"] unfolding toSeq_def 
          by fastforce 
        { assume a000:"\<exists>c\<^sub>c. \<Gamma>\<^sub>c pc = Some c\<^sub>c"
          then obtain c\<^sub>s where someps:"\<Gamma>\<^sub>s ps = Some c\<^sub>s"
             using a5 unfolding f_equiv_def by auto                       
          then have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Call ps, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (the (\<Gamma>\<^sub>s ps), toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls))" 
            using a5 someps
            by (metis  option.distinct(1) option.exhaust_sel 
                    r_into_rtranclp rtranclp.rtrancl_refl stepce.Callc)               
          then have "(\<Gamma>\<^sub>c,c\<^sub>c',R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c\<^sub>s,R\<^sub>s,G\<^sub>s)"
            using someps a6 h a000 by fastforce
          then have "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Call pc, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((\<sigma>g', \<sigma>l'), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Call ps, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',  toSeq ((aa, ba), \<Sigma>ls)) \<and>
                (((\<sigma>g', \<sigma>l'), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g', \<sigma>l'), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                (c\<^sub>c' = Call pc \<and>
                 c\<^sub>s' = Call ps \<and> (((\<sigma>g', \<sigma>l'), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', (\<sigma>g', \<sigma>l'), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))" 
          using  steps guar1 a6 h  unfolding related_transitions_def RGSim_pre_def  
          using someps a0 by fastforce
      }
      moreover{
        assume a000:"\<not>(\<exists>c\<^sub>c. \<Gamma>\<^sub>c pc = Some c\<^sub>c)"
        then have "\<Gamma>\<^sub>c pc = None" by auto
        then have "\<Gamma>\<^sub>s ps = None" using a5 unfolding f_equiv_def by auto
        then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Call ps, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck,  toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls))"
          unfolding toSeq_def                        
          by (simp add: r_into_rtranclp stepce.CallUndefinedc)
        then have "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Call pc, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((\<sigma>g', \<sigma>l'), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Call ps, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',  toSeq ((aa, ba), \<Sigma>ls)) \<and>
                (((\<sigma>g', \<sigma>l'), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g', \<sigma>l'), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                (c\<^sub>c' = Call pc \<and>
                 c\<^sub>s' = Call ps \<and> (((\<sigma>g', \<sigma>l'), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', (\<sigma>g', \<sigma>l'), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))" 
          using alpha Stuck_sim[OF alpha assms(3)] h a000  guar1 by blast
          
      } 
      ultimately have "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Call pc, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((\<sigma>g', \<sigma>l'), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Call ps, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',  toSeq ((aa, ba), \<Sigma>ls)) \<and>
                (((\<sigma>g', \<sigma>l'), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g', \<sigma>l'), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                (c\<^sub>c' = Call pc \<and>
                 c\<^sub>s' = Call ps \<and> (((\<sigma>g', \<sigma>l'), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', (\<sigma>g', \<sigma>l'), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))" 
        by auto
    } thus ?thesis by auto
  qed    
  ultimately show 
      "(((\<sigma>g, \<sigma>l), \<sigma>ls), (\<Sigma>g, \<Sigma>l), \<Sigma>ls) \<in> \<alpha> \<and>
        (\<forall>c\<^sub>c' a b.
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Call pc, CRef.toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', CRef.toSeq ((a, b), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Call ps, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                        (c\<^sub>s', CRef.toSeq ((aa, ba), \<Sigma>ls)) \<and>
                (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                (c\<^sub>c' = LanguageCon.com.Call pc \<and>
                 c\<^sub>s' = LanguageCon.com.Call ps \<and> (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))) \<and>
        (\<forall>v c\<^sub>c' a b.
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>Some v (LanguageCon.com.Call pc, CRef.toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow>
                           (c\<^sub>c', CRef.toSeq ((a, b), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                (\<exists>a ab b.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Call ps, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                    (\<exists>ac ad bb.
                        \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, ab, b) \<rightarrow> (ac, ad, bb) \<and>
                        \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ac, ad, bb) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', CRef.toSeq ((aa, ba), \<Sigma>ls)))) \<and>
                (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                (c\<^sub>c' = LanguageCon.com.Call pc \<and>
                 c\<^sub>s' = LanguageCon.com.Call ps \<and> (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))) \<and>
        (\<forall>a b ba aa bb bc.
            ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), ba), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, bb), bc) \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<longrightarrow>
            (((a, b), ba), (aa, bb), bc) \<in> \<xi> \<or> (\<Gamma>\<^sub>c,(LanguageCon.com.Call pc, (a, b), ba),R\<^sub>c,G\<^sub>c)
            \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(LanguageCon.com.Call ps, (aa, bb), bc),R\<^sub>s,G\<^sub>s))" 
      by auto   
qed   

 lemma Call_sound:    
 " \<xi> \<subseteq> \<alpha>  \<Longrightarrow> Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow> \<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c \<Longrightarrow> 
   (\<Gamma>\<^sub>c pc) \<rightleftharpoons>\<^sub>f (\<Gamma>\<^sub>s ps) \<Longrightarrow> 
  (\<forall>c\<^sub>c c\<^sub>s. \<Gamma>\<^sub>c pc = Some c\<^sub>c \<and> \<Gamma>\<^sub>s ps = Some c\<^sub>s \<longrightarrow> (\<Gamma>\<^sub>c,c\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c\<^sub>s,R\<^sub>s,G\<^sub>s)) \<Longrightarrow>   
  (\<Gamma>\<^sub>c,Call pc,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,Call ps,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def apply (rule, rule, rule)
  apply (rule Call_sim)
  unfolding RGSim_pre_def by auto 
   
type_synonym ('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula =  
   "(('gc\<times>'lc,'p,'f,'e) com \<times>     
     (('gc,'lc)par_state)  rel1 \<times> 
     (('gc,'lc)par_state) rel1 \<times> 
     ('gs\<times>'ls,'p,'f,'e) com \<times>     
     (('gs,'ls)par_state)  rel1 \<times> 
     (('gs,'ls)par_state) rel1 \<times> 
     (('gc,'lc)par_state,('gs,'ls)par_state) rel \<times>
     (('gc,'lc)par_state,('gs,'ls)par_state) rel \<times>
     (('gc,'lc)par_state,('gs,'ls)par_state) rel 
    )" 
   
 definition Com\<^sub>c:: "('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula \<Rightarrow> ('gc\<times>'lc,'p,'f,'e) com" where
  "Com\<^sub>c f \<equiv> fst f"

  definition Rel\<^sub>c :: "('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula \<Rightarrow> (('gc,'lc)par_state)  rel1" where
  "Rel\<^sub>c f \<equiv> fst (snd f)" 

 definition Gua\<^sub>c :: "('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula \<Rightarrow> (('gc,'lc)par_state)  rel1" where
  "Gua\<^sub>c f \<equiv> fst (snd (snd f))" 
  
 definition Com\<^sub>s:: "('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula \<Rightarrow> ('gs\<times>'ls,'p,'f,'e) com" where
  "Com\<^sub>s f \<equiv> fst (snd (snd (snd f)))"
  
 definition Rel\<^sub>s :: "('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula \<Rightarrow> (('gs,'ls)par_state)  rel1" where
  "Rel\<^sub>s f \<equiv>  fst (snd (snd (snd (snd f))))" 

 definition Gua\<^sub>s :: "('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula \<Rightarrow> (('gs,'ls)par_state)  rel1" where
  "Gua\<^sub>s f \<equiv>  fst (snd (snd (snd (snd (snd f)))))"
 
definition Pre :: "('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula \<Rightarrow> 
                     (('gc,'lc)par_state,('gs,'ls)par_state) rel " where
   "Pre f \<equiv>  fst (snd (snd (snd (snd (snd (snd f))))))" 

 definition PostQ :: " ('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula \<Rightarrow> 
                     (('gc,'lc)par_state,('gs,'ls)par_state) rel " where
   "PostQ f \<equiv>  fst (snd (snd (snd (snd (snd (snd (snd f)))))))" 
 
 definition PostA :: "('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula \<Rightarrow> 
                     (('gc,'lc)par_state,('gs,'ls)par_state) rel " where
   "PostA f \<equiv>  snd (snd (snd (snd (snd (snd (snd (snd f)))))))" 

    
definition PCom\<^sub>c :: "('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula list \<Rightarrow> ('gc,'lc,'p,'f,'e) par_com"
where
"PCom\<^sub>c Ps \<equiv> map Com\<^sub>c Ps"

definition PCom\<^sub>s :: "('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula list \<Rightarrow> ('gs,'ls,'p,'f,'e) par_com"
where
"PCom\<^sub>s Ps \<equiv> map Com\<^sub>s Ps"

definition par_sim_list :: "(('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula  \<Rightarrow>'b) \<Rightarrow> 
                           ('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula  list \<Rightarrow> 'b list"
where
"par_sim_list f Ps \<equiv> map f Ps"


lemma ParallelCom_Com:"i<length xs \<Longrightarrow> (par_sim_list Com\<^sub>s xs)!i = Com\<^sub>s (xs!i)"
unfolding par_sim_list_def Com\<^sub>s_def by fastforce    


  
lemma G_comp_aux': 
"g\<subseteq>G \<and> (s2, s2') \<in>g\<^sup>* \<Longrightarrow> (s2, s2') \<in> G\<^sup>*"
  by (metis rtrancl_eq_or_trancl trancl_mono)

lemma G_comp_aux: 
assumes a1:"(\<Union>j<length g. g ! j) \<subseteq> G" and
        a2:"(s2, s2') \<in> (g ! i)\<^sup>* " and
        a3:"i < length g"
      shows "(s2, s2') \<in> G\<^sup>*"
using a1 a2 a3 G_comp_aux'
  by (metis UN_subset_iff lessThan_iff)
    
lemma G_comp_aux1: 
assumes a1:"g \<subseteq> G" and
        a2:"(s2, s2') \<in> g\<^sup>* "
      shows "(s2, s2') \<in> G\<^sup>*"
using a1 a2  G_comp_aux' by metis
    
lemma G_comp:
  assumes a1:"(\<Union>j<length G1. (G1 !j)) \<subseteq> G\<^sub>1" and
          a2:" (\<Union>j<length G2. (G2 ! j)) \<subseteq> G\<^sub>2"  and
          a3:"((s1, s1'), s2, s2') \<in> (G1 ! i, (G2 ! i)\<^sup>*)\<^sub>\<alpha>" and
          a4:"i<length G1 \<and> i< length G2"
  shows "((s1, s1'), s2, s2') \<in> (G\<^sub>1, G\<^sub>2\<^sup>*)\<^sub>\<alpha>"  
proof-
  have "(s1, s1') \<in> G\<^sub>1" using a1 a3 a4 unfolding related_transitions_def by auto
  moreover have "(s2, s2') \<in> G\<^sub>2\<^sup>*" 
    using a2 a3 a4 G_comp_aux 
    unfolding related_transitions_def by auto
  ultimately show ?thesis using a3 unfolding related_transitions_def by auto
qed
  
lemma G_comp1:
  assumes a1:"G1 \<subseteq> G\<^sub>1" and
          a2:" G2 \<subseteq> G\<^sub>2"  and
          a3:"((s1, s1'), s2, s2') \<in> (G1, G2\<^sup>*)\<^sub>\<alpha>" 
  shows "((s1, s1'), s2, s2') \<in> (G\<^sub>1, G\<^sub>2\<^sup>*)\<^sub>\<alpha>"  
proof-
  have "(s1, s1') \<in> G\<^sub>1" using a1 a3  unfolding related_transitions_def by auto
  moreover have "(s2, s2') \<in> G\<^sub>2\<^sup>*" 
    using a2 a3 G_comp_aux1 
    unfolding related_transitions_def by auto
  ultimately show ?thesis using a3 unfolding related_transitions_def by auto
qed  
    
lemma sim_comp_not_mod:
  assumes a0:"(\<Gamma>\<^sub>c, (c\<^sub>c,\<sigma>),R\<^sub>c, G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,s\<^sub>s),R\<^sub>s, G\<^sub>s)" and
          a1:"(((\<sigma>,s\<^sub>c'),s\<^sub>s,s\<^sub>s') \<in> (R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" 
  shows "(\<Gamma>\<^sub>c, (c\<^sub>c,s\<^sub>c'),R\<^sub>c, G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,s\<^sub>s'),R\<^sub>s, G\<^sub>s)"
  using a0 a1 env_sim by blast
    
definition R_wf::"nat \<Rightarrow> (('\<sigma>g\<times>'\<sigma>l list), ('\<Sigma>g\<times>'\<Sigma>l list)) rel \<Rightarrow> bool"
  where "R_wf i \<alpha> \<equiv> \<forall>\<sigma>g \<sigma>l \<Sigma>g \<Sigma>l. ((\<sigma>g, \<sigma>l),(\<Sigma>g, \<Sigma>l)) \<in> \<alpha> \<longrightarrow> 
                       length \<sigma>l = length \<Sigma>l \<and> i = length \<sigma>l"

(* definition R_wf'::"nat \<Rightarrow> (('\<sigma>g\<times>'\<sigma>l list), ('\<Sigma>g\<times>'\<Sigma>l list)) rel \<Rightarrow> bool"
  where "R_wf' i \<alpha> \<equiv> \<forall>\<sigma>g \<sigma>l \<Sigma>g \<Sigma>l. ((\<sigma>g, \<sigma>l),(\<Sigma>g, \<Sigma>l)) \<in> \<alpha> \<longrightarrow> 
                       length \<sigma>l = length \<Sigma>l \<and> i \<le> length \<sigma>l" *)

lemma eq_step:"(\<forall>j\<noteq>i. \<sigma>'ls ! j = \<sigma>ls ! j) \<Longrightarrow> 
         \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c, CRef.toSeq (toSeqState i (\<sigma>g, \<sigma>ls))) \<rightarrow>
          (c', CRef.toSeq ((\<sigma>'g, (\<sigma>'ls!i)), snd (toSeqState i (\<sigma>g, \<sigma>ls)))) = 
         \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c, toSeqPar  i (\<sigma>g,\<sigma>ls)) \<rightarrow> (c',  toSeqPar i (\<sigma>'g,\<sigma>'ls))"
unfolding toSeq_def toSeqState_def by auto

definition Rel_wf::"nat \<Rightarrow> (('\<sigma>g\<times>'\<sigma>l list), ('\<Sigma>g\<times>'\<Sigma>l list)) rel \<Rightarrow> bool"
  where "Rel_wf i R \<equiv> \<forall>(x,y)\<in>R. i<length (snd x) \<and> i<length (snd y)"

lemma  toSeqPar_toSeq_SeqState:"CRef.toSeq (toSeqState i (\<sigma>g, \<sigma>ls)) = toSeqPar  i (\<sigma>g,\<sigma>ls)"
  unfolding toSeq_def toSeqState_def by auto

lemma Seq_rel_par':"((toSeqState i (g, ls), toSeqState i (g', ls'))) \<in> Seq_rel i R \<Longrightarrow> 
         Rel_wf i R  \<Longrightarrow>  i< length ls \<Longrightarrow> i< length ls' \<Longrightarrow>
       ((g, ls), (g',ls')) \<in> R"     
  unfolding Seq_rel_def Rel_wf_def apply auto using eq_toSeqState
  by (metis case_prodD snd_conv)
 

lemma Seq_rel_par:"((toSeqState i (g, ls), toSeqState i (g', ls'))) \<in> Seq_rel i R \<Longrightarrow> 
         R_wf (length ls') R \<Longrightarrow>  i< length ls \<Longrightarrow>  length ls = length ls' \<Longrightarrow>
       ((g, ls), (g',ls')) \<in> R"     
  unfolding Seq_rel_def R_wf_def apply auto using eq_toSeqState
  by metis

lemma par_rel_seq_rel:
     "((g, ls), (g',ls')) \<in> R \<Longrightarrow> 
       R_wf (length ls') R \<Longrightarrow>  i< length ls \<Longrightarrow>  length ls = length ls' \<Longrightarrow> 
          ((toSeqState i (g, ls), toSeqState i (g', ls'))) \<in> Seq_rel i R
       "     
  unfolding Seq_rel_def R_wf_def   
  by (metis (no_types, lifting) case_prod_conv image_iff) 

lemma par_rel_seq_rel':
     "((g, ls), (g',ls')) \<in> R \<Longrightarrow> 
       Rel_wf i R \<Longrightarrow>  i< length ls \<Longrightarrow>  i < length ls' \<Longrightarrow> 
          ((toSeqState i (g, ls), toSeqState i (g', ls'))) \<in> Seq_rel i R
       "     
  unfolding Seq_rel_def R_wf_def   
  by (metis (no_types, lifting) case_prod_conv image_iff) 

 

lemma Seq_rel_tran_par:
    "(toSeqState i (g, ls), toSeqState i (g', ls')) \<in> (Seq_rel i R)\<^sup>+ \<Longrightarrow>
        R_wf (length ls) R \<Longrightarrow> i < length ls \<Longrightarrow> length ls = length ls' \<Longrightarrow>         
      ((g, ls),toParState i ( toSeqState i (g', ls'))) \<in> R\<^sup>+"
proof (induct rule:Transitive_Closure.trancl_induct[case_names Refl Step])
  case (Refl y)
  have len:"length (snd y) = length ls - 1" 
    using Refl(1,2,3) unfolding Seq_rel_def apply auto
    by (simp add: R_wf_def len_toSeqState)     
  then have  "toSeqState i (toParState i y) = y"
    using Par2Seq0f 
    by (metis One_nat_def Refl.prems(2) Suc_pred 
           length_greater_0_conv less_Suc_eq_le list.size(3) not_less0)
  moreover have "length (snd (toParState i y)) = length ls" using len
    by (metis Refl.prems(2) Seq2Par len_toParState len_toSeqState snd_conv)
  ultimately show ?case using Seq_rel_par
    by (metis Refl.hyps Refl.prems(1) Refl.prems(2) prod.exhaust_sel trancl.r_into_trancl) 
next
  case (Step y z)
  then have len:"length (snd y) = length ls - 1 \<and> length (snd z) = length ls - 1" 
    using Step(1) unfolding Seq_rel_def apply auto    
    by (auto simp add: R_wf_def len_toSeqState) 
  then have "toSeqState i (toParState i y) = y"
    by (metis Nat.le_diff_conv2 One_nat_def Par2Seq0f Step.prems(2) 
        Suc_leI add.commute neq0_conv not_less_zero plus_1_eq_Suc)
  moreover have "toSeqState i (toParState i z) = z" using len 
    by (metis Nat.le_diff_conv2 One_nat_def Par2Seq0f Step.prems(2) 
        Suc_leI add.commute neq0_conv not_less_zero plus_1_eq_Suc)
  ultimately have "(toParState i y, toParState i z) \<in> R" using Step(2) Seq_rel_par len len_toParState
    by (metis One_nat_def Step.prems(1) Step.prems(2) Suc_leI gr0I gr_implies_not0 
          le_add_diff_inverse2 len_toParState prod.exhaust_sel)
  then show ?case using Step by auto
qed   

lemma Seq_rel_tran_par':
    "(toSeqState i (g, ls), toSeqState i (g', ls')) \<in> (Seq_rel i R)\<^sup>+ \<Longrightarrow>
        Rel_wf i R \<Longrightarrow> i < length ls \<Longrightarrow>  i < length ls' \<Longrightarrow>         
      ((g, ls),toParState i ( toSeqState i (g', ls'))) \<in> R\<^sup>+"
proof (induct rule:Transitive_Closure.trancl_induct[case_names Refl Step])
  case (Refl y)
  have len:"i\<le>length (snd y)" 
    using Refl(1,2,3) unfolding Seq_rel_def Rel_wf_def apply (auto simp add: split_def)
    by (metis One_nat_def Suc_pred len_toSeqState length_greater_0_conv 
          less_Suc_eq_le less_trans list.size(3) not_le_imp_less snd_conv)         
  then have  "toSeqState i (toParState i y) = y"
    using Par2Seq0f by fast
  moreover have "i < length (snd (toParState i y))" using len
    using par_seq_rel_i_length toParState_in_rel by blast
  ultimately show ?case using Seq_rel_par'
    by (metis Refl.hyps Refl.prems(1) Refl.prems(2) prod.exhaust_sel trancl.r_into_trancl) 
next
  case (Step y z)
  then have len:"i\<le>length (snd y) \<and> i\<le>length (snd z)" 
    using Step(1) unfolding Seq_rel_def apply auto    
    by (auto simp add: Rel_wf_def len_toSeqState) 
  then have "toSeqState i (toParState i y) = y" using Par2Seq0f by fast
  moreover have "toSeqState i (toParState i z) = z" using len  Par2Seq0f by fast
  ultimately have "(toParState i y, toParState i z) \<in> R" 
    using Step(2) Seq_rel_par' len len_toParState
    by (metis Step.prems(1) i_less_toSeq le_neq_implies_less less_add_one prod.exhaust_sel)
  then show ?case using Step by auto
qed   

lemma par_Seq_rel_tran:
    " ((g, ls), (g', ls')) \<in> R\<^sup>+ \<Longrightarrow>
        R_wf (length ls) R \<Longrightarrow> i < length ls \<Longrightarrow> length ls = length ls'\<Longrightarrow>
       (toSeqState i (g, ls), toSeqState i (g', ls')) \<in> (Seq_rel i R)\<^sup>+         
      " 
proof (induct rule:Transitive_Closure.trancl_induct[case_names Refl Step])
  case (Refl y)          
  then have  "toParState i (toSeqState i y) = y"    
    by (metis R_wf_def Seq2Par prod.exhaust_sel)   
  have f1: "\<forall>p. p = (fst p::'a, snd p::'b list)"
    by simp
  then have "length ls = length (snd y)"
    by (metis (no_types) R_wf_def Refl.hyps Refl.prems(1))
  then show ?case
    using f1 by (metis Refl.hyps Refl.prems(1) Refl.prems(2) par_rel_seq_rel trancl.r_into_trancl)    
next
  case (Step y z)  
  obtain y1 y2 z1 z2 where r:"((y1,y2), (z1,z2))\<in>R"  and "y=(y1,y2)" and "z=(z1,z2)"
    using Step.hyps(2)
    by (metis prod.exhaust_sel)
  then have "(toSeqState i  y,  toSeqState i z) \<in> Seq_rel i R" unfolding R_wf_def
    using Step.prems(1) Step.prems(2) par_rel_seq_rel[OF r]
    by (metis R_wf_def)    
  then show ?case using Step by auto
qed   

lemma Seq_rel_tran_clor_par:"((toSeqState i (g, ls), toSeqState i (g', ls'))) \<in> (Seq_rel i R)\<^sup>* \<Longrightarrow> 
         R_wf (length ls') R \<Longrightarrow>  i< length ls \<Longrightarrow>  length ls = length ls' \<Longrightarrow>
       ((g, ls), (g',ls')) \<in> R\<^sup>*"   
  apply (erule converse_rtranclE)
   apply (metis eq_toSeqState rtrancl.rtrancl_refl)
  using Seq_rel_tran_par
  by (metis (no_types, lifting) Seq2Par rtrancl_into_trancl2 trancl_into_rtrancl)  


lemma par_Seq_rel_tran':
    " ((g, ls), (g', ls')) \<in> R\<^sup>+ \<Longrightarrow>
        Rel_wf i R \<Longrightarrow> i < length ls \<Longrightarrow> i < length ls'\<Longrightarrow>
       (toSeqState i (g, ls), toSeqState i (g', ls')) \<in> (Seq_rel i R)\<^sup>+         
      " 
proof (induct rule:Transitive_Closure.trancl_induct[case_names Refl Step])
  case (Refl y)          
  then have  "toParState i (toSeqState i y) = y"
    by (metis (no_types, lifting) Seq2Par Sim_Rules.Rel_wf_def case_prodD prod.exhaust_sel)
  have f1: "\<forall>p. p = (fst p::'a, snd p::'b list)"
    by simp
  then have "i < length (snd y)" using Rel_wf_def Refl.hyps Refl.prems(1)
    by blast
  then show ?case
    by (metis Refl.hyps Refl.prems(1) Refl.prems(2) par_rel_seq_rel' 
                prod.exhaust_sel trancl.r_into_trancl)       
next
  case (Step y z)  
  obtain y1 y2 z1 z2 where r:"((y1,y2), (z1,z2))\<in>R"  and "y=(y1,y2)" and "z=(z1,z2)"
    using Step.hyps(2)
    by (metis prod.exhaust_sel)
  then have "(toSeqState i  y,  toSeqState i z) \<in> Seq_rel i R" unfolding Rel_wf_def
    using Step.prems(1) Step.prems(2) par_rel_seq_rel'[OF r]
    using Sim_Rules.Rel_wf_def by fastforce
  then show ?case using Step by auto
qed  

lemma Seq_rel_tran_clor_par':"((toSeqState i (g, ls), toSeqState i (g', ls'))) \<in> (Seq_rel i R)\<^sup>* \<Longrightarrow> 
         Rel_wf i R \<Longrightarrow>  i< length ls \<Longrightarrow>  i < length ls' \<Longrightarrow>
       ((g, ls), (g',ls')) \<in> R\<^sup>*"   
  apply (erule converse_rtranclE)
   apply (metis eq_toSeqState rtrancl.rtrancl_refl)
  using Seq_rel_tran_par'
  by (metis (no_types, lifting) Seq2Par rtrancl_into_trancl2 trancl_into_rtrancl) 

lemma par_Seq_rel_tran_clor:"((g, ls), (g',ls')) \<in> R\<^sup>* \<Longrightarrow>  
         R_wf (length ls') R \<Longrightarrow>  i< length ls \<Longrightarrow>  length ls = length ls' \<Longrightarrow>
     ((toSeqState i (g, ls), toSeqState i (g', ls'))) \<in> (Seq_rel i R)\<^sup>*
       "   
  apply (erule converse_rtranclE)
   apply (metis rtrancl.rtrancl_refl)  
  by (simp add: par_Seq_rel_tran rtrancl_into_trancl2 trancl_into_rtrancl)  

lemma par_Seq_rel_tran_clor':"((g, ls), (g',ls')) \<in> R\<^sup>* \<Longrightarrow>  
         Rel_wf i R \<Longrightarrow>  i< length ls \<Longrightarrow>  i < length ls' \<Longrightarrow>
     ((toSeqState i (g, ls), toSeqState i (g', ls'))) \<in> (Seq_rel i R)\<^sup>*
       "   
  apply (erule converse_rtranclE)
   apply (metis rtrancl.rtrancl_refl)  
  by (simp add: par_Seq_rel_tran' rtrancl_into_trancl2 trancl_into_rtrancl) 

lemma rel_tran_seq:"((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>'g, \<sigma>'ls)), 
         (toSeqState i (\<Sigma>g, \<Sigma>ls), toSeqState i (\<Sigma>'g, \<Sigma>'ls))) \<in> 
         (Seq_rel i G\<^sub>c, (Seq_rel i G\<^sub>s)\<^sup>*)\<^sub>Seq_rel i \<alpha> \<Longrightarrow> i < length \<sigma>ls \<Longrightarrow>
         R_wf (length \<sigma>ls) \<alpha> \<Longrightarrow> R_wf (length \<sigma>ls) G\<^sub>c \<Longrightarrow> R_wf (length \<sigma>ls) G\<^sub>s \<Longrightarrow>
         length \<sigma>'ls = length \<sigma>ls \<Longrightarrow> length \<sigma>ls = length \<Sigma>ls \<Longrightarrow>  
         length \<Sigma>ls =  length \<Sigma>'ls \<Longrightarrow>  
         (((\<sigma>g,\<sigma>ls), (\<sigma>'g,\<sigma>'ls)), (\<Sigma>g, \<Sigma>ls), (\<Sigma>'g, \<Sigma>'ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
  unfolding related_transitions_def 
  apply auto using Seq_rel_par apply fastforce using Seq_rel_tran_clor_par apply metis
  using Seq_rel_par apply fastforce using Seq_rel_par by fastforce 

lemma rel_tran_seq':"((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>'g, \<sigma>'ls)), 
         (toSeqState i (\<Sigma>g, \<Sigma>ls), toSeqState i (\<Sigma>'g, \<Sigma>'ls))) \<in> 
         (Seq_rel i G\<^sub>c, (Seq_rel i G\<^sub>s)\<^sup>*)\<^sub>Seq_rel i \<alpha> \<Longrightarrow> i < length \<sigma>ls \<Longrightarrow>
         Rel_wf i \<alpha> \<Longrightarrow> Rel_wf i G\<^sub>c \<Longrightarrow> Rel_wf i G\<^sub>s \<Longrightarrow>
         i < length \<sigma>'ls \<Longrightarrow> i < length \<sigma>ls \<Longrightarrow> i < length \<Sigma>ls  \<Longrightarrow>  
         i <  length \<Sigma>'ls \<Longrightarrow>  
         (((\<sigma>g,\<sigma>ls), (\<sigma>'g,\<sigma>'ls)), (\<Sigma>g, \<Sigma>ls), (\<Sigma>'g, \<Sigma>'ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
  unfolding related_transitions_def 
  apply auto using Seq_rel_par' apply fastforce using Seq_rel_tran_clor_par' apply metis
  using Seq_rel_par' apply fastforce using Seq_rel_par' by fastforce

lemma rel_tran_par:
      "(((\<sigma>g,\<sigma>ls), (\<sigma>'g,\<sigma>'ls)), (\<Sigma>g, \<Sigma>ls), (\<Sigma>'g, \<Sigma>'ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow> i < length \<sigma>ls \<Longrightarrow>
         R_wf (length \<sigma>ls) \<alpha> \<Longrightarrow> R_wf (length \<sigma>ls) G\<^sub>c \<Longrightarrow> R_wf (length \<sigma>ls) G\<^sub>s \<Longrightarrow>
         length \<sigma>'ls = length \<sigma>ls \<Longrightarrow> length \<sigma>ls = length \<Sigma>ls \<Longrightarrow>  
         length \<Sigma>ls =  length \<Sigma>'ls \<Longrightarrow>  
          ((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>'g, \<sigma>'ls)), 
         (toSeqState i (\<Sigma>g, \<Sigma>ls), toSeqState i (\<Sigma>'g, \<Sigma>'ls))) \<in> 
           (Seq_rel i G\<^sub>c, (Seq_rel i G\<^sub>s)\<^sup>*)\<^sub>Seq_rel i \<alpha>"
  unfolding related_transitions_def 
  apply auto using par_rel_seq_rel apply fastforce using par_Seq_rel_tran_clor apply metis
  using par_rel_seq_rel apply fastforce using par_rel_seq_rel by fastforce 


lemma rel_tran_par':
      "(((\<sigma>g,\<sigma>ls), (\<sigma>'g,\<sigma>'ls)), (\<Sigma>g, \<Sigma>ls), (\<Sigma>'g, \<Sigma>'ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow> i < length \<sigma>ls \<Longrightarrow>
         Rel_wf i \<alpha> \<Longrightarrow> Rel_wf i G\<^sub>c \<Longrightarrow> Rel_wf i G\<^sub>s \<Longrightarrow>
         i<length \<sigma>'ls  \<Longrightarrow> i < length \<Sigma>ls \<Longrightarrow>  
         i < length \<Sigma>'ls \<Longrightarrow>  
          ((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>'g, \<sigma>'ls)), 
         (toSeqState i (\<Sigma>g, \<Sigma>ls), toSeqState i (\<Sigma>'g, \<Sigma>'ls))) \<in> 
           (Seq_rel i G\<^sub>c, (Seq_rel i G\<^sub>s)\<^sup>*)\<^sub>Seq_rel i \<alpha>"
  unfolding related_transitions_def 
  apply auto using par_rel_seq_rel' apply fast using par_Seq_rel_tran_clor' apply metis
  using par_rel_seq_rel' apply fastforce using par_rel_seq_rel' by fastforce 

lemma R_wf_to_Rel_fwf:"R_wf (Suc i) \<alpha> \<Longrightarrow> Rel_wf i \<alpha>"
  unfolding R_wf_def Rel_wf_def apply auto
  apply (metis (no_types) lessI)
  by (metis (no_types) lessI)

definition xx
  where "xx i Q \<equiv> Seq_rel i (Q !i)"


lemma "\<Sigma>ls \<noteq> [] \<Longrightarrow> ba \<noteq> [] \<Longrightarrow>
        drop (Suc 0) \<Sigma>ls = drop (Suc 0) ba \<Longrightarrow>  \<Sigma>ls ! 0 = ba ! 0 \<Longrightarrow> ba = \<Sigma>ls"
  by (metis SmallStepCon.nth_tl drop0 drop_Suc)
 
definition seq_rels
  where "seq_rels R = map (\<lambda>i. Seq_rel i (R!i)) [ 0..< (length R)]"

(* lemma "i\<le>length \<sigma>ls \<Longrightarrow> j\<le>length \<sigma>ls \<Longrightarrow> toParState i ((\<sigma>g,\<sigma>l), \<sigma>ls) = toParState j ((\<sigma>g,\<sigma>l),\<sigma>ls)"
  unfolding toParState_def Let_def split_def apply auto

lemma assumes a0:"i< length Rs" and a1:"j< length Rs" and
       a2:"\<forall>i< length Rs. Rel_wf k (Rs!i)" and a3:"i\<le>k" and a4:"j\<le> k" and a5:"h< length Rs"
     shows "Par_rel j ((seq_rels Rs)!h) = Par_rel i ((seq_rels Rs)!h)"
proof-
  have "(seq_rels Rs)!h = Seq_rel h (Rs!h)"
    unfolding seq_rels_def using a5  by auto
  
qed *)

lemma eq_length:"length Rls = length (seq_rels Rls)"
  unfolding seq_rels_def by auto

definition Rel_wf_seq::"nat \<Rightarrow> (('g1,'l1) c_state tran set) \<Rightarrow> bool"
  where "Rel_wf_seq i R \<equiv> \<forall>(x,y)\<in>R. i<length (snd x) \<and> i<length (snd y)"

lemma Rel_wf_seq1:"Rel_wf (i+1) R1 \<Longrightarrow> Rel_wf_seq i (Seq_rel i R1)"
  unfolding Rel_wf_def Rel_wf_seq_def Seq_rel_def toSeqState_def split_def by auto 

lemma Rel_wf_seq2:"Rel_wf_seq i (Seq_rel i R1) \<Longrightarrow> Rel_wf (i+1) R1"
  unfolding Rel_wf_def Rel_wf_seq_def Seq_rel_def toSeqState_def split_def  by auto 

lemma Rel_wf_seq:"Rel_wf_seq i (Seq_rel i R1) = Rel_wf (i+1) R1"
  using Rel_wf_seq1 Rel_wf_seq2 by auto

lemma Rel_wf_subset:"Rel_wf i R2 \<Longrightarrow> R1 \<subseteq> R2 \<Longrightarrow> Rel_wf i R1"
  unfolding Rel_wf_def by fastforce

lemma R_wf_subset:"R_wf i R2 \<Longrightarrow> R1 \<subseteq> R2 \<Longrightarrow> R_wf i R1"
  unfolding R_wf_def by fastforce

lemma rest_sim: assumes    
  a0:"\<forall>i<length Rels\<^sub>c.
       R\<^sub>c \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. (Guas\<^sub>c ! j))
       \<subseteq> (Rels\<^sub>c ! i) \<and>
       R\<^sub>s \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. (Guas\<^sub>s ! j))
       \<subseteq> (Rels\<^sub>s!i)" and
    a0':"length Rels\<^sub>c = length Guas\<^sub>c \<and> length Rels\<^sub>c = length PostsQ \<and> length Rels\<^sub>c = length PostsA \<and>
         length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s " and
    a0''':"length Rels\<^sub>c >0" and
    a5:"\<forall>i<length PostsQ.                                                            
         (\<Gamma>\<^sub>c, (Coms\<^sub>c ! i,toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c !i), Seq_rel i (Guas\<^sub>c!i)) 
           \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>) 
         (\<Gamma>\<^sub>s,(Coms\<^sub>s! i,toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s!i), Seq_rel i (Guas\<^sub>s !i))" and
   a0'': "length Coms\<^sub>c = length Coms\<^sub>s" and
   a01'':"length Rels\<^sub>c = length Coms\<^sub>s" and      
   i_len:"i<length PostsQ" and  
   alpha_rel_guar:
      " (toSeqState i (\<sigma>'g, (\<sigma>'ls)), toSeqState i (\<Sigma>'g, \<Sigma>'ls)) \<in> Seq_rel i \<alpha> \<and>
        ((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>'g, (\<sigma>'ls))), 
           toSeqState i (\<Sigma>g, \<Sigma>ls), toSeqState i (\<Sigma>'g, \<Sigma>'ls)) 
             \<in> ((Seq_rel i (Guas\<^sub>c ! i), (Seq_rel i (Guas\<^sub>s ! i))\<^sup>*)\<^sub>(Seq_rel i \<alpha>)) \<and>
         (\<Gamma>\<^sub>c,(c', toSeqState i (\<sigma>'g, (\<sigma>'ls))), 
            Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
         (\<Gamma>\<^sub>s,(c\<^sub>s', toSeqState i (\<Sigma>'g, \<Sigma>'ls)),
             Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" and
   step:"i< length Coms\<^sub>c \<and>
        (\<forall>j. j\<noteq>i \<longrightarrow> Coms'\<^sub>c ! j = (Coms\<^sub>c !j)) \<and> Coms'\<^sub>c ! i= c' " and
   a15:"R_wf (length PostsQ) \<alpha>" and a16:"R_wf (length PostsQ) G\<^sub>c" and 
   a17:"R_wf (length PostsQ) G\<^sub>s" and a18:"\<forall>i<length PostsQ. R_wf (length PostsQ) (Guas\<^sub>c ! i)" and
   a19:"\<forall>i<length PostsQ. R_wf (length PostsQ) (Guas\<^sub>s ! i)" and 
   a20:"\<forall>i<length PostsQ. R_wf (length PostsQ) (Rels\<^sub>s ! i)" and
   a21:"\<forall>i<length PostsQ. R_wf (length PostsQ) (Rels\<^sub>c ! i)" and 
   len_\<sigma>:"length \<sigma>ls = length PostsQ" and "length \<sigma>ls = length \<sigma>'ls" and
   len_\<Sigma>:"length \<Sigma>ls = length \<sigma>ls" and len_\<Sigma>':"length \<Sigma>ls = length \<Sigma>'ls"
   shows "\<forall>i'<length PostsQ. (\<Gamma>\<^sub>c,(Coms'\<^sub>c ! i', toSeqState i' (\<sigma>'g,\<sigma>'ls)),
             Seq_rel i' (Rels\<^sub>c ! i'),Seq_rel i' (Guas\<^sub>c ! i')) 
          \<succeq>\<^sub>(\<^sub>Seq_rel i' \<alpha>\<^sub>;\<^sub>xx i' PostsQ\<^sub>;\<^sub>xx i' PostsA\<^sub>)
        (\<Gamma>\<^sub>s,(Coms\<^sub>s[i:=c\<^sub>s'] ! i', toSeqState i' (\<Sigma>'g, \<Sigma>'ls)),
            Seq_rel i' (Rels\<^sub>s ! i'),Seq_rel i' (Guas\<^sub>s ! i'))" 
proof-
 { fix i'
   assume i'_len:"i'<length PostsQ"
   { assume "i' = i" 
     then have 
       "(\<Gamma>\<^sub>c,(Coms'\<^sub>c ! i', toSeqState i' (\<sigma>'g, \<sigma>'ls)),Seq_rel i' (Rels\<^sub>c ! i'),Seq_rel i' (Guas\<^sub>c ! i'))
       \<succeq>\<^sub>(\<^sub>Seq_rel i' \<alpha>\<^sub>;\<^sub>xx i' PostsQ\<^sub>;\<^sub>xx i' PostsA\<^sub>)
    (\<Gamma>\<^sub>s,(Coms\<^sub>s[i := c\<^sub>s'] ! i', toSeqState i' (\<Sigma>'g, \<Sigma>'ls)),Seq_rel i' (Rels\<^sub>s ! i'),Seq_rel i' (Guas\<^sub>s ! i'))"
     using i'_len alpha_rel_guar step a0' a01'' by auto
   }
   moreover { assume i_i':"i'\<noteq>i"                  
     then have sim:
      "(\<Gamma>\<^sub>c, (Coms\<^sub>c ! i',toSeqState i' (\<sigma>g, \<sigma>ls)),Seq_rel i' (Rels\<^sub>c !i'), Seq_rel i' (Guas\<^sub>c!i')) 
         \<succeq>\<^sub>(\<^sub>Seq_rel i' \<alpha>\<^sub>;\<^sub>xx i' PostsQ\<^sub>;\<^sub>xx i' PostsA\<^sub>) 
       (\<Gamma>\<^sub>s,(Coms\<^sub>s! i',toSeqState i' (\<Sigma>g, \<Sigma>ls)),Seq_rel i' (Rels\<^sub>s!i'), Seq_rel i' (Guas\<^sub>s !i'))"
       using step a5 a0' a0'' a01'' i'_len by blast             
     have rel_alpha:"(toSeqState i' (\<sigma>'g, (\<sigma>'ls)), toSeqState i' (\<Sigma>'g, \<Sigma>'ls)) \<in> Seq_rel i' \<alpha> \<and>
                     ((toSeqState i' (\<sigma>g, \<sigma>ls), toSeqState i' (\<sigma>'g, (\<sigma>'ls))), 
                       toSeqState i' (\<Sigma>g, \<Sigma>ls), toSeqState i' (\<Sigma>'g, \<Sigma>'ls)) 
                   \<in> ((Seq_rel i' (Rels\<^sub>c ! i'), (Seq_rel i' (Rels\<^sub>s ! i'))\<^sup>*)\<^sub>(Seq_rel i' \<alpha>))" 
     proof- 
     {                 
       have x:
         "(toSeqState i (\<sigma>'g, (\<sigma>'ls)), toSeqState i (\<Sigma>'g, \<Sigma>'ls)) \<in> Seq_rel i \<alpha> \<and>
          ((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>'g, (\<sigma>'ls))), 
            toSeqState i (\<Sigma>g, \<Sigma>ls), toSeqState i (\<Sigma>'g, \<Sigma>'ls)) 
            \<in> ((Seq_rel i (Guas\<^sub>c ! i), (Seq_rel i (Guas\<^sub>s ! i))\<^sup>*)\<^sub>(Seq_rel i \<alpha>))" 
         using alpha_rel_guar by auto
       have "i' < length Rels\<^sub>c" using a0' i'_len by auto
       moreover have "i < length Guas\<^sub>c \<and> i < length Guas\<^sub>s" using a0' i_len by auto
       ultimately have "Guas\<^sub>c ! i \<subseteq> Rels\<^sub>c ! i' \<and> Guas\<^sub>s ! i \<subseteq> Rels\<^sub>s ! i'" 
         using a0 a01'' i_i' by blast 
       moreover  have 
         h:"(((\<sigma>g, \<sigma>ls), (\<sigma>'g, (\<sigma>'ls))), (\<Sigma>g, \<Sigma>ls),(\<Sigma>'g, \<Sigma>'ls)) \<in> (Guas\<^sub>c ! i, (Guas\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha>"              
          using rel_tran_seq[OF conjunct2[OF x]] a15 a18 
              a19 assms(18) i_len len_\<Sigma> len_\<Sigma>' len_\<sigma> by presburger              
        then have 
          h:"(((\<sigma>g, \<sigma>ls), (\<sigma>'g, (\<sigma>'ls))), (\<Sigma>g, \<Sigma>ls),(\<Sigma>'g, \<Sigma>'ls)) \<in> (Rels\<^sub>c ! i', (Rels\<^sub>s ! i')\<^sup>*)\<^sub>\<alpha>"
          using G_comp1[OF _ _ h, of "Rels\<^sub>c ! i'" "Rels\<^sub>s ! i'"] calculation
          by auto
       thus ?thesis using rel_tran_par[OF h]
         by (metis \<open>i' < length Rels\<^sub>c\<close> a0' a15 a20 a21 assms(18) 
               dest_sim_alpha env_sim len_\<Sigma> len_\<Sigma>' len_\<sigma> sim) 
     } qed                 
     have "(\<Gamma>\<^sub>c,(Coms'\<^sub>c ! i', toSeqState i' (\<sigma>'g, (\<sigma>'ls))), Seq_rel i' (Rels\<^sub>c ! i'),Seq_rel i' (Guas\<^sub>c ! i'))
          \<succeq>\<^sub>(\<^sub>Seq_rel i' \<alpha>\<^sub>;\<^sub>xx i' PostsQ\<^sub>;\<^sub>xx i' PostsA\<^sub>)
        (\<Gamma>\<^sub>s,(Coms\<^sub>s[i:=c\<^sub>s'] ! i', toSeqState i' (\<Sigma>'g, \<Sigma>'ls)), Seq_rel i' (Rels\<^sub>s ! i'),Seq_rel i' (Guas\<^sub>s ! i'))"          
       using i_i' alpha_rel_guar step  
            sim_comp_not_mod[OF sim conjunct2[OF rel_alpha]] by auto
   }
   ultimately have 
    "(\<Gamma>\<^sub>c,(Coms'\<^sub>c ! i', toSeqState i' (\<sigma>'g, \<sigma>'ls)),Seq_rel i' (Rels\<^sub>c ! i'),Seq_rel i' (Guas\<^sub>c ! i'))
       \<succeq>\<^sub>(\<^sub>Seq_rel i' \<alpha>\<^sub>;\<^sub>xx i' PostsQ\<^sub>;\<^sub>xx i' PostsA\<^sub>)
    (\<Gamma>\<^sub>s,(Coms\<^sub>s[i := c\<^sub>s'] ! i', toSeqState i' (\<Sigma>'g, \<Sigma>'ls)),Seq_rel i' (Rels\<^sub>s ! i'),Seq_rel i' (Guas\<^sub>s ! i'))"
      using i_len i'_len  by fastforce        
 } thus  ?thesis by auto
qed 

    
(* lemma par_all_skip_rtran:
    "\<forall>i<length C. \<Gamma>\<turnstile>\<^sub>c (C!i, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, s) \<Longrightarrow> length C > 0 \<Longrightarrow>
       \<exists>C'. \<Gamma>\<turnstile>\<^sub>p (C,s) \<rightarrow>\<^sub>\<tau>\<^sup>* (C', s) \<and> (\<forall>i<length C'. C' ! i = Skip) \<and> C' \<noteq> []"
proof (induction C )
  case (Nil) thus ?case by auto
next
  case (Cons a as)   
  {assume a0:"as=Nil"    
   then have "\<Gamma>\<turnstile>\<^sub>p (a#as, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (a#as[0:=Skip],s)" 
     using  Cons(2) mult_step_in_par by auto
   then have ?case using a0
     by (metis Cons.prems(1) length_Cons length_list_update less_Suc0 list.discI list.size(3) 
               list_update.simps(1) mult_step_in_par nth_list_update_eq) 
  }
  moreover { fix a1 as1
    assume a0:"as=a1#as1"
    then have "\<forall>i<length (as). \<Gamma>\<turnstile>\<^sub>c (as ! i, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, s)" 
      using Cons by auto
    moreover have "0 < length as" using a0 by auto
    ultimately obtain c'' where 
     x:"\<Gamma>\<turnstile>\<^sub>p (as, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c'',s) \<and> (\<forall>i<length c''. c'' ! i = LanguageCon.com.Skip) \<and> c'' \<noteq> []"
      using Cons(1) by auto
    then have "\<Gamma>\<turnstile>\<^sub>p (a#as, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (a#c'', s)" using par_tran_comp_rtran by auto
    moreover have step_c:"\<Gamma>\<turnstile>\<^sub>c ((a # c'') ! 0, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, s)" using Cons by auto
    ultimately have "\<Gamma>\<turnstile>\<^sub>p (a # as, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip#c'', s)" 
      using ParComp[of 0 "a#c''"] rtranclp.simps
    proof -
      have "\<Gamma>\<turnstile>\<^sub>p (a # c'',s) \<rightarrow>\<^sub>\<tau>\<^sup>* ((a # c'')[0 := LanguageCon.com.Skip], s)"
        using step_c mult_step_in_par by blast
      then show ?thesis
        using \<open>\<Gamma>\<turnstile>\<^sub>p (a # as, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (a # c'',s)\<close> by fastforce
    qed 
    then have ?case using x
      by (metis (no_types, lifting) length_Cons less_Suc_eq_0_disj list.discI nth_Cons_0 nth_Cons_Suc)  
  }      
  ultimately show ?case
    using list.exhaust by blast
      
qed *)

  
lemma aaa:"Suc i< length a \<Longrightarrow> Suc i< length b \<Longrightarrow> Suc i< length c \<Longrightarrow> Suc i<length d \<Longrightarrow> 
Suc i< length e \<Longrightarrow> Suc i< length f \<Longrightarrow> Suc i< length g \<Longrightarrow> Suc i<length h \<Longrightarrow> 
P (a!(Suc i)) (b!(Suc i)) (c!(Suc i)) (d!(Suc i)) (e!(Suc i)) (f!(Suc i)) (g!(Suc i)) (h!(Suc i)) \<Longrightarrow> 
P ((drop 1 a) !i) ((drop 1 b) !i) ((drop 1 c) !i) ((drop 1 d) !i) ((drop 1 e) !i) ((drop 1 f) !i) ((drop 1 g) !i) ((drop 1 h) !i)"  
  by fastforce  

lemma bbb:"length a = length b \<and> length a = length c \<and> length a = length d \<and>
           length a = length e \<and> length a = length f \<and> length a = length g \<and>
           length a = length h \<Longrightarrow>
          Suc i<length a \<Longrightarrow> P (a!(Suc i)) (b!(Suc i)) (c!(Suc i)) (d!(Suc i)) (e!(Suc i)) (f!(Suc i)) (g!(Suc i)) (h!(Suc i)) \<Longrightarrow> 
          P ((drop 1 a) !i) ((drop 1 b) !i) ((drop 1 c) !i) ((drop 1 d) !i) ((drop 1 e) !i) ((drop 1 f) !i) ((drop 1 g) !i) ((drop 1 h) !i)"
  using aaa by auto
  
lemma ccc:
assumes a0:"length a = length b \<and> length a = length c \<and> length a = length d \<and>
           length a = length e \<and> length a = length f \<and> length a = length g \<and>
           length a = length h" and
        a1:"\<forall>i<length a.   P (a!i) (b!i) (c!i) (d!i) (e!i) (f!i) (g!i) (h!i)"
      shows  "\<forall>i<length (drop 1 a). P ((drop 1 a) !i) ((drop 1 b) !i) ((drop 1 c) !i) ((drop 1 d) !i) ((drop 1 e) !i) ((drop 1 f) !i) ((drop 1 g) !i) ((drop 1 h) !i)"
proof -
  {fix i
  assume a3:"i<length (drop 1 a)"
  then have a4:"Suc i < length a" by auto
  then have a5:" P (a!Suc i) (b!Suc i) (c!Suc i) (d!Suc i) (e!Suc i) (f!Suc i) (g!Suc i) (h!Suc i)" 
    using a1 by auto
  then have "P ((drop 1 a) !i) ((drop 1 b) !i) ((drop 1 c) !i) ((drop 1 d) !i) ((drop 1 e) !i) ((drop 1 f) !i) ((drop 1 g) !i) ((drop 1 h) !i)"   
    using bbb[OF a0 a4] by auto
 }thus ?thesis by auto
qed
 
  
(* lemma x1:"\<forall>i<length C\<^sub>s'. C\<^sub>s'!i = Skip \<Longrightarrow> i< length ((Ca # C\<^sub>s')[0 := LanguageCon.com.Skip] ) \<Longrightarrow>
           (Ca # C\<^sub>s')[0 := LanguageCon.com.Skip] ! i = LanguageCon.com.Skip"
  sorry *)
  
lemma  G_in_R_drop:
  assumes a0:"\<forall>i<length R. A \<union> (\<Union>a\<in>{j. j < length G \<and> j \<noteq> i}. G ! a) \<subseteq> R ! i" and
          a1:"length R>0" and a2:"length G=length R"
  shows"\<forall>i<length (drop 1 R). 
        A \<union> (\<Union>a\<in>{j. j < length (drop 1 G) \<and> j \<noteq> i}. 
                   (drop 1 G) ! a) \<subseteq> (drop 1 R) ! i"        
  proof-
  {fix i
    assume len:"i<length (drop 1 R)"             
    then have r1:       
    "A \<union> (\<Union>a\<in>{j. j < length G \<and> j \<noteq> (Suc i)}. G ! a) \<subseteq> R ! (Suc i)"
      using a0 by auto
    have "(\<Union>a\<in>{j. j < length (drop 1 G) \<and> j \<noteq> i}. (drop 1 G) ! a) \<union> G ! 0 = 
         (\<Union>a\<in>{j. j < length G \<and> j \<noteq> (Suc i)}. G ! a) "          
    proof- 
      { fix x
        assume a0:"x \<in> ((\<Union>a\<in>{j. j < length (drop 1 G) \<and> j \<noteq> i}. (drop 1 G) ! a) \<union> G ! 0)"                       
        then have "x\<in>(\<Union>a\<in>{j. j < length G \<and> j \<noteq> (Suc i)}. G ! a)"
          using a0 a1 a2
          apply auto 
          apply (subgoal_tac "Suc xa<length G") 
            by auto               
      }
      moreover 
      {fix x
        fix j
        assume a00: "j < length G" and
               a01:"j \<noteq> Suc i" and
               a02:"x\<in>G !j"
        then have "(\<exists>j. j<length (drop 1 G) \<and> j\<noteq>i \<and> x\<in>(drop 1 G) ! j) \<or> x \<in>G ! 0"             
        proof-
          { assume a03:"j=0"
            then have ?thesis using a00 a01 a02 by auto
          }
          moreover {
            assume a03:"j\<noteq>0"            
            then obtain j' where suc: "j = Suc j'" 
              using not_gr_zero gr0_implies_Suc by auto
            then have "j'<length G - Suc 0 \<and> j' \<noteq> i \<and> x \<in> drop (Suc 0) G ! j'"
              using a00 a01 a02  by auto                      
            then have ?thesis using a00 a01 a02  by auto
          }
          ultimately show ?thesis by auto
        qed
        then have "x \<in> ((\<Union>a\<in>{j. j < length (drop 1 G) \<and> j \<noteq> i}. (drop 1 G)!a) \<union> G ! 0)"
          by auto             
      }              
      ultimately show ?thesis by fast qed
    then have "(\<Union>a\<in>{j. j < length (drop 1 G) \<and> j \<noteq> i}. (drop 1 G) ! a) \<subseteq> 
               (\<Union>a\<in>{j. j < length G \<and> j \<noteq> (Suc i)}. G ! a)"
      by auto
    then have "A \<union> (\<Union>a\<in>{j. j < length (drop 1 G) \<and> j \<noteq> i}. (drop 1 G) ! a) \<subseteq> (drop 1 R) ! i"
      using r1 len by auto          
  } thus ?thesis by fastforce
  qed   

lemma tran_Guar:
  assumes 
          a1:"0 < length (Ca # Cs)" and          
          a3:"length (Ca # Cs) = length C\<^sub>c \<and> length (Ca # Cs) = length Rels\<^sub>c" and
          a4:"length Rels\<^sub>c = length Guas\<^sub>c \<and>
              length Rels\<^sub>c = length PostsQ \<and>
              length Rels\<^sub>c = length PostsA \<and> length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s" and
           a5:"(((\<sigma>, \<sigma>),(\<Sigma>1, \<Sigma>2)) \<in> (Guas\<^sub>c!0,(Guas\<^sub>s!0)\<^sup>*)\<^sub>\<alpha>)" and
           a6:"Guasc = drop 1 Guas\<^sub>c \<and> Guass = drop 1 Guas\<^sub>s \<and> Postsq = drop 1 PostsQ \<and> 
             Postsa = drop 1 PostsA \<and> Csc = drop 1 C\<^sub>c" and
           a7:"(( \<sigma>,  \<sigma>), \<Sigma>, \<Sigma>1) \<in> 
                 (((\<Union>j<length Guasc. (Guasc !j)), (\<Union>j<length Guass. (Guass !j))\<^sup>*)\<^sub>\<alpha>) \<and>                   
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Cs,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s', \<Sigma>1)"
    shows "((\<sigma>, \<sigma>), \<Sigma>, \<Sigma>2) \<in> 
            (((\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)), (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s !j))\<^sup>*)\<^sub>\<alpha>)"
proof-
  have len:"0<length Guas\<^sub>s" using a7 a1 a3 a4 by auto
  then have f1:"((\<sigma>, \<sigma>), \<Sigma>, \<Sigma>2) \<in> 
          (((\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)), ((\<Union>j<length Guass. (Guass !j))\<union>(Guas\<^sub>s!0) )\<^sup>*)\<^sub>\<alpha>)"
  using a4 a7 a6 a5 a3  unfolding related_transitions_def
  apply auto   by (meson in_rtrancl_UnI rtrancl_trans)
  then have "(\<Union>j<length Guass. (Guass !j))\<union>(Guas\<^sub>s!0) \<subseteq>(\<Union>j<length Guas\<^sub>s. Guas\<^sub>s ! j)"
  using a6 len by fastforce
    thus ?thesis using  G_comp1[OF _ _ f1] by auto  
  qed
    
lemma guar_i_rely_j:
  assumes 
     a0:"0<length PostsQ" and
     a1:"length Rels\<^sub>c = length Guas\<^sub>c \<and>
        length Rels\<^sub>c = length PostsQ \<and>
        length Rels\<^sub>c = length PostsA \<and> length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s" and
     a2:"\<forall>i<length Rels\<^sub>c. R\<^sub>c \<union> (\<Union>a\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. Guas\<^sub>c ! a) \<subseteq> Rels\<^sub>c ! i" and
     a3:"\<forall>i<length Rels\<^sub>s. R\<^sub>s \<union> (\<Union>a\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. Guas\<^sub>s ! a) \<subseteq> Rels\<^sub>s ! i" and
     a4:"(((\<sigma>, \<sigma>),(\<Sigma>, \<Sigma>')) \<in> (Guas\<^sub>c!0,(Guas\<^sub>s!0)\<^sup>*)\<^sub>\<alpha>)"             
    shows "\<forall>i<length Guas\<^sub>c. i\<noteq>0 \<longrightarrow> (((\<sigma>, \<sigma>), \<Sigma>, \<Sigma>') \<in> (Rels\<^sub>c ! i, (Rels\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha>) "
      
proof-
  have inguars:"\<forall>i<length Rels\<^sub>c. i\<noteq>0 \<longrightarrow> Guas\<^sub>c!0 \<subseteq> Rels\<^sub>c!i \<and> Guas\<^sub>s!0 \<subseteq> Rels\<^sub>s!i"
  proof-
    {fix i
      assume a00:"i<length Rels\<^sub>c"  and a01:"i\<noteq>0"        
      have lens:"i<length Rels\<^sub>s" using a00 a1 by auto
      also have "0<length Guas\<^sub>c \<and> 0<length Guas\<^sub>s" using a0 a1 by auto
      ultimately have "Guas\<^sub>c!0 \<subseteq> Rels\<^sub>c!i \<and> Guas\<^sub>s!0 \<subseteq> Rels\<^sub>s!i" using a00 a01 a2 a3 a0 a1 
      by blast        
    }thus ?thesis by auto    
  qed
  then show ?thesis
  proof-
    {fix i
    assume a00:"i<length Guas\<^sub>c" and a01:"i\<noteq>0"
    then have "i<length Rels\<^sub>c" using a00 a1 by auto
    then have "Guas\<^sub>c!0 \<subseteq> Rels\<^sub>c!i \<and> Guas\<^sub>s!0 \<subseteq> Rels\<^sub>s!i" using a01 inguars by fastforce
    then have "(((\<sigma>, \<sigma>), \<Sigma>, \<Sigma>') \<in> (Rels\<^sub>c ! i, (Rels\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha>)"
      using G_comp1 a4 by auto }
    thus ?thesis by auto
  qed    
qed
  
 lemma all_skip_tran:
  assumes a0:"\<forall>i<length PostsQ. (\<Gamma>\<^sub>c,(C\<^sub>c ! i, \<sigma>),Rels\<^sub>c ! i,Guas\<^sub>c ! i) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>PostsQ ! i\<^sub>;\<^sub>PostsA ! i\<^sub>) 
              (\<Gamma>\<^sub>s,((Ca # Cs) ! i, \<Sigma>),Rels\<^sub>s ! i,Guas\<^sub>s ! i)" and       
       a1:"0 < length (Ca # Cs)" and
       a2:"\<forall>i<length C\<^sub>c. C\<^sub>c ! i = LanguageCon.com.Skip" and      
       a5:"length (Ca # Cs) = length C\<^sub>c \<and> length (Ca # Cs) = length Rels\<^sub>c" and
       a6:"length Rels\<^sub>c = length Guas\<^sub>c \<and>
          length Rels\<^sub>c = length PostsQ \<and>
          length Rels\<^sub>c = length PostsA \<and> length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s" and                     
       a11:"\<forall>i<length PostsQ. Sta\<^sub>s (PostsQ ! i) (Rels\<^sub>c ! i, (Rels\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha>" and
       a12:"\<forall>i<length Rels\<^sub>c. R\<^sub>c \<union> (\<Union>a\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. Guas\<^sub>c ! a) \<subseteq> Rels\<^sub>c ! i" and
       a13:"\<forall>i<length Rels\<^sub>s. R\<^sub>s \<union> (\<Union>a\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. Guas\<^sub>s ! a) \<subseteq> Rels\<^sub>s ! i" and
       a14:"(((\<sigma>, \<sigma>),(\<Sigma>', \<Sigma>2)) \<in> (Guas\<^sub>c!0,(Guas\<^sub>s!0)\<^sup>*)\<^sub>\<alpha>)  \<and>
            (\<sigma>, \<Sigma>2)\<in>PostsQ!0 \<and> PostsQ!0\<subseteq>\<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Ca, \<Sigma>1) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip,\<Sigma>2)" and
       a15':"Guasc = drop 1 Guas\<^sub>c \<and> Guass = drop 1 Guas\<^sub>s \<and> Postsq = drop 1 PostsQ \<and> 
             Postsa = drop 1 PostsA \<and> Csc = drop 1 C\<^sub>c" and
       a15:"((\<sigma>, \<sigma>), \<Sigma>, \<Sigma>1) \<in> 
                 (((\<Union>j<length Guasc. (Guasc !j)), (\<Union>j<length Guass. (Guass !j))\<^sup>*)\<^sub>\<alpha>) \<and> 
            (\<sigma>, \<Sigma>1)\<in> (\<Inter>i<length Postsq.  (Postsq ! i)) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Cs,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s', \<Sigma>1) \<and> (\<forall>i<length C\<^sub>s'. C\<^sub>s' ! i = Skip) \<and> C\<^sub>s' \<noteq> []" and
       a16:"Cs=Ca1#Cs1"
     shows "((\<sigma>, \<sigma>), \<Sigma>, \<Sigma>2) \<in> 
                 (((\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)), (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s !j))\<^sup>*)\<^sub>\<alpha>) \<and> 
            (\<sigma>, \<Sigma>2)\<in> (\<Inter>i<length PostsQ.  (PostsQ ! i)) \<and> 
                 (\<exists>C\<^sub>s''. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca # Cs,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s'', \<Sigma>2) \<and> (\<forall>i<length C\<^sub>s''. C\<^sub>s'' ! i = Skip) \<and> C\<^sub>s'' \<noteq> [])"
proof-  
  have "((\<sigma>, \<sigma>), \<Sigma>, \<Sigma>2) \<in> 
            (((\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)), (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s !j))\<^sup>*)\<^sub>\<alpha>)"
  using tran_Guar[OF a1 a4 a5 a6 _ a15' ] a15 a14 by auto
  moreover have "(ns\<^sub>c, ns2)\<in> (\<Inter>i<length PostsQ.  (PostsQ ! i))"
  proof-
    {fix i
     assume a00: "i<length PostsQ" 
     have len:"0<length PostsQ"  using a15' a1 a6 a5 by auto         
    have guars:"\<forall>i<length Guas\<^sub>c. i\<noteq>0 \<longrightarrow> ((\<sigma>, \<sigma>), \<Sigma>1, \<Sigma>2) \<in> (Rels\<^sub>c ! i, (Rels\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha> \<and> (\<sigma>, \<Sigma>2)\<in> \<alpha>\<^sub>x"
      using guar_i_rely_j[OF len a6 a12 a13 ] a14  a3 unfolding alpha_xstate_def by auto
    have "(ns\<^sub>c, ns2) \<in> (\<Inter>i<length Postsq. Postsq ! i)"
    proof-
      {fix i
        assume a00:"i<length Postsq"
        then have suc:"Suc i<length PostsQ \<and> Suc i\<noteq>0" using a15' by auto
        then have "((\<sigma>, \<sigma>), \<Sigma>1, \<Sigma>2) \<in> (Rels\<^sub>c ! Suc i, (Rels\<^sub>s ! Suc i)\<^sup>*)\<^sub>\<alpha>"
          using guars a6 by auto
        also have "(ns\<^sub>c, ns1)\<in> (PostsQ ! Suc i)" using a15 a15' suc by auto
        ultimately have "(ns\<^sub>c, ns2) \<in> PostsQ ! (Suc i)"
          using a3 a11 suc guars unfolding Sta\<^sub>s_def by fast    
        then have "(ns\<^sub>c, ns2) \<in> Postsq ! i"  using suc a00 a15' by auto           
      }thus ?thesis by auto
    qed      
    then have "(ns\<^sub>c, ns2)\<in>(PostsQ ! i)" using a14 a15' a00              
      by (cases i, auto)
    } thus ?thesis by auto
  qed
  moreover have "\<exists>C\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca # Cs,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s', \<Sigma>2) \<and> (\<forall>i<length C\<^sub>s'. C\<^sub>s' ! i = Skip) \<and> C\<^sub>s' \<noteq> []"
  proof-
    have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca#Cs, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Ca#C\<^sub>s', \<Sigma>1)"
      using a15 by (simp add: par_tran_comp_rtran)    
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca # Cs,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* ((Ca#C\<^sub>s')[0:=Skip], \<Sigma>2)"
      using a14 par_tran_comp_rtran a15 mult_step_in_par[of \<Gamma>\<^sub>s "Ca#C\<^sub>s'" 0 "\<Sigma>1" "Skip" "\<Sigma>2"]
      by auto        
    moreover have "(\<forall>i<length ((Ca # C\<^sub>s')[0 := LanguageCon.com.Skip]). 
        ((Ca # C\<^sub>s')[0 := LanguageCon.com.Skip]) ! i = Skip)"      
    proof -
      {fix i
        assume a00:"i<length  ((Ca # C\<^sub>s')[0 := LanguageCon.com.Skip])"
        then have "(Ca # C\<^sub>s')[0 := LanguageCon.com.Skip] ! i = LanguageCon.com.Skip"
          using a15  apply (cases i) by auto
      }  thus ?thesis by auto      
    qed
    moreover have "((Ca # C\<^sub>s')[0 := LanguageCon.com.Skip]) \<noteq> []" by auto      
    ultimately show ?thesis by auto
  qed    
  ultimately show ?thesis by auto
qed

    
lemma all_skip_tran:
  assumes a0:"\<forall>i<length PostsQ. (\<Gamma>\<^sub>c,(C\<^sub>c ! i, \<sigma>),Rels\<^sub>c ! i,Guas\<^sub>c ! i) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>PostsQ ! i\<^sub>;\<^sub>PostsA ! i\<^sub>) 
              (\<Gamma>\<^sub>s,((Ca # Cs) ! i, s\<^sub>s),Rels\<^sub>s ! i,Guas\<^sub>s ! i)" and       
       a1:"0 < length (Ca # Cs)" and
       a2:"\<forall>i<length C\<^sub>c. C\<^sub>c ! i = LanguageCon.com.Skip" and
       a3:" \<sigma> = Normal ns\<^sub>c" and
       a4:" s\<^sub>s = Normal ns\<^sub>s" and
       a5:"length (Ca # Cs) = length C\<^sub>c \<and> length (Ca # Cs) = length Rels\<^sub>c" and
       a6:"length Rels\<^sub>c = length Guas\<^sub>c \<and>
          length Rels\<^sub>c = length PostsQ \<and>
          length Rels\<^sub>c = length PostsA \<and> length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s" and                     
       a11:"\<forall>i<length PostsQ. Sta\<^sub>s (PostsQ ! i) (Rels\<^sub>c ! i, (Rels\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha>" and
       a12:"\<forall>i<length Rels\<^sub>c. R\<^sub>c \<union> (\<Union>a\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. Guas\<^sub>c ! a) \<subseteq> Rels\<^sub>c ! i" and
       a13:"\<forall>i<length Rels\<^sub>s. R\<^sub>s \<union> (\<Union>a\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. Guas\<^sub>s ! a) \<subseteq> Rels\<^sub>s ! i" and
       a14:"(((\<sigma>, \<sigma>),(Normal ns1, Normal ns2)) \<in> (Guas\<^sub>c!0,(Guas\<^sub>s!0)\<^sup>*)\<^sub>\<alpha>)  \<and>
            (ns\<^sub>c, ns2)\<in>PostsQ!0 \<and> PostsQ!0\<subseteq>\<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Ca, Normal ns1) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip,Normal ns2)" and
       a15':"Guasc = drop 1 Guas\<^sub>c \<and> Guass = drop 1 Guas\<^sub>s \<and> Postsq = drop 1 PostsQ \<and> 
             Postsa = drop 1 PostsA \<and> Csc = drop 1 C\<^sub>c" and
       a15:"((\<sigma>, \<sigma>), s\<^sub>s, Normal ns1) \<in> 
                 (((\<Union>j<length Guasc. (Guasc !j)), (\<Union>j<length Guass. (Guass !j))\<^sup>*)\<^sub>\<alpha>) \<and> 
            (ns\<^sub>c, ns1)\<in> (\<Inter>i<length Postsq.  (Postsq ! i)) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Cs,s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s', Normal ns1) \<and> (\<forall>i<length C\<^sub>s'. C\<^sub>s' ! i = Skip) \<and> C\<^sub>s' \<noteq> []" and
       a16:"Cs=Ca1#Cs1"
     shows "((\<sigma>, \<sigma>), s\<^sub>s, Normal ns2) \<in> 
                 (((\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)), (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s !j))\<^sup>*)\<^sub>\<alpha>) \<and> 
            (ns\<^sub>c, ns2)\<in> (\<Inter>i<length PostsQ.  (PostsQ ! i)) \<and> 
                 (\<exists>C\<^sub>s''. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca # Cs,s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s'', Normal ns2) \<and> (\<forall>i<length C\<^sub>s''. C\<^sub>s'' ! i = Skip) \<and> C\<^sub>s'' \<noteq> [])"
proof-  
  have "((\<sigma>, \<sigma>), s\<^sub>s, Normal ns2) \<in> 
            (((\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)), (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s !j))\<^sup>*)\<^sub>\<alpha>)"
  using tran_Guar[OF a1 a4 a5 a6 _ a15' ] a15 a14 by auto
  moreover have "(ns\<^sub>c, ns2)\<in> (\<Inter>i<length PostsQ.  (PostsQ ! i))"
  proof-
    {fix i
     assume a00: "i<length PostsQ" 
     have len:"0<length PostsQ"  using a15' a1 a6 a5 by auto         
    have guars:"\<forall>i<length Guas\<^sub>c. i\<noteq>0 \<longrightarrow> ((\<sigma>, \<sigma>), Normal ns1, Normal ns2) \<in> (Rels\<^sub>c ! i, (Rels\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha> \<and> (\<sigma>, Normal ns2)\<in> \<alpha>\<^sub>x"
      using guar_i_rely_j[OF len a6 a12 a13 ] a14  a3 unfolding alpha_xstate_def by auto
    have "(ns\<^sub>c, ns2) \<in> (\<Inter>i<length Postsq. Postsq ! i)"
    proof-
      {fix i
        assume a00:"i<length Postsq"
        then have suc:"Suc i<length PostsQ \<and> Suc i\<noteq>0" using a15' by auto
        then have "((\<sigma>, \<sigma>), Normal ns1, Normal ns2) \<in> (Rels\<^sub>c ! Suc i, (Rels\<^sub>s ! Suc i)\<^sup>*)\<^sub>\<alpha>"
          using guars a6 by auto
        also have "(ns\<^sub>c, ns1)\<in> (PostsQ ! Suc i)" using a15 a15' suc by auto
        ultimately have "(ns\<^sub>c, ns2) \<in> PostsQ ! (Suc i)"
          using a3 a11 suc guars unfolding Sta\<^sub>s_def by fast    
        then have "(ns\<^sub>c, ns2) \<in> Postsq ! i"  using suc a00 a15' by auto           
      }thus ?thesis by auto
    qed      
    then have "(ns\<^sub>c, ns2)\<in>(PostsQ ! i)" using a14 a15' a00              
      by (cases i, auto)
    } thus ?thesis by auto
  qed
  moreover have "\<exists>C\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca # Cs,s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s', Normal ns2) \<and> (\<forall>i<length C\<^sub>s'. C\<^sub>s' ! i = Skip) \<and> C\<^sub>s' \<noteq> []"
  proof-
    have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca#Cs, s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Ca#C\<^sub>s', Normal ns1)"
      using a15 by (simp add: par_tran_comp_rtran)    
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca # Cs,s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* ((Ca#C\<^sub>s')[0:=Skip], Normal ns2)"
      using a14 par_tran_comp_rtran a15 mult_step_in_par[of \<Gamma>\<^sub>s "Ca#C\<^sub>s'" 0 "Normal ns1" "Skip" "Normal ns2"]
      by auto        
    moreover have "(\<forall>i<length ((Ca # C\<^sub>s')[0 := LanguageCon.com.Skip]). 
        ((Ca # C\<^sub>s')[0 := LanguageCon.com.Skip]) ! i = Skip)"      
    proof -
      {fix i
        assume a00:"i<length  ((Ca # C\<^sub>s')[0 := LanguageCon.com.Skip])"
        then have "(Ca # C\<^sub>s')[0 := LanguageCon.com.Skip] ! i = LanguageCon.com.Skip"
          using a15  apply (cases i) by auto
      }  thus ?thesis by auto      
    qed
    moreover have "((Ca # C\<^sub>s')[0 := LanguageCon.com.Skip]) \<noteq> []" by auto      
    ultimately show ?thesis by auto
  qed    
  ultimately show ?thesis by auto
qed

lemma all_throw_tran:
  assumes    
       a1:"0 < length (Ca # Cs)" and  a3:" \<sigma> = Normal ns\<^sub>c" and               
       a4:" s\<^sub>s = Normal ns\<^sub>s" and
       a5:"length (Ca # Cs) = length C\<^sub>c \<and> length (Ca # Cs) = length Rels\<^sub>c" and
       a6:"length Rels\<^sub>c = length Guas\<^sub>c \<and>
          length Rels\<^sub>c = length PostsQ \<and>
          length Rels\<^sub>c = length PostsA \<and> length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s" and                    
       a14:"(((\<sigma>, \<sigma>),(Normal ns1, Normal ns2)) \<in> (Guas\<^sub>c!0,(Guas\<^sub>s!0)\<^sup>*)\<^sub>\<alpha>) \<and>
            (ns\<^sub>c,  ns2)\<in>PostsA!0 \<and> PostsA!0\<subseteq>\<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Ca, Normal ns1) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw,Normal ns2)" and
       a15':"Guasc = drop 1 Guas\<^sub>c \<and> Guass = drop 1 Guas\<^sub>s \<and> Postsq = drop 1 PostsQ \<and> 
             Postsa = drop 1 PostsA \<and> Csc = drop 1 C\<^sub>c" and
       a15:"((\<sigma>, \<sigma>), s\<^sub>s, Normal ns1) \<in> 
                 (((\<Union>j<length Guasc. (Guasc !j)), (\<Union>j<length Guass. (Guass !j))\<^sup>*)\<^sub>\<alpha>) \<and> 
            (ns\<^sub>c, ns1)\<in> (\<Inter>i<length Postsq.  (Postsq ! i)) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Cs,s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s', Normal ns1) \<and> (\<forall>i<length C\<^sub>s'. C\<^sub>s' ! i = Skip) \<and> C\<^sub>s' \<noteq> []"
     shows "((\<sigma>, \<sigma>), s\<^sub>s, Normal ns2) \<in> 
                 (((\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)), (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s !j))\<^sup>*)\<^sub>\<alpha>) \<and> 
            (ns\<^sub>c, ns2)\<in>  (\<Union>i<length PostsA.  (PostsA ! i)) \<and> 
                 (\<exists>C\<^sub>s''. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca # Cs,s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s'', Normal ns2)  \<and> 
                    final_c (C\<^sub>s'', Normal ns2) \<and> (\<exists>i<length C\<^sub>s''. C\<^sub>s'' ! i = LanguageCon.com.Throw))"
proof-  
  have "((\<sigma>, \<sigma>), s\<^sub>s, Normal ns2) \<in> 
            (((\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)), (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s !j))\<^sup>*)\<^sub>\<alpha>)"
  using tran_Guar[OF a1 a4 a5 a6 _ a15' ] a15 a14 by auto
  moreover have "(ns\<^sub>c,  ns2)\<in> (\<Union>i<length PostsA.  (PostsA ! i))"
    using a14 a1 a6 a5 by auto  
  moreover have "\<exists>C\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca # Cs,s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s', Normal ns2) \<and> 
                      final_c (C\<^sub>s', Normal ns2) \<and> 
                      (\<exists>i<length C\<^sub>s'. C\<^sub>s' ! i = Throw)"
  proof-
    have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca#Cs, s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Ca#C\<^sub>s', Normal ns1)"
      using a15 by (simp add: par_tran_comp_rtran)    
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca # Cs,s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* ((Ca#C\<^sub>s')[0:=Throw], Normal ns2)"
      using a14 par_tran_comp_rtran a15 mult_step_in_par[of \<Gamma>\<^sub>s "Ca#C\<^sub>s'" 0 "Normal ns1" "Throw" "Normal ns2"]
      by auto        
    moreover have "final_c ((Ca # C\<^sub>s')[0 := Throw], Normal ns2) \<and> 
                    (\<exists>i<length ((Ca # C\<^sub>s')[0 := Throw]). ((Ca # C\<^sub>s')[0 := Throw]) ! i = Throw)"      
    proof -
      have "final_c ((Ca # C\<^sub>s')[0 := LanguageCon.com.Throw], Normal ns2)"
        unfolding final_c_def final_def 
        proof (auto)          
        {fix i
          assume a00:"i < Suc (length C\<^sub>s')" and
                 a01:"(LanguageCon.com.Throw # C\<^sub>s') ! i \<noteq> LanguageCon.com.Throw"
          then have "(LanguageCon.com.Throw # C\<^sub>s') ! i = LanguageCon.com.Skip"
            using a15  apply (cases i) by auto
        } 
        then show "\<And>i. i < Suc (length C\<^sub>s') \<Longrightarrow>
           (LanguageCon.com.Throw # C\<^sub>s') ! i \<noteq> LanguageCon.com.Throw \<Longrightarrow>
           (LanguageCon.com.Throw # C\<^sub>s') ! i = LanguageCon.com.Skip" by auto     
        qed then show ?thesis by fastforce
    qed    
     ultimately show ?thesis by fastforce
  qed
  ultimately show ?thesis by auto
qed

lemma all_throw_tran':
  assumes    
       a1:"0 < length (Ca # Cs)" and  a3:" \<sigma> = Normal ns\<^sub>c" and        
       a4:" s\<^sub>s = Normal ns\<^sub>s" and
       a5:"length (Ca # Cs) = length C\<^sub>c \<and> length (Ca # Cs) = length Rels\<^sub>c" and
       a6:"length Rels\<^sub>c = length Guas\<^sub>c \<and>
          length Rels\<^sub>c = length PostsQ \<and>
          length Rels\<^sub>c = length PostsA \<and> length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s" and                    
       a14:"(((\<sigma>, \<sigma>),(Normal ns1, Normal ns2)) \<in> (Guas\<^sub>c!0,(Guas\<^sub>s!0)\<^sup>*)\<^sub>\<alpha>) \<and>
            (ns\<^sub>c, ns2)\<in>PostsA!0 \<and> PostsA!0\<subseteq>\<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Ca, Normal ns1) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw,Normal ns2)" and
       a15':"Guasc = drop 1 Guas\<^sub>c \<and> Guass = drop 1 Guas\<^sub>s \<and> Postsq = drop 1 PostsQ \<and> 
             Postsa = drop 1 PostsA \<and> Csc = drop 1 C\<^sub>c" and
       a15:"((\<sigma>, \<sigma>), s\<^sub>s, Normal ns1) \<in> 
                 (((\<Union>j<length Guasc. (Guasc !j)), (\<Union>j<length Guass. (Guass !j))\<^sup>*)\<^sub>\<alpha>) \<and> 
             (ns\<^sub>c, ns1) \<in> (\<Union>i<length Postsa. Postsa ! i) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Cs,s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s', Normal ns1) \<and> final_c (C\<^sub>s', Normal ns1) \<and>
                    (\<exists>i<length C\<^sub>s'. C\<^sub>s' ! i = LanguageCon.com.Throw)"
     shows "((\<sigma>, \<sigma>), s\<^sub>s, Normal ns2) \<in> 
                 (((\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)), (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s !j))\<^sup>*)\<^sub>\<alpha>) \<and> 
            (ns\<^sub>c, ns2)\<in>  (\<Union>i<length PostsA.  (PostsA ! i)) \<and> 
                 (\<exists>C\<^sub>s''. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca # Cs,s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s'', Normal ns2)  \<and> 
                    final_c (C\<^sub>s'', Normal ns2) \<and> (\<exists>i<length C\<^sub>s''. C\<^sub>s'' ! i = LanguageCon.com.Throw))"
proof-  
  have "((\<sigma>, \<sigma>), s\<^sub>s, Normal ns2) \<in> 
            (((\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)), (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s !j))\<^sup>*)\<^sub>\<alpha>)"
  using tran_Guar[OF a1 a4 a5 a6 _  ] a15 a14 a15' by auto
  moreover have "(ns\<^sub>c, ns2)\<in> (\<Union>i<length PostsA.  (PostsA ! i))"
    using a14 a1 a6 a5 by auto  
  moreover have "\<exists>C\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca # Cs,s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s', Normal ns2) \<and> 
                      final_c (C\<^sub>s', Normal ns2) \<and> 
                      (\<exists>i<length C\<^sub>s'. C\<^sub>s' ! i = Throw)"
  proof-
    have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca#Cs, s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Ca#C\<^sub>s', Normal ns1)"
      using a15 by (simp add: par_tran_comp_rtran)    
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca # Cs,s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* ((Ca#C\<^sub>s')[0:=Throw], Normal ns2)"
      using a14 par_tran_comp_rtran a15 mult_step_in_par[of \<Gamma>\<^sub>s "Ca#C\<^sub>s'" 0 "Normal ns1" "Throw" "Normal ns2"]
      by auto        
    moreover have "final_c ((Ca # C\<^sub>s')[0 := Throw], Normal ns2) \<and> 
                    (\<exists>i<length ((Ca # C\<^sub>s')[0 := Throw]). ((Ca # C\<^sub>s')[0 := Throw]) ! i = Throw)"      
    proof -
      have "final_c ((Ca # C\<^sub>s')[0 := LanguageCon.com.Throw], Normal ns2)"  
        unfolding final_c_def
        proof (auto)          
        {fix i
          assume a00:"i < Suc (length C\<^sub>s')"                
          then have "final ((LanguageCon.com.Throw # C\<^sub>s') ! i, Normal ns2)"
            using a15 unfolding final_c_def final_def apply (cases i) by auto
        } 
        then show "\<And>i. i < Suc (length C\<^sub>s') \<Longrightarrow>
         SmallStepCon.final ((LanguageCon.com.Throw # C\<^sub>s') ! i, Normal ns2)" by auto     
        qed then show ?thesis by fastforce
    qed    
     ultimately show ?thesis by fastforce
  qed
  ultimately show ?thesis by auto
qed
  
lemma all_throw_tran'':
  assumes    
       a1:"0 < length (Ca # Cs)" and  a3:" \<sigma> = Normal ns\<^sub>c" and               
       a4:" s\<^sub>s = Normal ns\<^sub>s" and
       a5:"length (Ca # Cs) = length C\<^sub>c \<and> length (Ca # Cs) = length Rels\<^sub>c" and
       a6:"length Rels\<^sub>c = length Guas\<^sub>c \<and>
          length Rels\<^sub>c = length PostsQ \<and>
          length Rels\<^sub>c = length PostsA \<and> length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s" and                    
       a10:"\<forall>i<length PostsA. Sta\<^sub>s (PostsA ! i) (Rels\<^sub>c ! i, (Rels\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha>" and
       a12:"\<forall>i<length Rels\<^sub>c. R\<^sub>c \<union> (\<Union>a\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. Guas\<^sub>c ! a) \<subseteq> Rels\<^sub>c ! i" and
       a13:"\<forall>i<length Rels\<^sub>s. R\<^sub>s \<union> (\<Union>a\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. Guas\<^sub>s ! a) \<subseteq> Rels\<^sub>s ! i" and
       a14:"(((\<sigma>, \<sigma>),(Normal ns1, Normal ns2)) \<in> (Guas\<^sub>c!0,(Guas\<^sub>s!0)\<^sup>*)\<^sub>\<alpha>) \<and>
            (ns\<^sub>c, ns2)\<in>PostsQ!0 \<and> PostsQ!0\<subseteq>\<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Ca, Normal ns1) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip,Normal ns2)" and
       a15':"Guasc = drop 1 Guas\<^sub>c \<and> Guass = drop 1 Guas\<^sub>s \<and> Postsq = drop 1 PostsQ \<and> 
             Postsa = drop 1 PostsA \<and> Csc = drop 1 C\<^sub>c" and
       a15:"((\<sigma>, \<sigma>), s\<^sub>s, Normal ns1) \<in> 
                 (((\<Union>j<length Guasc. (Guasc !j)), (\<Union>j<length Guass. (Guass !j))\<^sup>*)\<^sub>\<alpha>) \<and> 
             (ns\<^sub>c, ns1) \<in> (\<Union>i<length Postsa. Postsa ! i) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Cs,s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s', Normal ns1) \<and> final_c (C\<^sub>s', Normal ns1) \<and>
                    (\<exists>i<length C\<^sub>s'. C\<^sub>s' ! i = LanguageCon.com.Throw)"
     shows "((\<sigma>, \<sigma>), s\<^sub>s, Normal ns2) \<in> 
                 (((\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)), (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s !j))\<^sup>*)\<^sub>\<alpha>) \<and> 
            (ns\<^sub>c, ns2)\<in>  (\<Union>i<length PostsA.  (PostsA ! i)) \<and> 
                 (\<exists>C\<^sub>s''. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca # Cs,s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s'', Normal ns2)  \<and> 
                    final_c (C\<^sub>s'', Normal ns2) \<and> (\<exists>i<length C\<^sub>s''. C\<^sub>s'' ! i = LanguageCon.com.Throw))"
proof-    
  have "((\<sigma>, \<sigma>), s\<^sub>s, Normal ns2) \<in> 
            (((\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)), (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s !j))\<^sup>*)\<^sub>\<alpha>)"
  using tran_Guar[OF a1 a4 a5 a6 _  ] a15 a14 a15' by auto
  moreover have "(ns\<^sub>c,  ns2)\<in> (\<Union>i<length PostsA.  (PostsA ! i))"    
  proof-    
     have len:"0<length PostsQ"  using a15' a1 a6 a5 by auto    
    have guars:"\<forall>i<length Guas\<^sub>c. i\<noteq>0 \<longrightarrow> ((\<sigma>, \<sigma>), Normal ns1, Normal ns2) \<in> (Rels\<^sub>c ! i, (Rels\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha> \<and> (\<sigma>, Normal ns2)\<in> \<alpha>\<^sub>x"
      using guar_i_rely_j[OF len a6 a12 a13 ] a14 a3 unfolding alpha_xstate_def by auto
            
    have "(ns\<^sub>c,  ns2) \<in> (\<Union>i<length Postsa. Postsa ! i)"          
    proof-
      obtain i where i_post:"i<length Postsa \<and> (ns\<^sub>c,  ns1) \<in> Postsa ! i"    
        using a15 by auto
      then have suc:"Suc i<length PostsA \<and> Suc i\<noteq>0" using a15' by auto
      then have "((\<sigma>, \<sigma>), Normal ns1, Normal ns2) \<in> (Rels\<^sub>c ! Suc i, (Rels\<^sub>s ! Suc i)\<^sup>*)\<^sub>\<alpha>"
        using guars a6 by auto
      also have "(ns\<^sub>c,  ns1)\<in> (PostsA ! Suc i)" 
        using a15 a15' suc i_post by force
      ultimately have "(ns\<^sub>c,  ns2) \<in> PostsA ! (Suc i)"
        using a10 suc guars a3 unfolding Sta\<^sub>s_def by fast    
      then have "i<length Postsa \<and>(ns\<^sub>c,  ns2) \<in> Postsa ! i"  using i_post suc a15' by auto           
      thus ?thesis by auto
    qed        
    thus ?thesis using a15' by auto
  qed  
  moreover have "\<exists>C\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca # Cs,s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s', Normal ns2) \<and> 
                      final_c (C\<^sub>s', Normal ns2) \<and> 
                      (\<exists>i<length C\<^sub>s'. C\<^sub>s' ! i = Throw)"
  proof-
    have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca#Cs, s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Ca#C\<^sub>s', Normal ns1)"
      using a15 by (simp add: par_tran_comp_rtran)    
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca # Cs,s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* ((Ca#C\<^sub>s')[0:=Skip], Normal ns2)"
      using a14 par_tran_comp_rtran a15 mult_step_in_par[of \<Gamma>\<^sub>s "Ca#C\<^sub>s'" 0 "Normal ns1" "Skip" "Normal ns2"]
      by auto        
    moreover have "final_c ((Ca # C\<^sub>s')[0 := Skip], Normal ns2) \<and> 
                    (\<exists>i<length ((Ca # C\<^sub>s')[0 := Skip]). ((Ca # C\<^sub>s')[0 := Skip]) ! i = Throw)"      
    proof -
      have "final_c ((Ca # C\<^sub>s')[0 := Skip], Normal ns2)"  
        unfolding final_c_def
        proof (auto)          
        {fix i
          assume a00:"i < Suc (length C\<^sub>s')"                
          then have "final ((LanguageCon.com.Skip # C\<^sub>s') ! i, Normal ns2)"
            using a15 unfolding final_c_def final_def apply (cases i) by auto
        } 
        then show "\<And>i. i < Suc (length C\<^sub>s') \<Longrightarrow>
         SmallStepCon.final ((LanguageCon.com.Skip # C\<^sub>s') ! i, Normal ns2)" by auto     
      qed
      moreover have "(\<exists>i<length ((Ca # C\<^sub>s')[0 := Skip]). ((Ca # C\<^sub>s')[0 := Skip]) ! i = Throw)"
      using a15 by auto        
      ultimately show ?thesis by fastforce qed      
     ultimately show ?thesis by fastforce
  qed
  ultimately show ?thesis  by  auto
qed
    
  
lemma "(n,n1)  \<in> a\<^sup>* \<Longrightarrow>
       (n1,n2) \<in> b\<^sup>* \<Longrightarrow>
       (n,n2)\<in>(a \<union> b)\<^sup>*"
  by (meson in_rtrancl_UnI rtrancl_trans)
  
lemma guars_i_rels_0:
  assumes a0:"Cs=Ca1#Cs1" and       
          a1:"0 < length (Ca # Cs)" and 
          a2:"length (Ca # Cs) = length C\<^sub>c \<and> length (Ca # Cs) = length Rels\<^sub>c" and
          a3:"length Rels\<^sub>c = length Guas\<^sub>c \<and>
              length Rels\<^sub>c = length PostsQ \<and>
              length Rels\<^sub>c = length PostsA \<and>
              length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s" and
          a4:"\<forall>i<length Rels\<^sub>c.
       R\<^sub>c \<union> (\<Union>a\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. Guas\<^sub>c ! a) \<subseteq> Rels\<^sub>c ! i" and
          a5:"\<forall>i<length Rels\<^sub>s.
       R\<^sub>s \<union> (\<Union>a\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. Guas\<^sub>s ! a) \<subseteq> Rels\<^sub>s ! i" and
          a6:"((\<sigma>, \<sigma>), s\<^sub>s, ns1) \<in> 
                 (((\<Union>j<length (drop 1 Guas\<^sub>c). ((drop 1 Guas\<^sub>c) !j)), (\<Union>j<length (drop 1 Guas\<^sub>s). ((drop 1 Guas\<^sub>s) !j))\<^sup>*)\<^sub>\<alpha>)"
  shows "((\<sigma>, \<sigma>), s\<^sub>s,  ns1) \<in> (Rels\<^sub>c!0, (Rels\<^sub>s!0)\<^sup>*)\<^sub>\<alpha>"  
proof-
    let ?Guasc = "(drop 1 Guas\<^sub>c)"
    let ?Guass = "(drop 1 Guas\<^sub>s)"
    have "length Guas\<^sub>c > Suc 0" using a0 a1 a2 a3 by auto
    then have guasc_sub:"(\<Union>j<length ?Guasc. (?Guasc !j)) \<subseteq> (\<Union>x\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> 0}. Guas\<^sub>c ! x)"
      using Suc_less_eq2 by fastforce
    have "length Rels\<^sub>c > 0" using a1 a2 by auto
    then have "R\<^sub>c \<union> (\<Union>x\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> 0}. Guas\<^sub>c ! x) \<subseteq> Rels\<^sub>c ! 0" 
      using  a4 by auto
    then have a00:"(\<Union>j<length ?Guasc. (?Guasc !j)) \<subseteq> Rels\<^sub>c!0"
      using guasc_sub by blast
    have "length Guas\<^sub>s > Suc 0" using a0 a1 a2 a3 by auto
    then have guass_sub:"(\<Union>j<length ?Guass. (?Guass !j)) \<subseteq> (\<Union>x\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> 0}. Guas\<^sub>s ! x)"
      using Suc_less_eq2 by fastforce
    have "length Rels\<^sub>s > 0" using a0 a1 a2 a3 by auto
    then have "R\<^sub>s \<union> (\<Union>x\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> 0}. Guas\<^sub>s ! x) \<subseteq> Rels\<^sub>s ! 0" 
      using  a5 by auto
    then have a1:"(\<Union>j<length ?Guass. (?Guass !j)) \<subseteq> Rels\<^sub>s!0"
      using guass_sub by blast 
    show ?thesis using a6 G_comp1[OF a00 a1] by auto
  qed        
  
lemma par_all_skip_rtran_gen1:
    "\<forall>i<length PostsQ. (\<Gamma>\<^sub>c,(C\<^sub>c ! i, toSeqState i \<sigma>),Rels\<^sub>c ! i,Guas\<^sub>c ! i) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>PostsQ ! i\<^sub>;\<^sub>PostsA ! i\<^sub>) 
                  (\<Gamma>\<^sub>s,(C\<^sub>s ! i, toSeqState i s\<^sub>s),Rels\<^sub>s ! i,Guas\<^sub>s ! i) \<Longrightarrow> 
      length C\<^sub>s > 0 \<Longrightarrow>
     (\<forall>i<length C\<^sub>c. C\<^sub>c ! i = LanguageCon.com.Skip) \<Longrightarrow>
      length C\<^sub>s = length C\<^sub>c \<and> length C\<^sub>s = length Rels\<^sub>c \<Longrightarrow> 
      length Rels\<^sub>c = length Guas\<^sub>c \<and> length Rels\<^sub>c = length PostsQ \<and> 
      length Rels\<^sub>c = length PostsA \<and> length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s \<Longrightarrow> 
      length PostsQ = length (snd \<sigma>) \<Longrightarrow>  length (snd \<sigma>) = length (snd s\<^sub>s) \<Longrightarrow>
      (\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)) \<subseteq> G\<^sub>c \<Longrightarrow>
      (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s !j)) \<subseteq> G\<^sub>s \<Longrightarrow>      
       \<forall>i<length PostsA. Sta\<^sub>s (PostsA!i) (Rels\<^sub>c!i, (Rels\<^sub>s!i)\<^sup>*)\<^sub>\<alpha> \<Longrightarrow> 
       \<forall>i<length PostsQ. Sta\<^sub>s (PostsQ!i) (Rels\<^sub>c!i, (Rels\<^sub>s!i)\<^sup>*)\<^sub>\<alpha> \<Longrightarrow>
       \<forall>i<length Rels\<^sub>c.
          R\<^sub>c \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. (Guas\<^sub>c ! j))
            \<subseteq> (Rels\<^sub>c ! i) \<Longrightarrow>
       \<forall>i<length Rels\<^sub>s.   
          R\<^sub>s \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. (Guas\<^sub>s ! j))
            \<subseteq> (Rels\<^sub>s!i) \<Longrightarrow>
     \<exists>C\<^sub>s' ns1. ((\<sigma>, \<sigma>), s\<^sub>s,  ns1) \<in> (((\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)), (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s !j))\<^sup>*)\<^sub>\<alpha>) \<and> 
               (ns\<^sub>c,  ns1)\<in> (\<Inter>i<length PostsQ.  (PostsQ ! i)) \<and> 
               \<Gamma>\<^sub>s\<turnstile>\<^sub>p (C\<^sub>s,s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s',  ns1) \<and> (\<forall>i<length C\<^sub>s'. C\<^sub>s' ! i = Skip) \<and> C\<^sub>s' \<noteq> []"
proof (induction C\<^sub>s arbitrary: C\<^sub>c Rels\<^sub>c Guas\<^sub>c Rels\<^sub>s Guas\<^sub>s PostsQ PostsA s\<^sub>s)
  case (Nil) thus ?case by auto
next
  case (Cons Ca Cs)   
  {assume a0:"Cs=Nil"  
    then have sim:"(\<Gamma>\<^sub>c,(Skip, \<sigma>),Rels\<^sub>c ! 0,Guas\<^sub>c ! 0) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>PostsQ ! 0\<^sub>;\<^sub>PostsA ! 0\<^sub>) 
                  (\<Gamma>\<^sub>s,(Ca, s\<^sub>s),Rels\<^sub>s ! 0,Guas\<^sub>s ! 0)" using Cons(4,3,7,2,8) by fastforce        
    obtain ns1 where sim_res:"(((\<sigma>, \<sigma>),(s\<^sub>s, Normal ns1)) \<in> (Guas\<^sub>c!0,(Guas\<^sub>s!0)\<^sup>*)\<^sub>\<alpha>) \<and>
              (ns\<^sub>c,  ns1)\<in>PostsQ!0 \<and> PostsQ!0\<subseteq>\<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Ca, s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip,Normal ns1)"
      using  Cons(5) sim_elim_cases_c(1)[OF sim] by auto
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca # Cs, s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* ((Ca # Cs)[0:=Skip], Normal ns1) \<and> 
               (\<forall>i<length ((Ca # Cs)[0:=Skip]). ((Ca # Cs)[0:=Skip])! i = LanguageCon.com.Skip) \<and> 
               (Ca # Cs)[0:=Skip] \<noteq> []" using ParComp[OF Cons(3), of \<Gamma>\<^sub>s  ]
      by (metis (no_types, lifting) a0 length_Cons length_list_update linorder_neqE_nat list.size(3) 
                                   mult_step_in_par not_less_eq not_less_zero nth_Cons_0 nth_list_update) 
    moreover have "(((\<sigma>, \<sigma>),(s\<^sub>s, Normal ns1)) \<in> 
       (((\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)), (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s !j))\<^sup>*)\<^sub>\<alpha>))" 
      using sim_res Cons(9,10,3,7,8)
      by (metis G_comp1 SUP_upper lessThan_iff)        
    moreover have "(ns\<^sub>c,  ns1)\<in> (\<Inter>i<length PostsQ.  (PostsQ ! i))"  
    proof-
      have "length PostsQ = 1" using a0 Cons(7,8) by auto      
      then show ?thesis using sim_res by auto
    qed         
   ultimately have ?case using Cons(13) a0 by fastforce 
  }
  moreover {     
    fix Ca1 Cs1
    assume a0:"Cs=Ca1#Cs1"
    define Guasc where "Guasc = drop 1 Guas\<^sub>c"
    define Guass where "Guass = drop 1 Guas\<^sub>s"
    define Relsc where "Relsc = drop 1 Rels\<^sub>c"
    define Relss where "Relss = drop 1 Rels\<^sub>s"
    define Postsq where "Postsq = drop 1 PostsQ" 
    define Postsa where "Postsa = drop 1 PostsA"
    define Csc where "Csc = drop 1 C\<^sub>c"    
    have a00:"length PostsQ = length C\<^sub>c \<and>
    length PostsQ = length Rels\<^sub>c \<and>
    length PostsQ = length Rels\<^sub>s \<and>
    length PostsQ = length Guas\<^sub>c \<and>
    length PostsQ = length Guas\<^sub>s \<and>
    length PostsQ = length (Ca # Cs) \<and> length PostsQ = length PostsA" 
      using Cons(3,7,8) a0 by auto    
    then have len_g0: "length Rels\<^sub>c > 0 \<and> length Guas\<^sub>c > 0 \<and> length Rels\<^sub>s > 0 \<and> length Guas\<^sub>s > 0"
      using Cons(3) by auto
    have lens:"length Cs = length Guasc \<and> length Cs = length Guass \<and>  length Cs = length Relsc \<and>
               length Cs = length Relss \<and> length Cs = length Postsq \<and> length Cs = length Postsa \<and>
               length Cs = length Csc"               
      using Cons(3,7,8) a0 unfolding Guasc_def Guass_def Relsc_def Relss_def Postsq_def Postsa_def Csc_def 
      by (metis One_nat_def Suc_pred length_Cons length_drop old.nat.inject)    
    have len_ga:"(\<forall>i<length Guasc. Guasc!i = Guas\<^sub>c ! (i+1)) \<and> 
                    (\<forall>i<length Guass. Guass!i = Guas\<^sub>s ! (i+1)) \<and> 
                    (\<forall>i<length Relsc. Relsc!i = Rels\<^sub>c ! (i+1)) \<and>
                    (\<forall>i<length Relss. Relss!i = Rels\<^sub>s ! (i+1)) \<and> 
                    (\<forall>i<length Postsq. Postsq!i = PostsQ ! (i+1)) \<and>
                    (\<forall>i<length Postsa. Postsa!i = PostsA ! (i+1)) \<and>
                    (\<forall>i<length Csc. Csc!i = C\<^sub>c ! (i+1))"
      unfolding Guasc_def Guass_def Relsc_def Relss_def Postsq_def Postsa_def Csc_def by auto
    have "\<exists>C\<^sub>s' ns1. ((\<sigma>, \<sigma>), s\<^sub>s, Normal ns1) \<in> 
                 (((\<Union>j<length Guasc. (Guasc !j)), (\<Union>j<length Guass. (Guass !j))\<^sup>*)\<^sub>\<alpha>) \<and> 
               (ns\<^sub>c,  ns1)\<in> (\<Inter>i<length Postsq.  (Postsq ! i)) \<and> 
               \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Cs,s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s', Normal ns1) \<and> (\<forall>i<length C\<^sub>s'. C\<^sub>s' ! i = Skip) \<and> C\<^sub>s' \<noteq> []"        
    proof-   
      let ?p ="\<lambda> a b c d e f g h. (\<Gamma>\<^sub>c,(b, \<sigma>),c,e)
       \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>a\<^sub>;\<^sub>h\<^sub>)
       (\<Gamma>\<^sub>s,(g, s\<^sub>s),d,f)"
      have s0:"\<forall>i<length Postsq. (\<Gamma>\<^sub>c,(Csc ! i, \<sigma>),Relsc ! i,Guasc ! i) 
             \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>Postsq ! i\<^sub>;\<^sub>Postsa ! i\<^sub>) (\<Gamma>\<^sub>s,(Cs ! i, s\<^sub>s),Relss ! i,Guass ! i)"  
        using ccc[OF a00,of ?p] Cons(2)
        unfolding Guasc_def Guass_def Relsc_def Relss_def Postsq_def Postsa_def Csc_def
        by auto            
      have s1:"0 < length Cs" using a0 by auto
      have s2:"\<forall>i<length Csc. Csc ! i = LanguageCon.com.Skip" 
        using Cons(4) unfolding Csc_def by auto
      have s3:"length Cs = length Csc \<and> length Cs = length Relsc"    
        using lens by auto
      have s4:"length Relsc = length Guasc \<and>
            length Relsc = length Postsq \<and>
            length Relsc = length Postsa \<and>
            length Relsc = length Guass \<and> length Relsc = length Relss"    
        using lens by fastforce
      have s5:"(\<Union>a<length Guasc. Guasc ! a) \<subseteq> G\<^sub>c" 
        using Cons(9)  unfolding Guasc_def by fastforce
      
      have s7:"(\<Union>a<length Guass. Guass ! a) \<subseteq> G\<^sub>s"
        using Cons(10) unfolding Guass_def by fastforce
      have s8:"\<forall>i<length Postsa. Sta\<^sub>s (Postsa ! i) (Relsc ! i, (Relss ! i)\<^sup>*)\<^sub>\<alpha> " 
        using Cons(11) len_ga lens unfolding Postsa_def by force
      have s9:"\<forall>i<length Postsq. Sta\<^sub>s (Postsq ! i) (Relsc ! i, (Relss ! i)\<^sup>*)\<^sub>\<alpha>"
        using Cons(12) len_ga lens unfolding Postsq_def by force
      have s10:"\<forall>i<length Relsc.
         R\<^sub>c \<union> (\<Union>a\<in>{j. j < length Guasc \<and> j \<noteq> i}. Guasc ! a) \<subseteq> Relsc ! i"
        using G_in_R_drop[OF Cons(13)] len_g0 a00 unfolding Guasc_def Relsc_def
        by auto      
      have s11:"\<forall>i<length Relss.
             R\<^sub>s \<union> (\<Union>a\<in>{j. j < length Guass \<and> j \<noteq> i}. Guass ! a) \<subseteq> Relss ! i"
      using G_in_R_drop[OF Cons(14)] len_g0 a00 unfolding Guass_def Relss_def
        by auto        
    show ?thesis 
      using Cons(1)[OF s0 s1 s2 Cons(5)  Cons(6) s3 s4 s5 s7 s8 s9 s10 s11] 
      by auto
  qed 
  then obtain C\<^sub>s' ns1 
    where hyp_step:"((\<sigma>, \<sigma>), s\<^sub>s, Normal ns1) \<in> 
                 (((\<Union>j<length Guasc. (Guasc !j)), (\<Union>j<length Guass. (Guass !j))\<^sup>*)\<^sub>\<alpha>) \<and> 
            (ns\<^sub>c, ns1)\<in> (\<Inter>i<length Postsq.  (Postsq ! i)) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Cs,s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s', Normal ns1) \<and> (\<forall>i<length C\<^sub>s'. C\<^sub>s' ! i = Skip) \<and> C\<^sub>s' \<noteq> [] "
    by auto   
  moreover have "((\<sigma>, \<sigma>), s\<^sub>s, Normal ns1) \<in> 
                 (Rels\<^sub>c!0, (Rels\<^sub>s!0)\<^sup>*)\<^sub>\<alpha> \<and> (\<sigma>, Normal ns1) \<in> \<alpha>\<^sub>x"
    using guars_i_rels_0[OF a0 Cons(3,7,8,13,14)] Cons(5) hyp_step 
    unfolding Guass_def Guasc_def alpha_xstate_def by auto
  then have sim:"(\<Gamma>\<^sub>c,(Skip, \<sigma>),Rels\<^sub>c ! 0,Guas\<^sub>c ! 0) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>PostsQ ! 0\<^sub>;\<^sub>PostsA ! 0\<^sub>) 
             (\<Gamma>\<^sub>s,((Ca # Cs) ! 0,  Normal ns1),Rels\<^sub>s ! 0,Guas\<^sub>s ! 0)"  
    using Cons(2) Cons(4,7)  dest_sim_env_step a00 by fastforce 
  obtain ns2 where sim_res:
      "(((\<sigma>, \<sigma>),(Normal ns1, Normal ns2)) \<in> (Guas\<^sub>c!0,(Guas\<^sub>s!0)\<^sup>*)\<^sub>\<alpha>) \<and>
       (ns\<^sub>c, ns2)\<in>PostsQ!0 \<and> PostsQ!0\<subseteq>\<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Ca, Normal ns1) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip,Normal ns2)"
    using  Cons(5) sim_elim_cases_c(1)[OF sim] by auto    
  have "((\<sigma>, \<sigma>), s\<^sub>s, Normal ns2) \<in> 
                 (((\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)), (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s !j))\<^sup>*)\<^sub>\<alpha>) \<and> 
            (ns\<^sub>c,  ns2)\<in> (\<Inter>i<length PostsQ.  (PostsQ ! i)) \<and> 
                 (\<exists>C\<^sub>s''. \<Gamma>\<^sub>s\<turnstile>\<^sub>p ((Ca # Cs),s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s'', Normal ns2) \<and> (\<forall>i<length C\<^sub>s''. C\<^sub>s'' ! i = Skip) \<and> C\<^sub>s'' \<noteq> [])"
    using all_skip_tran[OF Cons(2-8) Cons(12-14) sim_res _  hyp_step a0] 
    unfolding Guasc_def Guass_def Postsq_def Postsa_def by auto
    then have ?case by auto
  }      
  ultimately show ?case using list.exhaust by blast      
qed
  
lemma cs_skip_tran:
 assumes a0:"\<forall>i<length PostsQ. (\<Gamma>\<^sub>c,(C\<^sub>c ! i, \<sigma>),Rels\<^sub>c ! i,Guas\<^sub>c ! i) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>PostsQ ! i\<^sub>;\<^sub>PostsA ! i\<^sub>)
            (\<Gamma>\<^sub>s,((Ca # Cs) ! i, s\<^sub>s),Rels\<^sub>s ! i,Guas\<^sub>s ! i)" and
         a1:"0 < length (Ca # Cs)" and a1':"Cs=Ca1#Cs1" and         
         a2:"C\<^sub>c = cca#ccs" and a2':"cca = Throw \<and> (\<forall>i<length ccs. ccs!i = Skip)" and
         a3:"\<sigma> = Normal ns\<^sub>c" and
         a4:"s\<^sub>s = Normal ns\<^sub>s" and
         a5:"length (Ca # Cs) = length C\<^sub>c \<and> length (Ca # Cs) = length Rels\<^sub>c" and
         a6:"length Rels\<^sub>c = length Guas\<^sub>c \<and>
             length Rels\<^sub>c = length PostsQ \<and>
             length Rels\<^sub>c = length PostsA \<and> length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s" and
         a7:"(\<Union>a<length Guas\<^sub>c. Guas\<^sub>c ! a) \<subseteq> G\<^sub>c" and
         a9:"(\<Union>a<length Guas\<^sub>s. Guas\<^sub>s ! a) \<subseteq> G\<^sub>s " and
         a10:"\<forall>i<length PostsA. Sta\<^sub>s (PostsA ! i) (Rels\<^sub>c ! i, (Rels\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha>" and
         a11:"\<forall>i<length PostsQ. Sta\<^sub>s (PostsQ ! i) (Rels\<^sub>c ! i, (Rels\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha>" and
         a12:"\<forall>i<length Rels\<^sub>c. R\<^sub>c \<union> (\<Union>a\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. Guas\<^sub>c ! a) \<subseteq> Rels\<^sub>c ! i" and
         a13:"\<forall>i<length Rels\<^sub>s. R\<^sub>s \<union> (\<Union>a\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. Guas\<^sub>s ! a) \<subseteq> Rels\<^sub>s ! i"          
       shows "\<exists>ns1'. 
            (((\<sigma>, \<sigma>), s\<^sub>s, Normal ns1') \<in> (\<Union>a<length Guas\<^sub>c. Guas\<^sub>c ! a, (\<Union>a<length Guas\<^sub>s. Guas\<^sub>s ! a)\<^sup>*)\<^sub>\<alpha>) \<and>
           (ns\<^sub>c,  ns1') \<in> (\<Union>a<length PostsA. PostsA ! a) \<and>
           (\<exists>c''. (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca # Cs, s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c'', Normal ns1')) \<and>
                  (final_c (c'', Normal ns1')) \<and> (\<exists>i<length c''. c'' ! i = LanguageCon.com.Throw))"
proof-
  define Guasc where "Guasc = drop 1 Guas\<^sub>c"
  define Guass where "Guass = drop 1 Guas\<^sub>s"
  define Relsc where "Relsc = drop 1 Rels\<^sub>c"
  define Relss where "Relss = drop 1 Rels\<^sub>s"
  define Postsq where "Postsq = drop 1 PostsQ" 
  define Postsa where "Postsa = drop 1 PostsA"
  define Csc where "Csc = drop 1 C\<^sub>c"
  then have a00:"length PostsQ = length C\<^sub>c \<and>
                 length PostsQ = length Rels\<^sub>c \<and>
                 length PostsQ = length Rels\<^sub>s \<and>
                 length PostsQ = length Guas\<^sub>c \<and>
                 length PostsQ = length Guas\<^sub>s \<and>
                 length PostsQ = length (Ca # Cs) \<and> 
                 length PostsQ = length PostsA" 
    using a6 a5 by auto
  then have len_g0: "length Rels\<^sub>c > 0 \<and> length Guas\<^sub>c > 0 \<and> length Rels\<^sub>s > 0 \<and> length Guas\<^sub>s > 0"
      using a1 by auto
  have lens:"length Cs = length Guasc \<and> length Cs = length Guass \<and>  length Cs = length Relsc \<and>
             length Cs = length Relss \<and> length Cs = length Postsq \<and> length Cs = length Postsa \<and>
             length Cs = length Csc"               
    using a00 a1 a6  unfolding Guasc_def Guass_def Relsc_def Relss_def Postsq_def Postsa_def Csc_def 
    by (metis One_nat_def Suc_pred length_Cons length_drop old.nat.inject)
  have len_ga:"(\<forall>i<length Guasc. Guasc!i = Guas\<^sub>c ! (i+1)) \<and> 
                  (\<forall>i<length Guass. Guass!i = Guas\<^sub>s ! (i+1)) \<and> 
                  (\<forall>i<length Relsc. Relsc!i = Rels\<^sub>c ! (i+1)) \<and>
                  (\<forall>i<length Relss. Relss!i = Rels\<^sub>s ! (i+1)) \<and> 
                  (\<forall>i<length Postsq. Postsq!i = PostsQ ! (i+1)) \<and>
                  (\<forall>i<length Postsa. Postsa!i = PostsA ! (i+1)) \<and>
                  (\<forall>i<length Csc. Csc!i = C\<^sub>c ! (i+1))"
    unfolding Guasc_def Guass_def Relsc_def Relss_def Postsq_def Postsa_def Csc_def by auto      
  have hyp_step:"\<exists>C\<^sub>s' ns1. ((\<sigma>, \<sigma>), s\<^sub>s, Normal ns1) \<in> 
                 (((\<Union>j<length Guasc. (Guasc !j)), (\<Union>j<length Guass. (Guass !j))\<^sup>*)\<^sub>\<alpha>) \<and> 
               (ns\<^sub>c, ns1)\<in> (\<Inter>i<length Postsq.  (Postsq ! i)) \<and> 
               \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Cs,s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s', Normal ns1) \<and> (\<forall>i<length C\<^sub>s'. C\<^sub>s' ! i = Skip) \<and> C\<^sub>s' \<noteq> []"        
    proof-   
      let ?p ="\<lambda> a b c d e f g h. (\<Gamma>\<^sub>c,(b, \<sigma>),c,e)
       \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>a\<^sub>;\<^sub>h\<^sub>)
       (\<Gamma>\<^sub>s,(g, s\<^sub>s),d,f)"
      have s0:"\<forall>i<length Postsq. (\<Gamma>\<^sub>c,(Csc ! i, \<sigma>),Relsc ! i,Guasc ! i) 
             \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>Postsq ! i\<^sub>;\<^sub>Postsa ! i\<^sub>) (\<Gamma>\<^sub>s,(Cs ! i, s\<^sub>s),Relss ! i,Guass ! i)"  
        using ccc[OF a00,of ?p] a0
        unfolding Guasc_def Guass_def Relsc_def Relss_def Postsq_def Postsa_def Csc_def
        by auto            
      have s1:"0 < length Cs" using a1' by auto
      have s2:"\<forall>i<length Csc. Csc ! i = LanguageCon.com.Skip" 
        using a2' a2 unfolding Csc_def by auto
      have s3:"length Cs = length Csc \<and> length Cs = length Relsc"    
        using lens by auto
      have s4:"length Relsc = length Guasc \<and>
            length Relsc = length Postsq \<and>
            length Relsc = length Postsa \<and>
            length Relsc = length Guass \<and> length Relsc = length Relss"    
        using lens by auto
      have s5:"(\<Union>a<length Guasc. Guasc ! a) \<subseteq> G\<^sub>c" 
        using a7 unfolding Guasc_def by fastforce     
      have s7:"(\<Union>a<length Guass. Guass ! a) \<subseteq> G\<^sub>s"
        using a9 unfolding Guass_def by fastforce
      have s8:"\<forall>i<length Postsa. Sta\<^sub>s (Postsa ! i) (Relsc ! i, (Relss ! i)\<^sup>*)\<^sub>\<alpha> " 
        using a10 len_ga lens unfolding Postsa_def by auto
      have s9:"\<forall>i<length Postsq. Sta\<^sub>s (Postsq ! i) (Relsc ! i, (Relss ! i)\<^sup>*)\<^sub>\<alpha>"
        using a11 len_ga lens unfolding Postsq_def by auto
      have s10:"\<forall>i<length Relsc.
         R\<^sub>c \<union> (\<Union>a\<in>{j. j < length Guasc \<and> j \<noteq> i}. Guasc ! a) \<subseteq> Relsc ! i"
         using G_in_R_drop[OF a12] len_g0 a00 unfolding Guasc_def Relsc_def
        by auto          
      have s11:"\<forall>i<length Relss.
             R\<^sub>s \<union> (\<Union>a\<in>{j. j < length Guass \<and> j \<noteq> i}. Guass ! a) \<subseteq> Relss ! i"
       using G_in_R_drop[OF a13] len_g0 a00 unfolding Guass_def Relss_def
        by auto
    show ?thesis 
      using par_all_skip_rtran_gen1 [OF s0 s1 s2 a3  a4 s3 s4 s5  s7 s8 s9 s10 s11] 
      by auto
  qed
  then obtain C\<^sub>s' ns1 
    where hyp_step:"((\<sigma>, \<sigma>), s\<^sub>s, Normal ns1) \<in> 
                 (((\<Union>j<length Guasc. (Guasc !j)), (\<Union>j<length Guass. (Guass !j))\<^sup>*)\<^sub>\<alpha>) \<and> 
            (ns\<^sub>c,  ns1)\<in> (\<Inter>i<length Postsq.  (Postsq ! i)) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Cs,s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s', Normal ns1) \<and> (\<forall>i<length C\<^sub>s'. C\<^sub>s' ! i = Skip) \<and> C\<^sub>s' \<noteq> [] "
    by auto       
  moreover have "((\<sigma>, \<sigma>), s\<^sub>s, Normal ns1) \<in> 
                 (Rels\<^sub>c!0, (Rels\<^sub>s!0)\<^sup>*)\<^sub>\<alpha> \<and> (\<sigma>, Normal ns1)\<in>\<alpha>\<^sub>x" 
    using guars_i_rels_0[OF a1' a1 a5 a6 a12 a13] hyp_step using a3
    unfolding Guass_def Guasc_def alpha_xstate_def by auto    
  moreover then have sim:"(\<Gamma>\<^sub>c,(Throw, Normal ns\<^sub>c),Rels\<^sub>c ! 0,Guas\<^sub>c ! 0) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>PostsQ ! 0\<^sub>;\<^sub>PostsA ! 0\<^sub>) 
             (\<Gamma>\<^sub>s,((Ca # Cs) ! 0,  Normal ns1),Rels\<^sub>s ! 0,Guas\<^sub>s ! 0)"  
    using a0 a2 a2' a5  a3 dest_sim_env_step a00 by fastforce 
  obtain ns2 where sim_res:
      "(((\<sigma>, \<sigma>),(Normal ns1, Normal ns2)) \<in> (Guas\<^sub>c!0,(Guas\<^sub>s!0)\<^sup>*)\<^sub>\<alpha>) \<and>
       (ns\<^sub>c,  ns2)\<in>PostsA!0 \<and> PostsA!0\<subseteq>\<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Ca, Normal ns1) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw,Normal ns2)"
    using  a3 sim_elim_cases_c(2)[OF sim] by auto
   have "((\<sigma>, \<sigma>), s\<^sub>s, Normal ns2) \<in> 
                 (((\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)), (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s !j))\<^sup>*)\<^sub>\<alpha>) \<and> 
            (ns\<^sub>c,  ns2)\<in> (\<Union>i<length PostsA.  (PostsA ! i)) \<and> 
                 (\<exists>C\<^sub>s''. \<Gamma>\<^sub>s\<turnstile>\<^sub>p ((Ca # Cs),s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s'', Normal ns2) \<and> 
                    final_c (C\<^sub>s'', Normal ns2) \<and> (\<exists>i<length C\<^sub>s''. C\<^sub>s'' ! i = LanguageCon.com.Throw))"
    using all_throw_tran[OF a1 a3 a4 a5 a6 sim_res _] hyp_step
    unfolding Guasc_def Guass_def Postsq_def Postsa_def by auto
  thus ?thesis by auto
qed
    
lemma par_throw_rtran_gen1:
    "\<forall>i<length PostsQ. (\<Gamma>\<^sub>c,(C\<^sub>c ! i, \<sigma>),Rels\<^sub>c ! i,Guas\<^sub>c ! i) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>PostsQ ! i\<^sub>;\<^sub>PostsA ! i\<^sub>) 
                  (\<Gamma>\<^sub>s,(C\<^sub>s ! i, s\<^sub>s),Rels\<^sub>s ! i,Guas\<^sub>s ! i) \<Longrightarrow> 
      length C\<^sub>s > 0 \<Longrightarrow>
      final_c (C\<^sub>c, \<sigma>) \<and>  (\<exists>i<length C\<^sub>c. C\<^sub>c ! i = LanguageCon.com.Throw) \<Longrightarrow>
      \<sigma> = Normal ns\<^sub>c \<Longrightarrow>
      s\<^sub>s = Normal ns\<^sub>s \<Longrightarrow>
      length C\<^sub>s = length C\<^sub>c \<and> length C\<^sub>s = length Rels\<^sub>c \<Longrightarrow> 
      length Rels\<^sub>c = length Guas\<^sub>c \<and> length Rels\<^sub>c = length PostsQ \<and> 
      length Rels\<^sub>c = length PostsA \<and> length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s \<Longrightarrow>
      (\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)) \<subseteq> G\<^sub>c \<Longrightarrow>      
      (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s !j)) \<subseteq> G\<^sub>s \<Longrightarrow>      
       \<forall>i<length PostsA. Sta\<^sub>s (PostsA!i) (Rels\<^sub>c!i, (Rels\<^sub>s!i)\<^sup>*)\<^sub>\<alpha> \<Longrightarrow> 
       \<forall>i<length PostsQ. Sta\<^sub>s (PostsQ!i) (Rels\<^sub>c!i, (Rels\<^sub>s!i)\<^sup>*)\<^sub>\<alpha> \<Longrightarrow>
       \<forall>i<length Rels\<^sub>c.
          R\<^sub>c \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. (Guas\<^sub>c ! j))
            \<subseteq> (Rels\<^sub>c ! i) \<Longrightarrow>
       \<forall>i<length Rels\<^sub>s.   
          R\<^sub>s \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. (Guas\<^sub>s ! j))
            \<subseteq> (Rels\<^sub>s!i) \<Longrightarrow>
     \<exists>ns1'. ((\<sigma>, \<sigma>), s\<^sub>s, Normal ns1') \<in> (((\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)), (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s !j))\<^sup>*)\<^sub>\<alpha>) \<and>
                (ns\<^sub>c,  ns1') \<in> (\<Union>i<length PostsA.  (PostsA ! i)) \<and>                
                (\<exists>c''. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (C\<^sub>s, s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c'', Normal ns1') \<and>
                       final_c (c'', Normal ns1') \<and> (\<exists>i<length c''. c'' ! i = LanguageCon.com.Throw))"
proof (induction C\<^sub>s arbitrary: C\<^sub>c Rels\<^sub>c Guas\<^sub>c Rels\<^sub>s Guas\<^sub>s PostsQ PostsA s\<^sub>s)
  case (Nil) thus ?case by auto
next
  case (Cons Ca Cs)   
  {assume a0:"Cs=Nil"   
   then have "C\<^sub>c!0 = Throw" using Cons(4,7) unfolding final_c_def final_def
      using a0 less_Suc0 by auto   
    then have sim:"(\<Gamma>\<^sub>c,(Throw, Normal ns\<^sub>c),Rels\<^sub>c ! 0,Guas\<^sub>c ! 0) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>PostsQ ! 0\<^sub>;\<^sub>PostsA ! 0\<^sub>) 
                  (\<Gamma>\<^sub>s,(Ca, s\<^sub>s),Rels\<^sub>s ! 0,Guas\<^sub>s ! 0)" using Cons(4,5,3,7,2,8) a0  by fastforce
    obtain ns1 where sim_res:"(((\<sigma>, \<sigma>),(s\<^sub>s, Normal ns1)) \<in> (Guas\<^sub>c!0,(Guas\<^sub>s!0)\<^sup>*)\<^sub>\<alpha>) \<and>
              (ns\<^sub>c,  ns1)\<in>PostsA!0 \<and> PostsA!0\<subseteq>\<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Ca, s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw,Normal ns1)"
      using  Cons(5) sim_elim_cases_c(2)[OF sim] by auto
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca # Cs, s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* ((Ca # Cs)[0:=Throw], Normal ns1) \<and> 
               (\<forall>i<length ((Ca # Cs)[0:=Throw]). ((Ca # Cs)[0:=Throw])! i = LanguageCon.com.Throw) \<and> 
               (Ca # Cs)[0:=Throw] \<noteq> []" using ParComp[OF Cons(3), of \<Gamma>\<^sub>s  ]
      by (metis (no_types, lifting) a0 length_Cons length_list_update linorder_neqE_nat list.size(3) 
                                   mult_step_in_par not_less_eq not_less_zero nth_Cons_0 nth_list_update) 
    moreover have "(((\<sigma>, \<sigma>),(s\<^sub>s, Normal ns1)) \<in> 
       (((\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)), (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s !j))\<^sup>*)\<^sub>\<alpha>))" 
      using sim_res Cons(9,10,3,7,8)
      by (metis G_comp1 SUP_upper lessThan_iff)        
    moreover have "(ns\<^sub>c,  ns1)\<in> (\<Union>i<length PostsA.  (PostsA ! i))"  
    proof-
      have "length PostsA = 1" using a0 Cons(7,8) by auto      
      then show ?thesis using sim_res by auto
    qed         
   ultimately have ?case using Cons(13) a0 unfolding final_c_def final_def by fastforce 
  } note x = this
  {     
    fix Ca1 Cs1
    assume a0:"Cs=Ca1#Cs1"
    define Guasc where "Guasc = drop 1 Guas\<^sub>c"
    define Guass where "Guass = drop 1 Guas\<^sub>s"
    define Relsc where "Relsc = drop 1 Rels\<^sub>c"
    define Relss where "Relss = drop 1 Rels\<^sub>s"
    define Postsq where "Postsq = drop 1 PostsQ" 
    define Postsa where "Postsa = drop 1 PostsA"
    define Csc where "Csc = drop 1 C\<^sub>c"
    then have a00:"length PostsQ = length C\<^sub>c \<and>
    length PostsQ = length Rels\<^sub>c \<and>
    length PostsQ = length Rels\<^sub>s \<and>
    length PostsQ = length Guas\<^sub>c \<and>
    length PostsQ = length Guas\<^sub>s \<and>
    length PostsQ = length (Ca # Cs) \<and> length PostsQ = length PostsA" 
      using Cons(3,7,8) by auto
    then have len_g0: "length Rels\<^sub>c > 0 \<and> length Guas\<^sub>c > 0 \<and> length Rels\<^sub>s > 0 \<and> length Guas\<^sub>s > 0"
       by auto
    then have lens:"length Cs = length Guasc \<and> length Cs = length Guass \<and>  length Cs = length Relsc \<and>
               length Cs = length Relss \<and> length Cs = length Postsq \<and> length Cs = length Postsa \<and>
               length Cs = length Csc"               
      using Cons(3,7,8) a0 unfolding Guasc_def Guass_def Relsc_def Relss_def Postsq_def Postsa_def Csc_def 
      by (metis One_nat_def Suc_pred length_Cons length_drop old.nat.inject)
    have len_ga:"(\<forall>i<length Guasc. Guasc!i = Guas\<^sub>c ! (i+1)) \<and> 
                    (\<forall>i<length Guass. Guass!i = Guas\<^sub>s ! (i+1)) \<and> 
                    (\<forall>i<length Relsc. Relsc!i = Rels\<^sub>c ! (i+1)) \<and>
                    (\<forall>i<length Relss. Relss!i = Rels\<^sub>s ! (i+1)) \<and> 
                    (\<forall>i<length Postsq. Postsq!i = PostsQ ! (i+1)) \<and>
                    (\<forall>i<length Postsa. Postsa!i = PostsA ! (i+1)) \<and>
                    (\<forall>i<length Csc. Csc!i = C\<^sub>c ! (i+1))"
      unfolding Guasc_def Guass_def Relsc_def Relss_def Postsq_def Postsa_def Csc_def by auto
    obtain cca ccs where cc:"C\<^sub>c=cca#ccs" using a0 Cons(7)
      by (metis Cons.prems(3) Cons_nth_drop_Suc drop_0 gr_implies_not_zero neq0_conv) 
    {
      assume css_skip:"\<forall>i<length ccs. ccs!i = Skip" 
      then have cca:"cca = Throw \<and> (\<forall>i<length ccs. ccs!i = Skip)" 
        using css_skip Cons(4) cc less_Suc_eq_0_disj 
        unfolding final_c_def final_def  by fastforce
      have ?case using cs_skip_tran[OF Cons(2-3) a0 cc cca Cons(5-14)] by auto
    }
    moreover{
      assume  css_throw: "\<not>(\<forall>i<length ccs. ccs!i = Skip)"
      then have ccs_throw:"\<exists>i<length ccs. ccs!i = Throw" 
        using Cons(4) unfolding final_c_def cc final_def by fastforce
      have hyp_step:
           "\<exists>ns1. ((\<sigma>, \<sigma>), s\<^sub>s, Normal ns1) \<in> 
                  (((\<Union>j<length Guasc. (Guasc !j)), (\<Union>j<length Guass. (Guass !j))\<^sup>*)\<^sub>\<alpha>) \<and> 
                  (ns\<^sub>c,  ns1)\<in> (\<Union>i<length Postsa.  (Postsa ! i)) \<and> 
                  (\<exists>c''. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Cs,s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c'', Normal ns1) \<and>
                    final_c (c'', Normal ns1) \<and>
                    (\<exists>i<length c''. c'' ! i = LanguageCon.com.Throw))"
       proof-
         let ?p ="\<lambda> a b c d e f g h. (\<Gamma>\<^sub>c,(b, \<sigma>),c,e) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>a\<^sub>;\<^sub>h\<^sub>) (\<Gamma>\<^sub>s,(g, s\<^sub>s),d,f)"
         have s0:"\<forall>i<length Postsq. (\<Gamma>\<^sub>c,(Csc ! i, \<sigma>),Relsc ! i,Guasc ! i) 
             \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>Postsq ! i\<^sub>;\<^sub>Postsa ! i\<^sub>) (\<Gamma>\<^sub>s,(Cs ! i, s\<^sub>s),Relss ! i,Guass ! i)"  
          using ccc[OF a00,of ?p] Cons(2)
          unfolding Guasc_def Guass_def Relsc_def Relss_def Postsq_def Postsa_def Csc_def
          by auto        
        have s1:"0 < length Cs" using a0 by auto
        have s2:"final_c (Csc,\<sigma>) \<and> (\<exists>i<length Csc. Csc!i = Throw)" 
          using Cons(4) ccs_throw cc
          unfolding Csc_def final_c_def final_def by auto
        have s3:"length Cs = length Csc \<and> length Cs = length Relsc"    
          using lens by auto
        have s4:"length Relsc = length Guasc \<and>
              length Relsc = length Postsq \<and>
              length Relsc = length Postsa \<and>
              length Relsc = length Guass \<and> length Relsc = length Relss"    
          using lens by auto
        have s5:"(\<Union>a<length Guasc. Guasc ! a) \<subseteq> G\<^sub>c" 
          using Cons(9)  unfolding Guasc_def by fastforce        
        have s7:"(\<Union>a<length Guass. Guass ! a) \<subseteq> G\<^sub>s"
          using Cons(10) unfolding Guass_def by fastforce
        have s8:"\<forall>i<length Postsa. Sta\<^sub>s (Postsa ! i) (Relsc ! i, (Relss ! i)\<^sup>*)\<^sub>\<alpha> " 
          using Cons(11) len_ga lens unfolding Postsa_def by force
        have s9:"\<forall>i<length Postsq. Sta\<^sub>s (Postsq ! i) (Relsc ! i, (Relss ! i)\<^sup>*)\<^sub>\<alpha>"
          using Cons(12) len_ga lens unfolding Postsq_def by force
        have s10:"\<forall>i<length Relsc.
          R\<^sub>c \<union> (\<Union>a\<in>{j. j < length Guasc \<and> j \<noteq> i}. Guasc ! a) \<subseteq> Relsc ! i"
          using G_in_R_drop[OF Cons(13)] len_g0 a00 unfolding Guasc_def Relsc_def
          by auto
        have s11:"\<forall>i<length Relss.
             R\<^sub>s \<union> (\<Union>a\<in>{j. j < length Guass \<and> j \<noteq> i}. Guass ! a) \<subseteq> Relss ! i"
          using G_in_R_drop[OF Cons(14)] len_g0 a00 unfolding Guass_def Relss_def
          by auto
        show ?thesis using Cons(1)[OF s0 s1 s2 Cons(5)  Cons(6) s3 s4 s5 s7 s8 s9 s10 s11] 
          by auto
      qed
      then obtain c'' ns1 where hyp_step:"((\<sigma>, \<sigma>), s\<^sub>s, Normal ns1) \<in> 
                  (((\<Union>j<length Guasc. (Guasc !j)), (\<Union>j<length Guass. (Guass !j))\<^sup>*)\<^sub>\<alpha>) \<and> 
                  (ns\<^sub>c,  ns1)\<in> (\<Union>i<length Postsa.  (Postsa ! i)) \<and> 
                   \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Cs,s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c'', Normal ns1) \<and>
                    final_c (c'', Normal ns1) \<and>
                    (\<exists>i<length c''. c'' ! i = LanguageCon.com.Throw)" by auto
      moreover have "((\<sigma>, \<sigma>), s\<^sub>s, Normal ns1) \<in> 
                 (Rels\<^sub>c!0, (Rels\<^sub>s!0)\<^sup>*)\<^sub>\<alpha> \<and> (\<sigma>,Normal ns1)\<in>\<alpha>\<^sub>x"
      using guars_i_rels_0[OF a0 Cons(3,7,8,13,14)] hyp_step Cons(5)
      unfolding Guass_def Guasc_def unfolding alpha_xstate_def by auto
      then have sim:"(\<Gamma>\<^sub>c,(C\<^sub>c!0, \<sigma>),Rels\<^sub>c ! 0,Guas\<^sub>c ! 0) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>PostsQ ! 0\<^sub>;\<^sub>PostsA ! 0\<^sub>) 
             (\<Gamma>\<^sub>s,((Ca # Cs) ! 0,  Normal ns1),Rels\<^sub>s ! 0,Guas\<^sub>s ! 0)"  
        using Cons(2) Cons(4,7)  
          dest_sim_env_step[of \<Gamma>\<^sub>c "C\<^sub>c!0" \<sigma> "Rels\<^sub>c ! 0" "Guas\<^sub>c ! 0" _ _ _ \<Gamma>\<^sub>s "(Ca # Cs) ! 0" s\<^sub>s] 
         a00 by fastforce
      then have "C\<^sub>c!0 = Skip \<or> C\<^sub>c!0 = Throw"
        using Cons(4) unfolding final_c_def cc final_def by fastforce         
      moreover{
        assume "C\<^sub>c!0 = Skip" 
        then have sim:"(\<Gamma>\<^sub>c,(Skip, \<sigma>),Rels\<^sub>c ! 0,Guas\<^sub>c ! 0) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>PostsQ ! 0\<^sub>;\<^sub>PostsA ! 0\<^sub>) 
                        (\<Gamma>\<^sub>s,((Ca # Cs) ! 0,  Normal ns1),Rels\<^sub>s ! 0,Guas\<^sub>s ! 0)" 
          using sim by auto
        then obtain ns2 where sim_res:"(((\<sigma>, \<sigma>),(Normal ns1, Normal ns2)) \<in> (Guas\<^sub>c!0,(Guas\<^sub>s!0)\<^sup>*)\<^sub>\<alpha>) \<and>
                 (ns\<^sub>c,  ns2)\<in>PostsQ!0 \<and> PostsQ!0\<subseteq>\<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Ca, Normal ns1) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip,Normal ns2)"
          using  Cons(5)  sim_elim_cases_c(1)[OF sim] by auto
         have "((\<sigma>, \<sigma>), s\<^sub>s, Normal ns2)
           \<in> ((\<Union>a<length Guas\<^sub>c.
                  Guas\<^sub>c ! a, (\<Union>a<length Guas\<^sub>s. Guas\<^sub>s ! a)\<^sup>*)\<^sub>\<alpha>) \<and>
           (ns\<^sub>c,  ns2) \<in> (\<Union>a<length PostsA. PostsA ! a) \<and>
           (\<exists>c''. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca # Cs, s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c'', Normal ns2) \<and>
                  final_c (c'', Normal ns2) \<and>
                  (\<exists>i<length c''. c'' ! i = LanguageCon.com.Throw))" 
        using all_throw_tran''[OF Cons(3) Cons(5)  Cons(6) Cons(7-8) Cons(11,13,14)  sim_res]   hyp_step 
          unfolding Guasc_def Guass_def Postsq_def Postsa_def by fast           
        then have ?case by auto
      }
      moreover{
        assume "C\<^sub>c!0 = Throw"
        then have sim:"(\<Gamma>\<^sub>c,(Throw, Normal ns\<^sub>c),Rels\<^sub>c ! 0,Guas\<^sub>c ! 0) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>PostsQ ! 0\<^sub>;\<^sub>PostsA ! 0\<^sub>) 
                        (\<Gamma>\<^sub>s,((Ca # Cs) ! 0,  Normal ns1),Rels\<^sub>s ! 0,Guas\<^sub>s ! 0)" 
          using Cons(5) sim by auto
        obtain ns2 where sim_res:
         "(((\<sigma>, \<sigma>),(Normal ns1, Normal ns2)) \<in> (Guas\<^sub>c!0,(Guas\<^sub>s!0)\<^sup>*)\<^sub>\<alpha>) \<and>
          (ns\<^sub>c, ns2)\<in>PostsA!0 \<and> PostsA!0\<subseteq>\<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Ca, Normal ns1) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw,Normal ns2)"
          using  Cons(5) sim_elim_cases_c(2)[OF sim] by auto    
        have "((\<sigma>, \<sigma>), s\<^sub>s, Normal ns2)
           \<in> ((\<Union>a<length Guas\<^sub>c.
                  Guas\<^sub>c ! a, (\<Union>a<length Guas\<^sub>s. Guas\<^sub>s ! a)\<^sup>*)\<^sub>\<alpha>) \<and>
           (ns\<^sub>c, ns2) \<in> (\<Union>a<length PostsA. PostsA ! a) \<and>
           (\<exists>c''. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Ca # Cs, s\<^sub>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c'', Normal ns2) \<and>
                  final_c (c'', Normal ns2) \<and>
                  (\<exists>i<length c''. c'' ! i = LanguageCon.com.Throw))"
       using all_throw_tran'[OF Cons(3) Cons(5) Cons(6) Cons(7,8) sim_res _] hyp_step 
          unfolding Guasc_def Guass_def Postsq_def Postsa_def by fast
        then have ?case by auto
      }
      ultimately have ?case by auto 
    }
    ultimately have ?case by auto
  }  note y = this    
  show ?case using list.exhaust[OF x y] by auto      
qed  





(* lemma "i\<le>j \<Longrightarrow> Rel_wf (i+1) R1 \<Longrightarrow> Rel_wf (j+1) R2 \<Longrightarrow> R1 \<subseteq> R2 \<Longrightarrow> Seq_rel (i+1) R1 \<subseteq> Seq_rel (j+1) R2"  
proof auto
  fix \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls
  assume a1: "i\<le> j" and 
         a2:"Rel_wf (i+1) R1" and
         a3:"Rel_wf (j+1) R2" and 
         a4:"R1 \<subseteq> R2" and "(((\<sigma>g,\<sigma>l), \<sigma>ls),((\<Sigma>g,\<Sigma>l), \<Sigma>ls)) \<in> Seq_rel (i+1) R1"  
  then have "(toParState i ((\<sigma>g,\<sigma>l), \<sigma>ls), toParState i ((\<Sigma>g,\<Sigma>l), \<Sigma>ls)) \<in> R1"
    
  then show "(((\<sigma>g,\<sigma>l), \<sigma>ls),((\<Sigma>g,\<Sigma>l), \<Sigma>ls)) \<in> Seq_rel (j+1) R2"
    
  
qed *)
thm list_nonempty_induct
lemma sim_final_skip: assumes 
  a0':"length Rels\<^sub>c = length Guas\<^sub>c \<and> length Rels\<^sub>c = length PostsQ \<and> length Rels\<^sub>c = length PostsA \<and>
         length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s " and
  a0'':"length Rels\<^sub>c = length Coms\<^sub>s \<and> length Rels\<^sub>c = length Coms\<^sub>c" and
  a0''':"length Rels\<^sub>c >0" and
  a0:"\<forall>i<length Rels\<^sub>c.
       R\<^sub>c \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. (Guas\<^sub>c ! j)) \<subseteq> (Rels\<^sub>c ! i) \<and>
       R\<^sub>s \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. (Guas\<^sub>s ! j)) \<subseteq> (Rels\<^sub>s!i)" and
  a1:" (\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)) \<subseteq> G\<^sub>c" and
  a2:" (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s ! j)) \<subseteq> G\<^sub>s" and             
  a3:" (\<Inter>i<length PostsQ.  (PostsQ ! i)) \<subseteq> \<gamma>\<^sub>n" and
  a4:" (\<Union>i<length PostsA.  (PostsA ! i)) \<subseteq> \<gamma>\<^sub>a " and 
  a5:"length PostsQ = length (snd \<sigma>)" and a14:"length PostsQ = length (snd \<Sigma>)" and 
  a6:"Rel_wf (Suc (length PostsQ)) \<alpha>" and a16:"Rel_wf (Suc (length PostsQ)) G\<^sub>c" and a17:"Rel_wf (Suc (length PostsQ)) G\<^sub>s" and
  a7:"\<forall>i<length PostsQ. Rel_wf i (Rels\<^sub>s ! i)" and
  a8:"\<forall>i<length PostsQ. Rel_wf i (Rels\<^sub>c ! i)" and
  a9:"(\<forall>i<length C. C ! i = LanguageCon.com.Skip)" and
  a10:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a11:"\<gamma>\<^sub>a \<subseteq> \<alpha>" and 
  a12: "C \<noteq> []" and 
  a13:"\<forall>i<length C. 
        (\<Gamma>\<^sub>c, (C ! i,toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c !i), Seq_rel i (Guas\<^sub>c!i)) 
                 \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>) 
        (\<Gamma>\<^sub>s,(S! i,toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s!i), Seq_rel i (Guas\<^sub>s !i))" and
  a14:"length C = length S" and  a14':"length C = length Rels\<^sub>c" and
  a15:"((\<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls)) \<in> \<alpha>" and a16:"length \<sigma>ls  = length \<Sigma>ls" and a17:"length PostsQ = length \<sigma>ls" and
  a18:"\<forall>i<length PostsQ. Rel_wf i (Guas\<^sub>c ! i)" and 
  a19:"\<forall>i<length PostsQ. Rel_wf i (Guas\<^sub>s ! i)" and 
  a20:"\<forall>i<length PostsQ. Rel_wf i (PostsQ ! i)"
  shows "\<exists>ab bb. (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                 ((\<sigma>g, \<sigma>ls), ab, bb) \<in> (\<Inter>i<length PostsQ.  (PostsQ ! i)) \<and> 
              (\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', ab, bb) \<and>
                    (\<forall>i<length c\<^sub>s'. c\<^sub>s' ! i = LanguageCon.com.Skip) \<and> c\<^sub>s' \<noteq> [])"
  using a12 a9 a13 a14 a15 a16 a14'
proof(induction arbitrary:  S \<Sigma>g \<Sigma>ls rule:list_nonempty_induct)
  case (single x )
  have sim:"(\<Gamma>\<^sub>c,(Skip, toSeqState 0 (\<sigma>g, \<sigma>ls)),Seq_rel 0 (Rels\<^sub>c ! 0),Seq_rel 0 (Guas\<^sub>c ! 0))
       \<succeq>\<^sub>(\<^sub>Seq_rel 0 \<alpha>\<^sub>;\<^sub>xx 0 PostsQ\<^sub>;\<^sub>xx 0 PostsA\<^sub>)
       (\<Gamma>\<^sub>s,(S ! 0, toSeqState 0 (\<Sigma>g, \<Sigma>ls)),Seq_rel 0 (Rels\<^sub>s ! 0),Seq_rel 0 (Guas\<^sub>s ! 0))"
    using single by auto  
  note x =  dest_final_skip[OF sim]
  then obtain  \<Sigma>g' \<Sigma>l' \<Sigma>ls' where step:
    "((toSeqState 0 (\<sigma>g, \<sigma>ls), toSeqState 0 (\<sigma>g, \<sigma>ls)), toSeqState 0 (\<Sigma>g, \<Sigma>ls), ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls'))
        \<in> (Seq_rel 0 (Guas\<^sub>c ! 0), (Seq_rel 0 (Guas\<^sub>s ! 0))\<^sup>*)\<^sub>Seq_rel 0 \<alpha> \<and>
        snd (toSeqState 0 (\<Sigma>g, \<Sigma>ls)) = \<Sigma>ls' \<and>
        (toSeqState 0 (\<sigma>g, \<sigma>ls), ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls')) \<in> xx 0 PostsQ \<and>
        xx 0 PostsQ \<subseteq> Seq_rel 0 \<alpha> \<and>
        \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S ! 0, CRef.toSeq (toSeqState 0 (\<Sigma>g, \<Sigma>ls))) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, (\<Sigma>g', \<Sigma>l'))"
    using dest_final_skip[OF sim] unfolding toSeq_def by auto 
  then have eq_seq_seq:"snd (toSeqState 0 (\<Sigma>g, \<Sigma>ls)) = \<Sigma>ls'" by auto
  have len_\<sigma>:"0<length \<sigma>ls" and  len_\<Sigma>:"0<length \<Sigma>ls" using a6
    using Rel_wf_def a0' a0''' single(4) by fastforce+  
  moreover have eq_\<Sigma>:"((\<Sigma>g', \<Sigma>l'), \<Sigma>ls') = toSeqState 0 ( toParState 0 ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls'))"
    by (simp add: Par2Seq0)    
  moreover have len_snd_Sigma: "length (snd (toParState 0 ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls'))) = length \<Sigma>ls"
    using step calculation unfolding toSeqState_def toParState_def by auto     
  ultimately have len_\<Sigma>':"0<length (snd ( toParState 0 ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls')))" 
    unfolding toSeqState_def toParState_def by simp    
  obtain \<Sigma>lls' where 
      eq_seq:"(\<Sigma>g', \<Sigma>lls') = toParState 0 ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls') \<and>
              ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls') = toSeqState 0 (\<Sigma>g', \<Sigma>lls')" using toPar_gi eq_\<Sigma>
    by (metis (no_types, lifting) prod.exhaust_sel)  
  have eq_to_seq:"toParState 0 ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls') = toPar 0 (\<Sigma>g', \<Sigma>l') (\<Sigma>g, \<Sigma>ls)" 
    using  eq_seq_seq unfolding toParState_def toSeqState_def Let_def split_def apply auto
    by (metis (no_types) Cons_nth_drop_Suc drop0 len_\<Sigma> list_update_code(2))
  have "(((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), (\<Sigma>g', \<Sigma>lls')) \<in> ((Guas\<^sub>c ! 0), (Guas\<^sub>s ! 0)\<^sup>*)\<^sub>\<alpha>"
  proof-    
    have rel:"((toSeqState 0 (\<sigma>g, \<sigma>ls), toSeqState 0 (\<sigma>g, \<sigma>ls)), 
           toSeqState 0 (\<Sigma>g, \<Sigma>ls), toSeqState 0 (\<Sigma>g', \<Sigma>lls'))
            \<in> (Seq_rel 0 (Guas\<^sub>c ! 0), (Seq_rel 0 (Guas\<^sub>s ! 0))\<^sup>*)\<^sub>Seq_rel 0 \<alpha>" 
      using   eq_seq local.step   by force      
    have a6':"Rel_wf 0 \<alpha>" using a6  unfolding Rel_wf_def by auto    
    show ?thesis using rel_tran_seq'[OF rel len_\<sigma> a6' _ _ _ ] single(5) a6 a0' a18 a19 
            len_snd_Sigma a0''' a17 eq_seq
      by (metis (no_types) len_snd_Sigma a0''' a17 eq_seq snd_conv)
  qed
  then have "(((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), (\<Sigma>g', \<Sigma>lls')) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
    by (metis (no_types, lifting) G_comp1 UN_subset_iff a0' a0''' a1 a2 lessThan_iff) 
  moreover have "((\<sigma>g, \<sigma>ls), \<Sigma>g', \<Sigma>lls') \<in>  (\<Inter> ((!) PostsQ ` {..<length PostsQ}))"
  proof-
    have "(toSeqState 0 (\<sigma>g, \<sigma>ls), toSeqState 0 (\<Sigma>g', \<Sigma>lls')) \<in> Seq_rel 0 (PostsQ!0)" 
      using eq_seq step unfolding xx_def by force    
    then have "((\<sigma>g, \<sigma>ls), (\<Sigma>g', \<Sigma>lls')) \<in> PostsQ ! 0" 
      using Seq_rel_par'  a0' a0''' a20
      by (metis a17 eq_seq len_snd_Sigma single.prems(5) snd_conv)    
    then show ?thesis using a3 a0' single(6) less_Suc0 by auto
  qed   
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* ([Skip], (\<Sigma>g', \<Sigma>lls')) \<and> 
                  (\<forall>i<length [Skip]. [Skip] ! i = LanguageCon.com.Skip) \<and> [Skip] \<noteq> []" 
  proof-
    have step_par_s:
      "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[0:=Skip], toPar 0 (\<Sigma>g', \<Sigma>l') (\<Sigma>g, \<Sigma>ls))"      
    proof- 
       have f3:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S ! 0, toSeqPar 0 (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, (\<Sigma>g', \<Sigma>l'))" 
        using step  
        by (auto simp add: toSeqPar_toSeq_SeqState)  
      then show ?thesis using mult_step_in_par1[OF _ _ f3] a0'
        using a17 single.prems(3) single.prems(5) single.prems(6) by force      
    qed
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[0:=Skip], (\<Sigma>g', \<Sigma>lls'))" using eq_to_seq eq_seq
      by presburger 
    then have  "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* ([Skip], (\<Sigma>g', \<Sigma>lls'))" using single(3)
      by (metis (no_types, lifting) length_Cons length_list_update 
           less_Suc0 list.size(3) nth_Cons_0 nth_equalityI nth_list_update_eq)
    moreover have  "(\<forall>i<length [Skip]. [Skip] ! i = LanguageCon.com.Skip)" by auto
    moreover have "[Skip] \<noteq> []" by auto
    ultimately show ?thesis by auto
  qed    
  ultimately show ?case by fastforce   
next
  case (cons x xs)
  obtain \<Sigma>g' \<Sigma>ls' where 
        "(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g', \<Sigma>ls') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
           ((\<sigma>g, \<sigma>ls), \<Sigma>g', \<Sigma>ls') \<in> \<Inter> ((!) PostsQ ` {..<length PostsQ})  \<and>
           \<gamma>\<^sub>n \<subseteq> \<alpha> \<and>
           (\<exists>c\<^sub>s'.
               \<Gamma>\<^sub>s\<turnstile>\<^sub>p (?S, ?\<Sigma>g, ?\<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>g', \<Sigma>ls') \<and>
               (\<forall>i<length c\<^sub>s'. c\<^sub>s' ! i = LanguageCon.com.Skip) \<and> c\<^sub>s' \<noteq> [])" 
  then show ?case sorry
qed

lemma sim_comp_sound1:
  assumes    
    a0':"length Rels\<^sub>c = length Guas\<^sub>c \<and> length Rels\<^sub>c = length PostsQ \<and> length Rels\<^sub>c = length PostsA \<and>
         length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s " and
    a0'':"length Rels\<^sub>c = length Coms\<^sub>s \<and> length Rels\<^sub>c = length Coms\<^sub>c" and
    a0''':"length Rels\<^sub>c >0" and
    a0:"\<forall>i<length Rels\<^sub>c.
       R\<^sub>c \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. (Guas\<^sub>c ! j)) \<subseteq> (Rels\<^sub>c ! i) \<and>
       R\<^sub>s \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. (Guas\<^sub>s ! j)) \<subseteq> (Rels\<^sub>s!i)" and
 a1:" (\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)) \<subseteq> G\<^sub>c" and
 a2:" (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s ! j)) \<subseteq> G\<^sub>s" and             
 a3:" (\<Inter>i<length PostsQ.  (PostsQ ! i)) \<subseteq> \<gamma>\<^sub>n" and
 a4:" (\<Union>i<length PostsA.  (PostsA ! i)) \<subseteq> \<gamma>\<^sub>a " and 
 a5:" \<forall>i<length PostsQ.                                                          
       (\<Gamma>\<^sub>c, (Coms\<^sub>c ! i,toSeqState i \<sigma>),Seq_rel i (Rels\<^sub>c !i), Seq_rel i (Guas\<^sub>c!i)) 
          \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>) 
       (\<Gamma>\<^sub>s,(Coms\<^sub>s! i,toSeqState i \<Sigma>),Seq_rel i (Rels\<^sub>s!i), Seq_rel i (Guas\<^sub>s !i))" and
 a8:"\<forall>i<length PostsA. Sta\<^sub>s (Seq_rel i (PostsA!i)) (Seq_rel i (Rels\<^sub>c!i), Seq_rel i ((Rels\<^sub>s!i)\<^sup>*))\<^sub>(Seq_rel i \<alpha>)" and
 a9:"\<forall>i<length PostsQ. Sta\<^sub>s (Seq_rel i (PostsQ!i)) (Seq_rel i (Rels\<^sub>c!i), Seq_rel i ((Rels\<^sub>s!i)\<^sup>*))\<^sub>(Seq_rel i \<alpha>)" and 
 a10:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a11:"\<gamma>\<^sub>a \<subseteq> \<alpha>" and 
 a12:"\<forall>i<length PostsQ. \<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow>(\<sigma>,\<sigma>)\<in> (Guas\<^sub>c ! i)" and 
 a13:"length PostsQ = length (snd \<sigma>)" and a14:"length PostsQ = length (snd \<Sigma>)" and 
 a15:"R_wf (length PostsQ) \<alpha>" and a16:"R_wf (length PostsQ) G\<^sub>c" and a17:"R_wf (length PostsQ) G\<^sub>s" and
 a20:"\<forall>i<length PostsQ. R_wf (length PostsQ) (Rels\<^sub>s ! i)" and
 a21:"\<forall>i<length PostsQ. R_wf (length PostsQ) (Rels\<^sub>c ! i)"
shows "(\<Gamma>\<^sub>c,(Coms\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Coms\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" 
  using a5 a0'' a13 a14 
proof (coinduction arbitrary:\<sigma> \<Sigma> Coms\<^sub>c Coms\<^sub>s,clarsimp)  
  fix \<sigma>g \<sigma>ls \<Sigma>g \<Sigma>ls Coms\<^sub>c' Coms\<^sub>s'
  assume a5:
   "\<forall>i<length \<sigma>ls. 
      (\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i)) 
         \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
      (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i, toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" and
  a01:"length \<Sigma>ls = length \<sigma>ls" and a02:"length PostsQ = length \<sigma>ls" and
  a0'': "length Coms\<^sub>c' = length Coms\<^sub>s'" and
  a01'':"length Rels\<^sub>c = length Coms\<^sub>s'" 
  have R_wf_Rc:"R_wf (length PostsQ) R\<^sub>c" 
  proof- 
    have "R\<^sub>c \<subseteq> Rels\<^sub>c !0" using a0 a0'''  by auto
    moreover have "R_wf (length PostsQ) (Rels\<^sub>c !0)" using a21 a0''' a0' by auto
    ultimately show ?thesis using R_wf_subset by auto
  qed
  have R_wf_Rs:"R_wf (length PostsQ) R\<^sub>s" 
  proof- 
    have "R\<^sub>s \<subseteq> Rels\<^sub>s !0" using a0 a0'''  by auto
    moreover have "R_wf (length PostsQ) (Rels\<^sub>s !0)" using a20 a0''' a0' by auto
    ultimately show ?thesis using R_wf_subset by auto
  qed
  have 
    a18:"\<forall>i<length PostsQ. R_wf (length PostsQ) (Guas\<^sub>c ! i)" and 
    a19:"\<forall>i<length PostsQ. R_wf (length PostsQ) (Guas\<^sub>s ! i)"
     apply auto  using a0' a1 a16 unfolding R_wf_def apply fastforce
     using a0' a2 a17 unfolding R_wf_def by fastforce     
  have a5':
    "\<forall>i<length PostsQ.   
      (\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i)) 
         \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
      (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i, toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))"
    using a5 a0'' a01'' a0' a02 by auto  
  moreover have alpha:"((\<sigma>g,\<sigma>ls), (\<Sigma>g,\<Sigma>ls)) \<in> \<alpha>"
  proof-              
     have "(toSeqState 0 (\<sigma>g,\<sigma>ls), toSeqState 0 (\<Sigma>g,\<Sigma>ls)) \<in> Seq_rel 0 \<alpha>"
      using  dest_sim_alpha a0' a0'''   a01'' a5' 
      by metis               
    then show ?thesis using a15 unfolding toSeqState_def 
         Seq_rel_def Let_def split_beta R_wf_def  apply auto
      by (metis Cons_nth_drop_Suc a0' a0''' a01  a02 drop0)      
  qed
(*  moreover have a02:"length PostsQ = length (\<sigma>ls)" using  alpha a15 unfolding R_wf_def by auto
  moreover have a01:"length \<Sigma>ls = length \<sigma>ls" using alpha a15 unfolding R_wf_def by auto *)
  moreover 
  { fix c\<^sub>c' \<sigma>'g \<sigma>'ls
    assume b01:"\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>\<tau> (Coms\<^sub>c', (\<sigma>g,\<sigma>ls)) \<rightarrow> (c\<^sub>c',  (\<sigma>'g,\<sigma>'ls))"
    then obtain i c' where "i< length Coms\<^sub>c' \<and>  
                            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> ((Coms\<^sub>c'!i), toSeqPar  i (\<sigma>g,\<sigma>ls)) \<rightarrow> (c',  toSeqPar i (\<sigma>'g,\<sigma>'ls)) \<and>
                            (\<forall>j. j\<noteq>i \<longrightarrow> c\<^sub>c'!j = (Coms\<^sub>c'!j)) \<and> c\<^sub>c'!i=c' \<and> (\<forall>j\<noteq>i. \<sigma>'ls ! j = \<sigma>ls ! j) \<and> 
                       length \<sigma>'ls = length \<sigma>ls"
      apply clarsimp apply (rule step_pev_pair_elim_cases[OF b01]) using a0' a0'' a01'' a02
      by (metis eq_snd_iff fstI length_list_update nth_list_update_eq nth_list_update_neq)      
    then have step:"i< length Coms\<^sub>c' \<and>  
                    \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> ((Coms\<^sub>c'!i), CRef.toSeq (toSeqState i (\<sigma>g, \<sigma>ls))) \<rightarrow>
                          (c', CRef.toSeq ((\<sigma>'g, (\<sigma>'ls!i)), snd (toSeqState i (\<sigma>g, \<sigma>ls)))) \<and>
                    (\<forall>j. j\<noteq>i \<longrightarrow> c\<^sub>c'!j = (Coms\<^sub>c'!j)) \<and> c\<^sub>c'!i=c' \<and> (\<forall>j\<noteq>i. \<sigma>'ls ! j = \<sigma>ls ! j) \<and>
                    length \<sigma>'ls = length \<sigma>ls"
      unfolding toSeq_def toSeqState_def by auto
    then have sim:
      "(\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i)) 
          \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
       (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i, toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" 
      using a5 a0' a0'' a01''
      by (simp add: a5') 
    have i_len:"i<length PostsQ" using a5 a0' a0'' a01'' step by auto   
    obtain c\<^sub>s' \<Sigma>'g \<Sigma>'ls where alpha_rel_guar:
      "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Coms\<^sub>s' ! i, CRef.toSeq (toSeqState i (\<Sigma>g, \<Sigma>ls))) \<rightarrow>\<^sub>\<tau>\<^sup>*
            (c\<^sub>s', CRef.toSeq ((\<Sigma>'g, \<Sigma>'ls), snd (toSeqState i (\<Sigma>g, \<Sigma>ls)))) \<and>
        (((\<sigma>'g, (\<sigma>'ls!i)), snd (toSeqState i (\<sigma>g, \<sigma>ls))), (\<Sigma>'g, \<Sigma>'ls), 
           snd (toSeqState i (\<Sigma>g, \<Sigma>ls))) \<in> Seq_rel i \<alpha> \<and>
        ((toSeqState i (\<sigma>g, \<sigma>ls), (\<sigma>'g, (\<sigma>'ls!i)), snd (toSeqState i (\<sigma>g, \<sigma>ls))), 
           toSeqState i (\<Sigma>g, \<Sigma>ls), (\<Sigma>'g, \<Sigma>'ls), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))) 
            \<in> ((Seq_rel i (Guas\<^sub>c ! i), (Seq_rel i (Guas\<^sub>s ! i))\<^sup>*)\<^sub>(Seq_rel i \<alpha>)) \<and>
         (\<Gamma>\<^sub>c,(c', (\<sigma>'g, (\<sigma>'ls!i)), snd (toSeqState i (\<sigma>g, \<sigma>ls))),
                Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
             (\<Gamma>\<^sub>s,(c\<^sub>s', (\<Sigma>'g, \<Sigma>'ls), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))),
                Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" 
      using  step apply clarify by (rule sim_elim_cases[OF sim], force)   
    obtain \<Sigma>'g1 \<Sigma>'ls1 
      where eq_\<Sigma>_par:"(\<Sigma>'g1, \<Sigma>'ls1) = (toPar i (\<Sigma>'g, \<Sigma>'ls) (\<Sigma>g, \<Sigma>ls))"
      by auto    
    have eq_toseq\<sigma>':"toSeqState i (\<sigma>'g, (\<sigma>'ls)) = ((\<sigma>'g, (\<sigma>'ls!i)), snd (toSeqState i (\<sigma>g, \<sigma>ls)))"
        using step unfolding toSeqState_def Let_def split_beta apply auto
        apply (metis a0' a0'' a01'' a02 append_eq_append_conv eq_list_i length_take)
        by (metis a0' a0'' a01'' a02 append_eq_append_conv eq_list_i length_drop)
    have eq_toseq\<Sigma>':"toSeqState i (toPar i (\<Sigma>'g, \<Sigma>'ls) (\<Sigma>g, \<Sigma>ls)) = 
                     ((\<Sigma>'g, \<Sigma>'ls), snd (toSeqState i (\<Sigma>g, \<Sigma>ls)))"
        unfolding toSeqState_def apply auto
        by (metis a0' a0'' a01 a01'' a02 local.step nth_list_update_eq) 
    have alpha_rel_guar':"(toSeqState i (\<sigma>'g, \<sigma>'ls), toSeqState i (\<Sigma>'g1, \<Sigma>'ls1)) \<in> Seq_rel i \<alpha> \<and>
     ((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>'g, \<sigma>'ls)), toSeqState i (\<Sigma>g, \<Sigma>ls), toSeqState i (\<Sigma>'g1, \<Sigma>'ls1))
     \<in> (Seq_rel i (Guas\<^sub>c ! i), (Seq_rel i (Guas\<^sub>s ! i))\<^sup>*)\<^sub>Seq_rel i \<alpha> \<and>
     (\<Gamma>\<^sub>c,(c', toSeqState i (\<sigma>'g, \<sigma>'ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
     \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
     (\<Gamma>\<^sub>s,(c\<^sub>s', toSeqState i (\<Sigma>'g1, \<Sigma>'ls1)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" 
       using alpha_rel_guar eq_\<Sigma>_par eq_toseq\<Sigma>' eq_toseq\<sigma>' by auto
    have "((\<sigma>'g, \<sigma>'ls), (toPar i (\<Sigma>'g, \<Sigma>'ls) (\<Sigma>g, \<Sigma>ls))) \<in> \<alpha>"
    proof-                   
      have "(toSeqState i (\<sigma>'g, (\<sigma>'ls)), toSeqState i (toPar i (\<Sigma>'g, \<Sigma>'ls) (\<Sigma>g, \<Sigma>ls))) 
         \<in> Seq_rel i \<alpha>"
        using alpha_rel_guar eq_toseq\<sigma>' eq_toseq\<Sigma>'
        by fastforce     
      moreover have "R_wf (length (snd (toPar i (\<Sigma>'g, \<Sigma>'ls) (\<Sigma>g, \<Sigma>ls)))) \<alpha>"
      proof-
        have "length (snd (toPar i (\<Sigma>'g, \<Sigma>'ls) (\<Sigma>g, \<Sigma>ls))) = length \<Sigma>ls"
          by auto
        also have "R_wf (length \<Sigma>ls) \<alpha>"
          using a01 a02 a15 by auto
        finally show ?thesis by auto
      qed
      ultimately show ?thesis using Seq_rel_par
        using R_wf_def a02 alpha i_len local.step by fastforce
    qed
    then have "((\<sigma>'g, \<sigma>'ls), \<Sigma>'g1,\<Sigma>'ls1) \<in> \<alpha>" using eq_\<Sigma>_par by auto
    moreover have step_par_s:
      "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Coms\<^sub>s'[i:=c\<^sub>s'], toPar i (\<Sigma>'g, \<Sigma>'ls) (\<Sigma>g, \<Sigma>ls))" 
      using mult_step_in_par1 a0' a01 a01'' a02 alpha_rel_guar a0'' step
    proof- 
       have f3:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Coms\<^sub>s' ! i, toSeqPar i (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', (\<Sigma>'g, \<Sigma>'ls))" 
        using alpha_rel_guar  
        apply (auto simp add: toSeqPar_toSeq_SeqState) by (auto simp add: toSeq_def) 
      then show ?thesis using mult_step_in_par1[OF _ _ f3] 
         mult_step_in_par1 a0' a01 a01'' a02  a0'' step by auto      
    qed
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Coms\<^sub>s'[i:=c\<^sub>s'], \<Sigma>'g1,\<Sigma>'ls1)" using eq_\<Sigma>_par by auto
    moreover have gcs:"(((\<sigma>g,\<sigma>ls), (\<sigma>'g,\<sigma>'ls)), (\<Sigma>g, \<Sigma>ls), 
                        toPar i (\<Sigma>'g, \<Sigma>'ls) (\<Sigma>g, \<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
    proof-
      have i_len:"i<length \<sigma>ls" 
        using a02 i_len step by auto
      moreover have "(((\<sigma>g, \<sigma>ls), \<sigma>'g, \<sigma>'ls), (\<Sigma>g, \<Sigma>ls), fst (toPar i (\<Sigma>'g, \<Sigma>'ls) (\<Sigma>g, \<Sigma>ls)), 
                    snd (toPar i (\<Sigma>'g, \<Sigma>'ls) (\<Sigma>g, \<Sigma>ls))) \<in> (Guas\<^sub>c ! i, (Guas\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha>"
      proof-        
        have eq_len:"
          length \<sigma>'ls = length \<sigma>ls \<and> length \<sigma>ls = length \<Sigma>ls \<and>
          length \<Sigma>ls =  length (snd (toPar i (\<Sigma>'g, \<Sigma>'ls) (\<Sigma>g, \<Sigma>ls)))"
          using step a01 by auto        
         moreover have RF:"R_wf (length \<sigma>ls) (Guas\<^sub>c ! i) \<and> R_wf (length \<sigma>ls) (Guas\<^sub>s ! i)"
           using a16 a17   unfolding R_wf_def apply auto
           by (metis (no_types, hide_lams) UN_subset_iff  lessThan_iff 
                  subsetD  a0'  a0'' a02  a01'' a2 a1 step)+  
         ultimately show ?thesis using eq_toseq\<Sigma>' eq_toseq\<sigma>'
           by (metis  i_len  a02 a15 alpha_rel_guar prod.exhaust_sel rel_tran_seq)
       qed     
       moreover have "Guas\<^sub>c ! i \<subseteq> G\<^sub>c"
         by (metis (no_types) UN_subset_iff i_len a0' a02 a1 lessThan_iff)
       moreover have "Guas\<^sub>s ! i \<subseteq> G\<^sub>s"
         by (metis (no_types) UN_subset_iff i_len a0' a02 a2 lessThan_iff)
       ultimately show ?thesis by (simp add: G_comp1)       
     qed
     then have "(((\<sigma>g,\<sigma>ls), (\<sigma>'g,\<sigma>'ls)), (\<Sigma>g, \<Sigma>ls), \<Sigma>'g1, \<Sigma>'ls1) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
       using eq_\<Sigma>_par by auto
     moreover have 
       "(\<forall>i'<length PostsQ. (\<Gamma>\<^sub>c,(c\<^sub>c' ! i', toSeqState i' (\<sigma>'g,\<sigma>'ls)),
             Seq_rel i' (Rels\<^sub>c ! i'),Seq_rel i' (Guas\<^sub>c ! i')) 
          \<succeq>\<^sub>(\<^sub>Seq_rel i' \<alpha>\<^sub>;\<^sub>xx i' PostsQ\<^sub>;\<^sub>xx i' PostsA\<^sub>)
        (\<Gamma>\<^sub>s,(Coms\<^sub>s'[i:=c\<^sub>s'] ! i', toSeqState i' (\<Sigma>'g1, \<Sigma>'ls1)),
            Seq_rel i' (Rels\<^sub>s ! i'),Seq_rel i' (Guas\<^sub>s ! i')))"  
     proof-
       have aa:"i < length Coms\<^sub>c' \<and> (\<forall>j. j \<noteq> i \<longrightarrow> c\<^sub>c' ! j = Coms\<^sub>c' ! j) \<and> c\<^sub>c' ! i = c'" using step
         by blast    
       have "length \<sigma>ls = length PostsQ" and "length \<sigma>ls = length \<sigma>'ls" and 
              "length \<Sigma>ls = length \<sigma>ls" and len_\<Sigma>':"length \<Sigma>ls = length \<Sigma>'ls1"
         using eq_\<Sigma>_par by (auto simp add: a02 step a01 )       
       then show ?thesis 
         using rest_sim[OF a0 a0' a0''' a5' a0'' a01'' i_len 
               alpha_rel_guar' aa a15 a16 a17 a18 a19 a20 a21] by auto                 
     qed   
     then have "(\<forall>i'<length \<sigma>ls. (\<Gamma>\<^sub>c,(c\<^sub>c' ! i', toSeqState i' (\<sigma>'g,\<sigma>'ls)),
             Seq_rel i' (Rels\<^sub>c ! i'),Seq_rel i' (Guas\<^sub>c ! i')) 
          \<succeq>\<^sub>(\<^sub>Seq_rel i' \<alpha>\<^sub>;\<^sub>xx i' PostsQ\<^sub>;\<^sub>xx i' PostsA\<^sub>)
        (\<Gamma>\<^sub>s,(Coms\<^sub>s'[i:=c\<^sub>s'] ! i', toSeqState i' (\<Sigma>'g1, \<Sigma>'ls1)),
            Seq_rel i' (Rels\<^sub>s ! i'),Seq_rel i' (Guas\<^sub>s ! i')))"  
       using a15 unfolding R_wf_def
       by (metis (no_types, hide_lams) calculation(1)  local.step )                      
     moreover have "length Coms\<^sub>s' = length (Coms\<^sub>s'[i:=c\<^sub>s']) \<and>
                    length Coms\<^sub>s' = length c\<^sub>c' \<and> length \<sigma>ls = length \<sigma>'ls \<and> 
                    length \<sigma>ls = length  \<Sigma>'ls1"
       by (metis (no_types, hide_lams) R_wf_def a0'' a15 b01 
           calculation(1) length_list_update local.step step_pev_pair_elim_cases)       
     ultimately have "\<exists>c\<^sub>s' aa ba.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', aa, ba) \<and>
                ((\<sigma>'g,\<sigma>'ls), aa, ba) \<in> \<alpha> \<and>
                (((\<sigma>g, \<sigma>ls),\<sigma>'g, \<sigma>'ls), (\<Sigma>g, \<Sigma>ls), aa, ba) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                ((\<forall>i<length \<sigma>ls. (\<Gamma>\<^sub>c,(c\<^sub>c' ! i, toSeqState i (\<sigma>'g,\<sigma>'ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                     \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
                     (\<Gamma>\<^sub>s,(c\<^sub>s' ! i, toSeqState i (aa, ba)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))) \<and>
                 length Coms\<^sub>s' = length c\<^sub>s' \<and>
                 length Coms\<^sub>s' = length c\<^sub>c' \<and> length \<sigma>ls = length \<sigma>'ls \<and> length \<sigma>ls = length ba  \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'g,\<sigma>'ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', aa, ba),R\<^sub>s,G\<^sub>s))" by blast
  } 
  moreover 
  { fix v c\<^sub>c' \<sigma>g' \<sigma>ls'
    assume b01: "\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>(Some v) (Coms\<^sub>c', (\<sigma>g,\<sigma>ls)) \<rightarrow> (c\<^sub>c', (\<sigma>g',\<sigma>ls')) "
    then obtain i c' where "i< length Coms\<^sub>c' \<and>  
                            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) ((Coms\<^sub>c'!i), toSeqPar  i (\<sigma>g,\<sigma>ls)) \<rightarrow> (c',  toSeqPar i (\<sigma>g',\<sigma>ls')) \<and>
                            (\<forall>j. j\<noteq>i \<longrightarrow> c\<^sub>c'!j = (Coms\<^sub>c'!j)) \<and> c\<^sub>c'!i=c' \<and> (\<forall>j\<noteq>i. \<sigma>ls' ! j = \<sigma>ls ! j) \<and> 
                       length \<sigma>ls' = length \<sigma>ls"
      apply clarsimp apply (rule step_pev_pair_elim_cases[OF b01]) using a0' a0'' a01'' a02
      by (metis eq_snd_iff fstI length_list_update nth_list_update_eq nth_list_update_neq)
    then have step:"i< length Coms\<^sub>c' \<and>  
                    \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) ((Coms\<^sub>c'!i), CRef.toSeq (toSeqState i (\<sigma>g, \<sigma>ls))) \<rightarrow>
                          (c', CRef.toSeq ((\<sigma>g', (\<sigma>ls'!i)), snd (toSeqState i (\<sigma>g, \<sigma>ls)))) \<and>
                    (\<forall>j. j\<noteq>i \<longrightarrow> c\<^sub>c'!j = (Coms\<^sub>c'!j)) \<and> c\<^sub>c'!i=c' \<and> (\<forall>j\<noteq>i. \<sigma>ls' ! j = \<sigma>ls ! j) \<and>
                    length \<sigma>ls' = length \<sigma>ls"
      unfolding toSeq_def toSeqState_def by auto
    then have sim:
      "(\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i)) 
          \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
       (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i, toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" 
      using a5 a0' a0'' a01''
      by (simp add: a5')
    have i_len:"i<length PostsQ" using a5 a0' a0'' a01'' step by auto
    obtain c\<^sub>s' \<Sigma>g' \<Sigma>ls' where alpha_rel_guar:
      "\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (Coms\<^sub>s' ! i, CRef.toSeq (toSeqState i (\<Sigma>g, \<Sigma>ls))) \<rightarrow>\<^sup>+
            (c\<^sub>s', CRef.toSeq ((\<Sigma>g', \<Sigma>ls'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls)))) \<and>
        (((\<sigma>g', (\<sigma>ls'!i)), snd (toSeqState i (\<sigma>g, \<sigma>ls))), (\<Sigma>g', \<Sigma>ls'), 
           snd (toSeqState i (\<Sigma>g, \<Sigma>ls))) \<in> Seq_rel i \<alpha> \<and>
        ((toSeqState i (\<sigma>g, \<sigma>ls), (\<sigma>g', (\<sigma>ls'!i)), snd (toSeqState i (\<sigma>g, \<sigma>ls))), 
           toSeqState i (\<Sigma>g, \<Sigma>ls), (\<Sigma>g', \<Sigma>ls'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))) 
            \<in> ((Seq_rel i (Guas\<^sub>c ! i), (Seq_rel i (Guas\<^sub>s ! i))\<^sup>*)\<^sub>(Seq_rel i \<alpha>)) \<and>
         (\<Gamma>\<^sub>c,(c', (\<sigma>g', (\<sigma>ls'!i)), snd (toSeqState i (\<sigma>g, \<sigma>ls))),
                Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
             (\<Gamma>\<^sub>s,(c\<^sub>s', (\<Sigma>g', \<Sigma>ls'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))),
                Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" 
      using  step apply clarify by (rule sim_elim_cases[OF sim], force)
    obtain \<Sigma>g'1 \<Sigma>ls'1 
      where eq_\<Sigma>_par:"(\<Sigma>g'1, \<Sigma>ls'1) = (toPar i (\<Sigma>g', \<Sigma>ls') (\<Sigma>g, \<Sigma>ls))"
      by auto    
    have eq_toseq\<sigma>':"toSeqState i (\<sigma>g', (\<sigma>ls')) = ((\<sigma>g', (\<sigma>ls'!i)), snd (toSeqState i (\<sigma>g, \<sigma>ls)))"
        using step unfolding toSeqState_def Let_def split_beta apply auto
        apply (metis a0' a0'' a01'' a02 append_eq_append_conv eq_list_i length_take)
        by (metis a0' a0'' a01'' a02 append_eq_append_conv eq_list_i length_drop)
    have eq_toseq\<Sigma>':"toSeqState i (toPar i (\<Sigma>g', \<Sigma>ls') (\<Sigma>g, \<Sigma>ls)) = 
                     ((\<Sigma>g', \<Sigma>ls'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls)))"
        unfolding toSeqState_def apply auto
        by (metis a0' a0'' a01 a01'' a02 local.step nth_list_update_eq) 
    have alpha_rel_guar':"(toSeqState i (\<sigma>g', \<sigma>ls'), toSeqState i (\<Sigma>g'1, \<Sigma>ls'1)) \<in> Seq_rel i \<alpha> \<and>
     ((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>g', \<sigma>ls')), toSeqState i (\<Sigma>g, \<Sigma>ls), toSeqState i (\<Sigma>g'1, \<Sigma>ls'1))
     \<in> (Seq_rel i (Guas\<^sub>c ! i), (Seq_rel i (Guas\<^sub>s ! i))\<^sup>*)\<^sub>Seq_rel i \<alpha> \<and>
     (\<Gamma>\<^sub>c,(c', toSeqState i (\<sigma>g', \<sigma>ls')),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
     \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
     (\<Gamma>\<^sub>s,(c\<^sub>s', toSeqState i (\<Sigma>g'1, \<Sigma>ls'1)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" 
       using alpha_rel_guar eq_\<Sigma>_par eq_toseq\<Sigma>' eq_toseq\<sigma>' by auto
    have "((\<sigma>g', \<sigma>ls'), (toPar i (\<Sigma>g', \<Sigma>ls') (\<Sigma>g, \<Sigma>ls))) \<in> \<alpha>"
    proof-                   
      have "(toSeqState i (\<sigma>g', (\<sigma>ls')), toSeqState i (toPar i (\<Sigma>g', \<Sigma>ls') (\<Sigma>g, \<Sigma>ls))) 
         \<in> Seq_rel i \<alpha>"
        using alpha_rel_guar eq_toseq\<sigma>' eq_toseq\<Sigma>'
        by fastforce     
      moreover have "R_wf (length (snd (toPar i (\<Sigma>g', \<Sigma>ls') (\<Sigma>g, \<Sigma>ls)))) \<alpha>"
      proof-
        have "length (snd (toPar i (\<Sigma>g', \<Sigma>ls') (\<Sigma>g, \<Sigma>ls))) = length \<Sigma>ls"
          by auto
        also have "R_wf (length \<Sigma>ls) \<alpha>"
          using a01 a02 a15 by auto
        finally show ?thesis by auto
      qed
      ultimately show ?thesis using Seq_rel_par
        using R_wf_def a02 alpha i_len local.step by fastforce
    qed
    then have "((\<sigma>g', \<sigma>ls'), \<Sigma>g'1,\<Sigma>ls'1) \<in> \<alpha>" using eq_\<Sigma>_par by auto
    moreover have step_par_s:
      "\<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (Coms\<^sub>s', (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sup>+ (Coms\<^sub>s'[i:=c\<^sub>s'], toPar i (\<Sigma>g', \<Sigma>ls') (\<Sigma>g, \<Sigma>ls))" 
      using mult_step_in_par1 a0' a01 a01'' a02 alpha_rel_guar a0'' step
    proof- 
       have f3:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (Coms\<^sub>s' ! i, toSeqPar i (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sup>+ (c\<^sub>s', (\<Sigma>g', \<Sigma>ls'))" 
        using alpha_rel_guar  
        apply (auto simp add: toSeqPar_toSeq_SeqState) apply (auto simp add: toSeq_def)
        by blast 
      then show ?thesis using mult_step_in_par_ev1[OF _ _ f3] 
         mult_step_in_par1 a0' a01 a01'' a02  a0'' step by auto      
    qed
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (Coms\<^sub>s', (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sup>+ (Coms\<^sub>s'[i:=c\<^sub>s'], \<Sigma>g'1,\<Sigma>ls'1)" using eq_\<Sigma>_par by auto
    then have "\<exists>a ab b.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                (\<exists>ac ad bb.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>(Some v) (a, ab, b) \<rightarrow> (ac, ad, bb) \<and> 
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>p (ac, ad, bb) \<rightarrow>\<^sub>\<tau>\<^sup>* (Coms\<^sub>s'[i:=c\<^sub>s'], (\<Sigma>g'1,\<Sigma>ls'1)))"
      by auto
    moreover have gcs:"(((\<sigma>g,\<sigma>ls), (\<sigma>g',\<sigma>ls')), (\<Sigma>g, \<Sigma>ls), 
                        toPar i (\<Sigma>g', \<Sigma>ls') (\<Sigma>g, \<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
    proof-
      have i_len:"i<length \<sigma>ls" 
        using a02 i_len step by auto
      moreover have "(((\<sigma>g, \<sigma>ls), \<sigma>g', \<sigma>ls'), (\<Sigma>g, \<Sigma>ls), fst (toPar i (\<Sigma>g', \<Sigma>ls') (\<Sigma>g, \<Sigma>ls)), 
                    snd (toPar i (\<Sigma>g', \<Sigma>ls') (\<Sigma>g, \<Sigma>ls))) \<in> (Guas\<^sub>c ! i, (Guas\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha>"
      proof-        
        have eq_len:"
          length \<sigma>ls' = length \<sigma>ls \<and> length \<sigma>ls = length \<Sigma>ls \<and>
          length \<Sigma>ls =  length (snd (toPar i (\<Sigma>g', \<Sigma>ls') (\<Sigma>g, \<Sigma>ls)))"
          using step a01 by auto        
         moreover have RF:"R_wf (length \<sigma>ls) (Guas\<^sub>c ! i) \<and> R_wf (length \<sigma>ls) (Guas\<^sub>s ! i)"
           using a16 a17   unfolding R_wf_def apply auto
           by (metis (no_types, hide_lams) UN_subset_iff  lessThan_iff 
                  subsetD  a0'  a0'' a02  a01'' a2 a1 step)+  
         ultimately show ?thesis using eq_toseq\<Sigma>' eq_toseq\<sigma>'
           by (metis  i_len  a02 a15 alpha_rel_guar prod.exhaust_sel rel_tran_seq)
       qed     
       moreover have "Guas\<^sub>c ! i \<subseteq> G\<^sub>c"
         by (metis (no_types) UN_subset_iff i_len a0' a02 a1 lessThan_iff)
       moreover have "Guas\<^sub>s ! i \<subseteq> G\<^sub>s"
         by (metis (no_types) UN_subset_iff i_len a0' a02 a2 lessThan_iff)
       ultimately show ?thesis by (simp add: G_comp1)       
     qed
     then have "(((\<sigma>g,\<sigma>ls), (\<sigma>g',\<sigma>ls')), (\<Sigma>g, \<Sigma>ls), \<Sigma>g'1, \<Sigma>ls'1) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
       using eq_\<Sigma>_par by auto
     moreover have 
       "(\<forall>i'<length PostsQ. (\<Gamma>\<^sub>c,(c\<^sub>c' ! i', toSeqState i' (\<sigma>g',\<sigma>ls')),
             Seq_rel i' (Rels\<^sub>c ! i'),Seq_rel i' (Guas\<^sub>c ! i')) 
          \<succeq>\<^sub>(\<^sub>Seq_rel i' \<alpha>\<^sub>;\<^sub>xx i' PostsQ\<^sub>;\<^sub>xx i' PostsA\<^sub>)
        (\<Gamma>\<^sub>s,(Coms\<^sub>s'[i:=c\<^sub>s'] ! i', toSeqState i' (\<Sigma>g'1, \<Sigma>ls'1)),
            Seq_rel i' (Rels\<^sub>s ! i'),Seq_rel i' (Guas\<^sub>s ! i')))"  
     proof-
       have aa:"i < length Coms\<^sub>c' \<and> (\<forall>j. j \<noteq> i \<longrightarrow> c\<^sub>c' ! j = Coms\<^sub>c' ! j) \<and> c\<^sub>c' ! i = c'" using step
         by blast    
       have "length \<sigma>ls = length PostsQ" and "length \<sigma>ls = length \<sigma>ls'" and 
              "length \<Sigma>ls = length \<sigma>ls" and len_\<Sigma>':"length \<Sigma>ls = length \<Sigma>ls'1"
         using eq_\<Sigma>_par by (auto simp add: a02 step a01 )       
       then show ?thesis 
         using rest_sim[OF a0 a0' a0''' a5' a0'' a01'' i_len 
               alpha_rel_guar' aa a15 a16 a17 a18 a19 a20 a21] by auto                 
     qed   
     then have "(\<forall>i'<length \<sigma>ls. (\<Gamma>\<^sub>c,(c\<^sub>c' ! i', toSeqState i' (\<sigma>g',\<sigma>ls')),
             Seq_rel i' (Rels\<^sub>c ! i'),Seq_rel i' (Guas\<^sub>c ! i')) 
          \<succeq>\<^sub>(\<^sub>Seq_rel i' \<alpha>\<^sub>;\<^sub>xx i' PostsQ\<^sub>;\<^sub>xx i' PostsA\<^sub>)
        (\<Gamma>\<^sub>s,(Coms\<^sub>s'[i:=c\<^sub>s'] ! i', toSeqState i' (\<Sigma>g'1, \<Sigma>ls'1)),
            Seq_rel i' (Rels\<^sub>s ! i'),Seq_rel i' (Guas\<^sub>s ! i')))"  
       using a15 unfolding R_wf_def
       by (metis (no_types, hide_lams) calculation(1)  local.step )                      
     moreover have "length Coms\<^sub>s' = length (Coms\<^sub>s'[i:=c\<^sub>s']) \<and>
                    length Coms\<^sub>s' = length c\<^sub>c' \<and> length \<sigma>ls = length \<sigma>ls' \<and> 
                    length \<sigma>ls = length  \<Sigma>ls'1"
       by (metis (no_types, hide_lams) R_wf_def a0'' a15 b01 
           calculation(1) length_list_update local.step step_pev_pair_elim_cases)
     ultimately have "(\<exists>c\<^sub>s' aa ba.
                (\<exists>a ab b.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                    (\<exists>ac ad bb.
                        \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>Some v (a, ab, b) \<rightarrow> (ac, ad, bb) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p (ac, ad, bb) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', aa, ba))) \<and>
                ((\<sigma>g',\<sigma>ls'), aa, ba) \<in> \<alpha> \<and>
                (((\<sigma>g, \<sigma>ls), \<sigma>g', \<sigma>ls'), (\<Sigma>g, \<Sigma>ls), aa, ba) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                ((\<forall>i<length \<sigma>ls. (\<Gamma>\<^sub>c,(c\<^sub>c' ! i, toSeqState i (\<sigma>g', \<sigma>ls')),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                     \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
                     (\<Gamma>\<^sub>s,(c\<^sub>s' ! i, toSeqState i (aa, ba)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))) \<and>
                 length Coms\<^sub>s' = length c\<^sub>s' \<and>
                 length Coms\<^sub>s' = length c\<^sub>c' \<and> length \<sigma>ls = length \<sigma>ls' \<and> length \<sigma>ls = length ba \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>g',\<sigma>ls'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', aa, ba),R\<^sub>s,G\<^sub>s)))" by blast
   }  
  moreover 
  { fix \<sigma>g' \<sigma>ls'  \<Sigma>g' \<Sigma>ls'
    assume b01:"(((\<sigma>g, \<sigma>ls), \<sigma>g', \<sigma>ls'), (\<Sigma>g, \<Sigma>ls), \<Sigma>g', \<Sigma>ls') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>"
    have len_sigma:"length \<sigma>ls = length \<sigma>ls'" 
      using R_wf_Rc b01 unfolding related_transitions_def R_wf_def by fastforce       
    moreover have len_Sigma:"length \<Sigma>ls = length \<Sigma>ls'" 
      using b01 a15 mem_Collect_eq unfolding related_transitions_def R_wf_def
      apply auto
      by metis
    moreover have len_sigma_Sigma:"length \<sigma>ls = length \<Sigma>ls" 
      using alpha a0' a15 unfolding R_wf_def by auto
    moreover have len_sigma_Sigma':"length \<sigma>ls = length \<Sigma>ls'" using len_Sigma calculation by auto
    moreover have "(\<forall>i<length \<sigma>ls. (\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i, toSeqState i (\<sigma>g', \<sigma>ls')),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
                (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i, toSeqState i (\<Sigma>g', \<Sigma>ls')),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i)))"    
    proof -
    { fix i
      assume i:"i<length \<sigma>ls"      
      then have i':"i<length PostsQ"
        by (simp add: a02)
      then have rels:"R\<^sub>c \<subseteq> Rels\<^sub>c ! i \<and> R\<^sub>s \<subseteq> Rels\<^sub>s ! i" using a0' a0 by auto
      then have sim:"(\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
                (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i, toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" 
        using a5 i by auto
      have rel:"(((\<sigma>g, \<sigma>ls), \<sigma>g', \<sigma>ls'), (\<Sigma>g, \<Sigma>ls), \<Sigma>g', \<Sigma>ls') \<in> (Rels\<^sub>c ! i, (Rels\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha> " 
        using G_comp1[OF _ _ _] b01 rels by auto        
      have "((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>g', \<sigma>ls')), 
                   toSeqState i ((\<Sigma>g, \<Sigma>ls)), toSeqState i (\<Sigma>g', \<Sigma>ls')) \<in> 
                    (Seq_rel i (Rels\<^sub>c ! i), (Seq_rel i (Rels\<^sub>s ! i))\<^sup>*)\<^sub>(Seq_rel i \<alpha>)"
      proof- 
        have "R_wf (length \<sigma>ls) (Rels\<^sub>c ! i)" using a21
          by (simp add: a02 i)
        moreover have "R_wf (length \<sigma>ls) (Rels\<^sub>s ! i)" using a20
          by (simp add: a02 i)
        ultimately show ?thesis 
          using rel_tran_par[OF rel i _ _ _  len_sigma[THEN sym]] 
            len_sigma_Sigma len_sigma_Sigma a0'
          using a02 a15 len_sigma_Sigma' by auto             
        qed
      moreover obtain a1 a2 a3 b1 b2 b3 where 
        seq1:"toSeqState i (\<sigma>g', \<sigma>ls') = ((a1, a2), a3)" and 
        seq2:"toSeqState i (\<Sigma>g', \<Sigma>ls') = ((b1,b2), b3)"
          unfolding toSeqState_def
          by auto
      ultimately have "(\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i,((a1, a2), a3)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
              \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
              (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i, ((b1, b2), b3)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))"
        apply auto
        by (rule dest_sim_env_step[OF sim], assumption)      
      then have "(\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i,toSeqState i (\<sigma>g', \<sigma>ls')),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
              \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
              (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i, toSeqState i (\<Sigma>g', \<Sigma>ls')),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))"  
        using seq1 seq2 by auto     
    } then show ?thesis by auto qed    
    ultimately have 
      "(\<forall>i<length \<sigma>ls. (\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i, toSeqState i (\<sigma>g', \<sigma>ls')),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
                (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i, toSeqState i (\<Sigma>g', \<Sigma>ls')),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))) \<and>
            length \<sigma>ls = length \<sigma>ls' \<and> length \<sigma>ls = length \<Sigma>ls' \<or>
            (\<Gamma>\<^sub>c,(Coms\<^sub>c', \<sigma>g', \<sigma>ls'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Coms\<^sub>s', \<Sigma>g', \<Sigma>ls'),R\<^sub>s,G\<^sub>s)"
    by auto   
  }
  moreover 
  { 
    assume i:"(\<forall>i<length Coms\<^sub>s'. Coms\<^sub>c' ! i = LanguageCon.com.Skip)" and
           c_not_empty: "Coms\<^sub>c' \<noteq> []"
    have  sim:"\<forall>i<length Coms\<^sub>s'. 
           (\<Gamma>\<^sub>c, (Coms\<^sub>c ! i,toSeqState i \<sigma>),Seq_rel i (Rels\<^sub>c !i), Seq_rel i (Guas\<^sub>c!i)) 
                 \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>) 
       (\<Gamma>\<^sub>s,(Coms\<^sub>s! i,toSeqState i \<Sigma>),Seq_rel i (Rels\<^sub>s!i), Seq_rel i (Guas\<^sub>s !i))" sorry
    have "\<exists>ab bb.
              (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
              ((\<sigma>g, \<sigma>ls), ab, bb) \<in> \<gamma>\<^sub>n \<and>
              \<gamma>\<^sub>n \<subseteq> \<alpha> \<and>
              (\<exists>c\<^sub>s'.
                  \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', ab, bb) \<and>
                  (\<forall>i<length c\<^sub>s'. c\<^sub>s' ! i = LanguageCon.com.Skip) \<and> c\<^sub>s' \<noteq> [])"
      sorry
  }
  moreover 
  { 
    assume i:"throw_program Coms\<^sub>c'" 
    have "\<exists>ab bb.
              (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
              ((\<sigma>g, \<sigma>ls), ab, bb) \<in> \<gamma>\<^sub>a \<and>
              \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
              (\<exists>c\<^sub>s'.
                  \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', ab, bb) \<and> throw_program c\<^sub>s')"
      sorry
  }
  moreover 
  { 
    assume i:"final_error Coms\<^sub>c'" 
    have "\<exists>ab bb.
              (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>              
              (\<exists>c\<^sub>s'.
                  \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', ab, bb) \<and> final_error_r Coms\<^sub>c' c\<^sub>s')"
      sorry
  }
  ultimately show "((\<sigma>g, \<sigma>ls), \<Sigma>g, \<Sigma>ls) \<in> \<alpha> \<and>
        (\<forall>c\<^sub>c' a b.
            (\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>\<tau> (Coms\<^sub>c', \<sigma>g, \<sigma>ls) \<rightarrow> (c\<^sub>c', a, b)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', aa, ba) \<and>
                ((a, b), aa, ba) \<in> \<alpha> \<and>
                (((\<sigma>g, \<sigma>ls), a, b), (\<Sigma>g, \<Sigma>ls), aa, ba) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                ((\<forall>i<length \<sigma>ls.
                     (\<Gamma>\<^sub>c,(c\<^sub>c' ! i,
                            toSeqState i (a, b)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                     \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
                     (\<Gamma>\<^sub>s,(c\<^sub>s' ! i,
                            toSeqState i
                             (aa, ba)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))) \<and>
                 length Coms\<^sub>s' = length c\<^sub>s' \<and>
                 length Coms\<^sub>s' = length c\<^sub>c' \<and>
                 length \<sigma>ls = length b \<and> length \<sigma>ls = length ba \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', a, b),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', aa, ba),R\<^sub>s,G\<^sub>s)))) \<and>
        (\<forall>v c\<^sub>c' a b.
            (\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>(Some v) (Coms\<^sub>c', \<sigma>g, \<sigma>ls) \<rightarrow> (c\<^sub>c', a, b)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                (\<exists>a ab b.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                    (\<exists>ac ad bb.
                        (\<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>(Some v) (a, ab, b) \<rightarrow> (ac, ad, bb)) \<and>
                        \<Gamma>\<^sub>s\<turnstile>\<^sub>p (ac, ad, bb) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', aa, ba))) \<and>
                ((a, b), aa, ba) \<in> \<alpha> \<and>
                (((\<sigma>g, \<sigma>ls), a, b), (\<Sigma>g, \<Sigma>ls), aa, ba) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                ((\<forall>i<length \<sigma>ls.
                     (\<Gamma>\<^sub>c,(c\<^sub>c' ! i,
                            toSeqState i (a, b)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                     \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
                     (\<Gamma>\<^sub>s,(c\<^sub>s' ! i,
                            toSeqState i
                             (aa, ba)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))) \<and>
                 length Coms\<^sub>s' = length c\<^sub>s' \<and>
                 length Coms\<^sub>s' = length c\<^sub>c' \<and>
                 length \<sigma>ls = length b \<and> length \<sigma>ls = length ba \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', a, b),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                 (\<Gamma>\<^sub>s,(c\<^sub>s', aa, ba),R\<^sub>s,G\<^sub>s)))) \<and>
        (\<forall>a b aa ba.
            (((\<sigma>g, \<sigma>ls), a, b), (\<Sigma>g, \<Sigma>ls), aa, ba) \<in> ((R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<longrightarrow>
            (\<forall>i<length \<sigma>ls.
                (\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i,
                       toSeqState i (a, b)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
                (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i,
                       toSeqState i (aa, ba)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))) \<and>
            length \<sigma>ls = length b \<and> length \<sigma>ls = length ba \<or>
            (\<Gamma>\<^sub>c,(Coms\<^sub>c', a, b),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
            (\<Gamma>\<^sub>s,(Coms\<^sub>s', aa, ba),R\<^sub>s,G\<^sub>s)) \<and>
        ((\<forall>i<length Coms\<^sub>s'. Coms\<^sub>c' ! i = LanguageCon.com.Skip) \<and> Coms\<^sub>c' \<noteq> [] \<longrightarrow>
         (\<exists>a b. (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), a, b) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                ((\<sigma>g, \<sigma>ls), a, b) \<in> \<gamma>\<^sub>n \<and>
                \<gamma>\<^sub>n \<subseteq> \<alpha> \<and>
                (\<exists>c\<^sub>s'.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', a, b) \<and>
                    (\<forall>i<length c\<^sub>s'. c\<^sub>s' ! i = LanguageCon.com.Skip) \<and> c\<^sub>s' \<noteq> []))) \<and>
        (throw_program Coms\<^sub>c' \<longrightarrow>
         (\<exists>a b. (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), a, b) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                ((\<sigma>g, \<sigma>ls), a, b) \<in> \<gamma>\<^sub>a \<and>
                \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
                (\<exists>c\<^sub>s'.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', a, b) \<and> throw_program c\<^sub>s'))) \<and>
        (final_error Coms\<^sub>c' \<longrightarrow>
         (\<exists>a b. (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), a, b) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                (\<exists>c\<^sub>s'.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', a, b) \<and>
                    final_error_r Coms\<^sub>c' c\<^sub>s')))" by auto
    assume b01:"s\<^sub>c' = Normal \<sigma>n \<and> (\<forall>i<length Coms\<^sub>s'. Coms\<^sub>c' ! i = LanguageCon.com.Skip) \<and> Coms\<^sub>c' \<noteq> []"
    then obtain ns\<^sub>c where nsc:"s\<^sub>c' = Normal ns\<^sub>c" and eq_\<alpha>:"\<sigma>n = ns\<^sub>c" by auto
    then obtain ns\<^sub>s where nss:"s\<^sub>s' =Normal ns\<^sub>s" using alpha  Normal_alpha by fastforce
    have len_com:"0 < length Coms\<^sub>s'" using a0''' a01'' by auto
    have skips:\<open>\<forall>i<length Coms\<^sub>c'. Coms\<^sub>c' ! i = LanguageCon.com.Skip\<close>
      by (simp add: a0'' b01)
    have len_coms:"length Coms\<^sub>s' = length Coms\<^sub>c' \<and> length Coms\<^sub>s' = length Rels\<^sub>c"
      by (simp add: a0'' a01'')
    have relc:"\<forall>i<length Rels\<^sub>c.
       R\<^sub>c \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. (Guas\<^sub>c ! j))
       \<subseteq> (Rels\<^sub>c ! i)" using a0 by auto
    have rels:"\<forall>i<length Rels\<^sub>s.
       R\<^sub>s \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. (Guas\<^sub>s ! j))
       \<subseteq> (Rels\<^sub>s ! i)" using a0 a0' by auto
     have "\<exists>\<Sigma>n'. (((Normal \<sigma>n, Normal \<sigma>n), s\<^sub>s', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                     (\<sigma>n, \<Sigma>n') \<in> \<gamma>\<^sub>n \<and>
                     \<gamma>\<^sub>n \<subseteq> \<alpha> \<and>
                     (\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', s\<^sub>s') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
                             (\<forall>i<length c\<^sub>s'. c\<^sub>s' ! i = LanguageCon.com.Skip) \<and> c\<^sub>s' \<noteq> [])"
       using par_all_skip_rtran_gen1[OF a5 len_com skips nsc nss len_coms a0' a1  a2 a8 a9 relc rels] a3 a4 a10 a11
       nsc eq_\<alpha>
      by (meson G_comp1 a1 a2 subsetCE) 
  }
 moreover 
 {fix \<sigma>n
   assume b01:"s\<^sub>c' = Normal \<sigma>n \<and> final_c (Coms\<^sub>c', s\<^sub>c') \<and> (\<exists>i<length Coms\<^sub>s'. Coms\<^sub>c' ! i = LanguageCon.com.Throw) "      
   then obtain ns\<^sub>s where nss:"s\<^sub>s' =Normal ns\<^sub>s" using alpha  Normal_alpha by fastforce
   have final_throw:"final_c (Coms\<^sub>c', s\<^sub>c') \<and> (\<exists>i<length Coms\<^sub>c'. Coms\<^sub>c' ! i = LanguageCon.com.Throw)" 
     using b01 a0'' by auto
  have len_com:"0 < length Coms\<^sub>s'" using a0''' a01'' by auto      
  have len_coms:"length Coms\<^sub>s' = length Coms\<^sub>c' \<and> length Coms\<^sub>s' = length Rels\<^sub>c"
    by (simp add: a0'' a01'')
  have relc:"\<forall>i<length Rels\<^sub>c.
         R\<^sub>c \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. (Guas\<^sub>c ! j)) \<subseteq> (Rels\<^sub>c ! i)" using a0 by auto
  have rels:"\<forall>i<length Rels\<^sub>s.
             R\<^sub>s \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. (Guas\<^sub>s ! j)) \<subseteq> (Rels\<^sub>s ! i)" using a0 a0' by auto
  have"\<exists>\<Sigma>n'. (((Normal \<sigma>n, Normal \<sigma>n), s\<^sub>s', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                     (\<sigma>n, \<Sigma>n') \<in> \<gamma>\<^sub>a \<and>
                     \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
                     (\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', s\<^sub>s') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
                             final_c (c\<^sub>s', Normal \<Sigma>n') \<and>
                             (\<exists>i<length c\<^sub>s'. c\<^sub>s' ! i = LanguageCon.com.Throw))" 
    using par_throw_rtran_gen1[OF a5 len_com final_throw _ nss len_coms a0' a1 a2 a8 a9 relc rels, of \<sigma>n] a3 a4 a10 a11
      b01 by (meson G_comp1 a1 a2 subsetCE) 
   }  
 moreover 
 {
  assume b01:"(\<forall>\<sigma>n. s\<^sub>c' \<noteq> Normal \<sigma>n) \<and> (\<forall>i<length Coms\<^sub>s'. Coms\<^sub>c' ! i = LanguageCon.com.Skip) \<and> Coms\<^sub>c' \<noteq> [] "      
  then have nss:"\<forall>\<Sigma>n. s\<^sub>s' \<noteq> Normal \<Sigma>n" using alpha  Normal_alpha
    using Normal_alpha2 by fastforce
  have "Coms\<^sub>s' \<noteq> []" using a0'' b01 by auto
  then have"\<exists>\<Sigma>' c\<^sub>s'.
        \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', s\<^sub>s') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<and>
        (s\<^sub>c', \<Sigma>') \<in> \<alpha>\<^sub>x \<and> (\<forall>i<length c\<^sub>s'. c\<^sub>s' ! i = LanguageCon.com.Skip) \<and> c\<^sub>s' \<noteq> []" 
    using par_step_tau_skip_s[OF nss] alpha  by blast
   }      
  ultimately show show "((\<sigma>g, \<sigma>ls), \<Sigma>g, \<Sigma>ls) \<in> \<alpha> \<and>
        (\<forall>c\<^sub>c' a b.
            (\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>\<tau> (Coms\<^sub>c', \<sigma>g, \<sigma>ls) \<rightarrow> (c\<^sub>c', a, b)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', aa, ba) \<and>
                ((a, b), aa, ba) \<in> \<alpha> \<and>
                (((\<sigma>g, \<sigma>ls), a, b), (\<Sigma>g, \<Sigma>ls), aa, ba) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                ((\<forall>i<length \<sigma>ls.
                     (\<Gamma>\<^sub>c,(c\<^sub>c' ! i,
                            toSeqState i (a, b)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                     \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
                     (\<Gamma>\<^sub>s,(c\<^sub>s' ! i,
                            toSeqState i
                             (aa, ba)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))) \<and>
                 length Coms\<^sub>s' = length c\<^sub>s' \<and>
                 length Coms\<^sub>s' = length c\<^sub>c' \<and>
                 length \<sigma>ls = length b \<and> length \<sigma>ls = length ba \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', a, b),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', aa, ba),R\<^sub>s,G\<^sub>s)))) \<and>
        (\<forall>v c\<^sub>c' a b.
            (\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>(Some v) (Coms\<^sub>c', \<sigma>g, \<sigma>ls) \<rightarrow> (c\<^sub>c', a, b)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                (\<exists>a ab b.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                    (\<exists>ac ad bb.
                        (\<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>(Some v) (a, ab, b) \<rightarrow> (ac, ad, bb)) \<and>
                        \<Gamma>\<^sub>s\<turnstile>\<^sub>p (ac, ad, bb) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', aa, ba))) \<and>
                ((a, b), aa, ba) \<in> \<alpha> \<and>
                (((\<sigma>g, \<sigma>ls), a, b), (\<Sigma>g, \<Sigma>ls), aa, ba) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                ((\<forall>i<length \<sigma>ls.
                     (\<Gamma>\<^sub>c,(c\<^sub>c' ! i,
                            toSeqState i (a, b)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                     \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
                     (\<Gamma>\<^sub>s,(c\<^sub>s' ! i,
                            toSeqState i
                             (aa, ba)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))) \<and>
                 length Coms\<^sub>s' = length c\<^sub>s' \<and>
                 length Coms\<^sub>s' = length c\<^sub>c' \<and>
                 length \<sigma>ls = length b \<and> length \<sigma>ls = length ba \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', a, b),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                 (\<Gamma>\<^sub>s,(c\<^sub>s', aa, ba),R\<^sub>s,G\<^sub>s)))) \<and>
        (\<forall>a b aa ba.
            (((\<sigma>g, \<sigma>ls), a, b), (\<Sigma>g, \<Sigma>ls), aa, ba) \<in> ((R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<longrightarrow>
            (\<forall>i<length \<sigma>ls.
                (\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i,
                       toSeqState i (a, b)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
                (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i,
                       toSeqState i (aa, ba)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))) \<and>
            length \<sigma>ls = length b \<and> length \<sigma>ls = length ba \<or>
            (\<Gamma>\<^sub>c,(Coms\<^sub>c', a, b),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
            (\<Gamma>\<^sub>s,(Coms\<^sub>s', aa, ba),R\<^sub>s,G\<^sub>s)) \<and>
        ((\<forall>i<length Coms\<^sub>s'. Coms\<^sub>c' ! i = LanguageCon.com.Skip) \<and> Coms\<^sub>c' \<noteq> [] \<longrightarrow>
         (\<exists>a b. (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), a, b) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                ((\<sigma>g, \<sigma>ls), a, b) \<in> \<gamma>\<^sub>n \<and>
                \<gamma>\<^sub>n \<subseteq> \<alpha> \<and>
                (\<exists>c\<^sub>s'.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', a, b) \<and>
                    (\<forall>i<length c\<^sub>s'. c\<^sub>s' ! i = LanguageCon.com.Skip) \<and> c\<^sub>s' \<noteq> []))) \<and>
        (throw_program Coms\<^sub>c' \<longrightarrow>
         (\<exists>a b. (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), a, b) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                ((\<sigma>g, \<sigma>ls), a, b) \<in> \<gamma>\<^sub>a \<and>
                \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
                (\<exists>c\<^sub>s'.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', a, b) \<and> throw_program c\<^sub>s'))) \<and>
        (final_error Coms\<^sub>c' \<longrightarrow>
         (\<exists>a b. (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), a, b) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                (\<exists>c\<^sub>s'.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', a, b) \<and>
                    final_error_r Coms\<^sub>c' c\<^sub>s')))"
    by force
qed
  
lemma sim_comp_sound:
  assumes a0':"length C>0" and
 a0:"\<forall>i<length C.
       R\<^sub>c \<union> (\<Union>j\<in>{j. j < length C \<and> j \<noteq> i}. (Gua\<^sub>c (C ! j)))
       \<subseteq> (Rel\<^sub>c (C ! i)) \<and>
       R\<^sub>s \<union> (\<Union>j\<in>{j. j < length C \<and> j \<noteq> i}. (Gua\<^sub>s (C ! j)))
       \<subseteq> (Rel\<^sub>s (C ! i))" and
 a1:" (\<Union>j<length C. (Gua\<^sub>c (C ! j))) \<subseteq> G\<^sub>c" and 
 a2:" (\<Union>j<length C. (Gua\<^sub>s (C ! j))) \<subseteq> G\<^sub>s" and             
 a3:" (\<Inter>i<length C.  (PostQ (C ! i))) \<subseteq> \<gamma>\<^sub>n" and 
 a4:" (\<Union>i<length C.  (PostA (C ! i))) \<subseteq> \<gamma>\<^sub>a " and 
 a5:" \<forall>i<length C.                                                    
      \<forall>\<gamma>\<^sub>n \<gamma>\<^sub>a. \<gamma>\<^sub>n = Seq_rel i (PostQ (C !i)) \<and> \<gamma>\<^sub>a = Seq_rel i (PostA (C!i)) \<longrightarrow>
     (\<Gamma>\<^sub>c, (Com\<^sub>c (C! i),toSeqState i \<sigma>),Seq_rel i (Rel\<^sub>c (C!i)), Seq_rel i (Gua\<^sub>c (C!i)))
       \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) 
     (\<Gamma>\<^sub>s,(Com\<^sub>s (C! i),toSeqState i s\<^sub>s),Seq_rel i (Rel\<^sub>s (C!i)), Seq_rel i (Gua\<^sub>s (C!i)))" and  
 a8:"\<forall>i<length C.
       Sta\<^sub>s (Seq_rel i (PostA (C ! i))) (Seq_rel i (Rel\<^sub>c (C ! i)), Seq_rel i((Rel\<^sub>s (C ! i))\<^sup>*))\<^sub>(Seq_rel i \<alpha>)" and
 a9:"\<forall>i<length C.
       Sta\<^sub>s (Seq_rel i (PostQ (C ! i))) (Seq_rel i (Rel\<^sub>c (C ! i)), Seq_rel i((Rel\<^sub>s (C ! i))\<^sup>*))\<^sub>(Seq_rel i \<alpha>)" and 
 a10:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a11:"\<gamma>\<^sub>a \<subseteq> \<alpha>"  and 
 a12:"\<forall>i<length C. \<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>)\<in> ((Gua\<^sub>c (C ! i)))" and
 a13:"length C = length (snd \<sigma>)" and a14:"length C = length (snd s\<^sub>s)" and 
 a15:"R_wf (length C) \<alpha>" and a16:"R_wf (length C) G\<^sub>c" and a17:"R_wf (length C) G\<^sub>s" and
 a20:"\<forall>i<length C. R_wf (length C) (Rel\<^sub>s (C!i))" and
 a21:"\<forall>i<length C. R_wf (length C) (Rel\<^sub>c (C!i))"

shows "(\<Gamma>\<^sub>c,(PCom\<^sub>c C,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(PCom\<^sub>s C,s\<^sub>s),R\<^sub>s,G\<^sub>s)"
proof-
  let ?Rels\<^sub>c = "par_sim_list Rel\<^sub>c C" and
      ?Rels\<^sub>s = "par_sim_list Rel\<^sub>s C" and
      ?Guas\<^sub>c = "par_sim_list Gua\<^sub>c C" and
      ?Guas\<^sub>s = "par_sim_list Gua\<^sub>s C" and
      ?PostsQ = "par_sim_list PostQ C" and
      ?PostsA = "par_sim_list PostA C" and
      ?Coms\<^sub>c = "par_sim_list Com\<^sub>c C" and
      ?Coms\<^sub>s = "par_sim_list Com\<^sub>s C"
      
  have a0'': "length ?Rels\<^sub>c = length ?Guas\<^sub>c \<and> length ?Rels\<^sub>c = length ?PostsQ \<and> length ?Rels\<^sub>c = length ?PostsA \<and>
         length ?Rels\<^sub>c = length ?Guas\<^sub>s \<and> length ?Rels\<^sub>c = length ?Rels\<^sub>s" unfolding par_sim_list_def by auto
  have a01'':"length ?Rels\<^sub>c = length ?Coms\<^sub>s \<and> length ?Rels\<^sub>c = length ?Coms\<^sub>c"  unfolding par_sim_list_def by auto
  have a0''':"length ?Rels\<^sub>c>0" using a0' unfolding par_sim_list_def by auto
  have a0':"\<forall>i<length ?Rels\<^sub>c.
       R\<^sub>c \<union> (\<Union>j\<in>{j. j < length ?Guas\<^sub>c \<and> j \<noteq> i}. (?Guas\<^sub>c ! j))
       \<subseteq> (?Rels\<^sub>c ! i) \<and>
       R\<^sub>s \<union> (\<Union>j\<in>{j. j < length ?Guas\<^sub>s \<and> j \<noteq> i}. (?Guas\<^sub>s ! j))
       \<subseteq> (?Rels\<^sub>s!i)" using a0 unfolding par_sim_list_def Gua\<^sub>c_def Rel\<^sub>c_def by auto  
  have a1':"(\<Union>j<length ?Guas\<^sub>c. (?Guas\<^sub>c !j)) \<subseteq> G\<^sub>c" 
    using a1 unfolding par_sim_list_def Gua\<^sub>c_def  by auto
  have a2':" (\<Union>j<length ?Guas\<^sub>s. (?Guas\<^sub>s ! j)) \<subseteq> G\<^sub>s"      
     using a2 unfolding par_sim_list_def Gua\<^sub>s_def  by auto
  have a3':" (\<Inter>i<length ?PostsQ.  (?PostsQ ! i)) \<subseteq> \<gamma>\<^sub>n" 
     using a3 unfolding par_sim_list_def PostQ_def by auto
  have a4':" (\<Union>i<length ?PostsA.  (?PostsA ! i)) \<subseteq> \<gamma>\<^sub>a " 
    using a4 unfolding par_sim_list_def PostA_def by auto  
  have a5':" \<forall>i<length ?PostsQ.                                                          
     (\<Gamma>\<^sub>c, (?Coms\<^sub>c ! i,toSeqState i \<sigma>),Seq_rel i (?Rels\<^sub>c !i), Seq_rel i (?Guas\<^sub>c!i)) 
        \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i ?PostsQ\<^sub>;\<^sub>xx i ?PostsA\<^sub>) 
     (\<Gamma>\<^sub>s,(?Coms\<^sub>s! i,toSeqState i s\<^sub>s),Seq_rel i (?Rels\<^sub>s!i), Seq_rel i (?Guas\<^sub>s !i))"
    using a5 unfolding par_sim_list_def xx_def by auto
  have a8':"\<forall>i<length ?PostsA.
     Sta\<^sub>s (Seq_rel i (?PostsA ! i)) (Seq_rel i (?Rels\<^sub>c ! i), Seq_rel i ((?Rels\<^sub>s ! i)\<^sup>*))\<^sub>(Seq_rel i \<alpha>)" 
    using a8  unfolding par_sim_list_def by auto
  have a9':"\<forall>i<length (?PostsQ).
     Sta\<^sub>s (Seq_rel i (?PostsQ ! i)) (Seq_rel i  (?Rels\<^sub>c ! i),Seq_rel i  ((?Rels\<^sub>s ! i)\<^sup>*))\<^sub>(Seq_rel i \<alpha>)"
    using a9  unfolding par_sim_list_def by auto
  have a12': "\<forall>i<length ?PostsQ. \<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>)\<in> ((?Guas\<^sub>c ! i))" 
    using a12 unfolding par_sim_list_def by auto
  have a13: "length ?PostsQ = length (snd \<sigma>)" using a13 unfolding par_sim_list_def by auto
  have a14: "length ?PostsQ = length (snd s\<^sub>s)" using a14 unfolding par_sim_list_def by auto  
  have a15:"R_wf (length ?PostsQ) \<alpha>" using a15 unfolding par_sim_list_def by auto
  have a16:"R_wf (length ?PostsQ) G\<^sub>c" using a16 unfolding par_sim_list_def by auto
  have a17:"R_wf (length ?PostsQ) G\<^sub>s" using a17 unfolding par_sim_list_def by auto
  have a18:"\<forall>i<length ?PostsQ. R_wf (length ?PostsQ) (?Rels\<^sub>s!i)" using a20 
    unfolding par_sim_list_def by auto
  have a19:"\<forall>i<length ?PostsQ. R_wf (length ?PostsQ) (?Rels\<^sub>c!i)" using a21 
    unfolding par_sim_list_def by auto
  have "(\<Gamma>\<^sub>c,(?Coms\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(?Coms\<^sub>s,s\<^sub>s),R\<^sub>s,G\<^sub>s)" 
    using sim_comp_sound1[OF a0'' a01'' a0''' a0' a1' a2' a3' a4' a5'  a8' a9' 
                             a10 a11 a12' a13 a14 a15 a16 a17 a18 a19]  
  by auto
thus ?thesis unfolding PCom\<^sub>c_def PCom\<^sub>s_def par_sim_list_def by auto
qed
  
lemma subset_R_wf: assumes a0:"\<xi> \<subseteq> \<alpha>" and 
              a1:"R_wf (length C) \<alpha>" and a2: "(\<sigma>,\<Sigma>)\<in> \<xi>"
            shows  "length C = length (snd \<sigma>)"
  using a0 a1 a2 unfolding R_wf_def
  by (metis prod.exhaust_sel subsetD)


lemma subset_R_wf1: assumes a0:"0 < length C" and "\<xi> \<subseteq> (\<Inter>i<length C.  (Pre (C ! i)))" and
              a1:"\<forall>i<length C. R_wf (length C) (Pre (C!i))" and a2: "(\<sigma>,\<Sigma>)\<in> \<xi>"
            shows  "length C = length (snd \<sigma>)"
  using a0 a1 a2 unfolding R_wf_def
 proof -
  have "(\<sigma>, \<Sigma>) \<in> Sim_Rules.Pre (C ! 0)"
    using a0 a2 assms(2) by auto
  then show ?thesis
    by (meson a0 a1 order.order_iff_strict subset_R_wf)
qed


lemma subset_R_wf2: assumes a0:"0 < length C" and "\<xi> \<subseteq> (\<Inter>i<length C.  (Pre (C ! i)))" and
              a1:"\<forall>i<length C. R_wf (length C) (Pre (C!i))" and a2: "(\<sigma>,\<Sigma>)\<in> \<xi>"
            shows  "length C = length (snd \<Sigma>)"
  using a0 a1 a2 unfolding R_wf_def
 proof -
  have "(\<sigma>, \<Sigma>) \<in> Sim_Rules.Pre (C ! 0)"
    using a0 a2 assms(2) by auto
  then show ?thesis  by (metis (no_types, hide_lams) R_wf_def a0 a1 prod.exhaust_sel)    
qed

lemma in_seq_rel:"R_wf n \<xi>\<^sub>s \<Longrightarrow>
       ((\<sigma>g, \<sigma>l), \<Sigma>g, \<Sigma>l) \<in> \<xi> \<Longrightarrow> 
       \<xi> \<subseteq> \<xi>\<^sub>s \<Longrightarrow> i < n \<Longrightarrow>
       (toSeqState i  (\<sigma>g, \<sigma>l), toSeqState i (\<Sigma>g,\<Sigma>l)) \<in> Seq_rel i \<xi>\<^sub>s"
  apply (rule par_rel_seq_rel)
  apply blast
  by (metis (no_types) R_wf_def subsetD)+

lemma split_pre_sim: assumes  a0:"\<forall>i<length C.
         \<forall>\<xi> \<gamma>\<^sub>n \<gamma>\<^sub>a.
            \<xi> = Seq_rel i (Pre (C ! i)) \<and>
            \<gamma>\<^sub>n = Seq_rel i (PostQ (C ! i)) \<and> \<gamma>\<^sub>a = Seq_rel i (PostA (C ! i)) \<longrightarrow>
            (\<forall>\<sigma> \<Sigma>. (\<sigma>, \<Sigma>) \<in> \<xi> \<longrightarrow> (\<Gamma>\<^sub>c,(Com\<^sub>c (C ! i), \<sigma>),Seq_rel i (Rel\<^sub>c (C ! i)),Seq_rel i (Gua\<^sub>c (C ! i)))
                    \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                    (\<Gamma>\<^sub>s,(Com\<^sub>s (C ! i), \<Sigma>),Seq_rel i (Rel\<^sub>s (C ! i)),Seq_rel i (Gua\<^sub>s (C ! i))))" and
    a1:"\<forall>i<length C. R_wf (length C) (Pre (C!i)) " and a2:"\<xi> \<subseteq> (\<Inter>i<length C.  (Pre (C ! i)))" and 
    a3:"(\<sigma>,\<Sigma>)\<in>\<xi>" 
  shows "\<forall>i<length C.  \<forall>\<gamma>\<^sub>n \<gamma>\<^sub>a.
         \<gamma>\<^sub>n = Seq_rel i (PostQ (C ! i)) \<and> \<gamma>\<^sub>a = Seq_rel i (PostA (C ! i)) \<longrightarrow>
         (\<Gamma>\<^sub>c,(Com\<^sub>c (C ! i), toSeqState i \<sigma>),Seq_rel i (Rel\<^sub>c (C ! i)),Seq_rel i (Gua\<^sub>c (C ! i)))
         \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
         (\<Gamma>\<^sub>s,(Com\<^sub>s (C ! i), toSeqState i \<Sigma>),Seq_rel i (Rel\<^sub>s (C ! i)),Seq_rel i (Gua\<^sub>s (C ! i)))"
proof-
  {fix i
    let ?p = "(PostQ (C ! i))" let ?q = "(PostA (C ! i))"
    assume "i < length C"
    moreover obtain \<sigma>1 \<sigma>2 \<Sigma>1 \<Sigma>2 where aa:"\<sigma> = (\<sigma>1,\<sigma>2)" and bb:"\<Sigma> = (\<Sigma>1, \<Sigma>2)"
      by moura 
    moreover have "(toSeqState i  (\<sigma>1,\<sigma>2), toSeqState i (\<Sigma>1, \<Sigma>2)) \<in> Seq_rel i (Pre (C!i))"
      using a1 a2 a3 calculation
      by (blast intro: in_seq_rel[of "length C" "Pre (C!i)" \<sigma>1 \<sigma>2 \<Sigma>1 \<Sigma>2 \<xi> i])     
    ultimately have "(\<Gamma>\<^sub>c,(Com\<^sub>c (C ! i), toSeqState i \<sigma>),Seq_rel i (Rel\<^sub>c (C ! i)),Seq_rel i (Gua\<^sub>c (C ! i)))
         \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>Seq_rel i ?p\<^sub>;\<^sub>Seq_rel i ?q\<^sub>)
         (\<Gamma>\<^sub>s,(Com\<^sub>s (C ! i), toSeqState i \<Sigma>),Seq_rel i (Rel\<^sub>s (C ! i)),Seq_rel i (Gua\<^sub>s (C ! i)))" 
      using a0  by fast
          
  } thus ?thesis by auto
qed
 
lemma sim_comp:
  "length C > 0 \<Longrightarrow> 
   \<forall>i<length C.
       R\<^sub>c \<union> (\<Union>j\<in>{j. j < length C \<and> j \<noteq> i}. (Gua\<^sub>c (C ! j)))
       \<subseteq> (Rel\<^sub>c (C ! i)) \<and>
       R\<^sub>s \<union> (\<Union>j\<in>{j. j < length C \<and> j \<noteq> i}. (Gua\<^sub>s (C ! j)))
       \<subseteq> (Rel\<^sub>s (C ! i)) \<Longrightarrow>
    (\<Union>j<length C. (Gua\<^sub>c (C ! j))) \<subseteq> G\<^sub>c \<Longrightarrow>  
    (\<Union>j<length C. (Gua\<^sub>s (C ! j))) \<subseteq> G\<^sub>s \<Longrightarrow>   
     \<xi> \<subseteq> (\<Inter>i<length C.  (Pre (C ! i))) \<Longrightarrow>     
     (\<Inter>i<length C.  (PostQ (C ! i))) \<subseteq> \<gamma>\<^sub>n \<Longrightarrow>
     (\<Union>i<length C.  (PostA (C ! i))) \<subseteq> \<gamma>\<^sub>a \<Longrightarrow>
    \<forall>i<length C.
      \<forall>\<xi> \<gamma>\<^sub>n \<gamma>\<^sub>a. \<xi> = Seq_rel i  (Pre (C !i)) \<and> \<gamma>\<^sub>n = Seq_rel i (PostQ (C !i)) \<and> \<gamma>\<^sub>a = Seq_rel i (PostA (C!i)) \<longrightarrow>
     (\<Gamma>\<^sub>c, Com\<^sub>c (C! i),Seq_rel i (Rel\<^sub>c (C!i)), Seq_rel i (Gua\<^sub>c (C!i))) 
        \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,Com\<^sub>s (C! i),Seq_rel i (Rel\<^sub>s (C!i)), Seq_rel i  (Gua\<^sub>s (C!i))) \<Longrightarrow>
    \<gamma>\<^sub>n \<subseteq> \<alpha> \<Longrightarrow> \<gamma>\<^sub>a \<subseteq> \<alpha> \<Longrightarrow>
   \<forall>i<length C.
       Sta\<^sub>s (Seq_rel i (PostA (C ! i))) (Seq_rel i (Rel\<^sub>c (C ! i)), Seq_rel i((Rel\<^sub>s (C ! i))\<^sup>*))\<^sub>(Seq_rel i \<alpha>) \<Longrightarrow>
   \<forall>i<length C.
       Sta\<^sub>s (Seq_rel i (PostQ (C ! i))) (Seq_rel i (Rel\<^sub>c (C ! i)), Seq_rel i((Rel\<^sub>s (C ! i))\<^sup>*))\<^sub>(Seq_rel i \<alpha>) \<Longrightarrow> 
   \<forall>i<length C. \<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>)\<in> ((Gua\<^sub>c (C ! i))) \<Longrightarrow> R_wf (length C) \<alpha> \<Longrightarrow> R_wf (length C) G\<^sub>c \<Longrightarrow>
   R_wf (length C) G\<^sub>s \<Longrightarrow> \<forall>i<length C. R_wf (length C) (Rel\<^sub>s (C!i)) \<Longrightarrow> \<forall>i<length C. R_wf (length C) (Pre (C!i)) \<Longrightarrow>
   \<forall>i<length C. R_wf (length C) (Rel\<^sub>c (C!i)) \<Longrightarrow>
   (\<Gamma>\<^sub>c,PCom\<^sub>c C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,PCom\<^sub>s C,R\<^sub>s,G\<^sub>s)" 
 unfolding RGSIM_p_pre_def RGSim_pre_def Pre_def
  apply (rule, rule,rule) apply (rule sim_comp_sound) 
        apply fast apply fast apply fast apply fast
               apply fast apply fast apply (rule split_pre_sim[of C \<Gamma>\<^sub>c \<alpha> \<Gamma>\<^sub>s \<xi>, simplified Pre_def], assumption+)
       apply (rule subset_R_wf1[of C \<xi>, simplified Pre_def], assumption+)
  by (rule subset_R_wf2[of C \<xi>, simplified Pre_def], assumption+)

lemma "\<alpha>' \<subseteq> \<alpha> \<Longrightarrow> \<alpha>\<subseteq> \<alpha>\<^sub>x \<Longrightarrow> \<alpha>' \<subseteq> \<alpha>\<^sub>x" by auto


lemma RGSim_Conseq_sound:
assumes  a0:"(\<Gamma>\<^sub>c,(C\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s)" and   
    a1:"\<gamma>\<^sub>n \<subseteq> \<gamma>\<^sub>n\<^sub>' \<and> \<gamma>\<^sub>n\<^sub>' \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>a \<subseteq> \<gamma>\<^sub>a\<^sub>' \<and> \<gamma>\<^sub>a\<^sub>' \<subseteq> \<alpha>" and 
   a3:"R\<^sub>s' \<subseteq> R\<^sub>s" and a4:"R\<^sub>c' \<subseteq> R\<^sub>c" and a5:"G\<^sub>s \<subseteq> G\<^sub>s'" and a6: "G\<^sub>c\<subseteq>G\<^sub>c'"   and a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and a8:"\<forall>\<sigma>.(\<sigma>,\<sigma>)\<in>G\<^sub>c"
 shows "(\<Gamma>\<^sub>c,(C\<^sub>c, \<sigma>),R\<^sub>c',G\<^sub>c') \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>'\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, \<Sigma>),R\<^sub>s',G\<^sub>s')"
  using a0
proof(coinduction arbitrary: C\<^sub>c C\<^sub>s \<sigma> \<Sigma>,clarsimp) 
fix C\<^sub>c' C\<^sub>s' \<sigma>' \<Sigma>'  
  assume a0:"(\<Gamma>\<^sub>c,(C\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)"
  have rg:"\<forall>\<sigma>.(\<sigma>,\<sigma>)\<in>G\<^sub>c'" using a6 a8 by auto
  then have "(\<forall>\<sigma>n. \<sigma>' = Normal \<sigma>n \<longrightarrow> (\<exists>\<Sigma>n. \<Sigma>' = Normal \<Sigma>n \<and> (\<sigma>n, \<Sigma>n) \<in> \<alpha>))"
    using  a0 dest_sim_alpha by blast
  moreover have "(\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x " using dest_sim_alpha_x[OF a0] by auto
  moreover {
    fix c\<^sub>c' \<sigma>n'
    assume a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (C\<^sub>c', \<sigma>') \<rightarrow> (c\<^sub>c', Normal \<sigma>n')"
    then obtain c\<^sub>s' \<Sigma>n' where "
       \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
       (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
       (((\<sigma>', Normal \<sigma>n'), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
       (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)" 
    using dest_sim_tau_step[OF a0 a00] by auto
    then have "\<exists>c\<^sub>s' \<Sigma>n'.
               (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n')) \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
               (((\<sigma>', Normal \<sigma>n'), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c', G\<^sub>s'\<^sup>*)\<^sub>\<alpha>) \<and>
               ((\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s) \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c',G\<^sub>c') \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>'\<^sub>)
                (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s',G\<^sub>s'))" using a5 a6
      by (meson G_comp1)
  }
  moreover {
    fix  v c\<^sub>c' \<sigma>n'
    assume a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C\<^sub>c', \<sigma>') \<rightarrow> (c\<^sub>c', Normal \<sigma>n')"
      then have "\<exists>c\<^sub>s' \<Sigma>n'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sup>+ (c\<^sub>s', Normal \<Sigma>n') \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
               (((\<sigma>', Normal \<sigma>n'),  \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)" 
        using dest_sim_ev_step[OF a0 a00] by auto
    then have  "(\<exists>c\<^sub>s' \<Sigma>n'.
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sup>+ (c\<^sub>s', Normal \<Sigma>n') \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
               (((\<sigma>', Normal \<sigma>n'),  \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c', G\<^sub>s'\<^sup>*)\<^sub>\<alpha>) \<and>
               ((\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s) \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c',G\<^sub>c') \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>'\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s',G\<^sub>s')))" using a5 a6
      by (meson G_comp1)
    then have  "\<exists>c\<^sub>s' \<Sigma>n'.
               (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                      (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n'))) \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
               (((\<sigma>', Normal \<sigma>n'), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c', G\<^sub>s'\<^sup>*)\<^sub>\<alpha>) \<and>
               ((\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s) \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c',G\<^sub>c') \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>'\<^sub>)
                (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s',G\<^sub>s'))" by auto
  }
  moreover{
    fix \<sigma>'' \<Sigma>''
    assume a00:"(((\<sigma>', \<sigma>''), \<Sigma>', \<Sigma>'') \<in> (R\<^sub>c', R\<^sub>s'\<^sup>*)\<^sub>\<alpha>) \<and> (\<sigma>'', \<Sigma>'') \<in> \<alpha>\<^sub>x"   
    then have a00:"((\<sigma>', \<sigma>''), \<Sigma>', \<Sigma>'') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and> (\<sigma>'',\<Sigma>'')\<in>\<alpha>\<^sub>x" 
      using a3 a4  by (meson G_comp1)    
    have "(\<Gamma>\<^sub>c,(C\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s) \<or>
                 (\<Gamma>\<^sub>c,(C\<^sub>c', \<sigma>''),R\<^sub>c',G\<^sub>c') \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>'\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>''),R\<^sub>s',G\<^sub>s')" 
      using dest_sim_env_step[OF a0 a00] by auto    
    then have "(\<Gamma>\<^sub>c,(C\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s) \<or>
           (\<Gamma>\<^sub>c,(C\<^sub>c', \<sigma>''),R\<^sub>c',G\<^sub>c') \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>'\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>''),R\<^sub>s',G\<^sub>s')"  by auto
  }
  moreover{   
    fix \<sigma>n
    assume "C\<^sub>c' = LanguageCon.com.Skip \<and> \<sigma>' = Normal \<sigma>n"
    then have a0:"(\<Gamma>\<^sub>c,(Skip,Normal \<sigma>n),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)"         
      using a0 by auto
    then have "\<exists>\<Sigma>n'. ((Normal \<sigma>n, Normal \<sigma>n), \<Sigma>', Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<sigma>n, \<Sigma>n') \<in> \<gamma>\<^sub>n \<and>
             \<gamma>\<^sub>n \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, Normal \<Sigma>n')" 
      using sim_elim_cases_c(1)[OF a0] by fastforce
    then have   "\<exists>\<Sigma>n'. (((Normal \<sigma>n, Normal \<sigma>n), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c', G\<^sub>s'\<^sup>*)\<^sub>\<alpha>) \<and>
                     (\<sigma>n, \<Sigma>n') \<in> \<gamma>\<^sub>n\<^sub>' \<and>
                     \<gamma>\<^sub>n\<^sub>' \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, Normal \<Sigma>n')"
      using  G_comp1  a1 a5 a6 by blast 
  }
  moreover{
    fix \<sigma>n
    assume "C\<^sub>c' = LanguageCon.com.Throw \<and> \<sigma>' = Normal \<sigma>n"
    then have a0:"(\<Gamma>\<^sub>c,(Throw,Normal \<sigma>n),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)" 
        using a0 by fastforce
    then have "\<exists>\<Sigma>n'. ((Normal \<sigma>n, Normal \<sigma>n),  \<Sigma>', Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<sigma>n, \<Sigma>n') \<in> \<gamma>\<^sub>a \<and>
             \<gamma>\<^sub>a \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, Normal \<Sigma>n')"  
      using  sim_elim_cases_c(2)[OF a0] by fastforce
    then have "\<exists>\<Sigma>n'. ((Normal \<sigma>n, Normal \<sigma>n), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c', G\<^sub>s'\<^sup>*)\<^sub>\<alpha> \<and>
                     (\<sigma>n, \<Sigma>n') \<in> \<gamma>\<^sub>a\<^sub>' \<and>
                     \<gamma>\<^sub>a\<^sub>' \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Throw, Normal \<Sigma>n')"
     using  G_comp1  a2 a5 a6 by blast 
  }
  moreover{
    fix c\<^sub>c' \<sigma>'' e
    assume sigma:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (C\<^sub>c', \<sigma>') \<rightarrow> (c\<^sub>c', \<sigma>'') \<and> (\<forall>\<sigma>n. \<sigma>'' \<noteq> Normal \<sigma>n) "        
    then have "\<exists>\<Sigma>'' c\<^sub>s'. (\<sigma>'',\<Sigma>'')\<in>\<alpha>\<^sub>x \<and> (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'')  \<or> 
               (\<exists>v. e = Some v \<and>  \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sup>+ (c\<^sub>s',\<Sigma>'') )) \<and> (\<sigma>', \<sigma>'') \<in> G\<^sub>c "
      using dest_sim_ev_step_not_normal[OF a0,of e c\<^sub>c' \<sigma>''] by fast
    then obtain \<Sigma>'' c\<^sub>s' where alpha:"(\<sigma>'',\<Sigma>'')\<in>\<alpha>\<^sub>x " and  
           "(\<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'') \<or>
            (\<exists>v. e = Some v \<and>
                 (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                        (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>''))))) \<and> (\<sigma>', \<sigma>'') \<in> G\<^sub>c' " using a6
      by fastforce+
    moreover have "(\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>''),R\<^sub>c',G\<^sub>c') \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>'\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>''),R\<^sub>s',G\<^sub>s')"          
      by (meson a3 a4 a7 rg alpha sigma sim_not_normal subset_trans)
    ultimately have "\<exists>\<Sigma>''. (\<sigma>'', \<Sigma>'') \<in> \<alpha>\<^sub>x \<and>
                   (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'') \<or>
                            (\<exists>v. e = Some v \<and>
                                 (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                                        (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, b) \<rightarrow> (aa, ba) \<and>
                                                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>''))))) \<and> 
                           (\<sigma>', \<sigma>'') \<in> G\<^sub>c' \<and>
                           ((\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s) \<or>
                            (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>''),R\<^sub>c',G\<^sub>c') \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>'\<^sub>)
                            (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>''),R\<^sub>s',G\<^sub>s')))" 
      by fast
  }
  moreover {
    assume a00:"(\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n) \<and> C\<^sub>c' = LanguageCon.com.Skip"
    then have "(\<exists>\<Sigma>''. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, \<Sigma>'') \<and> (\<sigma>', \<Sigma>'') \<in> \<alpha>\<^sub>x)"
       by (fastforce intro:sim_elim_cases[OF a0 ])      
  }
  ultimately show "(\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x \<and>
       (\<forall>\<sigma>n. \<sigma>' = Normal \<sigma>n \<longrightarrow> (\<exists>\<Sigma>n. \<Sigma>' = Normal \<Sigma>n \<and> (\<sigma>n, \<Sigma>n) \<in> \<alpha>)) \<and>
       (\<forall>c\<^sub>c' \<sigma>n'.
           (\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (C\<^sub>c', \<sigma>') \<rightarrow> (c\<^sub>c', Normal \<sigma>n')) \<longrightarrow>
           (\<exists>c\<^sub>s' \<Sigma>n'.
               (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n')) \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
               (((\<sigma>', Normal \<sigma>n'), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c', G\<^sub>s'\<^sup>*)\<^sub>\<alpha>) \<and>
               ((\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s) \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c',G\<^sub>c') \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>'\<^sub>)
                (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s',G\<^sub>s')))) \<and>
       (\<forall>v c\<^sub>c' \<sigma>n'.
           (\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C\<^sub>c', \<sigma>') \<rightarrow> (c\<^sub>c', Normal \<sigma>n')) \<longrightarrow>
           (\<exists>c\<^sub>s' \<Sigma>n'.
               (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                      (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n'))) \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
               (((\<sigma>', Normal \<sigma>n'), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c', G\<^sub>s'\<^sup>*)\<^sub>\<alpha>) \<and>
               ((\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s) \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c',G\<^sub>c') \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>'\<^sub>)
                (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s',G\<^sub>s')))) \<and>
       (\<forall>\<sigma>'' \<Sigma>''.
           (((\<sigma>', \<sigma>''), \<Sigma>', \<Sigma>'') \<in> (R\<^sub>c', R\<^sub>s'\<^sup>*)\<^sub>\<alpha>) \<and> (\<sigma>'', \<Sigma>'') \<in> \<alpha>\<^sub>x \<longrightarrow>
           (\<Gamma>\<^sub>c,(C\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s) \<or>
           (\<Gamma>\<^sub>c,(C\<^sub>c', \<sigma>''),R\<^sub>c',G\<^sub>c') \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>'\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>''),R\<^sub>s',G\<^sub>s')) \<and>
       (\<forall>\<sigma>n. C\<^sub>c' = LanguageCon.com.Skip \<and> \<sigma>' = Normal \<sigma>n \<longrightarrow>
             (\<exists>\<Sigma>n'. ((Normal \<sigma>n, Normal \<sigma>n), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c', G\<^sub>s'\<^sup>*)\<^sub>\<alpha> \<and>
                     (\<sigma>n, \<Sigma>n') \<in> \<gamma>\<^sub>n\<^sub>' \<and>
                     \<gamma>\<^sub>n\<^sub>' \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, Normal \<Sigma>n'))) \<and>
       (\<forall>\<sigma>n. C\<^sub>c' = LanguageCon.com.Throw \<and> \<sigma>' = Normal \<sigma>n \<longrightarrow>
             (\<exists>\<Sigma>n'. ((Normal \<sigma>n, Normal \<sigma>n), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c', G\<^sub>s'\<^sup>*)\<^sub>\<alpha> \<and>
                     (\<sigma>n, \<Sigma>n') \<in> \<gamma>\<^sub>a\<^sub>' \<and>
                     \<gamma>\<^sub>a\<^sub>' \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Throw, Normal \<Sigma>n'))) \<and>
       (\<forall>\<sigma>'' c\<^sub>c' e.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (C\<^sub>c', \<sigma>') \<rightarrow> (c\<^sub>c', \<sigma>'') \<and> (\<forall>\<sigma>n. \<sigma>'' \<noteq> Normal \<sigma>n) \<longrightarrow>
           (\<exists>\<Sigma>''. (\<sigma>'', \<Sigma>'') \<in> \<alpha>\<^sub>x \<and>
                   (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'') \<or>
                            (\<exists>v. e = Some v \<and>
                                 (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                                        (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, b) \<rightarrow> (aa, ba) \<and>
                                                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>''))))) \<and> (\<sigma>', \<sigma>'') \<in> G\<^sub>c' \<and>
                           ((\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s) \<or>
                            (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>''),R\<^sub>c',G\<^sub>c') \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>'\<^sub>)
                            (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>''),R\<^sub>s',G\<^sub>s'))))) \<and>
       ((\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n) \<and> C\<^sub>c' = LanguageCon.com.Skip \<longrightarrow>
        (\<exists>\<Sigma>''. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, \<Sigma>'') \<and> (\<sigma>', \<Sigma>'') \<in> \<alpha>\<^sub>x))" 
    by auto
qed
  
lemma RGSim_Conseq:
  "\<xi>\<^sub>'\<subseteq>\<xi> \<Longrightarrow>  \<gamma>\<^sub>n \<subseteq> \<gamma>\<^sub>n\<^sub>' \<and> \<gamma>\<^sub>n\<^sub>' \<subseteq> \<alpha> \<Longrightarrow> \<gamma>\<^sub>a \<subseteq> \<gamma>\<^sub>a\<^sub>' \<and> \<gamma>\<^sub>a\<^sub>' \<subseteq> \<alpha> \<Longrightarrow> 
   R\<^sub>s' \<subseteq> R\<^sub>s \<Longrightarrow> R\<^sub>c' \<subseteq> R\<^sub>c \<Longrightarrow> G\<^sub>s \<subseteq> G\<^sub>s' \<Longrightarrow> G\<^sub>c\<subseteq>G\<^sub>c' \<Longrightarrow> R\<^sub>c\<subseteq>1\<alpha>\<^sub>x \<Longrightarrow> \<forall>\<sigma>.(\<sigma>,\<sigma>)\<in>G\<^sub>c \<Longrightarrow>
  (\<Gamma>\<^sub>c,C\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow>
  (\<Gamma>\<^sub>c,C\<^sub>c,R\<^sub>c',G\<^sub>c') \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>'\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>'\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s',G\<^sub>s')"
  unfolding RGSim_pre_def apply (rule,rule,rule)  apply (rule RGSim_Conseq_sound[of \<Gamma>\<^sub>c C\<^sub>c _ R\<^sub>c G\<^sub>c \<alpha> \<gamma>\<^sub>n \<gamma>\<^sub>a])
    by auto    
    

lemma strenrel_sound:
assumes 
   a0:"(\<Gamma>\<^sub>c,(C\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s)" and
   a1:"\<forall>\<sigma>n \<Sigma>n. \<sigma>=Normal \<sigma>n \<and> \<Sigma> = Normal \<Sigma>n \<longrightarrow> (\<sigma>n,\<Sigma>n)\<in>\<alpha>\<^sub>'" and
   a2:"(\<gamma>\<^sub>n \<union> \<gamma>\<^sub>a) \<subseteq> \<alpha>\<^sub>' \<and> \<alpha>\<^sub>' \<subseteq> \<alpha>" and  a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and a8:"\<forall>\<sigma>.(\<sigma>,\<sigma>)\<in>G\<^sub>c" and
   a3:"Sta\<^sub>s \<alpha>\<^sub>' (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>" 
 shows "(\<Gamma>\<^sub>c,(C\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s)"   
   using a0 a1  
 proof (coinduction arbitrary:\<sigma> \<Sigma>  C\<^sub>c C\<^sub>s,clarsimp) 
   fix \<sigma>' \<Sigma>' C\<^sub>c' C\<^sub>s' 
   assume a0:"(\<Gamma>\<^sub>c,(C\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)" and
          a1:"\<forall>\<sigma>n \<Sigma>n. \<sigma>' = Normal \<sigma>n \<and> \<Sigma>' = Normal \<Sigma>n \<longrightarrow> (\<sigma>n, \<Sigma>n) \<in> \<alpha>\<^sub>'"
   have \<alpha>\<^sub>x:"(\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x" using a0
     using dest_sim_alpha_x by blast  
   moreover have " (\<forall>\<sigma>n. \<sigma>' = Normal \<sigma>n \<longrightarrow> (\<exists>\<Sigma>n. \<Sigma>' = Normal \<Sigma>n \<and> (\<sigma>n, \<Sigma>n) \<in> \<alpha>\<^sub>'))" 
     using a1 \<alpha>\<^sub>x Normal_alpha by fastforce
   moreover {
     fix c\<^sub>c' \<sigma>n'
     assume a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (C\<^sub>c', \<sigma>') \<rightarrow> (c\<^sub>c', Normal \<sigma>n')"
     then obtain \<sigma>n \<Sigma>n where \<sigma>n:"\<sigma>' = Normal \<sigma>n" and \<Sigma>n:"\<Sigma>' = Normal \<Sigma>n" using \<alpha>\<^sub>x
       by (metis a0 compe_normal_s'_normal_s dest_sim_alpha)        
     from a00 obtain c\<^sub>s' \<Sigma>n' where step_alpha:"
       \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
       (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
       (((Normal \<sigma>n, Normal \<sigma>n'), Normal \<Sigma>n, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
       (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)" 
    using dest_sim_tau_step[OF a0 a00] \<sigma>n \<Sigma>n by auto     
     have "\<exists>c\<^sub>s' \<Sigma>n'.
            \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha>\<^sub>' \<and>
               (((\<sigma>', Normal \<sigma>n'), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
               ((\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s) \<and>
                (\<sigma>n', \<Sigma>n') \<in> \<alpha>\<^sub>' \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))"
       using a1 a3 step_alpha \<sigma>n \<Sigma>n unfolding Sta\<^sub>s_def related_transitions_def by fast
   }
   moreover{
     fix  v c\<^sub>c' \<sigma>n'
     assume a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C\<^sub>c', \<sigma>') \<rightarrow> (c\<^sub>c', Normal \<sigma>n')"
     then obtain \<sigma>n \<Sigma>n where \<sigma>n:"\<sigma>' = Normal \<sigma>n" and \<Sigma>n:"\<Sigma>' = Normal \<Sigma>n" using \<alpha>\<^sub>x
       by (metis a0 compe_normal_s'_normal_s dest_sim_alpha)
     then obtain c\<^sub>s' \<Sigma>n' where step_alpha:" 
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sup>+ (c\<^sub>s', Normal \<Sigma>n') \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
              (((\<sigma>', Normal \<sigma>n'), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)
       " 
       using dest_sim_ev_step[OF a0 a00] by fast
     have "\<exists>c\<^sub>s' \<Sigma>n'.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sup>+ (c\<^sub>s', Normal \<Sigma>n') \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha>\<^sub>' \<and>
               (((\<sigma>', Normal \<sigma>n'), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
               ((\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s) \<and> (\<sigma>n', \<Sigma>n') \<in> \<alpha>\<^sub>' \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))"
       using a1 a3 step_alpha \<sigma>n \<Sigma>n unfolding Sta\<^sub>s_def related_transitions_def by fast
     then have "(\<exists>c\<^sub>s' \<Sigma>n'.
               (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                      (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n'))) \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha>\<^sub>' \<and>
               (((\<sigma>', Normal \<sigma>n'), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
               ((\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s) \<and>
                (\<sigma>n', \<Sigma>n') \<in> \<alpha>\<^sub>' \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))" by auto
   }
   moreover{
     fix  \<Sigma>'' \<sigma>''  
     assume a00:"(((\<sigma>', \<sigma>''), \<Sigma>', \<Sigma>'') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and> (\<sigma>'', \<Sigma>'') \<in> \<alpha>\<^sub>x"     
     then have a00':"((\<sigma>', \<sigma>''), \<Sigma>', \<Sigma>'') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and> (\<sigma>'',\<Sigma>'')\<in>\<alpha>\<^sub>x" 
       unfolding related_transitions_def using a2 by auto
      have "(\<Gamma>\<^sub>c,(C\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s) " 
        using dest_sim_env_step[OF a0 a00' ] by auto         
      then have "(\<Gamma>\<^sub>c,(C\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s) \<and>
           (\<forall>\<sigma>n \<Sigma>n. \<sigma>'' = Normal \<sigma>n \<and> \<Sigma>'' = Normal \<Sigma>n \<longrightarrow> (\<sigma>n, \<Sigma>n) \<in> \<alpha>\<^sub>') \<or>
           (\<Gamma>\<^sub>c,(C\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s)"
       using a00 unfolding related_transitions_def by auto     
    }
    
    moreover{
      fix \<sigma>n
      assume a00:"C\<^sub>c' = LanguageCon.com.Skip \<and> \<sigma>' = Normal \<sigma>n"
      then obtain \<Sigma>n where \<Sigma>':"\<Sigma>' = Normal \<Sigma>n" using \<alpha>\<^sub>x
        by (meson Normal_alpha)
    then have a0:"(\<Gamma>\<^sub>c,(Skip,Normal \<sigma>n),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', Normal \<Sigma>n),R\<^sub>s,G\<^sub>s)" 
      using a0 a00 by auto
    then obtain \<Sigma>n' where step_alpha:
      "((Normal \<sigma>n, Normal \<sigma>n), Normal \<Sigma>n, Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<sigma>n, \<Sigma>n') \<in> \<gamma>\<^sub>n \<and>
             \<gamma>\<^sub>n \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', Normal \<Sigma>n) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, Normal \<Sigma>n')" 
       by (force elim: sim_elim_cases_c(1))
    then have "(\<sigma>n, \<Sigma>n')\<in> \<alpha>\<^sub>'" using  a1 a3 step_alpha \<Sigma>' a00
      unfolding Sta\<^sub>s_def  by blast   
    then have   "((Normal \<sigma>n, Normal \<sigma>n), Normal \<Sigma>n, Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>')" 
      using   a00 \<Sigma>' a1 step_alpha unfolding related_transitions_def by auto
    then have "\<exists>\<Sigma>n'. ((Normal \<sigma>n, Normal \<sigma>n), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>' \<and>
                     (\<sigma>n, \<Sigma>n') \<in> \<gamma>\<^sub>n \<and>
                     \<gamma>\<^sub>n \<subseteq> \<alpha>\<^sub>' \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, Normal \<Sigma>n')"
      using step_alpha  a2 \<Sigma>' by auto
  }
  moreover{
    fix \<sigma>n
    assume a00:"C\<^sub>c' = LanguageCon.com.Throw \<and> \<sigma>' = Normal \<sigma>n"
   then obtain \<Sigma>n where \<Sigma>':"\<Sigma>' = Normal \<Sigma>n" using \<alpha>\<^sub>x
     by (meson Normal_alpha)
    then have a0:"(\<Gamma>\<^sub>c,(Throw,Normal \<sigma>n),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', Normal \<Sigma>n),R\<^sub>s,G\<^sub>s)" 
      using a0 a00 by auto
    then obtain \<Sigma>n' where step_alpha:
      "((Normal \<sigma>n, Normal \<sigma>n), Normal \<Sigma>n, Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<sigma>n, \<Sigma>n') \<in> \<gamma>\<^sub>a \<and>
             \<gamma>\<^sub>a \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', Normal \<Sigma>n) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Throw, Normal \<Sigma>n')" 
       by (force elim: sim_elim_cases_c(2))
    then have "(\<sigma>n, \<Sigma>n')\<in> \<alpha>\<^sub>'" using a1 a3 step_alpha \<Sigma>' a00 
      unfolding Sta\<^sub>s_def  by blast   
    then have   "((Normal \<sigma>n, Normal \<sigma>n), Normal \<Sigma>n, Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>')" 
      using  a00 \<Sigma>' a1 step_alpha unfolding related_transitions_def by auto
    then have "\<exists>\<Sigma>n'. (((Normal \<sigma>n, Normal \<sigma>n), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                     (\<sigma>n, \<Sigma>n') \<in> \<gamma>\<^sub>a \<and>
                     \<gamma>\<^sub>a \<subseteq> \<alpha>\<^sub>' \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Throw, Normal \<Sigma>n')"
      using step_alpha  a2 \<Sigma>' by auto
  }  
  moreover{
   fix \<sigma>'' c\<^sub>c' e
   assume sigma:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (C\<^sub>c', \<sigma>') \<rightarrow> (c\<^sub>c', \<sigma>'') \<and> (\<forall>\<sigma>n. \<sigma>'' \<noteq> Normal \<sigma>n)"
   then have "\<exists>\<Sigma>'' c\<^sub>s'. (\<sigma>'',\<Sigma>'')\<in>\<alpha>\<^sub>x \<and> (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'')  \<or> 
               (\<exists>v. e = Some v \<and>  \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sup>+ (c\<^sub>s',\<Sigma>'') )) \<and> (\<sigma>', \<sigma>'') \<in> G\<^sub>c "
     using dest_sim_ev_step_not_normal[OF a0,of e c\<^sub>c' \<sigma>''] by fast
   then obtain \<Sigma>'' c\<^sub>s' where alpha:"(\<sigma>'',\<Sigma>'')\<in>\<alpha>\<^sub>x " and  
           "(\<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'') \<or>
            (\<exists>v. e = Some v \<and>
                 (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                        (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>''))))) \<and>  (\<sigma>', \<sigma>'') \<in> G\<^sub>c" 
      by fastforce+
    moreover have "(\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s)"        
      by (meson a3 a7 a8 alpha sigma sim_not_normal subset_trans)
   ultimately have  "\<exists>\<Sigma>''. (\<sigma>'', \<Sigma>'') \<in> \<alpha>\<^sub>x \<and>
                   (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'') \<or>
                            (\<exists>v. e = Some v \<and>
                                 (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                                        (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                                                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>''))))) \<and> (\<sigma>', \<sigma>'') \<in> G\<^sub>c \<and> 
                           ((\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s) \<or>
                            (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s)))" by fast   
 }
  moreover{
    assume "(\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n) \<and> C\<^sub>c' = LanguageCon.com.Skip"
    then have "\<exists>\<Sigma>''. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, \<Sigma>'') \<and> (\<sigma>', \<Sigma>'') \<in> \<alpha>\<^sub>x"
     by (fastforce intro:sim_elim_cases[OF a0 ])    
  }
  ultimately show 
     "(\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x \<and>
       (\<forall>\<sigma>n. \<sigma>' = Normal \<sigma>n \<longrightarrow> (\<exists>\<Sigma>n. \<Sigma>' = Normal \<Sigma>n \<and> (\<sigma>n, \<Sigma>n) \<in> \<alpha>\<^sub>')) \<and>
       (\<forall>c\<^sub>c' \<sigma>n'.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (C\<^sub>c', \<sigma>') \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow>
           (\<exists>c\<^sub>s' \<Sigma>n'.
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha>\<^sub>' \<and>
               (((\<sigma>', Normal \<sigma>n'), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
               ((\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s) \<and>
                (\<sigma>n', \<Sigma>n') \<in> \<alpha>\<^sub>' \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))) \<and>
       (\<forall>v c\<^sub>c' \<sigma>n'.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C\<^sub>c', \<sigma>') \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow>
           (\<exists>c\<^sub>s' \<Sigma>n'.
               (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                      (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n'))) \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha>\<^sub>' \<and>
               (((\<sigma>', Normal \<sigma>n'), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
               ((\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s) \<and>
                (\<sigma>n', \<Sigma>n') \<in> \<alpha>\<^sub>' \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))) \<and>
       (\<forall>\<sigma>'' \<Sigma>''.
           (((\<sigma>', \<sigma>''), \<Sigma>', \<Sigma>'') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and> (\<sigma>'', \<Sigma>'') \<in> \<alpha>\<^sub>x \<longrightarrow>
           (\<Gamma>\<^sub>c,(C\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s) \<and>
           (\<forall>\<sigma>n \<Sigma>n. \<sigma>'' = Normal \<sigma>n \<and> \<Sigma>'' = Normal \<Sigma>n \<longrightarrow> (\<sigma>n, \<Sigma>n) \<in> \<alpha>\<^sub>') \<or>
           (\<Gamma>\<^sub>c,(C\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s)) \<and>
       (\<forall>\<sigma>n. C\<^sub>c' = LanguageCon.com.Skip \<and> \<sigma>' = Normal \<sigma>n \<longrightarrow>
             (\<exists>\<Sigma>n'. ((Normal \<sigma>n, Normal \<sigma>n), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>' \<and>
                     (\<sigma>n, \<Sigma>n') \<in> \<gamma>\<^sub>n \<and>
                     \<gamma>\<^sub>n \<subseteq> \<alpha>\<^sub>' \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, Normal \<Sigma>n'))) \<and>
       (\<forall>\<sigma>n. C\<^sub>c' = LanguageCon.com.Throw \<and> \<sigma>' = Normal \<sigma>n \<longrightarrow>
             (\<exists>\<Sigma>n'. (((Normal \<sigma>n, Normal \<sigma>n), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                     (\<sigma>n, \<Sigma>n') \<in> \<gamma>\<^sub>a \<and>
                     \<gamma>\<^sub>a \<subseteq> \<alpha>\<^sub>' \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Throw, Normal \<Sigma>n'))) \<and>
       (\<forall>\<sigma>'' c\<^sub>c' e.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (C\<^sub>c', \<sigma>') \<rightarrow> (c\<^sub>c', \<sigma>'') \<and> (\<forall>\<sigma>n. \<sigma>'' \<noteq> Normal \<sigma>n) \<longrightarrow>
           (\<exists>\<Sigma>''. (\<sigma>'', \<Sigma>'') \<in> \<alpha>\<^sub>x \<and>
                   (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'') \<or>
                            (\<exists>v. e = Some v \<and>
                                 (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                                        (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                                                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>''))))) \<and> (\<sigma>', \<sigma>'') \<in> G\<^sub>c \<and> 
                           ((\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s) \<or>
                            (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s))))) \<and>
       ((\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n) \<and> C\<^sub>c' = LanguageCon.com.Skip \<longrightarrow>
        (\<exists>\<Sigma>''. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, \<Sigma>'') \<and> (\<sigma>', \<Sigma>'') \<in> \<alpha>\<^sub>x)) " by auto
     
qed
  
 
lemma strenrel:
  "(\<Gamma>\<^sub>c,C\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow>
  (\<xi> \<union> \<gamma>\<^sub>n \<union> \<gamma>\<^sub>a) \<subseteq> \<alpha>\<^sub>' \<and> \<alpha>\<^sub>' \<subseteq> \<alpha> \<Longrightarrow>
  Sta\<^sub>s \<alpha>\<^sub>' (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow>   R\<^sub>c\<subseteq>1\<alpha>\<^sub>x \<Longrightarrow> \<forall>\<sigma>.(\<sigma>,\<sigma>)\<in>G\<^sub>c \<Longrightarrow>
   (\<Gamma>\<^sub>c,C\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def apply (rule, rule, rule) apply (rule strenrel_sound)   
  by auto
    
 lemma weakenrel_sound:
assumes 
   a0:"(\<Gamma>\<^sub>c,(C\<^sub>c, \<sigma>na),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, \<Sigma>na),R\<^sub>s,G\<^sub>s)" and
   a1:"\<alpha> \<subseteq> \<alpha>\<^sub>'" and
   a2:" Sta\<^sub>s \<alpha> (R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>'" and a4:" R\<^sub>c\<subseteq>1\<alpha>\<^sub>x " and a8:"\<forall>\<sigma>.(\<sigma>,\<sigma>)\<in>G\<^sub>c"
 shows "(\<Gamma>\<^sub>c,(C\<^sub>c, \<sigma>na),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, \<Sigma>na),R\<^sub>s,G\<^sub>s)"   
   using a0 
 proof (coinduction arbitrary:\<sigma>na \<Sigma>na  C\<^sub>c C\<^sub>s,clarsimp) 
   fix \<sigma>' \<Sigma>' C\<^sub>c' C\<^sub>s' 
   assume a0:"(\<Gamma>\<^sub>c,(C\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)"
   have alpha_rel:"\<forall>\<sigma>n. \<sigma>' = Normal \<sigma>n  \<longrightarrow> (\<exists>\<Sigma>n. \<Sigma>' = Normal \<Sigma>n \<and> (\<sigma>n,\<Sigma>n) \<in> \<alpha>\<^sub>')" 
     using dest_sim_alpha[OF a0] using a1 by fastforce
   moreover have \<alpha>\<^sub>x:"(\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x" using a0
     using dest_sim_alpha_x by blast 
   moreover{
     fix c\<^sub>c' \<sigma>n'
     assume a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (C\<^sub>c', \<sigma>') \<rightarrow> (c\<^sub>c', Normal \<sigma>n')"
     then obtain \<sigma>n \<Sigma>n where \<sigma>n:"\<sigma>' = Normal \<sigma>n" and \<Sigma>n:"\<Sigma>' = Normal \<Sigma>n" using \<alpha>\<^sub>x
       by (metis a0 compe_normal_s'_normal_s dest_sim_alpha)        
     then obtain cs' \<Sigma>n' where step_alpha:"
       \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (cs', Normal \<Sigma>n') \<and>
       (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
       (((Normal \<sigma>n, Normal \<sigma>n'),Normal \<Sigma>n, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
       (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(cs', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)" 
       using dest_sim_tau_step[OF a0 a00] by auto 
     moreover have "(\<sigma>n', \<Sigma>n') \<in> \<alpha>\<^sub>'" using a1 calculation by auto
     moreover have "(((Normal \<sigma>n, Normal \<sigma>n'),Normal \<Sigma>n, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>')"
       using step_alpha  a1   unfolding related_transitions_def  by auto
     ultimately have "(\<exists>c\<^sub>s' \<Sigma>n'.
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha>\<^sub>' \<and>
               (((\<sigma>', Normal \<sigma>n'), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
               ((\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s) \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))"
       using \<sigma>n \<Sigma>n
       by auto
   }
   moreover{
     fix  v c\<^sub>c' \<sigma>n'
     assume a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C\<^sub>c', \<sigma>') \<rightarrow> (c\<^sub>c', Normal \<sigma>n')"
     then obtain \<sigma>n \<Sigma>n where \<sigma>n:"\<sigma>' = Normal \<sigma>n" and \<Sigma>n:"\<Sigma>' = Normal \<Sigma>n" using \<alpha>\<^sub>x
       by (metis a0 compe_normal_s'_normal_s dest_sim_alpha)
     then obtain c\<^sub>s' \<Sigma>n' where step_alpha:" 
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sup>+ (c\<^sub>s', Normal \<Sigma>n') \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
               (((\<sigma>', Normal \<sigma>n'), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)" 
       using dest_sim_ev_step[OF a0 a00]  by fast
     moreover have "(\<sigma>n', \<Sigma>n') \<in> \<alpha>\<^sub>'" using a1 calculation by auto
     moreover have "((Normal \<sigma>n, Normal \<sigma>n'), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>'"
       using step_alpha  a1 \<sigma>n  \<Sigma>n unfolding related_transitions_def  by auto
     ultimately have " 
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sup>+ (c\<^sub>s', Normal \<Sigma>n') \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha>\<^sub>' \<and>
               (((Normal \<sigma>n, Normal \<sigma>n'), Normal \<Sigma>n, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
               ((\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s) \<or> (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c)
                \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))" using \<sigma>n \<Sigma>n by auto
     then have "\<exists>c\<^sub>s' \<Sigma>n'.
               (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                      (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n'))) \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha>\<^sub>' \<and>
               (((\<sigma>', Normal \<sigma>n'), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
               ((\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s) \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))" using \<sigma>n \<Sigma>n by fast
   }
   moreover{
    fix \<sigma>'' \<Sigma>''  
    assume a00:"(((\<sigma>', \<sigma>''), \<Sigma>', \<Sigma>'') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and> (\<sigma>'', \<Sigma>'') \<in> \<alpha>\<^sub>x"
    {assume "\<exists>\<sigma>n. \<sigma>' = Normal \<sigma>n"
      then obtain \<sigma>n \<Sigma>n where \<sigma>:"\<sigma>' = Normal \<sigma>n \<and> \<Sigma>' = Normal \<Sigma>n"
        using \<alpha>\<^sub>x by (metis Normal_alpha) 
       moreover have "(\<sigma>n,\<Sigma>n)\<in>\<alpha>" using dest_sim_alpha[OF a0] calculation by auto
     ultimately have a00':"((Normal \<sigma>n, \<sigma>''), Normal \<Sigma>n, \<Sigma>'') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and> (\<sigma>'', \<Sigma>'') \<in> \<alpha>\<^sub>x" 
       using a00 a2  unfolding Sta\<^sub>s_def related_transitions_def by fast
     then have "(\<Gamma>\<^sub>c,(C\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s) \<or>
                 (\<Gamma>\<^sub>c,(C\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s)"
       using dest_sim_env_step[OF a0] \<sigma>  unfolding related_transitions_def by auto        
    }
    moreover{
      assume a000:"\<nexists>\<sigma>n. \<sigma>' = Normal \<sigma>n"
      then have "\<nexists>\<Sigma>n. \<Sigma>' = Normal \<Sigma>n" using \<alpha>\<^sub>x
        using alpha_not_normal by auto
      then have "(\<nexists>\<sigma>n. \<sigma>'' = Normal \<sigma>n) \<and> (\<nexists>\<Sigma>n. \<Sigma>' = Normal \<Sigma>n)" 
        using a4 a00 a000 unfolding related_transitions_def
        by (metis (no_types, lifting) a00 simulation_env_not_normal)
      then have "(\<Gamma>\<^sub>c,(C\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s) \<or>
                 (\<Gamma>\<^sub>c,(C\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s)"
        using  sim_not_normal a00 a4 a8 by auto
   }
   ultimately have "(\<Gamma>\<^sub>c,(C\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s) \<or>
                 (\<Gamma>\<^sub>c,(C\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s)" by auto
  }
  moreover{
    fix \<sigma>n
    assume "C\<^sub>c' = LanguageCon.com.Skip \<and> \<sigma>' = Normal \<sigma>n"    
    then have a0:"(\<Gamma>\<^sub>c,(Skip,Normal \<sigma>n),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)"
      using a0 by auto
    then obtain \<Sigma>n' where step_alpha:
      "((Normal \<sigma>n, Normal \<sigma>n), \<Sigma>', Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<sigma>n, \<Sigma>n') \<in> \<gamma>\<^sub>n \<and>
             \<gamma>\<^sub>n \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, Normal \<Sigma>n')" 
      by (force elim: sim_elim_cases_c(1))    
    then have "(\<sigma>n,\<Sigma>n')\<in> \<alpha>\<^sub>'" using a1  
      unfolding Sta\<^sub>s_def  by blast   
    moreover have   "((Normal \<sigma>n, Normal \<sigma>n), \<Sigma>', Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>')" 
      using  a1 step_alpha unfolding related_transitions_def by auto    
    ultimately have "\<exists>\<Sigma>n'. (((Normal \<sigma>n, Normal \<sigma>n), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                     (\<sigma>n, \<Sigma>n') \<in> \<gamma>\<^sub>n \<and>
                     \<gamma>\<^sub>n \<subseteq> \<alpha>\<^sub>' \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, Normal \<Sigma>n')" 
      using step_alpha a1 by auto
  }
  moreover{
     fix \<sigma>n
     assume "C\<^sub>c' = LanguageCon.com.Throw \<and> \<sigma>' = Normal \<sigma>n"      
    then have a0:"(\<Gamma>\<^sub>c,(Throw,Normal \<sigma>n),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)"         
      using a0 by auto
    then obtain \<Sigma>n' where step_alpha:
      "((Normal \<sigma>n, Normal \<sigma>n),\<Sigma>', Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<sigma>n,\<Sigma>n') \<in> \<gamma>\<^sub>a \<and>
             \<gamma>\<^sub>a \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s',  \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, Normal \<Sigma>n')" 
      by (force elim: sim_elim_cases_c(2))
    then have "(\<sigma>n,\<Sigma>n')\<in> \<alpha>\<^sub>'" using a1 by auto   
    moreover have "((Normal \<sigma>n, Normal \<sigma>n), \<Sigma>', Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>')" 
      using a1 step_alpha unfolding related_transitions_def by auto    
    then have "\<exists>\<Sigma>n'. (((Normal \<sigma>n, Normal \<sigma>n), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                     (\<sigma>n, \<Sigma>n') \<in> \<gamma>\<^sub>a \<and>
                     \<gamma>\<^sub>a \<subseteq> \<alpha>\<^sub>' \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Throw, Normal \<Sigma>n')"
     using step_alpha a1 by auto
  }  
  moreover{
    fix \<sigma>'' c\<^sub>c' e
    assume a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (C\<^sub>c', \<sigma>') \<rightarrow> (c\<^sub>c', \<sigma>'') \<and> (\<forall>\<sigma>n. \<sigma>'' \<noteq> Normal \<sigma>n)"
    then have "\<exists>\<Sigma>'' c\<^sub>s'. (\<sigma>'',\<Sigma>'')\<in>\<alpha>\<^sub>x \<and> (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'')  \<or> 
               (\<exists>v. e = Some v \<and>  \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sup>+ (c\<^sub>s',\<Sigma>'') ))  \<and> (\<sigma>', \<sigma>'') \<in> G\<^sub>c"
     using dest_sim_ev_step_not_normal[OF a0,of e c\<^sub>c' \<sigma>''] by fast
   then obtain \<Sigma>'' c\<^sub>s' where alpha:"(\<sigma>'',\<Sigma>'')\<in>\<alpha>\<^sub>x " and  
           "((\<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s',  \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'') \<or>
            (\<exists>v. e = Some v \<and>
                 (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s',  \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                        (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'')))))) \<and> (\<sigma>', \<sigma>'') \<in> G\<^sub>c" 
      by fastforce+
    moreover have "(\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s)"
      by (simp add: a00 a4 a8 alpha sim_not_normal)              
    ultimately have "\<exists>\<Sigma>''. (\<sigma>'', \<Sigma>'') \<in> \<alpha>\<^sub>x \<and>
                  (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'') \<or>
                           (\<exists>v. e = Some v \<and>
                                (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                                       (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                                                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>''))))) \<and> (\<sigma>', \<sigma>'') \<in> G\<^sub>c \<and> 
                          ((\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s) \<or>
                           (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s)))"  by fastforce
  }
  moreover {
    assume "(\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n) \<and> C\<^sub>c' = LanguageCon.com.Skip"
    then have "(\<exists>\<Sigma>''. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, \<Sigma>'') \<and> (\<sigma>', \<Sigma>'') \<in> \<alpha>\<^sub>x)"
      by (fastforce intro:sim_elim_cases[OF a0 ])    
  }
  ultimately show 
     "(\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x \<and>
       (\<forall>\<sigma>n. \<sigma>' = Normal \<sigma>n \<longrightarrow> (\<exists>\<Sigma>n. \<Sigma>' = Normal \<Sigma>n \<and> (\<sigma>n, \<Sigma>n) \<in> \<alpha>\<^sub>')) \<and>
       (\<forall>c\<^sub>c' \<sigma>n'.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (C\<^sub>c', \<sigma>') \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow>
           (\<exists>c\<^sub>s' \<Sigma>n'.
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha>\<^sub>' \<and>
               (((\<sigma>', Normal \<sigma>n'), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
               ((\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s) \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))) \<and>
       (\<forall>v c\<^sub>c' \<sigma>n'.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C\<^sub>c', \<sigma>') \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow>
           (\<exists>c\<^sub>s' \<Sigma>n'.
               (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                      (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n'))) \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha>\<^sub>' \<and>
               (((\<sigma>', Normal \<sigma>n'), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
               ((\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s) \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))) \<and>
       (\<forall>\<sigma>'' \<Sigma>''. (((\<sigma>', \<sigma>''), \<Sigma>', \<Sigma>'') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and> (\<sigma>'', \<Sigma>'') \<in> \<alpha>\<^sub>x \<longrightarrow>
                 (\<Gamma>\<^sub>c,(C\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s) \<or>
                 (\<Gamma>\<^sub>c,(C\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s)) \<and>
       (\<forall>\<sigma>n. C\<^sub>c' = LanguageCon.com.Skip \<and> \<sigma>' = Normal \<sigma>n \<longrightarrow>
             (\<exists>\<Sigma>n'. (((Normal \<sigma>n, Normal \<sigma>n), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                     (\<sigma>n, \<Sigma>n') \<in> \<gamma>\<^sub>n \<and>
                     \<gamma>\<^sub>n \<subseteq> \<alpha>\<^sub>' \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, Normal \<Sigma>n'))) \<and>
       (\<forall>\<sigma>n. C\<^sub>c' = LanguageCon.com.Throw \<and> \<sigma>' = Normal \<sigma>n \<longrightarrow>
             (\<exists>\<Sigma>n'. (((Normal \<sigma>n, Normal \<sigma>n), \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                     (\<sigma>n, \<Sigma>n') \<in> \<gamma>\<^sub>a \<and>
                     \<gamma>\<^sub>a \<subseteq> \<alpha>\<^sub>' \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Throw, Normal \<Sigma>n'))) \<and>
       (\<forall>\<sigma>'' c\<^sub>c' e.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (C\<^sub>c', \<sigma>') \<rightarrow> (c\<^sub>c', \<sigma>'') \<and> (\<forall>\<sigma>n. \<sigma>'' \<noteq> Normal \<sigma>n) \<longrightarrow>
           (\<exists>\<Sigma>''. (\<sigma>'', \<Sigma>'') \<in> \<alpha>\<^sub>x \<and>
                  (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'') \<or>
                           (\<exists>v. e = Some v \<and>
                                (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                                       (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                                                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>''))))) \<and> (\<sigma>', \<sigma>'') \<in> G\<^sub>c \<and>
                          ((\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s) \<or>
                           (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s))))) \<and>
       ((\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n) \<and> C\<^sub>c' = LanguageCon.com.Skip \<longrightarrow>
        (\<exists>\<Sigma>''. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, \<Sigma>'') \<and> (\<sigma>', \<Sigma>'') \<in> \<alpha>\<^sub>x)) "
    by force 
     
qed   
    
 lemma weakenrel:
  "(\<Gamma>\<^sub>c,C\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow>
  \<alpha> \<subseteq> \<alpha>\<^sub>' \<Longrightarrow>
  Sta\<^sub>s \<alpha> (R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>' \<Longrightarrow>   R\<^sub>c\<subseteq>1\<alpha>\<^sub>x \<Longrightarrow> \<forall>\<sigma>.(\<sigma>,\<sigma>)\<in>G\<^sub>c \<Longrightarrow>
   (\<Gamma>\<^sub>c,C\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def apply (rule, rule, rule) apply (rule weakenrel_sound)     
  by auto
 

primrec state_mod :: "('s,'p,'f,'e) com \<Rightarrow> bool"
  where 
"state_mod (Basic _ _)  = True"
|"state_mod (Spec _ _)  = True"
|"state_mod (Await _ _ _)  = True"
|"state_mod Skip = False"
  |"state_mod (Seq _ _) = False"    
  |"state_mod (Cond _ _ _) = False"
  | "state_mod (While _ _) = False"
  | "state_mod (Call _) = False"
  | "state_mod (DynCom _) = False" 
  | "state_mod (Guard _ _ _) =False" 
  | "state_mod Throw = False"
  | "state_mod (Catch _ _) = False"

primrec label :: "('s,'p,'f,'e) com \<Rightarrow> 'e option"
  where
"label (Basic _ l)  = l"
|"label (Spec _ l)  = l"
|"label (Await _ _ l)  = l"
|"label Skip = None"
  |"label (Seq c1 c2) = (if (c1\<noteq>Skip \<and> c1\<noteq>Throw) then label c1 else None)"    
  |"label (Cond _ _ _) = None"
  | "label (While _ _) = None"
  | "label (Call _) = None"
  | "label (DynCom _) = None" 
  | "label (Guard _ _ _) =None" 
  | "label Throw = None"
  | "label (Catch c1 c2) = (if (c1\<noteq>Skip \<and> c1\<noteq>Throw) then label c1 else None)"

lemma 
  assumes a0:"(\<And>C'. \<Gamma>\<turnstile>\<^sub>c\<^sub>e (C1, Normal s) \<rightarrow> (C', s') \<Longrightarrow> label C1 = e)" and          
        a2:"\<Gamma>\<turnstile>\<^sub>c\<^sub>e (LanguageCon.com.Seq C1 C2, Normal s) \<rightarrow> (C', s')" and
       a3:"l = label C1" and a4:"C1 \<noteq> LanguageCon.com.Skip" and a5:"C1 \<noteq> LanguageCon.com.Throw" 
     shows "label C1 = e"
proof (cases C1)
  case Skip then show ?thesis using a4 by metis
next
  case (Basic x21 x22)   
  then show ?thesis using evstepc_elim_seq(3)[OF a2] a0 
    by fastforce  
next
  case (Spec x31 x32)    
  then show ?thesis using evstepc_elim_seq(3)[OF a2] a0 
    by fastforce     
next
  case (Seq x41 x42)      
  then show ?thesis using evstepc_elim_seq(3)[OF a2] a0 
    by fastforce
    
next
case (Cond x51 x52 x53)
  then show ?thesis using evstepc_elim_seq(3)[OF a2] a0 
    by fastforce
next
  case (While x61 x62)
  then show ?thesis  using evstepc_elim_seq(3)[OF a2] a0  
    by fastforce
next
  case (Call x7) then show ?thesis  using evstepc_elim_seq(3)[OF a2] a0  
    by fastforce
next
  case (DynCom x8) then show ?thesis  using evstepc_elim_seq(3)[OF a2] a0  
    by fastforce
next
  case (Guard x91 x92 x93)
    then show ?thesis  using evstepc_elim_seq(3)[OF a2] a0  
    by fastforce
next
  case Throw
  then show ?thesis  using evstepc_elim_seq(3)[OF a2] a0  
    by fastforce
next
  case (Catch x111 x112)
  then show ?thesis  using evstepc_elim_seq(3)[OF a2] a0  
    by fastforce
next
  case (Await x121 x122 x123)
  then show ?thesis  using evstepc_elim_seq(3)[OF a2] a0  
    by fastforce
qed


lemma label_step:"label C = l \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c\<^sub>e (C, Normal s) \<rightarrow> (C',s') \<Longrightarrow>
      l = e"
  apply (induction C arbitrary: C')  apply auto  
  by (fastforce elim: stepc_elim_cases1)+
                              

primrec com_step_n ::"('s,'p,'f,'e) com \<Rightarrow> 's \<Rightarrow> ('s,'p,'f,'e) body \<Rightarrow> (('s,'f) xstate) set"
  where
"com_step_n  (Basic f l) s \<Gamma> = {s'. (\<exists>sn. (sn = f s) \<and> s' = Normal sn)}"
|"com_step_n (Spec r l) s \<Gamma> = {s'. (\<exists>sn. ((s,sn)\<in> r) \<and> s' = Normal sn) \<or> ((\<nexists>sn.(s, sn)\<in>r) \<and> s' = Stuck)}"
|"com_step_n (Await b c l) s \<Gamma> = {t. (s \<in> b \<and> \<Gamma>\<^sub>\<not>\<^sub>a\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t)}"
(* |"com_step Skip s \<Gamma> = {Normal s} "
|"com_step (Seq _ _) s \<Gamma> = {Normal s}"    
|"com_step (Cond _ _ _) s \<Gamma> = {Normal s}"
| "com_step (While _ _) s \<Gamma> = {Normal s}"
| "com_step (Call _) s \<Gamma> = {Normal s}" 
| "com_step (DynCom _) s \<Gamma> = {Normal s}" 
| "com_step (Guard _ _ _) s \<Gamma> = {Normal s}" 
| "com_step Throw s \<Gamma> = {Normal s}"
| "com_step (Catch _ _) s \<Gamma> = {Normal s}"  *)

primrec com_step::"('s,'p,'f,'e) com \<Rightarrow> ('s,'f) xstate \<Rightarrow> ('s,'p,'f,'e) body \<Rightarrow> (('s,'f) xstate) set"
  where                         
"com_step C (Normal s) \<Gamma> = com_step_n C s \<Gamma>"
|"com_step C (Abrupt s) \<Gamma> = {Abrupt s}"
|"com_step C Stuck \<Gamma> = {Stuck}"
|"com_step C (Fault f) \<Gamma> = {Fault f}"

lemma com_step_BS:
  assumes a0:"s' \<in> com_step P (Normal s1) \<Gamma>" and
        a1:"(\<exists> f. P = Basic f l) \<or> (\<exists>r. P = Spec r l) \<or> (\<exists>b c. P = Await b c l)" and
        a2:"(\<forall>sn'. s' \<noteq> Abrupt sn')"
  shows  "\<Gamma>\<turnstile>\<^sub>c\<^sub>l (P, (Normal s1)) \<rightarrow> (Skip, s')"  
proof-
  show ?thesis using a0 a1 a2
    apply auto 
       apply (force intro: stepc_stepce_unique stepce.Basicc)    
      apply (force intro: stepc_stepce_unique stepce.Specc)           
      apply (meson stepce.SpecStuckc  stepc_stepce_unique)+
    by (meson a2 stepce.Awaitc stepc_stepce_unique)+
qed

lemma com_step_BS1:
  assumes a0:"s' \<in> com_step P s \<Gamma>" and
        a1:"(\<exists> f. P = Basic f l) \<or> (\<exists>r. P = Spec r l) \<or> (\<exists>b c. P = Await b c l)" and
        a2:"s' = Abrupt sn'" and
        a3:"s= Normal s1"
  shows  "\<Gamma>\<turnstile>\<^sub>c\<^sub>l (P, s) \<rightarrow> (Throw, Normal sn')"  
proof-
  show ?thesis using a0 a1 a2 a3
    apply auto 
    using AwaitAbruptc by fastforce 
qed

lemma com_step_BSNotNormal:
  assumes a0:"s' \<in> com_step P s \<Gamma>" and
        a1:"(\<exists> f l. P = Basic f l) \<or> (\<exists>r l. P = Spec r l) \<or> (\<exists>b c l. P = Await b c l)" and
        a2:"(\<forall>sn'. s \<noteq> Normal sn')"
  shows  "\<exists>l. \<Gamma>\<turnstile>\<^sub>c\<^sub>l (P, s) \<rightarrow> (Skip, s')"
proof (cases s)
  case Normal thus ?thesis using a2 by auto
next
case (Abrupt x2)
  then show ?thesis using a0 a1   
    by(fastforce intro: stepce.AbruptPropc )+
next
  case (Fault x3)
  then show ?thesis using a0 a1 by(fastforce intro: stepce.FaultPropc)+
next
  case Stuck
  then show ?thesis using a0 a1 by(fastforce intro: stepce.StuckPropc)+ 
qed

(* 
lemma com_step_n:"s' \<in> com_step P s \<Gamma> \<Longrightarrow> \<not>(\<exists>t'. s' = Abrupt t') \<Longrightarrow> 
                 (\<exists>b c l. P = Await b c l \<and> s\<in>b) \<Longrightarrow> \<exists>P' l. \<Gamma>\<turnstile>\<^sub>c\<^sub>l (P, s) \<rightarrow> (P', s')"  
  apply auto
   by (meson stepc.Awaitc stepc_stepce_unique)
  
lemma com_step_b:"s' \<in> com_step P s \<Gamma> \<Longrightarrow>  s' = Abrupt t' \<Longrightarrow> (\<exists>b c l. P = Await b c l \<and> s\<in>b) \<Longrightarrow> \<exists>P' l. \<Gamma>\<turnstile>\<^sub>c\<^sub>l (P, Normal s) \<rightarrow> (P', Normal t')"  
  apply auto
   by (meson stepc.AwaitAbruptc stepc_stepce_unique)


lemma "\<forall>\<sigma> \<sigma>' \<Sigma> . (Normal \<sigma>, Normal \<Sigma>)\<in>\<xi> \<and> \<sigma>' \<in> com_step  C \<sigma>  \<Gamma>\<^sub>c  \<longrightarrow> 
                (\<exists>\<Sigma>'. \<Sigma>' \<in> com_step  S \<Sigma> \<Gamma>\<^sub>s \<and> 
                     (Normal \<sigma>',Normal \<Sigma>')\<in>\<gamma>\<^sub>n \<and> 
                     (Normal \<sigma>, Normal \<sigma>') \<in> G\<^sub>c \<and>
                     (Normal \<Sigma>, Normal \<Sigma>') \<in> G\<^sub>s)"
  sorry *)

lemma mod_sound:
  assumes  
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>sn. (sn, sn)\<in>G\<^sub>c" and a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and  
 a9:"C = Basic fc l \<or> C = Spec rc l \<or> C = Await bc Cc l" and 
 a9': "S = Basic fs l \<or> S = Spec rs l \<or> S = Await bs Cs l" and  
 a10:"\<forall>\<sigma> \<sigma>' \<Sigma> . (\<sigma>, \<Sigma>)\<in>\<xi> \<and> \<sigma>' \<in> com_step  C (Normal \<sigma>)  \<Gamma>\<^sub>c  \<longrightarrow> 
                (\<exists>\<Sigma>'. \<Sigma>' \<in> com_step  S (Normal \<Sigma>) \<Gamma>\<^sub>s \<and>  (\<sigma>', \<Sigma>')\<in>\<alpha>\<^sub>x \<and> 
                       ((\<forall>\<sigma>n'. \<sigma>' = Normal \<sigma>n'   \<longrightarrow> 
                           (\<exists>\<Sigma>n'. \<Sigma>' = Normal \<Sigma>n' \<and> (\<sigma>n',\<Sigma>n')\<in>\<gamma>\<^sub>n \<and> 
                           (Normal \<sigma>, Normal \<sigma>n') \<in> G\<^sub>c \<and> (Normal \<Sigma>, Normal \<Sigma>n') \<in> G\<^sub>s)))  \<and> 
                       (\<forall>\<sigma>n'. \<sigma>' = Abrupt \<sigma>n'  \<longrightarrow> 
                           (\<exists>\<Sigma>n'. \<Sigma>' = Abrupt \<Sigma>n' \<and> (\<sigma>n', \<Sigma>n')\<in>\<gamma>\<^sub>a \<and> 
                                (Normal \<sigma>, Normal \<sigma>n') \<in> G\<^sub>c \<and> (Normal \<Sigma>, Normal \<Sigma>n') \<in> G\<^sub>s)) \<and> 
                       ((\<forall>\<sigma>n'. \<sigma>' \<noteq> Normal \<sigma>n') \<and> (\<forall>\<sigma>n'. \<sigma>' \<noteq> Abrupt \<sigma>n') \<longrightarrow> (Normal \<sigma>, \<sigma>')\<in> G\<^sub>c ))                      
                 " and
 a11:"(\<sigma>n, \<Sigma>n) \<in> \<xi>" and
 a12:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v (C, Normal \<sigma>n) \<rightarrow> (C', \<sigma>')"
shows "\<exists>S' \<Sigma>'.
          (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>n) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                 (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (S', \<Sigma>'))) \<and>
          (\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x  \<and> ((\<forall>\<sigma>n'. \<sigma>' = Normal \<sigma>n'   \<longrightarrow> 
                           (\<exists>\<Sigma>n'. \<Sigma>' = Normal \<Sigma>n' \<and> (\<sigma>n',\<Sigma>n')\<in>\<alpha> \<and> 
                             (Normal \<Sigma>n, Normal \<Sigma>n') \<in> G\<^sub>s))) \<and> (Normal \<sigma>n, \<sigma>') \<in> G\<^sub>c  \<and>                         
          (\<Gamma>\<^sub>c,(C', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S', \<Sigma>'),R\<^sub>s,G\<^sub>s)"
proof-  
  have v_l:"v = l" using a12 a9 label_step by fastforce   
  have c1:"C' = Skip \<or> C' = Throw" using a9 stepc_elim_cases1(3,4,8)
  proof -
    have "\<forall>f z c x ca xa. \<not> f\<turnstile>\<^sub>c\<^sub>z (c::('a, 'd, 'b, 'e) LanguageCon.com, x) \<rightarrow> (ca, xa) \<or> f\<turnstile>\<^sub>c (c, x) \<rightarrow> (ca, xa)"
      by (metis stepce_stepc)
    then show ?thesis
      using a12 a9 basic_skip spec_skip await_skip
      by (metis stepce_stepc)
  qed
  moreover {
    assume c1:"C' = Skip"
    then have  s1:"\<sigma>' \<in> com_step  C (Normal \<sigma>n) \<Gamma>\<^sub>c" using a9 a12       
      by  (fastforce elim: stepc_elim_cases1(4) stepc_elim_cases1(3)  stepc_elim_cases1(8))+             
    {assume "\<exists>sn1. \<sigma>' = Normal sn1"
      then obtain \<sigma>n' where \<sigma>n':"\<sigma>' = Normal \<sigma>n'" by auto
      then obtain \<Sigma>'  where cond: "\<Sigma>' \<in> com_step  S (Normal \<Sigma>n) \<Gamma>\<^sub>s \<and>   (\<sigma>', \<Sigma>')\<in>\<alpha>\<^sub>x \<and>
                           (\<exists>\<Sigma>n'. \<Sigma>' = Normal \<Sigma>n' \<and> (\<sigma>n',\<Sigma>n')\<in>\<gamma>\<^sub>n \<and> 
                           (Normal \<sigma>n, \<sigma>') \<in> G\<^sub>c \<and> (Normal \<Sigma>n, \<Sigma>') \<in> G\<^sub>s)"
       using a10 a11 c1 s1 by fast
      have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (S, Normal \<Sigma>n) \<rightarrow> (Skip, \<Sigma>')" 
        using com_step_BS cond a9'   v_l by fast           
      then have ?thesis using 
        a11 cond  a1 a2 Skip_sim_normal[OF  a2 _ a4  _ a6 a7 ] c1 cond  \<sigma>n' 
        unfolding related_transitions_def by blast
    }
    moreover { 
      assume ass0:"\<sigma>' = Stuck \<or> (\<exists>f. \<sigma>' = Fault f)"      
      then obtain \<Sigma>'  where cond: "\<Sigma>' \<in> com_step  S (Normal \<Sigma>n) \<Gamma>\<^sub>s \<and>  (\<sigma>', \<Sigma>')\<in>\<alpha>\<^sub>x \<and> (Normal \<sigma>n, \<sigma>') \<in> G\<^sub>c"
        using a10 a11 c1 s1 by fast     
      then have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (S, Normal \<Sigma>n) \<rightarrow> (Skip, \<Sigma>')" 
        using com_step_BS cond a9' v_l
        by (metis Fault_alpha Stuck_alpha ass0 xstate.distinct(7) xstate.distinct(9))                
      have ?thesis using steps cond  
           Skip_sim_normal_not_normal[OF  _ _ a7 a6 ]  c1 ass0 by fast
    }
    moreover { 
      assume ass0: "\<exists>sn. \<sigma>' = Abrupt sn"
      then have False using a12 c1 step_Abrupt_end        
        using stepce_stepc by fastforce
      then have ?thesis by auto
    }
    ultimately have ?thesis by (cases \<sigma>', auto)     
  }
  moreover 
  { assume c1:"C' = Throw"
    then obtain bc Cc where c:"C = Await bc Cc l"
      using a9 a12 
      by  (fastforce elim: stepc_elim_cases1(4) stepc_elim_cases1(3)  stepc_elim_cases1(8))
    then obtain \<sigma>n' where sn1: "\<sigma>' = Normal \<sigma>n' \<and> \<sigma>n \<in> bc \<and> \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>n\<rangle> \<Rightarrow> Abrupt \<sigma>n'"
      using c1 a12 by (fastforce elim: stepc_elim_cases1(8))
    moreover have  s1:"Abrupt \<sigma>n' \<in> com_step  C (Normal \<sigma>n) \<Gamma>\<^sub>c" using c calculation by auto          
    ultimately obtain \<Sigma>' \<Sigma>n' where cond: "\<Sigma>' \<in> com_step  S (Normal \<Sigma>n) \<Gamma>\<^sub>s \<and>                             
                                (\<Sigma>' = Abrupt \<Sigma>n' \<and> (\<sigma>n', \<Sigma>n')\<in>\<gamma>\<^sub>a \<and> 
                                (Normal \<sigma>n, Normal \<sigma>n') \<in> G\<^sub>c \<and> (Normal \<Sigma>n, Normal \<Sigma>n') \<in> G\<^sub>s)"
       using a10 a11 c1 s1  by fastforce         
    then have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (S, Normal \<Sigma>n) \<rightarrow> (Throw, Normal \<Sigma>n')" 
      using   a9' sn1 com_step_BS1 v_l by metis      
    then have sim:"(\<Gamma>\<^sub>c,(C', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Throw, Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)"
      using cond Throw_sim_normal[OF  a2' _ a5 _ a6 a7 ] sn1 c1 by fast
    then have ?thesis using a2' steps   a11  cond  a1 sn1
      unfolding related_transitions_def
      using dest_sim_alpha_x by fastforce
  }
  ultimately show ?thesis by auto 
qed

lemma intro_tau_step:"(\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                 (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c1', s1'))) \<Longrightarrow>          
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c1', s1') "  
  by auto           
  

lemma state_mod_sim_not_normal: assumes a0:"(\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n)" and
     a1:"(\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                       (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>e (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (S', \<Sigma>'))) \<and>
                (\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x \<and>
                (\<forall>\<sigma>n'. \<sigma>' = Normal \<sigma>n' \<longrightarrow>
                       (\<exists>\<Sigma>n'. \<Sigma>' = Normal \<Sigma>n' \<and>
                               (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
                                (Normal \<Sigma>, Normal \<Sigma>n') \<in> G\<^sub>s)) \<and> 
                 (Normal \<sigma>, \<sigma>') \<in> G\<^sub>c \<and>
                (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S', \<Sigma>'),R\<^sub>s,G\<^sub>s)"
   shows" \<exists>\<Sigma>'. (\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x \<and>
             (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<or>
                      (\<exists>v. e = Some v \<and>
                           (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                                  (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                                           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'))))) \<and> (Normal \<sigma>, \<sigma>') \<in> G\<^sub>c \<and>
                     (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s))"
proof-  
  have "(\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (S', \<Sigma>') \<or>
                      (\<exists>v. e = Some v \<and>
                           (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                                  (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                                           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (S', \<Sigma>')))))"
    using a1 by (cases e, fastforce+) 
  then show ?thesis using a1 by metis
qed



lemma mod_state_tau_sound: 
  assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>sn. (sn, sn)\<in>G\<^sub>c" and a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and 
 a9:"C = Basic fc v \<or> C = Spec rc v \<or>  C = Await bc Cc v" and 
 a9': "S = Basic fs v \<or> S = Spec rs v \<or> S = Await bs Cs v" and  
 a10:"\<forall>\<sigma> \<sigma>' \<Sigma> . (\<sigma>, \<Sigma>)\<in>\<xi> \<and> \<sigma>' \<in> com_step  C (Normal \<sigma>)  \<Gamma>\<^sub>c  \<longrightarrow> 
                (\<exists>\<Sigma>'. \<Sigma>' \<in> com_step  S (Normal \<Sigma>) \<Gamma>\<^sub>s \<and>  (\<sigma>', \<Sigma>')\<in>\<alpha>\<^sub>x \<and> 
                       ((\<forall>\<sigma>n'. \<sigma>' = Normal \<sigma>n'   \<longrightarrow> 
                           (\<exists>\<Sigma>n'. \<Sigma>' = Normal \<Sigma>n' \<and> (\<sigma>n',\<Sigma>n')\<in>\<gamma>\<^sub>n \<and> 
                           (Normal \<sigma>, Normal \<sigma>n') \<in> G\<^sub>c \<and> (Normal \<Sigma>, Normal \<Sigma>n') \<in> G\<^sub>s)))  \<and> 
                       (\<forall>\<sigma>n'. \<sigma>' = Abrupt \<sigma>n'  \<longrightarrow> 
                           (\<exists>\<Sigma>n'. \<Sigma>' = Abrupt \<Sigma>n' \<and> (\<sigma>n', \<Sigma>n')\<in>\<gamma>\<^sub>a \<and> 
                                (Normal \<sigma>, Normal \<sigma>n') \<in> G\<^sub>c \<and> (Normal \<Sigma>, Normal \<Sigma>n') \<in> G\<^sub>s)) \<and> 
                       ((\<forall>\<sigma>n'. \<sigma>' \<noteq> Normal \<sigma>n') \<and> (\<forall>\<sigma>n'. \<sigma>' \<noteq> Abrupt \<sigma>n') \<longrightarrow> (Normal \<sigma>, \<sigma>')\<in> G\<^sub>c ))                      
                 " 
shows "(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)"  
  
proof-
  {fix \<sigma> \<Sigma> 
    assume a11: "(\<sigma>, \<Sigma>) \<in> \<xi>"    
    then have "(\<Gamma>\<^sub>c,(C, Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal \<Sigma>),R\<^sub>s,G\<^sub>s)"
  apply (coinduction arbitrary: \<sigma> \<Sigma>)
      apply clarsimp
      apply (rule conjId)+
      apply (rule, rule, rule, rule) 
             apply (frule mod_sound[OF a1 a2 a2' a3 a4 a5 a6 a7   a9 a9' a10], fast)
      apply (fast intro: state_mod_sim_not_normal)      
      using a9 apply auto[2] 
      apply (rule, rule, rule)   apply (blast dest: sim_env[OF _ a3 a6 a7])          
         apply (clarify, frule mod_sound[OF  a1 a2 a2' a3 a4 a5 a6 a7   a9 a9' a10], auto)
      apply (fastforce dest: related_transition_intro[OF subsetD[OF a1]])                               
        apply(frule mod_sound[OF  a1 a2 a2' a3 a4 a5 a6 a7  a9 a9' a10], auto)      
        apply (frule related_transition_intro[OF subsetD[OF a1]], assumption+) 
        apply(meson rtranclp.rtrancl_into_rtrancl rtranclp_trans)  
      using  a1 unfolding alpha_xstate_def by auto   
  } then show ?thesis unfolding RGSim_pre_def by auto
qed

(* |"com_step Skip s \<Gamma> = {Normal s} "
|"com_step (Seq _ _) s \<Gamma> = {Normal s}"    
|"com_step (Cond _ _ _) s \<Gamma> = {Normal s}"
| "com_step (While _ _) s \<Gamma> = {Normal s}"
| "com_step (Call _) s \<Gamma> = {Normal s}" 
| "com_step (DynCom _) s \<Gamma> = {Normal s}" 
| "com_step (Guard _ _ _) s \<Gamma> = {Normal s}" 
| "com_step Throw s \<Gamma> = {Normal s}"
| "com_step (Catch _ _) s \<Gamma> = {Normal s}"  *)

(* primrec com_step1::"('s,'p,'f,'e) com \<Rightarrow> ('s,'p,'f,'e) body \<Rightarrow> 's set \<Rightarrow> 's set \<Rightarrow> ('s,'f) xstate"
  where                         
"com_step1 C (Normal s) \<Gamma> = com_step_n1 C s \<Gamma>"
|"com_step1 C (Abrupt s) \<Gamma> = {Abrupt s}"
|"com_step1 C Stuck \<Gamma> = {Stuck}"
|"com_step1 C (Fault f) \<Gamma> = {Fault f}" *)


lemma step_imp_normal_rel_:
  assumes 
 a0:"\<forall>\<sigma>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (P \<sigma>n) Cc 
        (Q \<sigma>n), s" and
 a1:"\<sigma> \<in> P \<sigma>" and
 a2:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Normal \<sigma>'"
shows
 "\<sigma>' \<in> Q \<sigma>"
proof-
 obtain n where " \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Cc,Normal \<sigma>\<rangle> =n\<Rightarrow> Normal \<sigma>'"
    using a2 Semantic.exec_to_execn by fastforce 
  moreover have "\<And>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<Turnstile>n:\<^bsub>/F\<^esub>  
        (P \<sigma>) Cc 
        (Q \<sigma>), s"
   using a0 a2   hoare_cnvalid by fastforce
  ultimately show ?thesis  unfolding cnvalid_def nvalid_def  
    using a2 a1  by blast
qed

lemma in_normal_not_abrupt:
  assumes 
 a0:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> P1 Cc Q, {}" and
  a1: "\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Abrupt \<sigma>'" and
   a3:"\<sigma> \<in> P1"
shows "P"
proof-
  obtain n where " \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Cc,Normal \<sigma>\<rangle> =n\<Rightarrow> Abrupt \<sigma>'"
    using a1 Semantic.exec_to_execn by fastforce 
  moreover have "\<And>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<Turnstile>n:\<^bsub>/F\<^esub> P1 Cc Q, {}"
    using a0  hoare_cnvalid by fastforce
  ultimately show ?thesis unfolding cnvalid_def nvalid_def using  a3 by fastforce
qed

lemma not_normal_false:
  assumes 
 a0:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> P1 Cc Q, {}" and
  a1: "\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow>  \<sigma>'" and a2:"\<forall>\<sigma>''. \<sigma>' \<noteq> Normal \<sigma>''" and
   a3:"\<sigma> \<in> P1" and a4:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Fault f"
shows "P"
proof-
  obtain n where " \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Cc,Normal \<sigma>\<rangle> =n\<Rightarrow>  \<sigma>'"
    using a1 Semantic.exec_to_execn by fastforce 
  moreover have "\<And>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<Turnstile>n:\<^bsub>/F\<^esub> P1 Cc Q, {}"
    using a0  hoare_cnvalid by fastforce
  ultimately obtain \<sigma>'' where "\<sigma>' = Normal \<sigma>''" unfolding cnvalid_def nvalid_def using  a3 a4
    using a1 by blast 
  then show ?thesis unfolding cnvalid_def nvalid_def using  a2 by auto
qed

lemma not_normal_false1:
  assumes 
 a0:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> P1 Cc Q, {}" and
  a1: "\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow>  \<sigma>'" and a2:"\<forall>\<sigma>''. \<sigma>' \<noteq> Normal \<sigma>''" and
   a3:"\<sigma> \<in> P1" and a4:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Fault f"
shows "P"
proof-
  obtain n where " \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Cc,Normal \<sigma>\<rangle> =n\<Rightarrow>  \<sigma>'"
    using a1 Semantic.exec_to_execn by fastforce 
  moreover have "\<And>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<Turnstile>n:\<^bsub>/F\<^esub> P1 Cc Q, {}"
    using a0  hoare_cnvalid by fastforce
  ultimately obtain \<sigma>'' where "\<sigma>' = Normal \<sigma>''" unfolding cnvalid_def nvalid_def using  a3 a4
    using a1 by blast 
  then show ?thesis unfolding cnvalid_def nvalid_def using  a2 by auto
qed


lemma step_spec_normal_rel:
  assumes 
 a0:"\<forall>\<sigma>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. \<sigma>n = s \<and> \<sigma>n\<in>Domain \<xi>}) Cc 
        ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>n), ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>a)" and
 a1:"\<forall>\<Sigma>n. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (\<sigma>,  s) \<in> \<xi> } \<inter> bs \<inter> {\<Sigma>n}) Cs 
         ({s. (Normal  \<Sigma>n, Normal s) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (\<sigma>',\<Sigma>n')\<in> \<gamma>\<^sub>n}),{}" and
 a2:"(\<sigma>, \<Sigma>) \<in> \<xi>" and a3:"\<sigma> \<in> bc" and a4:"\<Sigma>\<in>bs" and
 a5:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Normal \<sigma>'" and a6:"\<forall>\<Sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal \<Sigma>\<rangle> \<Rightarrow> Fault f"
shows "\<exists>\<Sigma>'. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal \<Sigma>\<rangle> \<Rightarrow> Normal \<Sigma>' \<and> (\<sigma>',\<Sigma>')\<in>\<gamma>\<^sub>n \<and> (Normal \<Sigma>, Normal \<Sigma>')\<in>G\<^sub>s"
proof-
  obtain n where " \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Cc,Normal \<sigma>\<rangle> =n\<Rightarrow> Normal \<sigma>'"
    using a5 Semantic.exec_to_execn by fastforce 
  moreover have "\<And>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<Turnstile>n:\<^bsub>/F\<^esub>  
        (bc \<inter> {s. \<sigma> = s \<and> \<sigma>\<in>Domain \<xi>}) Cc 
        ({s. (Normal \<sigma>, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>n), ({s. (Normal \<sigma>, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>a)"
   using a0 a2 a3 hoare_cnvalid by fastforce
  ultimately have "\<sigma>' \<in> Domain \<gamma>\<^sub>n"  unfolding cnvalid_def nvalid_def  
    using a2 a3  by blast
  have " \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (\<sigma>,  s) \<in> \<xi> } \<inter> bs \<inter> {\<Sigma>}) Cs 
         ({s. (Normal  \<Sigma>, Normal s) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (\<sigma>',\<Sigma>n')\<in> \<gamma>\<^sub>n}),{}"
    using a2 a1 by blast
  then have "\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (\<sigma>,  s) \<in> \<xi> } \<inter> bs \<inter> {\<Sigma>}) Cs 
         ({s. (Normal  \<Sigma>, Normal s) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (\<sigma>',\<Sigma>n')\<in> \<gamma>\<^sub>n}),{}"
    using hoaret_sound' by blast  
  thus ?thesis  
    using a4 a2 a6 Termination.terminates_implies_exec   unfolding validt_def valid_def
    by blast
qed

lemma step_spec_abrupt_rel:
  assumes 
 a0:"\<forall>\<sigma>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. \<sigma>n = s \<and> \<sigma>n\<in>Domain \<xi>}) Cc 
        ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>n), ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>a)" and
 a1:"\<forall>\<Sigma>n. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (\<sigma>,  s) \<in> \<xi> } \<inter> bs \<inter> {\<Sigma>n}) Cs 
         {},({s. (Normal  \<Sigma>n, Normal s) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (\<sigma>',\<Sigma>n')\<in> \<gamma>\<^sub>a})" and
 a2:"(\<sigma>, \<Sigma>) \<in> \<xi>" and a3:"\<sigma> \<in> bc" and a4:"\<Sigma>\<in>bs" and
 a5:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Abrupt \<sigma>'" and a6:"\<forall>\<Sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal \<Sigma>\<rangle> \<Rightarrow> Fault f"
shows "\<exists>\<Sigma>'. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal \<Sigma>\<rangle> \<Rightarrow> Abrupt \<Sigma>' \<and> (\<sigma>',\<Sigma>')\<in>\<gamma>\<^sub>a \<and> (Normal \<Sigma>, Normal \<Sigma>')\<in>G\<^sub>s"
proof-
  obtain n where " \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Cc,Normal \<sigma>\<rangle> =n\<Rightarrow> Abrupt \<sigma>'"
    using a5 Semantic.exec_to_execn by fastforce 
  moreover have "\<And>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<Turnstile>n:\<^bsub>/F\<^esub>  
        (bc \<inter> {s. \<sigma> = s \<and> \<sigma>\<in>Domain \<xi>}) Cc 
        ({s. (Normal \<sigma>, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>n), ({s. (Normal \<sigma>, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>a)"
   using a0 a2 a3 hoare_cnvalid by fastforce
  ultimately have "\<sigma>' \<in> Domain \<gamma>\<^sub>a"  unfolding cnvalid_def nvalid_def  
    using a2 a3 a5 by blast
  have " \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (\<sigma>,  s) \<in> \<xi> } \<inter> bs \<inter> {\<Sigma>}) Cs 
         {},({s. (Normal  \<Sigma>, Normal s) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (\<sigma>',\<Sigma>n')\<in> \<gamma>\<^sub>a})"
    using a2 a1 by blast
  then have "\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (\<sigma>,  s) \<in> \<xi> } \<inter> bs \<inter> {\<Sigma>}) Cs 
         {},({s. (Normal  \<Sigma>, Normal s) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (\<sigma>',\<Sigma>n')\<in> \<gamma>\<^sub>a})"
    using hoaret_sound' by blast  
  thus ?thesis  
    using a4 a2 a6 Termination.terminates_implies_exec  unfolding validt_def valid_def
    by fastforce
qed

lemma step_imp_normal_rel:
  assumes 
 a0:"\<forall>\<sigma>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. \<sigma>n = s \<and> \<sigma>n\<in>Domain \<xi>}) Cc 
        ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>n), ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>a)" and
 a1:"\<sigma> \<in>bc \<and> \<sigma>\<in>Domain \<xi>" and
 a2:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Normal \<sigma>'"
shows
 "\<sigma>'\<in> Domain \<gamma>\<^sub>n \<and> (Normal \<sigma>, Normal \<sigma>')\<in> G\<^sub>c"
proof-
 obtain n where " \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Cc,Normal \<sigma>\<rangle> =n\<Rightarrow> Normal \<sigma>'"
    using a2 Semantic.exec_to_execn by fastforce 
  moreover have "\<And>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<Turnstile>n:\<^bsub>/F\<^esub>  
        (bc \<inter> {s. \<sigma> = s \<and> \<sigma>\<in>Domain \<xi>}) Cc 
        ({s. (Normal \<sigma>, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>n), ({s. (Normal \<sigma>, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>a)"
   using a0 a2   hoare_cnvalid by fastforce
  ultimately show ?thesis  unfolding cnvalid_def nvalid_def  
    using a2 a1  by blast
qed

lemma step_imp_normal_rel1:
  assumes 
 a0:"\<forall>\<sigma>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. \<sigma>n = s \<and> \<sigma>n\<in>Domain \<xi>}) Cc 
        ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c} \<inter> p), s" and
 a1:"\<sigma> \<in>bc \<and> \<sigma>\<in>Domain \<xi>" and
 a2:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Normal \<sigma>'"
shows
 "\<sigma>'\<in> p \<and> (Normal \<sigma>, Normal \<sigma>')\<in> G\<^sub>c"
proof-
 obtain n where " \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Cc,Normal \<sigma>\<rangle> =n\<Rightarrow> Normal \<sigma>'"
    using a2 Semantic.exec_to_execn by fastforce 
  moreover have "\<And>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<Turnstile>n:\<^bsub>/F\<^esub>  
        (bc \<inter> {s. \<sigma> = s \<and> \<sigma>\<in>Domain \<xi>}) Cc 
        ({s. (Normal \<sigma>, Normal s) \<in> G\<^sub>c} \<inter> p), s"
   using a0 a2   hoare_cnvalid by fastforce
  ultimately show ?thesis  unfolding cnvalid_def nvalid_def  
    using a2 a1  by blast
qed

lemma step_imp_normal_rel2:
  assumes 
 a0:"\<forall>\<sigma>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. \<sigma>n = s \<and> (\<sigma>n,\<Sigma>)\<in>\<xi>}) Cc 
        ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c} \<inter> p), s" and
 a1:"\<sigma> \<in>bc \<and> (\<sigma>,\<Sigma>)\<in>\<xi>" and
 a2:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Normal \<sigma>'"
shows
 "\<sigma>'\<in> p \<and> (Normal \<sigma>, Normal \<sigma>')\<in> G\<^sub>c"
proof-
 obtain n where " \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Cc,Normal \<sigma>\<rangle> =n\<Rightarrow> Normal \<sigma>'"
    using a2 Semantic.exec_to_execn by fastforce 
  moreover have "\<And>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<Turnstile>n:\<^bsub>/F\<^esub>  
        (bc \<inter> {s. \<sigma> = s \<and> (\<sigma>,\<Sigma>)\<in>\<xi>}) Cc 
        ({s. (Normal \<sigma>, Normal s) \<in> G\<^sub>c} \<inter> p), s"
   using a0 a2   hoare_cnvalid by fastforce
  ultimately show ?thesis  unfolding cnvalid_def nvalid_def  
    using a2 a1  by blast
qed

lemma step_imp_abrupt_rel:
  assumes 
 a0:"\<forall>\<sigma>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. \<sigma>n = s \<and> \<sigma>n\<in>Domain \<xi>}) Cc 
        ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>n), ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>a)" and
 a1:"\<sigma> \<in>bc \<and> \<sigma>\<in>Domain \<xi>" and
 a2:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Abrupt \<sigma>'"
shows
 "\<sigma>'\<in> Domain \<gamma>\<^sub>a \<and> (Normal \<sigma>, Normal \<sigma>')\<in> G\<^sub>c"
proof-
 obtain n where " \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Cc,Normal \<sigma>\<rangle> =n\<Rightarrow> Abrupt \<sigma>'"
    using a2 Semantic.exec_to_execn by fastforce 
  moreover have "\<And>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<Turnstile>n:\<^bsub>/F\<^esub>  
        (bc \<inter> {s. \<sigma> = s \<and> \<sigma>\<in>Domain \<xi>}) Cc 
        ({s. (Normal \<sigma>, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>n), ({s. (Normal \<sigma>, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>a)"
   using a0 a2   hoare_cnvalid by fastforce
  ultimately show ?thesis  unfolding cnvalid_def nvalid_def  
    using a2 a1  by blast
qed


lemma await_sim:assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and  
 a9:"C = Await bc Cc v" and 
 a9': "S = Await bs Cs v" and  
a10:"\<forall>\<sigma>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. \<sigma>n = s \<and> \<sigma>n\<in>Domain \<xi>}) Cc 
        ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>n), ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>a)" and
 a11a:"\<forall>\<sigma>n \<sigma>n'. \<sigma>n \<in>(Domain \<xi> \<inter> bc) \<and> \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a \<turnstile>\<langle>Cc,Normal \<sigma>n\<rangle> \<Rightarrow> Normal \<sigma>n' \<longrightarrow>  
       (\<forall>\<Sigma>n. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (\<sigma>n,  s) \<in> \<xi> } \<inter> bs \<inter> {\<Sigma>n}) Cs 
         ({s. (Normal  \<Sigma>n, Normal s) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (\<sigma>n',\<Sigma>n')\<in> \<gamma>\<^sub>n}),{} )" and 
a11b:"\<forall>\<sigma>n \<sigma>n'. \<sigma>n \<in>(Domain \<xi> \<inter> bc) \<and> \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a \<turnstile>\<langle>Cc,Normal \<sigma>n\<rangle> \<Rightarrow> Abrupt \<sigma>n' \<longrightarrow>  
       (\<forall>\<Sigma>n. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (\<sigma>n,  s) \<in> \<xi> } \<inter> bs \<inter> {\<Sigma>n}) Cs 
         {},({s. (Normal  \<Sigma>n, Normal s) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (\<sigma>n',\<Sigma>n')\<in> \<gamma>\<^sub>a}) )" and 
 a12: "(\<sigma>, \<Sigma>) \<in> \<xi> " and
 a13: "\<xi> \<subseteq> (bc \<rightleftharpoons> bs)" and
 a14:"\<forall>\<Sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal \<Sigma>\<rangle> \<Rightarrow> Fault f" and 
a15: "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (C, Normal \<sigma>) \<rightarrow> (c1, Normal \<sigma>')"
shows "\<exists>c1' \<Sigma>'. 
         (\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
         (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c1', Normal \<Sigma>'))) \<and>
         (\<sigma>', \<Sigma>') \<in> \<alpha> \<and>
         (((Normal \<sigma>, Normal \<sigma>'), Normal \<Sigma>, Normal \<Sigma>') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
        (\<Gamma>\<^sub>c,(c1, Normal \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1', Normal \<Sigma>'),R\<^sub>s,G\<^sub>s)"
proof-
  have v_eq:"v1 = v" using a15 a9
    using label_step by fastforce
  have a12': "\<sigma>\<in>Domain \<xi>" using a12 by auto
  
    then have a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (Await bc Cc v1, Normal \<sigma>) \<rightarrow> (c1, Normal \<sigma>')" using a15 a9  v_eq by auto
    then have "c1 = Skip \<or> c1 = Throw" by (fastforce elim: stepc_normal_elim_cases)   
    then show ?thesis 
    proof
      assume a001:"c1 = Skip"
      then have \<sigma>b:"\<sigma>\<in>bc" and step:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Normal \<sigma>'" 
        using stepc_normal_elim_cases[OF a00]
        by (fast+)
      then have "(\<forall>\<Sigma>n. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (\<sigma>,  s) \<in> \<xi> } \<inter> bs \<inter> {\<Sigma>n}) Cs 
         ({s. (Normal  \<Sigma>n, Normal s) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (\<sigma>',\<Sigma>n')\<in> \<gamma>\<^sub>n}),{} )"
        using a11a a12' by auto
      have \<Sigma>b:"\<Sigma>\<in>bs"  using \<sigma>b a12 a13 same_set by fastforce
      then obtain \<Sigma>' where step_cs:"\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal \<Sigma>\<rangle> \<Rightarrow> Normal \<Sigma>' \<and> (\<sigma>', \<Sigma>') \<in> \<gamma>\<^sub>n \<and> (Normal \<Sigma>, Normal \<Sigma>')\<in>G\<^sub>s"
        using step_spec_normal_rel[OF a10 _ a12 \<sigma>b _ step a14, of bs G\<^sub>s] a11a a12' step \<sigma>b
        by auto
      moreover have " (Normal \<sigma>, Normal \<sigma>')\<in> G\<^sub>c" using step_imp_normal_rel[OF a10 conjI[OF \<sigma>b a12'] step]
        by auto
      then have "((Normal \<sigma>, Normal \<sigma>'), Normal \<Sigma>, Normal \<Sigma>') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>" 
        using calculation(1) a1 a12 a2 unfolding related_transitions_def by fastforce
      moreover have "\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
                          (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, Normal \<Sigma>'))"
        using calculation(1) \<Sigma>b a9' Awaitc[OF \<Sigma>b _] v_eq by fastforce   
      moreover have "(\<Gamma>\<^sub>c,(Skip, Normal \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Skip, Normal \<Sigma>'),R\<^sub>s,G\<^sub>s)"
        using Skip_sim_normal[OF a2 _ a4 _ a6 a7 ] step_cs by blast
      ultimately show ?thesis using a1 a12 a2 a9 a9' a001 by blast
    next
      assume a001:"c1 = Throw"
      then have \<sigma>b:"\<sigma>\<in>bc" and step:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Abrupt \<sigma>'"
        using stepc_normal_elim_cases[OF a00]
        by (fast+)            
      then have "(\<forall>\<Sigma>n. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (\<sigma>,  s) \<in> \<xi> } \<inter> bs \<inter> {\<Sigma>n}) Cs 
         {},({s. (Normal  \<Sigma>n, Normal s) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (\<sigma>',\<Sigma>n')\<in> \<gamma>\<^sub>a}) )"
        using a11b a12' by auto
      have \<Sigma>b:"\<Sigma>\<in>bs"  using \<sigma>b a12 a13 same_set by fastforce
      then obtain \<Sigma>' where step_cs:"\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal \<Sigma>\<rangle> \<Rightarrow> Abrupt \<Sigma>' \<and> (\<sigma>', \<Sigma>') \<in> \<gamma>\<^sub>a \<and> (Normal \<Sigma>, Normal \<Sigma>')\<in>G\<^sub>s"
        using step_spec_abrupt_rel[OF a10 _ a12 \<sigma>b _ step a14, of bs G\<^sub>s] a11b a12' step \<sigma>b
        by auto
      moreover have " (Normal \<sigma>, Normal \<sigma>')\<in> G\<^sub>c" using step_imp_abrupt_rel[OF a10 conjI[OF \<sigma>b a12'] step]
        by auto
      then have "((Normal \<sigma>, Normal \<sigma>'), Normal \<Sigma>, Normal \<Sigma>') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>" 
        using calculation(1) a1 a12 a2' unfolding related_transitions_def by fastforce
      moreover have "\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
                          (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, Normal \<Sigma>'))"
        using calculation(1) \<Sigma>b a9' AwaitAbruptc[OF \<Sigma>b _] v_eq by fastforce      
      moreover have "(\<Gamma>\<^sub>c,(Throw, Normal \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Throw, Normal \<Sigma>'),R\<^sub>s,G\<^sub>s)"
        using Throw_sim_normal[OF a2' _ a5 _ a6 a7 ] step_cs by blast 
      ultimately show ?thesis using a1 a12 a2' a9 a9' a001 by blast    
    qed 
  qed

lemma Step_Await_not_normal: assumes a0:"\<forall>\<sigma>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}
          \<turnstile>\<^bsub>/F \<^esub>(bc \<inter> {s. \<sigma>n = s \<and> \<sigma>n \<in> Domain \<xi>}) Cc ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>n),
                 ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>a)" and 
      a1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (Await bc Cc v, Normal \<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>')" and
      a2:"\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n" and a3:"(\<sigma>, \<Sigma>) \<in> \<xi>" and  a03:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Fault f"
    shows "P"
proof-
  
  have bc:"\<sigma>\<in>bc \<and> \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> \<sigma>' \<and> (\<forall>t'. \<sigma>' \<noteq> Abrupt t') " 
    using  stepc_elim_cases1(8)[OF a1] a2  by fastforce
  moreover have a0:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}
          \<turnstile>\<^bsub>/F \<^esub>(bc \<inter> {s. \<sigma> = s \<and> \<sigma> \<in> Domain \<xi>}) Cc ({s. (Normal \<sigma>, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>n),
                 ({s. (Normal \<sigma>, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>a)"
    using a3 a0 by auto  
  obtain n where  step:" \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Cc,Normal \<sigma>\<rangle> =n\<Rightarrow>  \<sigma>'"
    using a0 bc Semantic.exec_to_execn by fastforce 
  moreover have val:"\<And>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<Turnstile>n:\<^bsub>/F\<^esub>  
        (bc \<inter> {s. \<sigma> = s \<and> \<sigma>\<in>Domain \<xi>}) Cc 
        ({s. (Normal \<sigma>, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>n), ({s. (Normal \<sigma>, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>a)"
    using a0 a2 a3 hoare_cnvalid by fastforce
  have   
   "\<exists>\<sigma>n'. \<sigma>' = Abrupt \<sigma>n' \<and> \<sigma>n'\<in> Domain \<gamma>\<^sub>a \<and> (Normal \<sigma>, Normal \<sigma>n')\<in> G\<^sub>c" 
    using a2 val bc a3 step a03 unfolding cnvalid_def nvalid_def 
    by (cases \<sigma>', fast+) 
  thus ?thesis  using bc   by auto 
qed


lemma mod_state_Await_sound: 
  assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c"   and a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x"  and
 a9:"C = Await bc Cc v" and 
 a9': "S = Await bs Cs v" and  
a10:"\<forall>\<sigma>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. \<sigma>n = s \<and> \<sigma>n\<in>Domain \<xi>}) Cc 
        ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>n), ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c} \<inter> Domain \<gamma>\<^sub>a)" and
 a11a:"\<forall>\<sigma>n \<sigma>n'. \<sigma>n \<in>(Domain \<xi> \<inter> bc) \<and> \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a \<turnstile>\<langle>Cc,Normal \<sigma>n\<rangle> \<Rightarrow> Normal \<sigma>n' \<longrightarrow>  
       (\<forall>\<Sigma>n. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (\<sigma>n,  s) \<in> \<xi> } \<inter> bs \<inter> {\<Sigma>n}) Cs 
         ({s. (Normal  \<Sigma>n, Normal s) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (\<sigma>n',\<Sigma>n')\<in> \<gamma>\<^sub>n}),{} )" and 
a11b:"\<forall>\<sigma>n \<sigma>n'. \<sigma>n \<in>(Domain \<xi> \<inter> bc) \<and> \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a \<turnstile>\<langle>Cc,Normal \<sigma>n\<rangle> \<Rightarrow> Abrupt \<sigma>n' \<longrightarrow>  
       (\<forall>\<Sigma>n. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (\<sigma>n,  s) \<in> \<xi> } \<inter> bs \<inter> {\<Sigma>n}) Cs 
         {},({s. (Normal  \<Sigma>n, Normal s) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (\<sigma>n',\<Sigma>n')\<in> \<gamma>\<^sub>a}) )"  and a13: "\<xi> \<subseteq> (bc \<rightleftharpoons> bs)" and
a14:"\<forall>\<Sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal \<Sigma>\<rangle> \<Rightarrow> Fault f" and a15:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Fault f"
shows "(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)"    
proof-
  {fix \<sigma> \<Sigma> 
    assume a11: "(\<sigma>, \<Sigma>) \<in> \<xi>"   
    then have "(\<Gamma>\<^sub>c,(C, Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal \<Sigma>),R\<^sub>s,G\<^sub>s)" 
     apply (coinduction arbitrary: \<sigma> \<Sigma>)
      
      apply clarsimp
      apply (rule conjId)+ 
             apply (auto simp add: a9)
           apply (auto intro: Step_Await_not_normal[OF a10 _ _ _ a15, where v=v])  
          apply (blast dest: sim_env[OF _ a3 a6 a7])
         apply (frule await_sim[OF a1 a2 a2' a3 a4 a5 a6 a7  a9 a9' a10 a11a a11b _ a13 a14, simplified a9], fast+)
        apply (frule await_sim[OF a1 a2 a2' a3 a4 a5 a6 a7  a9 a9' a10 a11a a11b _ a13 a14, simplified a9], auto)
      using intro_tau_step apply fast
      using a1 unfolding alpha_xstate_def by auto
  }  then show ?thesis unfolding RGSim_pre_def  by auto
qed 

lemma basic_await_sim:assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and 
  a9:"C = Basic fc v" and 
 a9': "S = Await bs Cs v" and  
 a11:"\<forall>\<sigma>n \<sigma>n' \<Sigma>n. (\<sigma>n, \<Sigma>n)\<in>\<xi> \<and> Normal \<sigma>n' \<in> com_step  C (Normal \<sigma>n)  \<Gamma>\<^sub>c \<longrightarrow>  
       (\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (\<sigma>n,  s) \<in> \<xi> } \<inter> bs \<inter> {\<Sigma>n}) Cs 
         ({s. (Normal  \<Sigma>n, Normal s) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (\<sigma>n',\<Sigma>n')\<in> \<gamma>\<^sub>n}),{} )" and 
 a12: "(\<sigma>, \<Sigma>) \<in> \<xi> " and  a13:"Range \<xi> \<subseteq> bs" and 
a14:"\<forall>\<Sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal \<Sigma>\<rangle> \<Rightarrow> Fault f" and 
a15: "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (C, Normal \<sigma>) \<rightarrow> (c1, Normal \<sigma>')" and
a16:"(Normal \<sigma>, Normal (fc \<sigma>))\<in>G\<^sub>c" 
shows "\<exists>c1' \<Sigma>'. 
         (\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
         (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c1', Normal \<Sigma>'))) \<and>
         (\<sigma>', \<Sigma>') \<in> \<alpha> \<and>
         (((Normal \<sigma>, Normal \<sigma>'), Normal \<Sigma>, Normal \<Sigma>') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
        (\<Gamma>\<^sub>c,(c1, Normal \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1', Normal \<Sigma>'),R\<^sub>s,G\<^sub>s)"
proof-
  have v_eq:"v1 = v" using a15 a9
    using label_step by fastforce
  have a12': "\<sigma>\<in>Domain \<xi>" using a12 by auto
  have \<Sigma>inbs: "\<Sigma>\<in>bs" using a13 a12 by auto
  then have a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (Basic fc v, Normal \<sigma>) \<rightarrow> (c1, Normal \<sigma>')" using a15 a9  v_eq by auto
  then have c1:"c1 = Skip" and \<sigma>:"\<sigma>' = fc \<sigma>"
    apply  (fastforce elim: stepc_normal_elim_cases)
    by (meson a00 old.prod.inject stepc_Normal_elim_cases(3) stepce_stepc xstate.inject(1))   
  then have " Normal \<sigma>' \<in> com_step  C (Normal \<sigma>)  \<Gamma>\<^sub>c" using a9 by auto
  then have " \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (\<sigma>,  s) \<in> \<xi> } \<inter> bs \<inter> {\<Sigma>}) Cs 
         ({s. (Normal  \<Sigma>, Normal s) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (\<sigma>',\<Sigma>n')\<in> \<gamma>\<^sub>n}), {}"
    using a12 a11 by blast
  then have "\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (\<sigma>,  s) \<in> \<xi> } \<inter> bs \<inter> {\<Sigma>}) Cs 
        ({s. (Normal  \<Sigma>, Normal s) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (\<sigma>',\<Sigma>n')\<in> \<gamma>\<^sub>n}), {}"
    using hoaret_sound' by blast  
  moreover have \<Sigma>b:"\<Sigma>\<in>bs"  using  a12 a13 by fastforce
  ultimately obtain \<Sigma>' where step_cs:"\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal \<Sigma>\<rangle> \<Rightarrow> Normal \<Sigma>' \<and> (\<sigma>', \<Sigma>') \<in> \<gamma>\<^sub>n \<and> (Normal \<Sigma>, Normal \<Sigma>')\<in>G\<^sub>s"
    using a12 a14 Termination.terminates_implies_exec  unfolding validt_def valid_def
    by blast    
  moreover have " (Normal \<sigma>, Normal \<sigma>')\<in> G\<^sub>c" using a16 \<sigma>
      by auto
  then have "((Normal \<sigma>, Normal \<sigma>'), Normal \<Sigma>, Normal \<Sigma>') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>" 
      using calculation(1) a1 a12 a2 unfolding related_transitions_def by fastforce
    moreover have "\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
                        (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, Normal \<Sigma>'))"
      using calculation(1) \<Sigma>b a9' Awaitc[OF \<Sigma>b _] v_eq by fastforce   
    moreover have "(\<Gamma>\<^sub>c,(Skip, Normal \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Skip, Normal \<Sigma>'),R\<^sub>s,G\<^sub>s)"
      using Skip_sim_normal[OF a2 _ a4 _ a6 a7 ] step_cs by blast
    ultimately show ?thesis using a1 a12 a2 a9 a9' c1  by fast
qed 

lemma spec_await_sim:assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and  
 a9: "C = Spec f v" and  a9': "S = Await bs Cs v" and 
 a11:"\<forall>\<sigma>n \<sigma>n' \<Sigma>n. (\<sigma>n, \<Sigma>n)\<in>\<xi> \<and> Normal \<sigma>n' \<in> com_step  C (Normal \<sigma>n)  \<Gamma>\<^sub>c \<longrightarrow>  
       (\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (\<sigma>n,  s) \<in> \<xi> } \<inter> bs \<inter> {\<Sigma>n}) Cs 
         ({s. (Normal  \<Sigma>n, Normal s) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (\<sigma>n',\<Sigma>n')\<in> \<gamma>\<^sub>n}),{} )" and 
 a12: "(\<sigma>, \<Sigma>) \<in> \<xi> " and  a13:"Range \<xi> \<subseteq> bs" and 
a14:"\<forall>\<Sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal \<Sigma>\<rangle> \<Rightarrow> Fault f" and 
a15: "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (C, Normal \<sigma>) \<rightarrow> (c1, Normal \<sigma>')" and
a16:"\<forall>\<sigma>'. (\<sigma>,\<sigma>')\<in>f \<longrightarrow> (Normal \<sigma>, Normal \<sigma>')\<in>G\<^sub>c" 
shows "\<exists>c1' \<Sigma>'. 
         (\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
         (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c1', Normal \<Sigma>'))) \<and>
         (\<sigma>', \<Sigma>') \<in> \<alpha> \<and>
         (((Normal \<sigma>, Normal \<sigma>'), Normal \<Sigma>, Normal \<Sigma>') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
        (\<Gamma>\<^sub>c,(c1, Normal \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1', Normal \<Sigma>'),R\<^sub>s,G\<^sub>s)"
proof-
  have v_eq:"v1 = v" using a15 a9
    using label_step by fastforce
  have a12': "\<sigma>\<in>Domain \<xi>" using a12 by auto
  have \<Sigma>inbs: "\<Sigma>\<in>bs" using a13 a12 by auto
  then have a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (Spec f v, Normal \<sigma>) \<rightarrow> (c1, Normal \<sigma>')" using a15 a9  v_eq by auto
  then have c1:"c1 = Skip" and \<sigma>:"(\<sigma>,\<sigma>')\<in>f"
    apply  (fastforce elim: stepc_normal_elim_cases)
    using CRef.stepc_elim_cases(2) a00 spec_skip stepce_stepc by fastforce    
  then have " Normal \<sigma>' \<in> com_step  C (Normal \<sigma>)  \<Gamma>\<^sub>c" using a9 by auto
  then have " \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (\<sigma>,  s) \<in> \<xi> } \<inter> bs \<inter> {\<Sigma>}) Cs 
         ({s. (Normal  \<Sigma>, Normal s) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (\<sigma>',\<Sigma>n')\<in> \<gamma>\<^sub>n}), {}"
    using a12 a11 by blast
  then have "\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (\<sigma>,  s) \<in> \<xi> } \<inter> bs \<inter> {\<Sigma>}) Cs 
        ({s. (Normal  \<Sigma>, Normal s) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (\<sigma>',\<Sigma>n')\<in> \<gamma>\<^sub>n}), {}"
    using hoaret_sound' by blast  
  moreover have \<Sigma>b:"\<Sigma>\<in>bs"  using  a12 a13 by fastforce
  ultimately obtain \<Sigma>' where step_cs:"\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal \<Sigma>\<rangle> \<Rightarrow> Normal \<Sigma>' \<and> (\<sigma>', \<Sigma>') \<in> \<gamma>\<^sub>n \<and> (Normal \<Sigma>, Normal \<Sigma>')\<in>G\<^sub>s"
    using a12 a14 Termination.terminates_implies_exec  unfolding validt_def valid_def
    by blast    
  moreover have " (Normal \<sigma>, Normal \<sigma>')\<in> G\<^sub>c" using a16 \<sigma>
      by auto
  then have "((Normal \<sigma>, Normal \<sigma>'), Normal \<Sigma>, Normal \<Sigma>') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>" 
      using calculation(1) a1 a12 a2 unfolding related_transitions_def by fastforce
    moreover have "\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
                        (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, Normal \<Sigma>'))"
      using calculation(1) \<Sigma>b a9' Awaitc[OF \<Sigma>b _] v_eq by fastforce   
    moreover have "(\<Gamma>\<^sub>c,(Skip, Normal \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Skip, Normal \<Sigma>'),R\<^sub>s,G\<^sub>s)"
      using Skip_sim_normal[OF a2 _ a4 _ a6 a7] step_cs by blast
    ultimately show ?thesis using a1 a12 a2 a9 a9' c1  by fast
qed 

lemma basic_spec_await_sim:assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and 
  a9:"C = Basic fc v \<or> C = Spec rc v" and 
 a9': "S = Await bs Cs v" and  
 a10:"\<forall>\<sigma>n\<in>Domain \<xi>. \<forall>\<sigma>n'. (Normal \<sigma>n') \<in> com_step C (Normal \<sigma>n) \<Gamma>\<^sub>c \<longrightarrow> (Normal \<sigma>n, Normal \<sigma>n')\<in>G\<^sub>c" and
 a11:"\<forall>\<sigma>n \<sigma>n' \<Sigma>n. (\<sigma>n, \<Sigma>n)\<in>\<xi> \<and> Normal \<sigma>n' \<in> com_step  C (Normal \<sigma>n)  \<Gamma>\<^sub>c \<longrightarrow>  
       (\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (\<sigma>n,  s) \<in> \<xi> } \<inter> bs \<inter> {\<Sigma>n}) Cs 
         ({s. (Normal  \<Sigma>n, Normal s) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (\<sigma>n',\<Sigma>n')\<in> \<gamma>\<^sub>n}),{} )" and 
a12:"\<forall>\<Sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal \<Sigma>\<rangle> \<Rightarrow> Fault f" and
 a13: "(\<sigma>, \<Sigma>) \<in> \<xi> " and  a14:"Range \<xi> \<subseteq> bs" and
a15: "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (C, Normal \<sigma>) \<rightarrow> (c1, Normal \<sigma>')"
shows "\<exists>c1' \<Sigma>'. 
         (\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
         (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c1', Normal \<Sigma>'))) \<and>
         (\<sigma>', \<Sigma>') \<in> \<alpha> \<and>
         (((Normal \<sigma>, Normal \<sigma>'), Normal \<Sigma>, Normal \<Sigma>') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
        (\<Gamma>\<^sub>c,(c1, Normal \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1', Normal \<Sigma>'),R\<^sub>s,G\<^sub>s)"
proof-
  have a12': "\<sigma>\<in>Domain \<xi>" using a13 by auto  
  then show ?thesis 
    using a9 a10  basic_await_sim[OF a1 a2 a2' a3 a4 a5 a6 a7  _ a9' a11 a13 a14 a12 a15] 
              spec_await_sim[OF a1 a2 a2' a3 a4 a5 a6 a7  _ a9' a11 a13 a14 a12 a15]
    by auto
qed

lemma Step_Basic_Spec_not_normal: 
  assumes a0:"C = Basic fc v \<or> C = Spec rc v" and 
      a1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (C, Normal \<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>')" and
      a2:"\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n" and a3:"(\<sigma>, \<Sigma>) \<in> \<xi>" and
      a4:"\<forall>\<sigma>\<in>Domain \<xi>. \<exists>\<sigma>'. (\<sigma>,\<sigma>')\<in>rc"
    shows "P"
proof-
  {assume a00: "C = Basic fc v"
    then have ?thesis using a1 a2
      by (meson Pair_inject stepc_Normal_elim_cases(3) stepce_stepc)
  }
  moreover { 
    assume a00: "C = Spec rc v"
    then have ?thesis using a4 a3 a1 a2
      by (meson Domain.DomainI Pair_inject stepc_Normal_elim_cases(4) stepce_stepc)
  }
  ultimately show ?thesis using a0 by auto 
qed

lemma mod_state_Await_Spec_Sim: 
  assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c"   and a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and 
 a9:"C = Basic fc v \<or> C = Spec rc v" and 
 a9': "S = Await bs Cs v" and  
 a10:"\<forall>\<sigma>n\<in>Domain \<xi>. \<forall>\<sigma>n'. Normal \<sigma>n' \<in> com_step C (Normal \<sigma>n) \<Gamma>\<^sub>c \<longrightarrow> (Normal \<sigma>n, Normal \<sigma>n') \<in> G\<^sub>c" and
 a11:"\<forall>\<sigma>n \<sigma>n' \<Sigma>n. (\<sigma>n, \<Sigma>n)\<in>\<xi> \<and> Normal \<sigma>n' \<in> com_step  C (Normal \<sigma>n)  \<Gamma>\<^sub>c \<longrightarrow>  
       (\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (\<sigma>n,  s) \<in> \<xi> } \<inter> bs \<inter> {\<Sigma>n}) Cs 
         ({s. (Normal  \<Sigma>n, Normal s) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (\<sigma>n',\<Sigma>n')\<in> \<gamma>\<^sub>n}),{} )" and 
a12:"\<forall>\<Sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal \<Sigma>\<rangle> \<Rightarrow> Fault f" and a13:"Range \<xi> \<subseteq> bs" and
 a14:"\<forall>\<sigma>\<in>Domain \<xi>. \<exists>\<sigma>'. (\<sigma>,\<sigma>')\<in>rc"
shows "(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)"    
proof-
  {fix \<sigma> \<Sigma> 
    assume a15: "(\<sigma>, \<Sigma>) \<in> \<xi>"   
    then have "(\<Gamma>\<^sub>c,(C, Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal \<Sigma>),R\<^sub>s,G\<^sub>s)" 
     apply (coinduction arbitrary: \<sigma> \<Sigma>)
      
      apply clarsimp
      apply (rule conjId)+ 
      
             apply (auto intro: Step_Basic_Spec_not_normal[OF a9 _ _ _ a14])      
      using a9 apply simp using a9 apply simp  
          apply (blast dest: sim_env[OF _ a3 a6 a7])
         apply (frule basic_spec_await_sim[OF a1 a2 a2' a3 a4 a5 a6 a7  a9 a9' a10 a11 a12 _ a13], fast+)
      apply (frule basic_spec_await_sim[OF a1 a2 a2' a3 a4 a5 a6 a7  a9 a9' a10 a11 a12 _ a13], fast+)        
      using intro_tau_step apply fast
      using a1 unfolding alpha_xstate_def by auto
  }  then show ?thesis unfolding RGSim_pre_def  by auto
qed 

lemma await_basic_sim:assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and   
 a9:"C = Await bc Cc v" and  
a9': "S = Basic fc v" and
a10:"\<forall>\<sigma>n \<Sigma>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. \<sigma>n = s \<and> (\<sigma>n,\<Sigma>n)\<in>\<xi>}) Cc 
        ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c} \<inter> {s1. \<exists>\<Sigma>n'. Normal \<Sigma>n' \<in> com_step S (Normal \<Sigma>n) \<Gamma>\<^sub>c \<and> 
                                                 (s1, \<Sigma>n')\<in> \<gamma>\<^sub>n \<and> 
                                                (Normal \<Sigma>n, Normal \<Sigma>n') \<in> G\<^sub>s}), {}"  and
a12: "(\<sigma>, \<Sigma>) \<in> \<xi> " and  a13:"Domain \<xi> \<subseteq> bc" and 
a15: "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (C, Normal \<sigma>) \<rightarrow> (c1, Normal \<sigma>')" 
shows "\<exists>c1' \<Sigma>'. 
         (\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
         (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c1', Normal \<Sigma>'))) \<and>
         (\<sigma>', \<Sigma>') \<in> \<alpha> \<and>
         (((Normal \<sigma>, Normal \<sigma>'), Normal \<Sigma>, Normal \<Sigma>') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
        (\<Gamma>\<^sub>c,(c1, Normal \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1', Normal \<Sigma>'),R\<^sub>s,G\<^sub>s)"
proof-
  have v_eq:"v1 = v" using a15 a9
    using label_step by fastforce
  have a12': "\<sigma>\<in>Domain \<xi>" using a12 by auto
  have \<sigma>inbs: "\<sigma>\<in>bc" using a13 a12 by auto
  then have a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (Await bc Cc v, Normal \<sigma>) \<rightarrow> (c1, Normal \<sigma>')" using a15 a9  v_eq by auto
  then have c1:"c1 = Skip \<or> c1=Throw" 
    by  (fastforce elim: stepc_elim_cases1(8))
  {assume cSkip:"c1 = Skip"
   then have  \<sigma>:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Normal \<sigma>'"
     using a00 CRef.stepc_elim_cases1(8) a00 spec_skip stepce_stepc by fastforce
   then have a10:"\<forall>\<sigma>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. \<sigma>n = s \<and> (\<sigma>n,\<Sigma>)\<in>\<xi>}) Cc 
        ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c} \<inter> {s1. \<exists>\<Sigma>n'. Normal \<Sigma>n' \<in> com_step S (Normal \<Sigma>) \<Gamma>\<^sub>c \<and> 
                                                 (s1, \<Sigma>n')\<in> \<gamma>\<^sub>n \<and> 
                                                (Normal \<Sigma>, Normal \<Sigma>n') \<in> G\<^sub>s}), {}"
     using a10 by auto
   then obtain \<Sigma>n' where step_cs:"Normal \<Sigma>n' \<in> com_step S (Normal \<Sigma>) \<Gamma>\<^sub>c \<and> 
                           (\<sigma>', \<Sigma>n')\<in> \<gamma>\<^sub>n \<and> 
                          (Normal \<Sigma>, Normal \<Sigma>n') \<in> G\<^sub>s \<and> (Normal \<sigma>, Normal \<sigma>')\<in> G\<^sub>c"     
     using step_imp_normal_rel2[OF _ _ \<sigma>, of F bc \<Sigma> \<xi> G\<^sub>c "{s1. \<exists>\<Sigma>n'. Normal \<Sigma>n' \<in> com_step S (Normal \<Sigma>) \<Gamma>\<^sub>c \<and> 
                                                 (s1, \<Sigma>n')\<in> \<gamma>\<^sub>n \<and> 
                                                (Normal \<Sigma>, Normal \<Sigma>n') \<in> G\<^sub>s}" "{}"] a12 \<sigma>inbs 
     by auto   
   then have "((Normal \<sigma>, Normal \<sigma>'), Normal \<Sigma>, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>" 
      using  a1 a12 a2 unfolding related_transitions_def by fastforce
   moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (Basic fc v, Normal \<Sigma>) \<rightarrow> (Skip, Normal \<Sigma>n')" 
     using Basicc v_eq a9' step_cs by auto
   then have "\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
                        (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, Normal \<Sigma>n'))"
     using a9' by fastforce
   moreover have "(\<Gamma>\<^sub>c,(c1, Normal \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Skip, Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)"
      using Skip_sim_normal[OF a2 _ a4 _ a6 a7 ] step_cs cSkip by blast
    ultimately have ?thesis using a2 step_cs by blast
  }
  moreover {
    assume cSkip:"c1 = Throw"
    then have  \<sigma>:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Abrupt \<sigma>'"
      using a00 CRef.stepc_elim_cases1(8) a00 spec_skip stepce_stepc by fastforce
    then have ?thesis using in_normal_not_abrupt [OF _ \<sigma>] \<sigma>inbs a12 a10 by blast
  } 
  ultimately show ?thesis using c1 by auto
qed 

lemma await_spec_sim:assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and    
a9:"C = Await bc Cc v" and  
a9': "S = Spec rc v" and
a10:"\<forall>\<sigma>n \<Sigma>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. \<sigma>n = s \<and> (\<sigma>n,\<Sigma>n)\<in>\<xi>}) Cc 
        ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c} \<inter> {s1. \<exists>\<Sigma>n'. Normal \<Sigma>n' \<in> com_step S (Normal \<Sigma>n) \<Gamma>\<^sub>c \<and> 
                                                 (s1, \<Sigma>n')\<in> \<gamma>\<^sub>n \<and> 
                                                (Normal \<Sigma>n, Normal \<Sigma>n') \<in> G\<^sub>s}), {}"  and
a12: "(\<sigma>, \<Sigma>) \<in> \<xi> " and  a13:"Domain \<xi> \<subseteq> bc" and 
a15: "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (C, Normal \<sigma>) \<rightarrow> (c1, Normal \<sigma>')" 
shows "\<exists>c1' \<Sigma>'. 
         (\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
         (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c1', Normal \<Sigma>'))) \<and>
         (\<sigma>', \<Sigma>') \<in> \<alpha> \<and>
         (((Normal \<sigma>, Normal \<sigma>'), Normal \<Sigma>, Normal \<Sigma>') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
        (\<Gamma>\<^sub>c,(c1, Normal \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1', Normal \<Sigma>'),R\<^sub>s,G\<^sub>s)"
proof-
  have v_eq:"v1 = v" using a15 a9
    using label_step by fastforce
  have a12': "\<sigma>\<in>Domain \<xi>" using a12 by auto
  have \<sigma>inbs: "\<sigma>\<in>bc" using a13 a12 by auto
  then have a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (Await bc Cc v, Normal \<sigma>) \<rightarrow> (c1, Normal \<sigma>')" using a15 a9  v_eq by auto
  then have c1:"c1 = Skip \<or> c1=Throw" 
    by  (fastforce elim: stepc_elim_cases1(8))
  {assume cSkip:"c1 = Skip"
   then have  \<sigma>:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Normal \<sigma>'"
     using a00 CRef.stepc_elim_cases1(8) a00 spec_skip stepce_stepc by fastforce
   then have a10:"\<forall>\<sigma>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. \<sigma>n = s \<and> (\<sigma>n,\<Sigma>)\<in>\<xi>}) Cc 
        ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c} \<inter> {s1. \<exists>\<Sigma>n'. Normal \<Sigma>n' \<in> com_step S (Normal \<Sigma>) \<Gamma>\<^sub>c \<and> 
                                                 (s1, \<Sigma>n')\<in> \<gamma>\<^sub>n \<and> 
                                                (Normal \<Sigma>, Normal \<Sigma>n') \<in> G\<^sub>s}), {}"
     using a10 by auto
   then obtain \<Sigma>n' where step_cs:"Normal \<Sigma>n' \<in> com_step S (Normal \<Sigma>) \<Gamma>\<^sub>c \<and> 
                           (\<sigma>', \<Sigma>n')\<in> \<gamma>\<^sub>n \<and> 
                          (Normal \<Sigma>, Normal \<Sigma>n') \<in> G\<^sub>s \<and> (Normal \<sigma>, Normal \<sigma>')\<in> G\<^sub>c"     
     using step_imp_normal_rel2[OF _ _ \<sigma>, of F bc \<Sigma> \<xi> G\<^sub>c "{s1. \<exists>\<Sigma>n'. Normal \<Sigma>n' \<in> com_step S (Normal \<Sigma>) \<Gamma>\<^sub>c \<and> 
                                                 (s1, \<Sigma>n')\<in> \<gamma>\<^sub>n \<and> 
                                                (Normal \<Sigma>, Normal \<Sigma>n') \<in> G\<^sub>s}" "{}"] a12 \<sigma>inbs 
     by auto   
   then have "((Normal \<sigma>, Normal \<sigma>'), Normal \<Sigma>, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>" 
      using  a1 a12 a2 unfolding related_transitions_def by fastforce
   moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (Spec rc v, Normal \<Sigma>) \<rightarrow> (Skip, Normal \<Sigma>n')" 
     using Specc v_eq a9' step_cs by auto
   then have "\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
                        (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, Normal \<Sigma>n'))"
     using a9' by fastforce
   moreover have "(\<Gamma>\<^sub>c,(c1, Normal \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Skip, Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)"
      using Skip_sim_normal[OF a2 _ a4 _ a6 a7] step_cs cSkip by blast
    ultimately have ?thesis using a2 step_cs by blast
  }
  moreover {
    assume cSkip:"c1 = Throw"
    then have  \<sigma>:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Abrupt \<sigma>'"
      using a00 CRef.stepc_elim_cases1(8) a00 spec_skip stepce_stepc by fastforce
    then have ?thesis using in_normal_not_abrupt [OF _ \<sigma>] \<sigma>inbs a12 a10 by blast
  } 
  ultimately show ?thesis using c1 by auto
qed 

lemma await_basic_spec_sim:assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and 
a9:"C = Await bc Cc v" and    
a9':"S = Basic fc v \<or> S = Spec rc v" and  
a10:"\<forall>\<sigma>n \<Sigma>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. \<sigma>n = s \<and> (\<sigma>n,\<Sigma>n)\<in>\<xi>}) Cc 
        ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c} \<inter> {s1. \<exists>\<Sigma>n'. Normal \<Sigma>n' \<in> com_step S (Normal \<Sigma>n) \<Gamma>\<^sub>c \<and> 
                                                 (s1, \<Sigma>n')\<in> \<gamma>\<^sub>n \<and> 
                                                (Normal \<Sigma>n, Normal \<Sigma>n') \<in> G\<^sub>s}), {}"  and
a12: "(\<sigma>, \<Sigma>) \<in> \<xi> " and  a13:"Domain \<xi> \<subseteq> bc" and 
a15: "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (C, Normal \<sigma>) \<rightarrow> (c1, Normal \<sigma>')" 
shows "\<exists>c1' \<Sigma>'. 
         (\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
         (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c1', Normal \<Sigma>'))) \<and>
         (\<sigma>', \<Sigma>') \<in> \<alpha> \<and>
         (((Normal \<sigma>, Normal \<sigma>'), Normal \<Sigma>, Normal \<Sigma>') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
        (\<Gamma>\<^sub>c,(c1, Normal \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1', Normal \<Sigma>'),R\<^sub>s,G\<^sub>s)"
proof-
  have a12': "\<sigma>\<in>Domain \<xi>" using a12 by auto  
  then show ?thesis 
    using a9'  await_basic_sim[OF a1 a2 a2' a3 a4 a5 a6 a7  a9 _ a10 a12 a13 a15] 
              await_spec_sim[OF a1 a2 a2' a3 a4 a5 a6 a7  a9 _ a10 a12 a13 a15]
    by auto
qed

lemma Step_Await_not_normal1: 
  assumes  
      a1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (Await bc Cc v, Normal \<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>')" and
      a2:"\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n" and a3:"(\<sigma>, \<Sigma>) \<in> \<xi>" and
      a4:"\<forall>\<sigma>n \<Sigma>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. \<sigma>n = s \<and> (\<sigma>n,\<Sigma>n)\<in>\<xi>}) Cc 
        ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c} \<inter> {s1. \<exists>\<Sigma>n'. Normal \<Sigma>n' \<in> com_step S (Normal \<Sigma>n) \<Gamma>\<^sub>c \<and> 
                                                 (s1, \<Sigma>n')\<in> \<gamma>\<^sub>n \<and> 
                                                (Normal \<Sigma>n, Normal \<Sigma>n') \<in> G\<^sub>s}), {}" and a5:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Fault f"
    shows "P"
proof-
  have step: "\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow>  \<sigma>' \<and> \<sigma>\<in>bc" 
    using a1 a2
    by (metis Pair_inject stepc_Normal_elim_cases(8) stepce_stepc)   
  thus ?thesis using not_normal_false[OF spec[OF spec[OF a4]] _ a2, of \<sigma>] a3 a5 by auto
qed

lemma mod_state_Await_Impl_Sim: 
  assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c"   and a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and 
 a9:"C = Await bc Cc v" and    
a9':"S = Basic fc v \<or> S = Spec rc v" and  
a10:"\<forall>\<sigma>n \<Sigma>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. \<sigma>n = s \<and> (\<sigma>n,\<Sigma>n)\<in>\<xi>}) Cc 
        ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c} \<inter> {s1. \<exists>\<Sigma>n'. Normal \<Sigma>n' \<in> com_step S (Normal \<Sigma>n) \<Gamma>\<^sub>c \<and> 
                                                 (s1, \<Sigma>n')\<in> \<gamma>\<^sub>n \<and> 
                                                (Normal \<Sigma>n, Normal \<Sigma>n') \<in> G\<^sub>s}), {}"  and
a13:"Domain \<xi> \<subseteq> bc" and  
a12:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Fault f" 
shows "(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)"    
proof-
  {fix \<sigma> \<Sigma> 
    assume a15: "(\<sigma>, \<Sigma>) \<in> \<xi>"   
    then have "(\<Gamma>\<^sub>c,(C, Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal \<Sigma>),R\<^sub>s,G\<^sub>s)" 
     apply (coinduction arbitrary: \<sigma> \<Sigma>)
      
      apply clarsimp
      apply (rule conjId)+       
      using a9 apply (auto intro: Step_Await_not_normal1[OF _ _  _ a10 a12])    
      using a9 apply simp using a9 apply simp  
          apply (blast dest: sim_env[OF _ a3 a6 a7])
         apply (frule await_basic_spec_sim[OF a1 a2 a2' a3 a4 a5 a6 a7  a9 a9' a10 _ a13], fast+)
       apply (frule await_basic_spec_sim[OF a1 a2 a2' a3 a4 a5 a6 a7 a9 a9' a10 _ a13], fast+)        
      using intro_tau_step apply fast
      using a1 unfolding alpha_xstate_def by auto
  }  then show ?thesis unfolding RGSim_pre_def  by auto
qed

lemma Impl_Skip_sim1:
  assumes a0:"(\<sigma>, \<Sigma>) \<in> \<xi>" and
       a2:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (LanguageCon.com.Seq LanguageCon.com.Skip C, Normal \<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>')" and
       a3:"(\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n)" 
   shows
         "\<exists>\<Sigma>'. (\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x \<and>
             (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<or>
                      (\<exists>v. e = Some v \<and>
                           (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                                  (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, b) \<rightarrow> (aa, ba) \<and>
                                           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'))))) \<and> (Normal \<sigma>,\<sigma>')\<in>G\<^sub>c \<and>
                     (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s))"
  using a2 a3
  by (meson SmallStepCon.stepc_elim_cases(1) prod.inject stepc_Normal_elim_cases(5) stepce_stepc)

lemma Impl_Skip_sim2: 
  assumes  
 a0:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and
 a3: "(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)" and
 a4:"(\<sigma>, \<Sigma>) \<in> \<xi>" and
 a5:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Seq LanguageCon.com.Skip C, Normal \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n')"
shows "\<exists>c\<^sub>s' \<Sigma>n'.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
          (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
          (((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          (c\<^sub>c' = LanguageCon.com.Seq LanguageCon.com.Skip C \<and> c\<^sub>s' = S \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))"
proof -
  have "c\<^sub>c' = C" and "\<sigma>n' = \<sigma>"using a5
     apply (metis SmallStepCon.stepc_elim_cases(1) prod.sel(1) stepc_elim_cases_Seq_skip(1) stepce_stepc)
    by (metis (no_types) SmallStepCon.stepc_elim_cases(1) a5 prod.inject stepc_elim_cases_Seq_skip(1) stepce_stepc xstate.inject(1))   
  have rfgs:"(Normal \<Sigma>, Normal \<Sigma>)\<in> G\<^sub>s\<^sup>*" by auto
  have f1: "\<forall>a c. (a, c) \<notin> \<xi> \<or> (\<Gamma>\<^sub>c,(C, Normal a),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal c),R\<^sub>s,G\<^sub>s)"
    by (meson RGSim_pre_def a3)
  then have f2: "((Normal \<sigma>, Normal \<sigma>), Normal \<Sigma>, Normal \<Sigma>) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
    using a0 rfgs a4 related_transition_intro sim_alpha
    by (metis rtrancl_idemp)
  have "(\<sigma>, \<Sigma>) \<in> \<alpha>"
    using f1 by (meson a4 sim_alpha)
  then show ?thesis
    using f2 f1 \<open>\<sigma>n' = \<sigma>\<close> \<open>c\<^sub>c' = C\<close> a4 by auto
qed      
   


lemma Impl_Seq_Skip_sim: assumes a0:"\<xi> \<subseteq> \<alpha>" and 
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and
 a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and a8: "(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)" 
shows "(\<Gamma>\<^sub>c,Seq Skip C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)"
proof-
{fix \<sigma> \<Sigma> 
 assume a11: "(\<sigma>, \<Sigma>) \<in> \<xi>"    
 then have "(\<Gamma>\<^sub>c,(Seq Skip C, Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal \<Sigma>),R\<^sub>s,G\<^sub>s)"
   apply (coinduction arbitrary: \<sigma> \<Sigma>)
   apply simp
   apply (rule conjId)+
        apply (rule, rule, rule, rule)       
        apply (frule Impl_Skip_sim1, fast+)
       apply (blast dest: sim_env[OF _ a3 a6 a7])
      apply (meson stepc_elim_cases1(1) stepc_elim_cases_Seq_skip_ev(1))
     apply (rule, rule, rule)
     apply (frule Impl_Skip_sim2[OF a6  a8], fast+)
   using a0 apply auto[1] 
   unfolding alpha_xstate_def by auto
} thus ?thesis unfolding RGSim_pre_def by auto
qed

lemma Impl_Skip_sim1':
  assumes a0:"\<xi> \<subseteq> \<alpha>" and 
 a1:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a2:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and
 a3:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and a4: "(\<Gamma>\<^sub>c,(C, Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal \<Sigma>),R\<^sub>s,G\<^sub>s)" and
       a5:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (LanguageCon.com.Seq C Skip, Normal \<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>')" and
       a6:"(\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n)" 
   shows
         "\<exists>\<Sigma>'. (\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x \<and>
             (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<or>
                      (\<exists>v. e = Some v \<and>
                           (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                                  (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'))))) \<and>
                     (Normal \<sigma>, \<sigma>') \<in> G\<^sub>c \<and> (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s))"
proof-    
  {assume a00:"C = Skip"
    then have "c\<^sub>c' = Skip \<and> \<sigma>' = Normal \<sigma>" using a5
      by (metis SmallStepCon.stepc_elim_cases(1) a6 snd_conv stepc_Normal_elim_cases(5) stepce_stepc)
    then have ?thesis  using a4 a0 a00 
      using a6 by blast
  } 
  moreover {assume a00:"C=Throw" 
    then have ?thesis using stepc_elim_seq_skip(2)[OF a5[simplified a00]] a6  
      apply auto
      by (metis (no_types) throw1)  
  }
  moreover { assume "C\<noteq>Skip \<and> C\<noteq>Throw"  
    then obtain C' where "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (C, Normal \<sigma>) \<rightarrow> (C', \<sigma>')"
      using stepc_elim_cases1(5)[OF a5] by fastforce
    moreover obtain \<Sigma>' c\<^sub>s' where "(\<sigma>',\<Sigma>')\<in>\<alpha>\<^sub>x \<and> (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S,Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>')  \<or> 
                                           (\<exists>v. e = Some v \<and>  \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (S, Normal \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s',\<Sigma>') )) \<and>
                   (Normal \<sigma>, \<sigma>')\<in>G\<^sub>c" using dest_sim_ev_step_not_normal[OF a4] calculation a6 by fastforce        
    moreover have "\<forall>\<Sigma>n'. \<Sigma>'\<noteq>Normal \<Sigma>n'" using a6 calculation
      by (meson Normal_alpha2)
    then  have "(\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)" using sim_not_normal[OF _ a6 a3 a2] calculation 
      by auto
    ultimately have ?thesis by fastforce
  } ultimately show ?thesis by auto
qed

lemma Impl_Skip_sim2':
  assumes a0:"\<xi> \<subseteq> \<alpha>" and 
    a1:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
    a2:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and
    a3:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and a4: "(\<Gamma>\<^sub>c,(C, Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal \<Sigma>),R\<^sub>s,G\<^sub>s)" and          
          a6:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (LanguageCon.com.Seq C LanguageCon.com.Skip, Normal \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n')"
shows  "\<exists>c\<^sub>s' \<Sigma>n'.
          (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                 (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n'))) \<and>
          (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
          ((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
          ((\<exists>C. c\<^sub>c' = LanguageCon.com.Seq C LanguageCon.com.Skip \<and> (\<Gamma>\<^sub>c,(C, Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)) \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))"
proof-    
  have in_alpha:"( \<sigma>, \<Sigma>)\<in> \<alpha>" using a4
    by (meson sim_alpha)

  {assume a00:"C = Skip"    
    then have ?thesis  using not_seq_skip_throw_ev a6[simplified a00]
      by metis
  } 
  moreover {assume a00:"C=Throw" 
    then have ?thesis  using not_seq_skip_throw_ev a6[simplified a00]
      by metis  
  }
  moreover { assume "C\<noteq>Skip \<and> C\<noteq>Throw"  
    then obtain C' where step:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C, Normal \<sigma>) \<rightarrow> (C', Normal \<sigma>n') \<and> 
                               c\<^sub>c' = LanguageCon.com.Seq C' LanguageCon.com.Skip" 
      using stepc_elim_cases1(5)[OF a6] by auto
    moreover obtain \<Sigma>n' c\<^sub>s' where 
     " \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (S, Normal \<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s', Normal \<Sigma>n') \<and> (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
        ((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and> 
       (\<Gamma>\<^sub>c,(C', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)" 
      using dest_sim_ev_step[OF a4] step a6 by fastforce      
    ultimately have ?thesis  by fastforce
  } ultimately show ?thesis by fastforce
qed  

lemma Impl_Seq_Skip_sim3':
  assumes 
     a0:"\<xi> \<subseteq> \<alpha>" and 
    a1:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
    a2:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and
    a3:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and a4: "(\<Gamma>\<^sub>c,(C, Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal \<Sigma>),R\<^sub>s,G\<^sub>s)" and     
    a5:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Seq C LanguageCon.com.Skip, Normal \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n')" 
     shows
       "\<exists>c\<^sub>s' \<Sigma>n'.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
          (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
          ((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
          ((\<exists>C. c\<^sub>c' = LanguageCon.com.Seq C LanguageCon.com.Skip \<and> (\<Gamma>\<^sub>c,(C, Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)) \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))"
proof-
  have in_alpha:"( \<sigma>, \<Sigma>)\<in> \<alpha>" using a4
    by (meson sim_alpha)

  {assume a00:"C = Skip"    
    then have  eq:"c\<^sub>c' = Skip \<and> \<sigma>n' = \<sigma>"       
     proof -
       have "\<forall>f z x c xa. \<not> f\<turnstile>\<^sub>c\<^sub>z (LanguageCon.com.Skip::('a, 'd, 'c, 'e) LanguageCon.com, x) \<rightarrow> (c, xa)"
         by (metis (no_types) skip1)
       then have "(c\<^sub>c', Normal \<sigma>n'::('a, 'c) xstate) = (LanguageCon.com.Skip, Normal \<sigma>)"
         using stepc_elim_cases1(5)[OF a5[simplified a00]] by fastforce
       then have "c\<^sub>c' = LanguageCon.com.Skip \<and> (Normal \<sigma>n'::('a, 'c) xstate) = Normal \<sigma>"
         by fastforce
       then have "(c\<^sub>c' = LanguageCon.com.Skip \<and> (Normal \<sigma>n'::('a, 'c) xstate) = Normal \<sigma>) \<and> \<sigma>n' = \<sigma>"
         by (meson xstate.inject(1))
       then show ?thesis
         by presburger
     qed 
     moreover have  "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (S, Normal \<Sigma>)" by auto
     moreover have  "((\<exists>C. LanguageCon.com.Skip = LanguageCon.com.Seq C LanguageCon.com.Skip \<and> (\<Gamma>\<^sub>c,(C, Normal \<sigma>),R\<^sub>c,G\<^sub>c)
             \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal \<Sigma>),R\<^sub>s,G\<^sub>s)) \<or>
        (\<Gamma>\<^sub>c,(LanguageCon.com.Skip, Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal \<Sigma>),R\<^sub>s,G\<^sub>s))"
       using a4 a00 by fastforce 
     moreover have "((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"        
       unfolding related_transitions_def using a2 eq in_alpha by fastforce
     ultimately have ?thesis using a4 eq in_alpha by auto
  } 
  moreover {assume a00:"C=Throw" 
    then have  eq:"c\<^sub>c' = Throw \<and> \<sigma>n' = \<sigma>"
       using stepc_elim_cases1(5)[OF a5[simplified a00]] throw1
     proof -
       have "\<forall>f z x c xa. \<not> f\<turnstile>\<^sub>c\<^sub>z (Throw::('a, 'd, 'c, 'e) LanguageCon.com, Normal x) \<rightarrow> (c, xa)"
         using throw1 by auto
       then have "(c\<^sub>c', Normal \<sigma>n'::('a, 'c) xstate) = (LanguageCon.com.Throw, Normal \<sigma>)"
         using throw1  stepc_elim_cases1(5)[OF a5[simplified a00]] by fastforce
       then have "c\<^sub>c' = LanguageCon.com.Throw \<and> (Normal \<sigma>n'::('a, 'c) xstate) = Normal \<sigma>"
         by fastforce
       then have "(c\<^sub>c' = Throw \<and> (Normal \<sigma>n'::('a, 'c) xstate) = Normal \<sigma>) \<and> \<sigma>n' = \<sigma>"
         by (meson xstate.inject(1))
       then show ?thesis
         by presburger
     qed 
     moreover have  "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (S, Normal \<Sigma>)" by auto
     moreover have  "((\<exists>C. LanguageCon.com.Throw = LanguageCon.com.Seq C LanguageCon.com.Throw \<and> (\<Gamma>\<^sub>c,(C, Normal \<sigma>),R\<^sub>c,G\<^sub>c)
             \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal \<Sigma>),R\<^sub>s,G\<^sub>s)) \<or>
        (\<Gamma>\<^sub>c,(LanguageCon.com.Throw, Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal \<Sigma>),R\<^sub>s,G\<^sub>s))"
       using a4 a00 by fastforce 
     moreover have "((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"        
       unfolding related_transitions_def using a2 eq in_alpha by fastforce
     ultimately have ?thesis using a4 eq in_alpha by auto
  }
  moreover { assume "C\<noteq>Skip \<and> C\<noteq>Throw"  
    then obtain C' where step:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (C, Normal \<sigma>) \<rightarrow> (C', Normal \<sigma>n') \<and> 
                               c\<^sub>c' = LanguageCon.com.Seq C' LanguageCon.com.Skip" 
      using stepc_elim_cases1(5)[OF a5] by auto 
    moreover obtain \<Sigma>n' c\<^sub>s' where 
     "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
   (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
   ((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and> (\<Gamma>\<^sub>c,(C', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c)
      \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)" 
      using dest_sim_tau_step[OF a4] step a5 by fastforce      
    ultimately have ?thesis  by fastforce
  } ultimately show ?thesis by fastforce
qed

lemma Impl_Seq_Skip_sim'4:
  assumes a0:"(\<Gamma>\<^sub>c,(C, Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal \<Sigma>),R\<^sub>s,G\<^sub>s)" and
       a1:"((Normal \<sigma>, \<sigma>'), Normal \<Sigma>, \<Sigma>') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and> (\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x" and
        a6:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and a7:"\<forall>\<sigma>. (\<sigma>,\<sigma>)\<in>G\<^sub>c" 
     shows "(\<exists>\<sigma>. \<sigma>' = Normal \<sigma> \<and>
            (\<exists>\<Sigma>. \<Sigma>' = Normal \<Sigma> \<and> (\<Gamma>\<^sub>c,(C, Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal \<Sigma>),R\<^sub>s,G\<^sub>s))) \<or>
       (\<Gamma>\<^sub>c,(LanguageCon.com.Seq C LanguageCon.com.Skip, \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, \<Sigma>'),R\<^sub>s,G\<^sub>s)"
proof-
  have  sim:"(\<Gamma>\<^sub>c,(C,\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S,\<Sigma>'),R\<^sub>s,G\<^sub>s)" using dest_sim_env_step[OF a0 a1] by auto
  {assume a00:"\<exists>\<sigma>n'. \<sigma>' = Normal \<sigma>n'"
    then have  "\<exists>\<Sigma>n'. \<Sigma>' = Normal \<Sigma>n'" using a1
      by (meson Normal_alpha)
    then have ?thesis using a00 sim by fastforce     
  }
  moreover{assume a00:"\<forall>\<sigma>n'. \<sigma>' \<noteq> Normal \<sigma>n'"
    moreover have  "(\<sigma>',\<Sigma>')\<in>\<alpha>\<^sub>x" using a1
      by (meson alpha_not_normal)    
    ultimately have ?thesis using sim_not_normal[OF _ _ a6 a7]   by auto
  } ultimately show ?thesis by fastforce
qed

lemma Impl_Seq_Skip_sim': assumes a0:"\<xi> \<subseteq> \<alpha>" and 
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and
 a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and a8: "(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)" 
shows "(\<Gamma>\<^sub>c,Seq C Skip,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)"
proof-
{fix \<sigma> \<Sigma> 
  assume a11: "(\<sigma>, \<Sigma>) \<in> \<xi>"    
  then have  "(\<Gamma>\<^sub>c,(C,Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S,Normal \<Sigma>),R\<^sub>s,G\<^sub>s)" 
    using a8 unfolding RGSim_pre_def by auto
 then have "(\<Gamma>\<^sub>c,(Seq C Skip, Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal \<Sigma>),R\<^sub>s,G\<^sub>s)"
   apply (coinduction arbitrary: \<sigma> \<Sigma> C S)
   apply simp
   apply (rule conjId)+
        apply (rule, rule, rule, rule)    
        apply (rule Impl_Skip_sim1'[OF a0 a3 a6 a7], fast+)
   apply (rule, rule,rule)
       apply (blast dest: Impl_Seq_Skip_sim'4[OF _ _ a7 a6])   
      apply (rule, rule, rule,rule)   
   apply (rule Impl_Skip_sim2'[OF a0 a3 a6 a7 ], fast+)
     apply (rule, rule, rule)
     apply (rule Impl_Seq_Skip_sim3'[OF  a0 a3 a6 a7 ], fast+)
   apply (meson sim_alpha)   
   unfolding alpha_xstate_def by auto
} thus ?thesis unfolding RGSim_pre_def by auto
qed


lemma Impl_Seq_Throw_sim1:
  assumes 
    a1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (LanguageCon.com.Seq LanguageCon.com.Throw C, Normal \<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>')" and
    a2:"(\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n)"     
  shows"\<exists>\<Sigma>'. (\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x \<and>
             (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<or>
                      (\<exists>v. e = Some v \<and>
                           (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                                  (\<exists>aa ba.
                                      \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, b) \<rightarrow> (aa, ba) \<and>
                                      \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'))))) \<and>
                     (Normal \<sigma>, \<sigma>') \<in> G\<^sub>c \<and> (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                     (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s))"
 using a1 a2
    stepc_elim_seq_skip(2)[OF a1] prod.inject throw1 apply simp
proof -
  assume "\<And>P. \<lbrakk>\<And>c\<^sub>1' s'. \<lbrakk>c\<^sub>c' = LanguageCon.com.Seq c\<^sub>1' C \<and> \<sigma>' = s'; \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (LanguageCon.com.Throw, Normal \<sigma>) \<rightarrow> (c\<^sub>1', s')\<rbrakk> \<Longrightarrow> P; \<And>s. \<lbrakk>e = \<tau>; False; \<sigma> = s\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  then show ?thesis
    by (metis (no_types) throw1)
qed 

lemma Impl_Seq_Throw_sim2: 
  assumes  
 a0:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and
 a3: "(\<Gamma>\<^sub>c,Throw,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)" and
 a4:"(\<sigma>, \<Sigma>) \<in> \<xi>" and
 a5:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Seq Throw C, Normal \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n')"
shows "\<exists>c\<^sub>s' \<Sigma>n'.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
          (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
          (((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          (c\<^sub>c' = LanguageCon.com.Seq LanguageCon.com.Throw C \<and> c\<^sub>s' = S \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))"  
proof -
  have a00:"c\<^sub>c' = Throw \<and> Normal \<sigma>n' = Normal \<sigma>" 
    using  stepc_elim_seq_skip(2)[OF a5]  apply simp
    using throw1  by metis 
      
  have rfgs:"(Normal \<Sigma>, Normal \<Sigma>)\<in> G\<^sub>s\<^sup>*" by auto
  have f1: "\<forall>a c. (a, c) \<notin> \<xi> \<or> (\<Gamma>\<^sub>c,(Throw, Normal a),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal c),R\<^sub>s,G\<^sub>s)"
    by (meson RGSim_pre_def a3)
  then have f2: "((Normal \<sigma>, Normal \<sigma>), Normal \<Sigma>, Normal \<Sigma>) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
    using a0 rfgs a4 related_transition_intro sim_alpha
    by (metis rtrancl_idemp)
  have "(\<sigma>, \<Sigma>) \<in> \<alpha>"
    using f1 by (meson a4 sim_alpha)
  then show ?thesis
    using f2 f1 a00 a4 by auto
qed      

lemma Impl_Seq_Throw_sim: assumes a0:"\<xi> \<subseteq> \<alpha>" and 
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and
 a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and a8: "(\<Gamma>\<^sub>c,Throw,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)" 
shows "(\<Gamma>\<^sub>c,Seq Throw C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)"
proof-
{fix \<sigma> \<Sigma> 
 assume a11: "(\<sigma>, \<Sigma>) \<in> \<xi>"    
 then have "(\<Gamma>\<^sub>c,(Seq Throw C, Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal \<Sigma>),R\<^sub>s,G\<^sub>s)"
   apply (coinduction arbitrary: \<sigma> \<Sigma>)
   apply simp
   apply (rule conjId)+
        apply (rule, rule, rule, rule) 
        apply (rule Impl_Seq_Throw_sim1, fast+)
       apply (blast dest: sim_env[OF _ a3 a6 a7])   
      apply (rule, rule, rule, rule)
      apply (metis not_seq_skip_throw_ev)   
     apply (rule, rule, rule, frule Impl_Seq_Throw_sim2[OF a6  a8], fast+)
   using a0 apply auto[1] 
   unfolding alpha_xstate_def by auto
} thus ?thesis unfolding RGSim_pre_def by auto
qed

lemma mod_state_tran_v: "label C1 = \<tau> \<Longrightarrow>        
       \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>Some v (LanguageCon.com.Seq C1 C2, Normal \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<Longrightarrow>
       \<exists>c\<^sub>s' \<Sigma>n'.
          (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                 (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n'))) \<and>
          (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
          ((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
          (c\<^sub>c' = LanguageCon.com.Seq C1 C2 \<and> c\<^sub>s' = S \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or> (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c)
           \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))"
proof -
assume a1: "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>Some v (LanguageCon.com.Seq C1 C2, Normal \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n')"
  assume a2: "label C1 = \<tau>"
  obtain c1' where s:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C1, Normal \<sigma>) \<rightarrow> (c1', Normal \<sigma>n')" 
    using stepc_elim_cases1(5)[OF a1] by fastforce    
  thus ?thesis using label_step[OF _ s] a2 by force 
qed

lemma mod_state_only_spec_basic_tau_sound1:
  assumes a0:"C1 = Basic fc \<tau> \<or> C1 = Spec rc \<tau>" and   
 a1:"(\<sigma>, \<Sigma>) \<in> \<xi>" and 
 a2: "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (LanguageCon.com.Seq C1 C2, Normal \<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>')" and 
 a3:"(\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n)" and 
 a4:"\<forall>\<sigma> \<sigma>' \<Sigma> . (\<sigma>, \<Sigma>)\<in>\<xi> \<and> \<sigma>' \<in> com_step  C1 (Normal \<sigma>)  \<Gamma>\<^sub>c  \<longrightarrow> 
                (\<exists>\<sigma>n'. \<sigma>' = Normal \<sigma>n' \<and> (\<sigma>n',\<Sigma>)\<in>\<xi>\<^sub>1 \<and> (Normal \<sigma>, Normal \<sigma>n') \<in> G\<^sub>c)"
shows "\<exists>\<Sigma>'. (\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x \<and>
             (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<or>
                      (\<exists>v. e = Some v \<and>
                           (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                                  (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, b) \<rightarrow> (aa, ba) \<and>
                                           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'))))) \<and> (Normal \<sigma>,\<sigma>')\<in> G\<^sub>c \<and>
                     (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s))"
proof-
  {
    assume a00:"C1 = Basic fc \<tau>"    
    then have "\<sigma>' = Normal (fc \<sigma>)" using a2 
      by (metis LanguageCon.com.simps(12) LanguageCon.com.simps(48) Pair_inject stepc_Normal_elim_cases(3) stepc_Normal_elim_cases(5) stepce_stepc)     
    then have ?thesis using a3 by auto
  }
  moreover {
    assume a00:"C1 = Spec rc \<tau>"   
    then have e:"e=\<tau>"  using a2 label_step by fastforce
    have c\<^sub>c':"c\<^sub>c' = Seq Skip C2" using stepc_elim_cases1(5)[OF a2[simplified a00]]
    proof -
      obtain cc xx where
        f1: "(c\<^sub>c', \<sigma>') = (LanguageCon.com.Seq cc C2, xx) \<and> 
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (LanguageCon.com.Spec rc \<tau>, Normal \<sigma>) \<rightarrow> (cc, xx)"
        using stepc_elim_cases1(5)[OF a2[simplified a00]]  by force
      thus ?thesis
        using stepc_elim_cases1(4) by fastforce
    qed       
    moreover have step:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Spec rc \<tau>, Normal \<sigma>) \<rightarrow> (Skip, \<sigma>')"
     using  stepc_elim_cases(6)[OF a2[simplified a00 c\<^sub>c'], simplified e] by auto    
    moreover have \<sigma>:"\<sigma>' = Stuck" using stepc_elim_cases1(4)[OF step] a3     
      by fastforce
    moreover  have "(\<nexists>sn.(\<sigma>, sn)\<in>rc)" using stepc_elim_cases(3)[OF step[simplified \<sigma>]] by auto
    moreover have "\<sigma>' \<in> com_step  C1 (Normal \<sigma>)  \<Gamma>\<^sub>c " using calculation a00 by auto
    ultimately have ?thesis using a4 a00 a1 \<sigma> by fast
  } ultimately show ?thesis using a0 by auto  
qed

lemma mod_state_only_spec_basic_tau_sound2:
  assumes a0:"\<xi> \<subseteq> \<alpha> " and a0':"\<xi>\<^sub>1 \<subseteq> \<alpha> " and a1:"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and 
          a2:"(\<sigma>, \<Sigma>) \<in> \<xi>" and 
       a3:"\<forall>\<sigma> \<sigma>' \<Sigma> . (\<sigma>, \<Sigma>)\<in>\<xi> \<and> \<sigma>' \<in> com_step  C1 (Normal \<sigma>)  \<Gamma>\<^sub>c  \<longrightarrow> 
                (\<exists>\<sigma>n'. \<sigma>' = Normal \<sigma>n' \<and> (\<sigma>n',\<Sigma>)\<in>\<xi>\<^sub>1 \<and> (Normal \<sigma>, Normal \<sigma>n') \<in> G\<^sub>c)" and
       a4:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Seq C1 C2, Normal \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n')" and
       a5:"C1 = Basic fc \<tau> \<or> C1 = Spec rc \<tau>" and 
      a6:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and  
      a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x"  and a8:"(\<Gamma>\<^sub>c,C2,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)" 
  shows "(\<exists>c\<^sub>s' \<Sigma>n'.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
          (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
          ((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          (c\<^sub>c' = LanguageCon.com.Seq C1 C2 \<and> c\<^sub>s' = S \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))"
proof-
  have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (S, Normal \<Sigma>)" by auto
  moreover have "(Normal \<Sigma>, Normal \<Sigma>) \<in> G\<^sub>s\<^sup>*"  by auto
  moreover have "c\<^sub>c' = Seq Skip C2 \<and> (\<sigma>n',\<Sigma>)\<in>\<xi>\<^sub>1 \<and> (Normal \<sigma>, Normal \<sigma>n') \<in> G\<^sub>c" 
                 using a5
  proof
    assume a00:"C1 = LanguageCon.com.Basic fc \<tau> "    
    then have "c\<^sub>c' = Seq Skip C2" using a4
      by (metis LanguageCon.com.distinct(1) LanguageCon.com.distinct(37) prod.sel(1) 
          stepc_Normal_elim_cases(3) stepc_Normal_elim_cases(5) stepce_stepc)
    moreover have "(\<sigma>n',\<Sigma>)\<in>\<xi>\<^sub>1 \<and> (Normal \<sigma>, Normal \<sigma>n') \<in> G\<^sub>c"  
    proof -
      have "\<sigma>n' = fc \<sigma>" using a4[simplified calculation a00]
        by (meson CRef.stepc_elim_cases(6) Pair_inject stepc_Normal_elim_cases(3) stepce_stepc xstate.inject(1))
      then show ?thesis using a3[simplified a00] a2 by auto
    qed
    ultimately show ?thesis by auto    
  next
    assume a00:"C1 = LanguageCon.com.Spec rc \<tau>"
    have c\<^sub>c':"c\<^sub>c' = Seq Skip C2" using stepc_elim_cases1(5)[OF a4[simplified a00]]
    proof -
      obtain cc xx where
        f1: "(c\<^sub>c', Normal \<sigma>n') = (LanguageCon.com.Seq cc C2, xx) \<and> 
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Spec rc \<tau>, Normal \<sigma>) \<rightarrow> (cc, xx)"
        using stepc_elim_cases1(5)[OF a4[simplified a00]]  by force
      thus ?thesis
        using stepc_elim_cases1(4) by fastforce
    qed
    moreover have "(\<sigma>n',\<Sigma>)\<in>\<xi>\<^sub>1 \<and> (Normal \<sigma>, Normal \<sigma>n') \<in> G\<^sub>c"  
    proof-
      have "(\<sigma>,\<sigma>n')\<in>rc" using a4[simplified calculation a00]
        by (meson CRef.stepc_elim_cases(2) CRef.stepc_elim_cases(6)) 
      then show ?thesis  using a3[simplified a00] a2 by auto
    qed
    ultimately show ?thesis  by auto          
qed 
  moreover have "(\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal \<Sigma>),R\<^sub>s,G\<^sub>s)"
    using Impl_Seq_Skip_sim[OF a0' a1 a6  a7  a8] calculation 
    unfolding RGSim_pre_def by auto
  ultimately show ?thesis using a0' a0 a2 unfolding related_transitions_def by fast
qed

lemma imp_seq_Basic_Spec_sim: 
  assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a5:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and  
 a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and  
 a9:"C1 = Basic fc \<tau> \<or> C1 = Spec rc \<tau>" and   
 a10:"\<forall>\<sigma> \<sigma>' \<Sigma> . (\<sigma>, \<Sigma>)\<in>\<xi> \<and> \<sigma>' \<in> com_step  C1 (Normal \<sigma>)  \<Gamma>\<^sub>c  \<longrightarrow> 
                (\<exists>\<sigma>n'. \<sigma>' = Normal \<sigma>n' \<and> (\<sigma>n',\<Sigma>)\<in>\<xi>\<^sub>1 \<and> (Normal \<sigma>, Normal \<sigma>n') \<in> G\<^sub>c)" and
 a11:"(\<Gamma>\<^sub>c,C2,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)"
shows "(\<Gamma>\<^sub>c,Seq C1 C2 ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)"  
  
proof-
  {fix \<sigma> \<Sigma> 
    assume a12: "(\<sigma>, \<Sigma>) \<in> \<xi>"    
    then have "(\<Gamma>\<^sub>c,(Seq C1 C2, Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal \<Sigma>),R\<^sub>s,G\<^sub>s)"
      apply (coinduction arbitrary: \<sigma> \<Sigma>)
      apply clarsimp
      apply (rule conjId)+ 
           apply (rule, rule, rule, rule, frule mod_state_only_spec_basic_tau_sound1[OF a9 _ _ _ a10], fast+)      
                    apply (blast dest: sim_env[OF _ a3 a5 a7])
           apply (rule, rule, rule, rule)
          using a9 apply (fastforce intro: mod_state_tran_v) 
        apply (rule, rule, rule, frule mod_state_only_spec_basic_tau_sound2[OF a1 a2 a4 _ a10 _ a9 a5  a7 a11] , auto)
      using  a1 unfolding alpha_xstate_def by auto   
  } then show ?thesis unfolding RGSim_pre_def by auto
qed

lemma mod_state_only_atomic_tau_sound1:
  assumes   
 a1:"(\<sigma>, \<Sigma>) \<in> \<xi>" and
 a3: "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (LanguageCon.com.Seq C1 C2, Normal \<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>')" and 
 a4:"(\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n)" and 
 a5:"C1 = Await b Cc \<tau>" and    
 a6:"\<forall>\<sigma>n \<Sigma>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (b \<inter> {s. \<sigma>n = s \<and> (\<sigma>n,\<Sigma>n)\<in>\<xi>}) Cc 
        ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c \<and> (s, \<Sigma>n)\<in> \<xi>\<^sub>1}), {}" and
 a7:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Fault f"
shows "\<exists>\<Sigma>'. (\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x \<and>
             (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<or>
                      (\<exists>v. e = Some v \<and>
                           (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                                  (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, b) \<rightarrow> (aa, ba) \<and>
                                           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'))))) \<and> (Normal \<sigma>,\<sigma>')\<in>G\<^sub>c \<and>
                     (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s))"
proof-
  obtain cc' where step_Cc:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (Await b Cc \<tau>, Normal \<sigma>) \<rightarrow> (cc', \<sigma>')" and 
                   "c\<^sub>c' = LanguageCon.com.Seq cc' C2" 
    using stepc_elim_cases1(5)[OF a3, simplified a5] by auto
  have step: "\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow>  \<sigma>' \<and> \<sigma>\<in>b"
    using step_Cc a4
    by (metis Pair_inject stepc_Normal_elim_cases(8) stepce_stepc)   
  thus ?thesis using not_normal_false[OF spec[OF spec[OF a6]] _ a4, of \<sigma>] a1 a7 by blast 
qed

lemma mod_state_only_atomic_sound2:
  assumes a0:"\<xi> \<subseteq> \<alpha> " and a0':"\<xi>\<^sub>1 \<subseteq> \<alpha> " and a1:"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and 
          a2:"(\<sigma>, \<Sigma>) \<in> \<xi>" and a3:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Seq C1 C2, Normal \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n')" and        
      a9:"C1 = Await b Cc \<tau>" and   
      a6:"\<forall>sn. ( sn, sn)\<in>G\<^sub>c" and  
      a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and a8:"(\<Gamma>\<^sub>c,C2,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)" and      
      a10:"\<forall>\<sigma>n \<Sigma>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
           (b \<inter> {s. \<sigma>n = s \<and> (\<sigma>n,\<Sigma>n)\<in>\<xi>}) Cc 
           ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c \<and> (s, \<Sigma>n)\<in> \<xi>\<^sub>1}), {}"       
  shows "(\<exists>c\<^sub>s' \<Sigma>n'.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
          (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
          ((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          (c\<^sub>c' = LanguageCon.com.Seq C1 C2 \<and> c\<^sub>s' = S \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))"
proof-  
  have hoare:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
           (b \<inter> {s. \<sigma> = s \<and> (\<sigma>,\<Sigma>)\<in>\<xi>}) Cc 
           ({s. (Normal \<sigma>, Normal s) \<in> G\<^sub>c \<and> (s, \<Sigma>)\<in> \<xi>\<^sub>1}), {}" using a10 by auto
  have step_s:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (S, Normal \<Sigma>)" by auto
  moreover have g_s:"(Normal \<Sigma>, Normal \<Sigma>) \<in> G\<^sub>s\<^sup>*"  by auto  
  obtain cc' where step_Cc:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Await b Cc \<tau>, Normal \<sigma>) \<rightarrow> (cc', Normal \<sigma>n')" and 
                   cc':"c\<^sub>c' = LanguageCon.com.Seq cc' C2" 
    using stepc_elim_cases1(5)[OF a3, simplified a9] by auto 
  then have step: "(cc' = Skip \<and> \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Normal \<sigma>n') \<or>
                   (cc' = Throw \<and> \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Abrupt \<sigma>n')"  and \<sigma>b:"\<sigma>\<in>b"
    by (auto intro:stepc_elim_casese[OF step_Cc])
  moreover {
    assume a00:"cc' = Skip"
    then have "\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Normal \<sigma>n'" using step by auto  
    then have "(Normal \<sigma>, Normal \<sigma>n') \<in> G\<^sub>c \<and> (\<sigma>n', \<Sigma>)\<in> \<xi>\<^sub>1"
      using step_imp_normal_rel_ hoare a2 \<sigma>b by fast
    moreover have "(\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal \<Sigma>),R\<^sub>s,G\<^sub>s)"
      using Impl_Seq_Skip_sim[OF a0' a1 a6  a7  a8] calculation a00 cc' 
      unfolding RGSim_pre_def by auto
    ultimately have ?thesis using step_s g_s a0' a0 a2
      unfolding related_transitions_def by auto
  }
  moreover {
    assume "cc' = Throw" 
    then have "\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Abrupt \<sigma>n'" using step by auto    
    then have ?thesis using in_normal_not_abrupt[OF hoare] a2 \<sigma>b by blast
  }
  ultimately show ?thesis  by auto        
qed


lemma imp_seq_await_sim: 
  assumes
 a1:"\<xi> \<subseteq> \<alpha>" and  a2:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and 
 a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and 
 a9:"C1 = Await b Cc \<tau>" and   
 a10:"\<forall>\<sigma>n \<Sigma>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (b \<inter> {s. \<sigma>n = s \<and> (\<sigma>n,\<Sigma>n)\<in>\<xi>}) Cc 
        ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c \<and> (s, \<Sigma>n)\<in> \<xi>\<^sub>1}), {}" and
 a11:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Fault f" and
 a12:"(\<Gamma>\<^sub>c,C2,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)" 
shows "(\<Gamma>\<^sub>c,Seq C1 C2 ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)"  
  
proof-
  {fix \<sigma> \<Sigma> 
    assume "(\<sigma>, \<Sigma>) \<in> \<xi>"    
    then have "(\<Gamma>\<^sub>c,(Seq C1 C2, Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal \<Sigma>),R\<^sub>s,G\<^sub>s)"
      apply (coinduction arbitrary: \<sigma> \<Sigma>)
      apply clarsimp
      apply (rule conjId)+                                
           apply (rule, rule, rule, rule, frule mod_state_only_atomic_tau_sound1[OF  _ _ _ a9 a10 a11], fast+)      
          apply (blast dest: sim_env[OF _ a3 a6 a7])
          apply (rule, rule, rule, rule)
      using a9 apply (fastforce intro: mod_state_tran_v)
        apply (rule, rule, rule, frule mod_state_only_atomic_sound2[OF a1 a2 a4 _ _ a9  a6  a7 a12 a10] , auto)
      using  a1 unfolding alpha_xstate_def by auto   
  } then show ?thesis unfolding RGSim_pre_def by auto
qed


lemma spec_only_mod_sound:
  assumes  
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x"  and 
 a9:"C = Basic fc l \<or> C = Spec rc l \<or> C = Await bc Cc l" and 
 a9': "S = Basic fs l \<or> S = Spec rs l \<or> S = Await bs Cs l" and  
 a10:"\<forall>\<sigma> \<sigma>' \<Sigma> . (\<sigma>, \<Sigma>)\<in>\<xi> \<and> \<sigma>' \<in> com_step  C (Normal \<sigma>)  \<Gamma>\<^sub>c  \<longrightarrow> 
                (\<exists>\<Sigma>'. \<Sigma>' \<in> com_step  S (Normal \<Sigma>) \<Gamma>\<^sub>s \<and>  (\<sigma>', \<Sigma>')\<in>\<alpha>\<^sub>x \<and> 
                       ((\<forall>\<sigma>n'. \<sigma>' = Normal \<sigma>n'   \<longrightarrow> 
                           (\<exists>\<Sigma>n'. \<Sigma>' = Normal \<Sigma>n' \<and> (\<sigma>n',\<Sigma>n')\<in>\<gamma>\<^sub>n \<and> 
                           (Normal \<sigma>, Normal \<sigma>n') \<in> G\<^sub>c \<and> (Normal \<Sigma>, Normal \<Sigma>n') \<in> G\<^sub>s)))  \<and> 
                       (\<forall>\<sigma>n'. \<sigma>' = Abrupt \<sigma>n'  \<longrightarrow> 
                           (\<exists>\<Sigma>n'. \<Sigma>' = Abrupt \<Sigma>n' \<and> (\<sigma>n', \<Sigma>n')\<in>\<gamma>\<^sub>a \<and> 
                                (Normal \<sigma>, Normal \<sigma>n') \<in> G\<^sub>c \<and> (Normal \<Sigma>, Normal \<Sigma>n') \<in> G\<^sub>s))                      
                 )" and
 a11:"(\<sigma>n, \<Sigma>n) \<in> \<xi>" and
 a12:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v (C, Normal \<sigma>n) \<rightarrow> (C', \<sigma>')"
shows "\<exists>S' \<Sigma>'.
          (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>n) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                 (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (S', \<Sigma>'))) \<and>
          (\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x \<and> ((\<forall>\<sigma>n'. \<sigma>' = Normal \<sigma>n'   \<longrightarrow> 
                           (\<exists>\<Sigma>n'. \<Sigma>' = Normal \<Sigma>n' \<and> (\<sigma>n',\<Sigma>n')\<in>\<alpha> \<and> 
                           (Normal \<sigma>n, Normal \<sigma>n') \<in> G\<^sub>c \<and> (Normal \<Sigma>n, Normal \<Sigma>n') \<in> G\<^sub>s)))  \<and>                         
          (\<Gamma>\<^sub>c,(C', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S', \<Sigma>'),R\<^sub>s,G\<^sub>s)"
proof-  
  have v_l:"v = l" using a12 a9 label_step by fastforce   
  have c1:"C' = Skip \<or> C' = Throw" using a9 stepc_elim_cases1(3,4,8)
  proof -
    have "\<forall>f z c x ca xa. \<not> f\<turnstile>\<^sub>c\<^sub>z (c::('a, 'd, 'b, 'e) LanguageCon.com, x) \<rightarrow> (ca, xa) \<or> f\<turnstile>\<^sub>c (c, x) \<rightarrow> (ca, xa)"
      by (metis stepce_stepc)
    then show ?thesis
      using a12 a9 basic_skip spec_skip await_skip
      by (metis stepce_stepc)
  qed
  moreover {
    assume c1:"C' = Skip"
    then have  s1:"\<sigma>' \<in> com_step  C (Normal \<sigma>n) \<Gamma>\<^sub>c" using a9 a12       
      by  (fastforce elim: stepc_elim_cases1(4) stepc_elim_cases1(3)  stepc_elim_cases1(8))+             
    {assume "\<exists>sn1. \<sigma>' = Normal sn1"
      then obtain \<sigma>n' where \<sigma>n':"\<sigma>' = Normal \<sigma>n'" by auto
      then obtain \<Sigma>'  where cond: "\<Sigma>' \<in> com_step  S (Normal \<Sigma>n) \<Gamma>\<^sub>s \<and>   (\<sigma>', \<Sigma>')\<in>\<alpha>\<^sub>x \<and>
                           (\<exists>\<Sigma>n'. \<Sigma>' = Normal \<Sigma>n' \<and> (\<sigma>n',\<Sigma>n')\<in>\<gamma>\<^sub>n \<and> 
                           (Normal \<sigma>n, \<sigma>') \<in> G\<^sub>c \<and> (Normal \<Sigma>n, \<Sigma>') \<in> G\<^sub>s)"
       using a10 a11 c1 s1 by fast
      have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (S, Normal \<Sigma>n) \<rightarrow> (Skip, \<Sigma>')" 
        using com_step_BS cond a9'   v_l by fast           
      then have ?thesis using 
        a11 cond  a1 a2 Skip_sim_normal[OF  a2 _ a4  _ a6 a7 ] c1 cond  \<sigma>n' 
        unfolding related_transitions_def by blast
    }
    moreover { 
      assume ass0:"\<sigma>' = Stuck \<or> (\<exists>f. \<sigma>' = Fault f)"      
      then obtain \<Sigma>'  where cond: "\<Sigma>' \<in> com_step  S (Normal \<Sigma>n) \<Gamma>\<^sub>s \<and>  (\<sigma>', \<Sigma>')\<in>\<alpha>\<^sub>x"
        using a10 a11 c1 s1 by fast      
      then have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (S, Normal \<Sigma>n) \<rightarrow> (Skip, \<Sigma>')" 
        using com_step_BS cond a9' v_l
        by (metis Fault_alpha Stuck_alpha ass0 xstate.distinct(7) xstate.distinct(9))                
      have ?thesis using steps cond  
           Skip_sim_normal_not_normal[OF  _ _ a7 a6] c1 ass0 by fast
    }
    moreover { 
      assume ass0: "\<exists>sn. \<sigma>' = Abrupt sn"
      then have False using a12 c1 step_Abrupt_end        
        using stepce_stepc by fastforce
      then have ?thesis by auto
    }
    ultimately have ?thesis by (cases \<sigma>', auto)     
  }
  moreover 
  { assume c1:"C' = Throw"
    then obtain bc Cc where c:"C = Await bc Cc l"
      using a9 a12 
      by  (fastforce elim: stepc_elim_cases1(4) stepc_elim_cases1(3)  stepc_elim_cases1(8))
    then obtain \<sigma>n' where sn1: "\<sigma>' = Normal \<sigma>n' \<and> \<sigma>n \<in> bc \<and> \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>n\<rangle> \<Rightarrow> Abrupt \<sigma>n'"
      using c1 a12 by (fastforce elim: stepc_elim_cases1(8))
    moreover have  s1:"Abrupt \<sigma>n' \<in> com_step  C (Normal \<sigma>n) \<Gamma>\<^sub>c" using c calculation by auto          
    ultimately obtain \<Sigma>' \<Sigma>n' where cond: "\<Sigma>' \<in> com_step  S (Normal \<Sigma>n) \<Gamma>\<^sub>s \<and>                             
                                (\<Sigma>' = Abrupt \<Sigma>n' \<and> (\<sigma>n', \<Sigma>n')\<in>\<gamma>\<^sub>a \<and> 
                                (Normal \<sigma>n, Normal \<sigma>n') \<in> G\<^sub>c \<and> (Normal \<Sigma>n, Normal \<Sigma>n') \<in> G\<^sub>s)"
       using a10 a11 c1 s1  by force         
    then have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (S, Normal \<Sigma>n) \<rightarrow> (Throw, Normal \<Sigma>n')" 
      using   a9' sn1 com_step_BS1 v_l by metis      
    then have sim:"(\<Gamma>\<^sub>c,(C', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Throw, Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)"
      using cond Throw_sim_normal[OF  a2' _ a5 _ a6 a7 ] sn1 c1 by fast
    then have ?thesis using a2' steps   a11  cond  a1 sn1
      unfolding related_transitions_def
      using dest_sim_alpha_x by fastforce
  }
  ultimately show ?thesis by auto 
qed

lemma dest_sim_tau_step1:
  "(\<Gamma>\<^sub>c,(c\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
    (\<forall>c\<^sub>c' \<sigma>n'. \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c\<^sub>c, \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow>
    (\<exists>c\<^sub>s' \<Sigma>n'.  \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
              (\<sigma>n', \<Sigma>n')\<in>\<alpha> \<and> 
              (((\<sigma>,Normal \<sigma>n'),(\<Sigma>, Normal \<Sigma>n')) \<in> (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))"
  by (erule sim_elim_cases,auto)


lemma Spec_Seq_Skip_sim: assumes a0:"\<xi> \<subseteq> \<alpha>" and 
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and  
 a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and  a8: "(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)" 
shows "(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,Seq Skip S,R\<^sub>s,G\<^sub>s)"
proof-
{fix \<sigma>' \<Sigma>' 
  assume a11: "(\<sigma>', \<Sigma>') \<in> \<xi>"   
  then have "(\<Gamma>\<^sub>c,(C, Normal \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S, Normal \<Sigma>'),R\<^sub>s,G\<^sub>s)"
  proof (coinduction arbitrary: \<sigma>' \<Sigma>',simp)
    {fix \<sigma>'' \<Sigma>''
    assume a11:"(\<sigma>'', \<Sigma>'') \<in> \<xi>"
    have x:"(\<Gamma>\<^sub>c,(C,Normal \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal \<Sigma>''),R\<^sub>s,G\<^sub>s)"
      using a8 a11 unfolding RGSim_pre_def by auto  
    have step_s:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq Skip S, Normal \<Sigma>'') \<rightarrow> (S, Normal \<Sigma>'')"
      using SeqSkipc by auto
    have "(Normal \<sigma>'', Normal \<Sigma>'') \<in> \<alpha>\<^sub>x" unfolding alpha_xstate_def by auto
    moreover have "(\<sigma>'', \<Sigma>'') \<in> \<alpha> " using a11 a0 by auto
    moreover have "\<forall>c\<^sub>c' \<sigma>n'.
      \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (C, Normal \<sigma>'') \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow>
      (\<exists>c\<^sub>s' \<Sigma>n'.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Skip S, Normal \<Sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
          (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
          ((Normal \<sigma>'', Normal \<sigma>n'), Normal \<Sigma>'', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and> (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c)
          \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))"  using sim_elim_cases[OF x] step_s 
    by (meson  converse_rtranclp_into_rtranclp) 
  moreover have "\<forall>v c\<^sub>c' \<sigma>n'.
        \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>Some v (C, Normal \<sigma>'') \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow>
        (\<exists>c\<^sub>s' \<Sigma>n'.
             (\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (S, Normal \<Sigma>'') \<rightarrow>\<^sup>+  (c\<^sub>s', Normal \<Sigma>n')) \<and>
            (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
            ((Normal \<sigma>'', Normal \<sigma>n'), Normal \<Sigma>'', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and> (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c)
            \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))" 
    by (fastforce intro: sim_elim_cases[OF x])
  then have "\<forall>v c\<^sub>c' \<sigma>n'.
        \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>Some v (C, Normal \<sigma>'') \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow>
        (\<exists>c\<^sub>s' \<Sigma>n'.
             (\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (Seq Skip S, Normal \<Sigma>'') \<rightarrow>\<^sup>+  (c\<^sub>s', Normal \<Sigma>n')) \<and>
            (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
            ((Normal \<sigma>'', Normal \<sigma>n'), Normal \<Sigma>'', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and> (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c)
            \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))"
    using event_tran_closure_tau_tran[OF step_s]  by meson 
  then have "\<forall>v c\<^sub>c' \<sigma>n'.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C, Normal \<sigma>'') \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow>
           (\<exists>c\<^sub>s' \<Sigma>n'.
               (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq LanguageCon.com.Skip S, Normal \<Sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                      (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n'))) \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
               ((Normal \<sigma>'', Normal \<sigma>n'), Normal \<Sigma>'', Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (c\<^sub>c' = C \<and> c\<^sub>s' = LanguageCon.com.Seq LanguageCon.com.Skip S \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))" by fastforce
  moreover {
    fix \<sigma>' \<Sigma>' 
    assume a00:"((Normal \<sigma>'', \<sigma>'), Normal \<Sigma>'', \<Sigma>') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and> (\<sigma>',\<Sigma>')\<in>\<alpha>\<^sub>x"
    then have "(\<exists>\<sigma>''. \<sigma>' = Normal \<sigma>'' \<and> (\<exists>\<Sigma>''. \<Sigma>' = Normal \<Sigma>'' \<and> (\<sigma>'', \<Sigma>'') \<in> \<xi>)) \<or> (\<Gamma>\<^sub>c,(C, \<sigma>'),R\<^sub>c,G\<^sub>c)
                 \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S, \<Sigma>'),R\<^sub>s,G\<^sub>s)"
      using sim_env[OF  a11 a3 a6 a7 a00] by blast
  }
  moreover have "(C = LanguageCon.com.Skip \<longrightarrow>
        (\<exists>\<Sigma>n'. ((Normal \<sigma>'', Normal \<sigma>''), Normal \<Sigma>'', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                (\<sigma>'', \<Sigma>n') \<in> \<gamma>\<^sub>n \<and>
                \<gamma>\<^sub>n \<subseteq> \<alpha> \<and>
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Skip S, Normal \<Sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>*
                        (LanguageCon.com.Skip, Normal \<Sigma>n')))"
    using sim_elim_cases[OF x] step_s converse_rtranclp_into_rtranclp
    by smt
  moreover have "(C = LanguageCon.com.Throw \<longrightarrow>
        (\<exists>\<Sigma>n'. ((Normal \<sigma>'', Normal \<sigma>''), Normal \<Sigma>'', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                (\<sigma>'', \<Sigma>n') \<in> \<gamma>\<^sub>a \<and>
                \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Skip S, Normal \<Sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>*
                        (LanguageCon.com.Throw, Normal \<Sigma>n')))"
    using sim_elim_cases[OF x] step_s converse_rtranclp_into_rtranclp
    by smt
  moreover have"\<forall>\<sigma>' c\<^sub>c' e.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (C, Normal \<sigma>'') \<rightarrow> (c\<^sub>c', \<sigma>') \<and> (\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n) \<longrightarrow>
           (\<exists>\<Sigma>'. (\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x \<and>
                  (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Skip S, Normal \<Sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<or>
                           (\<exists>v. e = Some v \<and>
                                (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq LanguageCon.com.Skip S, Normal \<Sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>*
                                               (a, b) \<and>
                                       (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, b) \<rightarrow> (aa, ba) \<and>
                                                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'))))) \<and> (Normal \<sigma>'',\<sigma>')\<in>G\<^sub>c \<and>
                          (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)))" 
     using sim_elim_cases[OF x] step_s converse_rtranclp_into_rtranclp
     by smt 
   ultimately show 
      "(Normal \<sigma>'', Normal \<Sigma>'') \<in> \<alpha>\<^sub>x \<and>
       (\<sigma>'', \<Sigma>'') \<in> \<alpha> \<and>
       (\<forall>c\<^sub>c' \<sigma>n'.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (C, Normal \<sigma>'') \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow>
           (\<exists>c\<^sub>s' \<Sigma>n'.
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq LanguageCon.com.Skip S, Normal \<Sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
               ((Normal \<sigma>'', Normal \<sigma>n'), Normal \<Sigma>'', Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (c\<^sub>c' = C \<and> c\<^sub>s' = LanguageCon.com.Seq LanguageCon.com.Skip S \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))) \<and>
       (\<forall>v c\<^sub>c' \<sigma>n'.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C, Normal \<sigma>'') \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow>
           (\<exists>c\<^sub>s' \<Sigma>n'.
               (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq LanguageCon.com.Skip S, Normal \<Sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                      (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n'))) \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
               ((Normal \<sigma>'', Normal \<sigma>n'), Normal \<Sigma>'', Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (c\<^sub>c' = C \<and> c\<^sub>s' = LanguageCon.com.Seq LanguageCon.com.Skip S \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))) \<and>
       (\<forall>\<sigma>' \<Sigma>'. ((Normal \<sigma>'', \<sigma>'), Normal \<Sigma>'', \<Sigma>') \<in> ((R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> (\<sigma>',\<Sigma>')\<in>\<alpha>\<^sub>x \<longrightarrow>
                 (\<exists>\<sigma>''. \<sigma>' = Normal \<sigma>'' \<and> (\<exists>\<Sigma>''. \<Sigma>' = Normal \<Sigma>'' \<and> (\<sigma>'', \<Sigma>'') \<in> \<xi>)) \<or> (\<Gamma>\<^sub>c,(C, \<sigma>'),R\<^sub>c,G\<^sub>c)
                 \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(LanguageCon.com.Seq LanguageCon.com.Skip S, \<Sigma>'),R\<^sub>s,G\<^sub>s)) \<and>
       (C = LanguageCon.com.Skip \<longrightarrow>
        (\<exists>\<Sigma>n'. ((Normal \<sigma>'', Normal \<sigma>''), Normal \<Sigma>'', Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                (\<sigma>'', \<Sigma>n') \<in> \<gamma>\<^sub>n \<and>
                \<gamma>\<^sub>n \<subseteq> \<alpha> \<and>
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq LanguageCon.com.Skip S, Normal \<Sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>*
                        (LanguageCon.com.Skip, Normal \<Sigma>n'))) \<and>
       (C = LanguageCon.com.Throw \<longrightarrow>
        (\<exists>\<Sigma>n'. ((Normal \<sigma>'', Normal \<sigma>''), Normal \<Sigma>'', Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                (\<sigma>'', \<Sigma>n') \<in> \<gamma>\<^sub>a \<and>
                \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq LanguageCon.com.Skip S, Normal \<Sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>*
                        (LanguageCon.com.Throw, Normal \<Sigma>n'))) \<and>
       (\<forall>\<sigma>' c\<^sub>c' e.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (C, Normal \<sigma>'') \<rightarrow> (c\<^sub>c', \<sigma>') \<and> (\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n) \<longrightarrow>
           (\<exists>\<Sigma>'. (\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x \<and>
                  (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq LanguageCon.com.Skip S, Normal \<Sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<or>
                           (\<exists>v. e = Some v \<and>
                                (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq LanguageCon.com.Skip S, Normal \<Sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>*
                                               (a, b) \<and>
                                       (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                                                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>')))))  \<and> (Normal \<sigma>'',\<sigma>')\<in>G\<^sub>c \<and>
                          (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s))))"
     by blast
 } qed
} thus ?thesis unfolding RGSim_pre_def by auto
qed

  
lemma Spec_Seq_Throw_sim: assumes a0:"\<xi> \<subseteq> \<alpha>" and 
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and  
 a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" 
shows "(\<Gamma>\<^sub>c,Throw,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>) (\<Gamma>\<^sub>s,Seq Throw S,R\<^sub>s,G\<^sub>s)"
proof-
{fix \<sigma>' \<Sigma>' 
  assume a11: "(\<sigma>', \<Sigma>') \<in> \<xi>"     
  then have "(\<Gamma>\<^sub>c,(Throw, Normal \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>) (\<Gamma>\<^sub>s,(Seq Throw S, Normal \<Sigma>'),R\<^sub>s,G\<^sub>s)" 
  proof (coinduction arbitrary: \<sigma>' \<Sigma>',simp)
    {fix \<sigma>'' \<Sigma>''
    assume a11:"(\<sigma>'', \<Sigma>'') \<in> \<xi>"
    have x:"(\<Gamma>\<^sub>c,(Throw,Normal \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>) (\<Gamma>\<^sub>s,(Throw, Normal \<Sigma>''),R\<^sub>s,G\<^sub>s)"
      using Throw_sound[OF a0 a3 a6 a7] a11 unfolding RGSim_pre_def by fastforce  
    have step_s:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq Throw S, Normal \<Sigma>'') \<rightarrow> (Throw, Normal \<Sigma>'')"
      using SeqThrowc by fastforce
    have "(Normal \<sigma>'', Normal \<Sigma>'') \<in> \<alpha>\<^sub>x" unfolding alpha_xstate_def by auto
    moreover have "(\<sigma>'', \<Sigma>'') \<in> \<alpha> " using a11 a0 by auto
    moreover have "\<forall>c\<^sub>c' \<sigma>n'.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Throw, Normal \<sigma>'') \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow>
           (\<exists>c\<^sub>s' \<Sigma>n'.
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Throw S, Normal \<Sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
               (((Normal \<sigma>'', Normal \<sigma>n'), Normal \<Sigma>'', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (c\<^sub>c' = LanguageCon.com.Throw \<and>
                c\<^sub>s' = LanguageCon.com.Seq LanguageCon.com.Throw S \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>)
                (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))"  
      using sim_elim_cases[OF x] step_s by (meson  converse_rtranclp_into_rtranclp) 
  moreover have "\<forall>v c\<^sub>c' \<sigma>n'.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Throw, Normal \<sigma>'') \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow>
           (\<exists>c\<^sub>s' \<Sigma>n'.
               (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq Throw S, Normal \<Sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                      (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n'))) \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
               ((Normal \<sigma>'', Normal \<sigma>n'), Normal \<Sigma>'', Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (c\<^sub>c' = Throw \<and> c\<^sub>s' = LanguageCon.com.Seq LanguageCon.com.Throw S \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))" 
    using throw1 by fast
  moreover {
    fix \<sigma>' \<Sigma>' 
    assume a00:"((Normal \<sigma>'', \<sigma>'), Normal \<Sigma>'', \<Sigma>') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and> (\<sigma>',\<Sigma>')\<in>\<alpha>\<^sub>x"
    then have "(\<exists>\<sigma>''. \<sigma>' = Normal \<sigma>'' \<and> (\<exists>\<Sigma>''. \<Sigma>' = Normal \<Sigma>'' \<and> (\<sigma>'', \<Sigma>'') \<in> \<xi>)) \<or> (\<Gamma>\<^sub>c,(Throw, \<sigma>'),R\<^sub>c,G\<^sub>c)
                 \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>) (\<Gamma>\<^sub>s,(Seq Throw S, \<Sigma>'),R\<^sub>s,G\<^sub>s)"
      using sim_env[OF  a11 a3 a6 a7 a00] by blast
  }
  moreover have "(Throw = LanguageCon.com.Skip \<longrightarrow>
        (\<exists>\<Sigma>n'. ((Normal \<sigma>'', Normal \<sigma>''), Normal \<Sigma>'', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                (\<sigma>'', \<Sigma>n') \<in> \<gamma>\<^sub>n \<and>
                \<gamma>\<^sub>n \<subseteq> \<alpha> \<and>
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Throw S, Normal \<Sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>*
                        (LanguageCon.com.Skip, Normal \<Sigma>n')))"
    by auto
  moreover have "(Throw = LanguageCon.com.Throw \<longrightarrow>
        (\<exists>\<Sigma>n'. ((Normal \<sigma>'', Normal \<sigma>''), Normal \<Sigma>'', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                (\<sigma>'', \<Sigma>n') \<in> \<xi> \<and>
                \<xi> \<subseteq> \<alpha> \<and>
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Throw S, Normal \<Sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>*
                        (LanguageCon.com.Throw, Normal \<Sigma>n')))"
    using sim_elim_cases[OF x] step_s converse_rtranclp_into_rtranclp
    by smt
  moreover have"\<forall>\<sigma>' c\<^sub>c' e.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (Throw, Normal \<sigma>'') \<rightarrow> (c\<^sub>c', \<sigma>') \<and> (\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n) \<longrightarrow>
           (\<exists>\<Sigma>'. (\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x \<and>
                  (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Throw S, Normal \<Sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<or>
                           (\<exists>v. e = Some v \<and>
                                (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq Throw S, Normal \<Sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>*
                                               (a, b) \<and>
                                       (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, b) \<rightarrow> (aa, ba) \<and>
                                                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'))))) \<and> (Normal \<sigma>'',\<sigma>')\<in>G\<^sub>c \<and>
                          (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)))" 
      using throw1 by fast
   ultimately show 
      "(Normal \<sigma>'', Normal \<Sigma>'') \<in> \<alpha>\<^sub>x \<and>
       (\<sigma>'', \<Sigma>'') \<in> \<alpha> \<and>
       (\<forall>c\<^sub>c' \<sigma>n'.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Throw, Normal \<sigma>'') \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow>
           (\<exists>c\<^sub>s' \<Sigma>n'.
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Throw S, Normal \<Sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
               (((Normal \<sigma>'', Normal \<sigma>n'), Normal \<Sigma>'', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (c\<^sub>c' = LanguageCon.com.Throw \<and>
                c\<^sub>s' = LanguageCon.com.Seq LanguageCon.com.Throw S \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>)
                (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))) \<and>
       (\<forall>v c\<^sub>c' \<sigma>n'.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Throw, Normal \<sigma>'') \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow>
           (\<exists>c\<^sub>s' \<Sigma>n'.
               (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Throw S, Normal \<Sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                      (\<exists>aa ba.
                          \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n'))) \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
               (((Normal \<sigma>'', Normal \<sigma>n'), Normal \<Sigma>'', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (c\<^sub>c' = LanguageCon.com.Throw \<and>
                c\<^sub>s' = LanguageCon.com.Seq LanguageCon.com.Throw S \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>)
                (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))) \<and>
       (\<forall>\<sigma>' \<Sigma>'.
           (((Normal \<sigma>'', \<sigma>'), Normal \<Sigma>'', \<Sigma>') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> (\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x \<longrightarrow>
           (\<exists>\<sigma>''. \<sigma>' = Normal \<sigma>'' \<and> (\<exists>\<Sigma>''. \<Sigma>' = Normal \<Sigma>'' \<and> (\<sigma>'', \<Sigma>'') \<in> \<xi>)) \<or>
           (\<Gamma>\<^sub>c,(LanguageCon.com.Throw, \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>)
           (\<Gamma>\<^sub>s,(LanguageCon.com.Seq LanguageCon.com.Throw S, \<Sigma>'),R\<^sub>s,G\<^sub>s)) \<and>
       (\<exists>\<Sigma>n'. (((Normal \<sigma>'', Normal \<sigma>''), Normal \<Sigma>'', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (\<sigma>'', \<Sigma>n') \<in> \<xi> \<and> \<xi> \<subseteq> \<alpha> \<and>
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq LanguageCon.com.Throw S, Normal \<Sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>*
                       (LanguageCon.com.Throw, Normal \<Sigma>n')) \<and>
       (\<forall>\<sigma>' c\<^sub>c' e.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (LanguageCon.com.Throw, Normal \<sigma>'') \<rightarrow> (c\<^sub>c', \<sigma>') \<and>
           (\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n) \<longrightarrow>
           (\<exists>\<Sigma>'. (\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x \<and>
                  (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq LanguageCon.com.Throw S, Normal \<Sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<or>
                         (\<exists>v. e = Some v \<and>
                            (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq Throw S, Normal \<Sigma>'') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and> (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, b) \<rightarrow> (aa, ba) \<and>
                     \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'))))) \<and>
                     (Normal \<sigma>'', \<sigma>') \<in> G\<^sub>c \<and> 
                       (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c)\<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)))) "
     by blast
 } qed
} thus ?thesis unfolding RGSim_pre_def by auto
qed



lemma spec_mod_state_only_atomic_tau_sound1:
  assumes   
 a1:"(\<sigma>, \<Sigma>) \<in> \<xi>" and
 a3: "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (LanguageCon.com.Seq C1 C2, Normal \<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>')" and 
 a4:"(\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n)" and 
 a5:"C1 = Await b Cc \<tau>" and    
 a6:"\<forall>\<sigma>n \<Sigma>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (b \<inter> {s. \<sigma>n = s \<and> (\<sigma>n,\<Sigma>n)\<in>\<xi>}) Cc 
        ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c \<and> (s, \<Sigma>n)\<in> \<xi>\<^sub>1}), {}" and
 a7:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Fault f"
shows "\<exists>\<Sigma>'. (\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x \<and>
             (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<or>
                      (\<exists>v. e = Some v \<and>
                           (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                                  (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, b) \<rightarrow> (aa, ba) \<and>
                                           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'))))) \<and>
                     (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s))"
proof-
  obtain cc' where step_Cc:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (Await b Cc \<tau>, Normal \<sigma>) \<rightarrow> (cc', \<sigma>')" and 
                   "c\<^sub>c' = LanguageCon.com.Seq cc' C2" 
    using stepc_elim_cases1(5)[OF a3, simplified a5] by auto
  have step: "\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow>  \<sigma>' \<and> \<sigma>\<in>b"
    using step_Cc a4
    by (metis Pair_inject stepc_Normal_elim_cases(8) stepce_stepc)   
  thus ?thesis using not_normal_false[OF spec[OF spec[OF a6]] _ a4, of \<sigma>] a1 a7 by blast 
qed

lemma spec_mod_state_only_atomic_sound2:
  assumes a0:"\<xi> \<subseteq> \<alpha> " and a0':"\<xi>\<^sub>1 \<subseteq> \<alpha> " and a1:"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and 
          a2:"(\<sigma>, \<Sigma>) \<in> \<xi>" and a3:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Seq C1 C2, Normal \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n')" and        
      a9:"C1 = Await b Cc \<tau>" and   
      a6:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and  
      a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x"  and a8:"(\<Gamma>\<^sub>c,C2,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)" and      
      a10:"\<forall>\<sigma>n \<Sigma>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
           (b \<inter> {s. \<sigma>n = s \<and> (\<sigma>n,\<Sigma>n)\<in>\<xi>}) Cc 
           ({s. (Normal \<sigma>n, Normal s) \<in> G\<^sub>c \<and> (s, \<Sigma>n)\<in> \<xi>\<^sub>1}), {}"       
  shows "(\<exists>c\<^sub>s' \<Sigma>n'.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
          (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
          ((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          (c\<^sub>c' = LanguageCon.com.Seq C1 C2 \<and> c\<^sub>s' = S \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))"
proof-  
  have hoare:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
           (b \<inter> {s. \<sigma> = s \<and> (\<sigma>,\<Sigma>)\<in>\<xi>}) Cc 
           ({s. (Normal \<sigma>, Normal s) \<in> G\<^sub>c \<and> (s, \<Sigma>)\<in> \<xi>\<^sub>1}), {}" using a10 by auto
  have step_s:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (S, Normal \<Sigma>)" by auto
  moreover have g_s:"(Normal \<Sigma>, Normal \<Sigma>) \<in> G\<^sub>s\<^sup>*"  by auto  
  obtain cc' where step_Cc:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Await b Cc \<tau>, Normal \<sigma>) \<rightarrow> (cc', Normal \<sigma>n')" and 
                   cc':"c\<^sub>c' = LanguageCon.com.Seq cc' C2" 
    using stepc_elim_cases1(5)[OF a3, simplified a9] by auto 
  then have step: "(cc' = Skip \<and> \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Normal \<sigma>n') \<or>
                   (cc' = Throw \<and> \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Abrupt \<sigma>n')"  and \<sigma>b:"\<sigma>\<in>b"
    by (auto intro:stepc_elim_casese[OF step_Cc])
  moreover {
    assume a00:"cc' = Skip"
    then have "\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Normal \<sigma>n'" using step by auto  
    then have "(Normal \<sigma>, Normal \<sigma>n') \<in> G\<^sub>c \<and> (\<sigma>n', \<Sigma>)\<in> \<xi>\<^sub>1"
      using step_imp_normal_rel_ hoare a2 \<sigma>b by fast
    moreover have "(\<Gamma>\<^sub>c,(c\<^sub>c',Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal \<Sigma>),R\<^sub>s,G\<^sub>s)"
      using Impl_Seq_Skip_sim[OF a0' a1 a6  a7 a8] calculation a00 cc' 
      unfolding RGSim_pre_def by auto
    ultimately have ?thesis using step_s g_s a0' a0 a2
      unfolding related_transitions_def by auto
  }
  moreover {
    assume "cc' = Throw" 
    then have "\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Abrupt \<sigma>n'" using step by auto    
    then have ?thesis using in_normal_not_abrupt[OF hoare] a2 \<sigma>b by blast
  }
  ultimately show ?thesis  by auto        
qed

lemma await_step_sim_cond:
  assumes 
  a0:"(\<sigma>, \<Sigma>) \<in> \<xi>" and a2:"Range \<xi> \<subseteq> b" and
  a3:"S1 = Await b Ss \<tau>"  and
  a4:"\<forall>\<sigma>n \<Sigma>n. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub>
        (b \<inter> {s. \<Sigma>n = s \<and> (\<sigma>n,\<Sigma>n)\<in>\<xi>}) Ss 
        ({s. (Normal \<Sigma>n, Normal s) \<in> G\<^sub>s \<and> (\<sigma>n, s)\<in> \<xi>\<^sub>1}), {}" and
  a5:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Ss,Normal \<sigma>\<rangle> \<Rightarrow> Fault f" 
obtains \<Sigma>' where "(\<sigma>, \<Sigma>') \<in> \<xi>\<^sub>1 \<and> (Normal \<Sigma>, Normal \<Sigma>')\<in>G\<^sub>s \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, Normal \<Sigma>) \<rightarrow> (Skip, Normal \<Sigma>')"  
proof-
  have "\<Sigma> \<in> b" using a0 a2 by auto
  moreover have "\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub>
        (b \<inter> {s. \<Sigma> = s \<and> (\<sigma>,\<Sigma>)\<in>\<xi>}) Ss 
        ({s. (Normal \<Sigma>, Normal s) \<in> G\<^sub>s \<and> (\<sigma>, s)\<in> \<xi>\<^sub>1}), {}" using a4 by auto
  then have "\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> 
             (b \<inter> {s. \<Sigma> = s \<and> (\<sigma>, \<Sigma>) \<in> \<xi>}) Ss 
            ({s. (Normal \<Sigma>, Normal s) \<in> G\<^sub>s \<and> (\<sigma>, s) \<in> \<xi>\<^sub>1}),{}"
    using hoaret_sound' by blast  
  moreover obtain \<Sigma>' where "\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Ss,Normal \<Sigma>\<rangle> \<Rightarrow> Normal \<Sigma>' \<and> (\<sigma>, \<Sigma>') \<in> \<xi>\<^sub>1 \<and> 
                                      (Normal \<Sigma>, Normal \<Sigma>')\<in>G\<^sub>s"
    using calculation a0 a5 Termination.terminates_implies_exec  unfolding validt_def valid_def
    by blast   
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, Normal \<Sigma>) \<rightarrow> (Skip, Normal \<Sigma>')" 
    using a3 calculation Awaitc  by fastforce
  ultimately show ?thesis
    using that by blast
qed
 
lemma spec_mod_state_only_Await_sound1: assumes 
  a0:"(\<sigma>, \<Sigma>) \<in> \<xi>" and a1:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and a1':"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
  a2:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and  
  a4:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and  
  a6:"S1 = Await b Ss \<tau>" and a7:"Range \<xi> \<subseteq> b" and
  a8:"\<forall>\<sigma>n \<Sigma>n. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
        (b \<inter> {s. \<Sigma>n = s \<and> (\<sigma>n,\<Sigma>n)\<in>\<xi>}) Ss 
        ({s. (Normal \<Sigma>n, Normal s) \<in> G\<^sub>s \<and> (\<sigma>n, s)\<in> \<xi>\<^sub>1}), {}" and
  a9:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Ss,Normal \<sigma>\<rangle> \<Rightarrow> Fault f" and
  a10:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" and 
  a11:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (C, Normal \<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>') \<and> (\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n)"
  shows  "(\<exists>\<Sigma>'. (\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x \<and>
               (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq S1 S2, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<or>
                        (\<exists>v. e = Some v \<and>
                             (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq S1 S2, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                                    (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, b) \<rightarrow> (aa, ba) \<and>
                                             \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'))))) \<and> (Normal \<sigma>,\<sigma>')\<in>G\<^sub>c \<and>
                       (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)))"
proof-
  obtain \<Sigma>' where 
   "(\<sigma>, \<Sigma>') \<in> \<xi>\<^sub>1 \<and> (Normal \<Sigma>, Normal \<Sigma>')\<in>G\<^sub>s \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, Normal \<Sigma>) \<rightarrow> (Skip, Normal \<Sigma>')" 
    using await_step_sim_cond[OF a0 a7 a6 a8 a9] by auto
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq S1 S2, Normal \<Sigma>) \<rightarrow> (Seq Skip S2, Normal \<Sigma>')"
    using Seqc calculation by fastforce
  moreover have x:"(\<Gamma>\<^sub>c,(C,Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S2, Normal \<Sigma>'),R\<^sub>s,G\<^sub>s)"
    using  calculation Spec_Seq_Skip_sim[OF a1 a1' a2  a4 a10] 
    unfolding RGSim_pre_def by auto  
  moreover have "(\<exists>\<Sigma>''. (\<sigma>', \<Sigma>'') \<in> \<alpha>\<^sub>x \<and>
               (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq Skip S2, Normal \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'') \<or>
                        (\<exists>v. e = Some v \<and>
                             (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq Skip S2, Normal \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                                    (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                                             \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>''))))) \<and> (Normal \<sigma>,\<sigma>')\<in>G\<^sub>c \<and>
                       (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s)))" 
    using a11 sim_elim_cases[OF x] by fast  
  ultimately show ?thesis
    by (metis (no_types, lifting) converse_rtranclp_into_rtranclp)  
qed

lemma spec_mod_state_only_Await_sound2:
  assumes 
  a0:"(\<sigma>, \<Sigma>) \<in> \<xi>" and a0':"\<xi>\<subseteq>\<alpha>" and a1:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and a1':"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
  a2:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and 
  a4:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and 
  a6:"S1 = Await b Ss \<tau>" and a7:"Range \<xi> \<subseteq> b" and
  a8:"\<forall>\<sigma>n \<Sigma>n. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
        (b \<inter> {s. \<Sigma>n = s \<and> (\<sigma>n,\<Sigma>n)\<in>\<xi>}) Ss 
        ({s. (Normal \<Sigma>n, Normal s) \<in> G\<^sub>s \<and> (\<sigma>n, s)\<in> \<xi>\<^sub>1}), {}" and
  a9:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Ss,Normal \<sigma>\<rangle> \<Rightarrow> Fault f" and
  a10:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" and   
  a11:"C = LanguageCon.com.Throw" shows
      "\<exists>\<Sigma>n'. ((Normal \<sigma>, Normal \<sigma>), Normal \<Sigma>, Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
              (\<sigma>, \<Sigma>n') \<in> \<gamma>\<^sub>a \<and>
              \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq S1 S2, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Throw, Normal \<Sigma>n')"
proof-

obtain \<Sigma>' where 
   sim_cond:"(\<sigma>, \<Sigma>') \<in> \<xi>\<^sub>1 \<and> (Normal \<Sigma>, Normal \<Sigma>')\<in>G\<^sub>s \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, Normal \<Sigma>) \<rightarrow> (Skip, Normal \<Sigma>')" 
    using await_step_sim_cond[OF a0 a7 a6 a8 a9] by auto
  moreover have step:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq S1 S2, Normal \<Sigma>) \<rightarrow> (Seq Skip S2, Normal \<Sigma>')"
    using Seqc calculation by fastforce
  moreover have x:"(\<Gamma>\<^sub>c,(C,Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S2, Normal \<Sigma>'),R\<^sub>s,G\<^sub>s)"
    using  calculation Spec_Seq_Skip_sim[OF a1 a1' a2  a4  a10] 
    unfolding RGSim_pre_def by auto  
  ultimately obtain \<Sigma>n' where sim:"((Normal \<sigma>, Normal \<sigma>), Normal \<Sigma>', Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                 (\<sigma>, \<Sigma>n') \<in> \<gamma>\<^sub>a \<and>
                 \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq Skip S2, Normal \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Throw, Normal \<Sigma>n')"   
    using sim_elim_cases_c(2)[OF x[simplified a11]] by auto   
  moreover have "((Normal \<sigma>, Normal \<sigma>), Normal \<Sigma>, Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
    using related_transition_tran[OF subsetD[OF a0' a0]] calculation sim_cond by auto
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq S1 S2, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Throw, Normal \<Sigma>n')"
    using step calculation by auto
  ultimately show ?thesis by auto    
qed

lemma spec_mod_state_only_Await_sound3:
  assumes 
  a0:"(\<sigma>, \<Sigma>) \<in> \<xi>" and a0':"\<xi>\<subseteq>\<alpha>" and a1:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and a1':"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
  a2:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and  
  a4:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and   
  a6:"S1 = Await b Ss \<tau>" and a7:"Range \<xi> \<subseteq> b" and
  a8:"\<forall>\<sigma>n \<Sigma>n. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
        (b \<inter> {s. \<Sigma>n = s \<and> (\<sigma>n,\<Sigma>n)\<in>\<xi>}) Ss 
        ({s. (Normal \<Sigma>n, Normal s) \<in> G\<^sub>s \<and> (\<sigma>n, s)\<in> \<xi>\<^sub>1}), {}" and
  a9:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Ss,Normal \<sigma>\<rangle> \<Rightarrow> Fault f" and
  a10:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" and   
  a11:"C = Skip" shows
      "\<exists>\<Sigma>n'. ((Normal \<sigma>, Normal \<sigma>), Normal \<Sigma>, Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<sigma>, \<Sigma>n') \<in> \<gamma>\<^sub>n \<and> \<gamma>\<^sub>n \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq S1 S2, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, Normal \<Sigma>n')"
proof-

obtain \<Sigma>' where 
   sim_cond:"(\<sigma>, \<Sigma>') \<in> \<xi>\<^sub>1 \<and> (Normal \<Sigma>, Normal \<Sigma>')\<in>G\<^sub>s \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, Normal \<Sigma>) \<rightarrow> (Skip, Normal \<Sigma>')" 
    using await_step_sim_cond[OF a0 a7 a6 a8 a9] by auto
  moreover have step:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq S1 S2, Normal \<Sigma>) \<rightarrow> (Seq Skip S2, Normal \<Sigma>')"
    using Seqc calculation by fastforce
  moreover have x:"(\<Gamma>\<^sub>c,(C,Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S2, Normal \<Sigma>'),R\<^sub>s,G\<^sub>s)"
    using  calculation Spec_Seq_Skip_sim[OF a1 a1' a2  a4 a10] 
    unfolding RGSim_pre_def by auto  
  ultimately obtain \<Sigma>n' where sim:"((Normal \<sigma>, Normal \<sigma>), Normal \<Sigma>', Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<sigma>, \<Sigma>n') \<in> \<gamma>\<^sub>n \<and> \<gamma>\<^sub>n \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq Skip S2, Normal \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, Normal \<Sigma>n')"   
    using sim_elim_cases_c(1)[OF x[simplified a11]] by auto   
  moreover have "((Normal \<sigma>, Normal \<sigma>), Normal \<Sigma>, Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
    using related_transition_tran[OF subsetD[OF a0' a0]] calculation sim_cond by auto
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq S1 S2, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, Normal \<Sigma>n')"
    using step calculation by auto
  ultimately show ?thesis by auto    
qed

lemma spec_mod_state_only_Await_sound4: assumes 
  a0:"(\<sigma>, \<Sigma>) \<in> \<xi>" and  a0':"\<xi>\<subseteq>\<alpha>" and a1:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and a1':"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
  a2:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and 
  a4:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and 
  a6:"S1 = Await b Ss \<tau>" and a7:"Range \<xi> \<subseteq> b" and
  a8:"\<forall>\<sigma>n \<Sigma>n. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
        (b \<inter> {s. \<Sigma>n = s \<and> (\<sigma>n,\<Sigma>n)\<in>\<xi>}) Ss 
        ({s. (Normal \<Sigma>n, Normal s) \<in> G\<^sub>s \<and> (\<sigma>n, s)\<in> \<xi>\<^sub>1}), {}" and
  a9:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Ss,Normal \<sigma>\<rangle> \<Rightarrow> Fault f" and
  a10:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" and 
  a11:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C, Normal \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n')"
  shows  "\<exists>c\<^sub>s' \<Sigma>n'.
          (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq S1 S2, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                 (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n'))) \<and>
          (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
          ((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
          (c\<^sub>c' = C \<and> c\<^sub>s' = LanguageCon.com.Seq S1 S2 \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or> (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
           (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))"
proof-
 obtain \<Sigma>' where 
   sim_cond:"(\<sigma>, \<Sigma>') \<in> \<xi>\<^sub>1 \<and> (Normal \<Sigma>, Normal \<Sigma>')\<in>G\<^sub>s \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, Normal \<Sigma>) \<rightarrow> (Skip, Normal \<Sigma>')" 
    using await_step_sim_cond[OF a0 a7 a6 a8 a9] by auto
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq S1 S2, Normal \<Sigma>) \<rightarrow> (Seq Skip S2, Normal \<Sigma>')"
    using Seqc calculation by fastforce
  moreover have x:"(\<Gamma>\<^sub>c,(C,Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S2, Normal \<Sigma>'),R\<^sub>s,G\<^sub>s)"
    using  calculation Spec_Seq_Skip_sim[OF a1 a1' a2  a4  a10] 
    unfolding RGSim_pre_def by auto  
  moreover obtain c\<^sub>s' \<Sigma>n' where 
        "(\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq LanguageCon.com.Skip S2, Normal \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                   (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n'))) \<and>
            (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
            ((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and> (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
            (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)" 
    using a11 sim_elim_cases[OF x] by metis 
  moreover have "((Normal \<sigma>, Normal  \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
    using related_transition_tran[OF subsetD[OF a0' a0]] calculation sim_cond 
    by auto
  ultimately show ?thesis
    by (metis (no_types, lifting) converse_rtranclp_into_rtranclp)
qed

lemma spec_mod_state_only_Await_sound5: assumes 
  a0:"(\<sigma>, \<Sigma>) \<in> \<xi>" and  a0':"\<xi>\<subseteq>\<alpha>" and a1:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and a1':"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
  a2:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and 
  a4:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and   
  a6:"S1 = Await b Ss \<tau>" and a7:"Range \<xi> \<subseteq> b" and
  a8:"\<forall>\<sigma>n \<Sigma>n. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
        (b \<inter> {s. \<Sigma>n = s \<and> (\<sigma>n,\<Sigma>n)\<in>\<xi>}) Ss 
        ({s. (Normal \<Sigma>n, Normal s) \<in> G\<^sub>s \<and> (\<sigma>n, s)\<in> \<xi>\<^sub>1}), {}" and
  a9:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Ss,Normal \<sigma>\<rangle> \<Rightarrow> Fault f" and
  a10:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" and 
  a11:" \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (C, Normal \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n')"
  shows  "\<exists>c\<^sub>s' \<Sigma>n'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq S1 S2, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
                  (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and> ((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                  (c\<^sub>c' = C \<and> c\<^sub>s' = LanguageCon.com.Seq S1 S2 \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or>
                   (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))"
proof-
 obtain \<Sigma>' where 
   sim_cond:"(\<sigma>, \<Sigma>') \<in> \<xi>\<^sub>1 \<and> (Normal \<Sigma>, Normal \<Sigma>')\<in>G\<^sub>s \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, Normal \<Sigma>) \<rightarrow> (Skip, Normal \<Sigma>')" 
    using await_step_sim_cond[OF a0 a7 a6 a8 a9] by auto
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq S1 S2, Normal \<Sigma>) \<rightarrow> (Seq Skip S2, Normal \<Sigma>')"
    using Seqc calculation by fastforce
  moreover have x:"(\<Gamma>\<^sub>c,(C,Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S2, Normal \<Sigma>'),R\<^sub>s,G\<^sub>s)"
    using  calculation Spec_Seq_Skip_sim[OF a1 a1' a2 a4 a10] 
    unfolding RGSim_pre_def by auto  
  moreover obtain c\<^sub>s' \<Sigma>n' where 
        "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq Skip S2, Normal \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
                  (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and> ((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                  ((\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))" 
    using a11 sim_elim_cases[OF x] by metis 
  moreover have "((Normal \<sigma>, Normal  \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
    using related_transition_tran[OF subsetD[OF a0' a0]] calculation sim_cond 
    by auto
  ultimately show ?thesis 
    by (metis (no_types, lifting) converse_rtranclp_into_rtranclp)
qed

lemma seq_await_spec_sim: 
  assumes
 a1:"\<xi> \<subseteq> \<alpha>" and  a2:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and 
 a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and 
 a9:"S1 = Await b Ss \<tau>" and a9':"Range \<xi> \<subseteq> b" and 
 a10:"\<forall>\<sigma>n \<Sigma>n. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
        (b \<inter> {s. \<Sigma>n = s \<and> (\<sigma>n,\<Sigma>n)\<in>\<xi>}) Ss 
        ({s. (Normal \<Sigma>n, Normal s) \<in> G\<^sub>s \<and> (\<sigma>n, s)\<in> \<xi>\<^sub>1}), {}" and
 a11:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Ss,Normal \<sigma>\<rangle> \<Rightarrow> Fault f" and
 a12:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" 
shows "(\<Gamma>\<^sub>c,C ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,Seq S1 S2,R\<^sub>s,G\<^sub>s)"    
proof-
  {fix \<sigma> \<Sigma> 
    assume "(\<sigma>, \<Sigma>) \<in> \<xi>"    
    then have "(\<Gamma>\<^sub>c,(C, Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq S1 S2, Normal \<Sigma>),R\<^sub>s,G\<^sub>s)"
      apply (coinduction arbitrary: \<sigma> \<Sigma>)
      apply clarsimp
      apply (rule conjId)+       
             apply (rule, rule, rule, rule, frule  spec_mod_state_only_Await_sound1[OF  _ a2 a4 a6  a7  a9 a9' a10 a11 a12], fast+)
            apply (rule, frule spec_mod_state_only_Await_sound2[OF _ a1 a2 a4 a6  a7  a9 a9' a10 a11 a12], fast+)
          apply (rule, frule spec_mod_state_only_Await_sound3[OF _ a1 a2 a4 a6  a7  a9 a9' a10 a11 a12], fast+)
          apply (blast dest: sim_env[OF _ a3 a6 a7])
         apply (rule, rule, rule, rule,frule spec_mod_state_only_Await_sound4[OF _ a1 a2 a4 a6  a7  a9 a9' a10 a11 a12], fast+)      
      apply (rule, rule, rule, frule spec_mod_state_only_Await_sound5[OF _ a1 a2 a4 a6  a7  a9 a9' a10 a11 a12], fast+)
      using  a1 unfolding alpha_xstate_def by auto   
  } then show ?thesis unfolding RGSim_pre_def by auto
qed

lemma mod_state_tran_v_spec: "label C1 = \<tau> \<Longrightarrow>        
       \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>Some v (LanguageCon.com.Seq C1 C2, Normal \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<Longrightarrow>
       \<exists>c\<^sub>s' \<Sigma>n'.
          (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                 (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n'))) \<and>
          (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
          ((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
          (c\<^sub>c' = LanguageCon.com.Seq C1 C2 \<and> c\<^sub>s' = S \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or> (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c)
           \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))"
proof -
assume a1: "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>Some v (LanguageCon.com.Seq C1 C2, Normal \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n')"
  assume a2: "label C1 = \<tau>"
  obtain c1' where s:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C1, Normal \<sigma>) \<rightarrow> (c1', Normal \<sigma>n')" 
    using stepc_elim_cases1(5)[OF a1] by fastforce    
  thus ?thesis using label_step[OF _ s] a2 by force 
qed

lemma mod_state_only_impl_basic_tau_sound1:
  assumes a0:"C1 = Basic fc \<tau> \<or> C1 = Spec rc \<tau>" and   
 a1:"(\<sigma>, \<Sigma>) \<in> \<xi>" and 
 a2: "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (LanguageCon.com.Seq C1 C2, Normal \<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>')" and 
 a3:"(\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n)" and 
 a4:"\<forall>\<sigma> \<sigma>' \<Sigma> . (\<sigma>, \<Sigma>)\<in>\<xi> \<and> \<sigma>' \<in> com_step  C1 (Normal \<sigma>)  \<Gamma>\<^sub>c  \<longrightarrow> 
                (\<exists>\<sigma>n'. \<sigma>' = Normal \<sigma>n' \<and> (\<sigma>n',\<Sigma>)\<in>\<xi>\<^sub>1 \<and> (Normal \<sigma>, Normal \<sigma>n') \<in> G\<^sub>c)"
shows "\<exists>\<Sigma>'. (\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x \<and>
             (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<or>
                      (\<exists>v. e = Some v \<and>
                           (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                                  (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, b) \<rightarrow> (aa, ba) \<and>
                                           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'))))) \<and> (Normal \<sigma>,\<sigma>')\<in>G\<^sub>c \<and>
                     (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s))"
proof-
  {
    assume a00:"C1 = Basic fc \<tau>"    
    then have "\<sigma>' = Normal (fc \<sigma>)" using a2 
      by (metis LanguageCon.com.simps(12) LanguageCon.com.simps(48) Pair_inject stepc_Normal_elim_cases(3) stepc_Normal_elim_cases(5) stepce_stepc)     
    then have ?thesis using a3 by auto
  }
  moreover {
    assume a00:"C1 = Spec rc \<tau>"   
    then have e:"e=\<tau>"  using a2 label_step by fastforce
    have c\<^sub>c':"c\<^sub>c' = Seq Skip C2" using stepc_elim_cases1(5)[OF a2[simplified a00]]
    proof -
      obtain cc xx where
        f1: "(c\<^sub>c', \<sigma>') = (LanguageCon.com.Seq cc C2, xx) \<and> 
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (LanguageCon.com.Spec rc \<tau>, Normal \<sigma>) \<rightarrow> (cc, xx)"
        using stepc_elim_cases1(5)[OF a2[simplified a00]]  by force
      thus ?thesis
        using stepc_elim_cases1(4) by fastforce
    qed       
    moreover have step:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Spec rc \<tau>, Normal \<sigma>) \<rightarrow> (Skip, \<sigma>')"
     using  stepc_elim_cases(6)[OF a2[simplified a00 c\<^sub>c'], simplified e] by auto    
    moreover have \<sigma>:"\<sigma>' = Stuck" using stepc_elim_cases1(4)[OF step] a3     
      by fastforce
    moreover  have "(\<nexists>sn.(\<sigma>, sn)\<in>rc)" using stepc_elim_cases(3)[OF step[simplified \<sigma>]] by auto
    moreover have "\<sigma>' \<in> com_step  C1 (Normal \<sigma>)  \<Gamma>\<^sub>c " using calculation a00 by auto
    ultimately have ?thesis using a4 a00 a1 \<sigma> by fast
  } ultimately show ?thesis using a0 by auto  
qed

lemma mod_state_only_impl_basic_tau_sound2:
  assumes a0:"\<xi> \<subseteq> \<alpha> " and a0':"\<xi>\<^sub>1 \<subseteq> \<alpha> " and a1:"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and 
          a2:"(\<sigma>, \<Sigma>) \<in> \<xi>" and 
       a3:"\<forall>\<sigma> \<sigma>' \<Sigma> . (\<sigma>, \<Sigma>)\<in>\<xi> \<and> \<sigma>' \<in> com_step  C1 (Normal \<sigma>)  \<Gamma>\<^sub>c  \<longrightarrow> 
                (\<exists>\<sigma>n'. \<sigma>' = Normal \<sigma>n' \<and> (\<sigma>n',\<Sigma>)\<in>\<xi>\<^sub>1 \<and> (Normal \<sigma>, Normal \<sigma>n') \<in> G\<^sub>c)" and
       a4:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Seq C1 C2, Normal \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n')" and
       a5:"C1 = Basic fc \<tau> \<or> C1 = Spec rc \<tau>" and 
      a6:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and 
      a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and a8:"(\<Gamma>\<^sub>c,C2,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)" 
  shows "(\<exists>c\<^sub>s' \<Sigma>n'.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
          (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
          ((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          (c\<^sub>c' = LanguageCon.com.Seq C1 C2 \<and> c\<^sub>s' = S \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))"
proof-
  have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (S, Normal \<Sigma>)" by auto
  moreover have "(Normal \<Sigma>, Normal \<Sigma>) \<in> G\<^sub>s\<^sup>*"  by auto
  moreover have "c\<^sub>c' = Seq Skip C2 \<and> (\<sigma>n',\<Sigma>)\<in>\<xi>\<^sub>1 \<and> (Normal \<sigma>, Normal \<sigma>n') \<in> G\<^sub>c" 
                 using a5
  proof
    assume a00:"C1 = LanguageCon.com.Basic fc \<tau> "    
    then have "c\<^sub>c' = Seq Skip C2" using a4
      by (metis LanguageCon.com.distinct(1) LanguageCon.com.distinct(37) prod.sel(1) 
          stepc_Normal_elim_cases(3) stepc_Normal_elim_cases(5) stepce_stepc)
    moreover have "(\<sigma>n',\<Sigma>)\<in>\<xi>\<^sub>1 \<and> (Normal \<sigma>, Normal \<sigma>n') \<in> G\<^sub>c"  
    proof -
      have "\<sigma>n' = fc \<sigma>" using a4[simplified calculation a00]
        by (meson CRef.stepc_elim_cases(6) Pair_inject stepc_Normal_elim_cases(3) stepce_stepc xstate.inject(1))
      then show ?thesis using a3[simplified a00] a2 by auto
    qed
    ultimately show ?thesis by auto    
  next
    assume a00:"C1 = LanguageCon.com.Spec rc \<tau>"
    have c\<^sub>c':"c\<^sub>c' = Seq Skip C2" using stepc_elim_cases1(5)[OF a4[simplified a00]]
    proof -
      obtain cc xx where
        f1: "(c\<^sub>c', Normal \<sigma>n') = (LanguageCon.com.Seq cc C2, xx) \<and> 
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Spec rc \<tau>, Normal \<sigma>) \<rightarrow> (cc, xx)"
        using stepc_elim_cases1(5)[OF a4[simplified a00]]  by force
      thus ?thesis
        using stepc_elim_cases1(4) by fastforce
    qed
    moreover have "(\<sigma>n',\<Sigma>)\<in>\<xi>\<^sub>1 \<and> (Normal \<sigma>, Normal \<sigma>n') \<in> G\<^sub>c"  
    proof-
      have "(\<sigma>,\<sigma>n')\<in>rc" using a4[simplified calculation a00]
        by (meson CRef.stepc_elim_cases(2) CRef.stepc_elim_cases(6)) 
      then show ?thesis  using a3[simplified a00] a2 by auto
    qed
    ultimately show ?thesis  by auto          
qed 
  moreover have "(\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, Normal \<Sigma>),R\<^sub>s,G\<^sub>s)"
    using Impl_Seq_Skip_sim[OF a0' a1 a6  a7  a8] calculation 
    unfolding RGSim_pre_def by auto
  ultimately show ?thesis using a0' a0 a2 unfolding related_transitions_def by fast
qed

lemma spec_tran_basic_sim_cond:assumes 
  a0:"(\<sigma>, \<Sigma>) \<in> \<xi>" and
  a1:"\<forall>\<sigma> \<Sigma> \<Sigma>'.
       (\<sigma>, \<Sigma>) \<in> \<xi> \<and> \<Sigma>' \<in> com_step S1 (Normal \<Sigma>) \<Gamma>\<^sub>s \<longrightarrow>
       (\<exists>\<Sigma>n'. \<Sigma>' = Normal \<Sigma>n' \<and> (\<sigma>, \<Sigma>n') \<in> \<xi>\<^sub>1 \<and> (Normal \<Sigma>, Normal \<Sigma>n') \<in> G\<^sub>s)" and
  a2:    "S1 = LanguageCon.com.Basic fc \<tau> "
obtains \<Sigma>n' where "(\<sigma>, \<Sigma>n') \<in> \<xi>\<^sub>1 \<and> (Normal \<Sigma>, Normal \<Sigma>n')\<in>G\<^sub>s \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, Normal \<Sigma>) \<rightarrow> (Skip, Normal \<Sigma>n')"
proof-
  have "Normal (fc \<Sigma>) \<in> com_step S1 (Normal \<Sigma>) \<Gamma>\<^sub>s" using a2 by auto
  then have "(\<exists>\<Sigma>n'. Normal (fc \<Sigma>) = Normal \<Sigma>n' \<and> (\<sigma>, (fc \<Sigma>)) \<in> \<xi>\<^sub>1 \<and> (Normal \<Sigma>, Normal (fc \<Sigma>)) \<in> G\<^sub>s)"
    using a1 a0 by auto
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, Normal \<Sigma>) \<rightarrow> (Skip, Normal (fc \<Sigma>))"
    using Basicc a2 by auto
  ultimately show ?thesis using that by auto
qed

lemma spec_tran_spec_sim_cond:assumes 
  a0:"(\<sigma>, \<Sigma>) \<in> \<xi>" and
  a1:"\<forall>\<sigma> \<Sigma> \<Sigma>'.
       (\<sigma>, \<Sigma>) \<in> \<xi> \<and> \<Sigma>' \<in> com_step S1 (Normal \<Sigma>) \<Gamma>\<^sub>s \<longrightarrow>
       (\<exists>\<Sigma>n'. \<Sigma>' = Normal \<Sigma>n' \<and> (\<sigma>, \<Sigma>n') \<in> \<xi>\<^sub>1 \<and> (Normal \<Sigma>, Normal \<Sigma>n') \<in> G\<^sub>s)" and
  a2:    "S1 = Spec r \<tau> "
obtains \<Sigma>n' where "(\<sigma>, \<Sigma>n') \<in> \<xi>\<^sub>1 \<and> (Normal \<Sigma>, Normal \<Sigma>n')\<in>G\<^sub>s \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, Normal \<Sigma>) \<rightarrow> (Skip, Normal \<Sigma>n')"
proof-
  {assume a00: "\<exists>\<Sigma>'. (\<Sigma>,\<Sigma>') \<in> r"
    then obtain \<Sigma>' where a00:"(\<Sigma>,\<Sigma>') \<in> r" by auto
    then have "Normal \<Sigma>' \<in> com_step S1 (Normal \<Sigma>) \<Gamma>\<^sub>s" using a2 by auto
    then have "(\<exists>\<Sigma>n'. Normal \<Sigma>' = Normal \<Sigma>n' \<and> (\<sigma>, \<Sigma>') \<in> \<xi>\<^sub>1 \<and> (Normal \<Sigma>, Normal \<Sigma>') \<in> G\<^sub>s)"
      using a1 a0 by auto
    moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, Normal \<Sigma>) \<rightarrow> (Skip, Normal \<Sigma>')"
      using Specc a2 a00 by auto
    ultimately have ?thesis using that by auto  
  }
  moreover
  {assume a00: "\<not>(\<exists>\<Sigma>'. (\<Sigma>,\<Sigma>') \<in> r)"    
    then have "Stuck \<in> com_step S1 (Normal \<Sigma>) \<Gamma>\<^sub>s" using a2 by auto    
    then have ?thesis using that a1  a0 by auto  
  }
  ultimately show ?thesis  by auto
qed

lemma spec_mod_non_await_sound1: assumes 
  a0:"(\<sigma>, \<Sigma>) \<in> \<xi>" and a1:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and a1':"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
  a2:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and
  a4:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and  
  a6:"S1 = Basic fc \<tau> \<or> S1 = Spec rc \<tau>" and 
  a7:"\<forall>\<sigma> \<Sigma> \<Sigma>' . (\<sigma>, \<Sigma>)\<in>\<xi> \<and> \<Sigma>' \<in> com_step  S1 (Normal \<Sigma>)  \<Gamma>\<^sub>s  \<longrightarrow> 
                (\<exists>\<Sigma>n'. \<Sigma>' = Normal \<Sigma>n' \<and> (\<sigma>,\<Sigma>n')\<in>\<xi>\<^sub>1 \<and> (Normal \<Sigma>, Normal \<Sigma>n') \<in> G\<^sub>s)" and
  a8:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" and 
  a9:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (C, Normal \<sigma>) \<rightarrow> (c\<^sub>c', \<sigma>') \<and> (\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n)"
  shows  "(\<exists>\<Sigma>'. (\<sigma>', \<Sigma>') \<in> \<alpha>\<^sub>x \<and>
               (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq S1 S2, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>') \<or>
                        (\<exists>v. e = Some v \<and>
                             (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq S1 S2, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                                    (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                                             \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'))))) \<and> (Normal \<sigma>,\<sigma>')\<in>G\<^sub>c \<and>
                       (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)))"
proof-
  obtain \<Sigma>' where 
   "(\<sigma>, \<Sigma>') \<in> \<xi>\<^sub>1 \<and> (Normal \<Sigma>, Normal \<Sigma>')\<in>G\<^sub>s \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, Normal \<Sigma>) \<rightarrow> (Skip, Normal \<Sigma>')" 
    using a6 spec_tran_basic_sim_cond[OF a0 a7] spec_tran_spec_sim_cond[OF a0 a7] by blast     
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq S1 S2, Normal \<Sigma>) \<rightarrow> (Seq Skip S2, Normal \<Sigma>')"
    using Seqc calculation by fastforce
  moreover have x:"(\<Gamma>\<^sub>c,(C,Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S2, Normal \<Sigma>'),R\<^sub>s,G\<^sub>s)"
    using  calculation Spec_Seq_Skip_sim[OF a1 a1' a2  a4  a8] 
    unfolding RGSim_pre_def by auto  
  moreover have "(\<exists>\<Sigma>''. (\<sigma>', \<Sigma>'') \<in> \<alpha>\<^sub>x \<and>
               (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq Skip S2, Normal \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'') \<or>
                        (\<exists>v. e = Some v \<and>
                             (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq Skip S2, Normal \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                                    (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                                             \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>''))))) \<and> (Normal \<sigma>,\<sigma>')\<in>G\<^sub>c \<and>
                       (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s)))" 
    using a9 sim_elim_cases[OF x] by fast  
  ultimately show ?thesis
    by (metis (no_types, lifting) converse_rtranclp_into_rtranclp)  
qed

lemma spec_mod_non_await2:
  assumes 
  a0:"(\<sigma>, \<Sigma>) \<in> \<xi>" and a0':"\<xi>\<subseteq>\<alpha>" and a1:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and a1':"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
  a2:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and
  a4:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and 
  a6:"S1 = Basic fc \<tau> \<or> S1 = Spec rc \<tau>" and 
  a7:"\<forall>\<sigma> \<Sigma> \<Sigma>' . (\<sigma>, \<Sigma>)\<in>\<xi> \<and> \<Sigma>' \<in> com_step  S1 (Normal \<Sigma>)  \<Gamma>\<^sub>s  \<longrightarrow> 
                (\<exists>\<Sigma>n'. \<Sigma>' = Normal \<Sigma>n' \<and> (\<sigma>,\<Sigma>n')\<in>\<xi>\<^sub>1 \<and> (Normal \<Sigma>, Normal \<Sigma>n') \<in> G\<^sub>s)" and
  a8:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" and   
  a11:"C = LanguageCon.com.Throw" shows
      "\<exists>\<Sigma>n'. ((Normal \<sigma>, Normal \<sigma>), Normal \<Sigma>, Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
              (\<sigma>, \<Sigma>n') \<in> \<gamma>\<^sub>a \<and>
              \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq S1 S2, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Throw, Normal \<Sigma>n')"
proof-

  obtain \<Sigma>' where 
    sim_cond:"(\<sigma>, \<Sigma>') \<in> \<xi>\<^sub>1 \<and> (Normal \<Sigma>, Normal \<Sigma>')\<in>G\<^sub>s \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, Normal \<Sigma>) \<rightarrow> (Skip, Normal \<Sigma>')" 
    using a6 spec_tran_basic_sim_cond[OF a0 a7] spec_tran_spec_sim_cond[OF a0 a7] by blast
  moreover have step:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq S1 S2, Normal \<Sigma>) \<rightarrow> (Seq Skip S2, Normal \<Sigma>')"
    using Seqc calculation by fastforce
  moreover have x:"(\<Gamma>\<^sub>c,(C,Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S2, Normal \<Sigma>'),R\<^sub>s,G\<^sub>s)"
    using  calculation Spec_Seq_Skip_sim[OF a1 a1' a2  a4 a8] 
    unfolding RGSim_pre_def by auto  
  ultimately obtain \<Sigma>n' where sim:"((Normal \<sigma>, Normal \<sigma>), Normal \<Sigma>', Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                 (\<sigma>, \<Sigma>n') \<in> \<gamma>\<^sub>a \<and>
                 \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq Skip S2, Normal \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Throw, Normal \<Sigma>n')"   
    using sim_elim_cases_c(2)[OF x[simplified a11]] by auto   
  moreover have "((Normal \<sigma>, Normal \<sigma>), Normal \<Sigma>, Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
    using related_transition_tran[OF subsetD[OF a0' a0]] calculation sim_cond by auto
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq S1 S2, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Throw, Normal \<Sigma>n')"
    using step calculation by auto
  ultimately show ?thesis by auto    
qed

lemma spec_mod_non_await3:
  assumes 
  a0:"(\<sigma>, \<Sigma>) \<in> \<xi>" and a0':"\<xi>\<subseteq>\<alpha>" and a1:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and a1':"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
  a2:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and 
  a4:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and  
  a6:"S1 = Basic fc \<tau> \<or> S1 = Spec rc \<tau>" and 
  a7:"\<forall>\<sigma> \<Sigma> \<Sigma>' . (\<sigma>, \<Sigma>)\<in>\<xi> \<and> \<Sigma>' \<in> com_step  S1 (Normal \<Sigma>)  \<Gamma>\<^sub>s  \<longrightarrow> 
                (\<exists>\<Sigma>n'. \<Sigma>' = Normal \<Sigma>n' \<and> (\<sigma>,\<Sigma>n')\<in>\<xi>\<^sub>1 \<and> (Normal \<Sigma>, Normal \<Sigma>n') \<in> G\<^sub>s)" and
  a8:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" and 
  a11:"C = Skip" shows
      "\<exists>\<Sigma>n'. ((Normal \<sigma>, Normal \<sigma>), Normal \<Sigma>, Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<sigma>, \<Sigma>n') \<in> \<gamma>\<^sub>n \<and> \<gamma>\<^sub>n \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq S1 S2, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, Normal \<Sigma>n')"
proof-

obtain \<Sigma>' where 
   sim_cond:"(\<sigma>, \<Sigma>') \<in> \<xi>\<^sub>1 \<and> (Normal \<Sigma>, Normal \<Sigma>')\<in>G\<^sub>s \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, Normal \<Sigma>) \<rightarrow> (Skip, Normal \<Sigma>')" 
    using a6 spec_tran_basic_sim_cond[OF a0 a7] spec_tran_spec_sim_cond[OF a0 a7] by blast
  moreover have step:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq S1 S2, Normal \<Sigma>) \<rightarrow> (Seq Skip S2, Normal \<Sigma>')"
    using Seqc calculation by fastforce
  moreover have x:"(\<Gamma>\<^sub>c,(C,Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S2, Normal \<Sigma>'),R\<^sub>s,G\<^sub>s)"
    using  calculation Spec_Seq_Skip_sim[OF a1 a1' a2  a4  a8] 
    unfolding RGSim_pre_def by auto  
  ultimately obtain \<Sigma>n' where sim:"((Normal \<sigma>, Normal \<sigma>), Normal \<Sigma>', Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (\<sigma>, \<Sigma>n') \<in> \<gamma>\<^sub>n \<and> \<gamma>\<^sub>n \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq Skip S2, Normal \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, Normal \<Sigma>n')"   
    using sim_elim_cases_c(1)[OF x[simplified a11]] by auto   
  moreover have "((Normal \<sigma>, Normal \<sigma>), Normal \<Sigma>, Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
    using related_transition_tran[OF subsetD[OF a0' a0]] calculation sim_cond by auto
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq S1 S2, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, Normal \<Sigma>n')"
    using step calculation by auto
  ultimately show ?thesis by auto    
qed

lemma spec_mod_non_await4: assumes 
  a0:"(\<sigma>, \<Sigma>) \<in> \<xi>" and a0':"\<xi>\<subseteq>\<alpha>" and a1:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and a1':"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
  a2:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and
  a4:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and 
  a6:"S1 = Basic fc \<tau> \<or> S1 = Spec rc \<tau>" and 
  a7:"\<forall>\<sigma> \<Sigma> \<Sigma>' . (\<sigma>, \<Sigma>)\<in>\<xi> \<and> \<Sigma>' \<in> com_step  S1 (Normal \<Sigma>)  \<Gamma>\<^sub>s  \<longrightarrow> 
                (\<exists>\<Sigma>n'. \<Sigma>' = Normal \<Sigma>n' \<and> (\<sigma>,\<Sigma>n')\<in>\<xi>\<^sub>1 \<and> (Normal \<Sigma>, Normal \<Sigma>n') \<in> G\<^sub>s)" and
  a8:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" and 
  a9:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C, Normal \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n')"
  shows  "\<exists>c\<^sub>s' \<Sigma>n'.
          (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq S1 S2, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                 (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n'))) \<and>
          (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
          ((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
          (c\<^sub>c' = C \<and> c\<^sub>s' = LanguageCon.com.Seq S1 S2 \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or> (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
           (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))"
proof-
 obtain \<Sigma>' where 
   sim_cond:"(\<sigma>, \<Sigma>') \<in> \<xi>\<^sub>1 \<and> (Normal \<Sigma>, Normal \<Sigma>')\<in>G\<^sub>s \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, Normal \<Sigma>) \<rightarrow> (Skip, Normal \<Sigma>')" 
    using a6 spec_tran_basic_sim_cond[OF a0 a7] spec_tran_spec_sim_cond[OF a0 a7] by blast
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq S1 S2, Normal \<Sigma>) \<rightarrow> (Seq Skip S2, Normal \<Sigma>')"
    using Seqc calculation by fastforce
  moreover have x:"(\<Gamma>\<^sub>c,(C,Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S2, Normal \<Sigma>'),R\<^sub>s,G\<^sub>s)"
    using  calculation Spec_Seq_Skip_sim[OF a1 a1' a2  a4 a8] 
    unfolding RGSim_pre_def by auto  
  moreover obtain c\<^sub>s' \<Sigma>n' where 
        "(\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq LanguageCon.com.Skip S2, Normal \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                   (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n'))) \<and>
            (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
            ((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and> (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
            (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)" 
    using a9 sim_elim_cases[OF x] by metis 
  moreover have "((Normal \<sigma>, Normal  \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
    using related_transition_tran[OF subsetD[OF a0' a0]] calculation sim_cond 
    by auto
  ultimately show ?thesis
    by (metis (no_types, lifting) converse_rtranclp_into_rtranclp)
qed

lemma spec_mod_non_await5: assumes 
   a0:"(\<sigma>, \<Sigma>) \<in> \<xi>" and a0':"\<xi>\<subseteq>\<alpha>" and a1:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and a1':"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
  a2:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and  
  a4:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and   
  a6:"S1 = Basic fc \<tau> \<or> S1 = Spec rc \<tau>" and 
  a7:"\<forall>\<sigma> \<Sigma> \<Sigma>' . (\<sigma>, \<Sigma>)\<in>\<xi> \<and> \<Sigma>' \<in> com_step  S1 (Normal \<Sigma>)  \<Gamma>\<^sub>s  \<longrightarrow> 
                (\<exists>\<Sigma>n'. \<Sigma>' = Normal \<Sigma>n' \<and> (\<sigma>,\<Sigma>n')\<in>\<xi>\<^sub>1 \<and> (Normal \<Sigma>, Normal \<Sigma>n') \<in> G\<^sub>s)" and
  a8:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" and 
  a11:" \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (C, Normal \<sigma>) \<rightarrow> (c\<^sub>c', Normal \<sigma>n')"
  shows  "\<exists>c\<^sub>s' \<Sigma>n'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq S1 S2, Normal \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
                  (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and> ((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                  (c\<^sub>c' = C \<and> c\<^sub>s' = LanguageCon.com.Seq S1 S2 \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or>
                   (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))"
proof-
 obtain \<Sigma>' where 
   sim_cond:"(\<sigma>, \<Sigma>') \<in> \<xi>\<^sub>1 \<and> (Normal \<Sigma>, Normal \<Sigma>')\<in>G\<^sub>s \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, Normal \<Sigma>) \<rightarrow> (Skip, Normal \<Sigma>')" 
    using a6 spec_tran_basic_sim_cond[OF a0 a7] spec_tran_spec_sim_cond[OF a0 a7] by blast
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq S1 S2, Normal \<Sigma>) \<rightarrow> (Seq Skip S2, Normal \<Sigma>')"
    using Seqc calculation by fastforce
  moreover have x:"(\<Gamma>\<^sub>c,(C,Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S2, Normal \<Sigma>'),R\<^sub>s,G\<^sub>s)"
    using  calculation Spec_Seq_Skip_sim[OF a1 a1' a2  a4  a8] 
    unfolding RGSim_pre_def by auto  
  moreover obtain c\<^sub>s' \<Sigma>n' where 
        "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq Skip S2, Normal \<Sigma>') \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
                  (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and> ((Normal \<sigma>, Normal \<sigma>n'), Normal \<Sigma>', Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                  ((\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s))" 
    using a11 sim_elim_cases[OF x] by metis 
  moreover have "((Normal \<sigma>, Normal  \<sigma>n'), Normal \<Sigma>, Normal \<Sigma>n') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
    using related_transition_tran[OF subsetD[OF a0' a0]] calculation sim_cond 
    by auto
  ultimately show ?thesis 
    by (metis (no_types, lifting) converse_rtranclp_into_rtranclp)
qed


lemma seq_non_await_spec_sim: 
  assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a5:"\<forall>sn. ( sn,  sn)\<in>G\<^sub>c" and
 a7:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and 
 a9:"S1 = Basic fc \<tau> \<or> S1 = Spec rc \<tau>" and   
 a10:"\<forall>\<sigma> \<Sigma> \<Sigma>' . (\<sigma>, \<Sigma>)\<in>\<xi> \<and> \<Sigma>' \<in> com_step  S1 (Normal \<Sigma>)  \<Gamma>\<^sub>s  \<longrightarrow> 
                (\<exists>\<Sigma>n'. \<Sigma>' = Normal \<Sigma>n' \<and> (\<sigma>,\<Sigma>n')\<in>\<xi>\<^sub>1 \<and> (Normal \<Sigma>, Normal \<Sigma>n') \<in> G\<^sub>s)" and
 a11:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)"
shows "(\<Gamma>\<^sub>c,C ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,Seq S1 S2,R\<^sub>s,G\<^sub>s)"  
  
proof-
  {fix \<sigma> \<Sigma> 
    assume a12: "(\<sigma>, \<Sigma>) \<in> \<xi>"    
    then have "(\<Gamma>\<^sub>c,(C, Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq S1 S2, Normal \<Sigma>),R\<^sub>s,G\<^sub>s)"
      apply (coinduction arbitrary: \<sigma> \<Sigma>)
      apply clarsimp
      apply (rule conjId)+ 
             apply (rule, rule, rule, rule, frule  spec_mod_non_await_sound1[OF  _ a2 a4 a5  a7  a9 a10 a11], fast+)      
            apply (rule, frule spec_mod_non_await2[OF _ a1 a2 a4 a5  a7  a9 a10 a11], fast+)
          apply (rule, frule spec_mod_non_await3[OF _ a1 a2 a4 a5  a7  a9 a10 a11], fast+)
          apply (blast dest: sim_env[OF _ a3 a5 a7])       
         apply (rule, rule, rule, rule,frule spec_mod_non_await4[OF _ a1 a2 a4 a5  a7  a9 a10 a11], fast+)      
      apply (rule, rule, rule, frule spec_mod_non_await5[OF _ a1 a2 a4 a5  a7 a9 a10 a11], fast+)
      using  a1 unfolding alpha_xstate_def by auto   
  } then show ?thesis unfolding RGSim_pre_def by auto
qed

lemma If_branch_sim:
  assumes 
  a1:"\<xi> \<subseteq> \<alpha> \<and> \<gamma>\<^sub>n\<subseteq>\<alpha>" and 
  a2:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and 
  a3:"(\<forall>s. ( s, s)\<in>G\<^sub>c)" and 
  a4:"R\<^sub>c\<subseteq>1\<alpha>\<^sub>x" and
  a5:"\<xi>\<^sub>1= \<xi> \<inter> (b\<^sub>c \<odot> {s. True})" and 
  a6:"\<xi>\<^sub>2= \<xi> \<inter> (-(b\<^sub>c) \<odot> {s. True} )" and  
  a7:"(\<sigma>,\<Sigma>)\<in>\<xi>" and
  a9:"(\<Gamma>\<^sub>c,c1\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c\<^sub>s,R\<^sub>s,G\<^sub>s)" and 
  a10:"(\<Gamma>\<^sub>c,c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>2\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c\<^sub>s,R\<^sub>s,G\<^sub>s)"
shows  
  "(\<Gamma>\<^sub>c,(Cond b\<^sub>c c1\<^sub>c c2\<^sub>c,Normal \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,Normal \<Sigma>),R\<^sub>s,G\<^sub>s)"
using  a1 a2 a3 a4  a5 a6 a7  a9 a10
  proof(coinduction arbitrary: \<sigma> \<Sigma>,clarsimp)    
    fix \<sigma>n \<Sigma>n
    assume 
       a0:"(\<sigma>n, \<Sigma>n) \<in> \<xi>" and              
       a3:"Sta\<^sub>s \<xi> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>" and                            
       a8:"\<xi> \<subseteq> \<alpha>" and       
       a11:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and       
       a13:"(\<forall>s. ( s, s)\<in>G\<^sub>c)"     
    have "(\<sigma>n, \<Sigma>n) \<in> \<alpha>" using a0 a8 by fastforce
    moreover have "(Normal \<sigma>n, Normal \<Sigma>n) \<in> \<alpha>\<^sub>x" unfolding alpha_xstate_def by auto 
    moreover have "\<forall>\<sigma>' \<Sigma>'.
           (((Normal \<sigma>n, \<sigma>'), Normal \<Sigma>n, \<Sigma>') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> (\<sigma>', \<Sigma>')\<in> \<alpha>\<^sub>x \<longrightarrow>
           (\<exists>\<sigma>n'. \<sigma>' = Normal \<sigma>n' \<and> (\<exists>\<Sigma>n'. \<Sigma>' = Normal \<Sigma>n' \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi>)) \<or>
           (\<Gamma>\<^sub>c,(Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
           (\<Gamma>\<^sub>s,(c\<^sub>s, \<Sigma>'),R\<^sub>s,G\<^sub>s)" 
      using sim_env[OF a0 a3 a13 a4] by blast
    moreover have "\<forall>v c\<^sub>c' \<sigma>n'.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, Normal \<sigma>n) \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow>
           (\<exists>c\<^sub>s' \<Sigma>n'.
               (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, Normal \<Sigma>n) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                      (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, b) \<rightarrow> (aa, ba) \<and>
                               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n'))) \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
               ((Normal \<sigma>n, Normal \<sigma>n'), Normal \<Sigma>n, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
               (c\<^sub>c' = LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c \<and> c\<^sub>s' = c\<^sub>s \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))"
      by (metis CRef.stepc_elim_cases(10) CRef.stepc_elim_cases(9) 
               option.distinct(1) stepc_Normal_elim_cases(6) stepce_stepc) 
    moreover have "\<forall>c\<^sub>c' \<sigma>n'.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, Normal \<sigma>n) \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow>
           (\<exists>c\<^sub>s' \<Sigma>n'.
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, Normal \<Sigma>n) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
               ((Normal \<sigma>n, Normal \<sigma>n'), Normal \<Sigma>n, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
               (c\<^sub>c' = LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c \<and> c\<^sub>s' = c\<^sub>s \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))"
    proof -
      {fix c\<^sub>c' \<sigma>n'
        assume  a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, Normal \<sigma>n) \<rightarrow> (c\<^sub>c', Normal \<sigma>n')"
        then have eqs:"\<sigma>n = \<sigma>n'"
          using stepc_elim_cases2(1) by fastforce 
        have guar:"((Normal \<sigma>n, Normal \<sigma>n), Normal \<Sigma>n, Normal \<Sigma>n) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
        using  a13 a0 a8  unfolding related_transitions_def Id_def by auto
       have h:"(c\<^sub>c'=c1\<^sub>c \<and> \<sigma>n'\<in>b\<^sub>c) \<or> (c\<^sub>c'=c2\<^sub>c \<and> \<sigma>n'\<in> -b\<^sub>c)"  
        using stepc_elim_cases2(1)[OF a00] by auto
        {
          assume c:"c\<^sub>c' = c1\<^sub>c \<and> \<sigma>n' \<in> b\<^sub>c"
          then have sig1:"(\<sigma>n',  \<Sigma>n) \<in> \<xi>\<^sub>1"
            using a0 a5 a6 a7 eqs unfolding eq_rel_def ToNorm_def and_rel_def by auto          
          then have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, Normal \<Sigma>n) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s, Normal \<Sigma>n)"          
            by (simp add:  r_into_rtranclp )        
          have x:"(\<Gamma>\<^sub>c,(c1\<^sub>c, Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, Normal \<Sigma>n),R\<^sub>s,G\<^sub>s)" 
            using a9  sig1
            unfolding RGSim_pre_def by auto
          note l = conjI[OF x steps]
        } note l=this        
        {
          assume c:"c\<^sub>c' = c2\<^sub>c \<and> \<sigma>n' \<in> -b\<^sub>c"
          then have sig1:"(\<sigma>n', \<Sigma>n) \<in> \<xi>\<^sub>2"
            using a0 a5 a6 a7 eqs unfolding eq_rel_def ToNorm_def and_rel_def by auto
          then have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, Normal \<Sigma>n) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s, Normal \<Sigma>n)"          
            by (simp add:  r_into_rtranclp)        
          have x:"(\<Gamma>\<^sub>c,(c2\<^sub>c, Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, Normal \<Sigma>n),R\<^sub>s,G\<^sub>s)" 
            using a10  sig1
            unfolding RGSim_pre_def by auto
          note l = conjI[OF x steps]          
        } 
        then have "(\<exists>c\<^sub>s' \<Sigma>n'.
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, Normal \<Sigma>n) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
               ((Normal \<sigma>n, Normal \<sigma>n'), Normal \<Sigma>n, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
               (c\<^sub>c' = LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c \<and> c\<^sub>s' = c\<^sub>s \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))" 
          using guar l h  eqs calculation(1) by fastforce
       } thus ?thesis by auto
     qed
     moreover have"\<forall>\<sigma>'' c\<^sub>c' e.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, Normal \<sigma>n) \<rightarrow> (c\<^sub>c', \<sigma>'') \<and>
           (\<forall>\<sigma>n. \<sigma>'' \<noteq> Normal \<sigma>n) \<longrightarrow>
           (\<exists>\<Sigma>''. (\<sigma>'', \<Sigma>'') \<in> \<alpha>\<^sub>x \<and>
                   (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, Normal \<Sigma>n) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'') \<or>
                            (\<exists>v. e = Some v \<and>
                                 (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, Normal \<Sigma>n) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                                        (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, b) \<rightarrow> (aa, ba) \<and>
                                                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>''))))) \<and>
                           (Normal \<sigma>n, \<sigma>'') \<in> G\<^sub>c \<and> (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                           (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s)))"
      by (meson prod.inject stepc_elim_cases2(1))
    ultimately show "(Normal \<sigma>n, Normal \<Sigma>n) \<in> \<alpha>\<^sub>x \<and>
       (\<sigma>n, \<Sigma>n) \<in> \<alpha> \<and>
       (\<forall>c\<^sub>c' \<sigma>n'.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, Normal \<sigma>n) \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow>
           (\<exists>c\<^sub>s' \<Sigma>n'.
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, Normal \<Sigma>n) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n') \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
               (((Normal \<sigma>n, Normal \<sigma>n'), Normal \<Sigma>n, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (c\<^sub>c' = LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c \<and> c\<^sub>s' = c\<^sub>s \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))) \<and>
       (\<forall>v c\<^sub>c' \<sigma>n'.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, Normal \<sigma>n) \<rightarrow> (c\<^sub>c', Normal \<sigma>n') \<longrightarrow>
           (\<exists>c\<^sub>s' \<Sigma>n'.
               (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, Normal \<Sigma>n) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                      (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v)(a, b) \<rightarrow> (aa, ba) \<and>
                               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', Normal \<Sigma>n'))) \<and>
               (\<sigma>n', \<Sigma>n') \<in> \<alpha> \<and>
               (((Normal \<sigma>n, Normal \<sigma>n'), Normal \<Sigma>n, Normal \<Sigma>n') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (c\<^sub>c' = LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c \<and> c\<^sub>s' = c\<^sub>s \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', Normal \<sigma>n'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', Normal \<Sigma>n'),R\<^sub>s,G\<^sub>s)))) \<and>
       (\<forall>\<sigma>'' \<Sigma>''.
           (((Normal \<sigma>n, \<sigma>''), Normal \<Sigma>n, \<Sigma>'') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> (\<sigma>'', \<Sigma>'') \<in> \<alpha>\<^sub>x \<longrightarrow>
           (\<exists>\<sigma>. \<sigma>'' = Normal \<sigma> \<and> (\<exists>\<Sigma>. \<Sigma>'' = Normal \<Sigma> \<and> (\<sigma>, \<Sigma>) \<in> \<xi>)) \<or>
           (\<Gamma>\<^sub>c,(LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
           (\<Gamma>\<^sub>s,(c\<^sub>s, \<Sigma>''),R\<^sub>s,G\<^sub>s)) \<and>
       (\<forall>\<sigma>'' c\<^sub>c' e.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, Normal \<sigma>n) \<rightarrow> (c\<^sub>c', \<sigma>'') \<and>
           (\<forall>\<sigma>n. \<sigma>'' \<noteq> Normal \<sigma>n) \<longrightarrow>
           (\<exists>\<Sigma>''. (\<sigma>'', \<Sigma>'') \<in> \<alpha>\<^sub>x \<and>
                   (\<exists>c\<^sub>s'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, Normal \<Sigma>n) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>'') \<or>
                            (\<exists>v. e = Some v \<and>
                                 (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, Normal \<Sigma>n) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                                        (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                                                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>''))))) \<and>
                           (Normal \<sigma>n, \<sigma>'') \<in> G\<^sub>c \<and> (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>''),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                           (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>''),R\<^sub>s,G\<^sub>s))))" 
      by auto
  qed    

lemma If_branch_imp_sound:
  "\<xi> \<subseteq> \<alpha> \<and> \<gamma>\<^sub>n\<subseteq>\<alpha> \<Longrightarrow> Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow> \<forall>s. ( s, s)\<in>G\<^sub>c  \<Longrightarrow> R\<^sub>c\<subseteq>1\<alpha>\<^sub>x \<Longrightarrow>
   \<xi>\<^sub>1= \<xi> \<inter> (b\<^sub>c \<odot> {s. True}) \<Longrightarrow> \<xi>\<^sub>2= \<xi> \<inter> (-(b\<^sub>c) \<odot> {s. True} ) \<Longrightarrow>
  (\<Gamma>\<^sub>c,c1\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow> 
  (\<Gamma>\<^sub>c,c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>2\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow> 
  (\<Gamma>\<^sub>c,Cond b\<^sub>c c1\<^sub>c c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def apply (auto,rule If_branch_sim, auto)
  unfolding RGSim_pre_def by blast+ 

lemma If_branch1_imp_sound:
  "\<xi> \<subseteq> \<alpha> \<and> \<gamma>\<^sub>n\<subseteq>\<alpha> \<Longrightarrow> Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow> \<forall>s. ( s, s)\<in>G\<^sub>c  \<Longrightarrow> R\<^sub>c\<subseteq>1\<alpha>\<^sub>x \<Longrightarrow>
   \<xi> \<subseteq> (b\<^sub>c \<odot> {s. True}) \<Longrightarrow>
  (\<Gamma>\<^sub>c,c1\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow>  
  (\<Gamma>\<^sub>c,Cond b\<^sub>c c1\<^sub>c c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def apply (auto,rule If_branch_sim, auto)
  unfolding RGSim_pre_def by blast+


end
    
