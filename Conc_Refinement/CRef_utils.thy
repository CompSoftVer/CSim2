theory CRef_utils
imports Main CRef
begin

lemma "r \<subseteq> in_rel (R\<^sup>*) \<alpha> \<Longrightarrow> Sta\<^sub>s \<alpha> (r, R)\<^sub>\<alpha>"
  sorry




definition reach_end::"('g\<times>'l,'p,'f,'e) body \<Rightarrow> (('g,'l) c_state) rel1 \<Rightarrow> ('g,'l) c_state set  \<Rightarrow> 
                      ('g\<times>'l,'p,'f,'e) com \<Rightarrow> ('g,'l) c_state \<Rightarrow> ('g,'l) c_state \<Rightarrow> 
                      (('g, 'l, 'p,'f,'e) config_gs) list \<Rightarrow> bool"
  where "reach_end \<Gamma> R p c s s' l \<equiv>  (\<Gamma>,l)\<in> (cp\<^sub>e \<Gamma> c s \<inter> assum(p, R)) \<and> 
                                      final_glob (last l) \<and> snd(last l) = s'"

lemma "R1 \<subseteq> in_rel R2 \<alpha> \<Longrightarrow> R1 \<subseteq> in_rel (R2\<^sup>*) \<alpha>"
  unfolding in_rel_def apply auto
  by fastforce

lemma " "

lemma use_sim:
  assumes a0:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)" and
          a1:"reach_end \<Gamma>\<^sub>c R\<^sub>c P\<^sub>c C \<sigma> \<sigma>' l\<^sub>c" and a2:"reach_end \<Gamma>\<^sub>s R\<^sub>s P\<^sub>s S \<Sigma> \<Sigma>' l\<^sub>s" and 
          a3:"\<sigma> \<in> P\<^sub>c" and a4:"\<Sigma> \<in> P\<^sub>s" and a5:"(\<sigma>,\<Sigma>)\<in>\<xi>" and " R1 \<subseteq> in_rel (R2\<^sup>*) \<alpha>"
  shows"(t\<^sub>c,t\<^sub>s)\<in>\<alpha> \<and> (fst (last l\<^sub>c) = Skip \<longrightarrow> (t\<^sub>c,t\<^sub>s)\<in>\<gamma>n) \<and> (fst (last l\<^sub>c) = Throw \<longrightarrow> (t\<^sub>c,t\<^sub>s)\<in>\<gamma>a)"
proof-    
  have "(\<Gamma>\<^sub>c,(C, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, \<Sigma>),R\<^sub>s,G\<^sub>s)"
    using a0 a3 a4 a5  unfolding RGSim_pre_def by fast

qed

  
end
