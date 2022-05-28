theory continuity
  imports properties neighborhood connectedness compactness
begin

(**Definitions involving closure and interior:*)

(**The mapping \<phi>:'u\<Rightarrow>'v is continuous if its direct image distributes (increasingly) over the closure*)
definition ContinuousC::"('u \<sigma>,'u \<sigma>)\<phi>\<Rightarrow>('v \<sigma>,'v \<sigma>)\<phi>\<Rightarrow>('u,'v)\<phi>\<Rightarrow>bool" ("Cont\<^sup>C[_,_]")
  where "Cont\<^sup>C[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> \<equiv> \<forall>U. \<lbrakk>\<phi> (\<C>\<^sub>1 U)\<rbrakk> \<^bold>\<preceq> \<C>\<^sub>2 \<lbrakk>\<phi> U\<rbrakk>"

(**The mapping \<phi>:'u\<Rightarrow>'v is continuous if its inverse image distributes (decreasingly) over the interior*)
definition ContinuousI::"('u \<sigma>,'u \<sigma>)\<phi>\<Rightarrow>('v \<sigma>,'v \<sigma>)\<phi>\<Rightarrow>('u,'v)\<phi>\<Rightarrow>bool" ("Cont\<^sup>I[_,_]")
  where "Cont\<^sup>I[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> \<equiv> \<forall>V. \<lbrakk>\<phi> (\<I>[\<C>\<^sub>2] V)\<rbrakk>\<inverse> \<^bold>\<preceq> \<I>[\<C>\<^sub>1] \<lbrakk>\<phi> V\<rbrakk>\<inverse>"

(**The two definitions above are equivalent (modulo some conditions on the closures)*)
lemma ContinuousIC_equiv:
 "MONO \<C>\<^sub>1 \<Longrightarrow> MONO \<C>\<^sub>2 \<Longrightarrow> Cl_2 \<C>\<^sub>1 \<Longrightarrow> Cl_2 \<C>\<^sub>2 \<Longrightarrow> Cl_4' \<C>\<^sub>1 \<Longrightarrow> Cl_4' \<C>\<^sub>2
                            \<Longrightarrow> Cont\<^sup>C[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> = Cont\<^sup>I[\<C>\<^sub>1,\<C>\<^sub>2] \<phi>"
  oops (*Exercise: prove using minimal assumptions*)


(**Definitions involving fixed points: closed and open sets:*)

(**The mapping \<phi>:'u\<Rightarrow>'v is continuous iff the inverse image of every closed set is closed*)
definition ContinuousCl::"('u \<sigma>,'u \<sigma>)\<phi>\<Rightarrow>('v \<sigma>,'v \<sigma>)\<phi>\<Rightarrow>('u,'v)\<phi>\<Rightarrow>bool" ("Cont\<^sup>c\<^sup>l[_,_]")
  where "Cont\<^sup>c\<^sup>l[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> \<equiv> \<forall>V. Cl[\<C>\<^sub>2] V \<longrightarrow> Cl[\<C>\<^sub>1] \<lbrakk>\<phi> V\<rbrakk>\<inverse>"

(**The mapping \<phi>:'u\<Rightarrow>'v is continuous iff the inverse image of every open set is open*)
definition ContinuousOp::"('u \<sigma>,'u \<sigma>)\<phi>\<Rightarrow>('v \<sigma>,'v \<sigma>)\<phi>\<Rightarrow>('u,'v)\<phi>\<Rightarrow>bool" ("Cont\<^sup>o\<^sup>p[_,_]")
  where "Cont\<^sup>o\<^sup>p[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> \<equiv> \<forall>V. Op[\<C>\<^sub>2] V \<longrightarrow> Op[\<C>\<^sub>1] \<lbrakk>\<phi> V\<rbrakk>\<inverse>"

(**The two definitions above are equivalent (without assuming any condition on the closures)*)
lemma ContinuousClOp_equiv: "Cont\<^sup>c\<^sup>l[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> = Cont\<^sup>o\<^sup>p[\<C>\<^sub>1,\<C>\<^sub>2] \<phi>" 
  unfolding ContinuousCl_def ContinuousOp_def using img_inv_neg by (metis OpCldual fp_d)

(**Relate definitions involving both closure/interior and their fixed-points (under minimal conditions)*)
lemma ContinuousCCl_impl1: "MONO \<C>\<^sub>2 \<Longrightarrow> Cl_2 \<C>\<^sub>1
           \<Longrightarrow> Cont\<^sup>C[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> \<longrightarrow> Cont\<^sup>c\<^sup>l[\<C>\<^sub>1,\<C>\<^sub>2] \<phi>" unfolding ContinuousC_def ContinuousCl_def MONO_def EXPN_def subset_def img_inv_def by (smt (z3) fixpoint_pred_def img_dir_def setequ_char)
lemma ContinuousCCl_impl2: "MONO \<C>\<^sub>1 \<Longrightarrow> Cl_2 \<C>\<^sub>2  \<Longrightarrow> Cl_4' \<C>\<^sub>2 
           \<Longrightarrow> Cont\<^sup>c\<^sup>l[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> \<longrightarrow> Cont\<^sup>C[\<C>\<^sub>1,\<C>\<^sub>2] \<phi>" unfolding ContinuousC_def ContinuousCl_def MONO_def EXPN_def IDEM_b_def img_inv_def img_dir_def fixpoint_pred_def setequ_char subset_def by (smt (z3))
lemma ContinuousCCl_equiv: "MONO \<C>\<^sub>1 \<Longrightarrow> MONO \<C>\<^sub>2 \<Longrightarrow> Cl_2 \<C>\<^sub>1 \<Longrightarrow> Cl_2 \<C>\<^sub>2  \<Longrightarrow> Cl_4' \<C>\<^sub>2
           \<Longrightarrow> Cont\<^sup>c\<^sup>l[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> = Cont\<^sup>C[\<C>\<^sub>1,\<C>\<^sub>2] \<phi>" using ContinuousCCl_impl1 ContinuousCCl_impl2 by blast


(**Point-continuity based on interior *)
(**using direct image*)
definition pointContinuous1I::"('u \<sigma>,'u \<sigma>)\<phi>\<Rightarrow>('v \<sigma>,'v \<sigma>)\<phi>\<Rightarrow>('u,'v)\<phi>\<Rightarrow>'u\<Rightarrow>bool" ("pCont1\<^sup>I[_,_]")
  where "pCont1\<^sup>I[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> x \<equiv> \<forall>V. \<I>[\<C>\<^sub>2] V (\<phi> x) \<longrightarrow> (\<exists>U. \<I>[\<C>\<^sub>1] U x \<and> \<lbrakk>\<phi> U\<rbrakk> \<^bold>\<preceq> V)"
(**using inverse image*)
definition pointContinuous2I::"('u \<sigma>,'u \<sigma>)\<phi>\<Rightarrow>('v \<sigma>,'v \<sigma>)\<phi>\<Rightarrow>('u,'v)\<phi>\<Rightarrow>'u\<Rightarrow>bool" ("pCont2\<^sup>I[_,_]")
  where "pCont2\<^sup>I[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> x \<equiv> \<forall>V. \<I>[\<C>\<^sub>2] V (\<phi> x) \<longrightarrow> (\<exists>U. \<I>[\<C>\<^sub>1] U x \<and> U \<^bold>\<preceq> \<lbrakk>\<phi> V\<rbrakk>\<inverse>)"
(**Definitions using direct or inverse image are equivalent*)
lemma pointContinuousI_equiv: "pCont1\<^sup>I[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> x = pCont2\<^sup>I[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> x" unfolding pointContinuous1I_def pointContinuous2I_def by (smt (verit, del_insts) img_dir_def img_inv_def subset_def)

(**Point-continuity based on neighborhood *)
(**using direct image*)
definition pointContinuous1N::"('u \<sigma>,'u \<sigma>)\<phi>\<Rightarrow>('v \<sigma>,'v \<sigma>)\<phi>\<Rightarrow>('u,'v)\<phi>\<Rightarrow>'u\<Rightarrow>bool" ("pCont1\<^sup>N[_,_]")
  where "pCont1\<^sup>N[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> x \<equiv> \<forall>V. \<N>[\<C>\<^sub>2] (\<phi> x) V \<longrightarrow> (\<exists>U. \<lbrakk>\<phi> U\<rbrakk> \<^bold>\<preceq> V \<and> \<N>[\<C>\<^sub>1] x U)"
(**using inverse image*)
definition pointContinuous2N::"('u \<sigma>,'u \<sigma>)\<phi>\<Rightarrow>('v \<sigma>,'v \<sigma>)\<phi>\<Rightarrow>('u,'v)\<phi>\<Rightarrow>'u\<Rightarrow>bool" ("pCont2\<^sup>N[_,_]")
  where "pCont2\<^sup>N[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> x \<equiv> \<forall>V. \<N>[\<C>\<^sub>2] (\<phi> x) V \<longrightarrow> (\<exists>U. U \<^bold>\<preceq> \<lbrakk>\<phi> V\<rbrakk>\<inverse> \<and> \<N>[\<C>\<^sub>1] x U)"
(**Definitions using direct or inverse image are equivalent*)
lemma pointContinuousN_equiv: "pCont1\<^sup>N[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> x = pCont2\<^sup>N[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> x" unfolding pointContinuous1N_def pointContinuous2N_def by (smt (verit, best) img_dir_def img_inv_def subset_def)

(**Definitions using interior or neighborhood are equivalent*)
lemma pointContinuous_equiv: "pCont1\<^sup>I[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> x = pCont1\<^sup>N[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> x" unfolding pointContinuous1I_def pointContinuous1N_def Nbhd_Cl_def swap_def by blast

(**Revisiting (global) continuity: A mapping \<phi>:'u\<Rightarrow>'v is continuous 
  iff it is everywhere point-continuous (wrt. interior or nbhd)*)
definition ContinuousPI::"('u \<sigma>,'u \<sigma>)\<phi>\<Rightarrow>('v \<sigma>,'v \<sigma>)\<phi>\<Rightarrow>('u,'v)\<phi>\<Rightarrow>bool" ("Cont\<^sup>P\<^sup>I[_,_]")
  where "Cont\<^sup>P\<^sup>I[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> \<equiv> \<forall>x. pCont1\<^sup>I[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> x"
definition ContinuousPN::"('u \<sigma>,'u \<sigma>)\<phi>\<Rightarrow>('v \<sigma>,'v \<sigma>)\<phi>\<Rightarrow>('u,'v)\<phi>\<Rightarrow>bool" ("Cont\<^sup>P\<^sup>N[_,_]")
  where "Cont\<^sup>P\<^sup>N[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> \<equiv> \<forall>x. pCont1\<^sup>N[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> x"

(**Alternative definition of continuity based on neighborhoods:
 For every x, the inverse image of any neighborhood V of \<phi>(x) is a neighborhood of x*)
definition ContinuousNN::"('u \<sigma>,'u \<sigma>)\<phi>\<Rightarrow>('v \<sigma>,'v \<sigma>)\<phi>\<Rightarrow>('u,'v)\<phi>\<Rightarrow>bool" ("Cont\<^sup>N\<^sup>N[_,_]")
  where "Cont\<^sup>N\<^sup>N[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> \<equiv> \<forall>x V. \<N>[\<C>\<^sub>2] (\<phi> x) V \<longrightarrow> \<N>[\<C>\<^sub>1] x \<lbrakk>\<phi> V\<rbrakk>\<inverse>"
(**This alternative definition is equivalent to the previous one*)
lemma ContinuousPN_equ:  "MONO \<C>\<^sub>1 \<Longrightarrow> Cont\<^sup>P\<^sup>N[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> = Cont\<^sup>N\<^sup>N[\<C>\<^sub>1,\<C>\<^sub>2] \<phi>" 
  unfolding ContinuousNN_def ContinuousPN_def pointContinuous1N_def MONO_def
  unfolding Nbhd_Cl_def swap_def subset_def oops (*Exercise: prove (find missing assumptions)*)

(* Alternative definition of continuity based on interior:
 For every x, the interior of the inverse image of any set V whose interior contains \<phi>(x) contains x*)
definition ContinuousI'::"('u \<sigma>,'u \<sigma>)\<phi>\<Rightarrow>('v \<sigma>,'v \<sigma>)\<phi>\<Rightarrow>('u,'v)\<phi>\<Rightarrow>bool" ("Cont\<^sup>I\<^sup>I[_,_]")
  where "Cont\<^sup>I\<^sup>I[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> \<equiv> \<forall>x V. \<I>[\<C>\<^sub>2] V (\<phi> x) \<longrightarrow> \<I>[\<C>\<^sub>1] \<lbrakk>\<phi> V\<rbrakk>\<inverse> x"
(**This alternative definition is equivalent to the previous one*)
lemma ContinuousPI_equ:  "MONO \<C>\<^sub>1 \<Longrightarrow> Cont\<^sup>P\<^sup>I[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> = Cont\<^sup>I\<^sup>I[\<C>\<^sub>1,\<C>\<^sub>2] \<phi>" 
  unfolding ContinuousI'_def ContinuousPI_def pointContinuous1I_def by (smt (z3) MONO_def MONO_dual img_dir_def img_inv_def subset_def)

(**In particular the latter definition is equivalent to the one using interior (at the beginning) *)
lemma ContinuousII_equ: "Cont\<^sup>I\<^sup>I[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> = Cont\<^sup>I[\<C>\<^sub>1,\<C>\<^sub>2] \<phi>" unfolding ContinuousI'_def ContinuousI_def by (smt (verit, del_insts) img_inv_def subset_def)


(************* Preservation of properties under continuous maps ***************)

(** The composition of continuous maps is continuous*)
lemma "Cont\<^sup>C[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> \<and> Cont\<^sup>C[\<C>\<^sub>2,\<C>\<^sub>3] \<psi> \<longrightarrow> Cont\<^sup>C[\<C>\<^sub>1,\<C>\<^sub>3] (\<psi>\<circ>\<phi>)"
  unfolding ContinuousC_def img_dir_def oops (*Exercise: prove*)

lemma "Cont\<^sup>o\<^sup>p[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> \<and> Cont\<^sup>o\<^sup>p[\<C>\<^sub>2,\<C>\<^sub>3] \<psi> \<longrightarrow> Cont\<^sup>o\<^sup>p[\<C>\<^sub>1,\<C>\<^sub>3] (\<psi>\<circ>\<phi>)"
  unfolding ContinuousOp_def fixpoint_pred_def setequ_equ op_dual_def fun_comp_def
  using img_inv_neg oops (*Exercise: prove*)

(** Exercise: Preservation of set properties*)
(** Exercise: Preservation of separability/connectedness*)
(** Exercise: Preservation of compactness*)


(************ Open-, closed-maps and homeomorphisms ************)

(**The mapping \<phi>:'u\<Rightarrow>'v is called closed if the direct image of every closed set is closed*)
definition ClosedMap::"('u \<sigma>,'u \<sigma>)\<phi>\<Rightarrow>('v \<sigma>,'v \<sigma>)\<phi>\<Rightarrow>('u,'v)\<phi>\<Rightarrow>bool" ("Closed[_,_]")
  where "Closed[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> \<equiv> \<forall>U. Cl[\<C>\<^sub>1] U \<longrightarrow> Cl[\<C>\<^sub>2] \<lbrakk>\<phi> U\<rbrakk>"

(**The mapping \<phi>:'u\<Rightarrow>'v is called open if the direct image of every open set is open*)
definition OpenMap::"('u \<sigma>,'u \<sigma>)\<phi>\<Rightarrow>('v \<sigma>,'v \<sigma>)\<phi>\<Rightarrow>('u,'v)\<phi>\<Rightarrow>bool" ("Open[_,_]")
  where "Open[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> \<equiv> \<forall>U. Op[\<C>\<^sub>1] U \<longrightarrow> Op[\<C>\<^sub>2] \<lbrakk>\<phi> U\<rbrakk>"

(**The mapping \<phi>:'u\<Rightarrow>'v is a homeomorphism if it is bijective, continuous and its inverse is continuous too*)
definition Homeomorphism::"('u \<sigma>,'u \<sigma>)\<phi>\<Rightarrow>('v \<sigma>,'v \<sigma>)\<phi>\<Rightarrow>('u,'v)\<phi>\<Rightarrow>bool" ("Hom[_,_]")
  where "Hom[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> \<equiv> bijective \<phi> \<and> Cont\<^sup>C[\<C>\<^sub>1,\<C>\<^sub>2] \<phi> \<and> Cont\<^sup>C[\<C>\<^sub>2,\<C>\<^sub>1] \<phi>\<inverse>"

(**Exercise: verify further properties*)

end