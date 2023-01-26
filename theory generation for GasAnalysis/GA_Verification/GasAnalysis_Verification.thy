section \<open> GA \<close>

theory GasAnalysis_Verification
imports "Z_Machines.Z_Machine"

begin                

datatype ('s, 'e) tag =
  State (ofState: 's) | Event (ofEvent: 'e)

abbreviation "is_Event x \<equiv> \<not> is_State x"

type_synonym ('s, 'e) rctrace = "('s, 'e) tag list"

definition wf_rcstore :: "('s, 'e) rctrace \<Rightarrow> 's \<Rightarrow> 's option \<Rightarrow> bool" where
[z_defs]: "wf_rcstore tr st final = (
     length(tr) > 0 
   \<and> tr ! ((length tr) -1) = State st 
   \<and> (final \<noteq> None \<longrightarrow> (\<forall>i<length tr. tr ! i = State (the final) \<longrightarrow> i= (length tr) -1)) 
   \<and> (filter is_State tr) ! (length (filter is_State tr) -1) = State  st)"


notation undefined ("???")

text \<open> This theory file is to model the GasAnalysis state machine of the Chemical Detector case study.  \<close>

subsection \<open> type definition \<close>

enumtype St = initial | NoGas | GasDetected | Analysis  | Reading  | final

definition "St = {initial , NoGas , GasDetected , Analysis , Reading  , final}"


enumtype Evt = gas | turn | resume | stop

definition "Evt = {gas, turn, resume, stop}"


enumtype Angle = Left | Right | Back |Front

definition "Angle = {Left, Right, Back, Front}"

enumtype Status = noGas | gasD
definition "Status= {noGas, gasD}"

type_synonym Chem= "nat"
type_synonym Intensity= "nat"

record GasSensor =
  c :: Chem
  i :: Intensity

record_default GasSensor

definition Chem :: "Chem set" where "Chem = {1,2,3}"
consts thr::"Intensity" 
def_consts thr="2"

definition "SeqGasSensor = { [\<lparr> c = 1, i = 0 \<rparr>,\<lparr> c = 2, i = 1 \<rparr>,\<lparr> c = 2, i = 1 \<rparr>,\<lparr> c = 3, i = 3 \<rparr>]}"


text \<open> RoboChart functions using consts \<close>

fun goreq :: "Intensity \<times> Intensity \<Rightarrow> bool"
  where "goreq(i1, i2) = (i1 \<ge> i2)"

fun intensity_aux:: "GasSensor list \<Rightarrow> nat \<Rightarrow> Intensity" where
"intensity_aux [] n = n" | 
"intensity_aux (g # gs) n = (if (i g) > n then intensity_aux gs (i g) else  intensity_aux gs n)"


abbreviation "intensity gs \<equiv> intensity_aux gs 0"


fun analysis:: "GasSensor list \<Rightarrow> Status" where 
"analysis (gs) =(if intensity(gs)>0 then gasD else noGas ) "


fun angle::"nat\<Rightarrow> Angle"
  where"angle(x) = (if ((0<x \<and> x\<le>45)\<or> (x>315 \<and> x\<le>360)) then Front else 
  if 45< x \<and> x\<le> 135 then  Right else 
  if 135< x \<and> x\<le>225 then  Back else
 Left )"


fun location_aux :: "GasSensor list \<Rightarrow> nat \<Rightarrow> nat" where
"location_aux [] n = n" | 
"location_aux (g # gs) n = (if i g = intensity( g #gs) then  n else  location_aux gs n+1)"

fun location:: " GasSensor list\<Rightarrow> Angle"
  where "location(gs) =(if goreq(intensity(gs), thr) then angle((360 div size gs)*( location_aux gs 0)) else Front)"


subsection \<open> State Space \<close>

zstore GasAnalysis = 
  sts :: "Status"
  gs :: "GasSensor list"
  ins:: "Intensity"
  anl:: "Angle"
  st::"St"
  tr :: "(St, Evt) tag list"
  triggers:: "Evt set"
  where inv: 
    "wf_rcstore tr st (Some final)"
    "(st=GasDetected) \<longrightarrow> ins=intensity(gs)" 
    "sts=analysis(gs)" 



subsection \<open> Operations \<close>


zoperation InitialToReading =
  over GasAnalysis
  pre "st= initial"
  update "[ st\<Zprime>= Reading
           ,tr\<Zprime>=tr @ [State Reading]
           ,triggers\<Zprime>={gas}
         ]"

zoperation ReadingToAnalysis =
  over GasAnalysis
  params g\<in>"SeqGasSensor"
  pre "st= Reading "
  update "[ sts\<Zprime> =analysis(g)
           ,gs\<Zprime> = g
           ,st\<Zprime>= Analysis
           ,tr\<Zprime>=tr @ [Event gas, State Analysis]
           ,triggers\<Zprime>={}
           ]"



zoperation AnalysisToNoGas =
  over GasAnalysis
  pre "st= Analysis \<and> sts=(noGas)"
  update "[ st\<Zprime>= NoGas
           ,tr\<Zprime>=tr @ [Event resume, State NoGas]
           ,triggers\<Zprime>={}
          ]"
        
zoperation NoGasToReading =
  over GasAnalysis
  pre "st= NoGas "
  update "[ st\<Zprime>= Reading
           ,tr\<Zprime>=tr @ [ State Reading]
           ,triggers\<Zprime>={gas}
          ]"

zoperation AnalysisToGasDetected =
  over GasAnalysis
  pre "st= Analysis \<and> sts=(gasD)"
  update "[ st\<Zprime>= GasDetected
           ,tr\<Zprime>=tr @ [State GasDetected]
           ,ins\<Zprime> = intensity(gs)
           ,triggers\<Zprime>={} 
          ]"
        
zoperation GasDetectedToFinal =
  over GasAnalysis
  pre "st= GasDetected  \<and> goreq(ins, thr)"
  update "[ st\<Zprime>= final
           ,tr\<Zprime>=tr @ [Event stop, State final]
           ,triggers\<Zprime>={}
           ]"

zoperation GasDetectedToReading =
  over GasAnalysis
  pre "st= GasDetected \<and> \<not>goreq(ins, thr)"
  update "[ anl\<Zprime>= location(gs)
           ,st\<Zprime>= Reading
           ,tr\<Zprime>=tr @ [Event turn, State Reading]
           ,triggers\<Zprime>={gas}
           ]"

                
zoperation Bypass =
  over GasAnalysis
  pre "st = final"


definition Init :: "GasAnalysis subst" where
  [z_defs]:
  "Init = 
   [sts\<leadsto> noGas,
    gs \<leadsto> [],
    ins\<leadsto> 0,
    anl\<leadsto> Front,
    st\<leadsto> initial,
    tr \<leadsto>[State initial],
    triggers \<leadsto> {}
   ]"

 
zmachine GasAnalysisMachine = 
  init Init
  invariant GasAnalysis_inv
  operations InitialToReading AnalysisToNoGas AnalysisToGasDetected GasDetectedToFinal GasDetectedToReading ReadingToAnalysis NoGasToReading Bypass



subsection \<open> Structural Invariants \<close>

lemma Init [hoare_lemmas]:"Init establishes GasAnalysis_inv"
  by zpog_full

lemma InitialToReading_inv [hoare_lemmas]:"InitialToReading() preserves GasAnalysis_inv"
  apply zpog_full
  apply (metis St.distinct(9) less_Suc_eq nth_append tag.inject(1))
  by (metis St.distinct(9) not_less_less_Suc_eq nth_append tag.inject(1))
  
  
lemma AnalysisToNoGas_inv [hoare_lemmas]: "AnalysisToNoGas() preserves GasAnalysis_inv"
  apply zpog_full
  apply (metis One_nat_def Suc_eq_plus1 nth_Cons_0 nth_Cons_Suc nth_append_length_plus)
  by (metis St.distinct(28) less_SucE nth_append nth_append_length tag.disc(1) tag.disc(2) tag.inject(1))

  
lemma AnalysisToGasDetected_inv [hoare_lemmas]: "AnalysisToGasDetected() preserves GasAnalysis_inv"
  apply zpog_full
  by (metis St.distinct(27) less_antisym nth_append tag.inject(1))
  
lemma GasDetectedToFinal_inv [hoare_lemmas]: "GasDetectedToFinal() preserves GasAnalysis_inv"
  apply zpog_full
  apply (metis One_nat_def Suc_eq_plus1 nth_Cons_0 nth_Cons_Suc nth_append_length_plus)
  apply (metis St.distinct(23) not_less_less_Suc_eq nth_append nth_append_length tag.distinct(1) tag.inject(1))
  by (metis St.distinct(23) Suc_le_eq diff_Suc_Suc diff_diff_cancel less_SucE minus_nat.diff_0 nat_less_le nth_Cons_0 nth_Cons_Suc nth_append tag.distinct(1) tag.inject(1) zero_less_Suc)



  
lemma GasDetectedToReading_inv [hoare_lemmas]: "GasDetectedToReading() preserves GasAnalysis_inv"
  apply zpog_full
  apply (metis One_nat_def Suc_eq_plus1 nth_Cons_0 nth_Cons_Suc nth_append_length_plus)
  apply (metis St.distinct(24) less_antisym nth_append nth_append_length tag.distinct(1) tag.inject(1))
  by (smt (z3) One_nat_def St.distinct(24) Suc_eq_plus1 less_SucE nth_Cons_0 nth_Cons_Suc nth_append nth_append_length nth_append_length_plus tag.distinct(1) tag.inject(1))


  
lemma ReadingToAnalysis_inv [hoare_lemmas]: "ReadingToAnalysis (l) preserves GasAnalysis_inv"
  apply zpog_full
  apply (metis One_nat_def Suc_eq_plus1 nth_Cons_0 nth_Cons_Suc nth_append_length_plus)
  apply (metis St.distinct(29) not_less_less_Suc_eq nth_append nth_append_length tag.distinct(1) tag.inject(1))
  by (smt (z3) One_nat_def St.distinct(30) Suc_eq_plus1 less_SucE nth_Cons_0 nth_Cons_Suc nth_append nth_append_length nth_append_length_plus tag.distinct(1) tag.inject(1))

  
lemma NoGasToReading_inv [hoare_lemmas]: "NoGasToReading() preserves GasAnalysis_inv"
  apply zpog_full
  apply (metis St.distinct(17) less_antisym nth_append tag.inject(1))
  by (metis St.distinct(18) not_less_less_Suc_eq nth_append tag.inject(1))


lemma Bypass_inv [hoare_lemmas]: "Bypass() preserves GasAnalysis_inv"
  by (zpog_full; auto)


subsection \<open> Safety Requirements \<close>

zexpr R1 is
"sts=noGas \<and> thr>0 \<longrightarrow>(\<forall>i <(length tr). tr ! i \<noteq> State final)"

lemma "Init establishes R1 "
  by zpog_full

lemma "InitialToReading() preserves R1"
  apply zpog_full
  by (metis St.distinct(29) less_SucE nth_append nth_append_length tag.inject(1))

lemma "GasDetectedToFinal() preserves R1 under GasAnalysis_inv"
  by zpog_full

lemma "AnalysisToGasDetected() preserves R1 under GasAnalysis_inv"
 by zpog_full

lemma  "AnalysisToNoGas() preserves  R1"
  apply zpog_full
  by (metis One_nat_def St.distinct(18) Suc_eq_plus1 less_SucE nth_Cons_0 nth_Cons_Suc nth_append nth_append_length nth_append_length_plus tag.distinct(1) tag.inject(1))

lemma  "NoGasToReading() preserves R1"
  apply zpog_full
  by (simp add: nth_append)

lemma  "GasDetectedToReading() preserves   R1 "
  apply zpog_full
  by (metis One_nat_def St.distinct(30) Suc_eq_plus1 less_SucE nth_Cons_0 nth_Cons_Suc nth_append nth_append_length nth_append_length_plus tag.distinct(1) tag.inject(1)) 

lemma  "ReadingToAnalysis l preserves  R1 under GasAnalysis_inv  "
  apply zpog_full
  apply (metis (no_types, opaque_lifting) One_nat_def St.distinct(27) St.distinct(29) Suc_eq_plus1 Suc_lessI cancel_ab_semigroup_add_class.add_diff_cancel_left' diff_is_0_eq' less_Suc_eq_le not_less_eq nth_Cons_0 nth_Cons_Suc nth_append tag.distinct(1) tag.inject(1))
  apply (metis (mono_tags, lifting) One_nat_def St.distinct_disc(28) Suc_eq_plus1 less_SucE nth_Cons_0 nth_Cons_Suc nth_append nth_append_length nth_append_length_plus tag.distinct(1) tag.inject(1)) 
  done



zexpr R2 is
"length tr>1\<longrightarrow> ( \<forall> i <(length tr). tr! i = State final   \<longrightarrow> tr ! (i-1) = Event stop )"


lemma "Init establishes R2"
  by (zpog_full; auto)

lemma  "InitialToReading() preserves  R2 under GasAnalysis_inv"
  apply zpog_full
  apply (metis St.distinct(30) St.simps(10) less_Suc_eq nth_append nth_append_length tag.inject(1))
  by (metis St.distinct(30) St.simps(10) less_Suc_eq nth_append nth_append_length tag.inject(1))

 lemma  "AnalysisToNoGas() preserves  R2 under GasAnalysis_inv"
  apply zpog_full
  by (smt (verit, del_insts) One_nat_def St.distinct(18) St.distinct_disc(27) Suc_eq_plus1 less_SucE nth_Cons_0 nth_Cons_Suc nth_append nth_append_length nth_append_length_plus tag.disc(1) tag.disc(2) tag.inject(1))


lemma  "AnalysisToGasDetected()   preserves  R2 under GasAnalysis_inv"
  apply zpog_full
  by (metis St.distinct(24) St.distinct_disc(28) less_Suc_eq nth_append nth_append_length tag.inject(1))


lemma "GasDetectedToFinal() preserves R2 under GasAnalysis_inv" 
  apply zpog_full
  apply (metis St.distinct(24) cancel_comm_monoid_add_class.diff_zero diff_Suc_Suc less_antisym nth_append nth_append_length tag.distinct(1) tag.inject(1))
  by (metis less_2_cases_iff less_numeral_extra(3) thr_def)


lemma  "GasDetectedToReading() preserves   R2 under GasAnalysis_inv "
  apply zpog_full
  apply (smt (verit, best) St.distinct(24) St.distinct(30) Suc_diff_Suc diff_Suc_1 diff_Suc_Suc less_SucE minus_gr_zero_iff nth_Cons_0 nth_Cons_pos nth_append tag.distinct(1) tag.inject(1))
  by (smt (verit, best) One_nat_def St.distinct(24) St.distinct(30) Suc_eq_plus1 less_SucE nth_Cons_0 nth_Cons_Suc nth_append nth_append_length nth_append_length_plus tag.disc(1) tag.disc(2) tag.inject(1))


lemma  "ReadingToAnalysis l preserves  R2 under GasAnalysis_inv"
  apply zpog_full
  apply (smt (verit, best) One_nat_def St.distinct(30) St.distinct_disc(27) Suc_eq_plus1 less_SucE nth_Cons_0 nth_Cons_Suc nth_append nth_append_length nth_append_length_plus tag.disc(1) tag.disc(2) tag.inject(1))
  by (smt (verit, best) One_nat_def St.distinct(30) St.distinct_disc(28) Suc_eq_plus1 less_SucE nth_Cons_0 nth_Cons_Suc nth_append nth_append_length nth_append_length_plus tag.disc(1) tag.disc(2) tag.inject(1))


lemma  "NoGasToReading() preserves  R2 under GasAnalysis_inv "
  apply zpog_full
  apply (metis St.distinct(18) St.distinct(30) less_Suc_eq nth_append nth_append_length tag.inject(1))
  by (metis St.distinct(18) St.distinct(30) less_Suc_eq nth_append nth_append_length tag.inject(1))



zexpr R3
is "length tr>1 \<longrightarrow> (\<forall>i<length tr-1.  tr ! (i+1) = State Analysis \<longrightarrow>  tr ! i = Event gas)" 


lemma "Init establishes R3"
  by (zpog_full; auto)

lemma  "InitialToReading() preserves  R3 under GasAnalysis_inv"
  apply zpog_full
  apply (smt (verit) One_nat_def St.distinct(5) St.simps(26) Suc_pred diff_is_0_eq' length_tl less_Suc0 less_Suc_eq_le list.sel(2) list.size(3) not_less_eq nth_Cons_0 nth_append tag.inject(1))
  by (smt (verit, del_insts) St.distinct(5) St.simps(26) Suc_pred diff_is_0_eq' less_Suc0 less_Suc_eq less_Suc_eq_le not_less_eq nth_Cons_0 nth_append tag.inject(1))
 
 
lemma  "ReadingToAnalysis l preserves  R3 under GasAnalysis_inv "
  apply zpog_full
  apply (smt (verit, ccfv_SIG) Suc_pred less_2_cases not_less_eq not_less_iff_gr_or_eq nth_append nth_append_length numeral_2_eq_2 tag.distinct(1))
  by (metis (no_types, lifting) Suc_lessI Suc_pred length_greater_0_conv less_2_cases less_SucE nth_append nth_append_length numeral_2_eq_2 tag.distinct(1))



lemma  "AnalysisToNoGas() preserves  R3  under GasAnalysis_inv" 
  apply zpog_full
  by (smt (verit, del_insts) St.distinct(13) Suc_eq_plus1 Suc_pred less_2_cases_iff not_less_eq not_less_iff_gr_or_eq nth_Cons_0 nth_Cons_Suc nth_append nth_append_length nth_append_length_plus numeral_2_eq_2 one_add_one tag.distinct(1) tag.inject(1))



lemma  "AnalysisToGasDetected()   preserves  R3 under GasAnalysis_inv"
  apply zpog_full
  by (metis (no_types, lifting) Nat.lessE One_nat_def St.simps(20) Suc_leI Suc_lessI diff_Suc_1 diff_is_0_eq' length_greater_0_conv nth_append nth_append_length tag.inject(1))


lemma  "GasDetectedToReading() preserves  R3"
  apply zpog_full
  by (smt (verit, ccfv_SIG) One_nat_def St.simps(26) Suc_eq_plus1 Suc_less_eq2 cancel_ab_semigroup_add_class.add_diff_cancel_left' diff_Suc_1 length_Cons less_SucE less_nat_zero_code list.sel(3) list.size(3) not_less_iff_gr_or_eq nth_append nth_append_length nth_tl tag.distinct(1) tag.inject(1))


lemma  "NoGasToReading() preserves  R3"
  apply zpog_full
  by (metis (no_types, lifting) Nat.lessE One_nat_def St.simps(26) Suc_leI Suc_lessI diff_Suc_1 diff_is_0_eq' length_greater_0_conv nth_append nth_append_length tag.inject(1))



lemma "GasDetectedToFinal() preserves R3" 
  apply zpog_full
  by (smt (verit) One_nat_def St.simps(28) Suc_eq_plus1 Suc_less_eq2 cancel_ab_semigroup_add_class.add_diff_cancel_left' diff_Suc_1 length_Cons less_nat_zero_code list.sel(3) list.size(3) not_less_eq not_less_iff_gr_or_eq nth_append nth_append_length nth_tl tag.distinct(1) tag.inject(1))



zexpr R4
is "(length tr)>1\<longrightarrow> ( \<forall> i <(length tr)-1  . tr ! i = Event turn  \<longrightarrow> tr ! (i+1) = State Reading )"


lemma "Init establishes R4"
  by (zpog_full; auto)

lemma  "InitialToReading() preserves  R4"
  apply zpog_full
  by (simp add: nth_append)


lemma  "ReadingToAnalysis l preserves  R4 under GasAnalysis_inv"
  apply zpog_full
  apply (smt (verit) Evt.distinct(1) Suc_lessI Suc_pred length_greater_0_conv less_Suc0 less_Suc_eq nth_append nth_append_length tag.disc(1) tag.disc(2) tag.inject(2))
  by (smt (verit, del_insts) Evt.distinct(1) Suc_lessI Suc_pred length_greater_0_conv less_Suc0 less_Suc_eq nth_append nth_append_length tag.disc(1) tag.disc(2) tag.inject(2))

lemma  "AnalysisToNoGas() preserves  R4 under GasAnalysis_inv"
  apply zpog_full
  by (smt (verit, best) Evt.distinct(7) One_nat_def Suc_diff_1 less_Suc0 linorder_neqE_nat not_less_eq nth_append nth_append_length tag.distinct(1) tag.inject(2))

lemma  "AnalysisToGasDetected()   preserves  R4  under GasAnalysis_inv "
  apply zpog_full
  by (metis (no_types, lifting) Nat.lessE One_nat_def diff_Suc_1 less_Suc0 not_less_eq nth_append tag.disc(1) tag.disc(2))
 

lemma  "GasDetectedToReading() preserves   R4 under GasAnalysis_inv"
  apply zpog_full
  apply (smt (verit, del_insts) One_nat_def Suc_eq_plus1 Suc_leI Suc_lessI Suc_pred diff_is_0_eq' less_Suc_eq nth_Cons_0 nth_Cons_Suc nth_append nth_append_length_plus tag.distinct(1) zero_less_Suc)
  by (smt (verit, del_insts) One_nat_def Suc_eq_plus1 Suc_lessI Suc_pred not_less_eq nth_Cons_0 nth_Cons_Suc nth_append nth_append_length_plus tag.disc(1) tag.disc(2) zero_less_Suc)

  
lemma  "NoGasToReading() preserves  R4 under GasAnalysis_inv"
  apply zpog_full
  apply (simp add: nth_append)
  by (simp add: nth_append)
  

lemma "GasDetectedToFinal() preserves R4 under GasAnalysis_inv" 
  apply zpog_full
  apply (smt (verit) Evt.simps(10) Suc_pred less_Suc_eq not_less_eq nth_append nth_append_length tag.disc(1) tag.disc(2) tag.inject(2) zero_less_Suc)
  using Zero_not_Suc numerals(2) thr_def by presburger



zexpr R5 is 
"length(filter is_State tr)>1 \<longrightarrow> (\<forall>i< (length(filter is_State tr)-1).  (filter is_State tr) ! i = State Reading \<longrightarrow> ( (filter is_State tr) ! (i+1)) =  State Analysis)"


lemma "Init establishes R5"
  by zpog_full

lemma  "InitialToReading() preserves  R5 under GasAnalysis_inv"
apply zpog_full
  apply (metis (no_types, lifting) Nat.lessE One_nat_def St.distinct(7) diff_Suc_1 less_Suc0 not_less_eq nth_append tag.inject(1))
  by (metis (no_types, lifting) Nat.lessE One_nat_def St.distinct(7) diff_Suc_1 less_Suc0 not_less_eq nth_append tag.inject(1))

lemma  "AnalysisToNoGas() preserves  R5 under GasAnalysis_inv "
  apply zpog_full
  by (metis (no_types, lifting) Nat.lessE One_nat_def St.simps(26) diff_Suc_1 less_Suc0 not_less_eq nth_append tag.inject(1))

lemma  "AnalysisToGasDetected()   preserves  R5 under GasAnalysis_inv "
  apply zpog_full
  by (metis (no_types, lifting) One_nat_def St.distinct(25) Suc_eq_plus1 Suc_lessI diff_Suc_1 diff_is_0_eq less_diff_conv less_nat_zero_code linorder_not_less nth_append tag.inject(1))


lemma "GasDetectedToFinal() preserves R5  under GasAnalysis_inv  " 
  apply zpog_full
  apply (metis (no_types, lifting) One_nat_def St.distinct(21) Suc_eq_plus1 Suc_lessI diff_Suc_1 diff_is_0_eq gr_implies_not_zero less_diff_conv linorder_not_less nth_append tag.inject(1))
  by (metis less_2_cases_iff less_numeral_extra(3) thr_def)

lemma  "GasDetectedToReading() preserves   R5 under GasAnalysis_inv  "
  apply zpog_full
  apply (metis (no_types, lifting) One_nat_def St.distinct(21) Suc_eq_plus1 Suc_lessI diff_Suc_1 diff_is_0_eq less_diff_conv linorder_not_le not_less_zero nth_append tag.inject(1))
  by (metis (no_types, lifting) One_nat_def St.distinct(21) Suc_eq_plus1 Suc_lessI diff_Suc_1 diff_is_0_eq' less_diff_conv less_zeroE linorder_not_le nth_append tag.inject(1))


lemma  "ReadingToAnalysis l preserves  R5 under GasAnalysis_inv  "
  apply zpog_full
  apply (metis (no_types, lifting) One_nat_def Suc_eq_plus1 Suc_lessI diff_is_0_eq less_diff_conv less_nat_zero_code linorder_not_less nth_append nth_append_length)
  by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 Suc_lessI diff_is_0_eq less_diff_conv less_zeroE linorder_not_le nth_append nth_append_length)
  
lemma  "NoGasToReading() preserves  R5 under GasAnalysis_inv "
  apply zpog_full
  apply (metis (no_types, lifting) Nat.lessE One_nat_def St.distinct(15) diff_Suc_1 less_Suc0 not_less_eq nth_append tag.inject(1))
  by (metis (no_types, lifting) Nat.lessE One_nat_def St.distinct(15) diff_Suc_1 less_Suc0 not_less_eq nth_append tag.inject(1))
  


zexpr R6
is "  thr>0 \<and> intensity(gs)\<ge>thr  \<longrightarrow>   sts=gasD"


lemma "Init establishes R6"
  by (zpog_full; auto)


lemma  "InitialToReading()  preserves  R6"
  by (zpog_full; auto)

lemma  "ReadingToAnalysis l preserves  R6"
  by (zpog_full ; auto)  


lemma "GasDetectedToFinal() preserves R6" 
  by (zpog_full; auto)


lemma  "AnalysisToNoGas() preserves  R6"
  by (zpog_full; auto)  

lemma  "AnalysisToGasDetected() preserves  R6"
  by (zpog_full; auto)  


lemma  "GasDetectedToReading() preserves  R6"
  by (zpog_full; auto)  

lemma  "NoGasToReading() preserves  R6"
  by (zpog_full; auto)



definition [z_defs]: "GasAnalysis_axioms = (thr >0 )"


lemma R8_GasAnalysis_deadlock_free: "GasAnalysis_axioms  \<Longrightarrow> deadlock_free GasAnalysisMachine" 
  apply deadlock_free
  using SeqGasSensor_def St.exhaust_disc apply auto[1]
  using SeqGasSensor_def St.exhaust_disc by blast




end
