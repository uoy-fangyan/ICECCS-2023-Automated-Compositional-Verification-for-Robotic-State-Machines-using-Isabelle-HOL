theory LRE_Beh_16012023_034057
imports "Z_Machines.Z_Machine"
begin

subsection \<open> Introduction \<close>

text \<open> This theory file is to model the LRE_Beh state machine in Z Machine notations.\<close>

notation undefined ("???")

subsection \<open> type definition \<close>

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
   
enumtype St = OCM | MOM | HCM | CAM | initial 
definition [z_defs]: "St = {OCM, MOM, HCM, CAM, initial}" 


enumtype Evt = endTask | reqOCM | reqMOM | reqVel | advVel | position 
definition "Evt = {endTask, reqOCM, reqMOM, reqVel, advVel, position}" 


consts StaticObsDist :: "integer"
consts MinSafeDist :: "integer"
consts HCMVel :: "integer"
consts MOMVel :: "integer"
consts Obsts :: "(integer\<times>integer) list"
consts ReqV :: "(integer\<times>integer) set"

text \<open> function definition \<close>

consts maneuv :: " (integer\<times>integer) \<Rightarrow> (integer\<times>integer)"
consts setVel :: " (integer\<times>integer) \<times> integer \<Rightarrow>(integer\<times>integer)"
consts dist :: " (integer\<times>integer) \<times> (integer\<times>integer) list \<Rightarrow>integer"
consts CDA :: " (integer\<times>integer) \<times> (integer\<times>integer) list \<times> (integer\<times>integer) \<Rightarrow>integer"
consts inOPEZ :: " (integer\<times>integer) \<Rightarrow> bool"

subsection \<open> State Space \<close>

zstore LRE_Beh =
  pos :: "(integer\<times>integer)"
  vel :: "(integer\<times>integer)"
  reqV :: "(integer\<times>integer)"
  
  
  
  
  
  st::"St"
  tr :: "(St, Evt) tag list"
  triggers:: "Evt set"
  where inv: 
    "wf_rcstore tr st (Some final)"

subsection \<open> Operations \<close>

zoperation InitialToOCM =
  over LRE_Beh
  pre "st= initial"
  update "[st\<Zprime>= OCM
         ,tr\<Zprime> =tr  @ [State OCM]
         ,triggers\<Zprime> = {reqVel, reqMOM}
         ]"
        
zoperation OCMToMOM =
  over LRE_Beh
  pre "st= OCM \<and> ((vel.1 * vel.1) + (vel.2 * vel.2))\<le>(3 * 3) \<and> dist(pos, Obsts)>10 \<and> \<not>inOPEZ(pos)"
  update "[st\<Zprime>= MOM
          ,vel\<Zprime> =setVel(vel, MOMVel)
         ,tr\<Zprime> =tr @ [Event reqMOM]@ [Event advVel] @ [State MOM]
         ,triggers\<Zprime> = {endTask, reqOCM}
         ]"
        
zoperation MOMToOCM =
  over LRE_Beh
  pre "st= MOM"
  update "[st\<Zprime>= OCM
         ,tr\<Zprime> =tr @ [Event reqOCM] @ [State OCM]
         ,triggers\<Zprime> = {reqVel, reqMOM}
         ]"
        
zoperation HCMToOCM =
  over LRE_Beh
  pre "st= HCM"
  update "[st\<Zprime>= OCM
         ,tr\<Zprime> =tr @ [Event reqOCM] @ [State OCM]
         ,triggers\<Zprime> = {reqVel, reqMOM}
         ]"
        
zoperation MOMToHCM =
  over LRE_Beh
  pre "st= MOM \<and> ((vel.1 * vel.1) + (vel.2 * vel.2))>(3 * 3) \<and> dist(pos, Obsts)\<le>StaticObsDist \<and> CDA(pos, Obsts, vel)>MinSafeDist \<and> \<not>inOPEZ(pos)"
  update "[st\<Zprime>= HCM
          ,vel\<Zprime> =setVel(vel, HCMVel)
         ,tr\<Zprime> =tr @ [Event advVel] @ [State HCM]
         ,triggers\<Zprime> = {reqOCM}
         ]"
        
zoperation MOMToOCM_1 =
  over LRE_Beh
  pre "st= MOM \<and> inOPEZ(pos) \<and> (CDA(pos, Obsts, vel)>MinSafeDist \<or> dist(pos, Obsts)>StaticObsDist)"
  update "[st\<Zprime>= OCM
         ,tr\<Zprime> =tr  @ [State OCM]
         ,triggers\<Zprime> = {reqVel, reqMOM}
         ]"
        
zoperation HCMToOCM_1 =
  over LRE_Beh
  pre "st= HCM \<and> inOPEZ(pos) \<and> (CDA(pos, Obsts, vel)>MinSafeDist \<or> dist(pos, Obsts)>StaticObsDist)"
  update "[st\<Zprime>= OCM
         ,tr\<Zprime> =tr  @ [State OCM]
         ,triggers\<Zprime> = {reqVel, reqMOM}
         ]"
        
zoperation HCMToMOM =
  over LRE_Beh
  pre "st= HCM \<and> dist(pos, Obsts)>StaticObsDist \<and> \<not>inOPEZ(pos)"
  update "[st\<Zprime>= MOM
          ,vel\<Zprime> =setVel(vel, MOMVel)
         ,tr\<Zprime> =tr @ [Event advVel] @ [State MOM]
         ,triggers\<Zprime> = {endTask, reqOCM}
         ]"
        
zoperation OCMToOCM =
  over LRE_Beh
  params reqV_input \<in> "ReqV" 
  pre "st= OCM"
  update "[st\<Zprime>= OCM
         ,reqV\<Zprime> =reqV_input
         ,vel\<Zprime> = reqV_input
         ,tr\<Zprime> =tr @ [Event reqVel]@ [Event advVel] @ [State OCM]
         ,triggers\<Zprime> = {reqVel, reqMOM}
         ]"
        
zoperation MOMToOCM_2 =
  over LRE_Beh
  pre "st= MOM"
  update "[st\<Zprime>= OCM
         ,vel\<Zprime> = (0, 0)
         ,tr\<Zprime> =tr @ [Event endTask]@ [Event advVel] @ [State OCM]
         ,triggers\<Zprime> = {reqVel, reqMOM}
         ]"
        
zoperation HCMToCAM =
  over LRE_Beh
  pre "st= HCM \<and> CDA(pos, Obsts, vel)\<le>MinSafeDist \<and> dist(pos, Obsts)\<le>StaticObsDist"
  update "[st\<Zprime>= CAM
          ,vel\<Zprime> =maneuv(vel)
         ,tr\<Zprime> =tr @ [Event advVel] @ [State CAM]
         ,triggers\<Zprime> = {reqOCM}
         ]"
        
zoperation MOMToCAM =
  over LRE_Beh
  pre "st= MOM \<and> CDA(pos, Obsts, vel)\<le>MinSafeDist \<and> dist(pos, Obsts)\<le>StaticObsDist"
  update "[st\<Zprime>= CAM
          ,vel\<Zprime> =maneuv(vel)
         ,tr\<Zprime> =tr @ [Event advVel] @ [State CAM]
         ,triggers\<Zprime> = {reqOCM}
         ]"
        
zoperation CAMToOCM =
  over LRE_Beh
  pre "st= CAM \<and> CDA(pos, Obsts, vel)>MinSafeDist"
  update "[st\<Zprime>= OCM
         ,vel\<Zprime> = (0, 0)
         ,tr\<Zprime> =tr @ [Event advVel] @ [State OCM]
         ,triggers\<Zprime> = {reqVel, reqMOM}
         ]"
        
zoperation CAMToOCM_1 =
  over LRE_Beh
  pre "st= CAM"
  update "[st\<Zprime>= OCM
         ,tr\<Zprime> =tr @ [Event reqOCM] @ [State OCM]
         ,triggers\<Zprime> = {reqVel, reqMOM}
         ]"
        
zoperation CAMToCAM =
  over LRE_Beh
  pre "st= CAM \<and> CDA(pos, Obsts, vel)\<le>MinSafeDist \<and> dist(pos, Obsts)\<le>StaticObsDist"
  update "[st\<Zprime>= CAM
          ,vel\<Zprime> =maneuv(vel)
         ,tr\<Zprime> =tr @ [Event advVel] @ [State CAM]
         ,triggers\<Zprime> = {reqOCM}
         ]"
        
zoperation MOMToCAM_1 =
  over LRE_Beh
  pre "st= MOM \<and> ((((pos.1 + vel.1)<0 \<or> (pos.1 + vel.1)>99) \<or> (pos.2 + vel.2)<0) \<or> (pos.2 + vel.2)>99)"
  update "[st\<Zprime>= CAM
          ,vel\<Zprime> =maneuv(vel)
         ,tr\<Zprime> =tr @ [Event advVel] @ [State CAM]
         ,triggers\<Zprime> = {reqOCM}
         ]"
        
zoperation HCMToCAM_1 =
  over LRE_Beh
  pre "st= HCM \<and> ((((pos.1 + vel.1)<0 \<or> (pos.1 + vel.1)>99) \<or> (pos.2 + vel.2)<0) \<or> (pos.2 + vel.2)>99)"
  update "[st\<Zprime>= CAM
          ,vel\<Zprime> =maneuv(vel)
         ,tr\<Zprime> =tr @ [Event advVel] @ [State CAM]
         ,triggers\<Zprime> = {reqOCM}
         ]"
        
zoperation CAMToCAM_1 =
  over LRE_Beh
  pre "st= CAM \<and> ((((pos.1 + vel.1)<0 \<or> (pos.1 + vel.1)>99) \<or> (pos.2 + vel.2)<0) \<or> (pos.2 + vel.2)>99)"
  update "[st\<Zprime>= CAM
          ,vel\<Zprime> =maneuv(vel)
         ,tr\<Zprime> =tr @ [Event advVel] @ [State CAM]
         ,triggers\<Zprime> = {reqOCM}
         ]"
        

  
definition Init :: "LRE_Beh subst" where
  [z_defs]:
  "Init = 
  [st\<leadsto> ,
   tr\<leadsto> ,
   triggers\<leadsto> ,
   ]"
(*To be filled in by user*)
  
  
zmachine LRE_BehMachine =
  init Init
  invariant LRE_Beh_inv
  operations  InitialToOCM OCMToMOM MOMToOCM HCMToOCM MOMToHCM MOMToOCM_1 HCMToOCM_1 HCMToMOM OCMToOCM MOMToOCM_2 HCMToCAM MOMToCAM CAMToOCM CAMToOCM_1 CAMToCAM MOMToCAM_1 HCMToCAM_1 CAMToCAM_1 


subsection \<open> Structural Invariants \<close>

lemma Init_inv [hoare_lemmas]: "Init establishes LRE_Beh_inv"
  by zpog_full

lemma InitialToOCM_inv [hoare_lemmas]: "InitialToOCM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma OCMToMOM_inv [hoare_lemmas]: "OCMToMOM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma MOMToOCM_inv [hoare_lemmas]: "MOMToOCM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma HCMToOCM_inv [hoare_lemmas]: "HCMToOCM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma MOMToHCM_inv [hoare_lemmas]: "MOMToHCM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma MOMToOCM_1_inv [hoare_lemmas]: "MOMToOCM_1() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma HCMToOCM_1_inv [hoare_lemmas]: "HCMToOCM_1() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma HCMToMOM_inv [hoare_lemmas]: "HCMToMOM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma OCMToOCM_inv [hoare_lemmas]: "OCMToOCM (reqV) preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma MOMToOCM_2_inv [hoare_lemmas]: "MOMToOCM_2() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma HCMToCAM_inv [hoare_lemmas]: "HCMToCAM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma MOMToCAM_inv [hoare_lemmas]: "MOMToCAM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma CAMToOCM_inv [hoare_lemmas]: "CAMToOCM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma CAMToOCM_1_inv [hoare_lemmas]: "CAMToOCM_1() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma CAMToCAM_inv [hoare_lemmas]: "CAMToCAM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma MOMToCAM_1_inv [hoare_lemmas]: "MOMToCAM_1() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma HCMToCAM_1_inv [hoare_lemmas]: "HCMToCAM_1() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma CAMToCAM_1_inv [hoare_lemmas]: "CAMToCAM_1() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  

subsection \<open> Safety Requirements \<close>

zexpr R1 is ""

lemma  "Init establishes R1"
  by zpog_full

lemma "InitialToOCM() preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "OCMToMOM() preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "MOMToOCM() preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "HCMToOCM() preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "MOMToHCM() preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "MOMToOCM_1() preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "HCMToOCM_1() preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "HCMToMOM() preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "OCMToOCM (reqV) preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "MOMToOCM_2() preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "HCMToCAM() preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "MOMToCAM() preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "CAMToOCM() preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "CAMToOCM_1() preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "CAMToCAM() preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "MOMToCAM_1() preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "HCMToCAM_1() preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "CAMToCAM_1() preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  

definition [z_defs]: "LRE_Beh_axioms = ()"

lemma LRE_Beh_deadlock_free: "LRE_Beh_axioms  \<Longrightarrow> deadlock_free LRE_BehMachine" 
  unfolding LRE_BehMachine_def
  by deadlock_free
end

