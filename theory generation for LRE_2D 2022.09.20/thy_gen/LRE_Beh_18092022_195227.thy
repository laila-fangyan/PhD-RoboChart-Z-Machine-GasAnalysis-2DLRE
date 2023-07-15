theory LRE_Beh_18092022_075228
imports "Z_Machines.Z_Machine"
begin

notation undefined ("???")

subsection \<open> Introduction \<close>

text \<open> This theory file is to model the LRE_Beh state machine in Z Machine notations.\<close>

subsection \<open> type definition \<close>

enumtype ProperState = OCM | MOM | HCM | CAM | initial 

definition "ProperState = {OCM, MOM, HCM, CAM, initial}" 

enumtype Turn = Reverse | Port90 | NoTurn | Starboard90 | Starboard180

definition "Turn = {Reverse, Port90, NoTurn, Starboard90, Starboard180}"

record Obstacle =
  ns_rel_dist :: real
  ew_rel_dist :: real
  depth :: real
  id :: nat
  obs_hdng :: SVec
record_default Obstacle
record Advice =
  adv_turn :: Turn
  adv_hdng :: SVec
record_default Advice
record Close =
  horiz_cda :: real
  vert_cda :: real
  id :: nat
record_default Close
record SVec =
  radial :: real
  polar :: real
  azimuth :: real
record_default SVec













consts AvoidanceMargin :: "real"
consts LREHorizon :: "real"
consts LRETemporalHorizon :: "real"
consts ODA_AUV :: "real"
consts ODA_Obs :: "real"
consts StaticObsHorizDist :: "real"
consts StaticObsVertDist :: "real"
consts StaticObsDfltVertDist :: "real"
consts MinSafeDist :: "real"

text \<open> function definition \<close>

consts hdist :: " Obstacle \<Rightarrow> real"
consts vdist :: " Obstacle \<Rightarrow> real"
consts odist :: " Obstacle \<Rightarrow> real"

subsection \<open> State Space \<close>

zstore LRE_Beh =
  cobs :: "Close"
  inOPEZ :: "boolean"
  hvel :: "real"
  vvel :: "real"
  vel :: "real"
  cstc :: "Obstacle"
  cdyn :: "Obstacle"
  x :: "real"
  CDA :: "real"
  TCPA :: "real"
  depth :: "real"
  
  hdng :: "SVec"
  
  
  
  
  
  
  
  
  
  event_endTask::"bool"
  event_reqOCM::"bool"
  event_reqMOM::"bool"
  event_reqHCM::"bool"
  event_reqVel::"bool"
  event_reqHdng::"bool"
  event_advVel::"bool"
  event_advHdng::"bool"
  event_manoeuvre::"bool"
  act_st::"ProperState"
  desired_st::"ProperState set"
  clock::"integer"
where inv: "To be entered manually"

subsection \<open> Operations \<close>

zoperation InitialToOCM =
  over LRE_Beh
  pre "act_st= initial"
  update "[ act_st\<Zprime>= OCM
  		  , desired_st\<Zprime>= {MOM, OCM, OCM}
          ]"
        
zoperation OCMToMOM =
  over LRE_Beh
  pre "act_st= OCM \<and> vel\<le> \<and> odist(cdyn)> \<and> odist(cstc)> \<and> \<not>inOPEZ \<and> event_reqMOM"
  update "[ act_st\<Zprime>= MOM
  		  , desired_st\<Zprime>= {OCM, HCM, HCM, OCM, HCM, HCM, OCM, CAM}
          , event_advVel\<Zprime> = True
          ]"
        
zoperation MOMToOCM =
  over LRE_Beh
  pre "act_st= MOM \<and> event_reqOCM"
  update "[ act_st\<Zprime>= OCM
  		  , desired_st\<Zprime>= {MOM, OCM, OCM}
          ]"
        
zoperation HCMToOCM =
  over LRE_Beh
  pre "act_st= HCM \<and> event_reqOCM"
  update "[ act_st\<Zprime>= OCM
  		  , desired_st\<Zprime>= {MOM, OCM, OCM}
          ]"
        
zoperation MOMToHCM =
  over LRE_Beh
  pre "act_st= MOM \<and> hvel\<ge> \<and> hdist(cstc)\<le>StaticObsHorizDist"
  update "[ act_st\<Zprime>= HCM
  		  , desired_st\<Zprime>= {OCM, OCM, MOM, CAM}
          , event_advVel\<Zprime> = True
          ]"
        
zoperation MOMToHCM =
  over LRE_Beh
  pre "act_st= MOM \<and> event_reqHCM"
  update "[ act_st\<Zprime>= HCM
  		  , desired_st\<Zprime>= {OCM, OCM, MOM, CAM}
          , event_advVel\<Zprime> = True
          ]"
        
zoperation MOMToOCM =
  over LRE_Beh
  pre "act_st= MOM \<and> inOPEZ"
  update "[ act_st\<Zprime>= OCM
  		  , desired_st\<Zprime>= {MOM, OCM, OCM}
          ]"
        
zoperation HCMToOCM =
  over LRE_Beh
  pre "act_st= HCM \<and> inOPEZ"
  update "[ act_st\<Zprime>= OCM
  		  , desired_st\<Zprime>= {MOM, OCM, OCM}
          ]"
        
zoperation MOMToHCM =
  over LRE_Beh
  pre "act_st= MOM \<and> vvel\<ge> \<and> vdist(cstc)\<le>StaticObsVertDist"
  update "[ act_st\<Zprime>= HCM
  		  , desired_st\<Zprime>= {OCM, OCM, MOM, CAM}
          , event_advVel\<Zprime> = True
          ]"
        
zoperation MOMToHCM =
  over LRE_Beh
  pre "act_st= MOM \<and> vdist(cstc)\<le>StaticObsDfltVertDist"
  update "[ act_st\<Zprime>= HCM
  		  , desired_st\<Zprime>= {OCM, OCM, MOM, CAM}
          , event_advVel\<Zprime> = True
          ]"
        
zoperation HCMToMOM =
  over LRE_Beh
  pre "act_st= HCM \<and> hdist(cstc)>StaticObsHorizDist \<and> vdist(cstc)>StaticObsVertDist"
  update "[ act_st\<Zprime>= MOM
  		  , desired_st\<Zprime>= {OCM, HCM, HCM, OCM, HCM, HCM, OCM, CAM}
          , event_advVel\<Zprime> = True
          ]"
        
zoperation OCMToOCM =
  over LRE_Beh
  params x \<in> "real" 
  pre "act_st= OCM \<and> event_reqVel"
  update "[ act_st\<Zprime>= OCM
  		  , desired_st\<Zprime>= {MOM, OCM, OCM}
         , event_advVel\<Zprime> = True
          ]"
        
zoperation OCMToOCM =
  over LRE_Beh
  params x \<in> "real" 
  pre "act_st= OCM \<and> event_reqHdng"
  update "[ act_st\<Zprime>= OCM
  		  , desired_st\<Zprime>= {MOM, OCM, OCM}
         , event_advHdng\<Zprime> = True
          ]"
        
zoperation MOMToOCM =
  over LRE_Beh
  pre "act_st= MOM \<and> event_endTask"
  update "[ act_st\<Zprime>= OCM
  		  , desired_st\<Zprime>= {MOM, OCM, OCM}
         , event_advVel\<Zprime> = True
          ]"
        
zoperation HCMToCAM =
  over LRE_Beh
  pre "act_st= HCM \<and> CDA<MinSafeDist \<and> TCPA\<ge>0"
  update "[ act_st\<Zprime>= CAM
  		  , desired_st\<Zprime>= {OCM, OCM}
          , event_manoeuvre\<Zprime> = True
          ]"
        
zoperation MOMToCAM =
  over LRE_Beh
  pre "act_st= MOM \<and> CDA<MinSafeDist \<and> TCPA\<ge>0"
  update "[ act_st\<Zprime>= CAM
  		  , desired_st\<Zprime>= {OCM, OCM}
          , event_manoeuvre\<Zprime> = True
          ]"
        
zoperation CAMToOCM =
  over LRE_Beh
  pre "act_st= CAM \<and> CDA\<ge>MinSafeDist"
  update "[ act_st\<Zprime>= OCM
  		  , desired_st\<Zprime>= {MOM, OCM, OCM}
          ]"
        
zoperation CAMToOCM =
  over LRE_Beh
  pre "act_st= CAM \<and> event_reqOCM"
  update "[ act_st\<Zprime>= OCM
  		  , desired_st\<Zprime>= {MOM, OCM, OCM}
          ]"
        
zoperation Shine =
  over LRE_Beh
  params s\<in>"{act_st}"
  
definition Init :: "LRE_Beh subst" where
  [z_defs]:
  "Init = 
  [\<leadsto>]"
(*To be filled in by user*)
  
  
zmachine LRE_BehMachine =
  init Init
  operations  InitialToOCM OCMToMOM MOMToOCM HCMToOCM MOMToHCM MOMToHCM MOMToOCM HCMToOCM MOMToHCM MOMToHCM HCMToMOM OCMToOCM OCMToOCM MOMToOCM HCMToCAM MOMToCAM CAMToOCM CAMToOCM Shine

animate LRE_BehMachine


subsection \<open> Structural Invariants \<close>

lemma Init_inv: "Init establishes LRE_Beh_inv"
  by zpog_full

lemma InitialToOCM_inv: "InitialToOCM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma OCMToMOM_inv: "OCMToMOM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma MOMToOCM_inv: "MOMToOCM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma HCMToOCM_inv: "HCMToOCM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma MOMToHCM_inv: "MOMToHCM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma HCMToMOM_inv: "HCMToMOM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma OCMToOCM_inv: "OCMToOCM (x) preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma HCMToCAM_inv: "HCMToCAM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma MOMToCAM_inv: "MOMToCAM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma CAMToOCM_inv: "CAMToOCM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  

end

