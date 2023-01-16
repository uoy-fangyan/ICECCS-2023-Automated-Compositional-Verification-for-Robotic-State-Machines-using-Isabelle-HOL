This project includes two case studies: LRE and GasAnalysis.

The RoboChart model is provied as EMF models.

The transformation rule is in the folder of 'Transformation rule'. Both cases of LRE and GasAnalysis use the transformation rules in this folder.

The verificaiton result from Isbelle/HOL is under the direction of 'theory generatio for XX/ xx verificaiton'.

The transformation is implemented in Epsilon (download: https://www.eclipse.org/epsilon/download/)
The RoboChart metamodel shall be registered (metamodel download: https://robostar.cs.york.ac.uk/robotool/)
To generate a thy file in Epsilon, we launch configuration files.
To set up the configuration (GasAnalysis as example):
 1. right click the egx file to 'run configuration'
 2. source = /RoboChart_verification_in_Isabell_ICECCS2023/Transformation rule/thy_generation_rule.egx
 3. file should be generated in the following directory = RoboChart_verification_in_Isabell_ICECCS2023/theory generation for GasAnalysis/thy_gen
 4. Models/ add model /EMF model /Identification/ name=RC, model file =/RoboChart_verification_in_Isabell_ICECCS2023/theory generation for GasAnalysis/GasAnalysis_state_machine.model
 5. Common/ save as/ shared file = \RoboChart_verification_in_Isabell_ICECCS2023\theory generation for GasAnalysis
 


Theory file is verified in the Isabelle/UTP (download link: https://isabelle-utp.york.ac.uk/download)
After the thy file is generated, we need to open the file in Isabelle and verify each lemma for the requirements.
