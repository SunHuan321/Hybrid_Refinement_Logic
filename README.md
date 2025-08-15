# Hybrid Refinement Logic

## What is this repository for?
This project contains the Isabelle/HOL formalisation and soundness proof for hybrid refinement logic, a logic used to verify that implementation perserves certain properties (i.e., safety or security) from its design
## How do I get set up?
   1. Install Isabelle2023 from:<br>
       https://isabelle.in.tum.de <br>
   2. Make AFP available to Isabelle from:<br>
	https://www.isa-afp.org/ <br>
      add the afp path into the roots of Isabelle2025 <br>
   3. Change logic session to "Ordinary_Differential_Equations" (change requires restart) <br>
   4. Open the ".thy" files in this package in Isabelle2025 <br>

## Layout

### Semantics and Reasoning Framework
* Analysis_More : auxiliary lemmas for ODEs
* Language: syntax and semantics for HCSP used to model hybrid systems 
* Par_Refine: parallel refinement framework which support compositional refinement verification
* Sync_Refine: synchronization refinement framework which support refinement verification between synchronized parallel implementation and sequential design.
### Case Study
* Lander: An example of lunar lander, in which we prove the parallel lunar lander implementation can be abstracted by a sequential design.
