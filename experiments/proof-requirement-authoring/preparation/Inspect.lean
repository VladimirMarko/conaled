import Examples.ProofRequirementSupport

set_option pp.proofs true in
#print ProofRequirementTrial.Source.reverseBlocks

set_option pp.proofs true in
#print ProofRequirementTrial.Source.selected

set_option pp.proofs true in
#print ProofRequirementTrial.Source.selected._proof_1

#check @List.reverse_reverse
#check @List.reverse_append
#check @List.append_nil
