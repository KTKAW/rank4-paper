import Rank4StructureRound2.RFamilyCore

namespace QuiverProofs.Rank4StructureRound2.RFamily
open PolynomialCertificate

/-- Every integer point of the zero-unit square-overflow ray is semantically
NMA. The finite cores and all infinite regional exits have been checked. -/
theorem all_m_NMA (m : Int) (hm : 2 ≤ m) :
    ¬ MutationAcyclic (ofSix 0 1 (-(2*m-2)) 2 (-m) (2*m-1)) := by
  by_cases h2 : m=2
  · subst m
    simpa [Boundary2.node,Boundary2.pnode,matrix_six,eval] using Boundary2.NMA 0 (by decide)
  by_cases h3 : m=3
  · subst m
    simpa [Boundary3.node,Boundary3.pnode,matrix_six,eval] using Boundary3.NMA 0 (by decide)
  have ht : 0 ≤ m-4 := by omega
  have hC : -6+(m-4)*(-2)=-(2*m-2) := by omega
  have hE : -4+ -(m-4)= -m := by omega
  have hF : 7+(m-4)*2=2*m-1 := by omega
  simpa [HalfLine.node,HalfLine.pnode,matrix_six,eval,hC,hE,hF] using HalfLine.NMA (m-4) ht

#print axioms all_m_NMA
end QuiverProofs.Rank4StructureRound2.RFamily
