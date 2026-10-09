import Rank4StructureRound2.PFamilyCore
namespace QuiverProofs.Rank4StructureRound2.PFamily
open PolynomialCertificate

 theorem all_b_NMA (b : Int) (hb : 1 ≤ b) :
     ¬ MutationAcyclic (ofSix 2 b (-1) 1 (-1) (b+3)) := by
   by_cases h : b=1
   · subst b
     simpa [Boundary.node, Boundary.pnode, matrix_six, eval] using Boundary.NMA 0 (by decide)
   · have ht : 0 ≤ b-2 := by omega
     have h2 : 2+(b-2)=b := by omega
     have h5 : 5+(b-2)=b+3 := by omega
     simpa [HalfLine.node, HalfLine.pnode, matrix_six, eval, h2, h5] using HalfLine.NMA (b-2) ht
 #print axioms all_b_NMA
 end QuiverProofs.Rank4StructureRound2.PFamily
 